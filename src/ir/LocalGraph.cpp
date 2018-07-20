//#define LOCAL_GRAPH_DEBUG
/*
 * Copyright 2017 WebAssembly Community Group participants
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <unordered_map>
#include <unordered_set>

#include <wasm-builder.h>
#include <wasm-printing.h>
#include <ir/find_all.h>
#include <ir/local-graph.h>

namespace wasm {

namespace LocalGraphInternal {

// The algorithm we use to connect gets and sets is to first do one
// pass to create Sources for every get. A Source is still abstract
// at this point, and may contain both a bunch of sets and a bunch
// of incoming Sources. We then flow values on the Source graph.
// After doing so, each get has the sets in its Source.
//
// XXX
// So far this seems slower, and takes a lot more memory. The memory
// may be the larger issue.
// XXX

struct Source {
  std::unordered_set<SetLocal*> sets;
  std::unordered_set<Source*> inputs;
  std::unordered_set<Source*> outputs;

  // For blocks, we start out with the block output having a nullptr,
  // as nothing may reach there (no branches and no flow). When we
  // see the first branch, we add it with possibleMerge set to true.
  // If we see another branch, or later the flow, and they are not
  // identical to what's already there, we create a merge source.
  // In all cases we remove possibleMerge when the block is done.
  bool possibleMerge = false;

  // TODO: add a 'used' flag, which is marked on the roots, the
  //       sources we saw had a get. Flow that out to see which are
  //       needed, can save a lot of work potentially?
};

struct GetSetConnector : public PostWalker<GetSetConnector> {
  LocalGraph::GetSetses& getSetses;
  LocalGraph::Locations& locations;

  Index numLocals;

  // local index => current Source. This can be nullptr if we are
  // in unreachable control flow.
  typedef std::vector<Source*> Sources;

  // Current sources as we traverse.
  Sources currSources;

  GetSetConnector(LocalGraph::GetSetses& getSetses, LocalGraph::Locations& locations, Function* func) : getSetses(getSetses), locations(locations) {
    numLocals = func->getNumLocals();
    if (numLocals == 0) return;
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph: start\n";
#endif
    // Prepare to run
    setFunction(func);
    // Initial state: initial values (param or zero init) for all indexes
    currSources.resize(numLocals);
    for (Index i = 0; i < numLocals; i++) {
      currSources[i] = newSource(nullptr);
    }
    // Create the Source graph by walking the IR
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph:   walk " << func->name << '\n';
#endif
    PostWalker<GetSetConnector>::doWalkFunction(func);
    // Flow the Sources across blocks
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph:   flow\n";
#endif
    flow();
    // Get the getSets from their Sources
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph:   emit\n";
#endif
    emitGetSetses();
    // Finish up
    allSources.clear(); // free this now, users of the object don't need it
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph: done\n";
#endif
  }

  // All sources ever created.
  std::vector<std::unique_ptr<Source>> allSources;

  // Sources that are free for use.
  std::vector<Source*> availableSources;

  Source* newSource() {
    auto* source = new Source();
    allSources.push_back(std::unique_ptr<Source>(source));
    return source;
  }

  Source* newSource(SetLocal* set) {
    auto* source = newSource();
    source->sets.insert(set);
    return source;
  }

  // Connect a get to its Source
  std::unordered_map<GetLocal*, Source*> getSources;

  // Connect a name - a branch target - to relevant sources.
  std::unordered_map<Name, Sources> labelSources;

  std::unordered_set<Name> loopLabels;

  bool isLoopLabel(Name name) {
    return loopLabels.count(name) > 0;
  }

  // traversal work

  static void doPreVisitBlock(GetSetConnector* self, Expression** currp) {
    auto* curr = (*currp)->dynCast<Block>();
    if (!curr->name.is()) return;
    // The initial merge Sources at the block's end are empty. Branches
    // and the data flowing out may add to them.
    auto& sources = self->labelSources[curr->name];
    sources.resize(self->numLocals);
    std::fill(sources.begin(), sources.end(), nullptr);
  }

  static void doVisitBlock(GetSetConnector* self, Expression** currp) {
    auto* curr = (*currp)->dynCast<Block>();
    if (!curr->name.is()) return;
    auto& sources = self->labelSources[curr->name];
    if (inUnreachableCode(sources)) {
      // No branches to here, just flow out currSources
      return;
    }
    if (inUnreachableCode()) {
      // Only the branches exist, copy them.
      currSources = sources;
      // Clear possible merges that may have happened due to branches
      for (auto* source : currSources) {
        source->possibleMerge = false;
      }
      return;
    }
    // We need to merge the branches with the flow, as both exist.
    for (Index i = 0; i < numLocals; i++) {
      auto* branches = sources[i];
      auto* flow = currSources[i];
      if (branches != flow) {
        // There is something to combine here
        if (branches->possibleMerge) {
          // We need an actual merge.
          branches->possibleMerge = false;
          auto* merge = newSource();
          connectInput(merge, branches);
          connectInput(merge, flow);
          currSources[i] = merge;
        } else {
          // The branches is already a merge, add to that.
          connectInput(merge, flow);
        }
      } else {
        branches->possibleMerge = false;
      }
    }
  }

  static void doPreVisitLoop(GetSetConnector* self, Expression** currp) {
    auto* curr = (*currp)->dynCast<Loop>();
    if (!curr->name.is()) return;
    // Note this label is for a loop.
    self->loopLabels.insert(curr->name);
    // Each branch we see will add a source to the loop's sources.
    auto& sources = self->labelSources[curr->name];
    sources.resize(self->numLocals);
    // Prepare merge Sources for all indexes. We start with the input
    // flowing in, and branches will add further sources later. For
    // loops, unlike other things, we create a merge Source eagerly.
    for (Index i = 0; i < self->numLocals; i++) {
      Source* source = newSource();
      self->connectInput(source, self->currSources[i]);
      sources[i] = self->currSources[i] = source;
    }
  }

  std::vector<Sources> ifStack;

  static void doPreVisitIfTrue(GetSetConnector* self, Expression** currp) {
    self->ifStack.push_back(self->currSources); // needed for merge later
  }

  static void doPreVisitIfFalse(GetSetConnector* self, Expression** currp) {
    auto preIfTrue = self->ifStack.back();
    self->ifStack.back() = self->currSources;
    self->currSources = preIfTrue;
  }

  static void doVisitIf(GetSetConnector* self, Expression** currp) {
    // The if stack contains what we need to merge with the current
    // data - if no else, it contains the sources if we skip the
    // if body, and if there is an else, it contains the if true's
    // output.
    auto& sources = self->ifStack.back();
    if (inUnreachableCode(sources)) {
      // No previous sources to merge, just flow out currSources
      return;
    }
    if (inUnreachableCode()) {
      // Just copy the other arm.
      currSources = sources;
      return;
    }
    // We have two things to merge.
    for (Index i = 0; i < numLocals; i++) {
      auto* previous = sources[i];
      auto* flow = currSources[i];
      if (previous != flow) {
        // We need a merge.
        auto* merge = newSource();
        connectInput(merge, previous);
        connectInput(merge, flow);
        currSources[i] = merge;
      }
    }
    self->ifStack.pop_back();
  }

  static void doVisitGetLocal(GetSetConnector* self, Expression** currp) {
    if (self->inUnreachableCode()) return;
    auto* curr = (*currp)->cast<GetLocal>();
    self->getSources[curr] = self->currSources[curr->index];
    self->locations[curr] = currp;
  }

  static void doVisitSetLocal(GetSetConnector* self, Expression** currp) {
    if (self->inUnreachableCode()) return;
    auto* curr = (*currp)->cast<SetLocal>();
    self->currSources[curr->index] = self->newSource(curr);
    self->locations[curr] = currp;
  }

  static void scan(GetSetConnector* self, Expression** currp) {
    auto* curr = *currp;

    switch (curr->_id) {
      case Expression::Id::BlockId: {
        self->pushTask(GetSetConnector::doVisitBlock, currp);
        auto& list = curr->cast<Block>()->list;
        for (int i = int(list.size()) - 1; i >= 0; i--) {
          self->pushTask(GetSetConnector::scan, &list[i]);
        }
        self->pushTask(GetSetConnector::doPreVisitBlock, currp);
        break;
      }
      case Expression::Id::IfId: {
        auto* iff = curr->cast<If>();
        self->pushTask(GetSetConnector::doVisitIf, currp);
        if (iff->ifFalse) {
          self->pushTask(GetSetConnector::scan, &iff->ifFalse);
          self->pushTask(GetSetConnector::doPreVisitIfFalse, currp);
        }
        self->pushTask(GetSetConnector::scan, &iff->ifTrue);
        self->pushTask(GetSetConnector::doPreVisitIfTrue, currp);
        self->pushTask(GetSetConnector::scan, &iff->condition);
        break;
      }
      case Expression::Id::LoopId: {
        self->pushTask(GetSetConnector::doVisitLoop, currp);
        self->pushTask(GetSetConnector::scan, &curr->cast<Loop>()->body);
        self->pushTask(GetSetConnector::doPreVisitLoop, currp);
        break;
      }
      default: {
        PostWalker<GetSetConnector>::scan(self, currp);
      }
    }
  }

  void connectInput(Source* main, Source* input) {
    assert(main);
    assert(input);
    main->inputs.insert(input);
    input->outputs.insert(main);
  }

  void connectPossibleInput(Source* main, Source* input) {
    if (!input) return;
    connectInput(main, input);
  }

  void handleBranch(Name name) {
    if (inUnreachableCode()) return;
    // From here on, we can assume currSources are not nullptr
    auto& sources = labelSources[name];
    if (isLoopLabel(name)) {
      // Merge source was created eagerly, just connect
      for (Index i = 0; i < numLocals; i++) {
        connectInput(sources[i], currSources[i]);
      }
    } else {
      // For a block, we start with nullptr as there may not be
      // anything flowing out of the block at all.
      if (inUnreachableCode(sources)) {
        // This is the first branch reaching this block. Just
        // copy the current sources. We'll create a merge
        // later if necessary, knowing we need that thanks to
        // the possibleMerge flag.
        sources = currSources;
        for (auto* source : sources) {
          assert(!source->possibleMerge);
          source->possibleMerge = true;
        }
      } else {
        // There were already branches to here.
        for (Index i = 0; i < numLocals; i++) {
          auto* branches = sources[i];
          auto* curr = currSources[i];
          if (branches != curr) {
            // There is something to combine here.
            if (branches->possibleMerge) {
              // We need an actual merge.
              branches->possibleMerge = false;
              auto* merge = newSource();
              connectInput(merge, branches);
              connectInput(merge, curr);
              sources[i] = merge;
            } else {
              // The branches are already a merge, add to that.
              connectInput(branches, curr);
            }
          }
        }
      }
    }
  }

  void visitBreak(Break* curr) {
    handleBranch(curr->name);
    if (!curr->condition) {
      enterUnreachableCode();
    }
  }

  void visitSwitch(Switch* curr) {
    for (auto target : curr->targets) {
      handleBranch(target);
    }
    handleBranch(curr->default_);
    enterUnreachableCode();
  }

  void visitReturn(Return* curr) {
    enterUnreachableCode();
  }

  void visitUnreachable(Unreachable* curr) {
    enterUnreachableCode();
  }

  void enterUnreachableCode() {
    std::fill(currSources.begin(), currSources.end(), nullptr);
  }

  bool inUnreachableCode(Sources& sources) {
    return sources[0] == nullptr;
  }

  bool inUnreachableCode() {
    return inUnreachableCode(currSources);
  }

  void flow() {
    std::unordered_set<Source*> work;
    // The initial work is the set of sources with sets.
    for (auto& source : allSources) {
      if (!source->sets.empty()) {
        work.insert(source.get());
      }
    }
    // Keep working while stuff is flowing.
    while (!work.empty()) {
      auto* source = *work.begin();
      work.erase(work.begin());
      // Flow the sets to the outputs.
      for (auto* output : source->outputs) {
        for (auto* set : source->sets) {
          if (output->sets.find(set) == output->sets.end()) {
            output->sets.insert(set);
            work.insert(output);
          }
        }
      }
    }
  }

  void emitGetSetses() {
    for (auto& pair : getSources) {
      auto* get = pair.first;
      auto* source = pair.second;
      // Create the sets for the get, and prepare to add if there are any
      auto& emitted = getSetses[get];
      if (!source) {
        // was in unreachable code, nothing to do
        continue;
      }
      for (auto* set : source->sets) {
        emitted.insert(set);
      }
    }
  }

#ifdef LOCAL_GRAPH_DEBUG
  void dumpCurrSources(std::string title="dump") {
    std::cout << title << '\n';
    for (Index i = 0; i < numLocals; i++) {
      std::cout << " currSources[" << i << "] is " << currSources[i] << '\n';
    }
  }
#endif
};

} // namespace LocalGraphInternal

// LocalGraph implementation

LocalGraph::LocalGraph(Function* func) {
  LocalGraphInternal::GetSetConnector getSetConnector(getSetses, locations, func);

#if 0 // LOCAL_GRAPH_DEBUG
  std::cout << "LocalGraph: dump\n";
  for (auto& pair : getSetses) {
    auto* get = pair.first;
    auto& sets = pair.second;
    std::cout << "GET\n" << get << " is influenced by\n";
    for (auto* set : sets) {
      std::cout << set << '\n';
    }
  }
  std::cout << "total locations: " << locations.size() << '\n';
#endif
}

void LocalGraph::computeInfluences() {
  for (auto& pair : locations) {
    auto* curr = pair.first;
    if (auto* set = curr->dynCast<SetLocal>()) {
      FindAll<GetLocal> findAll(set->value);
      for (auto* get : findAll.list) {
        getInfluences[get].insert(set);
      }
    } else {
      auto* get = curr->cast<GetLocal>();
      for (auto* set : getSetses[get]) {
        setInfluences[set].insert(get);
      }
    }
  }
}

} // namespace wasm

