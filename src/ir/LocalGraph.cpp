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

struct Source {
  std::unordered_set<SetLocal*> sets;
  std::unordered_set<Source*> inputs;
  std::unordered_set<Source*> outputs;

  // TODO: add a 'used' flag, which is marked on the roots, the
  //       sources we saw had a get. Flow that out to see which are
  //       needed, can save a lot of work potentially?

  Source() {}

  Source(SetLocal* set) {
    sets.insert(set);
  }
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
    // Prepare to run
    setFunction(func);
    // Initial state: initial values (param or zero init) for all indexes
    currSources.resize(numLocals);
    for (Index i = 0; i < numLocals; i++) {
      currSources[i] = note(new Source(nullptr));
    }
    // Create the Source graph by walking the IR
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph: walk " << func->name << '\n';
#endif
    PostWalker<GetSetConnector>::doWalkFunction(func);
    // Flow the Sources across blocks
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph: flow\n";
#endif
    flow();
    // Get the getSets from their Sources
#ifdef LOCAL_GRAPH_DEBUG
    std::cout << "LocalGraph: emit\n";
#endif
    emitGetSetses();
  }

  std::vector<std::unique_ptr<Source>> allSources;

  Source* note(Source* source) {
    assert(source);
    allSources.push_back(std::unique_ptr<Source>(source));
    return source;
  }

  // Given a main source, add an input to it. One or both may
  // be unreachable (nullptrs). If main is unreachable but not
  // the input, we create main so that we can connect them.
  void addInput(Source*& main, Source* input) {
    if (!input) {
      return;
    }
    if (!main) {
      main = note(new Source());
    }
    main->inputs.insert(input);
    input->outputs.insert(main);
  }

  // Connect a get to its Source
  std::unordered_map<GetLocal*, Source*> getSources;

  // Connect a name - a branch target - to relevant sources.
  std::unordered_map<Name, Sources> labelSources;

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
    // Add the data flowing out at the end.
    for (Index i = 0; i < self->numLocals; i++) {
      // TODO: in all merges, may be trivial stuff we can optimize.
      //       or maybe at the end, if a Source has just one input and
      //       output, fuse them - compact the graph before flowing it.
      //       that would also be the time to dce the graph
      self->addInput(sources[i], self->currSources[i]);
      self->currSources[i] = sources[i];
    }
  }

  static void doPreVisitLoop(GetSetConnector* self, Expression** currp) {
    auto* curr = (*currp)->dynCast<Loop>();
    if (!curr->name.is()) return;
    // Each branch we see will add a source to the loop's sources.
    auto& sources = self->labelSources[curr->name];
    sources.resize(self->numLocals);
    // Prepare merge Sources for all indexes. We start with the input
    // flowing in, and branches will add further sources later.
    for (Index i = 0; i < self->numLocals; i++) {
      Source* source = nullptr; // we may not need one
      self->addInput(source, self->currSources[i]);
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
    for (Index i = 0; i < self->numLocals; i++) {
      Source* source = nullptr; // we may not need one
      self->addInput(source, sources[i]);
      self->addInput(source, self->currSources[i]);
      self->currSources[i] = source;
    }
    self->ifStack.pop_back();
  }

  static void doVisitGetLocal(GetSetConnector* self, Expression** currp) {
    auto* curr = (*currp)->cast<GetLocal>();
    self->getSources[curr] = self->currSources[curr->index];
    self->locations[curr] = currp;
  }

  static void doVisitSetLocal(GetSetConnector* self, Expression** currp) {
    auto* curr = (*currp)->cast<SetLocal>();
    self->currSources[curr->index] = self->note(new Source(curr));
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

  void handleBranch(Name name) {
    auto& sources = labelSources[name];
    for (Index i = 0; i < numLocals; i++) {
      addInput(sources[i], currSources[i]);
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

#ifdef LOCAL_GRAPH_DEBUG
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

