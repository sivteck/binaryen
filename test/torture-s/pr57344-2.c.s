	.text
	.file	"/b/build/slave/linux/build/src/buildbot/work/gcc/gcc/testsuite/gcc.c-torture/execute/pr57344-2.c"
	.globl	foo
	.type	foo,@function
foo:                                    # @foo
	.param  	i32
# BB#0:                                 # %entry
	block   	.LBB0_2
	i32.const	$push0=, -3161
	i32.ne  	$push1=, $0, $pop0
	br_if   	$pop1, .LBB0_2
# BB#1:                                 # %if.end
	#APP
	#NO_APP
	return
.LBB0_2:                                  # %if.then
	call    	abort
	unreachable
.Lfunc_end0:
	.size	foo, .Lfunc_end0-foo

	.globl	main
	.type	main,@function
main:                                   # @main
	.result 	i32
	.local  	i32, i32, i32
# BB#0:                                 # %entry
	i32.const	$0=, 0
	i32.load	$2=, i($0)
	block   	.LBB1_3
	i64.const	$push0=, 562525691183104
	i64.store	$discard=, s+8($0), $pop0
	i32.gt_s	$push1=, $2, $0
	br_if   	$pop1, .LBB1_3
# BB#1:                                 # %for.body.preheader
	i32.const	$push2=, -3161
	call    	foo, $pop2
	i32.load	$2=, i($0)
	i32.const	$1=, 1
	i32.add 	$push3=, $2, $1
	i32.store	$discard=, i($0), $pop3
	i32.const	$push4=, -1
	i32.gt_s	$push5=, $2, $pop4
	br_if   	$pop5, .LBB1_3
.LBB1_2:                                  # %for.body.for.body_crit_edge
                                        # =>This Inner Loop Header: Depth=1
	loop    	.LBB1_3
	i32.const	$2=, s+8
	i64.load32_u	$push17=, s+8($0)
	i32.const	$push11=, 4
	i32.add 	$push12=, $2, $pop11
	i64.load16_u	$push13=, 0($pop12)
	i32.const	$push6=, 6
	i32.add 	$push7=, $2, $pop6
	i64.load8_u	$push8=, 0($pop7)
	i64.const	$push9=, 16
	i64.shl 	$push10=, $pop8, $pop9
	i64.or  	$push14=, $pop13, $pop10
	i64.const	$push15=, 32
	i64.shl 	$push16=, $pop14, $pop15
	i64.or  	$push18=, $pop17, $pop16
	i64.const	$push19=, 15
	i64.shl 	$push20=, $pop18, $pop19
	i64.const	$push21=, 42
	i64.shr_s	$push22=, $pop20, $pop21
	i32.wrap/i64	$push23=, $pop22
	call    	foo, $pop23
	i32.load	$2=, i($0)
	i32.add 	$push24=, $2, $1
	i32.store	$discard=, i($0), $pop24
	i32.lt_s	$push25=, $2, $0
	br_if   	$pop25, .LBB1_2
.LBB1_3:                                  # %for.end
	return  	$0
.Lfunc_end1:
	.size	main, .Lfunc_end1-main

	.type	s,@object               # @s
	.bss
	.globl	s
	.align	4
s:
	.zero	16
	.size	s, 16

	.type	i,@object               # @i
	.globl	i
	.align	2
i:
	.int32	0                       # 0x0
	.size	i, 4


	.ident	"clang version 3.8.0 "
	.section	".note.GNU-stack","",@progbits