	.text
	.file	"/b/build/slave/linux/build/src/buildbot/work/gcc/gcc/testsuite/gcc.c-torture/execute/931018-1.c"
	.globl	main
	.type	main,@function
main:                                   # @main
	.result 	i32
# BB#0:                                 # %entry
	i32.const	$push0=, 0
	call    	exit, $pop0
	unreachable
.Lfunc_end0:
	.size	main, .Lfunc_end0-main

	.globl	f
	.type	f,@function
f:                                      # @f
	.param  	i32
	.result 	i32
# BB#0:                                 # %entry
	block   	.LBB1_2
	i32.const	$push0=, -559038737
	i32.ne  	$push1=, $0, $pop0
	br_if   	$pop1, .LBB1_2
# BB#1:                                 # %if.end
	return  	$0
.LBB1_2:                                  # %if.then
	call    	abort
	unreachable
.Lfunc_end1:
	.size	f, .Lfunc_end1-f

	.type	v,@object               # @v
	.section	.rodata,"a",@progbits
	.globl	v
	.align	2
v:
	.int32	3735928559              # 0xdeadbeef
	.size	v, 4

	.type	a,@object               # @a
	.bss
	.globl	a
	.align	4
a:
	.zero	16384
	.size	a, 16384


	.ident	"clang version 3.8.0 "
	.section	".note.GNU-stack","",@progbits