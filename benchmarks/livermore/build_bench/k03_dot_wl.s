.global _main
.align 2

_main:
  sub sp, sp, #224
  str x30, [sp, #216]
  str x29, [sp, #208]
  add x29, sp, #208
  // Save callee-saved registers
  stp d9, d8, [sp, #168]
  str d10, [sp, #184]

  // Initialize all variables to 0
  mov x0, #0

  mov x9, #0
  mov x7, #0
  fmov d9, x0
  fmov d8, x0
  fmov d10, x0
  fmov d7, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #120]
  str x0, [sp, #128]
  str x0, [sp, #136]
  str x0, [sp, #144]
  str x0, [sp, #152]
  str x0, [sp, #160]

.L0:
  mov x0, #0
  mov x9, x0
.L1:
  mov x0, #0
  mov x7, x0
.L2:
  mov x0, #0
  fmov d9, x0
.L3:
  mov x0, #0
  fmov d8, x0
.L4:
  mov x0, #0
  fmov d10, x0
.L5:
  mov x0, #0
  fmov d7, x0
.L6:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L8:
  fadd d10, d3, d8
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L10:
  fmul d7, d3, d8
.L11:
  mov x0, #1
  mov x9, x0
.L12:
  mov x0, #1001
  mov x4, x0
.L13:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L14:
  mov x0, #0
  fmov d5, x0
.L15:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L16:
  mov x0, #1
  mov x3, x0
.L17:
  mov x1, x9
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L27
.L18:
  fsub d3, d6, d8
.L19:
  fmul d3, d3, d10
.L20:
  fadd d10, d3, d8
.L21:
  fsub d8, d5, d8
.L22:
  fsub d3, d10, d7
.L23:
  fmul d3, d3, d4
.L24:
  mov x1, x9
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L25:
  add x9, x9, x3
.L26:
  b .L17
.L27:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L28:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L29:
  fadd d10, d3, d8
.L30:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L31:
  fmul d7, d3, d8
.L32:
  mov x0, #1
  mov x9, x0
.L33:
  mov x0, #1001
  mov x4, x0
.L34:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L35:
  mov x0, #0
  fmov d5, x0
.L36:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L37:
  mov x0, #1
  mov x3, x0
.L38:
  mov x1, x9
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L48
.L39:
  fsub d3, d6, d8
.L40:
  fmul d3, d3, d10
.L41:
  fadd d10, d3, d8
.L42:
  fsub d8, d5, d8
.L43:
  fsub d3, d10, d7
.L44:
  fmul d3, d3, d4
.L45:
  mov x1, x9
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L46:
  add x9, x9, x3
.L47:
  b .L38
.L48:
  mov x0, #1
  mov x7, x0
.L49:
  movz x0, #6576
  movk x0, #484, lsl #16
  mov x6, x0
.L50:
  mov x0, #1001
  mov x5, x0
.L51:
  mov x0, #1
  mov x4, x0
.L52:
  mov x0, #1
  mov x3, x0
.L53:
  mov x1, x7
  mov x2, x6
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L65
.L54:
  mov x0, #0
  fmov d9, x0
.L55:
  mov x0, #1
  mov x9, x0
.L56:
  mov x1, x9
  mov x2, x5
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L63
.L57:
  mov x1, x9
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L58:
  mov x1, x9
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L59:
  fmul d3, d4, d3
.L60:
  fadd d9, d9, d3
.L61:
  add x9, x9, x4
.L62:
  b .L56
.L63:
  add x7, x7, x3
.L64:
  b .L53
.L65:
  mov x0, x9
  str x0, [sp, #120]
.L66:
  mov x0, x7
  str x0, [sp, #128]
.L67:
  str d9, [sp, #136]
.L68:
  str d8, [sp, #144]
.L69:
  str d10, [sp, #152]
.L70:
  str d7, [sp, #160]
.L71:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #120]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #128]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print q (float)
  ldr d0, [sp, #136]
  sub sp, sp, #32
  adrp x8, .Lname_q@PAGE
  add x8, x8, .Lname_q@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #144]
  sub sp, sp, #32
  adrp x8, .Lname_fuzz@PAGE
  add x8, x8, .Lname_fuzz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print buzz (float)
  ldr d0, [sp, #152]
  sub sp, sp, #32
  adrp x8, .Lname_buzz@PAGE
  add x8, x8, .Lname_buzz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fizz (float)
  ldr d0, [sp, #160]
  sub sp, sp, #32
  adrp x8, .Lname_fizz@PAGE
  add x8, x8, .Lname_fizz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32

  // Exit with code 0
  mov x0, #0
  // Restore callee-saved registers
  ldp d9, d8, [sp, #168]
  ldr d10, [sp, #184]
  ldr x29, [sp, #208]
  ldr x30, [sp, #216]
  add sp, sp, #224
  ret

.Ldiv_by_zero:
  adrp x0, .Ldiv_msg@PAGE
  add x0, x0, .Ldiv_msg@PAGEOFF
  bl _printf
  mov x0, #1
  bl _exit

.Lbounds_err:
  adrp x0, .Lbounds_msg@PAGE
  add x0, x0, .Lbounds_msg@PAGEOFF
  bl _printf
  mov x0, #1
  bl _exit

.section __TEXT,__cstring
.Lfmt:
  .asciz "%s = %ld\n"
.Lfmt_float:
  .asciz "%s = %f\n"
.Ldiv_msg:
  .asciz "error: division by zero\n"
.Lbounds_msg:
  .asciz "error: array index out of bounds\n"
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_q:
  .asciz "q"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
