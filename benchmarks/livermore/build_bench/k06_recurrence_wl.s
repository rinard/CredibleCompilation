.global _main
.align 2

_main:
  sub sp, sp, #304
  str x30, [sp, #296]
  str x29, [sp, #288]
  add x29, sp, #288
  // Save callee-saved registers
  stp x21, x20, [sp, #240]
  str x19, [sp, #256]
  stp d9, d10, [sp, #272]
  str d8, [sp, #288]

  // Initialize all variables to 0
  mov x0, #0

  mov x21, #0
  mov x20, #0
  mov x19, #0
  fmov d9, x0
  fmov d10, x0
  fmov d8, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x15, #0
  mov x14, #0
  fmov d7, x0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #192]
  str x0, [sp, #200]
  str x0, [sp, #208]
  str x0, [sp, #216]
  str x0, [sp, #224]
  str x0, [sp, #232]

.L0:
  mov x0, #0
  mov x21, x0
.L1:
  mov x0, #0
  mov x20, x0
.L2:
  mov x0, #0
  mov x19, x0
.L3:
  mov x0, #0
  fmov d9, x0
.L4:
  mov x0, #0
  fmov d10, x0
.L5:
  mov x0, #0
  fmov d8, x0
.L6:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L8:
  fadd d10, d3, d9
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L10:
  fmul d8, d3, d9
.L11:
  mov x0, #1
  mov x20, x0
.L12:
  mov x0, #4096
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
  mov x1, x20
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L27
.L18:
  fsub d3, d6, d9
.L19:
  fmul d3, d3, d10
.L20:
  fadd d10, d3, d9
.L21:
  fsub d9, d5, d9
.L22:
  fsub d3, d10, d8
.L23:
  fmul d3, d3, d4
.L24:
  mov x1, x20
  adrp x8, _arr_b@PAGE
  add x8, x8, _arr_b@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L25:
  add x20, x20, x3
.L26:
  b .L17
.L27:
  mov x0, #1
  mov x19, x0
.L28:
  movz x0, #28488
  movk x0, #42, lsl #16
  mov x15, x0
.L29:
  mov x0, #1001
  mov x14, x0
.L30:
  mov x0, #0
  fmov d7, x0
.L31:
  mov x0, #1
  mov x13, x0
.L32:
  mov x0, #1
  mov x12, x0
.L33:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d6, x0
.L34:
  mov x0, #64
  mov x11, x0
.L35:
  mov x0, #1
  mov x10, x0
.L36:
  mov x0, #1
  mov x9, x0
.L37:
  mov x0, #64
  mov x7, x0
.L38:
  mov x0, #1
  mov x6, x0
.L39:
  mov x0, #1
  mov x5, x0
.L40:
  mov x0, #1
  mov x4, x0
.L41:
  mov x1, x19
  mov x2, x15
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L69
.L42:
  mov x0, #1
  mov x21, x0
.L43:
  mov x1, x21
  mov x2, x14
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L47
.L44:
  mov x1, x21
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  str d7, [x8, x1, lsl #3]
.L45:
  add x21, x21, x13
.L46:
  b .L43
.L47:
  mov x1, x12
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  str d6, [x8, x1, lsl #3]
.L48:
  mov x0, #2
  mov x21, x0
.L49:
  mov x1, x21
  mov x2, x11
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L67
.L50:
  mov x0, #1
  mov x20, x0
.L51:
  sub x3, x21, x10
.L52:
  mov x1, x20
  mov x2, x3
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L65
.L53:
  mov x1, x21
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  ldr d5, [x8, x1, lsl #3]
.L54:
  sub x3, x21, x9
.L55:
  mul x3, x3, x7
.L56:
  add x3, x3, x20
.L57:
  mov x1, x3
  mov x0, #4097
  cmp x1, x0
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_b@PAGE
  add x8, x8, _arr_b@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L58:
  sub x3, x21, x20
.L59:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L60:
  fmul d3, d4, d3
.L61:
  fadd d3, d5, d3
.L62:
  mov x1, x21
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L63:
  add x20, x20, x6
.L64:
  b .L51
.L65:
  add x21, x21, x5
.L66:
  b .L49
.L67:
  add x19, x19, x4
.L68:
  b .L41
.L69:
  mov x0, x21
  str x0, [sp, #192]
.L70:
  mov x0, x20
  str x0, [sp, #200]
.L71:
  mov x0, x19
  str x0, [sp, #208]
.L72:
  str d9, [sp, #216]
.L73:
  str d10, [sp, #224]
.L74:
  str d8, [sp, #232]
.L75:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #192]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #200]
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
  ldr x9, [sp, #208]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #216]
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
  ldr d0, [sp, #224]
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
  ldr d0, [sp, #232]
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
  ldp x21, x20, [sp, #240]
  ldr x19, [sp, #256]
  ldp d9, d10, [sp, #272]
  ldr d8, [sp, #288]
  ldr x29, [sp, #288]
  ldr x30, [sp, #296]
  add sp, sp, #304
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
.Lname_i:
  .asciz "i"
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_b
.align 3
_arr_b:
  .space 32776
.global _arr_w
.align 3
_arr_w:
  .space 8016
