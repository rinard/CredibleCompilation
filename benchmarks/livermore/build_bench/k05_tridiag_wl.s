.global _main
.align 2

_main:
  sub sp, sp, #288
  str x30, [sp, #280]
  str x29, [sp, #272]
  add x29, sp, #272
  // Save callee-saved registers
  stp d13, d12, [sp, #216]
  stp d11, d10, [sp, #232]
  stp d9, d8, [sp, #248]

  // Initialize all variables to 0
  mov x0, #0

  mov x13, #0
  mov x12, #0
  fmov d13, x0
  fmov d12, x0
  fmov d11, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x11, #0
  fmov d10, x0
  fmov d9, x0
  mov x10, #0
  fmov d8, x0
  fmov d7, x0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  str x0, [sp, #200]
  str x0, [sp, #208]

.L0:
  mov x0, #0
  mov x13, x0
.L1:
  mov x0, #0
  mov x12, x0
.L2:
  mov x0, #0
  fmov d13, x0
.L3:
  mov x0, #0
  fmov d12, x0
.L4:
  mov x0, #0
  fmov d11, x0
.L5:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d13, x0
.L6:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L7:
  fadd d12, d3, d13
.L8:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L9:
  fmul d11, d3, d13
.L10:
  mov x0, #1
  mov x13, x0
.L11:
  mov x0, #1001
  mov x4, x0
.L12:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L13:
  mov x0, #0
  fmov d5, x0
.L14:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L15:
  mov x0, #1
  mov x3, x0
.L16:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L26
.L17:
  fsub d3, d6, d13
.L18:
  fmul d3, d3, d12
.L19:
  fadd d12, d3, d13
.L20:
  fsub d13, d5, d13
.L21:
  fsub d3, d12, d11
.L22:
  fmul d3, d3, d4
.L23:
  mov x1, x13
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L24:
  add x13, x13, x3
.L25:
  b .L16
.L26:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d13, x0
.L27:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L28:
  fadd d12, d3, d13
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L30:
  fmul d11, d3, d13
.L31:
  mov x0, #1
  mov x13, x0
.L32:
  mov x0, #1001
  mov x4, x0
.L33:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L34:
  mov x0, #0
  fmov d5, x0
.L35:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L36:
  mov x0, #1
  mov x3, x0
.L37:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L47
.L38:
  fsub d3, d6, d13
.L39:
  fmul d3, d3, d12
.L40:
  fadd d12, d3, d13
.L41:
  fsub d13, d5, d13
.L42:
  fsub d3, d12, d11
.L43:
  fmul d3, d3, d4
.L44:
  mov x1, x13
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L45:
  add x13, x13, x3
.L46:
  b .L37
.L47:
  mov x0, #1
  mov x12, x0
.L48:
  movz x0, #36752
  movk x0, #118, lsl #16
  mov x11, x0
.L49:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L50:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d9, x0
.L51:
  mov x0, #1001
  mov x10, x0
.L52:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L53:
  mov x0, #0
  fmov d7, x0
.L54:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L55:
  mov x0, #1
  mov x9, x0
.L56:
  mov x0, #1001
  mov x7, x0
.L57:
  mov x0, #1
  mov x6, x0
.L58:
  mov x0, #1
  mov x5, x0
.L59:
  mov x0, #1
  mov x4, x0
.L60:
  mov x1, x12
  mov x2, x11
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L88
.L61:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d13, x0
.L62:
  fadd d12, d10, d13
.L63:
  fmul d11, d9, d13
.L64:
  mov x0, #1
  mov x13, x0
.L65:
  mov x1, x13
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L75
.L66:
  fsub d3, d8, d13
.L67:
  fmul d3, d3, d12
.L68:
  fadd d12, d3, d13
.L69:
  fsub d13, d7, d13
.L70:
  fsub d3, d12, d11
.L71:
  fmul d3, d3, d6
.L72:
  mov x1, x13
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L73:
  add x13, x13, x9
.L74:
  b .L65
.L75:
  mov x0, #2
  mov x13, x0
.L76:
  mov x1, x13
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L86
.L77:
  mov x1, x13
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d5, [x8, x1, lsl #3]
.L78:
  mov x1, x13
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L79:
  sub x3, x13, x6
.L80:
  mov x1, x3
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L81:
  fsub d3, d4, d3
.L82:
  fmul d3, d5, d3
.L83:
  mov x1, x13
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L84:
  add x13, x13, x5
.L85:
  b .L76
.L86:
  add x12, x12, x4
.L87:
  b .L60
.L88:
  mov x0, x13
  str x0, [sp, #176]
.L89:
  mov x0, x12
  str x0, [sp, #184]
.L90:
  str d13, [sp, #192]
.L91:
  str d12, [sp, #200]
.L92:
  str d11, [sp, #208]
.L93:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #176]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #184]
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
  ldr d0, [sp, #192]
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
  ldr d0, [sp, #200]
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
  ldr d0, [sp, #208]
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
  ldp d13, d12, [sp, #216]
  ldp d11, d10, [sp, #232]
  ldp d9, d8, [sp, #248]
  ldr x29, [sp, #272]
  ldr x30, [sp, #280]
  add sp, sp, #288
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
.Lname_rep:
  .asciz "rep"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
