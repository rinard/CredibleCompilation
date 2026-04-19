.global _main
.align 2

_main:
  sub sp, sp, #208
  str x30, [sp, #200]
  str x29, [sp, #192]
  add x29, sp, #192
  // Save callee-saved registers
  stp d8, d9, [sp, #176]

  // Initialize all variables to 0
  mov x0, #0

  mov x10, #0
  mov x11, #0
  mov x9, #0
  fmov d8, x0
  fmov d9, x0
  fmov d7, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #128]
  str x0, [sp, #136]
  str x0, [sp, #144]
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]

.L0:
  mov x0, #0
  mov x10, x0
.L1:
  mov x0, #0
  mov x11, x0
.L2:
  mov x0, #0
  mov x9, x0
.L3:
  mov x0, #0
  fmov d8, x0
.L4:
  mov x0, #0
  fmov d9, x0
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
  fadd d9, d3, d8
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
  mov x10, x0
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
  mov x1, x10
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L27
.L18:
  fsub d3, d6, d8
.L19:
  fmul d3, d3, d9
.L20:
  fadd d9, d3, d8
.L21:
  fsub d8, d5, d8
.L22:
  fsub d3, d9, d7
.L23:
  fmul d3, d3, d4
.L24:
  mov x1, x10
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L25:
  add x10, x10, x3
.L26:
  b .L17
.L27:
  mov x0, #1
  mov x9, x0
.L28:
  movz x0, #55224
  movk x0, #466, lsl #16
  mov x7, x0
.L29:
  mov x0, #501
  mov x6, x0
.L30:
  mov x0, #0
  fmov d6, x0
.L31:
  movz x0, #0
  movk x0, #8192, lsl #16
  movk x0, #41055, lsl #32
  movk x0, #16898, lsl #48
  fmov d5, x0
.L32:
  mov x0, #1001
  mov x5, x0
.L33:
  mov x0, #1
  mov x4, x0
.L34:
  mov x0, #1
  mov x3, x0
.L35:
  mov x1, x9
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L50
.L36:
  fsub d3, d6, d5
.L37:
  mov x1, x6
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L38:
  mov x0, #1
  mov x11, x0
.L39:
  mov x0, #2
  mov x10, x0
.L40:
  mov x1, x10
  mov x2, x5
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L48
.L41:
  mov x1, x10
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L42:
  mov x1, x11
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L43:
  fmov d1, d4
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L45
.L44:
  b .L46
.L45:
  mov x0, x10
  mov x11, x0
.L46:
  add x10, x10, x4
.L47:
  b .L40
.L48:
  add x9, x9, x3
.L49:
  b .L35
.L50:
  mov x0, x10
  str x0, [sp, #128]
.L51:
  mov x0, x11
  str x0, [sp, #136]
.L52:
  mov x0, x9
  str x0, [sp, #144]
.L53:
  str d8, [sp, #152]
.L54:
  str d9, [sp, #160]
.L55:
  str d7, [sp, #168]
.L56:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #128]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print m
  ldr x9, [sp, #136]
  sub sp, sp, #16
  adrp x8, .Lname_m@PAGE
  add x8, x8, .Lname_m@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #144]
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
  ldr d0, [sp, #152]
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
  ldr d0, [sp, #160]
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
  ldr d0, [sp, #168]
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
  ldp d8, d9, [sp, #176]
  ldr x29, [sp, #192]
  ldr x30, [sp, #200]
  add sp, sp, #208
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
.Lname_m:
  .asciz "m"
.Lname_rep:
  .asciz "rep"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_x
.align 3
_arr_x:
  .space 8016
