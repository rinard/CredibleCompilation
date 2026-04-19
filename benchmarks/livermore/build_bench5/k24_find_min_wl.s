.global _main
.align 2

_main:
  sub sp, sp, #208
  str x30, [sp, #200]
  str x29, [sp, #192]
  add x29, sp, #192
  // Save callee-saved registers
  str d9, [sp, #176]
  str d8, [sp, #184]

  // Initialize all variables to 0
  mov x0, #0

  mov x10, #0
  mov x11, #0
  mov x9, #0
  fmov d9, x0
  fmov d8, x0
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
  fmov d9, x0
.L4:
  mov x0, #0
  fmov d8, x0
.L5:
  mov x0, #0
  fmov d7, x0
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
  fadd d8, d3, d9
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L10:
  fmul d7, d3, d9
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
  cmp x10, x4
  b.gt .L26
.L18:
  fsub d3, d6, d9
.L19:
  fmadd d8, d3, d8, d9
.L20:
  fsub d9, d5, d9
.L21:
  fsub d3, d8, d7
.L22:
  fmul d3, d3, d4
.L23:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x10, lsl #3]
.L24:
  add x10, x10, x3
.L25:
  b .L17
.L26:
  mov x0, #1
  mov x9, x0
.L27:
  movz x0, #55224
  movk x0, #466, lsl #16
  mov x7, x0
.L28:
  mov x0, #501
  mov x6, x0
.L29:
  mov x0, #0
  fmov d6, x0
.L30:
  movz x0, #0
  movk x0, #8192, lsl #16
  movk x0, #41055, lsl #32
  movk x0, #16898, lsl #48
  fmov d5, x0
.L31:
  mov x0, #1001
  mov x5, x0
.L32:
  mov x0, #1
  mov x4, x0
.L33:
  mov x0, #1
  mov x3, x0
.L34:
  cmp x9, x7
  b.gt .L49
.L35:
  fsub d3, d6, d5
.L36:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x6, lsl #3]
.L37:
  mov x0, #1
  mov x11, x0
.L38:
  mov x0, #2
  mov x10, x0
.L39:
  cmp x10, x5
  b.gt .L47
.L40:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d4, [x8, x10, lsl #3]
.L41:
  cmp x11, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x11, lsl #3]
.L42:
  fmov d1, d4
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L44
.L43:
  b .L45
.L44:
  mov x11, x10
.L45:
  add x10, x10, x4
.L46:
  b .L39
.L47:
  add x9, x9, x3
.L48:
  b .L34
.L49:
  str d7, [sp, #48]
  str x9, [sp, #24]
  str x10, [sp, #8]
  str x11, [sp, #16]
  // printint __x11
  mov x1, x11
  sub sp, sp, #16
  str x1, [sp]
  adrp x0, .Lfmt_printint@PAGE
  add x0, x0, .Lfmt_printint@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d7, [sp, #48]
  ldr x9, [sp, #24]
  ldr x10, [sp, #8]
  ldr x11, [sp, #16]
.L50:
  cmp x11, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x11, lsl #3]
.L51:
  str d7, [sp, #48]
  str x9, [sp, #24]
  str x11, [sp, #16]
  str x10, [sp, #8]
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d7, [sp, #48]
  ldr x9, [sp, #24]
  ldr x11, [sp, #16]
  ldr x10, [sp, #8]
.L52:
  str x10, [sp, #128]
.L53:
  str x11, [sp, #136]
.L54:
  str x9, [sp, #144]
.L55:
  str d9, [sp, #152]
.L56:
  str d8, [sp, #160]
.L57:
  str d7, [sp, #168]
.L58:
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
  ldr d9, [sp, #176]
  ldr d8, [sp, #184]
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
.Lfmt_printint:
  .asciz "%ld\n"
.Lfmt_printfloat:
  .asciz "%f\n"
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
