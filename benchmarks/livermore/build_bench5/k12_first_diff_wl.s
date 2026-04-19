.global _main
.align 2

_main:
  sub sp, sp, #208
  str x30, [sp, #200]
  str x29, [sp, #192]
  add x29, sp, #192
  // Save callee-saved registers
  str d9, [sp, #168]
  str d8, [sp, #176]

  // Initialize all variables to 0
  mov x0, #0

  mov x10, #0
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
  str x0, [sp, #120]
  str x0, [sp, #128]
  str x0, [sp, #136]
  str x0, [sp, #144]
  str x0, [sp, #152]
  str x0, [sp, #160]

.L0:
  mov x0, #0
  mov x10, x0
.L1:
  mov x0, #0
  mov x9, x0
.L2:
  mov x0, #0
  fmov d9, x0
.L3:
  mov x0, #0
  fmov d8, x0
.L4:
  mov x0, #0
  fmov d7, x0
.L5:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L6:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L7:
  fadd d8, d3, d9
.L8:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L9:
  fmul d7, d3, d9
.L10:
  mov x0, #1
  mov x10, x0
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
  cmp x10, x4
  b.gt .L25
.L17:
  fsub d3, d6, d9
.L18:
  fmadd d8, d3, d8, d9
.L19:
  fsub d9, d5, d9
.L20:
  fsub d3, d8, d7
.L21:
  fmul d3, d3, d4
.L22:
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x10, lsl #3]
.L23:
  add x10, x10, x3
.L24:
  b .L16
.L25:
  mov x0, #1
  mov x9, x0
.L26:
  movz x0, #35952
  movk x0, #543, lsl #16
  mov x7, x0
.L27:
  mov x0, #1000
  mov x6, x0
.L28:
  mov x0, #1
  mov x5, x0
.L29:
  mov x0, #1
  str x0, [sp, #120]
.L30:
  mov x0, #1
  mov x4, x0
.L31:
  cmp x9, x7
  b.gt .L43
.L32:
  mov x0, #1
  mov x10, x0
.L33:
  cmp x10, x6
  b.gt .L41
.L34:
  add x3, x10, x5
.L35:
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L36:
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d3, [x8, x10, lsl #3]
.L37:
  fsub d3, d4, d3
.L38:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x10, lsl #3]
.L39:
  mov x10, x3
.L40:
  b .L33
.L41:
  add x9, x9, x4
.L42:
  b .L31
.L43:
  mov x0, #1
  mov x3, x0
.L44:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L45:
  str d7, [sp, #40]
  str x9, [sp, #16]
  str x10, [sp, #8]
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d7, [sp, #40]
  ldr x9, [sp, #16]
  ldr x10, [sp, #8]
.L46:
  str x10, [sp, #128]
.L47:
  str x9, [sp, #136]
.L48:
  str d9, [sp, #144]
.L49:
  str d8, [sp, #152]
.L50:
  str d7, [sp, #160]
.L51:
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
  // print rep
  ldr x9, [sp, #136]
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
  ldr d9, [sp, #168]
  ldr d8, [sp, #176]
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
.global _arr_x
.align 3
_arr_x:
  .space 8016
