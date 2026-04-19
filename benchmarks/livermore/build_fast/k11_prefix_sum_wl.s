.global _main
.align 2

_main:
  sub sp, sp, #224
  str x30, [sp, #216]
  str x29, [sp, #208]
  add x29, sp, #208
  // Save callee-saved registers
  str d8, [sp, #184]
  str d9, [sp, #192]

  // Initialize all variables to 0
  mov x0, #0

  mov x12, #0
  mov x11, #0
  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  fmov d3, x0
  mov x4, #0
  fmov d9, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x10, #0
  mov x9, #0
  mov x8, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #144]
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]

.L0:
  mov x0, #0
  mov x12, x0
.L1:
  mov x0, #0
  mov x11, x0
.L2:
  mov x0, #0
  fmov d8, x0
.L3:
  mov x0, #0
  fmov d7, x0
.L4:
  mov x0, #0
  fmov d6, x0
.L5:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L6:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L7:
  fadd d7, d3, d8
.L8:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L9:
  fmul d6, d3, d8
.L10:
  mov x0, #1
  mov x12, x0
.L11:
  mov x0, #1001
  mov x4, x0
.L12:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d9, x0
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
  cmp x12, x4
  b.gt .L25
.L17:
  fsub d3, d9, d8
.L18:
  fmadd d7, d3, d7, d8
.L19:
  fsub d8, d5, d8
.L20:
  fsub d3, d7, d6
.L21:
  fmul d3, d3, d4
.L22:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d3, [x0, x12, lsl #3]
.L23:
  add x12, x12, x3
.L24:
  b .L16
.L25:
  mov x0, #1
  mov x11, x0
.L26:
  mov x0, #35249
  mov x10, x0
.L27:
  mov x0, #1
  mov x9, x0
.L28:
  mov x0, #1
  mov x8, x0
.L29:
  mov x0, #1001
  mov x7, x0
.L30:
  mov x0, #1
  mov x6, x0
.L31:
  mov x0, #1
  mov x5, x0
.L32:
  mov x0, #1
  mov x4, x0
.L33:
  cmp x11, x10
  b.gt .L47
.L34:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d3, [x0, x8, lsl #3]
.L35:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x9, lsl #3]
.L36:
  mov x0, #2
  mov x12, x0
.L37:
  cmp x12, x7
  b.gt .L45
.L38:
  sub x3, x12, x6
.L39:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L40:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d3, [x0, x12, lsl #3]
.L41:
  fadd d3, d4, d3
.L42:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x12, lsl #3]
.L43:
  add x12, x12, x5
.L44:
  b .L37
.L45:
  add x11, x11, x4
.L46:
  b .L33
.L47:
  mov x0, #1001
  mov x3, x0
.L48:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L49:
  str x12, [sp, #8]
  str x11, [sp, #16]
  str d7, [sp, #32]
  str d6, [sp, #40]
  str d3, [sp, #48]
  str x4, [sp, #56]
  str d5, [sp, #72]
  str d4, [sp, #80]
  str x3, [sp, #88]
  str x10, [sp, #96]
  str x9, [sp, #104]
  str x8, [sp, #112]
  str x7, [sp, #120]
  str x6, [sp, #128]
  str x5, [sp, #136]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_49@PAGE
  add x0, x0, .Lfmt_print_49@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x12, [sp, #8]
  ldr x11, [sp, #16]
  ldr d7, [sp, #32]
  ldr d6, [sp, #40]
  ldr d3, [sp, #48]
  ldr x4, [sp, #56]
  ldr d5, [sp, #72]
  ldr d4, [sp, #80]
  ldr x3, [sp, #88]
  ldr x10, [sp, #96]
  ldr x9, [sp, #104]
  ldr x8, [sp, #112]
  ldr x7, [sp, #120]
  ldr x6, [sp, #128]
  ldr x5, [sp, #136]
.L50:
  mov x0, x12
  str x0, [sp, #144]
.L51:
  mov x0, x11
  str x0, [sp, #152]
.L52:
  str d8, [sp, #160]
.L53:
  str d7, [sp, #168]
.L54:
  str d6, [sp, #176]
.L55:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #144]
  sub sp, sp, #16
  adrp x1, .Lname_k@PAGE
  add x1, x1, .Lname_k@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #152]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #160]
  sub sp, sp, #32
  adrp x1, .Lname_fuzz@PAGE
  add x1, x1, .Lname_fuzz@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print buzz (float)
  ldr d0, [sp, #168]
  sub sp, sp, #32
  adrp x1, .Lname_buzz@PAGE
  add x1, x1, .Lname_buzz@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fizz (float)
  ldr d0, [sp, #176]
  sub sp, sp, #32
  adrp x1, .Lname_fizz@PAGE
  add x1, x1, .Lname_fizz@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32

  // Exit with code 0
  mov x0, #0
  // Restore callee-saved registers
  ldr d8, [sp, #184]
  ldr d9, [sp, #192]
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

.Lfmt_print_49:
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
