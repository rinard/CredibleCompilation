.global _main
.align 2

_main:
  sub sp, sp, #208
  str x30, [sp, #200]
  str x29, [sp, #192]
  add x29, sp, #192
  // Save callee-saved registers
  str d8, [sp, #168]
  str d9, [sp, #176]
  str d10, [sp, #184]

  // Initialize all variables to 0
  mov x0, #0

  mov x8, #0
  mov x7, #0
  fmov d8, x0
  fmov d7, x0
  fmov d9, x0
  fmov d10, x0
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
  mov x8, x0
.L1:
  mov x0, #0
  mov x7, x0
.L2:
  mov x0, #0
  fmov d8, x0
.L3:
  mov x0, #0
  fmov d7, x0
.L4:
  mov x0, #0
  fmov d9, x0
.L5:
  mov x0, #0
  fmov d10, x0
.L6:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L8:
  fadd d9, d3, d7
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L10:
  fmul d10, d3, d7
.L11:
  mov x0, #1
  mov x8, x0
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
  cmp x8, x4
  b.gt .L26
.L18:
  fsub d3, d6, d7
.L19:
  fmadd d9, d3, d9, d7
.L20:
  fsub d7, d5, d7
.L21:
  fsub d3, d9, d10
.L22:
  fmul d3, d3, d4
.L23:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d3, [x0, x8, lsl #3]
.L24:
  add x8, x8, x3
.L25:
  b .L17
.L26:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L27:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L28:
  fadd d9, d3, d7
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L30:
  fmul d10, d3, d7
.L31:
  mov x0, #1
  mov x8, x0
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
  cmp x8, x4
  b.gt .L46
.L38:
  fsub d3, d6, d7
.L39:
  fmadd d9, d3, d9, d7
.L40:
  fsub d7, d5, d7
.L41:
  fsub d3, d9, d10
.L42:
  fmul d3, d3, d4
.L43:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x8, lsl #3]
.L44:
  add x8, x8, x3
.L45:
  b .L37
.L46:
  mov x0, #1
  mov x7, x0
.L47:
  movz x0, #6576
  movk x0, #484, lsl #16
  mov x6, x0
.L48:
  mov x0, #1001
  mov x5, x0
.L49:
  mov x0, #1
  mov x4, x0
.L50:
  mov x0, #1
  mov x3, x0
.L51:
  cmp x7, x6
  b.gt .L62
.L52:
  mov x0, #0
  fmov d8, x0
.L53:
  mov x0, #1
  mov x8, x0
.L54:
  cmp x8, x5
  b.gt .L60
.L55:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d4, [x0, x8, lsl #3]
.L56:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x8, lsl #3]
.L57:
  fmadd d8, d4, d3, d8
.L58:
  add x8, x8, x4
.L59:
  b .L54
.L60:
  add x7, x7, x3
.L61:
  b .L51
.L62:
  str x8, [sp, #8]
  str x7, [sp, #16]
  str d7, [sp, #32]
  str d3, [sp, #56]
  str x4, [sp, #64]
  str d6, [sp, #72]
  str d5, [sp, #80]
  str d4, [sp, #88]
  str x3, [sp, #96]
  str x6, [sp, #104]
  str x5, [sp, #112]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d8
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_62@PAGE
  add x0, x0, .Lfmt_print_62@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x8, [sp, #8]
  ldr x7, [sp, #16]
  ldr d7, [sp, #32]
  ldr d3, [sp, #56]
  ldr x4, [sp, #64]
  ldr d6, [sp, #72]
  ldr d5, [sp, #80]
  ldr d4, [sp, #88]
  ldr x3, [sp, #96]
  ldr x6, [sp, #104]
  ldr x5, [sp, #112]
.L63:
  mov x0, x8
  str x0, [sp, #120]
.L64:
  mov x0, x7
  str x0, [sp, #128]
.L65:
  str d8, [sp, #136]
.L66:
  str d7, [sp, #144]
.L67:
  str d9, [sp, #152]
.L68:
  str d10, [sp, #160]
.L69:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #120]
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
  ldr x9, [sp, #128]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print q (float)
  ldr d0, [sp, #136]
  sub sp, sp, #32
  adrp x1, .Lname_q@PAGE
  add x1, x1, .Lname_q@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #144]
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
  ldr d0, [sp, #152]
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
  ldr d0, [sp, #160]
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
  ldr d8, [sp, #168]
  ldr d9, [sp, #176]
  ldr d10, [sp, #184]
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

.Lfmt_print_62:
  .asciz "%f\n"

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
