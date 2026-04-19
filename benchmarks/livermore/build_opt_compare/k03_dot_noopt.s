.global _main
.align 2

_main:
  sub sp, sp, #304
  str x30, [sp, #296]
  str x29, [sp, #288]
  add x29, sp, #288

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  str x0, [sp, #40]
  str x0, [sp, #48]
  str x0, [sp, #56]
  str x0, [sp, #64]
  str x0, [sp, #72]
  str x0, [sp, #80]
  str x0, [sp, #88]
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]
  str x0, [sp, #120]
  str x0, [sp, #128]
  str x0, [sp, #136]
  str x0, [sp, #144]
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  str x0, [sp, #200]
  str x0, [sp, #208]
  str x0, [sp, #216]
  str x0, [sp, #224]
  str x0, [sp, #232]
  str x0, [sp, #240]
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]
  str x0, [sp, #272]
  str x0, [sp, #280]

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #24]
.L3:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #32]
.L4:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #40]
.L5:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #48]
.L6:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L8:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L10:
  ldr d1, [sp, #64]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #48]
.L11:
  mov x0, #1
  str x0, [sp, #8]
.L12:
  mov x0, #1001
  str x0, [sp, #72]
.L13:
  ldr x1, [sp, #8]
  ldr x2, [sp, #72]
  cmp x1, x2
  b.gt .L27
.L14:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #80]
.L15:
  ldr d1, [sp, #80]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #88]
.L16:
  ldr d1, [sp, #88]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #96]
.L17:
  ldr d1, [sp, #96]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L18:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #104]
.L19:
  ldr d1, [sp, #104]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L20:
  ldr d1, [sp, #40]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #112]
.L21:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #120]
.L22:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fmul d0, d1, d2
  str d0, [sp, #128]
.L23:
  ldr x1, [sp, #8]
  ldr d0, [sp, #128]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L24:
  mov x0, #1
  str x0, [sp, #136]
.L25:
  ldr x1, [sp, #8]
  ldr x2, [sp, #136]
  add x0, x1, x2
  str x0, [sp, #8]
.L26:
  b .L12
.L27:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L28:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #144]
.L29:
  ldr d1, [sp, #144]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L30:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #152]
.L31:
  ldr d1, [sp, #152]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #48]
.L32:
  mov x0, #1
  str x0, [sp, #8]
.L33:
  mov x0, #1001
  str x0, [sp, #160]
.L34:
  ldr x1, [sp, #8]
  ldr x2, [sp, #160]
  cmp x1, x2
  b.gt .L48
.L35:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #168]
.L36:
  ldr d1, [sp, #168]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #176]
.L37:
  ldr d1, [sp, #176]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #184]
.L38:
  ldr d1, [sp, #184]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L39:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #192]
.L40:
  ldr d1, [sp, #192]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L41:
  ldr d1, [sp, #40]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #200]
.L42:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #208]
.L43:
  ldr d1, [sp, #200]
  ldr d2, [sp, #208]
  fmul d0, d1, d2
  str d0, [sp, #216]
.L44:
  ldr x1, [sp, #8]
  ldr d0, [sp, #216]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L45:
  mov x0, #1
  str x0, [sp, #224]
.L46:
  ldr x1, [sp, #8]
  ldr x2, [sp, #224]
  add x0, x1, x2
  str x0, [sp, #8]
.L47:
  b .L33
.L48:
  mov x0, #1
  str x0, [sp, #16]
.L49:
  movz x0, #6576
  movk x0, #484, lsl #16
  str x0, [sp, #232]
.L50:
  ldr x1, [sp, #16]
  ldr x2, [sp, #232]
  cmp x1, x2
  b.gt .L65
.L51:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #24]
.L52:
  mov x0, #1
  str x0, [sp, #8]
.L53:
  mov x0, #1001
  str x0, [sp, #240]
.L54:
  ldr x1, [sp, #8]
  ldr x2, [sp, #240]
  cmp x1, x2
  b.gt .L62
.L55:
  ldr x1, [sp, #8]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #248]
.L56:
  ldr x1, [sp, #8]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #256]
.L57:
  ldr d1, [sp, #248]
  ldr d2, [sp, #256]
  fmul d0, d1, d2
  str d0, [sp, #264]
.L58:
  ldr d1, [sp, #24]
  ldr d2, [sp, #264]
  fadd d0, d1, d2
  str d0, [sp, #24]
.L59:
  mov x0, #1
  str x0, [sp, #272]
.L60:
  ldr x1, [sp, #8]
  ldr x2, [sp, #272]
  add x0, x1, x2
  str x0, [sp, #8]
.L61:
  b .L53
.L62:
  mov x0, #1
  str x0, [sp, #280]
.L63:
  ldr x1, [sp, #16]
  ldr x2, [sp, #280]
  add x0, x1, x2
  str x0, [sp, #16]
.L64:
  b .L49
.L65:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #24]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_65@PAGE
  add x0, x0, .Lfmt_print_65@PAGEOFF
  bl _printf
  add sp, sp, #16
.L66:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #8]
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
  ldr x9, [sp, #16]
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
  ldr d0, [sp, #24]
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
  ldr d0, [sp, #32]
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
  ldr d0, [sp, #40]
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
  ldr d0, [sp, #48]
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

.Lfmt_print_65:
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
