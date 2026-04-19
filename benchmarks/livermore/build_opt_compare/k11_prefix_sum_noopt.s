.global _main
.align 2

_main:
  sub sp, sp, #272
  str x30, [sp, #264]
  str x29, [sp, #256]
  add x29, sp, #256

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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #24]
.L6:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L7:
  ldr d1, [sp, #48]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L8:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L9:
  ldr d1, [sp, #56]
  ldr d2, [sp, #24]
  fmul d0, d1, d2
  str d0, [sp, #40]
.L10:
  mov x0, #1
  str x0, [sp, #8]
.L11:
  mov x0, #1001
  str x0, [sp, #64]
.L12:
  ldr x1, [sp, #8]
  ldr x2, [sp, #64]
  cmp x1, x2
  b.gt .L26
.L13:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L14:
  ldr d1, [sp, #72]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #80]
.L15:
  ldr d1, [sp, #80]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L16:
  ldr d1, [sp, #88]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L17:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #96]
.L18:
  ldr d1, [sp, #96]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #24]
.L19:
  ldr d1, [sp, #32]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #104]
.L20:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #112]
.L21:
  ldr d1, [sp, #104]
  ldr d2, [sp, #112]
  fmul d0, d1, d2
  str d0, [sp, #120]
.L22:
  ldr x1, [sp, #8]
  ldr d0, [sp, #120]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L23:
  mov x0, #1
  str x0, [sp, #128]
.L24:
  ldr x1, [sp, #8]
  ldr x2, [sp, #128]
  add x0, x1, x2
  str x0, [sp, #8]
.L25:
  b .L11
.L26:
  mov x0, #1
  str x0, [sp, #16]
.L27:
  movz x0, #56168
  movk x0, #537, lsl #16
  str x0, [sp, #136]
.L28:
  ldr x1, [sp, #16]
  ldr x2, [sp, #136]
  cmp x1, x2
  b.gt .L48
.L29:
  mov x0, #1
  str x0, [sp, #144]
.L30:
  mov x0, #1
  str x0, [sp, #152]
.L31:
  ldr x1, [sp, #152]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #160]
.L32:
  ldr x1, [sp, #144]
  ldr d0, [sp, #160]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L33:
  mov x0, #2
  str x0, [sp, #8]
.L34:
  mov x0, #1001
  str x0, [sp, #168]
.L35:
  ldr x1, [sp, #8]
  ldr x2, [sp, #168]
  cmp x1, x2
  b.gt .L45
.L36:
  mov x0, #1
  str x0, [sp, #176]
.L37:
  ldr x1, [sp, #8]
  ldr x2, [sp, #176]
  sub x0, x1, x2
  str x0, [sp, #184]
.L38:
  ldr x1, [sp, #184]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #192]
.L39:
  ldr x1, [sp, #8]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #200]
.L40:
  ldr d1, [sp, #192]
  ldr d2, [sp, #200]
  fadd d0, d1, d2
  str d0, [sp, #208]
.L41:
  ldr x1, [sp, #8]
  ldr d0, [sp, #208]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L42:
  mov x0, #1
  str x0, [sp, #216]
.L43:
  ldr x1, [sp, #8]
  ldr x2, [sp, #216]
  add x0, x1, x2
  str x0, [sp, #8]
.L44:
  b .L34
.L45:
  mov x0, #1
  str x0, [sp, #224]
.L46:
  ldr x1, [sp, #16]
  ldr x2, [sp, #224]
  add x0, x1, x2
  str x0, [sp, #16]
.L47:
  b .L27
.L48:
  mov x0, #1001
  str x0, [sp, #232]
.L49:
  ldr x1, [sp, #232]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #240]
.L50:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #240]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_50@PAGE
  add x0, x0, .Lfmt_print_50@PAGEOFF
  bl _printf
  add sp, sp, #16
.L51:
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
  // print fuzz (float)
  ldr d0, [sp, #24]
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
  ldr d0, [sp, #32]
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
  ldr d0, [sp, #40]
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
  ldr x29, [sp, #256]
  ldr x30, [sp, #264]
  add sp, sp, #272
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

.Lfmt_print_50:
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
