.global _main
.align 2

_main:
  sub sp, sp, #288
  str x30, [sp, #280]
  str x29, [sp, #272]
  add x29, sp, #272
  // Save callee-saved registers
  str x19, [sp, #240]
  str d10, [sp, #248]
  str d9, [sp, #256]
  str d8, [sp, #264]

  // Initialize all variables to 0
  mov x0, #0

  mov x19, #0
  mov x15, #0
  mov x14, #0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x13, #0
  mov x12, #0
  fmov d7, x0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x8, #0
  str x0, [sp, #160]
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
  mov x19, x0
.L1:
  mov x0, #0
  mov x15, x0
.L2:
  mov x0, #0
  mov x14, x0
.L3:
  mov x0, #0
  fmov d10, x0
.L4:
  mov x0, #0
  fmov d9, x0
.L5:
  mov x0, #0
  fmov d8, x0
.L6:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L8:
  fadd d9, d3, d10
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L10:
  fmul d8, d3, d10
.L11:
  mov x0, #1
  mov x15, x0
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
  cmp x15, x4
  b.gt .L26
.L18:
  fsub d3, d6, d10
.L19:
  fmadd d9, d3, d9, d10
.L20:
  fsub d10, d5, d10
.L21:
  fsub d3, d9, d8
.L22:
  fmul d3, d3, d4
.L23:
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L24:
  add x15, x15, x3
.L25:
  b .L17
.L26:
  mov x0, #1
  mov x14, x0
.L27:
  movz x0, #28488
  movk x0, #42, lsl #16
  mov x13, x0
.L28:
  mov x0, #1001
  mov x12, x0
.L29:
  mov x0, #0
  fmov d7, x0
.L30:
  mov x0, #1
  mov x11, x0
.L31:
  mov x0, #1
  mov x10, x0
.L32:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d6, x0
.L33:
  mov x0, #64
  mov x9, x0
.L34:
  mov x0, #1
  mov x8, x0
.L35:
  mov x0, #1
  str x0, [sp, #160]
.L36:
  mov x0, #64
  mov x7, x0
.L37:
  mov x0, #1
  mov x6, x0
.L38:
  mov x0, #1
  mov x5, x0
.L39:
  mov x0, #1
  mov x4, x0
.L40:
  cmp x14, x13
  b.gt .L67
.L41:
  mov x0, #1
  mov x19, x0
.L42:
  cmp x19, x12
  b.gt .L46
.L43:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d7, [x0, x19, lsl #3]
.L44:
  add x19, x19, x11
.L45:
  b .L42
.L46:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d6, [x0, x10, lsl #3]
.L47:
  mov x0, #2
  mov x19, x0
.L48:
  cmp x19, x9
  b.gt .L65
.L49:
  mov x0, #1
  mov x15, x0
.L50:
  sub x3, x19, x8
.L51:
  cmp x15, x3
  b.gt .L63
.L52:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d5, [x0, x19, lsl #3]
.L53:
  mov x0, x3
  mov x3, x0
.L54:
  mul x3, x3, x7
.L55:
  add x3, x3, x15
.L56:
  mov x0, #4097
  cmp x3, x0
  b.hs .Lbounds_err
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L57:
  sub x3, x19, x15
.L58:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L59:
  fmadd d3, d4, d3, d5
.L60:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d3, [x0, x19, lsl #3]
.L61:
  add x15, x15, x6
.L62:
  b .L50
.L63:
  add x19, x19, x5
.L64:
  b .L48
.L65:
  add x14, x14, x4
.L66:
  b .L40
.L67:
  mov x0, #64
  mov x3, x0
.L68:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L69:
  str x15, [sp, #16]
  str x14, [sp, #24]
  str d3, [sp, #56]
  str x4, [sp, #64]
  str d6, [sp, #72]
  str d5, [sp, #80]
  str d4, [sp, #88]
  str x3, [sp, #96]
  str x13, [sp, #104]
  str x12, [sp, #112]
  str d7, [sp, #120]
  str x11, [sp, #128]
  str x10, [sp, #136]
  str x9, [sp, #144]
  str x8, [sp, #152]
  str x7, [sp, #168]
  str x6, [sp, #176]
  str x5, [sp, #184]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_69@PAGE
  add x0, x0, .Lfmt_print_69@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x15, [sp, #16]
  ldr x14, [sp, #24]
  ldr d3, [sp, #56]
  ldr x4, [sp, #64]
  ldr d6, [sp, #72]
  ldr d5, [sp, #80]
  ldr d4, [sp, #88]
  ldr x3, [sp, #96]
  ldr x13, [sp, #104]
  ldr x12, [sp, #112]
  ldr d7, [sp, #120]
  ldr x11, [sp, #128]
  ldr x10, [sp, #136]
  ldr x9, [sp, #144]
  ldr x8, [sp, #152]
  ldr x7, [sp, #168]
  ldr x6, [sp, #176]
  ldr x5, [sp, #184]
.L70:
  mov x0, x19
  str x0, [sp, #192]
.L71:
  mov x0, x15
  str x0, [sp, #200]
.L72:
  mov x0, x14
  str x0, [sp, #208]
.L73:
  str d10, [sp, #216]
.L74:
  str d9, [sp, #224]
.L75:
  str d8, [sp, #232]
.L76:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #192]
  sub sp, sp, #16
  adrp x1, .Lname_i@PAGE
  add x1, x1, .Lname_i@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #200]
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
  ldr x9, [sp, #208]
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
  ldr d0, [sp, #216]
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
  ldr d0, [sp, #224]
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
  ldr d0, [sp, #232]
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
  ldr x19, [sp, #240]
  ldr d10, [sp, #248]
  ldr d9, [sp, #256]
  ldr d8, [sp, #264]
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

.Lfmt_print_69:
  .asciz "%f\n"

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
