.global _main
.align 2

_main:
  sub sp, sp, #288
  str x30, [sp, #280]
  str x29, [sp, #272]
  add x29, sp, #272
  // Save callee-saved registers
  str d12, [sp, #216]
  str d11, [sp, #224]
  str d10, [sp, #232]
  str d13, [sp, #240]
  str d9, [sp, #248]
  str d8, [sp, #256]

  // Initialize all variables to 0
  mov x0, #0

  mov x12, #0
  mov x11, #0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x10, #0
  fmov d13, x0
  fmov d9, x0
  mov x9, #0
  fmov d8, x0
  fmov d7, x0
  mov x8, #0
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
  mov x12, x0
.L1:
  mov x0, #0
  mov x11, x0
.L2:
  mov x0, #0
  fmov d12, x0
.L3:
  mov x0, #0
  fmov d11, x0
.L4:
  mov x0, #0
  fmov d10, x0
.L5:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L6:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L7:
  fadd d11, d3, d12
.L8:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L9:
  fmul d10, d3, d12
.L10:
  mov x0, #1
  mov x12, x0
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
  cmp x12, x4
  b.gt .L25
.L17:
  fsub d3, d6, d12
.L18:
  fmadd d11, d3, d11, d12
.L19:
  fsub d12, d5, d12
.L20:
  fsub d3, d11, d10
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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L26:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L27:
  fadd d11, d3, d12
.L28:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L29:
  fmul d10, d3, d12
.L30:
  mov x0, #1
  mov x12, x0
.L31:
  mov x0, #1001
  mov x4, x0
.L32:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L33:
  mov x0, #0
  fmov d5, x0
.L34:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L35:
  mov x0, #1
  mov x3, x0
.L36:
  cmp x12, x4
  b.gt .L45
.L37:
  fsub d3, d6, d12
.L38:
  fmadd d11, d3, d11, d12
.L39:
  fsub d12, d5, d12
.L40:
  fsub d3, d11, d10
.L41:
  fmul d3, d3, d4
.L42:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d3, [x0, x12, lsl #3]
.L43:
  add x12, x12, x3
.L44:
  b .L36
.L45:
  mov x0, #1
  mov x11, x0
.L46:
  movz x0, #36752
  movk x0, #118, lsl #16
  mov x10, x0
.L47:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d13, x0
.L48:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d9, x0
.L49:
  mov x0, #1001
  mov x9, x0
.L50:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L51:
  mov x0, #0
  fmov d7, x0
.L52:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L53:
  mov x0, #1
  mov x8, x0
.L54:
  mov x0, #1001
  mov x7, x0
.L55:
  mov x0, #1
  mov x6, x0
.L56:
  mov x0, #1
  mov x5, x0
.L57:
  mov x0, #1
  mov x4, x0
.L58:
  cmp x11, x10
  b.gt .L85
.L59:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L60:
  fadd d11, d13, d12
.L61:
  fmul d10, d9, d12
.L62:
  mov x0, #1
  mov x12, x0
.L63:
  cmp x12, x9
  b.gt .L72
.L64:
  fsub d3, d8, d12
.L65:
  fmadd d11, d3, d11, d12
.L66:
  fsub d12, d7, d12
.L67:
  fsub d3, d11, d10
.L68:
  fmul d3, d3, d6
.L69:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x12, lsl #3]
.L70:
  add x12, x12, x8
.L71:
  b .L63
.L72:
  mov x0, #2
  mov x12, x0
.L73:
  cmp x12, x7
  b.gt .L83
.L74:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d5, [x0, x12, lsl #3]
.L75:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d4, [x0, x12, lsl #3]
.L76:
  sub x3, x12, x6
.L77:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L78:
  fsub d3, d4, d3
.L79:
  fmul d3, d5, d3
.L80:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x12, lsl #3]
.L81:
  add x12, x12, x5
.L82:
  b .L73
.L83:
  add x11, x11, x4
.L84:
  b .L58
.L85:
  mov x0, #501
  mov x3, x0
.L86:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L87:
  str x12, [sp, #8]
  str x11, [sp, #16]
  str d3, [sp, #48]
  str x4, [sp, #56]
  str d6, [sp, #64]
  str d5, [sp, #72]
  str d4, [sp, #80]
  str x3, [sp, #88]
  str x10, [sp, #96]
  str x9, [sp, #120]
  str d7, [sp, #136]
  str x8, [sp, #144]
  str x7, [sp, #152]
  str x6, [sp, #160]
  str x5, [sp, #168]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_87@PAGE
  add x0, x0, .Lfmt_print_87@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x12, [sp, #8]
  ldr x11, [sp, #16]
  ldr d3, [sp, #48]
  ldr x4, [sp, #56]
  ldr d6, [sp, #64]
  ldr d5, [sp, #72]
  ldr d4, [sp, #80]
  ldr x3, [sp, #88]
  ldr x10, [sp, #96]
  ldr x9, [sp, #120]
  ldr d7, [sp, #136]
  ldr x8, [sp, #144]
  ldr x7, [sp, #152]
  ldr x6, [sp, #160]
  ldr x5, [sp, #168]
.L88:
  mov x0, x12
  str x0, [sp, #176]
.L89:
  mov x0, x11
  str x0, [sp, #184]
.L90:
  str d12, [sp, #192]
.L91:
  str d11, [sp, #200]
.L92:
  str d10, [sp, #208]
.L93:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #176]
  sub sp, sp, #16
  adrp x1, .Lname_i@PAGE
  add x1, x1, .Lname_i@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #184]
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
  ldr d0, [sp, #192]
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
  ldr d0, [sp, #200]
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
  ldr d0, [sp, #208]
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
  ldr d12, [sp, #216]
  ldr d11, [sp, #224]
  ldr d10, [sp, #232]
  ldr d13, [sp, #240]
  ldr d9, [sp, #248]
  ldr d8, [sp, #256]
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

.Lfmt_print_87:
  .asciz "%f\n"

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
