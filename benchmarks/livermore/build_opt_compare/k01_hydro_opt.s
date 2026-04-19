.global _main
.align 2

_main:
  sub sp, sp, #288
  str x30, [sp, #280]
  str x29, [sp, #272]
  add x29, sp, #272
  // Save callee-saved registers
  str d8, [sp, #224]
  str d11, [sp, #232]
  str d10, [sp, #240]
  str d9, [sp, #248]
  str d12, [sp, #256]

  // Initialize all variables to 0
  mov x0, #0

  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  mov x11, #0
  mov x10, #0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d3, x0
  mov x4, #0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  fmov d12, x0
  mov x9, #0
  mov x8, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  str x0, [sp, #200]
  str x0, [sp, #208]
  str x0, [sp, #216]

.L0:
  mov x0, #0
  fmov d8, x0
.L1:
  mov x0, #0
  fmov d7, x0
.L2:
  mov x0, #0
  fmov d6, x0
.L3:
  mov x0, #0
  mov x11, x0
.L4:
  mov x0, #0
  mov x10, x0
.L5:
  mov x0, #0
  fmov d11, x0
.L6:
  mov x0, #0
  fmov d10, x0
.L7:
  mov x0, #0
  fmov d9, x0
.L8:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L10:
  fadd d10, d3, d11
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L12:
  fmul d9, d3, d11
.L13:
  mov x0, #1
  mov x11, x0
.L14:
  mov x0, #39
  mov x4, x0
.L15:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L16:
  mov x0, #0
  fmov d5, x0
.L17:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L18:
  mov x0, #1
  mov x3, x0
.L19:
  cmp x11, x4
  b.gt .L28
.L20:
  fsub d3, d6, d11
.L21:
  fmadd d10, d3, d10, d11
.L22:
  fsub d11, d5, d11
.L23:
  fsub d3, d10, d9
.L24:
  fmul d3, d3, d4
.L25:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d3, [x0, x11, lsl #3]
.L26:
  add x11, x11, x3
.L27:
  b .L19
.L28:
  mov x0, #28
  mov x3, x0
.L29:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L30:
  fmov d8, d3
.L31:
  mov x0, #30
  mov x3, x0
.L32:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L33:
  fmov d7, d3
.L34:
  mov x0, #36
  mov x3, x0
.L35:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L36:
  fmov d6, d3
.L37:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L38:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L39:
  fadd d10, d3, d11
.L40:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L41:
  fmul d9, d3, d11
.L42:
  mov x0, #1
  mov x11, x0
.L43:
  mov x0, #1001
  mov x4, x0
.L44:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L45:
  mov x0, #0
  fmov d5, x0
.L46:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L47:
  mov x0, #1
  mov x3, x0
.L48:
  cmp x11, x4
  b.gt .L57
.L49:
  fsub d3, d12, d11
.L50:
  fmadd d10, d3, d10, d11
.L51:
  fsub d11, d5, d11
.L52:
  fsub d3, d10, d9
.L53:
  fmul d3, d3, d4
.L54:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d3, [x0, x11, lsl #3]
.L55:
  add x11, x11, x3
.L56:
  b .L48
.L57:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L58:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L59:
  fadd d10, d3, d11
.L60:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L61:
  fmul d9, d3, d11
.L62:
  mov x0, #1
  mov x11, x0
.L63:
  mov x0, #1012
  mov x4, x0
.L64:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L65:
  mov x0, #0
  fmov d5, x0
.L66:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L67:
  mov x0, #1
  mov x3, x0
.L68:
  cmp x11, x4
  b.gt .L77
.L69:
  fsub d3, d12, d11
.L70:
  fmadd d10, d3, d10, d11
.L71:
  fsub d11, d5, d11
.L72:
  fsub d3, d10, d9
.L73:
  fmul d3, d3, d4
.L74:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d3, [x0, x11, lsl #3]
.L75:
  add x11, x11, x3
.L76:
  b .L68
.L77:
  mov x0, #1
  mov x10, x0
.L78:
  movz x0, #63672
  movk x0, #398, lsl #16
  mov x9, x0
.L79:
  mov x0, #1001
  mov x8, x0
.L80:
  mov x0, #10
  mov x7, x0
.L81:
  mov x0, #11
  mov x6, x0
.L82:
  mov x0, #1
  mov x5, x0
.L83:
  mov x0, #1
  mov x4, x0
.L84:
  cmp x10, x9
  b.gt .L100
.L85:
  mov x0, #1
  mov x11, x0
.L86:
  cmp x11, x8
  b.gt .L98
.L87:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d5, [x0, x11, lsl #3]
.L88:
  add x3, x11, x7
.L89:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L90:
  fmul d4, d7, d3
.L91:
  add x3, x11, x6
.L92:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L93:
  fmadd d3, d6, d3, d4
.L94:
  fmadd d3, d5, d3, d8
.L95:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x11, lsl #3]
.L96:
  add x11, x11, x5
.L97:
  b .L86
.L98:
  add x10, x10, x4
.L99:
  b .L84
.L100:
  mov x0, #1
  mov x3, x0
.L101:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L102:
  str d7, [sp, #16]
  str d6, [sp, #24]
  str x11, [sp, #32]
  str x10, [sp, #40]
  str d3, [sp, #72]
  str x4, [sp, #80]
  str d5, [sp, #88]
  str d4, [sp, #96]
  str x3, [sp, #104]
  str x9, [sp, #120]
  str x8, [sp, #128]
  str x7, [sp, #136]
  str x6, [sp, #144]
  str x5, [sp, #152]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_102@PAGE
  add x0, x0, .Lfmt_print_102@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d7, [sp, #16]
  ldr d6, [sp, #24]
  ldr x11, [sp, #32]
  ldr x10, [sp, #40]
  ldr d3, [sp, #72]
  ldr x4, [sp, #80]
  ldr d5, [sp, #88]
  ldr d4, [sp, #96]
  ldr x3, [sp, #104]
  ldr x9, [sp, #120]
  ldr x8, [sp, #128]
  ldr x7, [sp, #136]
  ldr x6, [sp, #144]
  ldr x5, [sp, #152]
.L103:
  str d8, [sp, #160]
.L104:
  str d7, [sp, #168]
.L105:
  str d6, [sp, #176]
.L106:
  mov x0, x11
  str x0, [sp, #184]
.L107:
  mov x0, x10
  str x0, [sp, #192]
.L108:
  str d11, [sp, #200]
.L109:
  str d10, [sp, #208]
.L110:
  str d9, [sp, #216]
.L111:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print q (float)
  ldr d0, [sp, #160]
  sub sp, sp, #32
  adrp x1, .Lname_q@PAGE
  add x1, x1, .Lname_q@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print r (float)
  ldr d0, [sp, #168]
  sub sp, sp, #32
  adrp x1, .Lname_r@PAGE
  add x1, x1, .Lname_r@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #176]
  sub sp, sp, #32
  adrp x1, .Lname_t@PAGE
  add x1, x1, .Lname_t@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print k
  ldr x9, [sp, #184]
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
  ldr x9, [sp, #192]
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
  ldr d0, [sp, #200]
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
  ldr d0, [sp, #208]
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
  ldr d0, [sp, #216]
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
  ldr d8, [sp, #224]
  ldr d11, [sp, #232]
  ldr d10, [sp, #240]
  ldr d9, [sp, #248]
  ldr d12, [sp, #256]
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

.Lfmt_print_102:
  .asciz "%f\n"

.Lname_q:
  .asciz "q"
.Lname_r:
  .asciz "r"
.Lname_t:
  .asciz "t"
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
.global _arr_spacer
.align 3
_arr_spacer:
  .space 320
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8104
.global _arr_x
.align 3
_arr_x:
  .space 8016
