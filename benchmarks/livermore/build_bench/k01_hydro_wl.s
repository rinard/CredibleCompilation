.global _main
.align 2

_main:
  sub sp, sp, #288
  str x30, [sp, #280]
  str x29, [sp, #272]
  add x29, sp, #272
  // Save callee-saved registers
  stp d10, d9, [sp, #224]
  stp d8, d12, [sp, #240]
  str d11, [sp, #256]

  // Initialize all variables to 0
  mov x0, #0

  fmov d7, x0
  fmov d6, x0
  fmov d5, x0
  mov x12, #0
  mov x11, #0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  fmov d3, x0
  mov x4, #0
  fmov d4, x0
  mov x3, #0
  fmov d12, x0
  fmov d11, x0
  mov x10, #0
  mov x9, #0
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
  fmov d7, x0
.L1:
  mov x0, #0
  fmov d6, x0
.L2:
  mov x0, #0
  fmov d5, x0
.L3:
  mov x0, #0
  mov x12, x0
.L4:
  mov x0, #0
  mov x11, x0
.L5:
  mov x0, #0
  fmov d10, x0
.L6:
  mov x0, #0
  fmov d9, x0
.L7:
  mov x0, #0
  fmov d8, x0
.L8:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L10:
  fadd d9, d3, d10
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L12:
  fmul d8, d3, d10
.L13:
  mov x0, #1
  mov x12, x0
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
  mov x1, x12
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L29
.L20:
  fsub d3, d6, d10
.L21:
  fmul d3, d3, d9
.L22:
  fadd d9, d3, d10
.L23:
  fsub d10, d5, d10
.L24:
  fsub d3, d9, d8
.L25:
  fmul d3, d3, d4
.L26:
  mov x1, x12
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L27:
  add x12, x12, x3
.L28:
  b .L19
.L29:
  mov x0, #28
  mov x3, x0
.L30:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L31:
  fmov d7, d3
.L32:
  mov x0, #30
  mov x3, x0
.L33:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L34:
  fmov d6, d3
.L35:
  mov x0, #36
  mov x3, x0
.L36:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L37:
  fmov d5, d3
.L38:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L40:
  fadd d9, d3, d10
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L42:
  fmul d8, d3, d10
.L43:
  mov x0, #1
  mov x12, x0
.L44:
  mov x0, #1001
  mov x4, x0
.L45:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L46:
  mov x0, #0
  fmov d11, x0
.L47:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L48:
  mov x0, #1
  mov x3, x0
.L49:
  mov x1, x12
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L59
.L50:
  fsub d3, d12, d10
.L51:
  fmul d3, d3, d9
.L52:
  fadd d9, d3, d10
.L53:
  fsub d10, d11, d10
.L54:
  fsub d3, d9, d8
.L55:
  fmul d3, d3, d4
.L56:
  mov x1, x12
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L57:
  add x12, x12, x3
.L58:
  b .L49
.L59:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L60:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L61:
  fadd d9, d3, d10
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L63:
  fmul d8, d3, d10
.L64:
  mov x0, #1
  mov x12, x0
.L65:
  mov x0, #1012
  mov x4, x0
.L66:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L67:
  mov x0, #0
  fmov d11, x0
.L68:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L69:
  mov x0, #1
  mov x3, x0
.L70:
  mov x1, x12
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L80
.L71:
  fsub d3, d12, d10
.L72:
  fmul d3, d3, d9
.L73:
  fadd d9, d3, d10
.L74:
  fsub d10, d11, d10
.L75:
  fsub d3, d9, d8
.L76:
  fmul d3, d3, d4
.L77:
  mov x1, x12
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L78:
  add x12, x12, x3
.L79:
  b .L70
.L80:
  mov x0, #1
  mov x11, x0
.L81:
  movz x0, #63672
  movk x0, #398, lsl #16
  mov x10, x0
.L82:
  mov x0, #1001
  mov x9, x0
.L83:
  mov x0, #10
  mov x7, x0
.L84:
  mov x0, #11
  mov x6, x0
.L85:
  mov x0, #1
  mov x5, x0
.L86:
  mov x0, #1
  mov x4, x0
.L87:
  mov x1, x11
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L105
.L88:
  mov x0, #1
  mov x12, x0
.L89:
  mov x1, x12
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L103
.L90:
  mov x1, x12
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d11, [x8, x1, lsl #3]
.L91:
  add x3, x12, x7
.L92:
  mov x1, x3
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L93:
  fmul d4, d6, d3
.L94:
  add x3, x12, x6
.L95:
  mov x1, x3
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L96:
  fmul d3, d5, d3
.L97:
  fadd d3, d4, d3
.L98:
  fmul d3, d11, d3
.L99:
  fadd d3, d7, d3
.L100:
  mov x1, x12
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L101:
  add x12, x12, x5
.L102:
  b .L89
.L103:
  add x11, x11, x4
.L104:
  b .L87
.L105:
  str d7, [sp, #160]
.L106:
  str d6, [sp, #168]
.L107:
  str d5, [sp, #176]
.L108:
  mov x0, x12
  str x0, [sp, #184]
.L109:
  mov x0, x11
  str x0, [sp, #192]
.L110:
  str d10, [sp, #200]
.L111:
  str d9, [sp, #208]
.L112:
  str d8, [sp, #216]
.L113:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print q (float)
  ldr d0, [sp, #160]
  sub sp, sp, #32
  adrp x8, .Lname_q@PAGE
  add x8, x8, .Lname_q@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print r (float)
  ldr d0, [sp, #168]
  sub sp, sp, #32
  adrp x8, .Lname_r@PAGE
  add x8, x8, .Lname_r@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #176]
  sub sp, sp, #32
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print k
  ldr x9, [sp, #184]
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
  ldr x9, [sp, #192]
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
  ldr d0, [sp, #200]
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
  ldr d0, [sp, #208]
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
  ldr d0, [sp, #216]
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
  ldp d10, d9, [sp, #224]
  ldp d8, d12, [sp, #240]
  ldr d11, [sp, #256]
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
