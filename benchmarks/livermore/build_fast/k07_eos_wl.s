.global _main
.align 2

_main:
  sub sp, sp, #336
  str x30, [sp, #328]
  str x29, [sp, #320]
  add x29, sp, #320
  // Save callee-saved registers
  str d10, [sp, #272]
  str d9, [sp, #280]
  str d8, [sp, #288]
  str d12, [sp, #296]
  str d11, [sp, #304]
  str d13, [sp, #312]

  // Initialize all variables to 0
  mov x0, #0

  mov x15, #0
  mov x14, #0
  fmov d6, x0
  fmov d5, x0
  fmov d7, x0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  fmov d3, x0
  mov x4, #0
  fmov d4, x0
  mov x3, #0
  fmov d12, x0
  fmov d11, x0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x8, #0
  mov x7, #0
  mov x6, #0
  str x0, [sp, #184]
  mov x5, #0
  fmov d13, x0
  str x0, [sp, #208]
  str x0, [sp, #216]
  str x0, [sp, #224]
  str x0, [sp, #232]
  str x0, [sp, #240]
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]

.L0:
  mov x0, #0
  mov x15, x0
.L1:
  mov x0, #0
  mov x14, x0
.L2:
  mov x0, #0
  fmov d6, x0
.L3:
  mov x0, #0
  fmov d5, x0
.L4:
  mov x0, #0
  fmov d7, x0
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
  mov x15, x0
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
  cmp x15, x4
  b.gt .L28
.L20:
  fsub d3, d6, d10
.L21:
  fmadd d9, d3, d9, d10
.L22:
  fsub d10, d5, d10
.L23:
  fsub d3, d9, d8
.L24:
  fmul d3, d3, d4
.L25:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L26:
  add x15, x15, x3
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
  fmov d7, d3
.L31:
  mov x0, #30
  mov x3, x0
.L32:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L33:
  fmov d6, d3
.L34:
  mov x0, #36
  mov x3, x0
.L35:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L36:
  fmov d5, d3
.L37:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L38:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L39:
  fadd d9, d3, d10
.L40:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L41:
  fmul d8, d3, d10
.L42:
  mov x0, #1
  mov x15, x0
.L43:
  mov x0, #1001
  mov x4, x0
.L44:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L45:
  mov x0, #0
  fmov d11, x0
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
  cmp x15, x4
  b.gt .L57
.L49:
  fsub d3, d12, d10
.L50:
  fmadd d9, d3, d9, d10
.L51:
  fsub d10, d11, d10
.L52:
  fsub d3, d9, d8
.L53:
  fmul d3, d3, d4
.L54:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L55:
  add x15, x15, x3
.L56:
  b .L48
.L57:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L58:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L59:
  fadd d9, d3, d10
.L60:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L61:
  fmul d8, d3, d10
.L62:
  mov x0, #1
  mov x15, x0
.L63:
  mov x0, #1001
  mov x4, x0
.L64:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L65:
  mov x0, #0
  fmov d11, x0
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
  cmp x15, x4
  b.gt .L77
.L69:
  fsub d3, d12, d10
.L70:
  fmadd d9, d3, d9, d10
.L71:
  fsub d10, d11, d10
.L72:
  fsub d3, d9, d8
.L73:
  fmul d3, d3, d4
.L74:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L75:
  add x15, x15, x3
.L76:
  b .L68
.L77:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L78:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L79:
  fadd d9, d3, d10
.L80:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L81:
  fmul d8, d3, d10
.L82:
  mov x0, #1
  mov x15, x0
.L83:
  mov x0, #1001
  mov x4, x0
.L84:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L85:
  mov x0, #0
  fmov d11, x0
.L86:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L87:
  mov x0, #1
  mov x3, x0
.L88:
  cmp x15, x4
  b.gt .L97
.L89:
  fsub d3, d12, d10
.L90:
  fmadd d9, d3, d9, d10
.L91:
  fsub d10, d11, d10
.L92:
  fsub d3, d9, d8
.L93:
  fmul d3, d3, d4
.L94:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L95:
  add x15, x15, x3
.L96:
  b .L88
.L97:
  mov x0, #1
  mov x15, x0
.L98:
  mov x0, #1001
  mov x4, x0
.L99:
  mov x0, #0
  fmov d3, x0
.L100:
  mov x0, #1
  mov x3, x0
.L101:
  cmp x15, x4
  b.gt .L105
.L102:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L103:
  add x15, x15, x3
.L104:
  b .L101
.L105:
  mov x0, #1
  mov x14, x0
.L106:
  mov x0, #11472
  mov x13, x0
.L107:
  mov x0, #995
  mov x12, x0
.L108:
  mov x0, #3
  mov x11, x0
.L109:
  mov x0, #2
  mov x10, x0
.L110:
  mov x0, #1
  mov x9, x0
.L111:
  mov x0, #6
  mov x8, x0
.L112:
  mov x0, #5
  mov x7, x0
.L113:
  mov x0, #4
  mov x6, x0
.L114:
  mov x0, #1
  str x0, [sp, #184]
.L115:
  mov x0, #1
  mov x5, x0
.L116:
  cmp x14, x13
  b.gt .L147
.L117:
  mov x0, #1
  mov x15, x0
.L118:
  cmp x15, x12
  b.gt .L145
.L119:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d11, [x0, x15, lsl #3]
.L120:
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d4, [x0, x15, lsl #3]
.L121:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d3, [x0, x15, lsl #3]
.L122:
  fmadd d3, d6, d3, d4
.L123:
  fmadd d12, d6, d3, d11
.L124:
  add x3, x15, x11
.L125:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d11, [x0, x3, lsl #3]
.L126:
  add x3, x15, x10
.L127:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L128:
  add x4, x15, x9
.L129:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d3, [x0, x4, lsl #3]
.L130:
  fmadd d3, d6, d3, d4
.L131:
  fmadd d13, d6, d3, d11
.L132:
  add x3, x15, x8
.L133:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d11, [x0, x3, lsl #3]
.L134:
  add x3, x15, x7
.L135:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L136:
  add x3, x15, x6
.L137:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L138:
  fmadd d3, d7, d3, d4
.L139:
  fmadd d3, d7, d3, d11
.L140:
  fmadd d3, d5, d3, d13
.L141:
  fmadd d3, d5, d3, d12
.L142:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L143:
  mov x0, x4
  mov x15, x0
.L144:
  b .L118
.L145:
  add x14, x14, x5
.L146:
  b .L116
.L147:
  mov x0, #1
  mov x3, x0
.L148:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L149:
  str x15, [sp, #8]
  str x14, [sp, #16]
  str d6, [sp, #24]
  str d5, [sp, #32]
  str d7, [sp, #40]
  str d3, [sp, #72]
  str x4, [sp, #80]
  str d4, [sp, #88]
  str x3, [sp, #96]
  str x13, [sp, #120]
  str x12, [sp, #128]
  str x11, [sp, #136]
  str x10, [sp, #144]
  str x9, [sp, #152]
  str x8, [sp, #160]
  str x7, [sp, #168]
  str x6, [sp, #176]
  str x5, [sp, #192]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_149@PAGE
  add x0, x0, .Lfmt_print_149@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x15, [sp, #8]
  ldr x14, [sp, #16]
  ldr d6, [sp, #24]
  ldr d5, [sp, #32]
  ldr d7, [sp, #40]
  ldr d3, [sp, #72]
  ldr x4, [sp, #80]
  ldr d4, [sp, #88]
  ldr x3, [sp, #96]
  ldr x13, [sp, #120]
  ldr x12, [sp, #128]
  ldr x11, [sp, #136]
  ldr x10, [sp, #144]
  ldr x9, [sp, #152]
  ldr x8, [sp, #160]
  ldr x7, [sp, #168]
  ldr x6, [sp, #176]
  ldr x5, [sp, #192]
.L150:
  mov x0, x15
  str x0, [sp, #208]
.L151:
  mov x0, x14
  str x0, [sp, #216]
.L152:
  str d6, [sp, #224]
.L153:
  str d5, [sp, #232]
.L154:
  str d7, [sp, #240]
.L155:
  str d10, [sp, #248]
.L156:
  str d9, [sp, #256]
.L157:
  str d8, [sp, #264]
.L158:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #208]
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
  ldr x9, [sp, #216]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r (float)
  ldr d0, [sp, #224]
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
  ldr d0, [sp, #232]
  sub sp, sp, #32
  adrp x1, .Lname_t@PAGE
  add x1, x1, .Lname_t@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print q (float)
  ldr d0, [sp, #240]
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
  ldr d0, [sp, #248]
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
  ldr d0, [sp, #256]
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
  ldr d0, [sp, #264]
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
  ldr d10, [sp, #272]
  ldr d9, [sp, #280]
  ldr d8, [sp, #288]
  ldr d12, [sp, #296]
  ldr d11, [sp, #304]
  ldr d13, [sp, #312]
  ldr x29, [sp, #320]
  ldr x30, [sp, #328]
  add sp, sp, #336
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

.Lfmt_print_149:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_r:
  .asciz "r"
.Lname_t:
  .asciz "t"
.Lname_q:
  .asciz "q"
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
.global _arr_u
.align 3
_arr_u:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
