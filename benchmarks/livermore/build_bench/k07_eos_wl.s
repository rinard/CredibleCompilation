.global _main
.align 2

_main:
  sub sp, sp, #352
  str x30, [sp, #344]
  str x29, [sp, #336]
  add x29, sp, #336
  // Save callee-saved registers
  str x19, [sp, #264]
  stp d9, d8, [sp, #280]
  stp d12, d11, [sp, #296]
  stp d10, d13, [sp, #312]

  // Initialize all variables to 0
  mov x0, #0

  mov x19, #0
  mov x15, #0
  fmov d5, x0
  fmov d4, x0
  fmov d6, x0
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  fmov d3, x0
  mov x4, #0
  mov x3, #0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  mov x14, #0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  fmov d13, x0
  str x0, [sp, #200]
  str x0, [sp, #208]
  str x0, [sp, #216]
  str x0, [sp, #224]
  str x0, [sp, #232]
  str x0, [sp, #240]
  str x0, [sp, #248]
  str x0, [sp, #256]

.L0:
  mov x0, #0
  mov x19, x0
.L1:
  mov x0, #0
  mov x15, x0
.L2:
  mov x0, #0
  fmov d5, x0
.L3:
  mov x0, #0
  fmov d4, x0
.L4:
  mov x0, #0
  fmov d6, x0
.L5:
  mov x0, #0
  fmov d9, x0
.L6:
  mov x0, #0
  fmov d8, x0
.L7:
  mov x0, #0
  fmov d7, x0
.L8:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L10:
  fadd d8, d3, d9
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L12:
  fmul d7, d3, d9
.L13:
  mov x0, #1
  mov x19, x0
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
  mov x1, x19
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L29
.L20:
  fsub d3, d6, d9
.L21:
  fmul d3, d3, d8
.L22:
  fadd d8, d3, d9
.L23:
  fsub d9, d5, d9
.L24:
  fsub d3, d8, d7
.L25:
  fmul d3, d3, d4
.L26:
  mov x1, x19
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L27:
  add x19, x19, x3
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
  fmov d6, d3
.L32:
  mov x0, #30
  mov x3, x0
.L33:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L34:
  fmov d5, d3
.L35:
  mov x0, #36
  mov x3, x0
.L36:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L37:
  fmov d4, d3
.L38:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L40:
  fadd d8, d3, d9
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L42:
  fmul d7, d3, d9
.L43:
  mov x0, #1
  mov x19, x0
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
  fmov d10, x0
.L48:
  mov x0, #1
  mov x3, x0
.L49:
  mov x1, x19
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L59
.L50:
  fsub d3, d12, d9
.L51:
  fmul d3, d3, d8
.L52:
  fadd d8, d3, d9
.L53:
  fsub d9, d11, d9
.L54:
  fsub d3, d8, d7
.L55:
  fmul d3, d3, d10
.L56:
  mov x1, x19
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L57:
  add x19, x19, x3
.L58:
  b .L49
.L59:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L60:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L61:
  fadd d8, d3, d9
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L63:
  fmul d7, d3, d9
.L64:
  mov x0, #1
  mov x19, x0
.L65:
  mov x0, #1001
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
  fmov d10, x0
.L69:
  mov x0, #1
  mov x3, x0
.L70:
  mov x1, x19
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L80
.L71:
  fsub d3, d12, d9
.L72:
  fmul d3, d3, d8
.L73:
  fadd d8, d3, d9
.L74:
  fsub d9, d11, d9
.L75:
  fsub d3, d8, d7
.L76:
  fmul d3, d3, d10
.L77:
  mov x1, x19
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L78:
  add x19, x19, x3
.L79:
  b .L70
.L80:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L81:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L82:
  fadd d8, d3, d9
.L83:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L84:
  fmul d7, d3, d9
.L85:
  mov x0, #1
  mov x19, x0
.L86:
  mov x0, #1001
  mov x4, x0
.L87:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L88:
  mov x0, #0
  fmov d11, x0
.L89:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L90:
  mov x0, #1
  mov x3, x0
.L91:
  mov x1, x19
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L101
.L92:
  fsub d3, d12, d9
.L93:
  fmul d3, d3, d8
.L94:
  fadd d8, d3, d9
.L95:
  fsub d9, d11, d9
.L96:
  fsub d3, d8, d7
.L97:
  fmul d3, d3, d10
.L98:
  mov x1, x19
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L99:
  add x19, x19, x3
.L100:
  b .L91
.L101:
  mov x0, #1
  mov x19, x0
.L102:
  mov x0, #1001
  mov x4, x0
.L103:
  mov x0, #0
  fmov d3, x0
.L104:
  mov x0, #1
  mov x3, x0
.L105:
  mov x1, x19
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L109
.L106:
  mov x1, x19
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L107:
  add x19, x19, x3
.L108:
  b .L105
.L109:
  mov x0, #1
  mov x15, x0
.L110:
  movz x0, #3200
  movk x0, #175, lsl #16
  mov x14, x0
.L111:
  mov x0, #995
  mov x13, x0
.L112:
  mov x0, #3
  mov x12, x0
.L113:
  mov x0, #2
  mov x11, x0
.L114:
  mov x0, #1
  mov x10, x0
.L115:
  mov x0, #6
  mov x9, x0
.L116:
  mov x0, #5
  mov x7, x0
.L117:
  mov x0, #4
  mov x6, x0
.L118:
  mov x0, #1
  mov x5, x0
.L119:
  mov x0, #1
  mov x4, x0
.L120:
  mov x1, x15
  mov x2, x14
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L159
.L121:
  mov x0, #1
  mov x19, x0
.L122:
  mov x1, x19
  mov x2, x13
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L157
.L123:
  mov x1, x19
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d11, [x8, x1, lsl #3]
.L124:
  mov x1, x19
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L125:
  mov x1, x19
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L126:
  fmul d3, d5, d3
.L127:
  fadd d3, d10, d3
.L128:
  fmul d3, d5, d3
.L129:
  fadd d10, d11, d3
.L130:
  add x3, x19, x12
.L131:
  mov x1, x3
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d12, [x8, x1, lsl #3]
.L132:
  add x3, x19, x11
.L133:
  mov x1, x3
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d11, [x8, x1, lsl #3]
.L134:
  add x3, x19, x10
.L135:
  mov x1, x3
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L136:
  fmul d3, d5, d3
.L137:
  fadd d3, d11, d3
.L138:
  fmul d3, d5, d3
.L139:
  fadd d11, d12, d3
.L140:
  add x3, x19, x9
.L141:
  mov x1, x3
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d12, [x8, x1, lsl #3]
.L142:
  add x3, x19, x7
.L143:
  mov x1, x3
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d13, [x8, x1, lsl #3]
.L144:
  add x3, x19, x6
.L145:
  mov x1, x3
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L146:
  fmul d3, d6, d3
.L147:
  fadd d3, d13, d3
.L148:
  fmul d3, d6, d3
.L149:
  fadd d3, d12, d3
.L150:
  fmul d3, d4, d3
.L151:
  fadd d3, d11, d3
.L152:
  fmul d3, d4, d3
.L153:
  fadd d3, d10, d3
.L154:
  mov x1, x19
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L155:
  add x19, x19, x5
.L156:
  b .L122
.L157:
  add x15, x15, x4
.L158:
  b .L120
.L159:
  mov x0, x19
  str x0, [sp, #200]
.L160:
  mov x0, x15
  str x0, [sp, #208]
.L161:
  str d5, [sp, #216]
.L162:
  str d4, [sp, #224]
.L163:
  str d6, [sp, #232]
.L164:
  str d9, [sp, #240]
.L165:
  str d8, [sp, #248]
.L166:
  str d7, [sp, #256]
.L167:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #200]
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
  ldr x9, [sp, #208]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r (float)
  ldr d0, [sp, #216]
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
  ldr d0, [sp, #224]
  sub sp, sp, #32
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print q (float)
  ldr d0, [sp, #232]
  sub sp, sp, #32
  adrp x8, .Lname_q@PAGE
  add x8, x8, .Lname_q@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #240]
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
  ldr d0, [sp, #248]
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
  ldr d0, [sp, #256]
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
  ldr x19, [sp, #264]
  ldp d9, d8, [sp, #280]
  ldp d12, d11, [sp, #296]
  ldp d10, d13, [sp, #312]
  ldr x29, [sp, #336]
  ldr x30, [sp, #344]
  add sp, sp, #352
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
