.global _main
.align 2

_main:
  sub sp, sp, #272
  str x30, [sp, #264]
  str x29, [sp, #256]
  add x29, sp, #256
  // Save callee-saved registers
  stp d10, d9, [sp, #200]
  stp d8, d12, [sp, #216]
  str d11, [sp, #232]

  // Initialize all variables to 0
  mov x0, #0

  mov x11, #0
  mov x10, #0
  fmov d7, x0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  fmov d12, x0
  fmov d11, x0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]

.L0:
  mov x0, #0
  mov x11, x0
.L1:
  mov x0, #0
  mov x10, x0
.L2:
  mov x0, #0
  fmov d7, x0
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
  mov x11, x0
.L12:
  mov x0, #39
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
  mov x1, x11
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L27
.L18:
  fsub d3, d6, d10
.L19:
  fmul d3, d3, d9
.L20:
  fadd d9, d3, d10
.L21:
  fsub d10, d5, d10
.L22:
  fsub d3, d9, d8
.L23:
  fmul d3, d3, d4
.L24:
  mov x1, x11
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L25:
  add x11, x11, x3
.L26:
  b .L17
.L27:
  mov x0, #26
  mov x3, x0
.L28:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L29:
  fmov d7, d3
.L30:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L31:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L32:
  fadd d9, d3, d10
.L33:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L34:
  fmul d8, d3, d10
.L35:
  mov x0, #1
  mov x11, x0
.L36:
  mov x0, #1001
  mov x4, x0
.L37:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L38:
  mov x0, #0
  fmov d5, x0
.L39:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L40:
  mov x0, #1
  mov x3, x0
.L41:
  mov x1, x11
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L51
.L42:
  fsub d3, d6, d10
.L43:
  fmul d3, d3, d9
.L44:
  fadd d9, d3, d10
.L45:
  fsub d10, d5, d10
.L46:
  fsub d3, d9, d8
.L47:
  fmul d3, d3, d4
.L48:
  mov x1, x11
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L49:
  add x11, x11, x3
.L50:
  b .L41
.L51:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L52:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L53:
  fadd d9, d3, d10
.L54:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L55:
  fmul d8, d3, d10
.L56:
  mov x0, #1
  mov x11, x0
.L57:
  mov x0, #1001
  mov x4, x0
.L58:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L59:
  mov x0, #0
  fmov d11, x0
.L60:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L61:
  mov x0, #0
  fmov d5, x0
.L62:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d4, x0
.L63:
  mov x0, #1
  mov x3, x0
.L64:
  mov x1, x11
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L78
.L65:
  fsub d3, d12, d10
.L66:
  fmul d3, d3, d9
.L67:
  fadd d9, d3, d10
.L68:
  fsub d10, d11, d10
.L69:
  fsub d3, d9, d8
.L70:
  fmul d3, d3, d6
.L71:
  mov x1, x11
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L72:
  mov x1, x11
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L73:
  fmov d1, d3
  fmov d2, d5
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L75
.L74:
  b .L76
.L75:
  mov x1, x11
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  str d4, [x8, x1, lsl #3]
.L76:
  add x11, x11, x3
.L77:
  b .L64
.L78:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d10, x0
.L79:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L80:
  fadd d9, d3, d10
.L81:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L82:
  fmul d8, d3, d10
.L83:
  mov x0, #1
  mov x11, x0
.L84:
  mov x0, #1001
  mov x4, x0
.L85:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L86:
  mov x0, #0
  fmov d11, x0
.L87:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L88:
  mov x0, #0
  fmov d5, x0
.L89:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d4, x0
.L90:
  mov x0, #1
  mov x3, x0
.L91:
  mov x1, x11
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L105
.L92:
  fsub d3, d12, d10
.L93:
  fmul d3, d3, d9
.L94:
  fadd d9, d3, d10
.L95:
  fsub d10, d11, d10
.L96:
  fsub d3, d9, d8
.L97:
  fmul d3, d3, d6
.L98:
  mov x1, x11
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L99:
  mov x1, x11
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L100:
  fmov d1, d3
  fmov d2, d5
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L102
.L101:
  b .L103
.L102:
  mov x1, x11
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d4, [x8, x1, lsl #3]
.L103:
  add x11, x11, x3
.L104:
  b .L91
.L105:
  mov x0, #1
  mov x11, x0
.L106:
  mov x0, #1001
  mov x4, x0
.L107:
  mov x0, #0
  fmov d4, x0
.L108:
  mov x0, #0
  fmov d3, x0
.L109:
  mov x0, #1
  mov x3, x0
.L110:
  mov x1, x11
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L115
.L111:
  mov x1, x11
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d4, [x8, x1, lsl #3]
.L112:
  mov x1, x11
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L113:
  add x11, x11, x3
.L114:
  b .L110
.L115:
  mov x0, #1
  mov x10, x0
.L116:
  movz x0, #39104
  movk x0, #11, lsl #16
  mov x9, x0
.L117:
  mov x0, #101
  mov x7, x0
.L118:
  movz x0, #18350
  movk x0, #31457, lsl #16
  movk x0, #44564, lsl #32
  movk x0, #16367, lsl #48
  fmov d6, x0
.L119:
  mov x0, #101
  mov x6, x0
.L120:
  mov x0, #101
  mov x5, x0
.L121:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d5, x0
.L122:
  mov x0, #1
  mov x4, x0
.L123:
  mov x0, #1
  mov x3, x0
.L124:
  mov x1, x10
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L146
.L125:
  movz x0, #0
  movk x0, #16436, lsl #48
  fmov d7, x0
.L126:
  fmul d4, d6, d7
.L127:
  mov x1, x6
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L128:
  fmul d3, d4, d3
.L129:
  mov x1, x7
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L130:
  mov x0, #1
  mov x11, x0
.L131:
  mov x1, x11
  mov x2, x5
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L144
.L132:
  mov x1, x11
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L133:
  mov x1, x11
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L134:
  fdiv d3, d4, d3
.L135:
  mov x1, x11
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L136:
  mov x1, x11
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L137:
  mov x1, x11
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L138:
  fmov d0, d3
  stp x29, x30, [sp, #-16]!
  bl _exp
  ldp x29, x30, [sp], #16
  fmov d3, d0
.L139:
  fsub d3, d3, d5
.L140:
  fdiv d3, d4, d3
.L141:
  mov x1, x11
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L142:
  add x11, x11, x4
.L143:
  b .L131
.L144:
  add x10, x10, x3
.L145:
  b .L124
.L146:
  mov x0, x11
  str x0, [sp, #152]
.L147:
  mov x0, x10
  str x0, [sp, #160]
.L148:
  str d7, [sp, #168]
.L149:
  str d10, [sp, #176]
.L150:
  str d9, [sp, #184]
.L151:
  str d8, [sp, #192]
.L152:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #152]
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
  ldr x9, [sp, #160]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print expmax (float)
  ldr d0, [sp, #168]
  sub sp, sp, #32
  adrp x8, .Lname_expmax@PAGE
  add x8, x8, .Lname_expmax@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #176]
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
  ldr d0, [sp, #184]
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
  ldr d0, [sp, #192]
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
  ldp d10, d9, [sp, #200]
  ldp d8, d12, [sp, #216]
  ldr d11, [sp, #232]
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
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_expmax:
  .asciz "expmax"
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
.global _arr_v
.align 3
_arr_v:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_w
.align 3
_arr_w:
  .space 8016
