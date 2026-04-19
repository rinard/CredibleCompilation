.global _main
.align 2

_main:
  sub sp, sp, #432
  str x30, [sp, #424]
  str x29, [sp, #416]
  add x29, sp, #416
  // Save callee-saved registers
  stp x28, x27, [sp, #312]
  stp x26, x25, [sp, #328]
  stp x24, x23, [sp, #344]
  stp x22, x21, [sp, #360]
  stp x20, x19, [sp, #376]
  stp d8, d9, [sp, #392]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  fmov d8, x0
  fmov d9, x0
  fmov d7, x0
  mov x4, #0
  fmov d3, x0
  mov x3, #0
  mov x10, #0
  mov x9, #0
  fmov d6, x0
  fmov d5, x0
  mov x7, #0
  mov x6, #0
  fmov d4, x0
  mov x5, #0
  str x0, [sp, #152]
  str x0, [sp, #160]
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  mov x23, #0
  mov x22, #0
  mov x21, #0
  mov x20, #0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  str x0, [sp, #288]
  str x0, [sp, #296]
  str x0, [sp, #304]

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #0
  str x0, [sp, #24]
.L3:
  mov x0, #0
  str x0, [sp, #32]
.L4:
  mov x0, #0
  fmov d8, x0
.L5:
  mov x0, #0
  fmov d9, x0
.L6:
  mov x0, #0
  fmov d7, x0
.L7:
  mov x0, #1
  str x0, [sp, #24]
.L8:
  mov x0, #2525
  mov x4, x0
.L9:
  mov x0, #0
  fmov d3, x0
.L10:
  mov x0, #1
  mov x3, x0
.L11:
  ldr x1, [sp, #24]
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L15
.L12:
  ldr x1, [sp, #24]
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L13:
  ldr x1, [sp, #24]
  add x0, x1, x3
  str x0, [sp, #24]
.L14:
  b .L11
.L15:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L16:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L17:
  fadd d9, d3, d8
.L18:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L19:
  fmul d7, d3, d8
.L20:
  mov x0, #1
  str x0, [sp, #16]
.L21:
  mov x0, #101
  mov x10, x0
.L22:
  mov x0, #25
  mov x9, x0
.L23:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L24:
  mov x0, #0
  fmov d5, x0
.L25:
  mov x0, #1
  mov x7, x0
.L26:
  mov x0, #25
  mov x6, x0
.L27:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L28:
  mov x0, #1
  mov x5, x0
.L29:
  mov x0, #1
  mov x4, x0
.L30:
  ldr x1, [sp, #16]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L47
.L31:
  mov x0, #1
  str x0, [sp, #8]
.L32:
  ldr x1, [sp, #8]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L45
.L33:
  fsub d3, d6, d8
.L34:
  fmul d3, d3, d9
.L35:
  fadd d9, d3, d8
.L36:
  fsub d8, d5, d8
.L37:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L38:
  mul x3, x3, x6
.L39:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L40:
  fsub d3, d9, d7
.L41:
  fmul d3, d3, d4
.L42:
  mov x1, x3
  adrp x8, _arr_cx@PAGE
  add x8, x8, _arr_cx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L43:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L44:
  b .L32
.L45:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L46:
  b .L30
.L47:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L48:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L49:
  fadd d9, d3, d8
.L50:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L51:
  fmul d7, d3, d8
.L52:
  mov x0, #1
  str x0, [sp, #16]
.L53:
  mov x0, #25
  mov x10, x0
.L54:
  mov x0, #101
  mov x9, x0
.L55:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L56:
  mov x0, #0
  fmov d5, x0
.L57:
  mov x0, #1
  mov x7, x0
.L58:
  mov x0, #101
  mov x6, x0
.L59:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L60:
  mov x0, #1
  mov x5, x0
.L61:
  mov x0, #1
  mov x4, x0
.L62:
  ldr x1, [sp, #16]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L79
.L63:
  mov x0, #1
  str x0, [sp, #8]
.L64:
  ldr x1, [sp, #8]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L77
.L65:
  fsub d3, d6, d8
.L66:
  fmul d3, d3, d9
.L67:
  fadd d9, d3, d8
.L68:
  fsub d8, d5, d8
.L69:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L70:
  mul x3, x3, x6
.L71:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L72:
  fsub d3, d9, d7
.L73:
  fmul d3, d3, d4
.L74:
  mov x1, x3
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L75:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L76:
  b .L64
.L77:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L78:
  b .L62
.L79:
  mov x0, #1
  str x0, [sp, #32]
.L80:
  movz x0, #51168
  movk x0, #37, lsl #16
  str x0, [sp, #152]
.L81:
  mov x0, #101
  str x0, [sp, #160]
.L82:
  mov x0, #25
  mov x28, x0
.L83:
  mov x0, #1
  mov x27, x0
.L84:
  mov x0, #25
  mov x26, x0
.L85:
  mov x0, #0
  fmov d6, x0
.L86:
  mov x0, #1
  mov x25, x0
.L87:
  mov x0, #1
  mov x24, x0
.L88:
  mov x0, #25
  mov x23, x0
.L89:
  mov x0, #25
  mov x22, x0
.L90:
  mov x0, #101
  mov x21, x0
.L91:
  mov x0, #1
  mov x20, x0
.L92:
  mov x0, #25
  mov x19, x0
.L93:
  mov x0, #1
  mov x15, x0
.L94:
  mov x0, #25
  mov x14, x0
.L95:
  mov x0, #1
  mov x13, x0
.L96:
  mov x0, #101
  mov x12, x0
.L97:
  mov x0, #1
  mov x11, x0
.L98:
  mov x0, #25
  mov x10, x0
.L99:
  mov x0, #1
  mov x9, x0
.L100:
  mov x0, #1
  mov x7, x0
.L101:
  mov x0, #1
  mov x6, x0
.L102:
  mov x0, #1
  mov x5, x0
.L103:
  ldr x1, [sp, #32]
  ldr x2, [sp, #152]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L148
.L104:
  mov x0, #1
  str x0, [sp, #16]
.L105:
  ldr x1, [sp, #16]
  ldr x2, [sp, #160]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L116
.L106:
  mov x0, #1
  str x0, [sp, #8]
.L107:
  ldr x1, [sp, #8]
  mov x2, x28
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L114
.L108:
  ldr x1, [sp, #16]
  sub x3, x1, x27
.L109:
  mul x3, x3, x26
.L110:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L111:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d6, [x8, x1, lsl #3]
.L112:
  ldr x1, [sp, #8]
  add x0, x1, x25
  str x0, [sp, #8]
.L113:
  b .L107
.L114:
  ldr x1, [sp, #16]
  add x0, x1, x24
  str x0, [sp, #16]
.L115:
  b .L105
.L116:
  mov x0, #1
  str x0, [sp, #24]
.L117:
  ldr x1, [sp, #24]
  mov x2, x23
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L146
.L118:
  mov x0, #1
  str x0, [sp, #8]
.L119:
  ldr x1, [sp, #8]
  mov x2, x22
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L144
.L120:
  mov x0, #1
  str x0, [sp, #16]
.L121:
  ldr x1, [sp, #16]
  mov x2, x21
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L142
.L122:
  ldr x1, [sp, #16]
  sub x3, x1, x20
.L123:
  mul x3, x3, x19
.L124:
  ldr x2, [sp, #8]
  add x4, x3, x2
.L125:
  ldr x1, [sp, #16]
  sub x3, x1, x15
.L126:
  mul x3, x3, x14
.L127:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L128:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d5, [x8, x1, lsl #3]
.L129:
  ldr x1, [sp, #8]
  sub x3, x1, x13
.L130:
  mul x3, x3, x12
.L131:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L132:
  mov x1, x3
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L133:
  ldr x1, [sp, #16]
  sub x3, x1, x11
.L134:
  mul x3, x3, x10
.L135:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L136:
  mov x1, x3
  adrp x8, _arr_cx@PAGE
  add x8, x8, _arr_cx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L137:
  fmul d3, d4, d3
.L138:
  fadd d3, d5, d3
.L139:
  mov x1, x4
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L140:
  ldr x1, [sp, #16]
  add x0, x1, x9
  str x0, [sp, #16]
.L141:
  b .L121
.L142:
  ldr x1, [sp, #8]
  add x0, x1, x7
  str x0, [sp, #8]
.L143:
  b .L119
.L144:
  ldr x1, [sp, #24]
  add x0, x1, x6
  str x0, [sp, #24]
.L145:
  b .L117
.L146:
  ldr x1, [sp, #32]
  add x0, x1, x5
  str x0, [sp, #32]
.L147:
  b .L103
.L148:
  str d8, [sp, #288]
.L149:
  str d9, [sp, #296]
.L150:
  str d7, [sp, #304]
.L151:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_j@PAGE
  add x8, x8, .Lname_j@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #24]
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
  ldr x9, [sp, #32]
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
  ldr d0, [sp, #288]
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
  ldr d0, [sp, #296]
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
  ldr d0, [sp, #304]
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
  ldp x28, x27, [sp, #312]
  ldp x26, x25, [sp, #328]
  ldp x24, x23, [sp, #344]
  ldp x22, x21, [sp, #360]
  ldp x20, x19, [sp, #376]
  ldp d8, d9, [sp, #392]
  ldr x29, [sp, #416]
  ldr x30, [sp, #424]
  add sp, sp, #432
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
.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
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
.global _arr_px
.align 3
_arr_px:
  .space 20208
.global _arr_cx
.align 3
_arr_cx:
  .space 20208
.global _arr_vy
.align 3
_arr_vy:
  .space 20208
