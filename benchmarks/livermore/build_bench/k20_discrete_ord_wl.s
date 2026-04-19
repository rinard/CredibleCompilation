.global _main
.align 2

_main:
  sub sp, sp, #352
  str x30, [sp, #344]
  str x29, [sp, #336]
  add x29, sp, #336
  // Save callee-saved registers
  stp d15, d14, [sp, #272]
  stp d13, d12, [sp, #288]
  stp d11, d10, [sp, #304]
  stp d9, d8, [sp, #320]

  // Initialize all variables to 0
  mov x0, #0

  mov x13, #0
  mov x12, #0
  str x0, [sp, #24]
  str x0, [sp, #32]
  str x0, [sp, #40]
  str x0, [sp, #48]
  str x0, [sp, #56]
  str x0, [sp, #64]
  fmov d15, x0
  fmov d14, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  fmov d7, x0
  mov x11, #0
  fmov d13, x0
  fmov d12, x0
  mov x10, #0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #240]
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]

.L0:
  mov x0, #0
  mov x13, x0
.L1:
  mov x0, #0
  mov x12, x0
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
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #56]
.L7:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #64]
.L8:
  mov x0, #0
  fmov d15, x0
.L9:
  mov x0, #0
  fmov d14, x0
.L10:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L11:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L12:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L13:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L14:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L15:
  mov x0, #1
  mov x13, x0
.L16:
  mov x0, #39
  mov x4, x0
.L17:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L18:
  mov x0, #0
  fmov d5, x0
.L19:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L20:
  mov x0, #1
  mov x3, x0
.L21:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L31
.L22:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L23:
  fmul d3, d3, d15
.L24:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L25:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L26:
  fsub d3, d15, d14
.L27:
  fmul d3, d3, d4
.L28:
  mov x1, x13
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L29:
  add x13, x13, x3
.L30:
  b .L21
.L31:
  mov x0, #15
  mov x3, x0
.L32:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L33:
  str d3, [sp, #24]
.L34:
  mov x0, #32
  mov x3, x0
.L35:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L36:
  str d3, [sp, #32]
.L37:
  mov x0, #36
  mov x3, x0
.L38:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L39:
  str d3, [sp, #40]
.L40:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L41:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L42:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L43:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L44:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L45:
  mov x0, #1
  mov x13, x0
.L46:
  mov x0, #1001
  mov x4, x0
.L47:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L48:
  mov x0, #0
  fmov d5, x0
.L49:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L50:
  mov x0, #1
  mov x3, x0
.L51:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L61
.L52:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L53:
  fmul d3, d3, d15
.L54:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L55:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L56:
  fsub d3, d15, d14
.L57:
  fmul d3, d3, d4
.L58:
  mov x1, x13
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L59:
  add x13, x13, x3
.L60:
  b .L51
.L61:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L62:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L63:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L64:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L65:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L66:
  mov x0, #1
  mov x13, x0
.L67:
  mov x0, #1001
  mov x4, x0
.L68:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L69:
  mov x0, #0
  fmov d5, x0
.L70:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L71:
  mov x0, #1
  mov x3, x0
.L72:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L82
.L73:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L74:
  fmul d3, d3, d15
.L75:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L76:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L77:
  fsub d3, d15, d14
.L78:
  fmul d3, d3, d4
.L79:
  mov x1, x13
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L80:
  add x13, x13, x3
.L81:
  b .L72
.L82:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L83:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L84:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L85:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L86:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L87:
  mov x0, #1
  mov x13, x0
.L88:
  mov x0, #1001
  mov x4, x0
.L89:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L90:
  mov x0, #0
  fmov d5, x0
.L91:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L92:
  mov x0, #1
  mov x3, x0
.L93:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L103
.L94:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L95:
  fmul d3, d3, d15
.L96:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L97:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L98:
  fsub d3, d15, d14
.L99:
  fmul d3, d3, d4
.L100:
  mov x1, x13
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L101:
  add x13, x13, x3
.L102:
  b .L93
.L103:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L104:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L105:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L106:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L107:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L108:
  mov x0, #1
  mov x13, x0
.L109:
  mov x0, #1001
  mov x4, x0
.L110:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L111:
  mov x0, #0
  fmov d5, x0
.L112:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L113:
  mov x0, #1
  mov x3, x0
.L114:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L124
.L115:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L116:
  fmul d3, d3, d15
.L117:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L118:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L119:
  fsub d3, d15, d14
.L120:
  fmul d3, d3, d4
.L121:
  mov x1, x13
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L122:
  add x13, x13, x3
.L123:
  b .L114
.L124:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L125:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L126:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L127:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L128:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L129:
  mov x0, #1
  mov x13, x0
.L130:
  mov x0, #1001
  mov x4, x0
.L131:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L132:
  mov x0, #0
  fmov d5, x0
.L133:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L134:
  mov x0, #1
  mov x3, x0
.L135:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L145
.L136:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L137:
  fmul d3, d3, d15
.L138:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L139:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L140:
  fsub d3, d15, d14
.L141:
  fmul d3, d3, d4
.L142:
  mov x1, x13
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L143:
  add x13, x13, x3
.L144:
  b .L135
.L145:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L146:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L147:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L148:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L149:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L150:
  mov x0, #1
  mov x13, x0
.L151:
  mov x0, #1001
  mov x4, x0
.L152:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L153:
  mov x0, #0
  fmov d5, x0
.L154:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L155:
  mov x0, #1
  mov x3, x0
.L156:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L166
.L157:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L158:
  fmul d3, d3, d15
.L159:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L160:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L161:
  fsub d3, d15, d14
.L162:
  fmul d3, d3, d4
.L163:
  mov x1, x13
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L164:
  add x13, x13, x3
.L165:
  b .L156
.L166:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L167:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L168:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L169:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L170:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L171:
  mov x0, #1
  mov x13, x0
.L172:
  mov x0, #1001
  mov x4, x0
.L173:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L174:
  mov x0, #0
  fmov d5, x0
.L175:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L176:
  mov x0, #1
  mov x3, x0
.L177:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L187
.L178:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L179:
  fmul d3, d3, d15
.L180:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L181:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L182:
  fsub d3, d15, d14
.L183:
  fmul d3, d3, d4
.L184:
  mov x1, x13
  adrp x8, _arr_g@PAGE
  add x8, x8, _arr_g@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L185:
  add x13, x13, x3
.L186:
  b .L177
.L187:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L188:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L189:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L190:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L191:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L192:
  mov x0, #1
  mov x13, x0
.L193:
  mov x0, #1001
  mov x4, x0
.L194:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d7, x0
.L195:
  mov x0, #0
  fmov d6, x0
.L196:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d5, x0
.L197:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d4, x0
.L198:
  mov x0, #1
  mov x3, x0
.L199:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L210
.L200:
  ldr d2, [sp, #64]
  fsub d3, d7, d2
.L201:
  fmul d3, d3, d15
.L202:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L203:
  ldr d2, [sp, #64]
  fsub d0, d6, d2
  str d0, [sp, #64]
.L204:
  fsub d3, d15, d14
.L205:
  fmul d3, d3, d5
.L206:
  fadd d3, d3, d4
.L207:
  mov x1, x13
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L208:
  add x13, x13, x3
.L209:
  b .L199
.L210:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L211:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L212:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L213:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L214:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L215:
  mov x0, #1
  mov x13, x0
.L216:
  mov x0, #1001
  mov x4, x0
.L217:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d7, x0
.L218:
  mov x0, #0
  fmov d6, x0
.L219:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d5, x0
.L220:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d4, x0
.L221:
  mov x0, #1
  mov x3, x0
.L222:
  mov x1, x13
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L233
.L223:
  ldr d2, [sp, #64]
  fsub d3, d7, d2
.L224:
  fmul d3, d3, d15
.L225:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L226:
  ldr d2, [sp, #64]
  fsub d0, d6, d2
  str d0, [sp, #64]
.L227:
  fsub d3, d15, d14
.L228:
  fmul d3, d3, d5
.L229:
  fadd d3, d3, d4
.L230:
  mov x1, x13
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L231:
  add x13, x13, x3
.L232:
  b .L222
.L233:
  mov x0, #1
  mov x12, x0
.L234:
  movz x0, #62672
  movk x0, #23, lsl #16
  mov x11, x0
.L235:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d13, x0
.L236:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d12, x0
.L237:
  mov x0, #1001
  mov x10, x0
.L238:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L239:
  mov x0, #0
  fmov d10, x0
.L240:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d9, x0
.L241:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L242:
  mov x0, #1
  mov x9, x0
.L243:
  mov x0, #1000
  mov x7, x0
.L244:
  mov x0, #0
  fmov d7, x0
.L245:
  mov x0, #0
  fmov d6, x0
.L246:
  mov x0, #1
  mov x6, x0
.L247:
  mov x0, #1
  mov x5, x0
.L248:
  mov x0, #1
  mov x4, x0
.L249:
  mov x1, x12
  mov x2, x11
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L320
.L250:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L251:
  ldr d2, [sp, #64]
  fadd d15, d13, d2
.L252:
  ldr d2, [sp, #64]
  fmul d14, d12, d2
.L253:
  mov x0, #1
  mov x13, x0
.L254:
  mov x1, x13
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L265
.L255:
  ldr d2, [sp, #64]
  fsub d3, d11, d2
.L256:
  fmul d3, d3, d15
.L257:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L258:
  ldr d2, [sp, #64]
  fsub d0, d10, d2
  str d0, [sp, #64]
.L259:
  fsub d3, d15, d14
.L260:
  fmul d3, d3, d9
.L261:
  fadd d3, d3, d8
.L262:
  mov x1, x13
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L263:
  add x13, x13, x9
.L264:
  b .L254
.L265:
  mov x0, #1
  mov x13, x0
.L266:
  mov x1, x13
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L318
.L267:
  mov x1, x13
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d5, [x8, x1, lsl #3]
.L268:
  mov x1, x13
  adrp x8, _arr_g@PAGE
  add x8, x8, _arr_g@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L269:
  mov x1, x13
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L270:
  ldr d2, [sp, #24]
  fadd d3, d3, d2
.L271:
  fdiv d3, d4, d3
.L272:
  fsub d0, d5, d3
  str d0, [sp, #48]
.L273:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16329, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L274:
  ldr d1, [sp, #48]
  fmov d2, d7
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L286
.L275:
  fmov d1, d6
  ldr d2, [sp, #48]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L277
.L276:
  b .L285
.L277:
  mov x1, x13
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L278:
  ldr d2, [sp, #48]
  fdiv d0, d3, d2
  str d0, [sp, #56]
.L279:
  ldr d1, [sp, #40]
  ldr d2, [sp, #56]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L281
.L280:
  b .L282
.L281:
  ldr x0, [sp, #40]
  str x0, [sp, #56]
.L282:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L284
.L283:
  b .L285
.L284:
  ldr x0, [sp, #32]
  str x0, [sp, #56]
.L285:
  b .L294
.L286:
  mov x1, x13
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L287:
  ldr d2, [sp, #48]
  fdiv d0, d3, d2
  str d0, [sp, #56]
.L288:
  ldr d1, [sp, #40]
  ldr d2, [sp, #56]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L290
.L289:
  b .L291
.L290:
  ldr x0, [sp, #40]
  str x0, [sp, #56]
.L291:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L293
.L292:
  b .L294
.L293:
  ldr x0, [sp, #32]
  str x0, [sp, #56]
.L294:
  mov x1, x13
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L295:
  mov x1, x13
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L296:
  ldr d2, [sp, #56]
  fmul d3, d3, d2
.L297:
  fadd d4, d4, d3
.L298:
  mov x1, x13
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L299:
  fmul d4, d4, d3
.L300:
  mov x1, x13
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L301:
  fadd d5, d4, d3
.L302:
  mov x1, x13
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L303:
  mov x1, x13
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L304:
  ldr d2, [sp, #56]
  fmul d3, d3, d2
.L305:
  fadd d3, d4, d3
.L306:
  fdiv d3, d5, d3
.L307:
  mov x1, x13
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L308:
  add x3, x13, x6
.L309:
  mov x1, x13
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L310:
  mov x1, x13
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L311:
  fsub d3, d4, d3
.L312:
  ldr d2, [sp, #56]
  fmul d4, d3, d2
.L313:
  mov x1, x13
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L314:
  fadd d3, d4, d3
.L315:
  mov x1, x3
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L316:
  add x13, x13, x5
.L317:
  b .L266
.L318:
  add x12, x12, x4
.L319:
  b .L249
.L320:
  mov x0, x13
  str x0, [sp, #240]
.L321:
  mov x0, x12
  str x0, [sp, #248]
.L322:
  str d15, [sp, #256]
.L323:
  str d14, [sp, #264]
.L324:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #240]
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
  ldr x9, [sp, #248]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print dk (float)
  ldr d0, [sp, #24]
  sub sp, sp, #32
  adrp x8, .Lname_dk@PAGE
  add x8, x8, .Lname_dk@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print s (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x8, .Lname_s@PAGE
  add x8, x8, .Lname_s@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #40]
  sub sp, sp, #32
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print di (float)
  ldr d0, [sp, #48]
  sub sp, sp, #32
  adrp x8, .Lname_di@PAGE
  add x8, x8, .Lname_di@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dn (float)
  ldr d0, [sp, #56]
  sub sp, sp, #32
  adrp x8, .Lname_dn@PAGE
  add x8, x8, .Lname_dn@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #64]
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
  ldr d0, [sp, #256]
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
  ldr d0, [sp, #264]
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
  ldp d15, d14, [sp, #272]
  ldp d13, d12, [sp, #288]
  ldp d11, d10, [sp, #304]
  ldp d9, d8, [sp, #320]
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
.Lname_dk:
  .asciz "dk"
.Lname_s:
  .asciz "s"
.Lname_t:
  .asciz "t"
.Lname_di:
  .asciz "di"
.Lname_dn:
  .asciz "dn"
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
.global _arr_x
.align 3
_arr_x:
  .space 8016
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_w
.align 3
_arr_w:
  .space 8016
.global _arr_v
.align 3
_arr_v:
  .space 8016
.global _arr_u
.align 3
_arr_u:
  .space 8016
.global _arr_g
.align 3
_arr_g:
  .space 8016
.global _arr_xx
.align 3
_arr_xx:
  .space 8016
.global _arr_vx
.align 3
_arr_vx:
  .space 8016
