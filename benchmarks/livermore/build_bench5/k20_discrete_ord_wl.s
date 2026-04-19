.global _main
.align 2

_main:
  sub sp, sp, #352
  str x30, [sp, #344]
  str x29, [sp, #336]
  add x29, sp, #336
  // Save callee-saved registers
  str d15, [sp, #272]
  str d14, [sp, #280]
  str d13, [sp, #288]
  str d12, [sp, #296]
  str d11, [sp, #304]
  str d10, [sp, #312]
  str d9, [sp, #320]
  str d8, [sp, #328]

  // Initialize all variables to 0
  mov x0, #0

  mov x12, #0
  mov x11, #0
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
  mov x10, #0
  fmov d13, x0
  fmov d12, x0
  mov x9, #0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #232]
  str x0, [sp, #240]
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]

.L0:
  mov x0, #0
  mov x12, x0
.L1:
  mov x0, #0
  mov x11, x0
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
  mov x12, x0
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
  cmp x12, x4
  b.gt .L30
.L22:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L23:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L24:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L25:
  fsub d3, d15, d14
.L26:
  fmul d3, d3, d4
.L27:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L28:
  add x12, x12, x3
.L29:
  b .L21
.L30:
  mov x0, #15
  mov x3, x0
.L31:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L32:
  str d3, [sp, #24]
.L33:
  mov x0, #32
  mov x3, x0
.L34:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L35:
  str d3, [sp, #32]
.L36:
  mov x0, #36
  mov x3, x0
.L37:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L38:
  str d3, [sp, #40]
.L39:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L40:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L41:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L42:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L43:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L44:
  mov x0, #1
  mov x12, x0
.L45:
  mov x0, #1001
  mov x4, x0
.L46:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L47:
  mov x0, #0
  fmov d5, x0
.L48:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L49:
  mov x0, #1
  mov x3, x0
.L50:
  cmp x12, x4
  b.gt .L59
.L51:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L52:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L53:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L54:
  fsub d3, d15, d14
.L55:
  fmul d3, d3, d4
.L56:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L57:
  add x12, x12, x3
.L58:
  b .L50
.L59:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L60:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L61:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L63:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L64:
  mov x0, #1
  mov x12, x0
.L65:
  mov x0, #1001
  mov x4, x0
.L66:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L67:
  mov x0, #0
  fmov d5, x0
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
  cmp x12, x4
  b.gt .L79
.L71:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L72:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L73:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L74:
  fsub d3, d15, d14
.L75:
  fmul d3, d3, d4
.L76:
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L77:
  add x12, x12, x3
.L78:
  b .L70
.L79:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L80:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L81:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L82:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L83:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L84:
  mov x0, #1
  mov x12, x0
.L85:
  mov x0, #1001
  mov x4, x0
.L86:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L87:
  mov x0, #0
  fmov d5, x0
.L88:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L89:
  mov x0, #1
  mov x3, x0
.L90:
  cmp x12, x4
  b.gt .L99
.L91:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L92:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L93:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L94:
  fsub d3, d15, d14
.L95:
  fmul d3, d3, d4
.L96:
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L97:
  add x12, x12, x3
.L98:
  b .L90
.L99:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L100:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L101:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L102:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L103:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L104:
  mov x0, #1
  mov x12, x0
.L105:
  mov x0, #1001
  mov x4, x0
.L106:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L107:
  mov x0, #0
  fmov d5, x0
.L108:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L109:
  mov x0, #1
  mov x3, x0
.L110:
  cmp x12, x4
  b.gt .L119
.L111:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L112:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L113:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L114:
  fsub d3, d15, d14
.L115:
  fmul d3, d3, d4
.L116:
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L117:
  add x12, x12, x3
.L118:
  b .L110
.L119:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L120:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L121:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L122:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L123:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L124:
  mov x0, #1
  mov x12, x0
.L125:
  mov x0, #1001
  mov x4, x0
.L126:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L127:
  mov x0, #0
  fmov d5, x0
.L128:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L129:
  mov x0, #1
  mov x3, x0
.L130:
  cmp x12, x4
  b.gt .L139
.L131:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L132:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L133:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L134:
  fsub d3, d15, d14
.L135:
  fmul d3, d3, d4
.L136:
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L137:
  add x12, x12, x3
.L138:
  b .L130
.L139:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L140:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L141:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L142:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L143:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L144:
  mov x0, #1
  mov x12, x0
.L145:
  mov x0, #1001
  mov x4, x0
.L146:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L147:
  mov x0, #0
  fmov d5, x0
.L148:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L149:
  mov x0, #1
  mov x3, x0
.L150:
  cmp x12, x4
  b.gt .L159
.L151:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L152:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L153:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L154:
  fsub d3, d15, d14
.L155:
  fmul d3, d3, d4
.L156:
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L157:
  add x12, x12, x3
.L158:
  b .L150
.L159:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L160:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L161:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L162:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L163:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L164:
  mov x0, #1
  mov x12, x0
.L165:
  mov x0, #1001
  mov x4, x0
.L166:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L167:
  mov x0, #0
  fmov d5, x0
.L168:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L169:
  mov x0, #1
  mov x3, x0
.L170:
  cmp x12, x4
  b.gt .L179
.L171:
  ldr d2, [sp, #64]
  fsub d3, d6, d2
.L172:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L173:
  ldr d2, [sp, #64]
  fsub d0, d5, d2
  str d0, [sp, #64]
.L174:
  fsub d3, d15, d14
.L175:
  fmul d3, d3, d4
.L176:
  adrp x8, _arr_g@PAGE
  add x8, x8, _arr_g@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L177:
  add x12, x12, x3
.L178:
  b .L170
.L179:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L180:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L181:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L182:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L183:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L184:
  mov x0, #1
  mov x12, x0
.L185:
  mov x0, #1001
  mov x4, x0
.L186:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d7, x0
.L187:
  mov x0, #0
  fmov d6, x0
.L188:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d5, x0
.L189:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d4, x0
.L190:
  mov x0, #1
  mov x3, x0
.L191:
  cmp x12, x4
  b.gt .L201
.L192:
  ldr d2, [sp, #64]
  fsub d3, d7, d2
.L193:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L194:
  ldr d2, [sp, #64]
  fsub d0, d6, d2
  str d0, [sp, #64]
.L195:
  fsub d3, d15, d14
.L196:
  fmul d3, d3, d5
.L197:
  fadd d3, d3, d4
.L198:
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L199:
  add x12, x12, x3
.L200:
  b .L191
.L201:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L202:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L203:
  ldr d2, [sp, #64]
  fadd d15, d3, d2
.L204:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L205:
  ldr d2, [sp, #64]
  fmul d14, d3, d2
.L206:
  mov x0, #1
  mov x12, x0
.L207:
  mov x0, #1001
  mov x4, x0
.L208:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d7, x0
.L209:
  mov x0, #0
  fmov d6, x0
.L210:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d5, x0
.L211:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d4, x0
.L212:
  mov x0, #1
  mov x3, x0
.L213:
  cmp x12, x4
  b.gt .L223
.L214:
  ldr d2, [sp, #64]
  fsub d3, d7, d2
.L215:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L216:
  ldr d2, [sp, #64]
  fsub d0, d6, d2
  str d0, [sp, #64]
.L217:
  fsub d3, d15, d14
.L218:
  fmul d3, d3, d5
.L219:
  fadd d3, d3, d4
.L220:
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L221:
  add x12, x12, x3
.L222:
  b .L213
.L223:
  mov x0, #1
  mov x11, x0
.L224:
  movz x0, #62672
  movk x0, #23, lsl #16
  mov x10, x0
.L225:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d13, x0
.L226:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d12, x0
.L227:
  mov x0, #1001
  mov x9, x0
.L228:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L229:
  mov x0, #0
  fmov d10, x0
.L230:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d9, x0
.L231:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L232:
  mov x0, #1
  mov x7, x0
.L233:
  mov x0, #1000
  mov x6, x0
.L234:
  mov x0, #0
  fmov d7, x0
.L235:
  mov x0, #0
  fmov d6, x0
.L236:
  mov x0, #1
  mov x5, x0
.L237:
  mov x0, #1
  str x0, [sp, #232]
.L238:
  mov x0, #1
  mov x4, x0
.L239:
  cmp x11, x10
  b.gt .L307
.L240:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L241:
  ldr d2, [sp, #64]
  fadd d15, d13, d2
.L242:
  ldr d2, [sp, #64]
  fmul d14, d12, d2
.L243:
  mov x0, #1
  mov x12, x0
.L244:
  cmp x12, x9
  b.gt .L254
.L245:
  ldr d2, [sp, #64]
  fsub d3, d11, d2
.L246:
  ldr d0, [sp, #64]
  fmadd d15, d3, d15, d0
.L247:
  ldr d2, [sp, #64]
  fsub d0, d10, d2
  str d0, [sp, #64]
.L248:
  fsub d3, d15, d14
.L249:
  fmul d3, d3, d9
.L250:
  fadd d3, d3, d8
.L251:
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L252:
  add x12, x12, x7
.L253:
  b .L244
.L254:
  mov x0, #1
  mov x12, x0
.L255:
  cmp x12, x6
  b.gt .L305
.L256:
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d5, [x8, x12, lsl #3]
.L257:
  adrp x8, _arr_g@PAGE
  add x8, x8, _arr_g@PAGEOFF
  ldr d4, [x8, x12, lsl #3]
.L258:
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L259:
  ldr d2, [sp, #24]
  fadd d3, d3, d2
.L260:
  fdiv d3, d4, d3
.L261:
  fsub d0, d5, d3
  str d0, [sp, #48]
.L262:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16329, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L263:
  ldr d1, [sp, #48]
  fmov d2, d7
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L275
.L264:
  fmov d1, d6
  ldr d2, [sp, #48]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L266
.L265:
  b .L274
.L266:
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L267:
  ldr d2, [sp, #48]
  fdiv d0, d3, d2
  str d0, [sp, #56]
.L268:
  ldr d1, [sp, #40]
  ldr d2, [sp, #56]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L270
.L269:
  b .L271
.L270:
  ldr x0, [sp, #40]
  str x0, [sp, #56]
.L271:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L273
.L272:
  b .L274
.L273:
  ldr x0, [sp, #32]
  str x0, [sp, #56]
.L274:
  b .L283
.L275:
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L276:
  ldr d2, [sp, #48]
  fdiv d0, d3, d2
  str d0, [sp, #56]
.L277:
  ldr d1, [sp, #40]
  ldr d2, [sp, #56]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L279
.L278:
  b .L280
.L279:
  ldr x0, [sp, #40]
  str x0, [sp, #56]
.L280:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L282
.L281:
  b .L283
.L282:
  ldr x0, [sp, #32]
  str x0, [sp, #56]
.L283:
  adrp x8, _arr_w@PAGE
  add x8, x8, _arr_w@PAGEOFF
  ldr d4, [x8, x12, lsl #3]
.L284:
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L285:
  ldr d2, [sp, #56]
  fmadd d4, d3, d2, d4
.L286:
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L287:
  fmul d4, d4, d3
.L288:
  adrp x8, _arr_u@PAGE
  add x8, x8, _arr_u@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L289:
  fadd d5, d4, d3
.L290:
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  ldr d4, [x8, x12, lsl #3]
.L291:
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L292:
  ldr d2, [sp, #56]
  fmadd d3, d3, d2, d4
.L293:
  fdiv d3, d5, d3
.L294:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x12, lsl #3]
.L295:
  add x3, x12, x5
.L296:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d4, [x8, x12, lsl #3]
.L297:
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L298:
  fsub d3, d4, d3
.L299:
  ldr d2, [sp, #56]
  fmul d4, d3, d2
.L300:
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x12, lsl #3]
.L301:
  fadd d3, d4, d3
.L302:
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L303:
  mov x12, x3
.L304:
  b .L255
.L305:
  add x11, x11, x4
.L306:
  b .L239
.L307:
  mov x0, #1
  mov x3, x0
.L308:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L309:
  str x11, [sp, #16]
  str x12, [sp, #8]
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x11, [sp, #16]
  ldr x12, [sp, #8]
.L310:
  str x12, [sp, #240]
.L311:
  str x11, [sp, #248]
.L312:
  str d15, [sp, #256]
.L313:
  str d14, [sp, #264]
.L314:
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
  ldr d15, [sp, #272]
  ldr d14, [sp, #280]
  ldr d13, [sp, #288]
  ldr d12, [sp, #296]
  ldr d11, [sp, #304]
  ldr d10, [sp, #312]
  ldr d9, [sp, #320]
  ldr d8, [sp, #328]
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
.Lfmt_printint:
  .asciz "%ld\n"
.Lfmt_printfloat:
  .asciz "%f\n"
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
