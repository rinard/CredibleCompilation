.global _main
.align 2

_main:
  sub sp, sp, #576
  str x30, [sp, #568]
  str x29, [sp, #560]
  add x29, sp, #560
  // Save callee-saved registers
  str x28, [sp, #448]
  str x27, [sp, #456]
  str x26, [sp, #464]
  str x25, [sp, #472]
  str x24, [sp, #480]
  str x23, [sp, #488]
  str x22, [sp, #496]
  str x21, [sp, #504]
  str x20, [sp, #512]
  str x19, [sp, #520]
  str d8, [sp, #528]
  str d10, [sp, #536]
  str d9, [sp, #544]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  fmov d5, x0
  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  fmov d3, x0
  mov x10, #0
  mov x9, #0
  fmov d10, x0
  fmov d9, x0
  mov x7, #0
  mov x6, #0
  fmov d4, x0
  mov x5, #0
  mov x4, #0
  mov x3, #0
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  str x0, [sp, #216]
  mov x23, #0
  str x0, [sp, #232]
  mov x22, #0
  mov x21, #0
  str x0, [sp, #256]
  mov x20, #0
  str x0, [sp, #272]
  mov x19, #0
  mov x15, #0
  str x0, [sp, #296]
  mov x14, #0
  str x0, [sp, #312]
  mov x13, #0
  str x0, [sp, #328]
  mov x12, #0
  str x0, [sp, #344]
  mov x11, #0
  str x0, [sp, #360]
  str x0, [sp, #368]
  str x0, [sp, #376]
  str x0, [sp, #384]
  str x0, [sp, #392]
  str x0, [sp, #400]
  str x0, [sp, #408]
  str x0, [sp, #416]
  str x0, [sp, #424]
  str x0, [sp, #432]
  str x0, [sp, #440]

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
  fmov d5, x0
.L4:
  mov x0, #0
  fmov d8, x0
.L5:
  mov x0, #0
  fmov d7, x0
.L6:
  mov x0, #0
  fmov d6, x0
.L7:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L8:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L9:
  fadd d7, d3, d8
.L10:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L11:
  fmul d6, d3, d8
.L12:
  mov x0, #1
  str x0, [sp, #8]
.L13:
  mov x0, #7
  mov x10, x0
.L14:
  mov x0, #101
  mov x9, x0
.L15:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L16:
  mov x0, #0
  fmov d9, x0
.L17:
  mov x0, #1
  mov x7, x0
.L18:
  mov x0, #101
  mov x6, x0
.L19:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L20:
  mov x0, #1
  mov x5, x0
.L21:
  mov x0, #1
  mov x4, x0
.L22:
  ldr x1, [sp, #8]
  cmp x1, x10
  b.gt .L38
.L23:
  mov x0, #1
  str x0, [sp, #16]
.L24:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L36
.L25:
  fsub d3, d10, d8
.L26:
  fmadd d7, d3, d7, d8
.L27:
  fsub d8, d9, d8
.L28:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L29:
  mul x3, x3, x6
.L30:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L31:
  fsub d3, d7, d6
.L32:
  fmul d3, d3, d4
.L33:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L34:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L35:
  b .L24
.L36:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L37:
  b .L22
.L38:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L40:
  fadd d7, d3, d8
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L42:
  fmul d6, d3, d8
.L43:
  mov x0, #1
  str x0, [sp, #8]
.L44:
  mov x0, #7
  mov x10, x0
.L45:
  mov x0, #101
  mov x9, x0
.L46:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L47:
  mov x0, #0
  fmov d9, x0
.L48:
  mov x0, #1
  mov x7, x0
.L49:
  mov x0, #101
  mov x6, x0
.L50:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L51:
  mov x0, #1
  mov x5, x0
.L52:
  mov x0, #1
  mov x4, x0
.L53:
  ldr x1, [sp, #8]
  cmp x1, x10
  b.gt .L69
.L54:
  mov x0, #1
  str x0, [sp, #16]
.L55:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L67
.L56:
  fsub d3, d10, d8
.L57:
  fmadd d7, d3, d7, d8
.L58:
  fsub d8, d9, d8
.L59:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L60:
  mul x3, x3, x6
.L61:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L62:
  fsub d3, d7, d6
.L63:
  fmul d3, d3, d4
.L64:
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L65:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L66:
  b .L55
.L67:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L68:
  b .L53
.L69:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L70:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L71:
  fadd d7, d3, d8
.L72:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L73:
  fmul d6, d3, d8
.L74:
  mov x0, #1
  str x0, [sp, #8]
.L75:
  mov x0, #7
  mov x10, x0
.L76:
  mov x0, #101
  mov x9, x0
.L77:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L78:
  mov x0, #0
  fmov d9, x0
.L79:
  mov x0, #1
  mov x7, x0
.L80:
  mov x0, #101
  mov x6, x0
.L81:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L82:
  mov x0, #1
  mov x5, x0
.L83:
  mov x0, #1
  mov x4, x0
.L84:
  ldr x1, [sp, #8]
  cmp x1, x10
  b.gt .L100
.L85:
  mov x0, #1
  str x0, [sp, #16]
.L86:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L98
.L87:
  fsub d3, d10, d8
.L88:
  fmadd d7, d3, d7, d8
.L89:
  fsub d8, d9, d8
.L90:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L91:
  mul x3, x3, x6
.L92:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L93:
  fsub d3, d7, d6
.L94:
  fmul d3, d3, d4
.L95:
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L96:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L97:
  b .L86
.L98:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L99:
  b .L84
.L100:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L101:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L102:
  fadd d7, d3, d8
.L103:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L104:
  fmul d6, d3, d8
.L105:
  mov x0, #1
  str x0, [sp, #8]
.L106:
  mov x0, #7
  mov x10, x0
.L107:
  mov x0, #101
  mov x9, x0
.L108:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L109:
  mov x0, #0
  fmov d9, x0
.L110:
  mov x0, #1
  mov x7, x0
.L111:
  mov x0, #101
  mov x6, x0
.L112:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L113:
  mov x0, #1
  mov x5, x0
.L114:
  mov x0, #1
  mov x4, x0
.L115:
  ldr x1, [sp, #8]
  cmp x1, x10
  b.gt .L131
.L116:
  mov x0, #1
  str x0, [sp, #16]
.L117:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L129
.L118:
  fsub d3, d10, d8
.L119:
  fmadd d7, d3, d7, d8
.L120:
  fsub d8, d9, d8
.L121:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L122:
  mul x3, x3, x6
.L123:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L124:
  fsub d3, d7, d6
.L125:
  fmul d3, d3, d4
.L126:
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L127:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L128:
  b .L117
.L129:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L130:
  b .L115
.L131:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L132:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L133:
  fadd d7, d3, d8
.L134:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L135:
  fmul d6, d3, d8
.L136:
  mov x0, #1
  str x0, [sp, #8]
.L137:
  mov x0, #7
  mov x10, x0
.L138:
  mov x0, #101
  mov x9, x0
.L139:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L140:
  mov x0, #0
  fmov d9, x0
.L141:
  mov x0, #1
  mov x7, x0
.L142:
  mov x0, #101
  mov x6, x0
.L143:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L144:
  mov x0, #1
  mov x5, x0
.L145:
  mov x0, #1
  mov x4, x0
.L146:
  ldr x1, [sp, #8]
  cmp x1, x10
  b.gt .L162
.L147:
  mov x0, #1
  str x0, [sp, #16]
.L148:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L160
.L149:
  fsub d3, d10, d8
.L150:
  fmadd d7, d3, d7, d8
.L151:
  fsub d8, d9, d8
.L152:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L153:
  mul x3, x3, x6
.L154:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L155:
  fsub d3, d7, d6
.L156:
  fmul d3, d3, d4
.L157:
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L158:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L159:
  b .L148
.L160:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L161:
  b .L146
.L162:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L163:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L164:
  fadd d7, d3, d8
.L165:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L166:
  fmul d6, d3, d8
.L167:
  mov x0, #1
  str x0, [sp, #8]
.L168:
  mov x0, #7
  mov x10, x0
.L169:
  mov x0, #101
  mov x9, x0
.L170:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L171:
  mov x0, #0
  fmov d9, x0
.L172:
  mov x0, #1
  mov x7, x0
.L173:
  mov x0, #101
  mov x6, x0
.L174:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L175:
  mov x0, #1
  mov x5, x0
.L176:
  mov x0, #1
  mov x4, x0
.L177:
  ldr x1, [sp, #8]
  cmp x1, x10
  b.gt .L193
.L178:
  mov x0, #1
  str x0, [sp, #16]
.L179:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L191
.L180:
  fsub d3, d10, d8
.L181:
  fmadd d7, d3, d7, d8
.L182:
  fsub d8, d9, d8
.L183:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L184:
  mul x3, x3, x6
.L185:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L186:
  fsub d3, d7, d6
.L187:
  fmul d3, d3, d4
.L188:
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L189:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L190:
  b .L179
.L191:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L192:
  b .L177
.L193:
  mov x0, #1
  str x0, [sp, #24]
.L194:
  movz x0, #61320
  movk x0, #130, lsl #16
  str x0, [sp, #152]
.L195:
  mov x0, #6
  str x0, [sp, #160]
.L196:
  mov x0, #100
  str x0, [sp, #168]
.L197:
  mov x0, #101
  mov x28, x0
.L198:
  mov x0, #1
  mov x27, x0
.L199:
  mov x0, #101
  mov x26, x0
.L200:
  mov x0, #2
  mov x25, x0
.L201:
  mov x0, #101
  mov x24, x0
.L202:
  mov x0, #1
  str x0, [sp, #216]
.L203:
  mov x0, #101
  mov x23, x0
.L204:
  mov x0, #1
  str x0, [sp, #232]
.L205:
  mov x0, #101
  mov x22, x0
.L206:
  mov x0, #1
  mov x21, x0
.L207:
  mov x0, #1
  str x0, [sp, #256]
.L208:
  mov x0, #101
  mov x20, x0
.L209:
  mov x0, #1
  str x0, [sp, #272]
.L210:
  mov x0, #101
  mov x19, x0
.L211:
  mov x0, #1
  mov x15, x0
.L212:
  mov x0, #1
  str x0, [sp, #296]
.L213:
  mov x0, #101
  mov x14, x0
.L214:
  mov x0, #1
  str x0, [sp, #312]
.L215:
  mov x0, #101
  mov x13, x0
.L216:
  mov x0, #1
  str x0, [sp, #328]
.L217:
  mov x0, #101
  mov x12, x0
.L218:
  mov x0, #1
  str x0, [sp, #344]
.L219:
  mov x0, #101
  mov x11, x0
.L220:
  movz x0, #26214
  movk x0, #26214, lsl #16
  movk x0, #26214, lsl #32
  movk x0, #16326, lsl #48
  fmov d9, x0
.L221:
  mov x0, #1
  str x0, [sp, #360]
.L222:
  mov x0, #101
  mov x10, x0
.L223:
  mov x0, #1
  mov x9, x0
.L224:
  mov x0, #1
  mov x7, x0
.L225:
  mov x0, #1
  mov x6, x0
.L226:
  ldr x1, [sp, #24]
  ldr x2, [sp, #152]
  cmp x1, x2
  b.gt .L293
.L227:
  mov x0, #2
  str x0, [sp, #8]
.L228:
  ldr x1, [sp, #8]
  ldr x2, [sp, #160]
  cmp x1, x2
  b.gt .L291
.L229:
  mov x0, #2
  str x0, [sp, #16]
.L230:
  ldr x1, [sp, #16]
  ldr x2, [sp, #168]
  cmp x1, x2
  b.gt .L289
.L231:
  ldr x1, [sp, #8]
  mul x3, x1, x28
.L232:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L233:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L234:
  ldr x1, [sp, #8]
  sub x4, x1, x27
.L235:
  mul x3, x4, x26
.L236:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L237:
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L238:
  fmul d5, d4, d3
.L239:
  ldr x1, [sp, #8]
  sub x3, x1, x25
.L240:
  mul x3, x3, x24
.L241:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L242:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L243:
.L244:
  mul x3, x4, x23
.L245:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L246:
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L247:
  fmadd d5, d4, d3, d5
.L248:
.L249:
  mul x3, x4, x22
.L250:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L251:
  add x3, x3, x21
.L252:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L253:
.L254:
  mul x3, x4, x20
.L255:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L256:
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L257:
  fmadd d5, d4, d3, d5
.L258:
.L259:
  mul x3, x4, x19
.L260:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L261:
  sub x3, x3, x15
.L262:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L263:
.L264:
  mul x3, x4, x14
.L265:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L266:
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L267:
  fmadd d4, d4, d3, d5
.L268:
.L269:
  mul x3, x4, x13
.L270:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L271:
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L272:
  fadd d5, d4, d3
.L273:
  mov x3, x4
.L274:
  mul x4, x3, x12
.L275:
  ldr x2, [sp, #16]
  add x5, x4, x2
.L276:
  mov x4, x3
.L277:
  mul x3, x4, x11
.L278:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L279:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L280:
  mov x3, x4
.L281:
  mul x3, x3, x10
.L282:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L283:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L284:
  fsub d3, d5, d3
.L285:
  fmadd d3, d9, d3, d4
.L286:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  str d3, [x8, x5, lsl #3]
.L287:
  ldr x1, [sp, #16]
  add x0, x1, x9
  str x0, [sp, #16]
.L288:
  b .L230
.L289:
  ldr x1, [sp, #8]
  add x0, x1, x7
  str x0, [sp, #8]
.L290:
  b .L228
.L291:
  ldr x1, [sp, #24]
  add x0, x1, x6
  str x0, [sp, #24]
.L292:
  b .L226
.L293:
  mov x0, #4
  str x0, [sp, #368]
.L294:
  mov x0, #1
  str x0, [sp, #376]
.L295:
  mov x0, #3
  str x0, [sp, #384]
.L296:
  mov x0, #101
  str x0, [sp, #392]
.L297:
  mov x0, #303
  str x0, [sp, #400]
.L298:
  mov x0, #51
  str x0, [sp, #408]
.L299:
  mov x0, #354
  mov x3, x0
.L300:
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L301:
  str d6, [sp, #56]
  str d7, [sp, #48]
  str d5, [sp, #32]
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d6, [sp, #56]
  ldr d7, [sp, #48]
  ldr d5, [sp, #32]
.L302:
  str d5, [sp, #416]
.L303:
  str d8, [sp, #424]
.L304:
  str d7, [sp, #432]
.L305:
  str d6, [sp, #440]
.L306:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print j
  ldr x9, [sp, #8]
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
  ldr x9, [sp, #16]
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
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print qa (float)
  ldr d0, [sp, #416]
  sub sp, sp, #32
  adrp x8, .Lname_qa@PAGE
  add x8, x8, .Lname_qa@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #424]
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
  ldr d0, [sp, #432]
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
  ldr d0, [sp, #440]
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
  ldr x28, [sp, #448]
  ldr x27, [sp, #456]
  ldr x26, [sp, #464]
  ldr x25, [sp, #472]
  ldr x24, [sp, #480]
  ldr x23, [sp, #488]
  ldr x22, [sp, #496]
  ldr x21, [sp, #504]
  ldr x20, [sp, #512]
  ldr x19, [sp, #520]
  ldr d8, [sp, #528]
  ldr d10, [sp, #536]
  ldr d9, [sp, #544]
  ldr x29, [sp, #560]
  ldr x30, [sp, #568]
  add sp, sp, #576
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
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_qa:
  .asciz "qa"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_za
.align 3
_arr_za:
  .space 5664
.global _arr_zr
.align 3
_arr_zr:
  .space 5664
.global _arr_zb
.align 3
_arr_zb:
  .space 5664
.global _arr_zu
.align 3
_arr_zu:
  .space 5664
.global _arr_zv
.align 3
_arr_zv:
  .space 5664
.global _arr_zz
.align 3
_arr_zz:
  .space 5664
