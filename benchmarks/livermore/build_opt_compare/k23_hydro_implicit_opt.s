.global _main
.align 2

_main:
  sub sp, sp, #640
  str x30, [sp, #632]
  str x29, [sp, #624]
  add x29, sp, #624
  // Save callee-saved registers
  str x21, [sp, #512]
  str x20, [sp, #520]
  str x19, [sp, #528]
  str x28, [sp, #536]
  str x27, [sp, #544]
  str x26, [sp, #552]
  str x25, [sp, #560]
  str x24, [sp, #568]
  str x23, [sp, #576]
  str x22, [sp, #584]
  str d8, [sp, #592]
  str d10, [sp, #600]
  str d9, [sp, #608]
  str d11, [sp, #616]

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
  mov x9, #0
  mov x8, #0
  fmov d10, x0
  fmov d9, x0
  mov x7, #0
  mov x6, #0
  fmov d4, x0
  mov x5, #0
  mov x4, #0
  mov x3, #0
  mov x21, #0
  mov x20, #0
  mov x19, #0
  mov x15, #0
  str x0, [sp, #184]
  mov x14, #0
  fmov d11, x0
  str x0, [sp, #208]
  mov x13, #0
  str x0, [sp, #224]
  mov x12, #0
  str x0, [sp, #240]
  mov x11, #0
  str x0, [sp, #256]
  mov x10, #0
  str x0, [sp, #272]
  str x0, [sp, #280]
  str x0, [sp, #288]
  str x0, [sp, #296]
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  mov x23, #0
  str x0, [sp, #352]
  mov x22, #0
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
  str x0, [sp, #448]
  str x0, [sp, #456]
  str x0, [sp, #464]
  str x0, [sp, #472]
  str x0, [sp, #480]
  str x0, [sp, #488]
  str x0, [sp, #496]
  str x0, [sp, #504]

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
  mov x9, x0
.L14:
  mov x0, #101
  mov x8, x0
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
  cmp x1, x9
  b.gt .L38
.L23:
  mov x0, #1
  str x0, [sp, #16]
.L24:
  ldr x1, [sp, #16]
  cmp x1, x8
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
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  str d3, [x0, x3, lsl #3]
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
  mov x9, x0
.L45:
  mov x0, #101
  mov x8, x0
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
  cmp x1, x9
  b.gt .L69
.L54:
  mov x0, #1
  str x0, [sp, #16]
.L55:
  ldr x1, [sp, #16]
  cmp x1, x8
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
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  str d3, [x0, x3, lsl #3]
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
  mov x9, x0
.L76:
  mov x0, #101
  mov x8, x0
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
  cmp x1, x9
  b.gt .L100
.L85:
  mov x0, #1
  str x0, [sp, #16]
.L86:
  ldr x1, [sp, #16]
  cmp x1, x8
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
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  str d3, [x0, x3, lsl #3]
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
  mov x9, x0
.L107:
  mov x0, #101
  mov x8, x0
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
  cmp x1, x9
  b.gt .L131
.L116:
  mov x0, #1
  str x0, [sp, #16]
.L117:
  ldr x1, [sp, #16]
  cmp x1, x8
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
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  str d3, [x0, x3, lsl #3]
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
  mov x9, x0
.L138:
  mov x0, #101
  mov x8, x0
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
  cmp x1, x9
  b.gt .L162
.L147:
  mov x0, #1
  str x0, [sp, #16]
.L148:
  ldr x1, [sp, #16]
  cmp x1, x8
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
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  str d3, [x0, x3, lsl #3]
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
  mov x9, x0
.L169:
  mov x0, #101
  mov x8, x0
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
  cmp x1, x9
  b.gt .L193
.L178:
  mov x0, #1
  str x0, [sp, #16]
.L179:
  ldr x1, [sp, #16]
  cmp x1, x8
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
  adrp x0, _arr_zz@PAGE
  add x0, x0, _arr_zz@PAGEOFF
  str d3, [x0, x3, lsl #3]
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
  str x0, [sp, #8]
.L194:
  mov x0, #7
  mov x21, x0
.L195:
  mov x0, #101
  mov x20, x0
.L196:
  mov x0, #1
  mov x19, x0
.L197:
  mov x0, #101
  mov x15, x0
.L198:
  mov x0, #1
  str x0, [sp, #184]
.L199:
  mov x0, #101
  mov x14, x0
.L200:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d11, x0
.L201:
  mov x0, #1
  str x0, [sp, #208]
.L202:
  mov x0, #101
  mov x13, x0
.L203:
  mov x0, #1
  str x0, [sp, #224]
.L204:
  mov x0, #101
  mov x12, x0
.L205:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L206:
  mov x0, #1
  str x0, [sp, #240]
.L207:
  mov x0, #101
  mov x11, x0
.L208:
  mov x0, #1
  str x0, [sp, #256]
.L209:
  mov x0, #101
  mov x10, x0
.L210:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d9, x0
.L211:
  mov x0, #1
  str x0, [sp, #272]
.L212:
  mov x0, #101
  mov x9, x0
.L213:
  mov x0, #1
  str x0, [sp, #280]
.L214:
  mov x0, #101
  mov x8, x0
.L215:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L216:
  mov x0, #1
  mov x7, x0
.L217:
  mov x0, #1
  mov x6, x0
.L218:
  ldr x1, [sp, #8]
  cmp x1, x21
  b.gt .L261
.L219:
  mov x0, #1
  str x0, [sp, #16]
.L220:
  ldr x1, [sp, #16]
  cmp x1, x20
  b.gt .L259
.L221:
  ldr x1, [sp, #8]
  sub x4, x1, x19
.L222:
  mul x3, x4, x15
.L223:
  ldr x2, [sp, #16]
  add x5, x3, x2
.L224:
  mov x0, x4
  mov x4, x0
.L225:
  mul x3, x4, x14
.L226:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L227:
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L228:
  fmul d3, d3, d11
.L229:
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  str d3, [x0, x5, lsl #3]
.L230:
  mov x0, x4
  mov x4, x0
.L231:
  mul x3, x4, x13
.L232:
  ldr x2, [sp, #16]
  add x5, x3, x2
.L233:
  mov x0, x4
  mov x4, x0
.L234:
  mul x3, x4, x12
.L235:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L236:
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L237:
  fmul d3, d3, d10
.L238:
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  str d3, [x0, x5, lsl #3]
.L239:
  mov x0, x4
  mov x4, x0
.L240:
  mul x3, x4, x11
.L241:
  ldr x2, [sp, #16]
  add x5, x3, x2
.L242:
  mov x0, x4
  mov x4, x0
.L243:
  mul x3, x4, x10
.L244:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L245:
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L246:
  fmul d3, d3, d9
.L247:
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  str d3, [x0, x5, lsl #3]
.L248:
  mov x0, x4
  mov x5, x0
.L249:
  mul x3, x5, x9
.L250:
  ldr x2, [sp, #16]
  add x4, x3, x2
.L251:
  mov x0, x5
  mov x3, x0
.L252:
  mul x3, x3, x8
.L253:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L254:
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L255:
  fmul d3, d3, d4
.L256:
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  str d3, [x0, x4, lsl #3]
.L257:
  ldr x1, [sp, #16]
  add x0, x1, x7
  str x0, [sp, #16]
.L258:
  b .L220
.L259:
  ldr x1, [sp, #8]
  add x0, x1, x6
  str x0, [sp, #8]
.L260:
  b .L218
.L261:
  mov x0, #1
  str x0, [sp, #24]
.L262:
  movz x0, #61320
  movk x0, #130, lsl #16
  str x0, [sp, #288]
.L263:
  mov x0, #6
  str x0, [sp, #296]
.L264:
  mov x0, #100
  mov x28, x0
.L265:
  mov x0, #101
  mov x27, x0
.L266:
  mov x0, #1
  mov x26, x0
.L267:
  mov x0, #101
  mov x25, x0
.L268:
  mov x0, #2
  mov x24, x0
.L269:
  mov x0, #101
  mov x23, x0
.L270:
  mov x0, #1
  str x0, [sp, #352]
.L271:
  mov x0, #101
  mov x22, x0
.L272:
  mov x0, #1
  str x0, [sp, #368]
.L273:
  mov x0, #101
  mov x21, x0
.L274:
  mov x0, #1
  mov x20, x0
.L275:
  mov x0, #1
  str x0, [sp, #376]
.L276:
  mov x0, #101
  mov x19, x0
.L277:
  mov x0, #1
  str x0, [sp, #384]
.L278:
  mov x0, #101
  mov x15, x0
.L279:
  mov x0, #1
  mov x14, x0
.L280:
  mov x0, #1
  str x0, [sp, #392]
.L281:
  mov x0, #101
  mov x13, x0
.L282:
  mov x0, #1
  str x0, [sp, #400]
.L283:
  mov x0, #101
  mov x12, x0
.L284:
  mov x0, #1
  str x0, [sp, #408]
.L285:
  mov x0, #101
  mov x11, x0
.L286:
  mov x0, #1
  str x0, [sp, #416]
.L287:
  mov x0, #101
  mov x10, x0
.L288:
  movz x0, #26214
  movk x0, #26214, lsl #16
  movk x0, #26214, lsl #32
  movk x0, #16326, lsl #48
  fmov d9, x0
.L289:
  mov x0, #1
  str x0, [sp, #424]
.L290:
  mov x0, #101
  mov x9, x0
.L291:
  mov x0, #1
  mov x8, x0
.L292:
  mov x0, #1
  mov x7, x0
.L293:
  mov x0, #1
  mov x6, x0
.L294:
  ldr x1, [sp, #24]
  ldr x2, [sp, #288]
  cmp x1, x2
  b.gt .L361
.L295:
  mov x0, #2
  str x0, [sp, #8]
.L296:
  ldr x1, [sp, #8]
  ldr x2, [sp, #296]
  cmp x1, x2
  b.gt .L359
.L297:
  mov x0, #2
  str x0, [sp, #16]
.L298:
  ldr x1, [sp, #16]
  cmp x1, x28
  b.gt .L357
.L299:
  ldr x1, [sp, #8]
  mul x3, x1, x27
.L300:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L301:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L302:
  ldr x1, [sp, #8]
  sub x4, x1, x26
.L303:
  mul x3, x4, x25
.L304:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L305:
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L306:
  fmul d5, d4, d3
.L307:
  ldr x1, [sp, #8]
  sub x3, x1, x24
.L308:
  mul x3, x3, x23
.L309:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L310:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L311:
  mov x0, x4
  mov x4, x0
.L312:
  mul x3, x4, x22
.L313:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L314:
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L315:
  fmadd d5, d4, d3, d5
.L316:
  mov x0, x4
  mov x4, x0
.L317:
  mul x3, x4, x21
.L318:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L319:
  add x3, x3, x20
.L320:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L321:
  mov x0, x4
  mov x4, x0
.L322:
  mul x3, x4, x19
.L323:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L324:
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L325:
  fmadd d5, d4, d3, d5
.L326:
  mov x0, x4
  mov x4, x0
.L327:
  mul x3, x4, x15
.L328:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L329:
  sub x3, x3, x14
.L330:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L331:
  mov x0, x4
  mov x4, x0
.L332:
  mul x3, x4, x13
.L333:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L334:
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L335:
  fmadd d4, d4, d3, d5
.L336:
  mov x0, x4
  mov x4, x0
.L337:
  mul x3, x4, x12
.L338:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L339:
  adrp x0, _arr_zz@PAGE
  add x0, x0, _arr_zz@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L340:
  fadd d5, d4, d3
.L341:
  mov x0, x4
  mov x3, x0
.L342:
  mul x4, x3, x11
.L343:
  ldr x2, [sp, #16]
  add x5, x4, x2
.L344:
  mov x0, x3
  mov x4, x0
.L345:
  mul x3, x4, x10
.L346:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L347:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L348:
  mov x0, x4
  mov x3, x0
.L349:
  mul x3, x3, x9
.L350:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L351:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L352:
  fsub d3, d5, d3
.L353:
  fmadd d3, d9, d3, d4
.L354:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  str d3, [x0, x5, lsl #3]
.L355:
  ldr x1, [sp, #16]
  add x0, x1, x8
  str x0, [sp, #16]
.L356:
  b .L298
.L357:
  ldr x1, [sp, #8]
  add x0, x1, x7
  str x0, [sp, #8]
.L358:
  b .L296
.L359:
  ldr x1, [sp, #24]
  add x0, x1, x6
  str x0, [sp, #24]
.L360:
  b .L294
.L361:
  mov x0, #4
  str x0, [sp, #432]
.L362:
  mov x0, #1
  str x0, [sp, #440]
.L363:
  mov x0, #3
  str x0, [sp, #448]
.L364:
  mov x0, #101
  str x0, [sp, #456]
.L365:
  mov x0, #303
  str x0, [sp, #464]
.L366:
  mov x0, #51
  str x0, [sp, #472]
.L367:
  mov x0, #354
  mov x3, x0
.L368:
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L369:
  str d5, [sp, #32]
  str d7, [sp, #48]
  str d6, [sp, #56]
  str d3, [sp, #64]
  str x9, [sp, #72]
  str x8, [sp, #80]
  str x7, [sp, #104]
  str x6, [sp, #112]
  str d4, [sp, #120]
  str x5, [sp, #128]
  str x4, [sp, #136]
  str x3, [sp, #144]
  str x15, [sp, #176]
  str x14, [sp, #192]
  str x13, [sp, #216]
  str x12, [sp, #232]
  str x11, [sp, #248]
  str x10, [sp, #264]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_369@PAGE
  add x0, x0, .Lfmt_print_369@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d5, [sp, #32]
  ldr d7, [sp, #48]
  ldr d6, [sp, #56]
  ldr d3, [sp, #64]
  ldr x9, [sp, #72]
  ldr x8, [sp, #80]
  ldr x7, [sp, #104]
  ldr x6, [sp, #112]
  ldr d4, [sp, #120]
  ldr x5, [sp, #128]
  ldr x4, [sp, #136]
  ldr x3, [sp, #144]
  ldr x15, [sp, #176]
  ldr x14, [sp, #192]
  ldr x13, [sp, #216]
  ldr x12, [sp, #232]
  ldr x11, [sp, #248]
  ldr x10, [sp, #264]
.L370:
  str d5, [sp, #480]
.L371:
  str d8, [sp, #488]
.L372:
  str d7, [sp, #496]
.L373:
  str d6, [sp, #504]
.L374:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print j
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x1, .Lname_j@PAGE
  add x1, x1, .Lname_j@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #16]
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
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print qa (float)
  ldr d0, [sp, #480]
  sub sp, sp, #32
  adrp x1, .Lname_qa@PAGE
  add x1, x1, .Lname_qa@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #488]
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
  ldr d0, [sp, #496]
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
  ldr d0, [sp, #504]
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
  ldr x21, [sp, #512]
  ldr x20, [sp, #520]
  ldr x19, [sp, #528]
  ldr x28, [sp, #536]
  ldr x27, [sp, #544]
  ldr x26, [sp, #552]
  ldr x25, [sp, #560]
  ldr x24, [sp, #568]
  ldr x23, [sp, #576]
  ldr x22, [sp, #584]
  ldr d8, [sp, #592]
  ldr d10, [sp, #600]
  ldr d9, [sp, #608]
  ldr d11, [sp, #616]
  ldr x29, [sp, #624]
  ldr x30, [sp, #632]
  add sp, sp, #640
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

.Lfmt_print_369:
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
