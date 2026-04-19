.global _main
.align 2

_main:
  sub sp, sp, #528
  str x30, [sp, #520]
  str x29, [sp, #512]
  add x29, sp, #512
  // Save callee-saved registers
  stp x28, x27, [sp, #392]
  stp x26, x25, [sp, #408]
  stp x24, x23, [sp, #424]
  stp x22, x21, [sp, #440]
  stp x20, x19, [sp, #456]
  stp d9, d8, [sp, #472]
  str d10, [sp, #488]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  fmov d3, x0
  mov x10, #0
  mov x9, #0
  fmov d10, x0
  fmov d5, x0
  mov x7, #0
  mov x6, #0
  fmov d4, x0
  mov x5, #0
  mov x4, #0
  mov x3, #0
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  str x0, [sp, #200]
  str x0, [sp, #208]
  str x0, [sp, #216]
  str x0, [sp, #224]
  str x0, [sp, #232]
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
  str x0, [sp, #360]
  str x0, [sp, #368]
  str x0, [sp, #376]
  str x0, [sp, #384]

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
  fmov d9, x0
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
  fmov d5, x0
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
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L39
.L23:
  mov x0, #1
  str x0, [sp, #16]
.L24:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L37
.L25:
  fsub d3, d10, d8
.L26:
  fmul d3, d3, d7
.L27:
  fadd d7, d3, d8
.L28:
  fsub d8, d5, d8
.L29:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L30:
  mul x3, x3, x6
.L31:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L32:
  fsub d3, d7, d6
.L33:
  fmul d3, d3, d4
.L34:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L35:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L36:
  b .L24
.L37:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L38:
  b .L22
.L39:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L40:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L41:
  fadd d7, d3, d8
.L42:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L43:
  fmul d6, d3, d8
.L44:
  mov x0, #1
  str x0, [sp, #8]
.L45:
  mov x0, #7
  mov x10, x0
.L46:
  mov x0, #101
  mov x9, x0
.L47:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L48:
  mov x0, #0
  fmov d5, x0
.L49:
  mov x0, #1
  mov x7, x0
.L50:
  mov x0, #101
  mov x6, x0
.L51:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L52:
  mov x0, #1
  mov x5, x0
.L53:
  mov x0, #1
  mov x4, x0
.L54:
  ldr x1, [sp, #8]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L71
.L55:
  mov x0, #1
  str x0, [sp, #16]
.L56:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L69
.L57:
  fsub d3, d10, d8
.L58:
  fmul d3, d3, d7
.L59:
  fadd d7, d3, d8
.L60:
  fsub d8, d5, d8
.L61:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L62:
  mul x3, x3, x6
.L63:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L64:
  fsub d3, d7, d6
.L65:
  fmul d3, d3, d4
.L66:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L67:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L68:
  b .L56
.L69:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L70:
  b .L54
.L71:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L72:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L73:
  fadd d7, d3, d8
.L74:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L75:
  fmul d6, d3, d8
.L76:
  mov x0, #1
  str x0, [sp, #8]
.L77:
  mov x0, #7
  mov x10, x0
.L78:
  mov x0, #101
  mov x9, x0
.L79:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L80:
  mov x0, #0
  fmov d5, x0
.L81:
  mov x0, #1
  mov x7, x0
.L82:
  mov x0, #101
  mov x6, x0
.L83:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L84:
  mov x0, #1
  mov x5, x0
.L85:
  mov x0, #1
  mov x4, x0
.L86:
  ldr x1, [sp, #8]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L103
.L87:
  mov x0, #1
  str x0, [sp, #16]
.L88:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L101
.L89:
  fsub d3, d10, d8
.L90:
  fmul d3, d3, d7
.L91:
  fadd d7, d3, d8
.L92:
  fsub d8, d5, d8
.L93:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L94:
  mul x3, x3, x6
.L95:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L96:
  fsub d3, d7, d6
.L97:
  fmul d3, d3, d4
.L98:
  mov x1, x3
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L99:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L100:
  b .L88
.L101:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L102:
  b .L86
.L103:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L104:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L105:
  fadd d7, d3, d8
.L106:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L107:
  fmul d6, d3, d8
.L108:
  mov x0, #1
  str x0, [sp, #8]
.L109:
  mov x0, #7
  mov x10, x0
.L110:
  mov x0, #101
  mov x9, x0
.L111:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L112:
  mov x0, #0
  fmov d5, x0
.L113:
  mov x0, #1
  mov x7, x0
.L114:
  mov x0, #101
  mov x6, x0
.L115:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L116:
  mov x0, #1
  mov x5, x0
.L117:
  mov x0, #1
  mov x4, x0
.L118:
  ldr x1, [sp, #8]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L135
.L119:
  mov x0, #1
  str x0, [sp, #16]
.L120:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L133
.L121:
  fsub d3, d10, d8
.L122:
  fmul d3, d3, d7
.L123:
  fadd d7, d3, d8
.L124:
  fsub d8, d5, d8
.L125:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L126:
  mul x3, x3, x6
.L127:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L128:
  fsub d3, d7, d6
.L129:
  fmul d3, d3, d4
.L130:
  mov x1, x3
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L131:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L132:
  b .L120
.L133:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L134:
  b .L118
.L135:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L136:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L137:
  fadd d7, d3, d8
.L138:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L139:
  fmul d6, d3, d8
.L140:
  mov x0, #1
  str x0, [sp, #8]
.L141:
  mov x0, #7
  mov x10, x0
.L142:
  mov x0, #101
  mov x9, x0
.L143:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L144:
  mov x0, #0
  fmov d5, x0
.L145:
  mov x0, #1
  mov x7, x0
.L146:
  mov x0, #101
  mov x6, x0
.L147:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L148:
  mov x0, #1
  mov x5, x0
.L149:
  mov x0, #1
  mov x4, x0
.L150:
  ldr x1, [sp, #8]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L167
.L151:
  mov x0, #1
  str x0, [sp, #16]
.L152:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L165
.L153:
  fsub d3, d10, d8
.L154:
  fmul d3, d3, d7
.L155:
  fadd d7, d3, d8
.L156:
  fsub d8, d5, d8
.L157:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L158:
  mul x3, x3, x6
.L159:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L160:
  fsub d3, d7, d6
.L161:
  fmul d3, d3, d4
.L162:
  mov x1, x3
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L163:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L164:
  b .L152
.L165:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L166:
  b .L150
.L167:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L168:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L169:
  fadd d7, d3, d8
.L170:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L171:
  fmul d6, d3, d8
.L172:
  mov x0, #1
  str x0, [sp, #8]
.L173:
  mov x0, #7
  mov x10, x0
.L174:
  mov x0, #101
  mov x9, x0
.L175:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L176:
  mov x0, #0
  fmov d5, x0
.L177:
  mov x0, #1
  mov x7, x0
.L178:
  mov x0, #101
  mov x6, x0
.L179:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L180:
  mov x0, #1
  mov x5, x0
.L181:
  mov x0, #1
  mov x4, x0
.L182:
  ldr x1, [sp, #8]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L199
.L183:
  mov x0, #1
  str x0, [sp, #16]
.L184:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L197
.L185:
  fsub d3, d10, d8
.L186:
  fmul d3, d3, d7
.L187:
  fadd d7, d3, d8
.L188:
  fsub d8, d5, d8
.L189:
  ldr x1, [sp, #8]
  sub x3, x1, x7
.L190:
  mul x3, x3, x6
.L191:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L192:
  fsub d3, d7, d6
.L193:
  fmul d3, d3, d4
.L194:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L195:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L196:
  b .L184
.L197:
  ldr x1, [sp, #8]
  add x0, x1, x4
  str x0, [sp, #8]
.L198:
  b .L182
.L199:
  mov x0, #1
  str x0, [sp, #24]
.L200:
  movz x0, #61320
  movk x0, #130, lsl #16
  str x0, [sp, #152]
.L201:
  mov x0, #6
  str x0, [sp, #160]
.L202:
  mov x0, #100
  str x0, [sp, #168]
.L203:
  mov x0, #101
  str x0, [sp, #176]
.L204:
  mov x0, #1
  str x0, [sp, #184]
.L205:
  mov x0, #101
  str x0, [sp, #192]
.L206:
  mov x0, #2
  str x0, [sp, #200]
.L207:
  mov x0, #101
  str x0, [sp, #208]
.L208:
  mov x0, #1
  str x0, [sp, #216]
.L209:
  mov x0, #101
  str x0, [sp, #224]
.L210:
  mov x0, #1
  str x0, [sp, #232]
.L211:
  mov x0, #101
  mov x28, x0
.L212:
  mov x0, #1
  mov x27, x0
.L213:
  mov x0, #1
  mov x26, x0
.L214:
  mov x0, #101
  mov x25, x0
.L215:
  mov x0, #1
  mov x24, x0
.L216:
  mov x0, #101
  mov x23, x0
.L217:
  mov x0, #1
  mov x22, x0
.L218:
  mov x0, #1
  mov x21, x0
.L219:
  mov x0, #101
  mov x20, x0
.L220:
  mov x0, #1
  mov x19, x0
.L221:
  mov x0, #101
  mov x15, x0
.L222:
  mov x0, #1
  mov x14, x0
.L223:
  mov x0, #101
  mov x13, x0
.L224:
  mov x0, #1
  mov x12, x0
.L225:
  mov x0, #101
  mov x11, x0
.L226:
  movz x0, #26214
  movk x0, #26214, lsl #16
  movk x0, #26214, lsl #32
  movk x0, #16326, lsl #48
  fmov d5, x0
.L227:
  mov x0, #1
  mov x10, x0
.L228:
  mov x0, #101
  mov x9, x0
.L229:
  mov x0, #1
  mov x7, x0
.L230:
  mov x0, #1
  mov x6, x0
.L231:
  mov x0, #1
  mov x5, x0
.L232:
  ldr x1, [sp, #24]
  ldr x2, [sp, #152]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L303
.L233:
  mov x0, #2
  str x0, [sp, #8]
.L234:
  ldr x1, [sp, #8]
  ldr x2, [sp, #160]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L301
.L235:
  mov x0, #2
  str x0, [sp, #16]
.L236:
  ldr x1, [sp, #16]
  ldr x2, [sp, #168]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L299
.L237:
  ldr x1, [sp, #8]
  ldr x2, [sp, #176]
  mul x3, x1, x2
.L238:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L239:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L240:
  ldr x1, [sp, #8]
  ldr x2, [sp, #184]
  sub x3, x1, x2
.L241:
  ldr x2, [sp, #192]
  mul x3, x3, x2
.L242:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L243:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L244:
  fmul d9, d4, d3
.L245:
  ldr x1, [sp, #8]
  ldr x2, [sp, #200]
  sub x3, x1, x2
.L246:
  ldr x2, [sp, #208]
  mul x3, x3, x2
.L247:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L248:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L249:
  ldr x1, [sp, #8]
  ldr x2, [sp, #216]
  sub x3, x1, x2
.L250:
  ldr x2, [sp, #224]
  mul x3, x3, x2
.L251:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L252:
  mov x1, x3
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L253:
  fmul d3, d4, d3
.L254:
  fadd d9, d9, d3
.L255:
  ldr x1, [sp, #8]
  ldr x2, [sp, #232]
  sub x3, x1, x2
.L256:
  mul x3, x3, x28
.L257:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L258:
  add x3, x3, x27
.L259:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L260:
  ldr x1, [sp, #8]
  sub x3, x1, x26
.L261:
  mul x3, x3, x25
.L262:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L263:
  mov x1, x3
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L264:
  fmul d3, d4, d3
.L265:
  fadd d9, d9, d3
.L266:
  ldr x1, [sp, #8]
  sub x3, x1, x24
.L267:
  mul x3, x3, x23
.L268:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L269:
  sub x3, x3, x22
.L270:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L271:
  ldr x1, [sp, #8]
  sub x3, x1, x21
.L272:
  mul x3, x3, x20
.L273:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L274:
  mov x1, x3
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L275:
  fmul d3, d4, d3
.L276:
  fadd d4, d9, d3
.L277:
  ldr x1, [sp, #8]
  sub x3, x1, x19
.L278:
  mul x3, x3, x15
.L279:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L280:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L281:
  fadd d9, d4, d3
.L282:
  ldr x1, [sp, #8]
  sub x3, x1, x14
.L283:
  mul x3, x3, x13
.L284:
  ldr x2, [sp, #16]
  add x4, x3, x2
.L285:
  ldr x1, [sp, #8]
  sub x3, x1, x12
.L286:
  mul x3, x3, x11
.L287:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L288:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L289:
  ldr x1, [sp, #8]
  sub x3, x1, x10
.L290:
  mul x3, x3, x9
.L291:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L292:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L293:
  fsub d3, d9, d3
.L294:
  fmul d3, d5, d3
.L295:
  fadd d3, d4, d3
.L296:
  mov x1, x4
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L297:
  ldr x1, [sp, #16]
  add x0, x1, x7
  str x0, [sp, #16]
.L298:
  b .L236
.L299:
  ldr x1, [sp, #8]
  add x0, x1, x6
  str x0, [sp, #8]
.L300:
  b .L234
.L301:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L302:
  b .L232
.L303:
  str d9, [sp, #360]
.L304:
  str d8, [sp, #368]
.L305:
  str d7, [sp, #376]
.L306:
  str d6, [sp, #384]
.L307:
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
  ldr d0, [sp, #360]
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
  ldr d0, [sp, #368]
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
  ldr d0, [sp, #376]
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
  ldr d0, [sp, #384]
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
  ldp x28, x27, [sp, #392]
  ldp x26, x25, [sp, #408]
  ldp x24, x23, [sp, #424]
  ldp x22, x21, [sp, #440]
  ldp x20, x19, [sp, #456]
  ldp d9, d8, [sp, #472]
  ldr d10, [sp, #488]
  ldr x29, [sp, #512]
  ldr x30, [sp, #520]
  add sp, sp, #528
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
