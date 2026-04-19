.global _main
.align 2

_main:
  sub sp, sp, #1024
  str x30, [sp, #1016]
  str x29, [sp, #1008]
  add x29, sp, #1008
  // Save callee-saved registers
  str x28, [sp, #864]
  str x27, [sp, #872]
  str x26, [sp, #880]
  str x25, [sp, #888]
  str x24, [sp, #896]
  str x23, [sp, #904]
  str x22, [sp, #912]
  str x21, [sp, #920]
  str x20, [sp, #928]
  str x19, [sp, #936]
  str d15, [sp, #944]
  str d14, [sp, #952]
  str d13, [sp, #960]
  str d12, [sp, #968]
  str d11, [sp, #976]
  str d10, [sp, #984]
  str d9, [sp, #992]
  str d8, [sp, #1000]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  fmov d15, x0
  fmov d14, x0
  fmov d13, x0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d3, x0
  mov x10, #0
  mov x9, #0
  fmov d6, x0
  fmov d5, x0
  mov x7, #0
  mov x6, #0
  fmov d4, x0
  mov x5, #0
  mov x4, #0
  mov x3, #0
  mov x14, #0
  mov x13, #0
  fmov d8, x0
  fmov d7, x0
  mov x12, #0
  mov x11, #0
  str x0, [sp, #232]
  str x0, [sp, #240]
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]
  str x0, [sp, #272]
  str x0, [sp, #280]
  str x0, [sp, #288]
  str x0, [sp, #296]
  str x0, [sp, #304]
  str x0, [sp, #312]
  str x0, [sp, #320]
  str x0, [sp, #328]
  str x0, [sp, #336]
  str x0, [sp, #344]
  str x0, [sp, #352]
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
  str x0, [sp, #448]
  str x0, [sp, #456]
  str x0, [sp, #464]
  str x0, [sp, #472]
  str x0, [sp, #480]
  str x0, [sp, #488]
  str x0, [sp, #496]
  str x0, [sp, #504]
  str x0, [sp, #512]
  str x0, [sp, #520]
  str x0, [sp, #528]
  str x0, [sp, #536]
  str x0, [sp, #544]
  str x0, [sp, #552]
  str x0, [sp, #560]
  str x0, [sp, #568]
  str x0, [sp, #576]
  str x0, [sp, #584]
  str x0, [sp, #592]
  str x0, [sp, #600]
  str x0, [sp, #608]
  str x0, [sp, #616]
  str x0, [sp, #624]
  str x0, [sp, #632]
  str x0, [sp, #640]
  str x0, [sp, #648]
  str x0, [sp, #656]
  str x0, [sp, #664]
  str x0, [sp, #672]
  str x0, [sp, #680]
  str x0, [sp, #688]
  str x0, [sp, #696]
  str x0, [sp, #704]
  str x0, [sp, #712]
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
  str x0, [sp, #808]
  str x0, [sp, #816]
  str x0, [sp, #824]
  str x0, [sp, #832]
  str x0, [sp, #840]
  str x0, [sp, #848]
  str x0, [sp, #856]

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
  fmov d0, x0
  str d0, [sp, #32]
.L4:
  mov x0, #0
  fmov d15, x0
.L5:
  mov x0, #0
  fmov d14, x0
.L6:
  mov x0, #0
  fmov d13, x0
.L7:
  mov x0, #0
  fmov d12, x0
.L8:
  mov x0, #0
  fmov d11, x0
.L9:
  mov x0, #0
  fmov d10, x0
.L10:
  mov x0, #0
  fmov d9, x0
.L11:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L12:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L13:
  fadd d10, d3, d11
.L14:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L15:
  fmul d9, d3, d11
.L16:
  mov x0, #1
  str x0, [sp, #16]
.L17:
  mov x0, #25
  mov x10, x0
.L18:
  mov x0, #101
  mov x9, x0
.L19:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L20:
  mov x0, #0
  fmov d5, x0
.L21:
  mov x0, #1
  mov x7, x0
.L22:
  mov x0, #101
  mov x6, x0
.L23:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L24:
  mov x0, #1
  mov x5, x0
.L25:
  mov x0, #1
  mov x4, x0
.L26:
  ldr x1, [sp, #16]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L43
.L27:
  mov x0, #1
  str x0, [sp, #24]
.L28:
  ldr x1, [sp, #24]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L41
.L29:
  fsub d3, d6, d11
.L30:
  fmul d3, d3, d10
.L31:
  fadd d10, d3, d11
.L32:
  fsub d11, d5, d11
.L33:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L34:
  mul x3, x3, x6
.L35:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L36:
  fsub d3, d10, d9
.L37:
  fmul d3, d3, d4
.L38:
  mov x1, x3
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L39:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L40:
  b .L28
.L41:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L42:
  b .L26
.L43:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L44:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L45:
  fadd d10, d3, d11
.L46:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L47:
  fmul d9, d3, d11
.L48:
  mov x0, #1
  str x0, [sp, #16]
.L49:
  mov x0, #7
  mov x10, x0
.L50:
  mov x0, #101
  mov x9, x0
.L51:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L52:
  mov x0, #0
  fmov d5, x0
.L53:
  mov x0, #1
  mov x7, x0
.L54:
  mov x0, #101
  mov x6, x0
.L55:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L56:
  mov x0, #1
  mov x5, x0
.L57:
  mov x0, #1
  mov x4, x0
.L58:
  ldr x1, [sp, #16]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L75
.L59:
  mov x0, #1
  str x0, [sp, #24]
.L60:
  ldr x1, [sp, #24]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L73
.L61:
  fsub d3, d6, d11
.L62:
  fmul d3, d3, d10
.L63:
  fadd d10, d3, d11
.L64:
  fsub d11, d5, d11
.L65:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L66:
  mul x3, x3, x6
.L67:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L68:
  fsub d3, d10, d9
.L69:
  fmul d3, d3, d4
.L70:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L71:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L72:
  b .L60
.L73:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L74:
  b .L58
.L75:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L76:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L77:
  fadd d10, d3, d11
.L78:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L79:
  fmul d9, d3, d11
.L80:
  mov x0, #1
  str x0, [sp, #16]
.L81:
  mov x0, #7
  mov x14, x0
.L82:
  mov x0, #101
  mov x13, x0
.L83:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L84:
  mov x0, #0
  fmov d7, x0
.L85:
  mov x0, #1
  mov x12, x0
.L86:
  mov x0, #101
  mov x11, x0
.L87:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L88:
  mov x0, #1
  mov x10, x0
.L89:
  mov x0, #101
  mov x9, x0
.L90:
  mov x0, #0
  fmov d5, x0
.L91:
  mov x0, #1
  mov x7, x0
.L92:
  mov x0, #101
  mov x6, x0
.L93:
  movz x0, #43516
  movk x0, #54001, lsl #16
  movk x0, #25165, lsl #32
  movk x0, #16208, lsl #48
  fmov d4, x0
.L94:
  mov x0, #1
  mov x5, x0
.L95:
  mov x0, #1
  mov x4, x0
.L96:
  ldr x1, [sp, #16]
  mov x2, x14
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L123
.L97:
  mov x0, #1
  str x0, [sp, #24]
.L98:
  ldr x1, [sp, #24]
  mov x2, x13
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L121
.L99:
  fsub d3, d8, d11
.L100:
  fmul d3, d3, d10
.L101:
  fadd d10, d3, d11
.L102:
  fsub d11, d7, d11
.L103:
  ldr x1, [sp, #16]
  sub x3, x1, x12
.L104:
  mul x3, x3, x11
.L105:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L106:
  fsub d3, d10, d9
.L107:
  fmul d3, d3, d6
.L108:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L109:
  ldr x1, [sp, #16]
  sub x3, x1, x10
.L110:
  mul x3, x3, x9
.L111:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L112:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L113:
  fmov d1, d3
  fmov d2, d5
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L115
.L114:
  b .L119
.L115:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L116:
  mul x3, x3, x6
.L117:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L118:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  str d4, [x8, x1, lsl #3]
.L119:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L120:
  b .L98
.L121:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L122:
  b .L96
.L123:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L124:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L125:
  fadd d10, d3, d11
.L126:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L127:
  fmul d9, d3, d11
.L128:
  mov x0, #1
  str x0, [sp, #16]
.L129:
  mov x0, #7
  mov x10, x0
.L130:
  mov x0, #101
  mov x9, x0
.L131:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L132:
  mov x0, #0
  fmov d5, x0
.L133:
  mov x0, #1
  mov x7, x0
.L134:
  mov x0, #101
  mov x6, x0
.L135:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L136:
  mov x0, #1
  mov x5, x0
.L137:
  mov x0, #1
  mov x4, x0
.L138:
  ldr x1, [sp, #16]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L155
.L139:
  mov x0, #1
  str x0, [sp, #24]
.L140:
  ldr x1, [sp, #24]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L153
.L141:
  fsub d3, d6, d11
.L142:
  fmul d3, d3, d10
.L143:
  fadd d10, d3, d11
.L144:
  fsub d11, d5, d11
.L145:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L146:
  mul x3, x3, x6
.L147:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L148:
  fsub d3, d10, d9
.L149:
  fmul d3, d3, d4
.L150:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L151:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L152:
  b .L140
.L153:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L154:
  b .L138
.L155:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L156:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L157:
  fadd d10, d3, d11
.L158:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L159:
  fmul d9, d3, d11
.L160:
  mov x0, #1
  str x0, [sp, #16]
.L161:
  mov x0, #7
  mov x10, x0
.L162:
  mov x0, #101
  mov x9, x0
.L163:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L164:
  mov x0, #0
  fmov d5, x0
.L165:
  mov x0, #1
  mov x7, x0
.L166:
  mov x0, #101
  mov x6, x0
.L167:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L168:
  mov x0, #1
  mov x5, x0
.L169:
  mov x0, #1
  mov x4, x0
.L170:
  ldr x1, [sp, #16]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L187
.L171:
  mov x0, #1
  str x0, [sp, #24]
.L172:
  ldr x1, [sp, #24]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L185
.L173:
  fsub d3, d6, d11
.L174:
  fmul d3, d3, d10
.L175:
  fadd d10, d3, d11
.L176:
  fsub d11, d5, d11
.L177:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L178:
  mul x3, x3, x6
.L179:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L180:
  fsub d3, d10, d9
.L181:
  fmul d3, d3, d4
.L182:
  mov x1, x3
  adrp x8, _arr_vs@PAGE
  add x8, x8, _arr_vs@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L183:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L184:
  b .L172
.L185:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L186:
  b .L170
.L187:
  mov x0, #1
  str x0, [sp, #8]
.L188:
  movz x0, #54696
  movk x0, #64, lsl #16
  str x0, [sp, #232]
.L189:
  mov x0, #7
  str x0, [sp, #240]
.L190:
  mov x0, #101
  str x0, [sp, #248]
.L191:
  mov x0, #7
  str x0, [sp, #256]
.L192:
  mov x0, #1
  str x0, [sp, #264]
.L193:
  mov x0, #101
  str x0, [sp, #272]
.L194:
  mov x0, #101
  str x0, [sp, #280]
.L195:
  mov x0, #1
  str x0, [sp, #288]
.L196:
  mov x0, #101
  str x0, [sp, #296]
.L197:
  mov x0, #1
  str x0, [sp, #304]
.L198:
  mov x0, #101
  str x0, [sp, #312]
.L199:
  mov x0, #1
  str x0, [sp, #320]
.L200:
  mov x0, #101
  str x0, [sp, #328]
.L201:
  mov x0, #1
  str x0, [sp, #336]
.L202:
  mov x0, #101
  str x0, [sp, #344]
.L203:
  mov x0, #101
  str x0, [sp, #352]
.L204:
  mov x0, #1
  str x0, [sp, #360]
.L205:
  mov x0, #101
  str x0, [sp, #368]
.L206:
  mov x0, #1
  str x0, [sp, #376]
.L207:
  mov x0, #101
  str x0, [sp, #384]
.L208:
  mov x0, #101
  str x0, [sp, #392]
.L209:
  mov x0, #1
  str x0, [sp, #400]
.L210:
  mov x0, #1
  str x0, [sp, #408]
.L211:
  mov x0, #101
  str x0, [sp, #416]
.L212:
  mov x0, #1
  str x0, [sp, #424]
.L213:
  mov x0, #101
  str x0, [sp, #432]
.L214:
  mov x0, #1
  str x0, [sp, #440]
.L215:
  mov x0, #1
  str x0, [sp, #448]
.L216:
  mov x0, #101
  str x0, [sp, #456]
.L217:
  mov x0, #1
  str x0, [sp, #464]
.L218:
  mov x0, #1
  str x0, [sp, #472]
.L219:
  mov x0, #101
  str x0, [sp, #480]
.L220:
  mov x0, #1
  str x0, [sp, #488]
.L221:
  mov x0, #1
  str x0, [sp, #496]
.L222:
  mov x0, #101
  str x0, [sp, #504]
.L223:
  mov x0, #1
  str x0, [sp, #512]
.L224:
  mov x0, #101
  str x0, [sp, #520]
.L225:
  mov x0, #1
  str x0, [sp, #528]
.L226:
  mov x0, #101
  str x0, [sp, #536]
.L227:
  mov x0, #101
  str x0, [sp, #544]
.L228:
  mov x0, #1
  str x0, [sp, #552]
.L229:
  mov x0, #101
  str x0, [sp, #560]
.L230:
  mov x0, #2
  str x0, [sp, #568]
.L231:
  mov x0, #101
  str x0, [sp, #576]
.L232:
  mov x0, #1
  str x0, [sp, #584]
.L233:
  mov x0, #101
  str x0, [sp, #592]
.L234:
  mov x0, #1
  str x0, [sp, #600]
.L235:
  mov x0, #1
  str x0, [sp, #608]
.L236:
  mov x0, #101
  str x0, [sp, #616]
.L237:
  mov x0, #1
  str x0, [sp, #624]
.L238:
  mov x0, #101
  str x0, [sp, #632]
.L239:
  mov x0, #1
  str x0, [sp, #640]
.L240:
  mov x0, #1
  str x0, [sp, #648]
.L241:
  mov x0, #101
  str x0, [sp, #656]
.L242:
  mov x0, #1
  str x0, [sp, #664]
.L243:
  mov x0, #101
  str x0, [sp, #672]
.L244:
  mov x0, #2
  str x0, [sp, #680]
.L245:
  mov x0, #101
  str x0, [sp, #688]
.L246:
  mov x0, #1
  str x0, [sp, #696]
.L247:
  mov x0, #2
  str x0, [sp, #704]
.L248:
  mov x0, #101
  str x0, [sp, #712]
.L249:
  mov x0, #2
  mov x28, x0
.L250:
  mov x0, #101
  mov x27, x0
.L251:
  mov x0, #1
  mov x26, x0
.L252:
  mov x0, #2
  mov x25, x0
.L253:
  mov x0, #101
  mov x24, x0
.L254:
  mov x0, #2
  mov x23, x0
.L255:
  mov x0, #101
  mov x22, x0
.L256:
  mov x0, #1
  mov x21, x0
.L257:
  mov x0, #101
  mov x20, x0
.L258:
  mov x0, #1
  mov x19, x0
.L259:
  mov x0, #101
  mov x15, x0
.L260:
  mov x0, #1
  mov x14, x0
.L261:
  mov x0, #101
  mov x13, x0
.L262:
  mov x0, #1
  mov x12, x0
.L263:
  mov x0, #101
  mov x11, x0
.L264:
  mov x0, #0
  fmov d5, x0
.L265:
  mov x0, #1
  mov x10, x0
.L266:
  mov x0, #101
  mov x9, x0
.L267:
  mov x0, #0
  fmov d4, x0
.L268:
  mov x0, #1
  mov x7, x0
.L269:
  mov x0, #1
  mov x6, x0
.L270:
  mov x0, #1
  mov x5, x0
.L271:
  ldr x1, [sp, #8]
  ldr x2, [sp, #232]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L471
.L272:
  movz x0, #16777
  movk x0, #58720, lsl #16
  movk x0, #8912, lsl #32
  movk x0, #16299, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L273:
  movz x0, #42467
  movk x0, #50331, lsl #16
  movk x0, #45088, lsl #32
  movk x0, #16306, lsl #48
  fmov d15, x0
.L274:
  mov x0, #2
  str x0, [sp, #16]
.L275:
  ldr x1, [sp, #16]
  ldr x2, [sp, #240]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L469
.L276:
  mov x0, #2
  str x0, [sp, #24]
.L277:
  ldr x1, [sp, #24]
  ldr x2, [sp, #248]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L467
.L278:
  ldr x1, [sp, #256]
  ldr x2, [sp, #16]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L461
.L279:
  ldr x1, [sp, #16]
  ldr x2, [sp, #264]
  sub x3, x1, x2
.L280:
  ldr x2, [sp, #272]
  mul x3, x3, x2
.L281:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L282:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L283:
  ldr x1, [sp, #16]
  ldr x2, [sp, #280]
  mul x3, x1, x2
.L284:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L285:
  mov x1, x3
  cmp x1, #708
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L286:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L289
.L287:
  movz x0, #42467
  movk x0, #50331, lsl #16
  movk x0, #45088, lsl #32
  movk x0, #16306, lsl #48
  fmov d12, x0
.L288:
  b .L290
.L289:
  movz x0, #16777
  movk x0, #58720, lsl #16
  movk x0, #8912, lsl #32
  movk x0, #16299, lsl #48
  fmov d12, x0
.L290:
  ldr x1, [sp, #16]
  ldr x2, [sp, #288]
  sub x3, x1, x2
.L291:
  ldr x2, [sp, #296]
  mul x3, x3, x2
.L292:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L293:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L294:
  ldr x1, [sp, #16]
  ldr x2, [sp, #304]
  sub x3, x1, x2
.L295:
  ldr x2, [sp, #312]
  mul x3, x3, x2
.L296:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L297:
  ldr x2, [sp, #320]
  sub x3, x3, x2
.L298:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L299:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L324
.L300:
  ldr x1, [sp, #16]
  ldr x2, [sp, #328]
  mul x3, x1, x2
.L301:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L302:
  mov x1, x3
  cmp x1, #708
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L303:
  ldr x1, [sp, #16]
  ldr x2, [sp, #336]
  sub x3, x1, x2
.L304:
  ldr x2, [sp, #344]
  mul x3, x3, x2
.L305:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L306:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L307:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L313
.L308:
  ldr x1, [sp, #16]
  ldr x2, [sp, #352]
  mul x3, x1, x2
.L309:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L310:
  mov x1, x3
  cmp x1, #708
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L311:
  fmov d14, d3
.L312:
  b .L318
.L313:
  ldr x1, [sp, #16]
  ldr x2, [sp, #360]
  sub x3, x1, x2
.L314:
  ldr x2, [sp, #368]
  mul x3, x3, x2
.L315:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L316:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L317:
  fmov d14, d3
.L318:
  ldr x1, [sp, #16]
  ldr x2, [sp, #376]
  sub x3, x1, x2
.L319:
  ldr x2, [sp, #384]
  mul x3, x3, x2
.L320:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L321:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L322:
  fmov d13, d3
.L323:
  b .L352
.L324:
  ldr x1, [sp, #16]
  ldr x2, [sp, #392]
  mul x3, x1, x2
.L325:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L326:
  ldr x2, [sp, #400]
  sub x3, x3, x2
.L327:
  mov x1, x3
  cmp x1, #708
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L328:
  ldr x1, [sp, #16]
  ldr x2, [sp, #408]
  sub x3, x1, x2
.L329:
  ldr x2, [sp, #416]
  mul x3, x3, x2
.L330:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L331:
  ldr x2, [sp, #424]
  sub x3, x3, x2
.L332:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L333:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L340
.L334:
  ldr x1, [sp, #16]
  ldr x2, [sp, #432]
  mul x3, x1, x2
.L335:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L336:
  ldr x2, [sp, #440]
  sub x3, x3, x2
.L337:
  mov x1, x3
  cmp x1, #708
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L338:
  fmov d14, d3
.L339:
  b .L346
.L340:
  ldr x1, [sp, #16]
  ldr x2, [sp, #448]
  sub x3, x1, x2
.L341:
  ldr x2, [sp, #456]
  mul x3, x3, x2
.L342:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L343:
  ldr x2, [sp, #464]
  sub x3, x3, x2
.L344:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L345:
  fmov d14, d3
.L346:
  ldr x1, [sp, #16]
  ldr x2, [sp, #472]
  sub x3, x1, x2
.L347:
  ldr x2, [sp, #480]
  mul x3, x3, x2
.L348:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L349:
  ldr x2, [sp, #488]
  sub x3, x3, x2
.L350:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L351:
  fmov d13, d3
.L352:
  ldr x1, [sp, #16]
  ldr x2, [sp, #496]
  sub x3, x1, x2
.L353:
  ldr x2, [sp, #504]
  mul x3, x3, x2
.L354:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L355:
  ldr x1, [sp, #16]
  ldr x2, [sp, #512]
  sub x3, x1, x2
.L356:
  ldr x2, [sp, #520]
  mul x3, x3, x2
.L357:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L358:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L359:
  ldr x1, [sp, #16]
  ldr x2, [sp, #528]
  sub x3, x1, x2
.L360:
  ldr x2, [sp, #536]
  mul x3, x3, x2
.L361:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L362:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L363:
  fmul d6, d6, d3
.L364:
  fmul d3, d14, d14
.L365:
  fadd d3, d6, d3
.L366:
  fsqrt d3, d3
.L367:
  fmul d3, d3, d12
.L368:
  fdiv d3, d3, d13
.L369:
  mov x1, x4
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L370:
  ldr x1, [sp, #544]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L456
.L371:
  ldr x1, [sp, #16]
  ldr x2, [sp, #552]
  sub x3, x1, x2
.L372:
  ldr x2, [sp, #560]
  mul x3, x3, x2
.L373:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L374:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L375:
  ldr x1, [sp, #16]
  ldr x2, [sp, #568]
  sub x3, x1, x2
.L376:
  ldr x2, [sp, #576]
  mul x3, x3, x2
.L377:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L378:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L379:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L409
.L380:
  ldr x1, [sp, #16]
  ldr x2, [sp, #584]
  sub x3, x1, x2
.L381:
  ldr x2, [sp, #592]
  mul x3, x3, x2
.L382:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L383:
  ldr x2, [sp, #600]
  add x3, x3, x2
.L384:
  mov x1, x3
  cmp x1, #708
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L385:
  ldr x1, [sp, #16]
  ldr x2, [sp, #608]
  sub x3, x1, x2
.L386:
  ldr x2, [sp, #616]
  mul x3, x3, x2
.L387:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L388:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L389:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L397
.L390:
  ldr x1, [sp, #16]
  ldr x2, [sp, #624]
  sub x3, x1, x2
.L391:
  ldr x2, [sp, #632]
  mul x3, x3, x2
.L392:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L393:
  ldr x2, [sp, #640]
  add x3, x3, x2
.L394:
  mov x1, x3
  cmp x1, #708
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L395:
  fmov d14, d3
.L396:
  b .L402
.L397:
  ldr x1, [sp, #16]
  ldr x2, [sp, #648]
  sub x3, x1, x2
.L398:
  ldr x2, [sp, #656]
  mul x3, x3, x2
.L399:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L400:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L401:
  fmov d14, d3
.L402:
  ldr x1, [sp, #16]
  ldr x2, [sp, #664]
  sub x3, x1, x2
.L403:
  ldr x2, [sp, #672]
  mul x3, x3, x2
.L404:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L405:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L406:
  fmov d13, d3
.L407:
  movz x0, #16777
  movk x0, #58720, lsl #16
  movk x0, #8912, lsl #32
  movk x0, #16299, lsl #48
  fmov d12, x0
.L408:
  b .L437
.L409:
  ldr x1, [sp, #16]
  ldr x2, [sp, #680]
  sub x3, x1, x2
.L410:
  ldr x2, [sp, #688]
  mul x3, x3, x2
.L411:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L412:
  ldr x2, [sp, #696]
  add x3, x3, x2
.L413:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L414:
  ldr x1, [sp, #16]
  ldr x2, [sp, #704]
  sub x3, x1, x2
.L415:
  ldr x2, [sp, #712]
  mul x3, x3, x2
.L416:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L417:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L418:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L426
.L419:
  ldr x1, [sp, #16]
  sub x3, x1, x28
.L420:
  mul x3, x3, x27
.L421:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L422:
  add x3, x3, x26
.L423:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L424:
  fmov d14, d3
.L425:
  b .L431
.L426:
  ldr x1, [sp, #16]
  sub x3, x1, x25
.L427:
  mul x3, x3, x24
.L428:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L429:
  mov x1, x3
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L430:
  fmov d14, d3
.L431:
  ldr x1, [sp, #16]
  sub x3, x1, x23
.L432:
  mul x3, x3, x22
.L433:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L434:
  mov x1, x3
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L435:
  fmov d13, d3
.L436:
  movz x0, #42467
  movk x0, #50331, lsl #16
  movk x0, #45088, lsl #32
  movk x0, #16306, lsl #48
  fmov d12, x0
.L437:
  ldr x1, [sp, #16]
  sub x3, x1, x21
.L438:
  mul x3, x3, x20
.L439:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L440:
  ldr x1, [sp, #16]
  sub x3, x1, x19
.L441:
  mul x3, x3, x15
.L442:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L443:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x1, lsl #3]
.L444:
  ldr x1, [sp, #16]
  sub x3, x1, x14
.L445:
  mul x3, x3, x13
.L446:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L447:
  mov x1, x3
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L448:
  fmul d6, d6, d3
.L449:
  fmul d3, d14, d14
.L450:
  fadd d3, d6, d3
.L451:
  fsqrt d3, d3
.L452:
  fmul d3, d3, d12
.L453:
  fdiv d3, d3, d13
.L454:
  mov x1, x4
  adrp x8, _arr_vs@PAGE
  add x8, x8, _arr_vs@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L455:
  b .L460
.L456:
  ldr x1, [sp, #16]
  sub x3, x1, x12
.L457:
  mul x3, x3, x11
.L458:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L459:
  mov x1, x3
  adrp x8, _arr_vs@PAGE
  add x8, x8, _arr_vs@PAGEOFF
  str d5, [x8, x1, lsl #3]
.L460:
  b .L465
.L461:
  ldr x1, [sp, #16]
  sub x3, x1, x10
.L462:
  mul x3, x3, x9
.L463:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L464:
  mov x1, x3
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  str d4, [x8, x1, lsl #3]
.L465:
  ldr x1, [sp, #24]
  add x0, x1, x7
  str x0, [sp, #24]
.L466:
  b .L277
.L467:
  ldr x1, [sp, #16]
  add x0, x1, x6
  str x0, [sp, #16]
.L468:
  b .L275
.L469:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L470:
  b .L271
.L471:
  str d15, [sp, #808]
.L472:
  str d14, [sp, #816]
.L473:
  str d13, [sp, #824]
.L474:
  str d12, [sp, #832]
.L475:
  str d11, [sp, #840]
.L476:
  str d10, [sp, #848]
.L477:
  str d9, [sp, #856]
.L478:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print rep
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
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
  // print ar (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x8, .Lname_ar@PAGE
  add x8, x8, .Lname_ar@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print br (float)
  ldr d0, [sp, #808]
  sub sp, sp, #32
  adrp x8, .Lname_br@PAGE
  add x8, x8, .Lname_br@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print r (float)
  ldr d0, [sp, #816]
  sub sp, sp, #32
  adrp x8, .Lname_r@PAGE
  add x8, x8, .Lname_r@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print s (float)
  ldr d0, [sp, #824]
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
  ldr d0, [sp, #832]
  sub sp, sp, #32
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #840]
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
  ldr d0, [sp, #848]
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
  ldr d0, [sp, #856]
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
  ldr x28, [sp, #864]
  ldr x27, [sp, #872]
  ldr x26, [sp, #880]
  ldr x25, [sp, #888]
  ldr x24, [sp, #896]
  ldr x23, [sp, #904]
  ldr x22, [sp, #912]
  ldr x21, [sp, #920]
  ldr x20, [sp, #928]
  ldr x19, [sp, #936]
  ldr d15, [sp, #944]
  ldr d14, [sp, #952]
  ldr d13, [sp, #960]
  ldr d12, [sp, #968]
  ldr d11, [sp, #976]
  ldr d10, [sp, #984]
  ldr d9, [sp, #992]
  ldr d8, [sp, #1000]
  ldr x29, [sp, #1008]
  ldr x30, [sp, #1016]
  add sp, sp, #1024
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
.Lname_rep:
  .asciz "rep"
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_ar:
  .asciz "ar"
.Lname_br:
  .asciz "br"
.Lname_r:
  .asciz "r"
.Lname_s:
  .asciz "s"
.Lname_t:
  .asciz "t"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_vy
.align 3
_arr_vy:
  .space 20208
.global _arr_vh
.align 3
_arr_vh:
  .space 5664
.global _arr_vf
.align 3
_arr_vf:
  .space 5664
.global _arr_vg
.align 3
_arr_vg:
  .space 5664
.global _arr_vs
.align 3
_arr_vs:
  .space 5664
