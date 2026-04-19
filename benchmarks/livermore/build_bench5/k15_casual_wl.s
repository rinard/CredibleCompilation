.global _main
.align 2

_main:
  sub sp, sp, #1104
  str x30, [sp, #1096]
  str x29, [sp, #1088]
  add x29, sp, #1088
  // Save callee-saved registers
  str x28, [sp, #944]
  str x27, [sp, #952]
  str x26, [sp, #960]
  str x25, [sp, #968]
  str x24, [sp, #976]
  str x23, [sp, #984]
  str x22, [sp, #992]
  str x21, [sp, #1000]
  str x20, [sp, #1008]
  str x19, [sp, #1016]
  str d15, [sp, #1024]
  str d14, [sp, #1032]
  str d13, [sp, #1040]
  str d12, [sp, #1048]
  str d11, [sp, #1056]
  str d10, [sp, #1064]
  str d9, [sp, #1072]
  str d8, [sp, #1080]

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
  mov x13, #0
  mov x12, #0
  fmov d8, x0
  fmov d7, x0
  mov x11, #0
  str x0, [sp, #224]
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
  mov x28, #0
  str x0, [sp, #672]
  mov x27, #0
  str x0, [sp, #688]
  mov x26, #0
  mov x25, #0
  str x0, [sp, #712]
  mov x24, #0
  str x0, [sp, #728]
  mov x23, #0
  mov x22, #0
  str x0, [sp, #752]
  mov x21, #0
  str x0, [sp, #768]
  mov x20, #0
  str x0, [sp, #784]
  mov x19, #0
  str x0, [sp, #800]
  mov x15, #0
  str x0, [sp, #816]
  mov x14, #0
  str x0, [sp, #832]
  str x0, [sp, #840]
  str x0, [sp, #848]
  str x0, [sp, #856]
  str x0, [sp, #864]
  str x0, [sp, #872]
  str x0, [sp, #880]
  str x0, [sp, #888]
  str x0, [sp, #896]
  str x0, [sp, #904]
  str x0, [sp, #912]
  str x0, [sp, #920]
  str x0, [sp, #928]
  str x0, [sp, #936]

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
  cmp x1, x10
  b.gt .L42
.L27:
  mov x0, #1
  str x0, [sp, #24]
.L28:
  ldr x1, [sp, #24]
  cmp x1, x9
  b.gt .L40
.L29:
  fsub d3, d6, d11
.L30:
  fmadd d10, d3, d10, d11
.L31:
  fsub d11, d5, d11
.L32:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L33:
  mul x3, x3, x6
.L34:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L35:
  fsub d3, d10, d9
.L36:
  fmul d3, d3, d4
.L37:
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L38:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L39:
  b .L28
.L40:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L41:
  b .L26
.L42:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L43:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L44:
  fadd d10, d3, d11
.L45:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L46:
  fmul d9, d3, d11
.L47:
  mov x0, #1
  str x0, [sp, #16]
.L48:
  mov x0, #7
  mov x10, x0
.L49:
  mov x0, #101
  mov x9, x0
.L50:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L51:
  mov x0, #0
  fmov d5, x0
.L52:
  mov x0, #1
  mov x7, x0
.L53:
  mov x0, #101
  mov x6, x0
.L54:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L55:
  mov x0, #1
  mov x5, x0
.L56:
  mov x0, #1
  mov x4, x0
.L57:
  ldr x1, [sp, #16]
  cmp x1, x10
  b.gt .L73
.L58:
  mov x0, #1
  str x0, [sp, #24]
.L59:
  ldr x1, [sp, #24]
  cmp x1, x9
  b.gt .L71
.L60:
  fsub d3, d6, d11
.L61:
  fmadd d10, d3, d10, d11
.L62:
  fsub d11, d5, d11
.L63:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L64:
  mul x3, x3, x6
.L65:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L66:
  fsub d3, d10, d9
.L67:
  fmul d3, d3, d4
.L68:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L69:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L70:
  b .L59
.L71:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L72:
  b .L57
.L73:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L74:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L75:
  fadd d10, d3, d11
.L76:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L77:
  fmul d9, d3, d11
.L78:
  mov x0, #1
  str x0, [sp, #16]
.L79:
  mov x0, #7
  mov x13, x0
.L80:
  mov x0, #101
  mov x12, x0
.L81:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L82:
  mov x0, #0
  fmov d7, x0
.L83:
  mov x0, #1
  mov x11, x0
.L84:
  mov x0, #101
  mov x10, x0
.L85:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L86:
  mov x0, #1
  str x0, [sp, #224]
.L87:
  mov x0, #101
  mov x9, x0
.L88:
  mov x0, #0
  fmov d5, x0
.L89:
  mov x0, #1
  str x0, [sp, #232]
.L90:
  mov x0, #101
  mov x7, x0
.L91:
  movz x0, #43516
  movk x0, #54001, lsl #16
  movk x0, #25165, lsl #32
  movk x0, #16208, lsl #48
  fmov d4, x0
.L92:
  mov x0, #1
  mov x6, x0
.L93:
  mov x0, #1
  mov x5, x0
.L94:
  ldr x1, [sp, #16]
  cmp x1, x13
  b.gt .L120
.L95:
  mov x0, #1
  str x0, [sp, #24]
.L96:
  ldr x1, [sp, #24]
  cmp x1, x12
  b.gt .L118
.L97:
  fsub d3, d8, d11
.L98:
  fmadd d10, d3, d10, d11
.L99:
  fsub d11, d7, d11
.L100:
  ldr x1, [sp, #16]
  sub x4, x1, x11
.L101:
  mul x3, x4, x10
.L102:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L103:
  fsub d3, d10, d9
.L104:
  fmul d3, d3, d6
.L105:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L106:
.L107:
  mul x3, x4, x9
.L108:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L109:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L110:
  fmov d1, d3
  fmov d2, d5
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L112
.L111:
  b .L116
.L112:
  mov x3, x4
.L113:
  mul x3, x3, x7
.L114:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L115:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  str d4, [x8, x3, lsl #3]
.L116:
  ldr x1, [sp, #24]
  add x0, x1, x6
  str x0, [sp, #24]
.L117:
  b .L96
.L118:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L119:
  b .L94
.L120:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L121:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L122:
  fadd d10, d3, d11
.L123:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L124:
  fmul d9, d3, d11
.L125:
  mov x0, #1
  str x0, [sp, #16]
.L126:
  mov x0, #7
  mov x10, x0
.L127:
  mov x0, #101
  mov x9, x0
.L128:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L129:
  mov x0, #0
  fmov d5, x0
.L130:
  mov x0, #1
  mov x7, x0
.L131:
  mov x0, #101
  mov x6, x0
.L132:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L133:
  mov x0, #1
  mov x5, x0
.L134:
  mov x0, #1
  mov x4, x0
.L135:
  ldr x1, [sp, #16]
  cmp x1, x10
  b.gt .L151
.L136:
  mov x0, #1
  str x0, [sp, #24]
.L137:
  ldr x1, [sp, #24]
  cmp x1, x9
  b.gt .L149
.L138:
  fsub d3, d6, d11
.L139:
  fmadd d10, d3, d10, d11
.L140:
  fsub d11, d5, d11
.L141:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L142:
  mul x3, x3, x6
.L143:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L144:
  fsub d3, d10, d9
.L145:
  fmul d3, d3, d4
.L146:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L147:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L148:
  b .L137
.L149:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L150:
  b .L135
.L151:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L152:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L153:
  fadd d10, d3, d11
.L154:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L155:
  fmul d9, d3, d11
.L156:
  mov x0, #1
  str x0, [sp, #16]
.L157:
  mov x0, #7
  mov x10, x0
.L158:
  mov x0, #101
  mov x9, x0
.L159:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L160:
  mov x0, #0
  fmov d5, x0
.L161:
  mov x0, #1
  mov x7, x0
.L162:
  mov x0, #101
  mov x6, x0
.L163:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L164:
  mov x0, #1
  mov x5, x0
.L165:
  mov x0, #1
  mov x4, x0
.L166:
  ldr x1, [sp, #16]
  cmp x1, x10
  b.gt .L182
.L167:
  mov x0, #1
  str x0, [sp, #24]
.L168:
  ldr x1, [sp, #24]
  cmp x1, x9
  b.gt .L180
.L169:
  fsub d3, d6, d11
.L170:
  fmadd d10, d3, d10, d11
.L171:
  fsub d11, d5, d11
.L172:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L173:
  mul x3, x3, x6
.L174:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L175:
  fsub d3, d10, d9
.L176:
  fmul d3, d3, d4
.L177:
  adrp x8, _arr_vs@PAGE
  add x8, x8, _arr_vs@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L178:
  ldr x1, [sp, #24]
  add x0, x1, x5
  str x0, [sp, #24]
.L179:
  b .L168
.L180:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L181:
  b .L166
.L182:
  mov x0, #1
  str x0, [sp, #8]
.L183:
  movz x0, #54696
  movk x0, #64, lsl #16
  str x0, [sp, #240]
.L184:
  mov x0, #7
  str x0, [sp, #248]
.L185:
  mov x0, #101
  str x0, [sp, #256]
.L186:
  mov x0, #7
  str x0, [sp, #264]
.L187:
  mov x0, #1
  str x0, [sp, #272]
.L188:
  mov x0, #101
  str x0, [sp, #280]
.L189:
  mov x0, #101
  str x0, [sp, #288]
.L190:
  mov x0, #1
  str x0, [sp, #296]
.L191:
  mov x0, #101
  str x0, [sp, #304]
.L192:
  mov x0, #1
  str x0, [sp, #312]
.L193:
  mov x0, #101
  str x0, [sp, #320]
.L194:
  mov x0, #1
  str x0, [sp, #328]
.L195:
  mov x0, #101
  str x0, [sp, #336]
.L196:
  mov x0, #1
  str x0, [sp, #344]
.L197:
  mov x0, #101
  str x0, [sp, #352]
.L198:
  mov x0, #101
  str x0, [sp, #360]
.L199:
  mov x0, #1
  str x0, [sp, #368]
.L200:
  mov x0, #101
  str x0, [sp, #376]
.L201:
  mov x0, #1
  str x0, [sp, #384]
.L202:
  mov x0, #101
  str x0, [sp, #392]
.L203:
  mov x0, #101
  str x0, [sp, #400]
.L204:
  mov x0, #1
  str x0, [sp, #408]
.L205:
  mov x0, #1
  str x0, [sp, #416]
.L206:
  mov x0, #101
  str x0, [sp, #424]
.L207:
  mov x0, #1
  str x0, [sp, #432]
.L208:
  mov x0, #101
  str x0, [sp, #440]
.L209:
  mov x0, #1
  str x0, [sp, #448]
.L210:
  mov x0, #1
  str x0, [sp, #456]
.L211:
  mov x0, #101
  str x0, [sp, #464]
.L212:
  mov x0, #1
  str x0, [sp, #472]
.L213:
  mov x0, #1
  str x0, [sp, #480]
.L214:
  mov x0, #101
  str x0, [sp, #488]
.L215:
  mov x0, #1
  str x0, [sp, #496]
.L216:
  mov x0, #1
  str x0, [sp, #504]
.L217:
  mov x0, #101
  str x0, [sp, #512]
.L218:
  mov x0, #1
  str x0, [sp, #520]
.L219:
  mov x0, #101
  str x0, [sp, #528]
.L220:
  mov x0, #1
  str x0, [sp, #536]
.L221:
  mov x0, #101
  str x0, [sp, #544]
.L222:
  mov x0, #101
  str x0, [sp, #552]
.L223:
  mov x0, #1
  str x0, [sp, #560]
.L224:
  mov x0, #101
  str x0, [sp, #568]
.L225:
  mov x0, #2
  str x0, [sp, #576]
.L226:
  mov x0, #101
  str x0, [sp, #584]
.L227:
  mov x0, #1
  str x0, [sp, #592]
.L228:
  mov x0, #101
  str x0, [sp, #600]
.L229:
  mov x0, #1
  str x0, [sp, #608]
.L230:
  mov x0, #1
  str x0, [sp, #616]
.L231:
  mov x0, #101
  str x0, [sp, #624]
.L232:
  mov x0, #1
  str x0, [sp, #632]
.L233:
  mov x0, #101
  str x0, [sp, #640]
.L234:
  mov x0, #1
  str x0, [sp, #648]
.L235:
  mov x0, #1
  str x0, [sp, #656]
.L236:
  mov x0, #101
  mov x28, x0
.L237:
  mov x0, #1
  str x0, [sp, #672]
.L238:
  mov x0, #101
  mov x27, x0
.L239:
  mov x0, #2
  str x0, [sp, #688]
.L240:
  mov x0, #101
  mov x26, x0
.L241:
  mov x0, #1
  mov x25, x0
.L242:
  mov x0, #2
  str x0, [sp, #712]
.L243:
  mov x0, #101
  mov x24, x0
.L244:
  mov x0, #2
  str x0, [sp, #728]
.L245:
  mov x0, #101
  mov x23, x0
.L246:
  mov x0, #1
  mov x22, x0
.L247:
  mov x0, #2
  str x0, [sp, #752]
.L248:
  mov x0, #101
  mov x21, x0
.L249:
  mov x0, #2
  str x0, [sp, #768]
.L250:
  mov x0, #101
  mov x20, x0
.L251:
  mov x0, #1
  str x0, [sp, #784]
.L252:
  mov x0, #101
  mov x19, x0
.L253:
  mov x0, #1
  str x0, [sp, #800]
.L254:
  mov x0, #101
  mov x15, x0
.L255:
  mov x0, #1
  str x0, [sp, #816]
.L256:
  mov x0, #101
  mov x14, x0
.L257:
  mov x0, #1
  str x0, [sp, #832]
.L258:
  mov x0, #101
  mov x13, x0
.L259:
  mov x0, #0
  fmov d5, x0
.L260:
  mov x0, #1
  mov x12, x0
.L261:
  mov x0, #101
  mov x11, x0
.L262:
  mov x0, #0
  fmov d4, x0
.L263:
  mov x0, #1
  mov x10, x0
.L264:
  mov x0, #1
  mov x9, x0
.L265:
  mov x0, #1
  mov x7, x0
.L266:
  ldr x1, [sp, #8]
  ldr x2, [sp, #240]
  cmp x1, x2
  b.gt .L464
.L267:
  movz x0, #16777
  movk x0, #58720, lsl #16
  movk x0, #8912, lsl #32
  movk x0, #16299, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L268:
  movz x0, #42467
  movk x0, #50331, lsl #16
  movk x0, #45088, lsl #32
  movk x0, #16306, lsl #48
  fmov d15, x0
.L269:
  mov x0, #2
  str x0, [sp, #16]
.L270:
  ldr x1, [sp, #16]
  ldr x2, [sp, #248]
  cmp x1, x2
  b.gt .L462
.L271:
  mov x0, #2
  str x0, [sp, #24]
.L272:
  ldr x1, [sp, #24]
  ldr x2, [sp, #256]
  cmp x1, x2
  b.gt .L460
.L273:
  ldr x1, [sp, #264]
  ldr x2, [sp, #16]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L454
.L274:
  ldr x1, [sp, #16]
  ldr x2, [sp, #272]
  sub x5, x1, x2
.L275:
  ldr x2, [sp, #280]
  mul x3, x5, x2
.L276:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L277:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L278:
  ldr x1, [sp, #16]
  ldr x2, [sp, #288]
  mul x4, x1, x2
.L279:
  ldr x2, [sp, #24]
  add x3, x4, x2
.L280:
  cmp x3, #708
  b.ge .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L281:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L284
.L282:
  movz x0, #42467
  movk x0, #50331, lsl #16
  movk x0, #45088, lsl #32
  movk x0, #16306, lsl #48
  fmov d12, x0
.L283:
  b .L286
.L284:
  movz x0, #16777
  movk x0, #58720, lsl #16
  movk x0, #8912, lsl #32
  movk x0, #16299, lsl #48
  fmov d12, x0
.L285:
.L286:
  ldr x2, [sp, #304]
  mul x3, x5, x2
.L287:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L288:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L289:
  mov x6, x5
.L290:
  ldr x2, [sp, #320]
  mul x3, x6, x2
.L291:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L292:
  ldr x2, [sp, #328]
  sub x3, x3, x2
.L293:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L294:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L319
.L295:
  mov x5, x4
.L296:
  ldr x2, [sp, #24]
  add x3, x5, x2
.L297:
  cmp x3, #708
  b.ge .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L298:
  mov x4, x6
.L299:
  ldr x2, [sp, #352]
  mul x3, x4, x2
.L300:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L301:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L302:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L308
.L303:
  mov x3, x5
.L304:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L305:
  cmp x3, #708
  b.ge .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L306:
  fmov d14, d3
.L307:
  b .L313
.L308:
  mov x3, x4
.L309:
  ldr x2, [sp, #376]
  mul x3, x3, x2
.L310:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L311:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L312:
  fmov d14, d3
.L313:
  mov x3, x4
.L314:
  ldr x2, [sp, #392]
  mul x3, x3, x2
.L315:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L316:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L317:
  fmov d13, d3
.L318:
  b .L347
.L319:
  mov x5, x4
.L320:
  ldr x2, [sp, #24]
  add x3, x5, x2
.L321:
  ldr x2, [sp, #408]
  sub x3, x3, x2
.L322:
  cmp x3, #708
  b.ge .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L323:
  mov x4, x6
.L324:
  ldr x2, [sp, #424]
  mul x3, x4, x2
.L325:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L326:
  ldr x2, [sp, #432]
  sub x3, x3, x2
.L327:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L328:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L335
.L329:
  mov x3, x5
.L330:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L331:
  ldr x2, [sp, #448]
  sub x3, x3, x2
.L332:
  cmp x3, #708
  b.ge .Lbounds_err
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L333:
  fmov d14, d3
.L334:
  b .L341
.L335:
  mov x3, x4
.L336:
  ldr x2, [sp, #464]
  mul x3, x3, x2
.L337:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L338:
  ldr x2, [sp, #472]
  sub x3, x3, x2
.L339:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L340:
  fmov d14, d3
.L341:
  mov x3, x4
.L342:
  ldr x2, [sp, #488]
  mul x3, x3, x2
.L343:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L344:
  ldr x2, [sp, #496]
  sub x3, x3, x2
.L345:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L346:
  fmov d13, d3
.L347:
  mov x3, x6
.L348:
  ldr x2, [sp, #512]
  mul x4, x3, x2
.L349:
  ldr x2, [sp, #24]
  add x5, x4, x2
.L350:
  mov x4, x3
.L351:
  ldr x2, [sp, #528]
  mul x3, x4, x2
.L352:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L353:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L354:
.L355:
  ldr x2, [sp, #544]
  mul x3, x4, x2
.L356:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L357:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L358:
  fmul d3, d6, d3
.L359:
  fmadd d3, d14, d14, d3
.L360:
  fsqrt d3, d3
.L361:
  fmul d3, d3, d12
.L362:
  fdiv d3, d3, d13
.L363:
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  str d3, [x8, x5, lsl #3]
.L364:
  ldr x1, [sp, #552]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L449
.L365:
  mov x5, x4
.L366:
  ldr x2, [sp, #568]
  mul x3, x5, x2
.L367:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L368:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L369:
  ldr x1, [sp, #16]
  ldr x2, [sp, #576]
  sub x4, x1, x2
.L370:
  ldr x2, [sp, #584]
  mul x3, x4, x2
.L371:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L372:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L373:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L404
.L374:
  mov x4, x5
.L375:
  ldr x2, [sp, #600]
  mul x3, x4, x2
.L376:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L377:
  ldr x2, [sp, #608]
  add x3, x3, x2
.L378:
  cmp x3, #708
  b.ge .Lbounds_err
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L379:
.L380:
  ldr x2, [sp, #624]
  mul x3, x4, x2
.L381:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L382:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L383:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L391
.L384:
  mov x3, x4
.L385:
  ldr x2, [sp, #640]
  mul x3, x3, x2
.L386:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L387:
  ldr x2, [sp, #648]
  add x3, x3, x2
.L388:
  cmp x3, #708
  b.ge .Lbounds_err
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L389:
  fmov d14, d3
.L390:
  b .L396
.L391:
  mov x3, x4
.L392:
  mul x3, x3, x28
.L393:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L394:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L395:
  fmov d14, d3
.L396:
  mov x3, x4
.L397:
  mul x3, x3, x27
.L398:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L399:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L400:
  fmov d13, d3
.L401:
  movz x0, #16777
  movk x0, #58720, lsl #16
  movk x0, #8912, lsl #32
  movk x0, #16299, lsl #48
  fmov d12, x0
.L402:
  b .L431
.L403:
.L404:
  mul x3, x4, x26
.L405:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L406:
  add x3, x3, x25
.L407:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L408:
.L409:
  mul x3, x4, x24
.L410:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L411:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L412:
  fmov d1, d6
  fmov d2, d3
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L420
.L413:
  mov x3, x4
.L414:
  mul x3, x3, x23
.L415:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L416:
  add x3, x3, x22
.L417:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L418:
  fmov d14, d3
.L419:
  b .L425
.L420:
  mov x3, x4
.L421:
  mul x3, x3, x21
.L422:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L423:
  adrp x8, _arr_vg@PAGE
  add x8, x8, _arr_vg@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L424:
  fmov d14, d3
.L425:
  mov x3, x4
.L426:
  mul x3, x3, x20
.L427:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L428:
  adrp x8, _arr_vf@PAGE
  add x8, x8, _arr_vf@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L429:
  fmov d13, d3
.L430:
  movz x0, #42467
  movk x0, #50331, lsl #16
  movk x0, #45088, lsl #32
  movk x0, #16306, lsl #48
  fmov d12, x0
.L431:
  mov x3, x5
.L432:
  mul x4, x3, x19
.L433:
  ldr x2, [sp, #24]
  add x5, x4, x2
.L434:
  mov x4, x3
.L435:
  mul x3, x4, x15
.L436:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L437:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d6, [x8, x3, lsl #3]
.L438:
  mov x3, x4
.L439:
  mul x3, x3, x14
.L440:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L441:
  adrp x8, _arr_vh@PAGE
  add x8, x8, _arr_vh@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L442:
  fmul d3, d6, d3
.L443:
  fmadd d3, d14, d14, d3
.L444:
  fsqrt d3, d3
.L445:
  fmul d3, d3, d12
.L446:
  fdiv d3, d3, d13
.L447:
  adrp x8, _arr_vs@PAGE
  add x8, x8, _arr_vs@PAGEOFF
  str d3, [x8, x5, lsl #3]
.L448:
  b .L453
.L449:
  mov x3, x4
.L450:
  mul x3, x3, x13
.L451:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L452:
  adrp x8, _arr_vs@PAGE
  add x8, x8, _arr_vs@PAGEOFF
  str d5, [x8, x3, lsl #3]
.L453:
  b .L458
.L454:
  ldr x1, [sp, #16]
  sub x3, x1, x12
.L455:
  mul x3, x3, x11
.L456:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L457:
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  str d4, [x8, x3, lsl #3]
.L458:
  ldr x1, [sp, #24]
  add x0, x1, x10
  str x0, [sp, #24]
.L459:
  b .L272
.L460:
  ldr x1, [sp, #16]
  add x0, x1, x9
  str x0, [sp, #16]
.L461:
  b .L270
.L462:
  ldr x1, [sp, #8]
  add x0, x1, x7
  str x0, [sp, #8]
.L463:
  b .L266
.L464:
  mov x0, #4
  str x0, [sp, #840]
.L465:
  mov x0, #1
  str x0, [sp, #848]
.L466:
  mov x0, #3
  str x0, [sp, #856]
.L467:
  mov x0, #101
  str x0, [sp, #864]
.L468:
  mov x0, #303
  str x0, [sp, #872]
.L469:
  mov x0, #51
  str x0, [sp, #880]
.L470:
  mov x0, #354
  mov x3, x0
.L471:
  adrp x8, _arr_vy@PAGE
  add x8, x8, _arr_vy@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L472:
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
.L473:
  str d15, [sp, #888]
.L474:
  str d14, [sp, #896]
.L475:
  str d13, [sp, #904]
.L476:
  str d12, [sp, #912]
.L477:
  str d11, [sp, #920]
.L478:
  str d10, [sp, #928]
.L479:
  str d9, [sp, #936]
.L480:
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
  ldr d0, [sp, #888]
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
  ldr d0, [sp, #896]
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
  ldr d0, [sp, #904]
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
  ldr d0, [sp, #912]
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
  ldr d0, [sp, #920]
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
  ldr d0, [sp, #928]
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
  ldr d0, [sp, #936]
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
  ldr x28, [sp, #944]
  ldr x27, [sp, #952]
  ldr x26, [sp, #960]
  ldr x25, [sp, #968]
  ldr x24, [sp, #976]
  ldr x23, [sp, #984]
  ldr x22, [sp, #992]
  ldr x21, [sp, #1000]
  ldr x20, [sp, #1008]
  ldr x19, [sp, #1016]
  ldr d15, [sp, #1024]
  ldr d14, [sp, #1032]
  ldr d13, [sp, #1040]
  ldr d12, [sp, #1048]
  ldr d11, [sp, #1056]
  ldr d10, [sp, #1064]
  ldr d9, [sp, #1072]
  ldr d8, [sp, #1080]
  ldr x29, [sp, #1088]
  ldr x30, [sp, #1096]
  add sp, sp, #1104
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
