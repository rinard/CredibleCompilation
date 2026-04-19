.global _main
.align 2

_main:
  sub sp, sp, #1472
  str x30, [sp, #1464]
  str x29, [sp, #1456]
  add x29, sp, #1456
  // Save callee-saved registers
  str x19, [sp, #1320]
  str x28, [sp, #1328]
  str x27, [sp, #1336]
  str x26, [sp, #1344]
  str x25, [sp, #1352]
  str x24, [sp, #1360]
  str x23, [sp, #1368]
  str x22, [sp, #1376]
  str x21, [sp, #1384]
  str x20, [sp, #1392]
  str d9, [sp, #1400]
  str d8, [sp, #1408]
  str d11, [sp, #1416]
  str d10, [sp, #1424]
  str d12, [sp, #1432]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  fmov d5, x0
  fmov d3, x0
  mov x10, #0
  mov x9, #0
  fmov d11, x0
  fmov d10, x0
  mov x7, #0
  mov x6, #0
  fmov d4, x0
  mov x5, #0
  mov x4, #0
  mov x3, #0
  fmov d12, x0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  str x0, [sp, #216]
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
  str x0, [sp, #664]
  str x0, [sp, #672]
  str x0, [sp, #680]
  str x0, [sp, #688]
  str x0, [sp, #696]
  str x0, [sp, #704]
  str x0, [sp, #712]
  str x0, [sp, #720]
  str x0, [sp, #728]
  str x0, [sp, #736]
  str x0, [sp, #744]
  str x0, [sp, #752]
  str x0, [sp, #760]
  str x0, [sp, #768]
  str x0, [sp, #776]
  str x0, [sp, #784]
  str x0, [sp, #792]
  str x0, [sp, #800]
  str x0, [sp, #808]
  str x0, [sp, #816]
  str x0, [sp, #824]
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
  str x0, [sp, #944]
  str x0, [sp, #952]
  str x0, [sp, #960]
  str x0, [sp, #968]
  str x0, [sp, #976]
  str x0, [sp, #984]
  str x0, [sp, #992]
  str x0, [sp, #1000]
  str x0, [sp, #1008]
  str x0, [sp, #1016]
  str x0, [sp, #1024]
  str x0, [sp, #1032]
  str x0, [sp, #1040]
  str x0, [sp, #1048]
  str x0, [sp, #1056]
  str x0, [sp, #1064]
  str x0, [sp, #1072]
  str x0, [sp, #1080]
  str x0, [sp, #1088]
  str x0, [sp, #1096]
  str x0, [sp, #1104]
  str x0, [sp, #1112]
  str x0, [sp, #1120]
  str x0, [sp, #1128]
  str x0, [sp, #1136]
  str x0, [sp, #1144]
  str x0, [sp, #1152]
  str x0, [sp, #1160]
  str x0, [sp, #1168]
  str x0, [sp, #1176]
  str x0, [sp, #1184]
  str x0, [sp, #1192]
  str x0, [sp, #1200]
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  mov x23, #0
  mov x22, #0
  mov x21, #0
  mov x20, #0
  str x0, [sp, #1280]
  str x0, [sp, #1288]
  str x0, [sp, #1296]
  str x0, [sp, #1304]
  str x0, [sp, #1312]

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
  mov x0, #0
  fmov d5, x0
.L8:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L10:
  fadd d6, d3, d7
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L12:
  fmul d5, d3, d7
.L13:
  mov x0, #1
  str x0, [sp, #24]
.L14:
  mov x0, #7
  mov x10, x0
.L15:
  mov x0, #101
  mov x9, x0
.L16:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L17:
  mov x0, #0
  fmov d10, x0
.L18:
  mov x0, #1
  mov x7, x0
.L19:
  mov x0, #101
  mov x6, x0
.L20:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L21:
  mov x0, #1
  mov x5, x0
.L22:
  mov x0, #1
  mov x4, x0
.L23:
  ldr x1, [sp, #24]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L40
.L24:
  mov x0, #1
  str x0, [sp, #16]
.L25:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L38
.L26:
  fsub d3, d11, d7
.L27:
  fmul d3, d3, d6
.L28:
  fadd d6, d3, d7
.L29:
  fsub d7, d10, d7
.L30:
  ldr x1, [sp, #24]
  sub x3, x1, x7
.L31:
  mul x3, x3, x6
.L32:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L33:
  fsub d3, d6, d5
.L34:
  fmul d3, d3, d4
.L35:
  mov x1, x3
  adrp x8, _arr_zp@PAGE
  add x8, x8, _arr_zp@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L36:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L37:
  b .L25
.L38:
  ldr x1, [sp, #24]
  add x0, x1, x4
  str x0, [sp, #24]
.L39:
  b .L23
.L40:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L41:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L42:
  fadd d6, d3, d7
.L43:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L44:
  fmul d5, d3, d7
.L45:
  mov x0, #1
  str x0, [sp, #24]
.L46:
  mov x0, #7
  mov x10, x0
.L47:
  mov x0, #101
  mov x9, x0
.L48:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L49:
  mov x0, #0
  fmov d10, x0
.L50:
  mov x0, #1
  mov x7, x0
.L51:
  mov x0, #101
  mov x6, x0
.L52:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L53:
  mov x0, #1
  mov x5, x0
.L54:
  mov x0, #1
  mov x4, x0
.L55:
  ldr x1, [sp, #24]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L72
.L56:
  mov x0, #1
  str x0, [sp, #16]
.L57:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L70
.L58:
  fsub d3, d11, d7
.L59:
  fmul d3, d3, d6
.L60:
  fadd d6, d3, d7
.L61:
  fsub d7, d10, d7
.L62:
  ldr x1, [sp, #24]
  sub x3, x1, x7
.L63:
  mul x3, x3, x6
.L64:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L65:
  fsub d3, d6, d5
.L66:
  fmul d3, d3, d4
.L67:
  mov x1, x3
  adrp x8, _arr_zq@PAGE
  add x8, x8, _arr_zq@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L68:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L69:
  b .L57
.L70:
  ldr x1, [sp, #24]
  add x0, x1, x4
  str x0, [sp, #24]
.L71:
  b .L55
.L72:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L73:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L74:
  fadd d6, d3, d7
.L75:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L76:
  fmul d5, d3, d7
.L77:
  mov x0, #1
  str x0, [sp, #24]
.L78:
  mov x0, #7
  mov x10, x0
.L79:
  mov x0, #101
  mov x9, x0
.L80:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L81:
  mov x0, #0
  fmov d10, x0
.L82:
  mov x0, #1
  mov x7, x0
.L83:
  mov x0, #101
  mov x6, x0
.L84:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L85:
  mov x0, #1
  mov x5, x0
.L86:
  mov x0, #1
  mov x4, x0
.L87:
  ldr x1, [sp, #24]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L104
.L88:
  mov x0, #1
  str x0, [sp, #16]
.L89:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L102
.L90:
  fsub d3, d11, d7
.L91:
  fmul d3, d3, d6
.L92:
  fadd d6, d3, d7
.L93:
  fsub d7, d10, d7
.L94:
  ldr x1, [sp, #24]
  sub x3, x1, x7
.L95:
  mul x3, x3, x6
.L96:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L97:
  fsub d3, d6, d5
.L98:
  fmul d3, d3, d4
.L99:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L100:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L101:
  b .L89
.L102:
  ldr x1, [sp, #24]
  add x0, x1, x4
  str x0, [sp, #24]
.L103:
  b .L87
.L104:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L105:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L106:
  fadd d6, d3, d7
.L107:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L108:
  fmul d5, d3, d7
.L109:
  mov x0, #1
  str x0, [sp, #24]
.L110:
  mov x0, #7
  mov x10, x0
.L111:
  mov x0, #101
  mov x9, x0
.L112:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L113:
  mov x0, #0
  fmov d11, x0
.L114:
  mov x0, #1
  mov x7, x0
.L115:
  mov x0, #101
  mov x6, x0
.L116:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L117:
  movz x0, #0
  movk x0, #16420, lsl #48
  fmov d4, x0
.L118:
  mov x0, #1
  mov x5, x0
.L119:
  mov x0, #1
  mov x4, x0
.L120:
  ldr x1, [sp, #24]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L138
.L121:
  mov x0, #1
  str x0, [sp, #16]
.L122:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L136
.L123:
  fsub d3, d12, d7
.L124:
  fmul d3, d3, d6
.L125:
  fadd d6, d3, d7
.L126:
  fsub d7, d11, d7
.L127:
  ldr x1, [sp, #24]
  sub x3, x1, x7
.L128:
  mul x3, x3, x6
.L129:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L130:
  fsub d3, d6, d5
.L131:
  fmul d3, d3, d10
.L132:
  fadd d3, d3, d4
.L133:
  mov x1, x3
  adrp x8, _arr_zm@PAGE
  add x8, x8, _arr_zm@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L134:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L135:
  b .L122
.L136:
  ldr x1, [sp, #24]
  add x0, x1, x4
  str x0, [sp, #24]
.L137:
  b .L120
.L138:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L139:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L140:
  fadd d6, d3, d7
.L141:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L142:
  fmul d5, d3, d7
.L143:
  mov x0, #1
  str x0, [sp, #24]
.L144:
  mov x0, #7
  mov x10, x0
.L145:
  mov x0, #101
  mov x9, x0
.L146:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L147:
  mov x0, #0
  fmov d10, x0
.L148:
  mov x0, #1
  mov x7, x0
.L149:
  mov x0, #101
  mov x6, x0
.L150:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L151:
  mov x0, #1
  mov x5, x0
.L152:
  mov x0, #1
  mov x4, x0
.L153:
  ldr x1, [sp, #24]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L170
.L154:
  mov x0, #1
  str x0, [sp, #16]
.L155:
  ldr x1, [sp, #16]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L168
.L156:
  fsub d3, d11, d7
.L157:
  fmul d3, d3, d6
.L158:
  fadd d6, d3, d7
.L159:
  fsub d7, d10, d7
.L160:
  ldr x1, [sp, #24]
  sub x3, x1, x7
.L161:
  mul x3, x3, x6
.L162:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L163:
  fsub d3, d6, d5
.L164:
  fmul d3, d3, d4
.L165:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L166:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L167:
  b .L155
.L168:
  ldr x1, [sp, #24]
  add x0, x1, x4
  str x0, [sp, #24]
.L169:
  b .L153
.L170:
  mov x0, #1
  str x0, [sp, #24]
.L171:
  mov x0, #7
  mov x19, x0
.L172:
  mov x0, #101
  mov x15, x0
.L173:
  mov x0, #1
  mov x14, x0
.L174:
  mov x0, #101
  mov x13, x0
.L175:
  mov x0, #0
  fmov d11, x0
.L176:
  mov x0, #1
  mov x12, x0
.L177:
  mov x0, #101
  mov x11, x0
.L178:
  mov x0, #0
  fmov d10, x0
.L179:
  mov x0, #1
  mov x10, x0
.L180:
  mov x0, #101
  mov x9, x0
.L181:
  mov x0, #0
  fmov d4, x0
.L182:
  mov x0, #1
  mov x7, x0
.L183:
  mov x0, #101
  mov x6, x0
.L184:
  mov x0, #0
  fmov d3, x0
.L185:
  mov x0, #1
  mov x5, x0
.L186:
  mov x0, #1
  mov x4, x0
.L187:
  ldr x1, [sp, #24]
  mov x2, x19
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L210
.L188:
  mov x0, #1
  str x0, [sp, #16]
.L189:
  ldr x1, [sp, #16]
  mov x2, x15
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L208
.L190:
  ldr x1, [sp, #24]
  sub x3, x1, x14
.L191:
  mul x3, x3, x13
.L192:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L193:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  str d11, [x8, x1, lsl #3]
.L194:
  ldr x1, [sp, #24]
  sub x3, x1, x12
.L195:
  mul x3, x3, x11
.L196:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L197:
  mov x1, x3
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  str d10, [x8, x1, lsl #3]
.L198:
  ldr x1, [sp, #24]
  sub x3, x1, x10
.L199:
  mul x3, x3, x9
.L200:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L201:
  mov x1, x3
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  str d4, [x8, x1, lsl #3]
.L202:
  ldr x1, [sp, #24]
  sub x3, x1, x7
.L203:
  mul x3, x3, x6
.L204:
  ldr x2, [sp, #16]
  add x3, x3, x2
.L205:
  mov x1, x3
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L206:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L207:
  b .L189
.L208:
  ldr x1, [sp, #24]
  add x0, x1, x4
  str x0, [sp, #24]
.L209:
  b .L187
.L210:
  mov x0, #1
  str x0, [sp, #8]
.L211:
  movz x0, #5744
  movk x0, #21, lsl #16
  str x0, [sp, #216]
.L212:
  mov x0, #6
  str x0, [sp, #224]
.L213:
  mov x0, #100
  str x0, [sp, #232]
.L214:
  mov x0, #1
  str x0, [sp, #240]
.L215:
  mov x0, #101
  str x0, [sp, #248]
.L216:
  mov x0, #1
  str x0, [sp, #256]
.L217:
  mov x0, #1
  str x0, [sp, #264]
.L218:
  mov x0, #101
  str x0, [sp, #272]
.L219:
  mov x0, #1
  str x0, [sp, #280]
.L220:
  mov x0, #1
  str x0, [sp, #288]
.L221:
  mov x0, #1
  str x0, [sp, #296]
.L222:
  mov x0, #101
  str x0, [sp, #304]
.L223:
  mov x0, #1
  str x0, [sp, #312]
.L224:
  mov x0, #1
  str x0, [sp, #320]
.L225:
  mov x0, #101
  str x0, [sp, #328]
.L226:
  mov x0, #1
  str x0, [sp, #336]
.L227:
  mov x0, #1
  str x0, [sp, #344]
.L228:
  mov x0, #101
  str x0, [sp, #352]
.L229:
  mov x0, #1
  str x0, [sp, #360]
.L230:
  mov x0, #1
  str x0, [sp, #368]
.L231:
  mov x0, #101
  str x0, [sp, #376]
.L232:
  mov x0, #1
  str x0, [sp, #384]
.L233:
  mov x0, #101
  str x0, [sp, #392]
.L234:
  mov x0, #1
  str x0, [sp, #400]
.L235:
  mov x0, #1
  str x0, [sp, #408]
.L236:
  mov x0, #101
  str x0, [sp, #416]
.L237:
  mov x0, #1
  str x0, [sp, #424]
.L238:
  mov x0, #1
  str x0, [sp, #432]
.L239:
  mov x0, #1
  str x0, [sp, #440]
.L240:
  mov x0, #101
  str x0, [sp, #448]
.L241:
  mov x0, #1
  str x0, [sp, #456]
.L242:
  mov x0, #1
  str x0, [sp, #464]
.L243:
  mov x0, #101
  str x0, [sp, #472]
.L244:
  mov x0, #1
  str x0, [sp, #480]
.L245:
  mov x0, #101
  str x0, [sp, #488]
.L246:
  mov x0, #1
  str x0, [sp, #496]
.L247:
  mov x0, #1
  str x0, [sp, #504]
.L248:
  mov x0, #101
  str x0, [sp, #512]
.L249:
  mov x0, #1
  str x0, [sp, #520]
.L250:
  mov x0, #1
  str x0, [sp, #528]
.L251:
  mov x0, #101
  str x0, [sp, #536]
.L252:
  mov x0, #1
  str x0, [sp, #544]
.L253:
  mov x0, #101
  str x0, [sp, #552]
.L254:
  mov x0, #1
  str x0, [sp, #560]
.L255:
  mov x0, #101
  str x0, [sp, #568]
.L256:
  mov x0, #1
  str x0, [sp, #576]
.L257:
  mov x0, #1
  str x0, [sp, #584]
.L258:
  mov x0, #101
  str x0, [sp, #592]
.L259:
  mov x0, #1
  str x0, [sp, #600]
.L260:
  mov x0, #101
  str x0, [sp, #608]
.L261:
  mov x0, #1
  str x0, [sp, #616]
.L262:
  mov x0, #101
  str x0, [sp, #624]
.L263:
  mov x0, #1
  str x0, [sp, #632]
.L264:
  mov x0, #1
  str x0, [sp, #640]
.L265:
  mov x0, #1
  str x0, [sp, #648]
.L266:
  mov x0, #6
  str x0, [sp, #656]
.L267:
  mov x0, #100
  str x0, [sp, #664]
.L268:
  mov x0, #1
  str x0, [sp, #672]
.L269:
  mov x0, #101
  str x0, [sp, #680]
.L270:
  mov x0, #1
  str x0, [sp, #688]
.L271:
  mov x0, #101
  str x0, [sp, #696]
.L272:
  mov x0, #1
  str x0, [sp, #704]
.L273:
  mov x0, #101
  str x0, [sp, #712]
.L274:
  mov x0, #1
  str x0, [sp, #720]
.L275:
  mov x0, #101
  str x0, [sp, #728]
.L276:
  mov x0, #1
  str x0, [sp, #736]
.L277:
  mov x0, #101
  str x0, [sp, #744]
.L278:
  mov x0, #1
  str x0, [sp, #752]
.L279:
  mov x0, #1
  str x0, [sp, #760]
.L280:
  mov x0, #101
  str x0, [sp, #768]
.L281:
  mov x0, #1
  str x0, [sp, #776]
.L282:
  mov x0, #1
  str x0, [sp, #784]
.L283:
  mov x0, #101
  str x0, [sp, #792]
.L284:
  mov x0, #1
  str x0, [sp, #800]
.L285:
  mov x0, #101
  str x0, [sp, #808]
.L286:
  mov x0, #1
  str x0, [sp, #816]
.L287:
  mov x0, #1
  str x0, [sp, #824]
.L288:
  mov x0, #101
  str x0, [sp, #832]
.L289:
  mov x0, #1
  str x0, [sp, #840]
.L290:
  mov x0, #101
  str x0, [sp, #848]
.L291:
  mov x0, #1
  str x0, [sp, #856]
.L292:
  mov x0, #1
  str x0, [sp, #864]
.L293:
  mov x0, #101
  str x0, [sp, #872]
.L294:
  mov x0, #1
  str x0, [sp, #880]
.L295:
  mov x0, #1
  str x0, [sp, #888]
.L296:
  mov x0, #101
  str x0, [sp, #896]
.L297:
  mov x0, #1
  str x0, [sp, #904]
.L298:
  mov x0, #101
  str x0, [sp, #912]
.L299:
  mov x0, #1
  str x0, [sp, #920]
.L300:
  mov x0, #1
  str x0, [sp, #928]
.L301:
  mov x0, #101
  str x0, [sp, #936]
.L302:
  mov x0, #1
  str x0, [sp, #944]
.L303:
  mov x0, #101
  str x0, [sp, #952]
.L304:
  mov x0, #1
  str x0, [sp, #960]
.L305:
  mov x0, #101
  str x0, [sp, #968]
.L306:
  mov x0, #1
  str x0, [sp, #976]
.L307:
  mov x0, #101
  str x0, [sp, #984]
.L308:
  mov x0, #1
  str x0, [sp, #992]
.L309:
  mov x0, #101
  str x0, [sp, #1000]
.L310:
  mov x0, #1
  str x0, [sp, #1008]
.L311:
  mov x0, #101
  str x0, [sp, #1016]
.L312:
  mov x0, #1
  str x0, [sp, #1024]
.L313:
  mov x0, #1
  str x0, [sp, #1032]
.L314:
  mov x0, #101
  str x0, [sp, #1040]
.L315:
  mov x0, #1
  str x0, [sp, #1048]
.L316:
  mov x0, #1
  str x0, [sp, #1056]
.L317:
  mov x0, #101
  str x0, [sp, #1064]
.L318:
  mov x0, #1
  str x0, [sp, #1072]
.L319:
  mov x0, #101
  str x0, [sp, #1080]
.L320:
  mov x0, #1
  str x0, [sp, #1088]
.L321:
  mov x0, #1
  str x0, [sp, #1096]
.L322:
  mov x0, #101
  str x0, [sp, #1104]
.L323:
  mov x0, #1
  str x0, [sp, #1112]
.L324:
  mov x0, #101
  str x0, [sp, #1120]
.L325:
  mov x0, #1
  str x0, [sp, #1128]
.L326:
  mov x0, #1
  str x0, [sp, #1136]
.L327:
  mov x0, #101
  str x0, [sp, #1144]
.L328:
  mov x0, #1
  str x0, [sp, #1152]
.L329:
  mov x0, #1
  str x0, [sp, #1160]
.L330:
  mov x0, #101
  str x0, [sp, #1168]
.L331:
  mov x0, #1
  str x0, [sp, #1176]
.L332:
  mov x0, #101
  str x0, [sp, #1184]
.L333:
  mov x0, #1
  str x0, [sp, #1192]
.L334:
  mov x0, #1
  str x0, [sp, #1200]
.L335:
  mov x0, #101
  mov x28, x0
.L336:
  mov x0, #1
  mov x27, x0
.L337:
  mov x0, #1
  mov x26, x0
.L338:
  mov x0, #6
  mov x25, x0
.L339:
  mov x0, #100
  mov x24, x0
.L340:
  mov x0, #1
  mov x23, x0
.L341:
  mov x0, #101
  mov x22, x0
.L342:
  mov x0, #1
  mov x21, x0
.L343:
  mov x0, #101
  mov x20, x0
.L344:
  mov x0, #1
  mov x19, x0
.L345:
  mov x0, #101
  mov x15, x0
.L346:
  mov x0, #1
  mov x14, x0
.L347:
  mov x0, #101
  mov x13, x0
.L348:
  mov x0, #1
  mov x12, x0
.L349:
  mov x0, #101
  mov x11, x0
.L350:
  mov x0, #1
  mov x10, x0
.L351:
  mov x0, #101
  mov x9, x0
.L352:
  mov x0, #1
  mov x7, x0
.L353:
  mov x0, #1
  mov x6, x0
.L354:
  mov x0, #1
  mov x5, x0
.L355:
  ldr x1, [sp, #8]
  ldr x2, [sp, #216]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L662
.L356:
  movz x0, #44460
  movk x0, #24536, lsl #16
  movk x0, #20342, lsl #32
  movk x0, #16238, lsl #48
  fmov d9, x0
.L357:
  movz x0, #6921
  movk x0, #24222, lsl #16
  movk x0, #52009, lsl #32
  movk x0, #16240, lsl #48
  fmov d8, x0
.L358:
  mov x0, #2
  str x0, [sp, #16]
.L359:
  ldr x1, [sp, #16]
  ldr x2, [sp, #224]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L466
.L360:
  mov x0, #2
  str x0, [sp, #24]
.L361:
  ldr x1, [sp, #24]
  ldr x2, [sp, #232]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L464
.L362:
  ldr x1, [sp, #16]
  ldr x2, [sp, #240]
  sub x3, x1, x2
.L363:
  ldr x2, [sp, #248]
  mul x3, x3, x2
.L364:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L365:
  ldr x1, [sp, #16]
  ldr x2, [sp, #256]
  add x3, x1, x2
.L366:
  ldr x2, [sp, #264]
  sub x3, x3, x2
.L367:
  ldr x2, [sp, #272]
  mul x3, x3, x2
.L368:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L369:
  ldr x2, [sp, #280]
  sub x3, x3, x2
.L370:
  mov x1, x3
  adrp x8, _arr_zp@PAGE
  add x8, x8, _arr_zp@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L371:
  ldr x1, [sp, #16]
  ldr x2, [sp, #288]
  add x3, x1, x2
.L372:
  ldr x2, [sp, #296]
  sub x3, x3, x2
.L373:
  ldr x2, [sp, #304]
  mul x3, x3, x2
.L374:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L375:
  ldr x2, [sp, #312]
  sub x3, x3, x2
.L376:
  mov x1, x3
  adrp x8, _arr_zq@PAGE
  add x8, x8, _arr_zq@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L377:
  fadd d4, d4, d3
.L378:
  ldr x1, [sp, #16]
  ldr x2, [sp, #320]
  sub x3, x1, x2
.L379:
  ldr x2, [sp, #328]
  mul x3, x3, x2
.L380:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L381:
  ldr x2, [sp, #336]
  sub x3, x3, x2
.L382:
  mov x1, x3
  adrp x8, _arr_zp@PAGE
  add x8, x8, _arr_zp@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L383:
  fsub d4, d4, d3
.L384:
  ldr x1, [sp, #16]
  ldr x2, [sp, #344]
  sub x3, x1, x2
.L385:
  ldr x2, [sp, #352]
  mul x3, x3, x2
.L386:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L387:
  ldr x2, [sp, #360]
  sub x3, x3, x2
.L388:
  mov x1, x3
  adrp x8, _arr_zq@PAGE
  add x8, x8, _arr_zq@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L389:
  fsub d10, d4, d3
.L390:
  ldr x1, [sp, #16]
  ldr x2, [sp, #368]
  sub x3, x1, x2
.L391:
  ldr x2, [sp, #376]
  mul x3, x3, x2
.L392:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L393:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L394:
  ldr x1, [sp, #16]
  ldr x2, [sp, #384]
  sub x3, x1, x2
.L395:
  ldr x2, [sp, #392]
  mul x3, x3, x2
.L396:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L397:
  ldr x2, [sp, #400]
  sub x3, x3, x2
.L398:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L399:
  fadd d3, d4, d3
.L400:
  fmul d10, d10, d3
.L401:
  ldr x1, [sp, #16]
  ldr x2, [sp, #408]
  sub x3, x1, x2
.L402:
  ldr x2, [sp, #416]
  mul x3, x3, x2
.L403:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L404:
  ldr x2, [sp, #424]
  sub x3, x3, x2
.L405:
  mov x1, x3
  adrp x8, _arr_zm@PAGE
  add x8, x8, _arr_zm@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L406:
  ldr x1, [sp, #16]
  ldr x2, [sp, #432]
  add x3, x1, x2
.L407:
  ldr x2, [sp, #440]
  sub x3, x3, x2
.L408:
  ldr x2, [sp, #448]
  mul x3, x3, x2
.L409:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L410:
  ldr x2, [sp, #456]
  sub x3, x3, x2
.L411:
  mov x1, x3
  adrp x8, _arr_zm@PAGE
  add x8, x8, _arr_zm@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L412:
  fadd d3, d4, d3
.L413:
  fdiv d3, d10, d3
.L414:
  mov x1, x4
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L415:
  ldr x1, [sp, #16]
  ldr x2, [sp, #464]
  sub x3, x1, x2
.L416:
  ldr x2, [sp, #472]
  mul x3, x3, x2
.L417:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L418:
  ldr x1, [sp, #16]
  ldr x2, [sp, #480]
  sub x3, x1, x2
.L419:
  ldr x2, [sp, #488]
  mul x3, x3, x2
.L420:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L421:
  ldr x2, [sp, #496]
  sub x3, x3, x2
.L422:
  mov x1, x3
  adrp x8, _arr_zp@PAGE
  add x8, x8, _arr_zp@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L423:
  ldr x1, [sp, #16]
  ldr x2, [sp, #504]
  sub x3, x1, x2
.L424:
  ldr x2, [sp, #512]
  mul x3, x3, x2
.L425:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L426:
  ldr x2, [sp, #520]
  sub x3, x3, x2
.L427:
  mov x1, x3
  adrp x8, _arr_zq@PAGE
  add x8, x8, _arr_zq@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L428:
  fadd d4, d4, d3
.L429:
  ldr x1, [sp, #16]
  ldr x2, [sp, #528]
  sub x3, x1, x2
.L430:
  ldr x2, [sp, #536]
  mul x3, x3, x2
.L431:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L432:
  mov x1, x3
  adrp x8, _arr_zp@PAGE
  add x8, x8, _arr_zp@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L433:
  fsub d4, d4, d3
.L434:
  ldr x1, [sp, #16]
  ldr x2, [sp, #544]
  sub x3, x1, x2
.L435:
  ldr x2, [sp, #552]
  mul x3, x3, x2
.L436:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L437:
  mov x1, x3
  adrp x8, _arr_zq@PAGE
  add x8, x8, _arr_zq@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L438:
  fsub d10, d4, d3
.L439:
  ldr x1, [sp, #16]
  ldr x2, [sp, #560]
  sub x3, x1, x2
.L440:
  ldr x2, [sp, #568]
  mul x3, x3, x2
.L441:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L442:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L443:
  ldr x1, [sp, #16]
  ldr x2, [sp, #576]
  sub x3, x1, x2
.L444:
  ldr x2, [sp, #584]
  sub x3, x3, x2
.L445:
  ldr x2, [sp, #592]
  mul x3, x3, x2
.L446:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L447:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L448:
  fadd d3, d4, d3
.L449:
  fmul d10, d10, d3
.L450:
  ldr x1, [sp, #16]
  ldr x2, [sp, #600]
  sub x3, x1, x2
.L451:
  ldr x2, [sp, #608]
  mul x3, x3, x2
.L452:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L453:
  mov x1, x3
  adrp x8, _arr_zm@PAGE
  add x8, x8, _arr_zm@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L454:
  ldr x1, [sp, #16]
  ldr x2, [sp, #616]
  sub x3, x1, x2
.L455:
  ldr x2, [sp, #624]
  mul x3, x3, x2
.L456:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L457:
  ldr x2, [sp, #632]
  sub x3, x3, x2
.L458:
  mov x1, x3
  adrp x8, _arr_zm@PAGE
  add x8, x8, _arr_zm@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L459:
  fadd d3, d4, d3
.L460:
  fdiv d3, d10, d3
.L461:
  mov x1, x4
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L462:
  ldr x1, [sp, #24]
  ldr x2, [sp, #640]
  add x0, x1, x2
  str x0, [sp, #24]
.L463:
  b .L361
.L464:
  ldr x1, [sp, #16]
  ldr x2, [sp, #648]
  add x0, x1, x2
  str x0, [sp, #16]
.L465:
  b .L359
.L466:
  mov x0, #2
  str x0, [sp, #16]
.L467:
  ldr x1, [sp, #16]
  ldr x2, [sp, #656]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L624
.L468:
  mov x0, #2
  str x0, [sp, #24]
.L469:
  ldr x1, [sp, #24]
  ldr x2, [sp, #664]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L622
.L470:
  ldr x1, [sp, #16]
  ldr x2, [sp, #672]
  sub x3, x1, x2
.L471:
  ldr x2, [sp, #680]
  mul x3, x3, x2
.L472:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L473:
  ldr x1, [sp, #16]
  ldr x2, [sp, #688]
  sub x3, x1, x2
.L474:
  ldr x2, [sp, #696]
  mul x3, x3, x2
.L475:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L476:
  mov x1, x3
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  ldr d11, [x8, x1, lsl #3]
.L477:
  ldr x1, [sp, #16]
  ldr x2, [sp, #704]
  sub x3, x1, x2
.L478:
  ldr x2, [sp, #712]
  mul x3, x3, x2
.L479:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L480:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L481:
  ldr x1, [sp, #16]
  ldr x2, [sp, #720]
  sub x3, x1, x2
.L482:
  ldr x2, [sp, #728]
  mul x3, x3, x2
.L483:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L484:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L485:
  ldr x1, [sp, #16]
  ldr x2, [sp, #736]
  sub x3, x1, x2
.L486:
  ldr x2, [sp, #744]
  mul x3, x3, x2
.L487:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L488:
  ldr x2, [sp, #752]
  add x3, x3, x2
.L489:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L490:
  fsub d3, d4, d3
.L491:
  fmul d12, d10, d3
.L492:
  ldr x1, [sp, #16]
  ldr x2, [sp, #760]
  sub x3, x1, x2
.L493:
  ldr x2, [sp, #768]
  mul x3, x3, x2
.L494:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L495:
  ldr x2, [sp, #776]
  sub x3, x3, x2
.L496:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L497:
  ldr x1, [sp, #16]
  ldr x2, [sp, #784]
  sub x3, x1, x2
.L498:
  ldr x2, [sp, #792]
  mul x3, x3, x2
.L499:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L500:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L501:
  ldr x1, [sp, #16]
  ldr x2, [sp, #800]
  sub x3, x1, x2
.L502:
  ldr x2, [sp, #808]
  mul x3, x3, x2
.L503:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L504:
  ldr x2, [sp, #816]
  sub x3, x3, x2
.L505:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L506:
  fsub d3, d4, d3
.L507:
  fmul d3, d10, d3
.L508:
  fsub d12, d12, d3
.L509:
  ldr x1, [sp, #16]
  ldr x2, [sp, #824]
  sub x3, x1, x2
.L510:
  ldr x2, [sp, #832]
  mul x3, x3, x2
.L511:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L512:
  mov x1, x3
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L513:
  ldr x1, [sp, #16]
  ldr x2, [sp, #840]
  sub x3, x1, x2
.L514:
  ldr x2, [sp, #848]
  mul x3, x3, x2
.L515:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L516:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L517:
  ldr x1, [sp, #16]
  ldr x2, [sp, #856]
  sub x3, x1, x2
.L518:
  ldr x2, [sp, #864]
  sub x3, x3, x2
.L519:
  ldr x2, [sp, #872]
  mul x3, x3, x2
.L520:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L521:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L522:
  fsub d3, d4, d3
.L523:
  fmul d3, d10, d3
.L524:
  fsub d12, d12, d3
.L525:
  ldr x1, [sp, #16]
  ldr x2, [sp, #880]
  add x3, x1, x2
.L526:
  ldr x2, [sp, #888]
  sub x3, x3, x2
.L527:
  ldr x2, [sp, #896]
  mul x3, x3, x2
.L528:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L529:
  mov x1, x3
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L530:
  ldr x1, [sp, #16]
  ldr x2, [sp, #904]
  sub x3, x1, x2
.L531:
  ldr x2, [sp, #912]
  mul x3, x3, x2
.L532:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L533:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L534:
  ldr x1, [sp, #16]
  ldr x2, [sp, #920]
  add x3, x1, x2
.L535:
  ldr x2, [sp, #928]
  sub x3, x3, x2
.L536:
  ldr x2, [sp, #936]
  mul x3, x3, x2
.L537:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L538:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L539:
  fsub d3, d4, d3
.L540:
  fmul d3, d10, d3
.L541:
  fadd d3, d12, d3
.L542:
  fmul d3, d8, d3
.L543:
  fadd d3, d11, d3
.L544:
  mov x1, x4
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L545:
  ldr x1, [sp, #16]
  ldr x2, [sp, #944]
  sub x3, x1, x2
.L546:
  ldr x2, [sp, #952]
  mul x3, x3, x2
.L547:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L548:
  ldr x1, [sp, #16]
  ldr x2, [sp, #960]
  sub x3, x1, x2
.L549:
  ldr x2, [sp, #968]
  mul x3, x3, x2
.L550:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L551:
  mov x1, x3
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  ldr d11, [x8, x1, lsl #3]
.L552:
  ldr x1, [sp, #16]
  ldr x2, [sp, #976]
  sub x3, x1, x2
.L553:
  ldr x2, [sp, #984]
  mul x3, x3, x2
.L554:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L555:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L556:
  ldr x1, [sp, #16]
  ldr x2, [sp, #992]
  sub x3, x1, x2
.L557:
  ldr x2, [sp, #1000]
  mul x3, x3, x2
.L558:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L559:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L560:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1008]
  sub x3, x1, x2
.L561:
  ldr x2, [sp, #1016]
  mul x3, x3, x2
.L562:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L563:
  ldr x2, [sp, #1024]
  add x3, x3, x2
.L564:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L565:
  fsub d3, d4, d3
.L566:
  fmul d12, d10, d3
.L567:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1032]
  sub x3, x1, x2
.L568:
  ldr x2, [sp, #1040]
  mul x3, x3, x2
.L569:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L570:
  ldr x2, [sp, #1048]
  sub x3, x3, x2
.L571:
  mov x1, x3
  adrp x8, _arr_za@PAGE
  add x8, x8, _arr_za@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L572:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1056]
  sub x3, x1, x2
.L573:
  ldr x2, [sp, #1064]
  mul x3, x3, x2
.L574:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L575:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L576:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1072]
  sub x3, x1, x2
.L577:
  ldr x2, [sp, #1080]
  mul x3, x3, x2
.L578:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L579:
  ldr x2, [sp, #1088]
  sub x3, x3, x2
.L580:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L581:
  fsub d3, d4, d3
.L582:
  fmul d3, d10, d3
.L583:
  fsub d12, d12, d3
.L584:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1096]
  sub x3, x1, x2
.L585:
  ldr x2, [sp, #1104]
  mul x3, x3, x2
.L586:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L587:
  mov x1, x3
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L588:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1112]
  sub x3, x1, x2
.L589:
  ldr x2, [sp, #1120]
  mul x3, x3, x2
.L590:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L591:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L592:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1128]
  sub x3, x1, x2
.L593:
  ldr x2, [sp, #1136]
  sub x3, x3, x2
.L594:
  ldr x2, [sp, #1144]
  mul x3, x3, x2
.L595:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L596:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L597:
  fsub d3, d4, d3
.L598:
  fmul d3, d10, d3
.L599:
  fsub d12, d12, d3
.L600:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1152]
  add x3, x1, x2
.L601:
  ldr x2, [sp, #1160]
  sub x3, x3, x2
.L602:
  ldr x2, [sp, #1168]
  mul x3, x3, x2
.L603:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L604:
  mov x1, x3
  adrp x8, _arr_zb@PAGE
  add x8, x8, _arr_zb@PAGEOFF
  ldr d10, [x8, x1, lsl #3]
.L605:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1176]
  sub x3, x1, x2
.L606:
  ldr x2, [sp, #1184]
  mul x3, x3, x2
.L607:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L608:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L609:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1192]
  add x3, x1, x2
.L610:
  ldr x2, [sp, #1200]
  sub x3, x3, x2
.L611:
  mul x3, x3, x28
.L612:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L613:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L614:
  fsub d3, d4, d3
.L615:
  fmul d3, d10, d3
.L616:
  fadd d3, d12, d3
.L617:
  fmul d3, d8, d3
.L618:
  fadd d3, d11, d3
.L619:
  mov x1, x4
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L620:
  ldr x1, [sp, #24]
  add x0, x1, x27
  str x0, [sp, #24]
.L621:
  b .L469
.L622:
  ldr x1, [sp, #16]
  add x0, x1, x26
  str x0, [sp, #16]
.L623:
  b .L467
.L624:
  mov x0, #2
  str x0, [sp, #16]
.L625:
  ldr x1, [sp, #16]
  mov x2, x25
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L660
.L626:
  mov x0, #2
  str x0, [sp, #24]
.L627:
  ldr x1, [sp, #24]
  mov x2, x24
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L658
.L628:
  ldr x1, [sp, #16]
  sub x3, x1, x23
.L629:
  mul x3, x3, x22
.L630:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L631:
  ldr x1, [sp, #16]
  sub x3, x1, x21
.L632:
  mul x3, x3, x20
.L633:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L634:
  mov x1, x3
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L635:
  ldr x1, [sp, #16]
  sub x3, x1, x19
.L636:
  mul x3, x3, x15
.L637:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L638:
  mov x1, x3
  adrp x8, _arr_zu@PAGE
  add x8, x8, _arr_zu@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L639:
  fmul d3, d9, d3
.L640:
  fadd d3, d4, d3
.L641:
  mov x1, x4
  adrp x8, _arr_zr@PAGE
  add x8, x8, _arr_zr@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L642:
  ldr x1, [sp, #16]
  sub x3, x1, x14
.L643:
  mul x3, x3, x13
.L644:
  ldr x2, [sp, #24]
  add x4, x3, x2
.L645:
  ldr x1, [sp, #16]
  sub x3, x1, x12
.L646:
  mul x3, x3, x11
.L647:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L648:
  mov x1, x3
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L649:
  ldr x1, [sp, #16]
  sub x3, x1, x10
.L650:
  mul x3, x3, x9
.L651:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L652:
  mov x1, x3
  adrp x8, _arr_zv@PAGE
  add x8, x8, _arr_zv@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L653:
  fmul d3, d9, d3
.L654:
  fadd d3, d4, d3
.L655:
  mov x1, x4
  adrp x8, _arr_zz@PAGE
  add x8, x8, _arr_zz@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L656:
  ldr x1, [sp, #24]
  add x0, x1, x7
  str x0, [sp, #24]
.L657:
  b .L627
.L658:
  ldr x1, [sp, #16]
  add x0, x1, x6
  str x0, [sp, #16]
.L659:
  b .L625
.L660:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L661:
  b .L355
.L662:
  str d9, [sp, #1280]
.L663:
  str d8, [sp, #1288]
.L664:
  str d7, [sp, #1296]
.L665:
  str d6, [sp, #1304]
.L666:
  str d5, [sp, #1312]
.L667:
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
  // print j
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_j@PAGE
  add x8, x8, .Lname_j@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print t (float)
  ldr d0, [sp, #1280]
  sub sp, sp, #32
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print s (float)
  ldr d0, [sp, #1288]
  sub sp, sp, #32
  adrp x8, .Lname_s@PAGE
  add x8, x8, .Lname_s@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #1296]
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
  ldr d0, [sp, #1304]
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
  ldr d0, [sp, #1312]
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
  ldr x19, [sp, #1320]
  ldr x28, [sp, #1328]
  ldr x27, [sp, #1336]
  ldr x26, [sp, #1344]
  ldr x25, [sp, #1352]
  ldr x24, [sp, #1360]
  ldr x23, [sp, #1368]
  ldr x22, [sp, #1376]
  ldr x21, [sp, #1384]
  ldr x20, [sp, #1392]
  ldr d9, [sp, #1400]
  ldr d8, [sp, #1408]
  ldr d11, [sp, #1416]
  ldr d10, [sp, #1424]
  ldr d12, [sp, #1432]
  ldr x29, [sp, #1456]
  ldr x30, [sp, #1464]
  add sp, sp, #1472
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
.Lname_k:
  .asciz "k"
.Lname_j:
  .asciz "j"
.Lname_t:
  .asciz "t"
.Lname_s:
  .asciz "s"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_zp
.align 3
_arr_zp:
  .space 5664
.global _arr_zq
.align 3
_arr_zq:
  .space 5664
.global _arr_zr
.align 3
_arr_zr:
  .space 5664
.global _arr_zm
.align 3
_arr_zm:
  .space 5664
.global _arr_zz
.align 3
_arr_zz:
  .space 5664
.global _arr_za
.align 3
_arr_za:
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
