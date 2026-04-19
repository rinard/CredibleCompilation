.global _main
.align 2

_main:
  sub sp, sp, #1456
  str x30, [sp, #1448]
  str x29, [sp, #1440]
  add x29, sp, #1440
  // Save callee-saved registers
  str x28, [sp, #1328]
  str x27, [sp, #1336]
  str x26, [sp, #1344]
  str x25, [sp, #1352]
  str x24, [sp, #1360]
  str x23, [sp, #1368]
  str x22, [sp, #1376]
  str x21, [sp, #1384]
  str x20, [sp, #1392]
  str x19, [sp, #1400]
  str d10, [sp, #1408]
  str d9, [sp, #1416]
  str d8, [sp, #1424]
  str d11, [sp, #1432]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  str x0, [sp, #40]
  str x0, [sp, #48]
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]
  mov x9, #0
  mov x8, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  mov x4, #0
  mov x3, #0
  fmov d3, x0
  fmov d11, x0
  fmov d5, x0
  fmov d4, x0
  str x0, [sp, #208]
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
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  str x0, [sp, #776]
  str x0, [sp, #784]
  str x0, [sp, #792]
  str x0, [sp, #800]
  str x0, [sp, #808]
  str x0, [sp, #816]
  mov x24, #0
  str x0, [sp, #832]
  str x0, [sp, #840]
  str x0, [sp, #848]
  str x0, [sp, #856]
  str x0, [sp, #864]
  str x0, [sp, #872]
  mov x23, #0
  mov x22, #0
  mov x21, #0
  mov x20, #0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  str x0, [sp, #936]
  mov x13, #0
  mov x12, #0
  str x0, [sp, #960]
  mov x11, #0
  mov x10, #0
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
  str x0, [sp, #1208]
  str x0, [sp, #1216]
  str x0, [sp, #1224]
  str x0, [sp, #1232]
  str x0, [sp, #1240]
  str x0, [sp, #1248]
  str x0, [sp, #1256]
  str x0, [sp, #1264]
  str x0, [sp, #1272]
  str x0, [sp, #1280]
  str x0, [sp, #1288]
  str x0, [sp, #1296]
  str x0, [sp, #1304]
  str x0, [sp, #1312]
  str x0, [sp, #1320]

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
  str x0, [sp, #40]
.L5:
  mov x0, #0
  str x0, [sp, #48]
.L6:
  mov x0, #0
  fmov d10, x0
.L7:
  mov x0, #0
  fmov d9, x0
.L8:
  mov x0, #0
  fmov d8, x0
.L9:
  mov x0, #0
  fmov d7, x0
.L10:
  mov x0, #0
  fmov d6, x0
.L11:
  mov x0, #0
  str x0, [sp, #96]
.L12:
  mov x0, #0
  str x0, [sp, #104]
.L13:
  mov x0, #0
  str x0, [sp, #112]
.L14:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L15:
  movz x0, #0
  movk x0, #16352, lsl #48
  fmov d9, x0
.L16:
  mov x0, #1
  str x0, [sp, #104]
.L17:
  mov x0, #4
  mov x9, x0
.L18:
  mov x0, #64
  mov x8, x0
.L19:
  mov x0, #1
  mov x7, x0
.L20:
  mov x0, #64
  mov x6, x0
.L21:
  mov x0, #1
  mov x5, x0
.L22:
  mov x0, #1
  mov x4, x0
.L23:
  ldr x1, [sp, #104]
  cmp x1, x9
  b.gt .L35
.L24:
  mov x0, #1
  str x0, [sp, #112]
.L25:
  ldr x1, [sp, #112]
  cmp x1, x8
  b.gt .L33
.L26:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L27:
  mul x3, x3, x6
.L28:
  ldr x2, [sp, #112]
  add x3, x3, x2
.L29:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d10, [x0, x3, lsl #3]
.L30:
  fadd d10, d10, d9
.L31:
  ldr x1, [sp, #112]
  add x0, x1, x5
  str x0, [sp, #112]
.L32:
  b .L25
.L33:
  ldr x1, [sp, #104]
  add x0, x1, x4
  str x0, [sp, #104]
.L34:
  b .L23
.L35:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L36:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L37:
  fadd d7, d3, d8
.L38:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L39:
  fmul d6, d3, d8
.L40:
  mov x0, #1
  str x0, [sp, #104]
.L41:
  mov x0, #64
  mov x9, x0
.L42:
  mov x0, #64
  mov x8, x0
.L43:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L44:
  mov x0, #0
  fmov d5, x0
.L45:
  mov x0, #1
  mov x7, x0
.L46:
  mov x0, #64
  mov x6, x0
.L47:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L48:
  mov x0, #1
  mov x5, x0
.L49:
  mov x0, #1
  mov x4, x0
.L50:
  ldr x1, [sp, #104]
  cmp x1, x9
  b.gt .L66
.L51:
  mov x0, #1
  str x0, [sp, #96]
.L52:
  ldr x1, [sp, #96]
  cmp x1, x8
  b.gt .L64
.L53:
  fsub d3, d11, d8
.L54:
  fmadd d7, d3, d7, d8
.L55:
  fsub d8, d5, d8
.L56:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L57:
  mul x3, x3, x6
.L58:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L59:
  fsub d3, d7, d6
.L60:
  fmul d3, d3, d4
.L61:
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  str d3, [x0, x3, lsl #3]
.L62:
  ldr x1, [sp, #96]
  add x0, x1, x5
  str x0, [sp, #96]
.L63:
  b .L52
.L64:
  ldr x1, [sp, #104]
  add x0, x1, x4
  str x0, [sp, #104]
.L65:
  b .L50
.L66:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L67:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L68:
  fadd d7, d3, d8
.L69:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L70:
  fmul d6, d3, d8
.L71:
  mov x0, #1
  str x0, [sp, #104]
.L72:
  mov x0, #64
  mov x9, x0
.L73:
  mov x0, #64
  mov x8, x0
.L74:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L75:
  mov x0, #0
  fmov d5, x0
.L76:
  mov x0, #1
  mov x7, x0
.L77:
  mov x0, #64
  mov x6, x0
.L78:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L79:
  mov x0, #1
  mov x5, x0
.L80:
  mov x0, #1
  mov x4, x0
.L81:
  ldr x1, [sp, #104]
  cmp x1, x9
  b.gt .L97
.L82:
  mov x0, #1
  str x0, [sp, #96]
.L83:
  ldr x1, [sp, #96]
  cmp x1, x8
  b.gt .L95
.L84:
  fsub d3, d11, d8
.L85:
  fmadd d7, d3, d7, d8
.L86:
  fsub d8, d5, d8
.L87:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L88:
  mul x3, x3, x6
.L89:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L90:
  fsub d3, d7, d6
.L91:
  fmul d3, d3, d4
.L92:
  adrp x0, _arr_c@PAGE
  add x0, x0, _arr_c@PAGEOFF
  str d3, [x0, x3, lsl #3]
.L93:
  ldr x1, [sp, #96]
  add x0, x1, x5
  str x0, [sp, #96]
.L94:
  b .L83
.L95:
  ldr x1, [sp, #104]
  add x0, x1, x4
  str x0, [sp, #104]
.L96:
  b .L81
.L97:
  mov x0, #1
  str x0, [sp, #104]
.L98:
  mov x0, #64
  mov x9, x0
.L99:
  mov x0, #64
  mov x8, x0
.L100:
  mov x0, #1
  mov x7, x0
.L101:
  mov x0, #64
  mov x6, x0
.L102:
  mov x0, #0
  fmov d3, x0
.L103:
  mov x0, #1
  mov x5, x0
.L104:
  mov x0, #1
  mov x4, x0
.L105:
  ldr x1, [sp, #104]
  cmp x1, x9
  b.gt .L116
.L106:
  mov x0, #1
  str x0, [sp, #96]
.L107:
  ldr x1, [sp, #96]
  cmp x1, x8
  b.gt .L114
.L108:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L109:
  mul x3, x3, x6
.L110:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L111:
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  str d3, [x0, x3, lsl #3]
.L112:
  ldr x1, [sp, #96]
  add x0, x1, x5
  str x0, [sp, #96]
.L113:
  b .L107
.L114:
  ldr x1, [sp, #104]
  add x0, x1, x4
  str x0, [sp, #104]
.L115:
  b .L105
.L116:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L117:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L118:
  fadd d7, d3, d8
.L119:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L120:
  fmul d6, d3, d8
.L121:
  mov x0, #1
  str x0, [sp, #112]
.L122:
  mov x0, #1001
  mov x4, x0
.L123:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L124:
  mov x0, #0
  fmov d5, x0
.L125:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L126:
  mov x0, #1
  mov x3, x0
.L127:
  ldr x1, [sp, #112]
  cmp x1, x4
  b.gt .L136
.L128:
  fsub d3, d11, d8
.L129:
  fmadd d7, d3, d7, d8
.L130:
  fsub d8, d5, d8
.L131:
  fsub d3, d7, d6
.L132:
  fmul d3, d3, d4
.L133:
  ldr x1, [sp, #112]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d3, [x0, x1, lsl #3]
.L134:
  ldr x1, [sp, #112]
  add x0, x1, x3
  str x0, [sp, #112]
.L135:
  b .L127
.L136:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L137:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L138:
  fadd d7, d3, d8
.L139:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L140:
  fmul d6, d3, d8
.L141:
  mov x0, #1
  str x0, [sp, #112]
.L142:
  mov x0, #1001
  mov x4, x0
.L143:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L144:
  mov x0, #0
  fmov d5, x0
.L145:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L146:
  mov x0, #1
  mov x3, x0
.L147:
  ldr x1, [sp, #112]
  cmp x1, x4
  b.gt .L156
.L148:
  fsub d3, d11, d8
.L149:
  fmadd d7, d3, d7, d8
.L150:
  fsub d8, d5, d8
.L151:
  fsub d3, d7, d6
.L152:
  fmul d3, d3, d4
.L153:
  ldr x1, [sp, #112]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d3, [x0, x1, lsl #3]
.L154:
  ldr x1, [sp, #112]
  add x0, x1, x3
  str x0, [sp, #112]
.L155:
  b .L147
.L156:
  mov x0, #1
  str x0, [sp, #96]
.L157:
  mov x0, #96
  mov x9, x0
.L158:
  mov x0, #1
  mov x8, x0
.L159:
  mov x0, #64
  mov x7, x0
.L160:
  mov x0, #1
  str x0, [sp, #208]
.L161:
  mov x0, #64
  mov x6, x0
.L162:
  mov x0, #1
  mov x5, x0
.L163:
  ldr x1, [sp, #96]
  cmp x1, x9
  b.gt .L172
.L164:
  ldr x1, [sp, #96]
  sub x4, x1, x8
.L165:
  cbz x7, .Ldiv_by_zero
  sdiv x0, x4, x7
  mul x0, x0, x7
  sub x3, x4, x0
.L166:
  ldr x1, [sp, #96]
  adrp x0, _arr_e@PAGE
  add x0, x0, _arr_e@PAGEOFF
  str x3, [x0, x1, lsl #3]
.L167:
  mov x0, x4
  mov x3, x0
.L168:
  cbz x6, .Ldiv_by_zero
  sdiv x0, x3, x6
  mul x0, x0, x6
  sub x3, x3, x0
.L169:
  ldr x1, [sp, #96]
  adrp x0, _arr_f@PAGE
  add x0, x0, _arr_f@PAGEOFF
  str x3, [x0, x1, lsl #3]
.L170:
  ldr x1, [sp, #96]
  add x0, x1, x5
  str x0, [sp, #96]
.L171:
  b .L163
.L172:
  mov x0, #1
  str x0, [sp, #16]
.L173:
  movz x0, #14096
  movk x0, #39, lsl #16
  str x0, [sp, #216]
.L174:
  mov x0, #4
  str x0, [sp, #224]
.L175:
  mov x0, #64
  str x0, [sp, #232]
.L176:
  mov x0, #1
  str x0, [sp, #240]
.L177:
  mov x0, #64
  str x0, [sp, #248]
.L178:
  mov x0, #1
  str x0, [sp, #256]
.L179:
  mov x0, #1
  str x0, [sp, #264]
.L180:
  mov x0, #64
  str x0, [sp, #272]
.L181:
  mov x0, #64
  str x0, [sp, #280]
.L182:
  mov x0, #1
  str x0, [sp, #288]
.L183:
  mov x0, #64
  str x0, [sp, #296]
.L184:
  mov x0, #0
  fmov d11, x0
.L185:
  mov x0, #1
  str x0, [sp, #304]
.L186:
  mov x0, #1
  str x0, [sp, #312]
.L187:
  mov x0, #64
  str x0, [sp, #320]
.L188:
  mov x0, #1
  str x0, [sp, #328]
.L189:
  mov x0, #1
  str x0, [sp, #336]
.L190:
  mov x0, #64
  str x0, [sp, #344]
.L191:
  mov x0, #2
  str x0, [sp, #352]
.L192:
  mov x0, #1
  str x0, [sp, #360]
.L193:
  mov x0, #64
  str x0, [sp, #368]
.L194:
  mov x0, #63
  str x0, [sp, #376]
.L195:
  mov x0, #63
  str x0, [sp, #384]
.L196:
  mov x0, #3
  str x0, [sp, #392]
.L197:
  mov x0, #1
  str x0, [sp, #400]
.L198:
  mov x0, #64
  str x0, [sp, #408]
.L199:
  mov x0, #3
  str x0, [sp, #416]
.L200:
  mov x0, #1
  str x0, [sp, #424]
.L201:
  mov x0, #64
  str x0, [sp, #432]
.L202:
  mov x0, #1
  str x0, [sp, #440]
.L203:
  mov x0, #1
  str x0, [sp, #448]
.L204:
  mov x0, #64
  str x0, [sp, #456]
.L205:
  mov x0, #1
  str x0, [sp, #464]
.L206:
  mov x0, #4
  str x0, [sp, #472]
.L207:
  mov x0, #1
  str x0, [sp, #480]
.L208:
  mov x0, #64
  str x0, [sp, #488]
.L209:
  mov x0, #4
  str x0, [sp, #496]
.L210:
  mov x0, #1
  str x0, [sp, #504]
.L211:
  mov x0, #64
  str x0, [sp, #512]
.L212:
  mov x0, #1
  str x0, [sp, #520]
.L213:
  mov x0, #1
  str x0, [sp, #528]
.L214:
  mov x0, #64
  str x0, [sp, #536]
.L215:
  mov x0, #1
  str x0, [sp, #544]
.L216:
  mov x0, #1
  str x0, [sp, #552]
.L217:
  mov x0, #1
  str x0, [sp, #560]
.L218:
  mov x0, #64
  str x0, [sp, #568]
.L219:
  mov x0, #1
  str x0, [sp, #576]
.L220:
  mov x0, #1
  str x0, [sp, #584]
.L221:
  mov x0, #64
  str x0, [sp, #592]
.L222:
  mov x0, #3
  str x0, [sp, #600]
.L223:
  mov x0, #1
  str x0, [sp, #608]
.L224:
  mov x0, #64
  str x0, [sp, #616]
.L225:
  mov x0, #2
  str x0, [sp, #624]
.L226:
  mov x0, #1
  str x0, [sp, #632]
.L227:
  mov x0, #64
  str x0, [sp, #640]
.L228:
  mov x0, #2
  str x0, [sp, #648]
.L229:
  mov x0, #1
  str x0, [sp, #656]
.L230:
  mov x0, #64
  str x0, [sp, #664]
.L231:
  mov x0, #4
  str x0, [sp, #672]
.L232:
  mov x0, #1
  str x0, [sp, #680]
.L233:
  mov x0, #64
  str x0, [sp, #688]
.L234:
  mov x0, #1
  str x0, [sp, #696]
.L235:
  mov x0, #1
  str x0, [sp, #704]
.L236:
  mov x0, #64
  str x0, [sp, #712]
.L237:
  mov x0, #2
  str x0, [sp, #720]
.L238:
  mov x0, #1
  str x0, [sp, #728]
.L239:
  mov x0, #64
  str x0, [sp, #736]
.L240:
  mov x0, #63
  mov x28, x0
.L241:
  mov x0, #1
  mov x27, x0
.L242:
  mov x0, #63
  mov x26, x0
.L243:
  mov x0, #1
  mov x25, x0
.L244:
  mov x0, #1
  str x0, [sp, #776]
.L245:
  mov x0, #1
  str x0, [sp, #784]
.L246:
  mov x0, #64
  str x0, [sp, #792]
.L247:
  mov x0, #1
  str x0, [sp, #800]
.L248:
  mov x0, #1
  str x0, [sp, #808]
.L249:
  mov x0, #64
  str x0, [sp, #816]
.L250:
  mov x0, #32
  mov x24, x0
.L251:
  mov x0, #2
  str x0, [sp, #832]
.L252:
  mov x0, #1
  str x0, [sp, #840]
.L253:
  mov x0, #64
  str x0, [sp, #848]
.L254:
  mov x0, #2
  str x0, [sp, #856]
.L255:
  mov x0, #1
  str x0, [sp, #864]
.L256:
  mov x0, #64
  str x0, [sp, #872]
.L257:
  mov x0, #32
  mov x23, x0
.L258:
  mov x0, #32
  mov x22, x0
.L259:
  mov x0, #32
  mov x21, x0
.L260:
  mov x0, #1
  mov x20, x0
.L261:
  mov x0, #1
  mov x19, x0
.L262:
  mov x0, #64
  mov x15, x0
.L263:
  mov x0, #1
  mov x14, x0
.L264:
  mov x0, #1
  str x0, [sp, #936]
.L265:
  mov x0, #1
  mov x13, x0
.L266:
  mov x0, #64
  mov x12, x0
.L267:
  mov x0, #1
  str x0, [sp, #960]
.L268:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d5, x0
.L269:
  mov x0, #1
  mov x11, x0
.L270:
  mov x0, #1
  mov x10, x0
.L271:
  ldr x1, [sp, #16]
  ldr x2, [sp, #216]
  cmp x1, x2
  b.gt .L431
.L272:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L273:
  mov x0, #1
  str x0, [sp, #104]
.L274:
  ldr x1, [sp, #104]
  ldr x2, [sp, #224]
  cmp x1, x2
  b.gt .L286
.L275:
  mov x0, #1
  str x0, [sp, #112]
.L276:
  ldr x1, [sp, #112]
  ldr x2, [sp, #232]
  cmp x1, x2
  b.gt .L284
.L277:
  ldr x1, [sp, #104]
  ldr x2, [sp, #240]
  sub x3, x1, x2
.L278:
  ldr x2, [sp, #248]
  mul x3, x3, x2
.L279:
  ldr x2, [sp, #112]
  add x3, x3, x2
.L280:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d10, [x0, x3, lsl #3]
.L281:
  fadd d10, d10, d9
.L282:
  ldr x1, [sp, #112]
  ldr x2, [sp, #256]
  add x0, x1, x2
  str x0, [sp, #112]
.L283:
  b .L276
.L284:
  ldr x1, [sp, #104]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #104]
.L285:
  b .L274
.L286:
  mov x0, #1
  str x0, [sp, #104]
.L287:
  ldr x1, [sp, #104]
  ldr x2, [sp, #272]
  cmp x1, x2
  b.gt .L298
.L288:
  mov x0, #1
  str x0, [sp, #96]
.L289:
  ldr x1, [sp, #96]
  ldr x2, [sp, #280]
  cmp x1, x2
  b.gt .L296
.L290:
  ldr x1, [sp, #104]
  ldr x2, [sp, #288]
  sub x3, x1, x2
.L291:
  ldr x2, [sp, #296]
  mul x3, x3, x2
.L292:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L293:
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  str d11, [x0, x3, lsl #3]
.L294:
  ldr x1, [sp, #96]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #96]
.L295:
  b .L289
.L296:
  ldr x1, [sp, #104]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #104]
.L297:
  b .L287
.L298:
  mov x0, #1
  str x0, [sp, #8]
.L299:
  ldr x1, [sp, #8]
  ldr x2, [sp, #320]
  cmp x1, x2
  b.gt .L429
.L300:
  mov x0, #0
  str x0, [sp, #984]
.L301:
  mov x0, #0
  mov x3, x0
.L302:
  ldr x2, [sp, #8]
  add x9, x3, x2
.L303:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d3, [x0, x9, lsl #3]
.L304:
  fcvtzs x0, d3
  mov x3, x0
.L305:
  mov x0, x3
  str x0, [sp, #24]
.L306:
  mov x0, #1
  str x0, [sp, #992]
.L307:
  mov x0, #64
  mov x3, x0
.L308:
  ldr x2, [sp, #8]
  add x8, x3, x2
.L309:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d3, [x0, x8, lsl #3]
.L310:
  fcvtzs x0, d3
  mov x3, x0
.L311:
  mov x0, x3
  str x0, [sp, #32]
.L312:
  ldr x1, [sp, #24]
  ldr x2, [sp, #376]
  and x0, x1, x2
  str x0, [sp, #24]
.L313:
  ldr x1, [sp, #32]
  ldr x2, [sp, #384]
  and x0, x1, x2
  str x0, [sp, #32]
.L314:
  mov x0, #2
  str x0, [sp, #1000]
.L315:
  mov x0, #128
  mov x3, x0
.L316:
  ldr x2, [sp, #8]
  add x6, x3, x2
.L317:
  mov x0, #2
  str x0, [sp, #1008]
.L318:
  mov x0, #128
  str x0, [sp, #1016]
.L319:
  mov x0, x6
  mov x7, x0
.L320:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d4, [x0, x7, lsl #3]
.L321:
  ldr x1, [sp, #32]
  ldr x2, [sp, #440]
  add x4, x1, x2
.L322:
  ldr x2, [sp, #448]
  sub x3, x4, x2
.L323:
  ldr x2, [sp, #456]
  mul x5, x3, x2
.L324:
  ldr x1, [sp, #24]
  ldr x2, [sp, #464]
  add x3, x1, x2
.L325:
  add x5, x5, x3
.L326:
  mov x0, #4097
  cmp x5, x0
  b.hs .Lbounds_err
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  ldr d3, [x0, x5, lsl #3]
.L327:
  fadd d3, d4, d3
.L328:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d3, [x0, x6, lsl #3]
.L329:
  mov x0, #3
  str x0, [sp, #1024]
.L330:
  mov x0, #192
  mov x5, x0
.L331:
  ldr x2, [sp, #8]
  add x6, x5, x2
.L332:
  mov x0, #3
  str x0, [sp, #1032]
.L333:
  mov x0, #192
  str x0, [sp, #1040]
.L334:
  mov x0, x6
  mov x5, x0
.L335:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d4, [x0, x5, lsl #3]
.L336:
  mov x0, x4
  mov x4, x0
.L337:
  ldr x2, [sp, #528]
  sub x4, x4, x2
.L338:
  ldr x2, [sp, #536]
  mul x4, x4, x2
.L339:
  mov x0, x3
  mov x3, x0
.L340:
  add x3, x4, x3
.L341:
  mov x0, #4097
  cmp x3, x0
  b.hs .Lbounds_err
  adrp x0, _arr_c@PAGE
  add x0, x0, _arr_c@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L342:
  fadd d3, d4, d3
.L343:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d3, [x0, x6, lsl #3]
.L344:
  mov x0, #0
  str x0, [sp, #1048]
.L345:
  mov x0, #0
  str x0, [sp, #1056]
.L346:
  mov x0, x9
  mov x4, x0
.L347:
  mov x0, #0
  str x0, [sp, #1064]
.L348:
  mov x0, #0
  str x0, [sp, #1072]
.L349:
  mov x0, x4
  mov x3, x0
.L350:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L351:
  mov x0, #2
  str x0, [sp, #1080]
.L352:
  mov x0, #128
  str x0, [sp, #1088]
.L353:
  mov x0, x7
  mov x6, x0
.L354:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d3, [x0, x6, lsl #3]
.L355:
  fadd d3, d4, d3
.L356:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d3, [x0, x4, lsl #3]
.L357:
  mov x0, #1
  str x0, [sp, #1096]
.L358:
  mov x0, #64
  str x0, [sp, #1104]
.L359:
  mov x0, x8
  mov x6, x0
.L360:
  mov x0, #1
  str x0, [sp, #1112]
.L361:
  mov x0, #64
  str x0, [sp, #1120]
.L362:
  mov x0, x6
  mov x4, x0
.L363:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d4, [x0, x4, lsl #3]
.L364:
  mov x0, #3
  str x0, [sp, #1128]
.L365:
  mov x0, #192
  str x0, [sp, #1136]
.L366:
  mov x0, x5
  mov x5, x0
.L367:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d3, [x0, x5, lsl #3]
.L368:
  fadd d3, d4, d3
.L369:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d3, [x0, x6, lsl #3]
.L370:
  mov x0, #0
  str x0, [sp, #1144]
.L371:
  mov x0, #0
  str x0, [sp, #1152]
.L372:
  mov x0, x3
  mov x3, x0
.L373:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L374:
  fcvtzs x0, d3
  mov x5, x0
.L375:
  mov x0, x5
  str x0, [sp, #40]
.L376:
  mov x0, #1
  str x0, [sp, #1160]
.L377:
  mov x0, #64
  str x0, [sp, #1168]
.L378:
  mov x0, x4
  mov x5, x0
.L379:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d3, [x0, x5, lsl #3]
.L380:
  fcvtzs x0, d3
  mov x4, x0
.L381:
  mov x0, x4
  str x0, [sp, #48]
.L382:
  ldr x1, [sp, #40]
  and x4, x1, x28
.L383:
  sub x0, x4, x27
  str x0, [sp, #40]
.L384:
  ldr x1, [sp, #48]
  and x4, x1, x26
.L385:
  sub x0, x4, x25
  str x0, [sp, #48]
.L386:
  mov x0, #0
  str x0, [sp, #1176]
.L387:
  mov x0, #0
  str x0, [sp, #1184]
.L388:
  mov x0, x3
  mov x4, x0
.L389:
  mov x0, #0
  str x0, [sp, #1192]
.L390:
  mov x0, #0
  str x0, [sp, #1200]
.L391:
  mov x0, x4
  mov x3, x0
.L392:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L393:
  ldr x1, [sp, #40]
  add x3, x1, x24
.L394:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L395:
  fadd d3, d4, d3
.L396:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d3, [x0, x4, lsl #3]
.L397:
  mov x0, #1
  str x0, [sp, #1208]
.L398:
  mov x0, #64
  str x0, [sp, #1216]
.L399:
  mov x0, x5
  mov x4, x0
.L400:
  mov x0, #1
  str x0, [sp, #1224]
.L401:
  mov x0, #64
  str x0, [sp, #1232]
.L402:
  mov x0, x4
  mov x3, x0
.L403:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L404:
  ldr x1, [sp, #48]
  add x3, x1, x23
.L405:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L406:
  fadd d3, d4, d3
.L407:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d3, [x0, x4, lsl #3]
.L408:
  ldr x1, [sp, #40]
  add x3, x1, x22
.L409:
  cmp x3, #97
  b.hs .Lbounds_err
  adrp x0, _arr_e@PAGE
  add x0, x0, _arr_e@PAGEOFF
  ldr x3, [x0, x3, lsl #3]
.L410:
  ldr x1, [sp, #40]
  add x0, x1, x3
  str x0, [sp, #40]
.L411:
  ldr x1, [sp, #48]
  add x3, x1, x21
.L412:
  cmp x3, #97
  b.hs .Lbounds_err
  adrp x0, _arr_f@PAGE
  add x0, x0, _arr_f@PAGEOFF
  ldr x3, [x0, x3, lsl #3]
.L413:
  ldr x1, [sp, #48]
  add x0, x1, x3
  str x0, [sp, #48]
.L414:
  ldr x1, [sp, #48]
  add x4, x1, x20
.L415:
  sub x3, x4, x19
.L416:
  mul x5, x3, x15
.L417:
  ldr x1, [sp, #40]
  add x3, x1, x14
.L418:
  add x5, x5, x3
.L419:
  mov x0, x4
  mov x4, x0
.L420:
  sub x4, x4, x13
.L421:
  mul x4, x4, x12
.L422:
  mov x0, x3
  mov x3, x0
.L423:
  add x3, x4, x3
.L424:
  mov x0, #6177
  cmp x3, x0
  b.hs .Lbounds_err
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L425:
  fadd d3, d3, d5
.L426:
  mov x0, #6177
  cmp x5, x0
  b.hs .Lbounds_err
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  str d3, [x0, x5, lsl #3]
.L427:
  ldr x1, [sp, #8]
  add x0, x1, x11
  str x0, [sp, #8]
.L428:
  b .L299
.L429:
  ldr x1, [sp, #16]
  add x0, x1, x10
  str x0, [sp, #16]
.L430:
  b .L271
.L431:
  mov x0, #1
  str x0, [sp, #1240]
.L432:
  mov x0, #1
  str x0, [sp, #1248]
.L433:
  mov x0, #0
  str x0, [sp, #1256]
.L434:
  mov x0, #64
  str x0, [sp, #1264]
.L435:
  mov x0, #0
  str x0, [sp, #1272]
.L436:
  mov x0, #1
  str x0, [sp, #1280]
.L437:
  mov x0, #1
  mov x3, x0
.L438:
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L439:
  str d7, [sp, #80]
  str d6, [sp, #88]
  str x9, [sp, #120]
  str x8, [sp, #128]
  str x7, [sp, #136]
  str x6, [sp, #144]
  str x5, [sp, #152]
  str x4, [sp, #160]
  str x3, [sp, #168]
  str d3, [sp, #176]
  str d5, [sp, #192]
  str d4, [sp, #200]
  str x15, [sp, #920]
  str x14, [sp, #928]
  str x13, [sp, #944]
  str x12, [sp, #952]
  str x11, [sp, #968]
  str x10, [sp, #976]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_439@PAGE
  add x0, x0, .Lfmt_print_439@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d7, [sp, #80]
  ldr d6, [sp, #88]
  ldr x9, [sp, #120]
  ldr x8, [sp, #128]
  ldr x7, [sp, #136]
  ldr x6, [sp, #144]
  ldr x5, [sp, #152]
  ldr x4, [sp, #160]
  ldr x3, [sp, #168]
  ldr d3, [sp, #176]
  ldr d5, [sp, #192]
  ldr d4, [sp, #200]
  ldr x15, [sp, #920]
  ldr x14, [sp, #928]
  ldr x13, [sp, #944]
  ldr x12, [sp, #952]
  ldr x11, [sp, #968]
  ldr x10, [sp, #976]
.L440:
  str d10, [sp, #1288]
.L441:
  str d9, [sp, #1296]
.L442:
  str d8, [sp, #1304]
.L443:
  str d7, [sp, #1312]
.L444:
  str d6, [sp, #1320]
.L445:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print ip
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x1, .Lname_ip@PAGE
  add x1, x1, .Lname_ip@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i1
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x1, .Lname_i1@PAGE
  add x1, x1, .Lname_i1@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j1
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x1, .Lname_j1@PAGE
  add x1, x1, .Lname_j1@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i2
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x1, .Lname_i2@PAGE
  add x1, x1, .Lname_i2@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j2
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x1, .Lname_j2@PAGE
  add x1, x1, .Lname_j2@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ds (float)
  ldr d0, [sp, #1288]
  sub sp, sp, #32
  adrp x1, .Lname_ds@PAGE
  add x1, x1, .Lname_ds@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dw (float)
  ldr d0, [sp, #1296]
  sub sp, sp, #32
  adrp x1, .Lname_dw@PAGE
  add x1, x1, .Lname_dw@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #1304]
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
  ldr d0, [sp, #1312]
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
  ldr d0, [sp, #1320]
  sub sp, sp, #32
  adrp x1, .Lname_fizz@PAGE
  add x1, x1, .Lname_fizz@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print i
  ldr x9, [sp, #96]
  sub sp, sp, #16
  adrp x1, .Lname_i@PAGE
  add x1, x1, .Lname_i@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j
  ldr x9, [sp, #104]
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
  ldr x9, [sp, #112]
  sub sp, sp, #16
  adrp x1, .Lname_k@PAGE
  add x1, x1, .Lname_k@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  // Restore callee-saved registers
  ldr x28, [sp, #1328]
  ldr x27, [sp, #1336]
  ldr x26, [sp, #1344]
  ldr x25, [sp, #1352]
  ldr x24, [sp, #1360]
  ldr x23, [sp, #1368]
  ldr x22, [sp, #1376]
  ldr x21, [sp, #1384]
  ldr x20, [sp, #1392]
  ldr x19, [sp, #1400]
  ldr d10, [sp, #1408]
  ldr d9, [sp, #1416]
  ldr d8, [sp, #1424]
  ldr d11, [sp, #1432]
  ldr x29, [sp, #1440]
  ldr x30, [sp, #1448]
  add sp, sp, #1456
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

.Lfmt_print_439:
  .asciz "%f\n"

.Lname_ip:
  .asciz "ip"
.Lname_rep:
  .asciz "rep"
.Lname_i1:
  .asciz "i1"
.Lname_j1:
  .asciz "j1"
.Lname_i2:
  .asciz "i2"
.Lname_j2:
  .asciz "j2"
.Lname_ds:
  .asciz "ds"
.Lname_dw:
  .asciz "dw"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"
.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"

.section __DATA,__data
.global _arr_p
.align 3
_arr_p:
  .space 2056
.global _arr_b
.align 3
_arr_b:
  .space 32776
.global _arr_c
.align 3
_arr_c:
  .space 32776
.global _arr_h
.align 3
_arr_h:
  .space 49416
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_e
.align 3
_arr_e:
  .space 776
.global _arr_f
.align 3
_arr_f:
  .space 776
