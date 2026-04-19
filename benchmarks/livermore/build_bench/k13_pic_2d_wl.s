.global _main
.align 2

_main:
  sub sp, sp, #1264
  str x30, [sp, #1256]
  str x29, [sp, #1248]
  add x29, sp, #1248
  // Save callee-saved registers
  str x28, [sp, #1128]
  str x27, [sp, #1136]
  str x26, [sp, #1144]
  str x25, [sp, #1152]
  str x24, [sp, #1160]
  str x23, [sp, #1168]
  str x22, [sp, #1176]
  str x21, [sp, #1184]
  str x20, [sp, #1192]
  str x19, [sp, #1200]
  str d11, [sp, #1208]
  str d10, [sp, #1216]
  str d9, [sp, #1224]
  str d8, [sp, #1232]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  str x0, [sp, #40]
  str x0, [sp, #48]
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]
  mov x10, #0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  mov x4, #0
  mov x3, #0
  fmov d3, x0
  fmov d6, x0
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
  mov x28, #0
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
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  str x0, [sp, #768]
  str x0, [sp, #776]
  str x0, [sp, #784]
  str x0, [sp, #792]
  str x0, [sp, #800]
  str x0, [sp, #808]
  mov x23, #0
  str x0, [sp, #824]
  str x0, [sp, #832]
  str x0, [sp, #840]
  str x0, [sp, #848]
  str x0, [sp, #856]
  str x0, [sp, #864]
  mov x22, #0
  mov x21, #0
  mov x20, #0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  mov x13, #0
  mov x12, #0
  mov x11, #0
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
  fmov d11, x0
.L7:
  mov x0, #0
  fmov d10, x0
.L8:
  mov x0, #0
  fmov d9, x0
.L9:
  mov x0, #0
  fmov d8, x0
.L10:
  mov x0, #0
  fmov d7, x0
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
  fmov d11, x0
.L15:
  movz x0, #0
  movk x0, #16352, lsl #48
  fmov d10, x0
.L16:
  mov x0, #1
  str x0, [sp, #104]
.L17:
  mov x0, #4
  mov x10, x0
.L18:
  mov x0, #64
  mov x9, x0
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
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L35
.L24:
  mov x0, #1
  str x0, [sp, #112]
.L25:
  ldr x1, [sp, #112]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L33
.L26:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L27:
  mul x3, x3, x6
.L28:
  ldr x2, [sp, #112]
  add x3, x3, x2
.L29:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d11, [x8, x1, lsl #3]
.L30:
  fadd d11, d11, d10
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
  fmov d9, x0
.L36:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L37:
  fadd d8, d3, d9
.L38:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L39:
  fmul d7, d3, d9
.L40:
  mov x0, #1
  str x0, [sp, #104]
.L41:
  mov x0, #64
  mov x10, x0
.L42:
  mov x0, #64
  mov x9, x0
.L43:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
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
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L67
.L51:
  mov x0, #1
  str x0, [sp, #96]
.L52:
  ldr x1, [sp, #96]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L65
.L53:
  fsub d3, d6, d9
.L54:
  fmul d3, d3, d8
.L55:
  fadd d8, d3, d9
.L56:
  fsub d9, d5, d9
.L57:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L58:
  mul x3, x3, x6
.L59:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L60:
  fsub d3, d8, d7
.L61:
  fmul d3, d3, d4
.L62:
  mov x1, x3
  adrp x8, _arr_b@PAGE
  add x8, x8, _arr_b@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L63:
  ldr x1, [sp, #96]
  add x0, x1, x5
  str x0, [sp, #96]
.L64:
  b .L52
.L65:
  ldr x1, [sp, #104]
  add x0, x1, x4
  str x0, [sp, #104]
.L66:
  b .L50
.L67:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L68:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L69:
  fadd d8, d3, d9
.L70:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L71:
  fmul d7, d3, d9
.L72:
  mov x0, #1
  str x0, [sp, #104]
.L73:
  mov x0, #64
  mov x10, x0
.L74:
  mov x0, #64
  mov x9, x0
.L75:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L76:
  mov x0, #0
  fmov d5, x0
.L77:
  mov x0, #1
  mov x7, x0
.L78:
  mov x0, #64
  mov x6, x0
.L79:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L80:
  mov x0, #1
  mov x5, x0
.L81:
  mov x0, #1
  mov x4, x0
.L82:
  ldr x1, [sp, #104]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L99
.L83:
  mov x0, #1
  str x0, [sp, #96]
.L84:
  ldr x1, [sp, #96]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L97
.L85:
  fsub d3, d6, d9
.L86:
  fmul d3, d3, d8
.L87:
  fadd d8, d3, d9
.L88:
  fsub d9, d5, d9
.L89:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L90:
  mul x3, x3, x6
.L91:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L92:
  fsub d3, d8, d7
.L93:
  fmul d3, d3, d4
.L94:
  mov x1, x3
  adrp x8, _arr_c@PAGE
  add x8, x8, _arr_c@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L95:
  ldr x1, [sp, #96]
  add x0, x1, x5
  str x0, [sp, #96]
.L96:
  b .L84
.L97:
  ldr x1, [sp, #104]
  add x0, x1, x4
  str x0, [sp, #104]
.L98:
  b .L82
.L99:
  mov x0, #1
  str x0, [sp, #104]
.L100:
  mov x0, #64
  mov x10, x0
.L101:
  mov x0, #64
  mov x9, x0
.L102:
  mov x0, #1
  mov x7, x0
.L103:
  mov x0, #64
  mov x6, x0
.L104:
  mov x0, #0
  fmov d3, x0
.L105:
  mov x0, #1
  mov x5, x0
.L106:
  mov x0, #1
  mov x4, x0
.L107:
  ldr x1, [sp, #104]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L118
.L108:
  mov x0, #1
  str x0, [sp, #96]
.L109:
  ldr x1, [sp, #96]
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L116
.L110:
  ldr x1, [sp, #104]
  sub x3, x1, x7
.L111:
  mul x3, x3, x6
.L112:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L113:
  mov x1, x3
  adrp x8, _arr_h@PAGE
  add x8, x8, _arr_h@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L114:
  ldr x1, [sp, #96]
  add x0, x1, x5
  str x0, [sp, #96]
.L115:
  b .L109
.L116:
  ldr x1, [sp, #104]
  add x0, x1, x4
  str x0, [sp, #104]
.L117:
  b .L107
.L118:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L119:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L120:
  fadd d8, d3, d9
.L121:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L122:
  fmul d7, d3, d9
.L123:
  mov x0, #1
  str x0, [sp, #112]
.L124:
  mov x0, #1001
  mov x4, x0
.L125:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L126:
  mov x0, #0
  fmov d5, x0
.L127:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L128:
  mov x0, #1
  mov x3, x0
.L129:
  ldr x1, [sp, #112]
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L139
.L130:
  fsub d3, d6, d9
.L131:
  fmul d3, d3, d8
.L132:
  fadd d8, d3, d9
.L133:
  fsub d9, d5, d9
.L134:
  fsub d3, d8, d7
.L135:
  fmul d3, d3, d4
.L136:
  ldr x1, [sp, #112]
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L137:
  ldr x1, [sp, #112]
  add x0, x1, x3
  str x0, [sp, #112]
.L138:
  b .L129
.L139:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L140:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L141:
  fadd d8, d3, d9
.L142:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L143:
  fmul d7, d3, d9
.L144:
  mov x0, #1
  str x0, [sp, #112]
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
  ldr x1, [sp, #112]
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L160
.L151:
  fsub d3, d6, d9
.L152:
  fmul d3, d3, d8
.L153:
  fadd d8, d3, d9
.L154:
  fsub d9, d5, d9
.L155:
  fsub d3, d8, d7
.L156:
  fmul d3, d3, d4
.L157:
  ldr x1, [sp, #112]
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L158:
  ldr x1, [sp, #112]
  add x0, x1, x3
  str x0, [sp, #112]
.L159:
  b .L150
.L160:
  mov x0, #1
  str x0, [sp, #96]
.L161:
  mov x0, #96
  mov x10, x0
.L162:
  mov x0, #1
  mov x9, x0
.L163:
  mov x0, #64
  mov x7, x0
.L164:
  mov x0, #1
  mov x6, x0
.L165:
  mov x0, #64
  mov x5, x0
.L166:
  mov x0, #1
  mov x4, x0
.L167:
  ldr x1, [sp, #96]
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L176
.L168:
  ldr x1, [sp, #96]
  sub x3, x1, x9
.L169:
  cbz x7, .Ldiv_by_zero
  sdiv x0, x3, x7
  mul x0, x0, x7
  sub x3, x3, x0
.L170:
  ldr x1, [sp, #96]
  mov x2, x3
  adrp x8, _arr_e@PAGE
  add x8, x8, _arr_e@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L171:
  ldr x1, [sp, #96]
  sub x3, x1, x6
.L172:
  cbz x5, .Ldiv_by_zero
  sdiv x0, x3, x5
  mul x0, x0, x5
  sub x3, x3, x0
.L173:
  ldr x1, [sp, #96]
  mov x2, x3
  adrp x8, _arr_f@PAGE
  add x8, x8, _arr_f@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L174:
  ldr x1, [sp, #96]
  add x0, x1, x4
  str x0, [sp, #96]
.L175:
  b .L167
.L176:
  mov x0, #1
  str x0, [sp, #16]
.L177:
  movz x0, #14096
  movk x0, #39, lsl #16
  str x0, [sp, #208]
.L178:
  mov x0, #4
  str x0, [sp, #216]
.L179:
  mov x0, #64
  str x0, [sp, #224]
.L180:
  mov x0, #1
  str x0, [sp, #232]
.L181:
  mov x0, #64
  str x0, [sp, #240]
.L182:
  mov x0, #1
  str x0, [sp, #248]
.L183:
  mov x0, #1
  str x0, [sp, #256]
.L184:
  mov x0, #64
  str x0, [sp, #264]
.L185:
  mov x0, #64
  str x0, [sp, #272]
.L186:
  mov x0, #1
  str x0, [sp, #280]
.L187:
  mov x0, #64
  str x0, [sp, #288]
.L188:
  mov x0, #0
  fmov d6, x0
.L189:
  mov x0, #1
  str x0, [sp, #296]
.L190:
  mov x0, #1
  str x0, [sp, #304]
.L191:
  mov x0, #64
  str x0, [sp, #312]
.L192:
  mov x0, #1
  str x0, [sp, #320]
.L193:
  mov x0, #1
  str x0, [sp, #328]
.L194:
  mov x0, #64
  str x0, [sp, #336]
.L195:
  mov x0, #2
  str x0, [sp, #344]
.L196:
  mov x0, #1
  str x0, [sp, #352]
.L197:
  mov x0, #64
  str x0, [sp, #360]
.L198:
  mov x0, #63
  str x0, [sp, #368]
.L199:
  mov x0, #63
  str x0, [sp, #376]
.L200:
  mov x0, #3
  str x0, [sp, #384]
.L201:
  mov x0, #1
  str x0, [sp, #392]
.L202:
  mov x0, #64
  str x0, [sp, #400]
.L203:
  mov x0, #3
  str x0, [sp, #408]
.L204:
  mov x0, #1
  str x0, [sp, #416]
.L205:
  mov x0, #64
  str x0, [sp, #424]
.L206:
  mov x0, #1
  str x0, [sp, #432]
.L207:
  mov x0, #1
  str x0, [sp, #440]
.L208:
  mov x0, #64
  str x0, [sp, #448]
.L209:
  mov x0, #1
  str x0, [sp, #456]
.L210:
  mov x0, #4
  str x0, [sp, #464]
.L211:
  mov x0, #1
  str x0, [sp, #472]
.L212:
  mov x0, #64
  str x0, [sp, #480]
.L213:
  mov x0, #4
  str x0, [sp, #488]
.L214:
  mov x0, #1
  str x0, [sp, #496]
.L215:
  mov x0, #64
  str x0, [sp, #504]
.L216:
  mov x0, #1
  str x0, [sp, #512]
.L217:
  mov x0, #1
  str x0, [sp, #520]
.L218:
  mov x0, #64
  str x0, [sp, #528]
.L219:
  mov x0, #1
  mov x28, x0
.L220:
  mov x0, #1
  str x0, [sp, #544]
.L221:
  mov x0, #1
  str x0, [sp, #552]
.L222:
  mov x0, #64
  str x0, [sp, #560]
.L223:
  mov x0, #1
  str x0, [sp, #568]
.L224:
  mov x0, #1
  str x0, [sp, #576]
.L225:
  mov x0, #64
  str x0, [sp, #584]
.L226:
  mov x0, #3
  str x0, [sp, #592]
.L227:
  mov x0, #1
  str x0, [sp, #600]
.L228:
  mov x0, #64
  str x0, [sp, #608]
.L229:
  mov x0, #2
  str x0, [sp, #616]
.L230:
  mov x0, #1
  str x0, [sp, #624]
.L231:
  mov x0, #64
  str x0, [sp, #632]
.L232:
  mov x0, #2
  str x0, [sp, #640]
.L233:
  mov x0, #1
  str x0, [sp, #648]
.L234:
  mov x0, #64
  str x0, [sp, #656]
.L235:
  mov x0, #4
  str x0, [sp, #664]
.L236:
  mov x0, #1
  str x0, [sp, #672]
.L237:
  mov x0, #64
  str x0, [sp, #680]
.L238:
  mov x0, #1
  str x0, [sp, #688]
.L239:
  mov x0, #1
  str x0, [sp, #696]
.L240:
  mov x0, #64
  str x0, [sp, #704]
.L241:
  mov x0, #2
  str x0, [sp, #712]
.L242:
  mov x0, #1
  str x0, [sp, #720]
.L243:
  mov x0, #64
  str x0, [sp, #728]
.L244:
  mov x0, #63
  mov x27, x0
.L245:
  mov x0, #1
  mov x26, x0
.L246:
  mov x0, #63
  mov x25, x0
.L247:
  mov x0, #1
  mov x24, x0
.L248:
  mov x0, #1
  str x0, [sp, #768]
.L249:
  mov x0, #1
  str x0, [sp, #776]
.L250:
  mov x0, #64
  str x0, [sp, #784]
.L251:
  mov x0, #1
  str x0, [sp, #792]
.L252:
  mov x0, #1
  str x0, [sp, #800]
.L253:
  mov x0, #64
  str x0, [sp, #808]
.L254:
  mov x0, #32
  mov x23, x0
.L255:
  mov x0, #2
  str x0, [sp, #824]
.L256:
  mov x0, #1
  str x0, [sp, #832]
.L257:
  mov x0, #64
  str x0, [sp, #840]
.L258:
  mov x0, #2
  str x0, [sp, #848]
.L259:
  mov x0, #1
  str x0, [sp, #856]
.L260:
  mov x0, #64
  str x0, [sp, #864]
.L261:
  mov x0, #32
  mov x22, x0
.L262:
  mov x0, #32
  mov x21, x0
.L263:
  mov x0, #32
  mov x20, x0
.L264:
  mov x0, #1
  mov x19, x0
.L265:
  mov x0, #1
  mov x15, x0
.L266:
  mov x0, #64
  mov x14, x0
.L267:
  mov x0, #1
  mov x13, x0
.L268:
  mov x0, #1
  mov x12, x0
.L269:
  mov x0, #1
  mov x11, x0
.L270:
  mov x0, #64
  mov x10, x0
.L271:
  mov x0, #1
  mov x9, x0
.L272:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d5, x0
.L273:
  mov x0, #1
  mov x7, x0
.L274:
  mov x0, #1
  mov x6, x0
.L275:
  ldr x1, [sp, #16]
  ldr x2, [sp, #208]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L435
.L276:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d11, x0
.L277:
  mov x0, #1
  str x0, [sp, #104]
.L278:
  ldr x1, [sp, #104]
  ldr x2, [sp, #216]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L290
.L279:
  mov x0, #1
  str x0, [sp, #112]
.L280:
  ldr x1, [sp, #112]
  ldr x2, [sp, #224]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L288
.L281:
  ldr x1, [sp, #104]
  ldr x2, [sp, #232]
  sub x3, x1, x2
.L282:
  ldr x2, [sp, #240]
  mul x3, x3, x2
.L283:
  ldr x2, [sp, #112]
  add x3, x3, x2
.L284:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d11, [x8, x1, lsl #3]
.L285:
  fadd d11, d11, d10
.L286:
  ldr x1, [sp, #112]
  ldr x2, [sp, #248]
  add x0, x1, x2
  str x0, [sp, #112]
.L287:
  b .L280
.L288:
  ldr x1, [sp, #104]
  ldr x2, [sp, #256]
  add x0, x1, x2
  str x0, [sp, #104]
.L289:
  b .L278
.L290:
  mov x0, #1
  str x0, [sp, #104]
.L291:
  ldr x1, [sp, #104]
  ldr x2, [sp, #264]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L302
.L292:
  mov x0, #1
  str x0, [sp, #96]
.L293:
  ldr x1, [sp, #96]
  ldr x2, [sp, #272]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L300
.L294:
  ldr x1, [sp, #104]
  ldr x2, [sp, #280]
  sub x3, x1, x2
.L295:
  ldr x2, [sp, #288]
  mul x3, x3, x2
.L296:
  ldr x2, [sp, #96]
  add x3, x3, x2
.L297:
  mov x1, x3
  adrp x8, _arr_h@PAGE
  add x8, x8, _arr_h@PAGEOFF
  str d6, [x8, x1, lsl #3]
.L298:
  ldr x1, [sp, #96]
  ldr x2, [sp, #296]
  add x0, x1, x2
  str x0, [sp, #96]
.L299:
  b .L293
.L300:
  ldr x1, [sp, #104]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #104]
.L301:
  b .L291
.L302:
  mov x0, #1
  str x0, [sp, #8]
.L303:
  ldr x1, [sp, #8]
  ldr x2, [sp, #312]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L433
.L304:
  mov x0, #0
  str x0, [sp, #944]
.L305:
  mov x0, #0
  mov x3, x0
.L306:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L307:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L308:
  fcvtzs x0, d3
  mov x3, x0
.L309:
  mov x0, x3
  str x0, [sp, #24]
.L310:
  mov x0, #1
  str x0, [sp, #952]
.L311:
  mov x0, #64
  mov x3, x0
.L312:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L313:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L314:
  fcvtzs x0, d3
  mov x3, x0
.L315:
  mov x0, x3
  str x0, [sp, #32]
.L316:
  ldr x1, [sp, #24]
  ldr x2, [sp, #368]
  and x0, x1, x2
  str x0, [sp, #24]
.L317:
  ldr x1, [sp, #32]
  ldr x2, [sp, #376]
  and x0, x1, x2
  str x0, [sp, #32]
.L318:
  mov x0, #2
  str x0, [sp, #960]
.L319:
  mov x0, #128
  mov x3, x0
.L320:
  ldr x2, [sp, #8]
  add x5, x3, x2
.L321:
  mov x0, #2
  str x0, [sp, #968]
.L322:
  mov x0, #128
  mov x3, x0
.L323:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L324:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L325:
  ldr x1, [sp, #32]
  ldr x2, [sp, #432]
  add x3, x1, x2
.L326:
  ldr x2, [sp, #440]
  sub x3, x3, x2
.L327:
  ldr x2, [sp, #448]
  mul x4, x3, x2
.L328:
  ldr x1, [sp, #24]
  ldr x2, [sp, #456]
  add x3, x1, x2
.L329:
  add x3, x4, x3
.L330:
  mov x1, x3
  mov x0, #4097
  cmp x1, x0
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_b@PAGE
  add x8, x8, _arr_b@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L331:
  fadd d3, d4, d3
.L332:
  mov x1, x5
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L333:
  mov x0, #3
  str x0, [sp, #976]
.L334:
  mov x0, #192
  mov x3, x0
.L335:
  ldr x2, [sp, #8]
  add x5, x3, x2
.L336:
  mov x0, #3
  str x0, [sp, #984]
.L337:
  mov x0, #192
  mov x3, x0
.L338:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L339:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L340:
  ldr x1, [sp, #32]
  ldr x2, [sp, #512]
  add x3, x1, x2
.L341:
  ldr x2, [sp, #520]
  sub x3, x3, x2
.L342:
  ldr x2, [sp, #528]
  mul x4, x3, x2
.L343:
  ldr x1, [sp, #24]
  add x3, x1, x28
.L344:
  add x3, x4, x3
.L345:
  mov x1, x3
  mov x0, #4097
  cmp x1, x0
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_c@PAGE
  add x8, x8, _arr_c@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L346:
  fadd d3, d4, d3
.L347:
  mov x1, x5
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L348:
  mov x0, #0
  str x0, [sp, #992]
.L349:
  mov x0, #0
  mov x3, x0
.L350:
  ldr x2, [sp, #8]
  add x4, x3, x2
.L351:
  mov x0, #0
  str x0, [sp, #1000]
.L352:
  mov x0, #0
  mov x3, x0
.L353:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L354:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L355:
  mov x0, #2
  str x0, [sp, #1008]
.L356:
  mov x0, #128
  mov x3, x0
.L357:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L358:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L359:
  fadd d3, d4, d3
.L360:
  mov x1, x4
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L361:
  mov x0, #1
  str x0, [sp, #1016]
.L362:
  mov x0, #64
  mov x3, x0
.L363:
  ldr x2, [sp, #8]
  add x4, x3, x2
.L364:
  mov x0, #1
  str x0, [sp, #1024]
.L365:
  mov x0, #64
  mov x3, x0
.L366:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L367:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L368:
  mov x0, #3
  str x0, [sp, #1032]
.L369:
  mov x0, #192
  mov x3, x0
.L370:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L371:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L372:
  fadd d3, d4, d3
.L373:
  mov x1, x4
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L374:
  mov x0, #0
  str x0, [sp, #1040]
.L375:
  mov x0, #0
  mov x3, x0
.L376:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L377:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L378:
  fcvtzs x0, d3
  mov x3, x0
.L379:
  mov x0, x3
  str x0, [sp, #40]
.L380:
  mov x0, #1
  str x0, [sp, #1048]
.L381:
  mov x0, #64
  mov x3, x0
.L382:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L383:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L384:
  fcvtzs x0, d3
  mov x3, x0
.L385:
  mov x0, x3
  str x0, [sp, #48]
.L386:
  ldr x1, [sp, #40]
  and x3, x1, x27
.L387:
  sub x0, x3, x26
  str x0, [sp, #40]
.L388:
  ldr x1, [sp, #48]
  and x3, x1, x25
.L389:
  sub x0, x3, x24
  str x0, [sp, #48]
.L390:
  mov x0, #0
  str x0, [sp, #1056]
.L391:
  mov x0, #0
  mov x3, x0
.L392:
  ldr x2, [sp, #8]
  add x4, x3, x2
.L393:
  mov x0, #0
  str x0, [sp, #1064]
.L394:
  mov x0, #0
  mov x3, x0
.L395:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L396:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L397:
  ldr x1, [sp, #40]
  add x3, x1, x23
.L398:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L399:
  fadd d3, d4, d3
.L400:
  mov x1, x4
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L401:
  mov x0, #1
  str x0, [sp, #1072]
.L402:
  mov x0, #64
  mov x3, x0
.L403:
  ldr x2, [sp, #8]
  add x4, x3, x2
.L404:
  mov x0, #1
  str x0, [sp, #1080]
.L405:
  mov x0, #64
  mov x3, x0
.L406:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L407:
  mov x1, x3
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L408:
  ldr x1, [sp, #48]
  add x3, x1, x22
.L409:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L410:
  fadd d3, d4, d3
.L411:
  mov x1, x4
  adrp x8, _arr_p@PAGE
  add x8, x8, _arr_p@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L412:
  ldr x1, [sp, #40]
  add x3, x1, x21
.L413:
  mov x1, x3
  cmp x1, #97
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_e@PAGE
  add x8, x8, _arr_e@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L414:
  ldr x1, [sp, #40]
  add x0, x1, x3
  str x0, [sp, #40]
.L415:
  ldr x1, [sp, #48]
  add x3, x1, x20
.L416:
  mov x1, x3
  cmp x1, #97
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_f@PAGE
  add x8, x8, _arr_f@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L417:
  ldr x1, [sp, #48]
  add x0, x1, x3
  str x0, [sp, #48]
.L418:
  ldr x1, [sp, #48]
  add x3, x1, x19
.L419:
  sub x3, x3, x15
.L420:
  mul x4, x3, x14
.L421:
  ldr x1, [sp, #40]
  add x3, x1, x13
.L422:
  add x5, x4, x3
.L423:
  ldr x1, [sp, #48]
  add x3, x1, x12
.L424:
  sub x3, x3, x11
.L425:
  mul x4, x3, x10
.L426:
  ldr x1, [sp, #40]
  add x3, x1, x9
.L427:
  add x3, x4, x3
.L428:
  mov x1, x3
  mov x0, #6177
  cmp x1, x0
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_h@PAGE
  add x8, x8, _arr_h@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L429:
  fadd d3, d3, d5
.L430:
  mov x1, x5
  mov x0, #6177
  cmp x1, x0
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_h@PAGE
  add x8, x8, _arr_h@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L431:
  ldr x1, [sp, #8]
  add x0, x1, x7
  str x0, [sp, #8]
.L432:
  b .L303
.L433:
  ldr x1, [sp, #16]
  add x0, x1, x6
  str x0, [sp, #16]
.L434:
  b .L275
.L435:
  str d11, [sp, #1088]
.L436:
  str d10, [sp, #1096]
.L437:
  str d9, [sp, #1104]
.L438:
  str d8, [sp, #1112]
.L439:
  str d7, [sp, #1120]
.L440:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print ip
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_ip@PAGE
  add x8, x8, .Lname_ip@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i1
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_i1@PAGE
  add x8, x8, .Lname_i1@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j1
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_j1@PAGE
  add x8, x8, .Lname_j1@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i2
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_i2@PAGE
  add x8, x8, .Lname_i2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j2
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x8, .Lname_j2@PAGE
  add x8, x8, .Lname_j2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ds (float)
  ldr d0, [sp, #1088]
  sub sp, sp, #32
  adrp x8, .Lname_ds@PAGE
  add x8, x8, .Lname_ds@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dw (float)
  ldr d0, [sp, #1096]
  sub sp, sp, #32
  adrp x8, .Lname_dw@PAGE
  add x8, x8, .Lname_dw@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #1104]
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
  ldr d0, [sp, #1112]
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
  ldr d0, [sp, #1120]
  sub sp, sp, #32
  adrp x8, .Lname_fizz@PAGE
  add x8, x8, .Lname_fizz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print i
  ldr x9, [sp, #96]
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
  ldr x9, [sp, #104]
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
  ldr x9, [sp, #112]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  // Restore callee-saved registers
  ldr x28, [sp, #1128]
  ldr x27, [sp, #1136]
  ldr x26, [sp, #1144]
  ldr x25, [sp, #1152]
  ldr x24, [sp, #1160]
  ldr x23, [sp, #1168]
  ldr x22, [sp, #1176]
  ldr x21, [sp, #1184]
  ldr x20, [sp, #1192]
  ldr x19, [sp, #1200]
  ldr d11, [sp, #1208]
  ldr d10, [sp, #1216]
  ldr d9, [sp, #1224]
  ldr d8, [sp, #1232]
  ldr x29, [sp, #1248]
  ldr x30, [sp, #1256]
  add sp, sp, #1264
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
