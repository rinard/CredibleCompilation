.global _main
.align 2

_main:
  sub sp, sp, #736
  str x30, [sp, #728]
  str x29, [sp, #720]
  add x29, sp, #720
  // Save callee-saved registers
  str d8, [sp, #648]
  str d9, [sp, #656]
  str d10, [sp, #664]
  str d11, [sp, #672]
  str d12, [sp, #680]
  str d13, [sp, #688]
  str d15, [sp, #696]
  str d14, [sp, #704]

  // Initialize all variables to 0
  mov x0, #0

  mov x12, #0
  mov x11, #0
  mov x10, #0
  fmov d8, x0
  fmov d9, x0
  fmov d10, x0
  fmov d11, x0
  fmov d12, x0
  fmov d13, x0
  str x0, [sp, #80]
  fmov d7, x0
  str x0, [sp, #96]
  fmov d15, x0
  fmov d14, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #200]
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

.L0:
  mov x0, #0
  mov x12, x0
.L1:
  mov x0, #0
  mov x11, x0
.L2:
  mov x0, #0
  mov x10, x0
.L3:
  mov x0, #0
  fmov d8, x0
.L4:
  mov x0, #0
  fmov d9, x0
.L5:
  mov x0, #0
  fmov d10, x0
.L6:
  mov x0, #0
  fmov d11, x0
.L7:
  mov x0, #0
  fmov d12, x0
.L8:
  mov x0, #0
  fmov d13, x0
.L9:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #80]
.L10:
  mov x0, #0
  fmov d7, x0
.L11:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #96]
.L12:
  mov x0, #0
  fmov d15, x0
.L13:
  mov x0, #0
  fmov d14, x0
.L14:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L15:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L16:
  ldr d2, [sp, #96]
  fadd d15, d3, d2
.L17:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L18:
  ldr d2, [sp, #96]
  fmul d14, d3, d2
.L19:
  mov x0, #1
  mov x12, x0
.L20:
  mov x0, #39
  mov x4, x0
.L21:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L22:
  mov x0, #0
  fmov d5, x0
.L23:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L24:
  mov x0, #1
  mov x3, x0
.L25:
  mov x1, x12
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L35
.L26:
  ldr d2, [sp, #96]
  fsub d3, d6, d2
.L27:
  fmul d3, d3, d15
.L28:
  ldr d2, [sp, #96]
  fadd d15, d3, d2
.L29:
  ldr d2, [sp, #96]
  fsub d0, d5, d2
  str d0, [sp, #96]
.L30:
  fsub d3, d15, d14
.L31:
  fmul d3, d3, d4
.L32:
  mov x1, x12
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L33:
  add x12, x12, x3
.L34:
  b .L25
.L35:
  mov x0, #16
  mov x3, x0
.L36:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L37:
  str d3, [sp, #80]
.L38:
  mov x0, #17
  mov x3, x0
.L39:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L40:
  fmov d13, d3
.L41:
  mov x0, #18
  mov x3, x0
.L42:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L43:
  fmov d12, d3
.L44:
  mov x0, #19
  mov x3, x0
.L45:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L46:
  fmov d11, d3
.L47:
  mov x0, #20
  mov x3, x0
.L48:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L49:
  fmov d10, d3
.L50:
  mov x0, #21
  mov x3, x0
.L51:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L52:
  fmov d9, d3
.L53:
  mov x0, #22
  mov x3, x0
.L54:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L55:
  fmov d8, d3
.L56:
  mov x0, #12
  mov x3, x0
.L57:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L58:
  fmov d7, d3
.L59:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L60:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L61:
  ldr d2, [sp, #96]
  fadd d15, d3, d2
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L63:
  ldr d2, [sp, #96]
  fmul d14, d3, d2
.L64:
  mov x0, #1
  mov x11, x0
.L65:
  mov x0, #25
  mov x10, x0
.L66:
  mov x0, #101
  mov x9, x0
.L67:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L68:
  mov x0, #0
  fmov d5, x0
.L69:
  mov x0, #1
  mov x7, x0
.L70:
  mov x0, #101
  mov x6, x0
.L71:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L72:
  mov x0, #1
  mov x5, x0
.L73:
  mov x0, #1
  mov x4, x0
.L74:
  mov x1, x11
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L91
.L75:
  mov x0, #1
  mov x12, x0
.L76:
  mov x1, x12
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L89
.L77:
  ldr d2, [sp, #96]
  fsub d3, d6, d2
.L78:
  fmul d3, d3, d15
.L79:
  ldr d2, [sp, #96]
  fadd d15, d3, d2
.L80:
  ldr d2, [sp, #96]
  fsub d0, d5, d2
  str d0, [sp, #96]
.L81:
  sub x3, x11, x7
.L82:
  mul x3, x3, x6
.L83:
  add x3, x3, x12
.L84:
  fsub d3, d15, d14
.L85:
  fmul d3, d3, d4
.L86:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L87:
  add x12, x12, x5
.L88:
  b .L76
.L89:
  add x11, x11, x4
.L90:
  b .L74
.L91:
  mov x0, #1
  mov x10, x0
.L92:
  movz x0, #18200
  movk x0, #925, lsl #16
  mov x9, x0
.L93:
  mov x0, #101
  mov x7, x0
.L94:
  mov x0, #1
  str x0, [sp, #200]
.L95:
  mov x0, #1
  str x0, [sp, #208]
.L96:
  mov x0, #101
  str x0, [sp, #216]
.L97:
  mov x0, #13
  str x0, [sp, #224]
.L98:
  mov x0, #1
  str x0, [sp, #232]
.L99:
  mov x0, #101
  str x0, [sp, #240]
.L100:
  mov x0, #12
  str x0, [sp, #248]
.L101:
  mov x0, #1
  str x0, [sp, #256]
.L102:
  mov x0, #101
  str x0, [sp, #264]
.L103:
  mov x0, #11
  str x0, [sp, #272]
.L104:
  mov x0, #1
  str x0, [sp, #280]
.L105:
  mov x0, #101
  str x0, [sp, #288]
.L106:
  mov x0, #10
  str x0, [sp, #296]
.L107:
  mov x0, #1
  str x0, [sp, #304]
.L108:
  mov x0, #101
  str x0, [sp, #312]
.L109:
  mov x0, #9
  str x0, [sp, #320]
.L110:
  mov x0, #1
  str x0, [sp, #328]
.L111:
  mov x0, #101
  str x0, [sp, #336]
.L112:
  mov x0, #8
  str x0, [sp, #344]
.L113:
  mov x0, #1
  str x0, [sp, #352]
.L114:
  mov x0, #101
  str x0, [sp, #360]
.L115:
  mov x0, #7
  str x0, [sp, #368]
.L116:
  mov x0, #1
  str x0, [sp, #376]
.L117:
  mov x0, #101
  str x0, [sp, #384]
.L118:
  mov x0, #5
  str x0, [sp, #392]
.L119:
  mov x0, #1
  str x0, [sp, #400]
.L120:
  mov x0, #101
  str x0, [sp, #408]
.L121:
  mov x0, #6
  str x0, [sp, #416]
.L122:
  mov x0, #1
  str x0, [sp, #424]
.L123:
  mov x0, #101
  str x0, [sp, #432]
.L124:
  mov x0, #3
  str x0, [sp, #440]
.L125:
  mov x0, #1
  str x0, [sp, #448]
.L126:
  mov x0, #101
  str x0, [sp, #456]
.L127:
  mov x0, #1
  mov x6, x0
.L128:
  mov x0, #1
  mov x5, x0
.L129:
  mov x1, x10
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L197
.L130:
  mov x0, #1
  mov x12, x0
.L131:
  mov x1, x12
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L195
.L132:
  mov x0, #0
  str x0, [sp, #464]
.L133:
  mov x0, #0
  mov x3, x0
.L134:
  add x4, x3, x12
.L135:
  mov x0, #12
  str x0, [sp, #472]
.L136:
  mov x0, #1212
  mov x3, x0
.L137:
  add x3, x3, x12
.L138:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L139:
  fmul d4, d8, d3
.L140:
  mov x0, #11
  str x0, [sp, #480]
.L141:
  mov x0, #1111
  mov x3, x0
.L142:
  add x3, x3, x12
.L143:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L144:
  fmul d3, d9, d3
.L145:
  fadd d4, d4, d3
.L146:
  mov x0, #10
  str x0, [sp, #488]
.L147:
  mov x0, #1010
  mov x3, x0
.L148:
  add x3, x3, x12
.L149:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L150:
  fmul d3, d10, d3
.L151:
  fadd d4, d4, d3
.L152:
  mov x0, #9
  str x0, [sp, #496]
.L153:
  mov x0, #909
  mov x3, x0
.L154:
  add x3, x3, x12
.L155:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L156:
  fmul d3, d11, d3
.L157:
  fadd d4, d4, d3
.L158:
  mov x0, #8
  str x0, [sp, #504]
.L159:
  mov x0, #808
  mov x3, x0
.L160:
  add x3, x3, x12
.L161:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L162:
  fmul d3, d12, d3
.L163:
  fadd d4, d4, d3
.L164:
  mov x0, #7
  str x0, [sp, #512]
.L165:
  mov x0, #707
  mov x3, x0
.L166:
  add x3, x3, x12
.L167:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L168:
  fmul d3, d13, d3
.L169:
  fadd d4, d4, d3
.L170:
  mov x0, #6
  str x0, [sp, #520]
.L171:
  mov x0, #606
  mov x3, x0
.L172:
  add x3, x3, x12
.L173:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L174:
  ldr d1, [sp, #80]
  fmul d3, d1, d3
.L175:
  fadd d5, d4, d3
.L176:
  mov x0, #4
  str x0, [sp, #528]
.L177:
  mov x0, #404
  mov x3, x0
.L178:
  add x3, x3, x12
.L179:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L180:
  mov x0, #5
  str x0, [sp, #536]
.L181:
  mov x0, #505
  mov x3, x0
.L182:
  add x3, x3, x12
.L183:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L184:
  fadd d3, d4, d3
.L185:
  fmul d3, d7, d3
.L186:
  fadd d4, d5, d3
.L187:
  mov x0, #2
  str x0, [sp, #544]
.L188:
  mov x0, #202
  mov x3, x0
.L189:
  add x3, x3, x12
.L190:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L191:
  fadd d3, d4, d3
.L192:
  mov x1, x4
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L193:
  add x12, x12, x6
.L194:
  b .L131
.L195:
  add x10, x10, x5
.L196:
  b .L129
.L197:
  mov x0, x12
  str x0, [sp, #552]
.L198:
  mov x0, x11
  str x0, [sp, #560]
.L199:
  mov x0, x10
  str x0, [sp, #568]
.L200:
  str d8, [sp, #576]
.L201:
  str d9, [sp, #584]
.L202:
  str d10, [sp, #592]
.L203:
  str d11, [sp, #600]
.L204:
  str d12, [sp, #608]
.L205:
  str d13, [sp, #616]
.L206:
  str d7, [sp, #624]
.L207:
  str d15, [sp, #632]
.L208:
  str d14, [sp, #640]
.L209:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #552]
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
  ldr x9, [sp, #560]
  sub sp, sp, #16
  adrp x8, .Lname_j@PAGE
  add x8, x8, .Lname_j@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #568]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print dm28 (float)
  ldr d0, [sp, #576]
  sub sp, sp, #32
  adrp x8, .Lname_dm28@PAGE
  add x8, x8, .Lname_dm28@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm27 (float)
  ldr d0, [sp, #584]
  sub sp, sp, #32
  adrp x8, .Lname_dm27@PAGE
  add x8, x8, .Lname_dm27@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm26 (float)
  ldr d0, [sp, #592]
  sub sp, sp, #32
  adrp x8, .Lname_dm26@PAGE
  add x8, x8, .Lname_dm26@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm25 (float)
  ldr d0, [sp, #600]
  sub sp, sp, #32
  adrp x8, .Lname_dm25@PAGE
  add x8, x8, .Lname_dm25@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm24 (float)
  ldr d0, [sp, #608]
  sub sp, sp, #32
  adrp x8, .Lname_dm24@PAGE
  add x8, x8, .Lname_dm24@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm23 (float)
  ldr d0, [sp, #616]
  sub sp, sp, #32
  adrp x8, .Lname_dm23@PAGE
  add x8, x8, .Lname_dm23@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm22 (float)
  ldr d0, [sp, #80]
  sub sp, sp, #32
  adrp x8, .Lname_dm22@PAGE
  add x8, x8, .Lname_dm22@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print c0 (float)
  ldr d0, [sp, #624]
  sub sp, sp, #32
  adrp x8, .Lname_c0@PAGE
  add x8, x8, .Lname_c0@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #96]
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
  ldr d0, [sp, #632]
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
  ldr d0, [sp, #640]
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
  ldr d8, [sp, #648]
  ldr d9, [sp, #656]
  ldr d10, [sp, #664]
  ldr d11, [sp, #672]
  ldr d12, [sp, #680]
  ldr d13, [sp, #688]
  ldr d15, [sp, #696]
  ldr d14, [sp, #704]
  ldr x29, [sp, #720]
  ldr x30, [sp, #728]
  add sp, sp, #736
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
.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
.Lname_rep:
  .asciz "rep"
.Lname_dm28:
  .asciz "dm28"
.Lname_dm27:
  .asciz "dm27"
.Lname_dm26:
  .asciz "dm26"
.Lname_dm25:
  .asciz "dm25"
.Lname_dm24:
  .asciz "dm24"
.Lname_dm23:
  .asciz "dm23"
.Lname_dm22:
  .asciz "dm22"
.Lname_c0:
  .asciz "c0"
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
.global _arr_px
.align 3
_arr_px:
  .space 20208
