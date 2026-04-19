.global _main
.align 2

_main:
  sub sp, sp, #784
  str x30, [sp, #776]
  str x29, [sp, #768]
  add x29, sp, #768
  // Save callee-saved registers
  str d8, [sp, #696]
  str d9, [sp, #704]
  str d10, [sp, #712]
  str d11, [sp, #720]
  str d12, [sp, #728]
  str d13, [sp, #736]
  str d15, [sp, #744]
  str d14, [sp, #752]

  // Initialize all variables to 0
  mov x0, #0

  mov x10, #0
  mov x9, #0
  mov x8, #0
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
  mov x11, #0
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
  str x0, [sp, #648]
  str x0, [sp, #656]
  str x0, [sp, #664]
  str x0, [sp, #672]
  str x0, [sp, #680]
  str x0, [sp, #688]

.L0:
  mov x0, #0
  mov x10, x0
.L1:
  mov x0, #0
  mov x9, x0
.L2:
  mov x0, #0
  mov x8, x0
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
  mov x10, x0
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
  cmp x10, x4
  b.gt .L34
.L26:
  ldr d2, [sp, #96]
  fsub d3, d6, d2
.L27:
  ldr d0, [sp, #96]
  fmadd d15, d3, d15, d0
.L28:
  ldr d2, [sp, #96]
  fsub d0, d5, d2
  str d0, [sp, #96]
.L29:
  fsub d3, d15, d14
.L30:
  fmul d3, d3, d4
.L31:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L32:
  add x10, x10, x3
.L33:
  b .L25
.L34:
  mov x0, #16
  mov x3, x0
.L35:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L36:
  str d3, [sp, #80]
.L37:
  mov x0, #17
  mov x3, x0
.L38:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L39:
  fmov d13, d3
.L40:
  mov x0, #18
  mov x3, x0
.L41:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L42:
  fmov d12, d3
.L43:
  mov x0, #19
  mov x3, x0
.L44:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L45:
  fmov d11, d3
.L46:
  mov x0, #20
  mov x3, x0
.L47:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L48:
  fmov d10, d3
.L49:
  mov x0, #21
  mov x3, x0
.L50:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L51:
  fmov d9, d3
.L52:
  mov x0, #22
  mov x3, x0
.L53:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L54:
  fmov d8, d3
.L55:
  mov x0, #12
  mov x3, x0
.L56:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L57:
  fmov d7, d3
.L58:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L59:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L60:
  ldr d2, [sp, #96]
  fadd d15, d3, d2
.L61:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L62:
  ldr d2, [sp, #96]
  fmul d14, d3, d2
.L63:
  mov x0, #1
  mov x9, x0
.L64:
  mov x0, #25
  mov x11, x0
.L65:
  mov x0, #101
  mov x8, x0
.L66:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L67:
  mov x0, #0
  fmov d5, x0
.L68:
  mov x0, #1
  mov x7, x0
.L69:
  mov x0, #101
  mov x6, x0
.L70:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L71:
  mov x0, #1
  mov x5, x0
.L72:
  mov x0, #1
  mov x4, x0
.L73:
  cmp x9, x11
  b.gt .L89
.L74:
  mov x0, #1
  mov x10, x0
.L75:
  cmp x10, x8
  b.gt .L87
.L76:
  ldr d2, [sp, #96]
  fsub d3, d6, d2
.L77:
  ldr d0, [sp, #96]
  fmadd d15, d3, d15, d0
.L78:
  ldr d2, [sp, #96]
  fsub d0, d5, d2
  str d0, [sp, #96]
.L79:
  sub x3, x9, x7
.L80:
  mul x3, x3, x6
.L81:
  add x3, x3, x10
.L82:
  fsub d3, d15, d14
.L83:
  fmul d3, d3, d4
.L84:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d3, [x0, x3, lsl #3]
.L85:
  add x10, x10, x5
.L86:
  b .L75
.L87:
  add x9, x9, x4
.L88:
  b .L73
.L89:
  mov x0, #1
  mov x8, x0
.L90:
  movz x0, #18200
  movk x0, #925, lsl #16
  mov x11, x0
.L91:
  mov x0, #101
  mov x7, x0
.L92:
  mov x0, #1
  str x0, [sp, #200]
.L93:
  mov x0, #1
  str x0, [sp, #208]
.L94:
  mov x0, #101
  str x0, [sp, #216]
.L95:
  mov x0, #13
  str x0, [sp, #224]
.L96:
  mov x0, #1
  str x0, [sp, #232]
.L97:
  mov x0, #101
  str x0, [sp, #240]
.L98:
  mov x0, #12
  str x0, [sp, #248]
.L99:
  mov x0, #1
  str x0, [sp, #256]
.L100:
  mov x0, #101
  str x0, [sp, #264]
.L101:
  mov x0, #11
  str x0, [sp, #272]
.L102:
  mov x0, #1
  str x0, [sp, #280]
.L103:
  mov x0, #101
  str x0, [sp, #288]
.L104:
  mov x0, #10
  str x0, [sp, #296]
.L105:
  mov x0, #1
  str x0, [sp, #304]
.L106:
  mov x0, #101
  str x0, [sp, #312]
.L107:
  mov x0, #9
  str x0, [sp, #320]
.L108:
  mov x0, #1
  str x0, [sp, #328]
.L109:
  mov x0, #101
  str x0, [sp, #336]
.L110:
  mov x0, #8
  str x0, [sp, #344]
.L111:
  mov x0, #1
  str x0, [sp, #352]
.L112:
  mov x0, #101
  str x0, [sp, #360]
.L113:
  mov x0, #7
  str x0, [sp, #368]
.L114:
  mov x0, #1
  str x0, [sp, #376]
.L115:
  mov x0, #101
  str x0, [sp, #384]
.L116:
  mov x0, #5
  str x0, [sp, #392]
.L117:
  mov x0, #1
  str x0, [sp, #400]
.L118:
  mov x0, #101
  str x0, [sp, #408]
.L119:
  mov x0, #6
  str x0, [sp, #416]
.L120:
  mov x0, #1
  str x0, [sp, #424]
.L121:
  mov x0, #101
  str x0, [sp, #432]
.L122:
  mov x0, #3
  str x0, [sp, #440]
.L123:
  mov x0, #1
  str x0, [sp, #448]
.L124:
  mov x0, #101
  str x0, [sp, #456]
.L125:
  mov x0, #1
  mov x6, x0
.L126:
  mov x0, #1
  mov x5, x0
.L127:
  cmp x8, x11
  b.gt .L188
.L128:
  mov x0, #1
  mov x10, x0
.L129:
  cmp x10, x7
  b.gt .L186
.L130:
  mov x0, #0
  str x0, [sp, #464]
.L131:
  mov x0, #0
  mov x3, x0
.L132:
  add x4, x3, x10
.L133:
  mov x0, #12
  str x0, [sp, #472]
.L134:
  mov x0, #1212
  mov x3, x0
.L135:
  add x3, x3, x10
.L136:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L137:
  fmul d4, d8, d3
.L138:
  mov x0, #11
  str x0, [sp, #480]
.L139:
  mov x0, #1111
  mov x3, x0
.L140:
  add x3, x3, x10
.L141:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L142:
  fmadd d4, d9, d3, d4
.L143:
  mov x0, #10
  str x0, [sp, #488]
.L144:
  mov x0, #1010
  mov x3, x0
.L145:
  add x3, x3, x10
.L146:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L147:
  fmadd d4, d10, d3, d4
.L148:
  mov x0, #9
  str x0, [sp, #496]
.L149:
  mov x0, #909
  mov x3, x0
.L150:
  add x3, x3, x10
.L151:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L152:
  fmadd d4, d11, d3, d4
.L153:
  mov x0, #8
  str x0, [sp, #504]
.L154:
  mov x0, #808
  mov x3, x0
.L155:
  add x3, x3, x10
.L156:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L157:
  fmadd d4, d12, d3, d4
.L158:
  mov x0, #7
  str x0, [sp, #512]
.L159:
  mov x0, #707
  mov x3, x0
.L160:
  add x3, x3, x10
.L161:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L162:
  fmadd d4, d13, d3, d4
.L163:
  mov x0, #6
  str x0, [sp, #520]
.L164:
  mov x0, #606
  mov x3, x0
.L165:
  add x3, x3, x10
.L166:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L167:
  ldr d1, [sp, #80]
  fmadd d5, d1, d3, d4
.L168:
  mov x0, #4
  str x0, [sp, #528]
.L169:
  mov x0, #404
  mov x3, x0
.L170:
  add x3, x3, x10
.L171:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L172:
  mov x0, #5
  str x0, [sp, #536]
.L173:
  mov x0, #505
  mov x3, x0
.L174:
  add x3, x3, x10
.L175:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L176:
  fadd d3, d4, d3
.L177:
  fmadd d4, d7, d3, d5
.L178:
  mov x0, #2
  str x0, [sp, #544]
.L179:
  mov x0, #202
  mov x3, x0
.L180:
  add x3, x3, x10
.L181:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L182:
  fadd d3, d4, d3
.L183:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d3, [x0, x4, lsl #3]
.L184:
  add x10, x10, x6
.L185:
  b .L129
.L186:
  add x8, x8, x5
.L187:
  b .L127
.L188:
  mov x0, #1
  str x0, [sp, #552]
.L189:
  mov x0, #1
  str x0, [sp, #560]
.L190:
  mov x0, #0
  str x0, [sp, #568]
.L191:
  mov x0, #101
  str x0, [sp, #576]
.L192:
  mov x0, #0
  str x0, [sp, #584]
.L193:
  mov x0, #51
  str x0, [sp, #592]
.L194:
  mov x0, #51
  mov x3, x0
.L195:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L196:
  str x10, [sp, #8]
  str x9, [sp, #16]
  str x8, [sp, #24]
  str d7, [sp, #88]
  str d3, [sp, #120]
  str x4, [sp, #128]
  str d6, [sp, #136]
  str d5, [sp, #144]
  str d4, [sp, #152]
  str x3, [sp, #160]
  str x11, [sp, #168]
  str x7, [sp, #176]
  str x6, [sp, #184]
  str x5, [sp, #192]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_196@PAGE
  add x0, x0, .Lfmt_print_196@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x10, [sp, #8]
  ldr x9, [sp, #16]
  ldr x8, [sp, #24]
  ldr d7, [sp, #88]
  ldr d3, [sp, #120]
  ldr x4, [sp, #128]
  ldr d6, [sp, #136]
  ldr d5, [sp, #144]
  ldr d4, [sp, #152]
  ldr x3, [sp, #160]
  ldr x11, [sp, #168]
  ldr x7, [sp, #176]
  ldr x6, [sp, #184]
  ldr x5, [sp, #192]
.L197:
  mov x0, x10
  str x0, [sp, #600]
.L198:
  mov x0, x9
  str x0, [sp, #608]
.L199:
  mov x0, x8
  str x0, [sp, #616]
.L200:
  str d8, [sp, #624]
.L201:
  str d9, [sp, #632]
.L202:
  str d10, [sp, #640]
.L203:
  str d11, [sp, #648]
.L204:
  str d12, [sp, #656]
.L205:
  str d13, [sp, #664]
.L206:
  str d7, [sp, #672]
.L207:
  str d15, [sp, #680]
.L208:
  str d14, [sp, #688]
.L209:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #600]
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
  ldr x9, [sp, #608]
  sub sp, sp, #16
  adrp x1, .Lname_j@PAGE
  add x1, x1, .Lname_j@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #616]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print dm28 (float)
  ldr d0, [sp, #624]
  sub sp, sp, #32
  adrp x1, .Lname_dm28@PAGE
  add x1, x1, .Lname_dm28@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm27 (float)
  ldr d0, [sp, #632]
  sub sp, sp, #32
  adrp x1, .Lname_dm27@PAGE
  add x1, x1, .Lname_dm27@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm26 (float)
  ldr d0, [sp, #640]
  sub sp, sp, #32
  adrp x1, .Lname_dm26@PAGE
  add x1, x1, .Lname_dm26@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm25 (float)
  ldr d0, [sp, #648]
  sub sp, sp, #32
  adrp x1, .Lname_dm25@PAGE
  add x1, x1, .Lname_dm25@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm24 (float)
  ldr d0, [sp, #656]
  sub sp, sp, #32
  adrp x1, .Lname_dm24@PAGE
  add x1, x1, .Lname_dm24@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm23 (float)
  ldr d0, [sp, #664]
  sub sp, sp, #32
  adrp x1, .Lname_dm23@PAGE
  add x1, x1, .Lname_dm23@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dm22 (float)
  ldr d0, [sp, #80]
  sub sp, sp, #32
  adrp x1, .Lname_dm22@PAGE
  add x1, x1, .Lname_dm22@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print c0 (float)
  ldr d0, [sp, #672]
  sub sp, sp, #32
  adrp x1, .Lname_c0@PAGE
  add x1, x1, .Lname_c0@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #96]
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
  ldr d0, [sp, #680]
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
  ldr d0, [sp, #688]
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
  ldr d8, [sp, #696]
  ldr d9, [sp, #704]
  ldr d10, [sp, #712]
  ldr d11, [sp, #720]
  ldr d12, [sp, #728]
  ldr d13, [sp, #736]
  ldr d15, [sp, #744]
  ldr d14, [sp, #752]
  ldr x29, [sp, #768]
  ldr x30, [sp, #776]
  add sp, sp, #784
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

.Lfmt_print_196:
  .asciz "%f\n"

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
