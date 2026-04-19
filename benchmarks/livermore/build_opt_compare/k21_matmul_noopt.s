.global _main
.align 2

_main:
  sub sp, sp, #800
  str x30, [sp, #792]
  str x29, [sp, #784]
  add x29, sp, #784

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  str x0, [sp, #40]
  str x0, [sp, #48]
  str x0, [sp, #56]
  str x0, [sp, #64]
  str x0, [sp, #72]
  str x0, [sp, #80]
  str x0, [sp, #88]
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]
  str x0, [sp, #120]
  str x0, [sp, #128]
  str x0, [sp, #136]
  str x0, [sp, #144]
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
  fmov d0, x0
  str d0, [sp, #40]
.L5:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #48]
.L6:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #56]
.L7:
  mov x0, #1
  str x0, [sp, #24]
.L8:
  mov x0, #2525
  str x0, [sp, #64]
.L9:
  ldr x1, [sp, #24]
  ldr x2, [sp, #64]
  cmp x1, x2
  b.gt .L15
.L10:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #72]
.L11:
  ldr x1, [sp, #24]
  ldr d0, [sp, #72]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L12:
  mov x0, #1
  str x0, [sp, #80]
.L13:
  ldr x1, [sp, #24]
  ldr x2, [sp, #80]
  add x0, x1, x2
  str x0, [sp, #24]
.L14:
  b .L8
.L15:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L16:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #88]
.L17:
  ldr d1, [sp, #88]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L18:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L19:
  ldr d1, [sp, #96]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L20:
  mov x0, #1
  str x0, [sp, #16]
.L21:
  mov x0, #101
  str x0, [sp, #104]
.L22:
  ldr x1, [sp, #16]
  ldr x2, [sp, #104]
  cmp x1, x2
  b.gt .L47
.L23:
  mov x0, #1
  str x0, [sp, #8]
.L24:
  mov x0, #25
  str x0, [sp, #112]
.L25:
  ldr x1, [sp, #8]
  ldr x2, [sp, #112]
  cmp x1, x2
  b.gt .L44
.L26:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #120]
.L27:
  ldr d1, [sp, #120]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #128]
.L28:
  ldr d1, [sp, #128]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #136]
.L29:
  ldr d1, [sp, #136]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L30:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #144]
.L31:
  ldr d1, [sp, #144]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L32:
  mov x0, #1
  str x0, [sp, #152]
.L33:
  ldr x1, [sp, #16]
  ldr x2, [sp, #152]
  sub x0, x1, x2
  str x0, [sp, #160]
.L34:
  mov x0, #25
  str x0, [sp, #168]
.L35:
  ldr x1, [sp, #160]
  ldr x2, [sp, #168]
  mul x0, x1, x2
  str x0, [sp, #176]
.L36:
  ldr x1, [sp, #176]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #184]
.L37:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L38:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #200]
.L39:
  ldr d1, [sp, #192]
  ldr d2, [sp, #200]
  fmul d0, d1, d2
  str d0, [sp, #208]
.L40:
  ldr x1, [sp, #184]
  ldr d0, [sp, #208]
  adrp x0, _arr_cx@PAGE
  add x0, x0, _arr_cx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L41:
  mov x0, #1
  str x0, [sp, #216]
.L42:
  ldr x1, [sp, #8]
  ldr x2, [sp, #216]
  add x0, x1, x2
  str x0, [sp, #8]
.L43:
  b .L24
.L44:
  mov x0, #1
  str x0, [sp, #224]
.L45:
  ldr x1, [sp, #16]
  ldr x2, [sp, #224]
  add x0, x1, x2
  str x0, [sp, #16]
.L46:
  b .L21
.L47:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L48:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #232]
.L49:
  ldr d1, [sp, #232]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L50:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #240]
.L51:
  ldr d1, [sp, #240]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L52:
  mov x0, #1
  str x0, [sp, #16]
.L53:
  mov x0, #25
  str x0, [sp, #248]
.L54:
  ldr x1, [sp, #16]
  ldr x2, [sp, #248]
  cmp x1, x2
  b.gt .L79
.L55:
  mov x0, #1
  str x0, [sp, #8]
.L56:
  mov x0, #101
  str x0, [sp, #256]
.L57:
  ldr x1, [sp, #8]
  ldr x2, [sp, #256]
  cmp x1, x2
  b.gt .L76
.L58:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #264]
.L59:
  ldr d1, [sp, #264]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #272]
.L60:
  ldr d1, [sp, #272]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #280]
.L61:
  ldr d1, [sp, #280]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L62:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #288]
.L63:
  ldr d1, [sp, #288]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L64:
  mov x0, #1
  str x0, [sp, #296]
.L65:
  ldr x1, [sp, #16]
  ldr x2, [sp, #296]
  sub x0, x1, x2
  str x0, [sp, #304]
.L66:
  mov x0, #101
  str x0, [sp, #312]
.L67:
  ldr x1, [sp, #304]
  ldr x2, [sp, #312]
  mul x0, x1, x2
  str x0, [sp, #320]
.L68:
  ldr x1, [sp, #320]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #328]
.L69:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #336]
.L70:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #344]
.L71:
  ldr d1, [sp, #336]
  ldr d2, [sp, #344]
  fmul d0, d1, d2
  str d0, [sp, #352]
.L72:
  ldr x1, [sp, #328]
  ldr d0, [sp, #352]
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L73:
  mov x0, #1
  str x0, [sp, #360]
.L74:
  ldr x1, [sp, #8]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #8]
.L75:
  b .L56
.L76:
  mov x0, #1
  str x0, [sp, #368]
.L77:
  ldr x1, [sp, #16]
  ldr x2, [sp, #368]
  add x0, x1, x2
  str x0, [sp, #16]
.L78:
  b .L53
.L79:
  mov x0, #1
  str x0, [sp, #32]
.L80:
  movz x0, #51168
  movk x0, #37, lsl #16
  str x0, [sp, #376]
.L81:
  ldr x1, [sp, #32]
  ldr x2, [sp, #376]
  cmp x1, x2
  b.gt .L148
.L82:
  mov x0, #1
  str x0, [sp, #16]
.L83:
  mov x0, #101
  str x0, [sp, #384]
.L84:
  ldr x1, [sp, #16]
  ldr x2, [sp, #384]
  cmp x1, x2
  b.gt .L101
.L85:
  mov x0, #1
  str x0, [sp, #8]
.L86:
  mov x0, #25
  str x0, [sp, #392]
.L87:
  ldr x1, [sp, #8]
  ldr x2, [sp, #392]
  cmp x1, x2
  b.gt .L98
.L88:
  mov x0, #1
  str x0, [sp, #400]
.L89:
  ldr x1, [sp, #16]
  ldr x2, [sp, #400]
  sub x0, x1, x2
  str x0, [sp, #408]
.L90:
  mov x0, #25
  str x0, [sp, #416]
.L91:
  ldr x1, [sp, #408]
  ldr x2, [sp, #416]
  mul x0, x1, x2
  str x0, [sp, #424]
.L92:
  ldr x1, [sp, #424]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #432]
.L93:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #440]
.L94:
  ldr x1, [sp, #432]
  ldr d0, [sp, #440]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L95:
  mov x0, #1
  str x0, [sp, #448]
.L96:
  ldr x1, [sp, #8]
  ldr x2, [sp, #448]
  add x0, x1, x2
  str x0, [sp, #8]
.L97:
  b .L86
.L98:
  mov x0, #1
  str x0, [sp, #456]
.L99:
  ldr x1, [sp, #16]
  ldr x2, [sp, #456]
  add x0, x1, x2
  str x0, [sp, #16]
.L100:
  b .L83
.L101:
  mov x0, #1
  str x0, [sp, #24]
.L102:
  mov x0, #25
  str x0, [sp, #464]
.L103:
  ldr x1, [sp, #24]
  ldr x2, [sp, #464]
  cmp x1, x2
  b.gt .L145
.L104:
  mov x0, #1
  str x0, [sp, #8]
.L105:
  mov x0, #25
  str x0, [sp, #472]
.L106:
  ldr x1, [sp, #8]
  ldr x2, [sp, #472]
  cmp x1, x2
  b.gt .L142
.L107:
  mov x0, #1
  str x0, [sp, #16]
.L108:
  mov x0, #101
  str x0, [sp, #480]
.L109:
  ldr x1, [sp, #16]
  ldr x2, [sp, #480]
  cmp x1, x2
  b.gt .L139
.L110:
  mov x0, #1
  str x0, [sp, #488]
.L111:
  ldr x1, [sp, #16]
  ldr x2, [sp, #488]
  sub x0, x1, x2
  str x0, [sp, #496]
.L112:
  mov x0, #25
  str x0, [sp, #504]
.L113:
  ldr x1, [sp, #496]
  ldr x2, [sp, #504]
  mul x0, x1, x2
  str x0, [sp, #512]
.L114:
  ldr x1, [sp, #512]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #520]
.L115:
  mov x0, #1
  str x0, [sp, #528]
.L116:
  ldr x1, [sp, #16]
  ldr x2, [sp, #528]
  sub x0, x1, x2
  str x0, [sp, #536]
.L117:
  mov x0, #25
  str x0, [sp, #544]
.L118:
  ldr x1, [sp, #536]
  ldr x2, [sp, #544]
  mul x0, x1, x2
  str x0, [sp, #552]
.L119:
  ldr x1, [sp, #552]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #560]
.L120:
  ldr x1, [sp, #560]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #568]
.L121:
  mov x0, #1
  str x0, [sp, #576]
.L122:
  ldr x1, [sp, #8]
  ldr x2, [sp, #576]
  sub x0, x1, x2
  str x0, [sp, #584]
.L123:
  mov x0, #101
  str x0, [sp, #592]
.L124:
  ldr x1, [sp, #584]
  ldr x2, [sp, #592]
  mul x0, x1, x2
  str x0, [sp, #600]
.L125:
  ldr x1, [sp, #600]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #608]
.L126:
  ldr x1, [sp, #608]
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #616]
.L127:
  mov x0, #1
  str x0, [sp, #624]
.L128:
  ldr x1, [sp, #16]
  ldr x2, [sp, #624]
  sub x0, x1, x2
  str x0, [sp, #632]
.L129:
  mov x0, #25
  str x0, [sp, #640]
.L130:
  ldr x1, [sp, #632]
  ldr x2, [sp, #640]
  mul x0, x1, x2
  str x0, [sp, #648]
.L131:
  ldr x1, [sp, #648]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #656]
.L132:
  ldr x1, [sp, #656]
  adrp x0, _arr_cx@PAGE
  add x0, x0, _arr_cx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #664]
.L133:
  ldr d1, [sp, #616]
  ldr d2, [sp, #664]
  fmul d0, d1, d2
  str d0, [sp, #672]
.L134:
  ldr d1, [sp, #568]
  ldr d2, [sp, #672]
  fadd d0, d1, d2
  str d0, [sp, #680]
.L135:
  ldr x1, [sp, #520]
  ldr d0, [sp, #680]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L136:
  mov x0, #1
  str x0, [sp, #688]
.L137:
  ldr x1, [sp, #16]
  ldr x2, [sp, #688]
  add x0, x1, x2
  str x0, [sp, #16]
.L138:
  b .L108
.L139:
  mov x0, #1
  str x0, [sp, #696]
.L140:
  ldr x1, [sp, #8]
  ldr x2, [sp, #696]
  add x0, x1, x2
  str x0, [sp, #8]
.L141:
  b .L105
.L142:
  mov x0, #1
  str x0, [sp, #704]
.L143:
  ldr x1, [sp, #24]
  ldr x2, [sp, #704]
  add x0, x1, x2
  str x0, [sp, #24]
.L144:
  b .L102
.L145:
  mov x0, #1
  str x0, [sp, #712]
.L146:
  ldr x1, [sp, #32]
  ldr x2, [sp, #712]
  add x0, x1, x2
  str x0, [sp, #32]
.L147:
  b .L80
.L148:
  mov x0, #51
  str x0, [sp, #720]
.L149:
  mov x0, #1
  str x0, [sp, #728]
.L150:
  ldr x1, [sp, #720]
  ldr x2, [sp, #728]
  sub x0, x1, x2
  str x0, [sp, #736]
.L151:
  mov x0, #25
  str x0, [sp, #744]
.L152:
  ldr x1, [sp, #736]
  ldr x2, [sp, #744]
  mul x0, x1, x2
  str x0, [sp, #752]
.L153:
  mov x0, #13
  str x0, [sp, #760]
.L154:
  ldr x1, [sp, #752]
  ldr x2, [sp, #760]
  add x0, x1, x2
  str x0, [sp, #768]
.L155:
  ldr x1, [sp, #768]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #776]
.L156:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #776]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_156@PAGE
  add x0, x0, .Lfmt_print_156@PAGEOFF
  bl _printf
  add sp, sp, #16
.L157:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #8]
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
  ldr x9, [sp, #16]
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
  ldr x9, [sp, #24]
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
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #40]
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
  ldr d0, [sp, #48]
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
  ldr d0, [sp, #56]
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
  ldr x29, [sp, #784]
  ldr x30, [sp, #792]
  add sp, sp, #800
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

.Lfmt_print_156:
  .asciz "%f\n"

.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_px
.align 3
_arr_px:
  .space 20208
.global _arr_cx
.align 3
_arr_cx:
  .space 20208
.global _arr_vy
.align 3
_arr_vy:
  .space 20208
