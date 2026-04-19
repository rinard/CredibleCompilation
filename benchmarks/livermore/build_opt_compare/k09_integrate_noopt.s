.global _main
.align 2

_main:
  sub sp, sp, #1344
  str x30, [sp, #1336]
  str x29, [sp, #1328]
  add x29, sp, #1328

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
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #64]
.L8:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #72]
.L9:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #80]
.L10:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #88]
.L11:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #96]
.L12:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #104]
.L13:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #112]
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
  fmov d0, x0
  str d0, [sp, #120]
.L16:
  ldr d1, [sp, #120]
  ldr d2, [sp, #96]
  fadd d0, d1, d2
  str d0, [sp, #104]
.L17:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #128]
.L18:
  ldr d1, [sp, #128]
  ldr d2, [sp, #96]
  fmul d0, d1, d2
  str d0, [sp, #112]
.L19:
  mov x0, #1
  str x0, [sp, #8]
.L20:
  mov x0, #39
  str x0, [sp, #136]
.L21:
  ldr x1, [sp, #8]
  ldr x2, [sp, #136]
  cmp x1, x2
  b.gt .L35
.L22:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #144]
.L23:
  ldr d1, [sp, #144]
  ldr d2, [sp, #96]
  fsub d0, d1, d2
  str d0, [sp, #152]
.L24:
  ldr d1, [sp, #152]
  ldr d2, [sp, #104]
  fmul d0, d1, d2
  str d0, [sp, #160]
.L25:
  ldr d1, [sp, #160]
  ldr d2, [sp, #96]
  fadd d0, d1, d2
  str d0, [sp, #104]
.L26:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #168]
.L27:
  ldr d1, [sp, #168]
  ldr d2, [sp, #96]
  fsub d0, d1, d2
  str d0, [sp, #96]
.L28:
  ldr d1, [sp, #104]
  ldr d2, [sp, #112]
  fsub d0, d1, d2
  str d0, [sp, #176]
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #184]
.L30:
  ldr d1, [sp, #176]
  ldr d2, [sp, #184]
  fmul d0, d1, d2
  str d0, [sp, #192]
.L31:
  ldr x1, [sp, #8]
  ldr d0, [sp, #192]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L32:
  mov x0, #1
  str x0, [sp, #200]
.L33:
  ldr x1, [sp, #8]
  ldr x2, [sp, #200]
  add x0, x1, x2
  str x0, [sp, #8]
.L34:
  b .L20
.L35:
  mov x0, #16
  str x0, [sp, #208]
.L36:
  ldr x1, [sp, #208]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #216]
.L37:
  ldr x0, [sp, #216]
  str x0, [sp, #80]
.L38:
  mov x0, #17
  str x0, [sp, #224]
.L39:
  ldr x1, [sp, #224]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #232]
.L40:
  ldr x0, [sp, #232]
  str x0, [sp, #72]
.L41:
  mov x0, #18
  str x0, [sp, #240]
.L42:
  ldr x1, [sp, #240]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #248]
.L43:
  ldr x0, [sp, #248]
  str x0, [sp, #64]
.L44:
  mov x0, #19
  str x0, [sp, #256]
.L45:
  ldr x1, [sp, #256]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #264]
.L46:
  ldr x0, [sp, #264]
  str x0, [sp, #56]
.L47:
  mov x0, #20
  str x0, [sp, #272]
.L48:
  ldr x1, [sp, #272]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #280]
.L49:
  ldr x0, [sp, #280]
  str x0, [sp, #48]
.L50:
  mov x0, #21
  str x0, [sp, #288]
.L51:
  ldr x1, [sp, #288]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #296]
.L52:
  ldr x0, [sp, #296]
  str x0, [sp, #40]
.L53:
  mov x0, #22
  str x0, [sp, #304]
.L54:
  ldr x1, [sp, #304]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #312]
.L55:
  ldr x0, [sp, #312]
  str x0, [sp, #32]
.L56:
  mov x0, #12
  str x0, [sp, #320]
.L57:
  ldr x1, [sp, #320]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #328]
.L58:
  ldr x0, [sp, #328]
  str x0, [sp, #88]
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
  fmov d0, x0
  str d0, [sp, #336]
.L61:
  ldr d1, [sp, #336]
  ldr d2, [sp, #96]
  fadd d0, d1, d2
  str d0, [sp, #104]
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #344]
.L63:
  ldr d1, [sp, #344]
  ldr d2, [sp, #96]
  fmul d0, d1, d2
  str d0, [sp, #112]
.L64:
  mov x0, #1
  str x0, [sp, #16]
.L65:
  mov x0, #25
  str x0, [sp, #352]
.L66:
  ldr x1, [sp, #16]
  ldr x2, [sp, #352]
  cmp x1, x2
  b.gt .L91
.L67:
  mov x0, #1
  str x0, [sp, #8]
.L68:
  mov x0, #101
  str x0, [sp, #360]
.L69:
  ldr x1, [sp, #8]
  ldr x2, [sp, #360]
  cmp x1, x2
  b.gt .L88
.L70:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #368]
.L71:
  ldr d1, [sp, #368]
  ldr d2, [sp, #96]
  fsub d0, d1, d2
  str d0, [sp, #376]
.L72:
  ldr d1, [sp, #376]
  ldr d2, [sp, #104]
  fmul d0, d1, d2
  str d0, [sp, #384]
.L73:
  ldr d1, [sp, #384]
  ldr d2, [sp, #96]
  fadd d0, d1, d2
  str d0, [sp, #104]
.L74:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #392]
.L75:
  ldr d1, [sp, #392]
  ldr d2, [sp, #96]
  fsub d0, d1, d2
  str d0, [sp, #96]
.L76:
  mov x0, #1
  str x0, [sp, #400]
.L77:
  ldr x1, [sp, #16]
  ldr x2, [sp, #400]
  sub x0, x1, x2
  str x0, [sp, #408]
.L78:
  mov x0, #101
  str x0, [sp, #416]
.L79:
  ldr x1, [sp, #408]
  ldr x2, [sp, #416]
  mul x0, x1, x2
  str x0, [sp, #424]
.L80:
  ldr x1, [sp, #424]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #432]
.L81:
  ldr d1, [sp, #104]
  ldr d2, [sp, #112]
  fsub d0, d1, d2
  str d0, [sp, #440]
.L82:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #448]
.L83:
  ldr d1, [sp, #440]
  ldr d2, [sp, #448]
  fmul d0, d1, d2
  str d0, [sp, #456]
.L84:
  ldr x1, [sp, #432]
  ldr d0, [sp, #456]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L85:
  mov x0, #1
  str x0, [sp, #464]
.L86:
  ldr x1, [sp, #8]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #8]
.L87:
  b .L68
.L88:
  mov x0, #1
  str x0, [sp, #472]
.L89:
  ldr x1, [sp, #16]
  ldr x2, [sp, #472]
  add x0, x1, x2
  str x0, [sp, #16]
.L90:
  b .L65
.L91:
  mov x0, #1
  str x0, [sp, #24]
.L92:
  movz x0, #18200
  movk x0, #925, lsl #16
  str x0, [sp, #480]
.L93:
  ldr x1, [sp, #24]
  ldr x2, [sp, #480]
  cmp x1, x2
  b.gt .L197
.L94:
  mov x0, #1
  str x0, [sp, #8]
.L95:
  mov x0, #101
  str x0, [sp, #488]
.L96:
  ldr x1, [sp, #8]
  ldr x2, [sp, #488]
  cmp x1, x2
  b.gt .L194
.L97:
  mov x0, #1
  str x0, [sp, #496]
.L98:
  mov x0, #1
  str x0, [sp, #504]
.L99:
  ldr x1, [sp, #496]
  ldr x2, [sp, #504]
  sub x0, x1, x2
  str x0, [sp, #512]
.L100:
  mov x0, #101
  str x0, [sp, #520]
.L101:
  ldr x1, [sp, #512]
  ldr x2, [sp, #520]
  mul x0, x1, x2
  str x0, [sp, #528]
.L102:
  ldr x1, [sp, #528]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #536]
.L103:
  mov x0, #13
  str x0, [sp, #544]
.L104:
  mov x0, #1
  str x0, [sp, #552]
.L105:
  ldr x1, [sp, #544]
  ldr x2, [sp, #552]
  sub x0, x1, x2
  str x0, [sp, #560]
.L106:
  mov x0, #101
  str x0, [sp, #568]
.L107:
  ldr x1, [sp, #560]
  ldr x2, [sp, #568]
  mul x0, x1, x2
  str x0, [sp, #576]
.L108:
  ldr x1, [sp, #576]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #584]
.L109:
  ldr x1, [sp, #584]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #592]
.L110:
  ldr d1, [sp, #32]
  ldr d2, [sp, #592]
  fmul d0, d1, d2
  str d0, [sp, #600]
.L111:
  mov x0, #12
  str x0, [sp, #608]
.L112:
  mov x0, #1
  str x0, [sp, #616]
.L113:
  ldr x1, [sp, #608]
  ldr x2, [sp, #616]
  sub x0, x1, x2
  str x0, [sp, #624]
.L114:
  mov x0, #101
  str x0, [sp, #632]
.L115:
  ldr x1, [sp, #624]
  ldr x2, [sp, #632]
  mul x0, x1, x2
  str x0, [sp, #640]
.L116:
  ldr x1, [sp, #640]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #648]
.L117:
  ldr x1, [sp, #648]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #656]
.L118:
  ldr d1, [sp, #40]
  ldr d2, [sp, #656]
  fmul d0, d1, d2
  str d0, [sp, #664]
.L119:
  ldr d1, [sp, #600]
  ldr d2, [sp, #664]
  fadd d0, d1, d2
  str d0, [sp, #672]
.L120:
  mov x0, #11
  str x0, [sp, #680]
.L121:
  mov x0, #1
  str x0, [sp, #688]
.L122:
  ldr x1, [sp, #680]
  ldr x2, [sp, #688]
  sub x0, x1, x2
  str x0, [sp, #696]
.L123:
  mov x0, #101
  str x0, [sp, #704]
.L124:
  ldr x1, [sp, #696]
  ldr x2, [sp, #704]
  mul x0, x1, x2
  str x0, [sp, #712]
.L125:
  ldr x1, [sp, #712]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #720]
.L126:
  ldr x1, [sp, #720]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #728]
.L127:
  ldr d1, [sp, #48]
  ldr d2, [sp, #728]
  fmul d0, d1, d2
  str d0, [sp, #736]
.L128:
  ldr d1, [sp, #672]
  ldr d2, [sp, #736]
  fadd d0, d1, d2
  str d0, [sp, #744]
.L129:
  mov x0, #10
  str x0, [sp, #752]
.L130:
  mov x0, #1
  str x0, [sp, #760]
.L131:
  ldr x1, [sp, #752]
  ldr x2, [sp, #760]
  sub x0, x1, x2
  str x0, [sp, #768]
.L132:
  mov x0, #101
  str x0, [sp, #776]
.L133:
  ldr x1, [sp, #768]
  ldr x2, [sp, #776]
  mul x0, x1, x2
  str x0, [sp, #784]
.L134:
  ldr x1, [sp, #784]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #792]
.L135:
  ldr x1, [sp, #792]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #800]
.L136:
  ldr d1, [sp, #56]
  ldr d2, [sp, #800]
  fmul d0, d1, d2
  str d0, [sp, #808]
.L137:
  ldr d1, [sp, #744]
  ldr d2, [sp, #808]
  fadd d0, d1, d2
  str d0, [sp, #816]
.L138:
  mov x0, #9
  str x0, [sp, #824]
.L139:
  mov x0, #1
  str x0, [sp, #832]
.L140:
  ldr x1, [sp, #824]
  ldr x2, [sp, #832]
  sub x0, x1, x2
  str x0, [sp, #840]
.L141:
  mov x0, #101
  str x0, [sp, #848]
.L142:
  ldr x1, [sp, #840]
  ldr x2, [sp, #848]
  mul x0, x1, x2
  str x0, [sp, #856]
.L143:
  ldr x1, [sp, #856]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #864]
.L144:
  ldr x1, [sp, #864]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #872]
.L145:
  ldr d1, [sp, #64]
  ldr d2, [sp, #872]
  fmul d0, d1, d2
  str d0, [sp, #880]
.L146:
  ldr d1, [sp, #816]
  ldr d2, [sp, #880]
  fadd d0, d1, d2
  str d0, [sp, #888]
.L147:
  mov x0, #8
  str x0, [sp, #896]
.L148:
  mov x0, #1
  str x0, [sp, #904]
.L149:
  ldr x1, [sp, #896]
  ldr x2, [sp, #904]
  sub x0, x1, x2
  str x0, [sp, #912]
.L150:
  mov x0, #101
  str x0, [sp, #920]
.L151:
  ldr x1, [sp, #912]
  ldr x2, [sp, #920]
  mul x0, x1, x2
  str x0, [sp, #928]
.L152:
  ldr x1, [sp, #928]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #936]
.L153:
  ldr x1, [sp, #936]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #944]
.L154:
  ldr d1, [sp, #72]
  ldr d2, [sp, #944]
  fmul d0, d1, d2
  str d0, [sp, #952]
.L155:
  ldr d1, [sp, #888]
  ldr d2, [sp, #952]
  fadd d0, d1, d2
  str d0, [sp, #960]
.L156:
  mov x0, #7
  str x0, [sp, #968]
.L157:
  mov x0, #1
  str x0, [sp, #976]
.L158:
  ldr x1, [sp, #968]
  ldr x2, [sp, #976]
  sub x0, x1, x2
  str x0, [sp, #984]
.L159:
  mov x0, #101
  str x0, [sp, #992]
.L160:
  ldr x1, [sp, #984]
  ldr x2, [sp, #992]
  mul x0, x1, x2
  str x0, [sp, #1000]
.L161:
  ldr x1, [sp, #1000]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1008]
.L162:
  ldr x1, [sp, #1008]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1016]
.L163:
  ldr d1, [sp, #80]
  ldr d2, [sp, #1016]
  fmul d0, d1, d2
  str d0, [sp, #1024]
.L164:
  ldr d1, [sp, #960]
  ldr d2, [sp, #1024]
  fadd d0, d1, d2
  str d0, [sp, #1032]
.L165:
  mov x0, #5
  str x0, [sp, #1040]
.L166:
  mov x0, #1
  str x0, [sp, #1048]
.L167:
  ldr x1, [sp, #1040]
  ldr x2, [sp, #1048]
  sub x0, x1, x2
  str x0, [sp, #1056]
.L168:
  mov x0, #101
  str x0, [sp, #1064]
.L169:
  ldr x1, [sp, #1056]
  ldr x2, [sp, #1064]
  mul x0, x1, x2
  str x0, [sp, #1072]
.L170:
  ldr x1, [sp, #1072]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1080]
.L171:
  ldr x1, [sp, #1080]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1088]
.L172:
  mov x0, #6
  str x0, [sp, #1096]
.L173:
  mov x0, #1
  str x0, [sp, #1104]
.L174:
  ldr x1, [sp, #1096]
  ldr x2, [sp, #1104]
  sub x0, x1, x2
  str x0, [sp, #1112]
.L175:
  mov x0, #101
  str x0, [sp, #1120]
.L176:
  ldr x1, [sp, #1112]
  ldr x2, [sp, #1120]
  mul x0, x1, x2
  str x0, [sp, #1128]
.L177:
  ldr x1, [sp, #1128]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1136]
.L178:
  ldr x1, [sp, #1136]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1144]
.L179:
  ldr d1, [sp, #1088]
  ldr d2, [sp, #1144]
  fadd d0, d1, d2
  str d0, [sp, #1152]
.L180:
  ldr d1, [sp, #88]
  ldr d2, [sp, #1152]
  fmul d0, d1, d2
  str d0, [sp, #1160]
.L181:
  ldr d1, [sp, #1032]
  ldr d2, [sp, #1160]
  fadd d0, d1, d2
  str d0, [sp, #1168]
.L182:
  mov x0, #3
  str x0, [sp, #1176]
.L183:
  mov x0, #1
  str x0, [sp, #1184]
.L184:
  ldr x1, [sp, #1176]
  ldr x2, [sp, #1184]
  sub x0, x1, x2
  str x0, [sp, #1192]
.L185:
  mov x0, #101
  str x0, [sp, #1200]
.L186:
  ldr x1, [sp, #1192]
  ldr x2, [sp, #1200]
  mul x0, x1, x2
  str x0, [sp, #1208]
.L187:
  ldr x1, [sp, #1208]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1216]
.L188:
  ldr x1, [sp, #1216]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1224]
.L189:
  ldr d1, [sp, #1168]
  ldr d2, [sp, #1224]
  fadd d0, d1, d2
  str d0, [sp, #1232]
.L190:
  ldr x1, [sp, #536]
  ldr d0, [sp, #1232]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L191:
  mov x0, #1
  str x0, [sp, #1240]
.L192:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1240]
  add x0, x1, x2
  str x0, [sp, #8]
.L193:
  b .L95
.L194:
  mov x0, #1
  str x0, [sp, #1248]
.L195:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1248]
  add x0, x1, x2
  str x0, [sp, #24]
.L196:
  b .L92
.L197:
  mov x0, #1
  str x0, [sp, #1256]
.L198:
  mov x0, #1
  str x0, [sp, #1264]
.L199:
  ldr x1, [sp, #1256]
  ldr x2, [sp, #1264]
  sub x0, x1, x2
  str x0, [sp, #1272]
.L200:
  mov x0, #101
  str x0, [sp, #1280]
.L201:
  ldr x1, [sp, #1272]
  ldr x2, [sp, #1280]
  mul x0, x1, x2
  str x0, [sp, #1288]
.L202:
  mov x0, #51
  str x0, [sp, #1296]
.L203:
  ldr x1, [sp, #1288]
  ldr x2, [sp, #1296]
  add x0, x1, x2
  str x0, [sp, #1304]
.L204:
  ldr x1, [sp, #1304]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1312]
.L205:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #1312]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_205@PAGE
  add x0, x0, .Lfmt_print_205@PAGEOFF
  bl _printf
  add sp, sp, #16
.L206:
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
  // print dm28 (float)
  ldr d0, [sp, #32]
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
  ldr d0, [sp, #40]
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
  ldr d0, [sp, #48]
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
  ldr d0, [sp, #56]
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
  ldr d0, [sp, #64]
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
  ldr d0, [sp, #72]
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
  ldr d0, [sp, #88]
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
  ldr d0, [sp, #104]
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
  ldr d0, [sp, #112]
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
  ldr x29, [sp, #1328]
  ldr x30, [sp, #1336]
  add sp, sp, #1344
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

.Lfmt_print_205:
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
