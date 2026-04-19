.global _main
.align 2

_main:
  sub sp, sp, #1456
  str x30, [sp, #1448]
  str x29, [sp, #1440]
  add x29, sp, #1440

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
  str x0, [sp, #1320]
  str x0, [sp, #1328]
  str x0, [sp, #1336]
  str x0, [sp, #1344]
  str x0, [sp, #1352]
  str x0, [sp, #1360]
  str x0, [sp, #1368]
  str x0, [sp, #1376]
  str x0, [sp, #1384]
  str x0, [sp, #1392]
  str x0, [sp, #1400]
  str x0, [sp, #1408]
  str x0, [sp, #1416]
  str x0, [sp, #1424]
  str x0, [sp, #1432]

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #24]
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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L11:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #88]
.L12:
  ldr d1, [sp, #88]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L13:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L14:
  ldr d1, [sp, #96]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L15:
  mov x0, #1
  str x0, [sp, #8]
.L16:
  mov x0, #39
  str x0, [sp, #104]
.L17:
  ldr x1, [sp, #8]
  ldr x2, [sp, #104]
  cmp x1, x2
  b.gt .L31
.L18:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #112]
.L19:
  ldr d1, [sp, #112]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #120]
.L20:
  ldr d1, [sp, #120]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #128]
.L21:
  ldr d1, [sp, #128]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L22:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #136]
.L23:
  ldr d1, [sp, #136]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L24:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #144]
.L25:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #152]
.L26:
  ldr d1, [sp, #144]
  ldr d2, [sp, #152]
  fmul d0, d1, d2
  str d0, [sp, #160]
.L27:
  ldr x1, [sp, #8]
  ldr d0, [sp, #160]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L28:
  mov x0, #1
  str x0, [sp, #168]
.L29:
  ldr x1, [sp, #8]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #8]
.L30:
  b .L16
.L31:
  mov x0, #15
  str x0, [sp, #176]
.L32:
  ldr x1, [sp, #176]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #184]
.L33:
  ldr x0, [sp, #184]
  str x0, [sp, #24]
.L34:
  mov x0, #32
  str x0, [sp, #192]
.L35:
  ldr x1, [sp, #192]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #200]
.L36:
  ldr x0, [sp, #200]
  str x0, [sp, #32]
.L37:
  mov x0, #36
  str x0, [sp, #208]
.L38:
  ldr x1, [sp, #208]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #216]
.L39:
  ldr x0, [sp, #216]
  str x0, [sp, #40]
.L40:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L41:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #224]
.L42:
  ldr d1, [sp, #224]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L43:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #232]
.L44:
  ldr d1, [sp, #232]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L45:
  mov x0, #1
  str x0, [sp, #8]
.L46:
  mov x0, #1001
  str x0, [sp, #240]
.L47:
  ldr x1, [sp, #8]
  ldr x2, [sp, #240]
  cmp x1, x2
  b.gt .L61
.L48:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #248]
.L49:
  ldr d1, [sp, #248]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #256]
.L50:
  ldr d1, [sp, #256]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #264]
.L51:
  ldr d1, [sp, #264]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L52:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #272]
.L53:
  ldr d1, [sp, #272]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L54:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #280]
.L55:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #288]
.L56:
  ldr d1, [sp, #280]
  ldr d2, [sp, #288]
  fmul d0, d1, d2
  str d0, [sp, #296]
.L57:
  ldr x1, [sp, #8]
  ldr d0, [sp, #296]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L58:
  mov x0, #1
  str x0, [sp, #304]
.L59:
  ldr x1, [sp, #8]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #8]
.L60:
  b .L46
.L61:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L62:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #312]
.L63:
  ldr d1, [sp, #312]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L64:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #320]
.L65:
  ldr d1, [sp, #320]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L66:
  mov x0, #1
  str x0, [sp, #8]
.L67:
  mov x0, #1001
  str x0, [sp, #328]
.L68:
  ldr x1, [sp, #8]
  ldr x2, [sp, #328]
  cmp x1, x2
  b.gt .L82
.L69:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #336]
.L70:
  ldr d1, [sp, #336]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #344]
.L71:
  ldr d1, [sp, #344]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #352]
.L72:
  ldr d1, [sp, #352]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L73:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #360]
.L74:
  ldr d1, [sp, #360]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L75:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #368]
.L76:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #376]
.L77:
  ldr d1, [sp, #368]
  ldr d2, [sp, #376]
  fmul d0, d1, d2
  str d0, [sp, #384]
.L78:
  ldr x1, [sp, #8]
  ldr d0, [sp, #384]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L79:
  mov x0, #1
  str x0, [sp, #392]
.L80:
  ldr x1, [sp, #8]
  ldr x2, [sp, #392]
  add x0, x1, x2
  str x0, [sp, #8]
.L81:
  b .L67
.L82:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L83:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #400]
.L84:
  ldr d1, [sp, #400]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L85:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #408]
.L86:
  ldr d1, [sp, #408]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L87:
  mov x0, #1
  str x0, [sp, #8]
.L88:
  mov x0, #1001
  str x0, [sp, #416]
.L89:
  ldr x1, [sp, #8]
  ldr x2, [sp, #416]
  cmp x1, x2
  b.gt .L103
.L90:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #424]
.L91:
  ldr d1, [sp, #424]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #432]
.L92:
  ldr d1, [sp, #432]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #440]
.L93:
  ldr d1, [sp, #440]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L94:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #448]
.L95:
  ldr d1, [sp, #448]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L96:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #456]
.L97:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #464]
.L98:
  ldr d1, [sp, #456]
  ldr d2, [sp, #464]
  fmul d0, d1, d2
  str d0, [sp, #472]
.L99:
  ldr x1, [sp, #8]
  ldr d0, [sp, #472]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L100:
  mov x0, #1
  str x0, [sp, #480]
.L101:
  ldr x1, [sp, #8]
  ldr x2, [sp, #480]
  add x0, x1, x2
  str x0, [sp, #8]
.L102:
  b .L88
.L103:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L104:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #488]
.L105:
  ldr d1, [sp, #488]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L106:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #496]
.L107:
  ldr d1, [sp, #496]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L108:
  mov x0, #1
  str x0, [sp, #8]
.L109:
  mov x0, #1001
  str x0, [sp, #504]
.L110:
  ldr x1, [sp, #8]
  ldr x2, [sp, #504]
  cmp x1, x2
  b.gt .L124
.L111:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #512]
.L112:
  ldr d1, [sp, #512]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #520]
.L113:
  ldr d1, [sp, #520]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #528]
.L114:
  ldr d1, [sp, #528]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L115:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #536]
.L116:
  ldr d1, [sp, #536]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L117:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #544]
.L118:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #552]
.L119:
  ldr d1, [sp, #544]
  ldr d2, [sp, #552]
  fmul d0, d1, d2
  str d0, [sp, #560]
.L120:
  ldr x1, [sp, #8]
  ldr d0, [sp, #560]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L121:
  mov x0, #1
  str x0, [sp, #568]
.L122:
  ldr x1, [sp, #8]
  ldr x2, [sp, #568]
  add x0, x1, x2
  str x0, [sp, #8]
.L123:
  b .L109
.L124:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L125:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #576]
.L126:
  ldr d1, [sp, #576]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L127:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #584]
.L128:
  ldr d1, [sp, #584]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L129:
  mov x0, #1
  str x0, [sp, #8]
.L130:
  mov x0, #1001
  str x0, [sp, #592]
.L131:
  ldr x1, [sp, #8]
  ldr x2, [sp, #592]
  cmp x1, x2
  b.gt .L145
.L132:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #600]
.L133:
  ldr d1, [sp, #600]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #608]
.L134:
  ldr d1, [sp, #608]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #616]
.L135:
  ldr d1, [sp, #616]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L136:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #624]
.L137:
  ldr d1, [sp, #624]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L138:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #632]
.L139:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #640]
.L140:
  ldr d1, [sp, #632]
  ldr d2, [sp, #640]
  fmul d0, d1, d2
  str d0, [sp, #648]
.L141:
  ldr x1, [sp, #8]
  ldr d0, [sp, #648]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L142:
  mov x0, #1
  str x0, [sp, #656]
.L143:
  ldr x1, [sp, #8]
  ldr x2, [sp, #656]
  add x0, x1, x2
  str x0, [sp, #8]
.L144:
  b .L130
.L145:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L146:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #664]
.L147:
  ldr d1, [sp, #664]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L148:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #672]
.L149:
  ldr d1, [sp, #672]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L150:
  mov x0, #1
  str x0, [sp, #8]
.L151:
  mov x0, #1001
  str x0, [sp, #680]
.L152:
  ldr x1, [sp, #8]
  ldr x2, [sp, #680]
  cmp x1, x2
  b.gt .L166
.L153:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #688]
.L154:
  ldr d1, [sp, #688]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #696]
.L155:
  ldr d1, [sp, #696]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #704]
.L156:
  ldr d1, [sp, #704]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L157:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #712]
.L158:
  ldr d1, [sp, #712]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L159:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #720]
.L160:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #728]
.L161:
  ldr d1, [sp, #720]
  ldr d2, [sp, #728]
  fmul d0, d1, d2
  str d0, [sp, #736]
.L162:
  ldr x1, [sp, #8]
  ldr d0, [sp, #736]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L163:
  mov x0, #1
  str x0, [sp, #744]
.L164:
  ldr x1, [sp, #8]
  ldr x2, [sp, #744]
  add x0, x1, x2
  str x0, [sp, #8]
.L165:
  b .L151
.L166:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L167:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #752]
.L168:
  ldr d1, [sp, #752]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L169:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #760]
.L170:
  ldr d1, [sp, #760]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L171:
  mov x0, #1
  str x0, [sp, #8]
.L172:
  mov x0, #1001
  str x0, [sp, #768]
.L173:
  ldr x1, [sp, #8]
  ldr x2, [sp, #768]
  cmp x1, x2
  b.gt .L187
.L174:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #776]
.L175:
  ldr d1, [sp, #776]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #784]
.L176:
  ldr d1, [sp, #784]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #792]
.L177:
  ldr d1, [sp, #792]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L178:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #800]
.L179:
  ldr d1, [sp, #800]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L180:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #808]
.L181:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #816]
.L182:
  ldr d1, [sp, #808]
  ldr d2, [sp, #816]
  fmul d0, d1, d2
  str d0, [sp, #824]
.L183:
  ldr x1, [sp, #8]
  ldr d0, [sp, #824]
  adrp x0, _arr_g@PAGE
  add x0, x0, _arr_g@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L184:
  mov x0, #1
  str x0, [sp, #832]
.L185:
  ldr x1, [sp, #8]
  ldr x2, [sp, #832]
  add x0, x1, x2
  str x0, [sp, #8]
.L186:
  b .L172
.L187:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L188:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #840]
.L189:
  ldr d1, [sp, #840]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L190:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #848]
.L191:
  ldr d1, [sp, #848]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L192:
  mov x0, #1
  str x0, [sp, #8]
.L193:
  mov x0, #1001
  str x0, [sp, #856]
.L194:
  ldr x1, [sp, #8]
  ldr x2, [sp, #856]
  cmp x1, x2
  b.gt .L210
.L195:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #864]
.L196:
  ldr d1, [sp, #864]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #872]
.L197:
  ldr d1, [sp, #872]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #880]
.L198:
  ldr d1, [sp, #880]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L199:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #888]
.L200:
  ldr d1, [sp, #888]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L201:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #896]
.L202:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #904]
.L203:
  ldr d1, [sp, #896]
  ldr d2, [sp, #904]
  fmul d0, d1, d2
  str d0, [sp, #912]
.L204:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #920]
.L205:
  ldr d1, [sp, #912]
  ldr d2, [sp, #920]
  fadd d0, d1, d2
  str d0, [sp, #928]
.L206:
  ldr x1, [sp, #8]
  ldr d0, [sp, #928]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L207:
  mov x0, #1
  str x0, [sp, #936]
.L208:
  ldr x1, [sp, #8]
  ldr x2, [sp, #936]
  add x0, x1, x2
  str x0, [sp, #8]
.L209:
  b .L193
.L210:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L211:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #944]
.L212:
  ldr d1, [sp, #944]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L213:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #952]
.L214:
  ldr d1, [sp, #952]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L215:
  mov x0, #1
  str x0, [sp, #8]
.L216:
  mov x0, #1001
  str x0, [sp, #960]
.L217:
  ldr x1, [sp, #8]
  ldr x2, [sp, #960]
  cmp x1, x2
  b.gt .L233
.L218:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #968]
.L219:
  ldr d1, [sp, #968]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #976]
.L220:
  ldr d1, [sp, #976]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #984]
.L221:
  ldr d1, [sp, #984]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L222:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #992]
.L223:
  ldr d1, [sp, #992]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L224:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #1000]
.L225:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #1008]
.L226:
  ldr d1, [sp, #1000]
  ldr d2, [sp, #1008]
  fmul d0, d1, d2
  str d0, [sp, #1016]
.L227:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d0, x0
  str d0, [sp, #1024]
.L228:
  ldr d1, [sp, #1016]
  ldr d2, [sp, #1024]
  fadd d0, d1, d2
  str d0, [sp, #1032]
.L229:
  ldr x1, [sp, #8]
  ldr d0, [sp, #1032]
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L230:
  mov x0, #1
  str x0, [sp, #1040]
.L231:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1040]
  add x0, x1, x2
  str x0, [sp, #8]
.L232:
  b .L216
.L233:
  mov x0, #1
  str x0, [sp, #16]
.L234:
  movz x0, #62672
  movk x0, #23, lsl #16
  str x0, [sp, #1048]
.L235:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1048]
  cmp x1, x2
  b.gt .L320
.L236:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L237:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #1056]
.L238:
  ldr d1, [sp, #1056]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L239:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #1064]
.L240:
  ldr d1, [sp, #1064]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #80]
.L241:
  mov x0, #1
  str x0, [sp, #8]
.L242:
  mov x0, #1001
  str x0, [sp, #1072]
.L243:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1072]
  cmp x1, x2
  b.gt .L259
.L244:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #1080]
.L245:
  ldr d1, [sp, #1080]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #1088]
.L246:
  ldr d1, [sp, #1088]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #1096]
.L247:
  ldr d1, [sp, #1096]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L248:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #1104]
.L249:
  ldr d1, [sp, #1104]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #64]
.L250:
  ldr d1, [sp, #72]
  ldr d2, [sp, #80]
  fsub d0, d1, d2
  str d0, [sp, #1112]
.L251:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #1120]
.L252:
  ldr d1, [sp, #1112]
  ldr d2, [sp, #1120]
  fmul d0, d1, d2
  str d0, [sp, #1128]
.L253:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #1136]
.L254:
  ldr d1, [sp, #1128]
  ldr d2, [sp, #1136]
  fadd d0, d1, d2
  str d0, [sp, #1144]
.L255:
  ldr x1, [sp, #8]
  ldr d0, [sp, #1144]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L256:
  mov x0, #1
  str x0, [sp, #1152]
.L257:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1152]
  add x0, x1, x2
  str x0, [sp, #8]
.L258:
  b .L242
.L259:
  mov x0, #1
  str x0, [sp, #8]
.L260:
  mov x0, #1000
  str x0, [sp, #1160]
.L261:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1160]
  cmp x1, x2
  b.gt .L317
.L262:
  ldr x1, [sp, #8]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1168]
.L263:
  ldr x1, [sp, #8]
  adrp x0, _arr_g@PAGE
  add x0, x0, _arr_g@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1176]
.L264:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1184]
.L265:
  ldr d1, [sp, #1184]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #1192]
.L266:
  ldr d1, [sp, #1176]
  ldr d2, [sp, #1192]
  fdiv d0, d1, d2
  str d0, [sp, #1200]
.L267:
  ldr d1, [sp, #1168]
  ldr d2, [sp, #1200]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L268:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16329, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L269:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #1208]
.L270:
  ldr d1, [sp, #48]
  ldr d2, [sp, #1208]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L283
.L271:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #1216]
.L272:
  ldr d1, [sp, #1216]
  ldr d2, [sp, #48]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L274
.L273:
  b .L282
.L274:
  ldr x1, [sp, #8]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1224]
.L275:
  ldr d1, [sp, #1224]
  ldr d2, [sp, #48]
  fdiv d0, d1, d2
  str d0, [sp, #56]
.L276:
  ldr d1, [sp, #40]
  ldr d2, [sp, #56]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L278
.L277:
  b .L279
.L278:
  ldr x0, [sp, #40]
  str x0, [sp, #56]
.L279:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L281
.L280:
  b .L282
.L281:
  ldr x0, [sp, #32]
  str x0, [sp, #56]
.L282:
  b .L291
.L283:
  ldr x1, [sp, #8]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1232]
.L284:
  ldr d1, [sp, #1232]
  ldr d2, [sp, #48]
  fdiv d0, d1, d2
  str d0, [sp, #56]
.L285:
  ldr d1, [sp, #40]
  ldr d2, [sp, #56]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L287
.L286:
  b .L288
.L287:
  ldr x0, [sp, #40]
  str x0, [sp, #56]
.L288:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L290
.L289:
  b .L291
.L290:
  ldr x0, [sp, #32]
  str x0, [sp, #56]
.L291:
  ldr x1, [sp, #8]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1240]
.L292:
  ldr x1, [sp, #8]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1248]
.L293:
  ldr d1, [sp, #1248]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #1256]
.L294:
  ldr d1, [sp, #1240]
  ldr d2, [sp, #1256]
  fadd d0, d1, d2
  str d0, [sp, #1264]
.L295:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1272]
.L296:
  ldr d1, [sp, #1264]
  ldr d2, [sp, #1272]
  fmul d0, d1, d2
  str d0, [sp, #1280]
.L297:
  ldr x1, [sp, #8]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1288]
.L298:
  ldr d1, [sp, #1280]
  ldr d2, [sp, #1288]
  fadd d0, d1, d2
  str d0, [sp, #1296]
.L299:
  ldr x1, [sp, #8]
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1304]
.L300:
  ldr x1, [sp, #8]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1312]
.L301:
  ldr d1, [sp, #1312]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #1320]
.L302:
  ldr d1, [sp, #1304]
  ldr d2, [sp, #1320]
  fadd d0, d1, d2
  str d0, [sp, #1328]
.L303:
  ldr d1, [sp, #1296]
  ldr d2, [sp, #1328]
  fdiv d0, d1, d2
  str d0, [sp, #1336]
.L304:
  ldr x1, [sp, #8]
  ldr d0, [sp, #1336]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L305:
  mov x0, #1
  str x0, [sp, #1344]
.L306:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1344]
  add x0, x1, x2
  str x0, [sp, #1352]
.L307:
  ldr x1, [sp, #8]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1360]
.L308:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1368]
.L309:
  ldr d1, [sp, #1360]
  ldr d2, [sp, #1368]
  fsub d0, d1, d2
  str d0, [sp, #1376]
.L310:
  ldr d1, [sp, #1376]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #1384]
.L311:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1392]
.L312:
  ldr d1, [sp, #1384]
  ldr d2, [sp, #1392]
  fadd d0, d1, d2
  str d0, [sp, #1400]
.L313:
  ldr x1, [sp, #1352]
  ldr d0, [sp, #1400]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L314:
  mov x0, #1
  str x0, [sp, #1408]
.L315:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1408]
  add x0, x1, x2
  str x0, [sp, #8]
.L316:
  b .L260
.L317:
  mov x0, #1
  str x0, [sp, #1416]
.L318:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1416]
  add x0, x1, x2
  str x0, [sp, #16]
.L319:
  b .L234
.L320:
  mov x0, #1
  str x0, [sp, #1424]
.L321:
  ldr x1, [sp, #1424]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1432]
.L322:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #1432]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_322@PAGE
  add x0, x0, .Lfmt_print_322@PAGEOFF
  bl _printf
  add sp, sp, #16
.L323:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #8]
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
  // print dk (float)
  ldr d0, [sp, #24]
  sub sp, sp, #32
  adrp x1, .Lname_dk@PAGE
  add x1, x1, .Lname_dk@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print s (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x1, .Lname_s@PAGE
  add x1, x1, .Lname_s@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #40]
  sub sp, sp, #32
  adrp x1, .Lname_t@PAGE
  add x1, x1, .Lname_t@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print di (float)
  ldr d0, [sp, #48]
  sub sp, sp, #32
  adrp x1, .Lname_di@PAGE
  add x1, x1, .Lname_di@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print dn (float)
  ldr d0, [sp, #56]
  sub sp, sp, #32
  adrp x1, .Lname_dn@PAGE
  add x1, x1, .Lname_dn@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #64]
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
  ldr d0, [sp, #72]
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
  ldr d0, [sp, #80]
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

.Lfmt_print_322:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_dk:
  .asciz "dk"
.Lname_s:
  .asciz "s"
.Lname_t:
  .asciz "t"
.Lname_di:
  .asciz "di"
.Lname_dn:
  .asciz "dn"
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
.global _arr_x
.align 3
_arr_x:
  .space 8016
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_w
.align 3
_arr_w:
  .space 8016
.global _arr_v
.align 3
_arr_v:
  .space 8016
.global _arr_u
.align 3
_arr_u:
  .space 8016
.global _arr_g
.align 3
_arr_g:
  .space 8016
.global _arr_xx
.align 3
_arr_xx:
  .space 8016
.global _arr_vx
.align 3
_arr_vx:
  .space 8016
