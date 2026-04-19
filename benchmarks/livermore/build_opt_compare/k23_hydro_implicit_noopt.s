.global _main
.align 2

_main:
  sub sp, sp, #2176
  str x30, [sp, #2168]
  str x29, [sp, #2160]
  add x29, sp, #2160

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
  str x0, [sp, #1440]
  str x0, [sp, #1448]
  str x0, [sp, #1456]
  str x0, [sp, #1464]
  str x0, [sp, #1472]
  str x0, [sp, #1480]
  str x0, [sp, #1488]
  str x0, [sp, #1496]
  str x0, [sp, #1504]
  str x0, [sp, #1512]
  str x0, [sp, #1520]
  str x0, [sp, #1528]
  str x0, [sp, #1536]
  str x0, [sp, #1544]
  str x0, [sp, #1552]
  str x0, [sp, #1560]
  str x0, [sp, #1568]
  str x0, [sp, #1576]
  str x0, [sp, #1584]
  str x0, [sp, #1592]
  str x0, [sp, #1600]
  str x0, [sp, #1608]
  str x0, [sp, #1616]
  str x0, [sp, #1624]
  str x0, [sp, #1632]
  str x0, [sp, #1640]
  str x0, [sp, #1648]
  str x0, [sp, #1656]
  str x0, [sp, #1664]
  str x0, [sp, #1672]
  str x0, [sp, #1680]
  str x0, [sp, #1688]
  str x0, [sp, #1696]
  str x0, [sp, #1704]
  str x0, [sp, #1712]
  str x0, [sp, #1720]
  str x0, [sp, #1728]
  str x0, [sp, #1736]
  str x0, [sp, #1744]
  str x0, [sp, #1752]
  str x0, [sp, #1760]
  str x0, [sp, #1768]
  str x0, [sp, #1776]
  str x0, [sp, #1784]
  str x0, [sp, #1792]
  str x0, [sp, #1800]
  str x0, [sp, #1808]
  str x0, [sp, #1816]
  str x0, [sp, #1824]
  str x0, [sp, #1832]
  str x0, [sp, #1840]
  str x0, [sp, #1848]
  str x0, [sp, #1856]
  str x0, [sp, #1864]
  str x0, [sp, #1872]
  str x0, [sp, #1880]
  str x0, [sp, #1888]
  str x0, [sp, #1896]
  str x0, [sp, #1904]
  str x0, [sp, #1912]
  str x0, [sp, #1920]
  str x0, [sp, #1928]
  str x0, [sp, #1936]
  str x0, [sp, #1944]
  str x0, [sp, #1952]
  str x0, [sp, #1960]
  str x0, [sp, #1968]
  str x0, [sp, #1976]
  str x0, [sp, #1984]
  str x0, [sp, #1992]
  str x0, [sp, #2000]
  str x0, [sp, #2008]
  str x0, [sp, #2016]
  str x0, [sp, #2024]
  str x0, [sp, #2032]
  str x0, [sp, #2040]
  str x0, [sp, #2048]
  str x0, [sp, #2056]
  str x0, [sp, #2064]
  str x0, [sp, #2072]
  str x0, [sp, #2080]
  str x0, [sp, #2088]
  str x0, [sp, #2096]
  str x0, [sp, #2104]
  str x0, [sp, #2112]
  str x0, [sp, #2120]
  str x0, [sp, #2128]
  str x0, [sp, #2136]
  str x0, [sp, #2144]
  str x0, [sp, #2152]

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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L8:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L9:
  ldr d1, [sp, #64]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L10:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L11:
  ldr d1, [sp, #72]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L12:
  mov x0, #1
  str x0, [sp, #8]
.L13:
  mov x0, #7
  str x0, [sp, #80]
.L14:
  ldr x1, [sp, #8]
  ldr x2, [sp, #80]
  cmp x1, x2
  b.gt .L39
.L15:
  mov x0, #1
  str x0, [sp, #16]
.L16:
  mov x0, #101
  str x0, [sp, #88]
.L17:
  ldr x1, [sp, #16]
  ldr x2, [sp, #88]
  cmp x1, x2
  b.gt .L36
.L18:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L19:
  ldr d1, [sp, #96]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #104]
.L20:
  ldr d1, [sp, #104]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #112]
.L21:
  ldr d1, [sp, #112]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L22:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #120]
.L23:
  ldr d1, [sp, #120]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L24:
  mov x0, #1
  str x0, [sp, #128]
.L25:
  ldr x1, [sp, #8]
  ldr x2, [sp, #128]
  sub x0, x1, x2
  str x0, [sp, #136]
.L26:
  mov x0, #101
  str x0, [sp, #144]
.L27:
  ldr x1, [sp, #136]
  ldr x2, [sp, #144]
  mul x0, x1, x2
  str x0, [sp, #152]
.L28:
  ldr x1, [sp, #152]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #160]
.L29:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #168]
.L30:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #176]
.L31:
  ldr d1, [sp, #168]
  ldr d2, [sp, #176]
  fmul d0, d1, d2
  str d0, [sp, #184]
.L32:
  ldr x1, [sp, #160]
  ldr d0, [sp, #184]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L33:
  mov x0, #1
  str x0, [sp, #192]
.L34:
  ldr x1, [sp, #16]
  ldr x2, [sp, #192]
  add x0, x1, x2
  str x0, [sp, #16]
.L35:
  b .L16
.L36:
  mov x0, #1
  str x0, [sp, #200]
.L37:
  ldr x1, [sp, #8]
  ldr x2, [sp, #200]
  add x0, x1, x2
  str x0, [sp, #8]
.L38:
  b .L13
.L39:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L40:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #208]
.L41:
  ldr d1, [sp, #208]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L42:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #216]
.L43:
  ldr d1, [sp, #216]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L44:
  mov x0, #1
  str x0, [sp, #8]
.L45:
  mov x0, #7
  str x0, [sp, #224]
.L46:
  ldr x1, [sp, #8]
  ldr x2, [sp, #224]
  cmp x1, x2
  b.gt .L71
.L47:
  mov x0, #1
  str x0, [sp, #16]
.L48:
  mov x0, #101
  str x0, [sp, #232]
.L49:
  ldr x1, [sp, #16]
  ldr x2, [sp, #232]
  cmp x1, x2
  b.gt .L68
.L50:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #240]
.L51:
  ldr d1, [sp, #240]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #248]
.L52:
  ldr d1, [sp, #248]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #256]
.L53:
  ldr d1, [sp, #256]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L54:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #264]
.L55:
  ldr d1, [sp, #264]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L56:
  mov x0, #1
  str x0, [sp, #272]
.L57:
  ldr x1, [sp, #8]
  ldr x2, [sp, #272]
  sub x0, x1, x2
  str x0, [sp, #280]
.L58:
  mov x0, #101
  str x0, [sp, #288]
.L59:
  ldr x1, [sp, #280]
  ldr x2, [sp, #288]
  mul x0, x1, x2
  str x0, [sp, #296]
.L60:
  ldr x1, [sp, #296]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #304]
.L61:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #312]
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #320]
.L63:
  ldr d1, [sp, #312]
  ldr d2, [sp, #320]
  fmul d0, d1, d2
  str d0, [sp, #328]
.L64:
  ldr x1, [sp, #304]
  ldr d0, [sp, #328]
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L65:
  mov x0, #1
  str x0, [sp, #336]
.L66:
  ldr x1, [sp, #16]
  ldr x2, [sp, #336]
  add x0, x1, x2
  str x0, [sp, #16]
.L67:
  b .L48
.L68:
  mov x0, #1
  str x0, [sp, #344]
.L69:
  ldr x1, [sp, #8]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #8]
.L70:
  b .L45
.L71:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L72:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #352]
.L73:
  ldr d1, [sp, #352]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L74:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #360]
.L75:
  ldr d1, [sp, #360]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L76:
  mov x0, #1
  str x0, [sp, #8]
.L77:
  mov x0, #7
  str x0, [sp, #368]
.L78:
  ldr x1, [sp, #8]
  ldr x2, [sp, #368]
  cmp x1, x2
  b.gt .L103
.L79:
  mov x0, #1
  str x0, [sp, #16]
.L80:
  mov x0, #101
  str x0, [sp, #376]
.L81:
  ldr x1, [sp, #16]
  ldr x2, [sp, #376]
  cmp x1, x2
  b.gt .L100
.L82:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #384]
.L83:
  ldr d1, [sp, #384]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #392]
.L84:
  ldr d1, [sp, #392]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #400]
.L85:
  ldr d1, [sp, #400]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L86:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #408]
.L87:
  ldr d1, [sp, #408]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L88:
  mov x0, #1
  str x0, [sp, #416]
.L89:
  ldr x1, [sp, #8]
  ldr x2, [sp, #416]
  sub x0, x1, x2
  str x0, [sp, #424]
.L90:
  mov x0, #101
  str x0, [sp, #432]
.L91:
  ldr x1, [sp, #424]
  ldr x2, [sp, #432]
  mul x0, x1, x2
  str x0, [sp, #440]
.L92:
  ldr x1, [sp, #440]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #448]
.L93:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #456]
.L94:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #464]
.L95:
  ldr d1, [sp, #456]
  ldr d2, [sp, #464]
  fmul d0, d1, d2
  str d0, [sp, #472]
.L96:
  ldr x1, [sp, #448]
  ldr d0, [sp, #472]
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L97:
  mov x0, #1
  str x0, [sp, #480]
.L98:
  ldr x1, [sp, #16]
  ldr x2, [sp, #480]
  add x0, x1, x2
  str x0, [sp, #16]
.L99:
  b .L80
.L100:
  mov x0, #1
  str x0, [sp, #488]
.L101:
  ldr x1, [sp, #8]
  ldr x2, [sp, #488]
  add x0, x1, x2
  str x0, [sp, #8]
.L102:
  b .L77
.L103:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L104:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #496]
.L105:
  ldr d1, [sp, #496]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L106:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #504]
.L107:
  ldr d1, [sp, #504]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L108:
  mov x0, #1
  str x0, [sp, #8]
.L109:
  mov x0, #7
  str x0, [sp, #512]
.L110:
  ldr x1, [sp, #8]
  ldr x2, [sp, #512]
  cmp x1, x2
  b.gt .L135
.L111:
  mov x0, #1
  str x0, [sp, #16]
.L112:
  mov x0, #101
  str x0, [sp, #520]
.L113:
  ldr x1, [sp, #16]
  ldr x2, [sp, #520]
  cmp x1, x2
  b.gt .L132
.L114:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #528]
.L115:
  ldr d1, [sp, #528]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #536]
.L116:
  ldr d1, [sp, #536]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #544]
.L117:
  ldr d1, [sp, #544]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L118:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #552]
.L119:
  ldr d1, [sp, #552]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L120:
  mov x0, #1
  str x0, [sp, #560]
.L121:
  ldr x1, [sp, #8]
  ldr x2, [sp, #560]
  sub x0, x1, x2
  str x0, [sp, #568]
.L122:
  mov x0, #101
  str x0, [sp, #576]
.L123:
  ldr x1, [sp, #568]
  ldr x2, [sp, #576]
  mul x0, x1, x2
  str x0, [sp, #584]
.L124:
  ldr x1, [sp, #584]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #592]
.L125:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #600]
.L126:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #608]
.L127:
  ldr d1, [sp, #600]
  ldr d2, [sp, #608]
  fmul d0, d1, d2
  str d0, [sp, #616]
.L128:
  ldr x1, [sp, #592]
  ldr d0, [sp, #616]
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L129:
  mov x0, #1
  str x0, [sp, #624]
.L130:
  ldr x1, [sp, #16]
  ldr x2, [sp, #624]
  add x0, x1, x2
  str x0, [sp, #16]
.L131:
  b .L112
.L132:
  mov x0, #1
  str x0, [sp, #632]
.L133:
  ldr x1, [sp, #8]
  ldr x2, [sp, #632]
  add x0, x1, x2
  str x0, [sp, #8]
.L134:
  b .L109
.L135:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L136:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #640]
.L137:
  ldr d1, [sp, #640]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L138:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #648]
.L139:
  ldr d1, [sp, #648]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L140:
  mov x0, #1
  str x0, [sp, #8]
.L141:
  mov x0, #7
  str x0, [sp, #656]
.L142:
  ldr x1, [sp, #8]
  ldr x2, [sp, #656]
  cmp x1, x2
  b.gt .L167
.L143:
  mov x0, #1
  str x0, [sp, #16]
.L144:
  mov x0, #101
  str x0, [sp, #664]
.L145:
  ldr x1, [sp, #16]
  ldr x2, [sp, #664]
  cmp x1, x2
  b.gt .L164
.L146:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #672]
.L147:
  ldr d1, [sp, #672]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #680]
.L148:
  ldr d1, [sp, #680]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #688]
.L149:
  ldr d1, [sp, #688]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L150:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #696]
.L151:
  ldr d1, [sp, #696]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L152:
  mov x0, #1
  str x0, [sp, #704]
.L153:
  ldr x1, [sp, #8]
  ldr x2, [sp, #704]
  sub x0, x1, x2
  str x0, [sp, #712]
.L154:
  mov x0, #101
  str x0, [sp, #720]
.L155:
  ldr x1, [sp, #712]
  ldr x2, [sp, #720]
  mul x0, x1, x2
  str x0, [sp, #728]
.L156:
  ldr x1, [sp, #728]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #736]
.L157:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #744]
.L158:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #752]
.L159:
  ldr d1, [sp, #744]
  ldr d2, [sp, #752]
  fmul d0, d1, d2
  str d0, [sp, #760]
.L160:
  ldr x1, [sp, #736]
  ldr d0, [sp, #760]
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L161:
  mov x0, #1
  str x0, [sp, #768]
.L162:
  ldr x1, [sp, #16]
  ldr x2, [sp, #768]
  add x0, x1, x2
  str x0, [sp, #16]
.L163:
  b .L144
.L164:
  mov x0, #1
  str x0, [sp, #776]
.L165:
  ldr x1, [sp, #8]
  ldr x2, [sp, #776]
  add x0, x1, x2
  str x0, [sp, #8]
.L166:
  b .L141
.L167:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L168:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #784]
.L169:
  ldr d1, [sp, #784]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L170:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #792]
.L171:
  ldr d1, [sp, #792]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L172:
  mov x0, #1
  str x0, [sp, #8]
.L173:
  mov x0, #7
  str x0, [sp, #800]
.L174:
  ldr x1, [sp, #8]
  ldr x2, [sp, #800]
  cmp x1, x2
  b.gt .L199
.L175:
  mov x0, #1
  str x0, [sp, #16]
.L176:
  mov x0, #101
  str x0, [sp, #808]
.L177:
  ldr x1, [sp, #16]
  ldr x2, [sp, #808]
  cmp x1, x2
  b.gt .L196
.L178:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #816]
.L179:
  ldr d1, [sp, #816]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #824]
.L180:
  ldr d1, [sp, #824]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #832]
.L181:
  ldr d1, [sp, #832]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L182:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #840]
.L183:
  ldr d1, [sp, #840]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L184:
  mov x0, #1
  str x0, [sp, #848]
.L185:
  ldr x1, [sp, #8]
  ldr x2, [sp, #848]
  sub x0, x1, x2
  str x0, [sp, #856]
.L186:
  mov x0, #101
  str x0, [sp, #864]
.L187:
  ldr x1, [sp, #856]
  ldr x2, [sp, #864]
  mul x0, x1, x2
  str x0, [sp, #872]
.L188:
  ldr x1, [sp, #872]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #880]
.L189:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #888]
.L190:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #896]
.L191:
  ldr d1, [sp, #888]
  ldr d2, [sp, #896]
  fmul d0, d1, d2
  str d0, [sp, #904]
.L192:
  ldr x1, [sp, #880]
  ldr d0, [sp, #904]
  adrp x0, _arr_zz@PAGE
  add x0, x0, _arr_zz@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L193:
  mov x0, #1
  str x0, [sp, #912]
.L194:
  ldr x1, [sp, #16]
  ldr x2, [sp, #912]
  add x0, x1, x2
  str x0, [sp, #16]
.L195:
  b .L176
.L196:
  mov x0, #1
  str x0, [sp, #920]
.L197:
  ldr x1, [sp, #8]
  ldr x2, [sp, #920]
  add x0, x1, x2
  str x0, [sp, #8]
.L198:
  b .L173
.L199:
  mov x0, #1
  str x0, [sp, #8]
.L200:
  mov x0, #7
  str x0, [sp, #928]
.L201:
  ldr x1, [sp, #8]
  ldr x2, [sp, #928]
  cmp x1, x2
  b.gt .L267
.L202:
  mov x0, #1
  str x0, [sp, #16]
.L203:
  mov x0, #101
  str x0, [sp, #936]
.L204:
  ldr x1, [sp, #16]
  ldr x2, [sp, #936]
  cmp x1, x2
  b.gt .L264
.L205:
  mov x0, #1
  str x0, [sp, #944]
.L206:
  ldr x1, [sp, #8]
  ldr x2, [sp, #944]
  sub x0, x1, x2
  str x0, [sp, #952]
.L207:
  mov x0, #101
  str x0, [sp, #960]
.L208:
  ldr x1, [sp, #952]
  ldr x2, [sp, #960]
  mul x0, x1, x2
  str x0, [sp, #968]
.L209:
  ldr x1, [sp, #968]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #976]
.L210:
  mov x0, #1
  str x0, [sp, #984]
.L211:
  ldr x1, [sp, #8]
  ldr x2, [sp, #984]
  sub x0, x1, x2
  str x0, [sp, #992]
.L212:
  mov x0, #101
  str x0, [sp, #1000]
.L213:
  ldr x1, [sp, #992]
  ldr x2, [sp, #1000]
  mul x0, x1, x2
  str x0, [sp, #1008]
.L214:
  ldr x1, [sp, #1008]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1016]
.L215:
  ldr x1, [sp, #1016]
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1024]
.L216:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #1032]
.L217:
  ldr d1, [sp, #1024]
  ldr d2, [sp, #1032]
  fmul d0, d1, d2
  str d0, [sp, #1040]
.L218:
  ldr x1, [sp, #976]
  ldr d0, [sp, #1040]
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L219:
  mov x0, #1
  str x0, [sp, #1048]
.L220:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1048]
  sub x0, x1, x2
  str x0, [sp, #1056]
.L221:
  mov x0, #101
  str x0, [sp, #1064]
.L222:
  ldr x1, [sp, #1056]
  ldr x2, [sp, #1064]
  mul x0, x1, x2
  str x0, [sp, #1072]
.L223:
  ldr x1, [sp, #1072]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1080]
.L224:
  mov x0, #1
  str x0, [sp, #1088]
.L225:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1088]
  sub x0, x1, x2
  str x0, [sp, #1096]
.L226:
  mov x0, #101
  str x0, [sp, #1104]
.L227:
  ldr x1, [sp, #1096]
  ldr x2, [sp, #1104]
  mul x0, x1, x2
  str x0, [sp, #1112]
.L228:
  ldr x1, [sp, #1112]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1120]
.L229:
  ldr x1, [sp, #1120]
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1128]
.L230:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #1136]
.L231:
  ldr d1, [sp, #1128]
  ldr d2, [sp, #1136]
  fmul d0, d1, d2
  str d0, [sp, #1144]
.L232:
  ldr x1, [sp, #1080]
  ldr d0, [sp, #1144]
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L233:
  mov x0, #1
  str x0, [sp, #1152]
.L234:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1152]
  sub x0, x1, x2
  str x0, [sp, #1160]
.L235:
  mov x0, #101
  str x0, [sp, #1168]
.L236:
  ldr x1, [sp, #1160]
  ldr x2, [sp, #1168]
  mul x0, x1, x2
  str x0, [sp, #1176]
.L237:
  ldr x1, [sp, #1176]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1184]
.L238:
  mov x0, #1
  str x0, [sp, #1192]
.L239:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1192]
  sub x0, x1, x2
  str x0, [sp, #1200]
.L240:
  mov x0, #101
  str x0, [sp, #1208]
.L241:
  ldr x1, [sp, #1200]
  ldr x2, [sp, #1208]
  mul x0, x1, x2
  str x0, [sp, #1216]
.L242:
  ldr x1, [sp, #1216]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1224]
.L243:
  ldr x1, [sp, #1224]
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1232]
.L244:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #1240]
.L245:
  ldr d1, [sp, #1232]
  ldr d2, [sp, #1240]
  fmul d0, d1, d2
  str d0, [sp, #1248]
.L246:
  ldr x1, [sp, #1184]
  ldr d0, [sp, #1248]
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L247:
  mov x0, #1
  str x0, [sp, #1256]
.L248:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1256]
  sub x0, x1, x2
  str x0, [sp, #1264]
.L249:
  mov x0, #101
  str x0, [sp, #1272]
.L250:
  ldr x1, [sp, #1264]
  ldr x2, [sp, #1272]
  mul x0, x1, x2
  str x0, [sp, #1280]
.L251:
  ldr x1, [sp, #1280]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1288]
.L252:
  mov x0, #1
  str x0, [sp, #1296]
.L253:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1296]
  sub x0, x1, x2
  str x0, [sp, #1304]
.L254:
  mov x0, #101
  str x0, [sp, #1312]
.L255:
  ldr x1, [sp, #1304]
  ldr x2, [sp, #1312]
  mul x0, x1, x2
  str x0, [sp, #1320]
.L256:
  ldr x1, [sp, #1320]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1328]
.L257:
  ldr x1, [sp, #1328]
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1336]
.L258:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #1344]
.L259:
  ldr d1, [sp, #1336]
  ldr d2, [sp, #1344]
  fmul d0, d1, d2
  str d0, [sp, #1352]
.L260:
  ldr x1, [sp, #1288]
  ldr d0, [sp, #1352]
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L261:
  mov x0, #1
  str x0, [sp, #1360]
.L262:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1360]
  add x0, x1, x2
  str x0, [sp, #16]
.L263:
  b .L203
.L264:
  mov x0, #1
  str x0, [sp, #1368]
.L265:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1368]
  add x0, x1, x2
  str x0, [sp, #8]
.L266:
  b .L200
.L267:
  mov x0, #1
  str x0, [sp, #24]
.L268:
  movz x0, #61320
  movk x0, #130, lsl #16
  str x0, [sp, #1376]
.L269:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1376]
  cmp x1, x2
  b.gt .L371
.L270:
  mov x0, #2
  str x0, [sp, #8]
.L271:
  mov x0, #6
  str x0, [sp, #1384]
.L272:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1384]
  cmp x1, x2
  b.gt .L368
.L273:
  mov x0, #2
  str x0, [sp, #16]
.L274:
  mov x0, #100
  str x0, [sp, #1392]
.L275:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1392]
  cmp x1, x2
  b.gt .L365
.L276:
  mov x0, #101
  str x0, [sp, #1400]
.L277:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1400]
  mul x0, x1, x2
  str x0, [sp, #1408]
.L278:
  ldr x1, [sp, #1408]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1416]
.L279:
  ldr x1, [sp, #1416]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1424]
.L280:
  mov x0, #1
  str x0, [sp, #1432]
.L281:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1432]
  sub x0, x1, x2
  str x0, [sp, #1440]
.L282:
  mov x0, #101
  str x0, [sp, #1448]
.L283:
  ldr x1, [sp, #1440]
  ldr x2, [sp, #1448]
  mul x0, x1, x2
  str x0, [sp, #1456]
.L284:
  ldr x1, [sp, #1456]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1464]
.L285:
  ldr x1, [sp, #1464]
  adrp x0, _arr_zr@PAGE
  add x0, x0, _arr_zr@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1472]
.L286:
  ldr d1, [sp, #1424]
  ldr d2, [sp, #1472]
  fmul d0, d1, d2
  str d0, [sp, #1480]
.L287:
  mov x0, #2
  str x0, [sp, #1488]
.L288:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1488]
  sub x0, x1, x2
  str x0, [sp, #1496]
.L289:
  mov x0, #101
  str x0, [sp, #1504]
.L290:
  ldr x1, [sp, #1496]
  ldr x2, [sp, #1504]
  mul x0, x1, x2
  str x0, [sp, #1512]
.L291:
  ldr x1, [sp, #1512]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1520]
.L292:
  ldr x1, [sp, #1520]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1528]
.L293:
  mov x0, #1
  str x0, [sp, #1536]
.L294:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1536]
  sub x0, x1, x2
  str x0, [sp, #1544]
.L295:
  mov x0, #101
  str x0, [sp, #1552]
.L296:
  ldr x1, [sp, #1544]
  ldr x2, [sp, #1552]
  mul x0, x1, x2
  str x0, [sp, #1560]
.L297:
  ldr x1, [sp, #1560]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1568]
.L298:
  ldr x1, [sp, #1568]
  adrp x0, _arr_zb@PAGE
  add x0, x0, _arr_zb@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1576]
.L299:
  ldr d1, [sp, #1528]
  ldr d2, [sp, #1576]
  fmul d0, d1, d2
  str d0, [sp, #1584]
.L300:
  ldr d1, [sp, #1480]
  ldr d2, [sp, #1584]
  fadd d0, d1, d2
  str d0, [sp, #1592]
.L301:
  mov x0, #1
  str x0, [sp, #1600]
.L302:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1600]
  sub x0, x1, x2
  str x0, [sp, #1608]
.L303:
  mov x0, #101
  str x0, [sp, #1616]
.L304:
  ldr x1, [sp, #1608]
  ldr x2, [sp, #1616]
  mul x0, x1, x2
  str x0, [sp, #1624]
.L305:
  ldr x1, [sp, #1624]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1632]
.L306:
  mov x0, #1
  str x0, [sp, #1640]
.L307:
  ldr x1, [sp, #1632]
  ldr x2, [sp, #1640]
  add x0, x1, x2
  str x0, [sp, #1648]
.L308:
  ldr x1, [sp, #1648]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1656]
.L309:
  mov x0, #1
  str x0, [sp, #1664]
.L310:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1664]
  sub x0, x1, x2
  str x0, [sp, #1672]
.L311:
  mov x0, #101
  str x0, [sp, #1680]
.L312:
  ldr x1, [sp, #1672]
  ldr x2, [sp, #1680]
  mul x0, x1, x2
  str x0, [sp, #1688]
.L313:
  ldr x1, [sp, #1688]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1696]
.L314:
  ldr x1, [sp, #1696]
  adrp x0, _arr_zu@PAGE
  add x0, x0, _arr_zu@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1704]
.L315:
  ldr d1, [sp, #1656]
  ldr d2, [sp, #1704]
  fmul d0, d1, d2
  str d0, [sp, #1712]
.L316:
  ldr d1, [sp, #1592]
  ldr d2, [sp, #1712]
  fadd d0, d1, d2
  str d0, [sp, #1720]
.L317:
  mov x0, #1
  str x0, [sp, #1728]
.L318:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1728]
  sub x0, x1, x2
  str x0, [sp, #1736]
.L319:
  mov x0, #101
  str x0, [sp, #1744]
.L320:
  ldr x1, [sp, #1736]
  ldr x2, [sp, #1744]
  mul x0, x1, x2
  str x0, [sp, #1752]
.L321:
  ldr x1, [sp, #1752]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1760]
.L322:
  mov x0, #1
  str x0, [sp, #1768]
.L323:
  ldr x1, [sp, #1760]
  ldr x2, [sp, #1768]
  sub x0, x1, x2
  str x0, [sp, #1776]
.L324:
  ldr x1, [sp, #1776]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1784]
.L325:
  mov x0, #1
  str x0, [sp, #1792]
.L326:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1792]
  sub x0, x1, x2
  str x0, [sp, #1800]
.L327:
  mov x0, #101
  str x0, [sp, #1808]
.L328:
  ldr x1, [sp, #1800]
  ldr x2, [sp, #1808]
  mul x0, x1, x2
  str x0, [sp, #1816]
.L329:
  ldr x1, [sp, #1816]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1824]
.L330:
  ldr x1, [sp, #1824]
  adrp x0, _arr_zv@PAGE
  add x0, x0, _arr_zv@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1832]
.L331:
  ldr d1, [sp, #1784]
  ldr d2, [sp, #1832]
  fmul d0, d1, d2
  str d0, [sp, #1840]
.L332:
  ldr d1, [sp, #1720]
  ldr d2, [sp, #1840]
  fadd d0, d1, d2
  str d0, [sp, #1848]
.L333:
  mov x0, #1
  str x0, [sp, #1856]
.L334:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1856]
  sub x0, x1, x2
  str x0, [sp, #1864]
.L335:
  mov x0, #101
  str x0, [sp, #1872]
.L336:
  ldr x1, [sp, #1864]
  ldr x2, [sp, #1872]
  mul x0, x1, x2
  str x0, [sp, #1880]
.L337:
  ldr x1, [sp, #1880]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1888]
.L338:
  ldr x1, [sp, #1888]
  adrp x0, _arr_zz@PAGE
  add x0, x0, _arr_zz@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1896]
.L339:
  ldr d1, [sp, #1848]
  ldr d2, [sp, #1896]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L340:
  mov x0, #1
  str x0, [sp, #1904]
.L341:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1904]
  sub x0, x1, x2
  str x0, [sp, #1912]
.L342:
  mov x0, #101
  str x0, [sp, #1920]
.L343:
  ldr x1, [sp, #1912]
  ldr x2, [sp, #1920]
  mul x0, x1, x2
  str x0, [sp, #1928]
.L344:
  ldr x1, [sp, #1928]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1936]
.L345:
  mov x0, #1
  str x0, [sp, #1944]
.L346:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1944]
  sub x0, x1, x2
  str x0, [sp, #1952]
.L347:
  mov x0, #101
  str x0, [sp, #1960]
.L348:
  ldr x1, [sp, #1952]
  ldr x2, [sp, #1960]
  mul x0, x1, x2
  str x0, [sp, #1968]
.L349:
  ldr x1, [sp, #1968]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #1976]
.L350:
  ldr x1, [sp, #1976]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1984]
.L351:
  movz x0, #26214
  movk x0, #26214, lsl #16
  movk x0, #26214, lsl #32
  movk x0, #16326, lsl #48
  fmov d0, x0
  str d0, [sp, #1992]
.L352:
  mov x0, #1
  str x0, [sp, #2000]
.L353:
  ldr x1, [sp, #8]
  ldr x2, [sp, #2000]
  sub x0, x1, x2
  str x0, [sp, #2008]
.L354:
  mov x0, #101
  str x0, [sp, #2016]
.L355:
  ldr x1, [sp, #2008]
  ldr x2, [sp, #2016]
  mul x0, x1, x2
  str x0, [sp, #2024]
.L356:
  ldr x1, [sp, #2024]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #2032]
.L357:
  ldr x1, [sp, #2032]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2040]
.L358:
  ldr d1, [sp, #32]
  ldr d2, [sp, #2040]
  fsub d0, d1, d2
  str d0, [sp, #2048]
.L359:
  ldr d1, [sp, #1992]
  ldr d2, [sp, #2048]
  fmul d0, d1, d2
  str d0, [sp, #2056]
.L360:
  ldr d1, [sp, #1984]
  ldr d2, [sp, #2056]
  fadd d0, d1, d2
  str d0, [sp, #2064]
.L361:
  ldr x1, [sp, #1936]
  ldr d0, [sp, #2064]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L362:
  mov x0, #1
  str x0, [sp, #2072]
.L363:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2072]
  add x0, x1, x2
  str x0, [sp, #16]
.L364:
  b .L274
.L365:
  mov x0, #1
  str x0, [sp, #2080]
.L366:
  ldr x1, [sp, #8]
  ldr x2, [sp, #2080]
  add x0, x1, x2
  str x0, [sp, #8]
.L367:
  b .L271
.L368:
  mov x0, #1
  str x0, [sp, #2088]
.L369:
  ldr x1, [sp, #24]
  ldr x2, [sp, #2088]
  add x0, x1, x2
  str x0, [sp, #24]
.L370:
  b .L268
.L371:
  mov x0, #4
  str x0, [sp, #2096]
.L372:
  mov x0, #1
  str x0, [sp, #2104]
.L373:
  ldr x1, [sp, #2096]
  ldr x2, [sp, #2104]
  sub x0, x1, x2
  str x0, [sp, #2112]
.L374:
  mov x0, #101
  str x0, [sp, #2120]
.L375:
  ldr x1, [sp, #2112]
  ldr x2, [sp, #2120]
  mul x0, x1, x2
  str x0, [sp, #2128]
.L376:
  mov x0, #51
  str x0, [sp, #2136]
.L377:
  ldr x1, [sp, #2128]
  ldr x2, [sp, #2136]
  add x0, x1, x2
  str x0, [sp, #2144]
.L378:
  ldr x1, [sp, #2144]
  adrp x0, _arr_za@PAGE
  add x0, x0, _arr_za@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2152]
.L379:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #2152]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_379@PAGE
  add x0, x0, .Lfmt_print_379@PAGEOFF
  bl _printf
  add sp, sp, #16
.L380:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print j
  ldr x9, [sp, #8]
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
  ldr x9, [sp, #16]
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
  // print qa (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x1, .Lname_qa@PAGE
  add x1, x1, .Lname_qa@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
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
  ldr x29, [sp, #2160]
  ldr x30, [sp, #2168]
  add sp, sp, #2176
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

.Lfmt_print_379:
  .asciz "%f\n"

.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_qa:
  .asciz "qa"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_za
.align 3
_arr_za:
  .space 5664
.global _arr_zr
.align 3
_arr_zr:
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
.global _arr_zz
.align 3
_arr_zz:
  .space 5664
