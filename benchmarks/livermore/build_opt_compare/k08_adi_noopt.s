.global _main
.align 2

_main:
  sub sp, sp, #2336
  str x30, [sp, #2328]
  str x29, [sp, #2320]
  add x29, sp, #2320

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
  str x0, [sp, #2160]
  str x0, [sp, #2168]
  str x0, [sp, #2176]
  str x0, [sp, #2184]
  str x0, [sp, #2192]
  str x0, [sp, #2200]
  str x0, [sp, #2208]
  str x0, [sp, #2216]
  str x0, [sp, #2224]
  str x0, [sp, #2232]
  str x0, [sp, #2240]
  str x0, [sp, #2248]
  str x0, [sp, #2256]
  str x0, [sp, #2264]
  str x0, [sp, #2272]
  str x0, [sp, #2280]
  str x0, [sp, #2288]
  str x0, [sp, #2296]
  str x0, [sp, #2304]
  str x0, [sp, #2312]

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
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #120]
.L15:
  mov x0, #0
  str x0, [sp, #128]
.L16:
  mov x0, #0
  str x0, [sp, #136]
.L17:
  mov x0, #0
  str x0, [sp, #144]
.L18:
  mov x0, #0
  str x0, [sp, #152]
.L19:
  mov x0, #0
  str x0, [sp, #160]
.L20:
  mov x0, #0
  str x0, [sp, #168]
.L21:
  mov x0, #0
  str x0, [sp, #176]
.L22:
  mov x0, #0
  str x0, [sp, #184]
.L23:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #192]
.L24:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #200]
.L25:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #208]
.L26:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L27:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #216]
.L28:
  ldr d1, [sp, #216]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #224]
.L30:
  ldr d1, [sp, #224]
  ldr d2, [sp, #192]
  fmul d0, d1, d2
  str d0, [sp, #208]
.L31:
  mov x0, #1
  str x0, [sp, #128]
.L32:
  mov x0, #39
  str x0, [sp, #232]
.L33:
  ldr x1, [sp, #128]
  ldr x2, [sp, #232]
  cmp x1, x2
  b.gt .L47
.L34:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #240]
.L35:
  ldr d1, [sp, #240]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #248]
.L36:
  ldr d1, [sp, #248]
  ldr d2, [sp, #200]
  fmul d0, d1, d2
  str d0, [sp, #256]
.L37:
  ldr d1, [sp, #256]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L38:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #264]
.L39:
  ldr d1, [sp, #264]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L40:
  ldr d1, [sp, #200]
  ldr d2, [sp, #208]
  fsub d0, d1, d2
  str d0, [sp, #272]
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #280]
.L42:
  ldr d1, [sp, #272]
  ldr d2, [sp, #280]
  fmul d0, d1, d2
  str d0, [sp, #288]
.L43:
  ldr x1, [sp, #128]
  ldr d0, [sp, #288]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L44:
  mov x0, #1
  str x0, [sp, #296]
.L45:
  ldr x1, [sp, #128]
  ldr x2, [sp, #296]
  add x0, x1, x2
  str x0, [sp, #128]
.L46:
  b .L32
.L47:
  mov x0, #1
  str x0, [sp, #304]
.L48:
  ldr x1, [sp, #304]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #312]
.L49:
  ldr x0, [sp, #312]
  str x0, [sp, #48]
.L50:
  mov x0, #2
  str x0, [sp, #320]
.L51:
  ldr x1, [sp, #320]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #328]
.L52:
  ldr x0, [sp, #328]
  str x0, [sp, #56]
.L53:
  mov x0, #3
  str x0, [sp, #336]
.L54:
  ldr x1, [sp, #336]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #344]
.L55:
  ldr x0, [sp, #344]
  str x0, [sp, #64]
.L56:
  mov x0, #4
  str x0, [sp, #352]
.L57:
  ldr x1, [sp, #352]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #360]
.L58:
  ldr x0, [sp, #360]
  str x0, [sp, #72]
.L59:
  mov x0, #5
  str x0, [sp, #368]
.L60:
  ldr x1, [sp, #368]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #376]
.L61:
  ldr x0, [sp, #376]
  str x0, [sp, #80]
.L62:
  mov x0, #6
  str x0, [sp, #384]
.L63:
  ldr x1, [sp, #384]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #392]
.L64:
  ldr x0, [sp, #392]
  str x0, [sp, #88]
.L65:
  mov x0, #7
  str x0, [sp, #400]
.L66:
  ldr x1, [sp, #400]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #408]
.L67:
  ldr x0, [sp, #408]
  str x0, [sp, #96]
.L68:
  mov x0, #8
  str x0, [sp, #416]
.L69:
  ldr x1, [sp, #416]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #424]
.L70:
  ldr x0, [sp, #424]
  str x0, [sp, #104]
.L71:
  mov x0, #9
  str x0, [sp, #432]
.L72:
  ldr x1, [sp, #432]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #440]
.L73:
  ldr x0, [sp, #440]
  str x0, [sp, #112]
.L74:
  mov x0, #34
  str x0, [sp, #448]
.L75:
  ldr x1, [sp, #448]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #456]
.L76:
  ldr x0, [sp, #456]
  str x0, [sp, #120]
.L77:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L78:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #464]
.L79:
  ldr d1, [sp, #464]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L80:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #472]
.L81:
  ldr d1, [sp, #472]
  ldr d2, [sp, #192]
  fmul d0, d1, d2
  str d0, [sp, #208]
.L82:
  mov x0, #1
  str x0, [sp, #184]
.L83:
  mov x0, #5
  str x0, [sp, #480]
.L84:
  ldr x1, [sp, #184]
  ldr x2, [sp, #480]
  cmp x1, x2
  b.gt .L120
.L85:
  mov x0, #1
  str x0, [sp, #176]
.L86:
  mov x0, #101
  str x0, [sp, #488]
.L87:
  ldr x1, [sp, #176]
  ldr x2, [sp, #488]
  cmp x1, x2
  b.gt .L117
.L88:
  mov x0, #1
  str x0, [sp, #168]
.L89:
  mov x0, #2
  str x0, [sp, #496]
.L90:
  ldr x1, [sp, #168]
  ldr x2, [sp, #496]
  cmp x1, x2
  b.gt .L114
.L91:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #504]
.L92:
  ldr d1, [sp, #504]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #512]
.L93:
  ldr d1, [sp, #512]
  ldr d2, [sp, #200]
  fmul d0, d1, d2
  str d0, [sp, #520]
.L94:
  ldr d1, [sp, #520]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L95:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #528]
.L96:
  ldr d1, [sp, #528]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L97:
  mov x0, #1
  str x0, [sp, #536]
.L98:
  ldr x1, [sp, #184]
  ldr x2, [sp, #536]
  sub x0, x1, x2
  str x0, [sp, #544]
.L99:
  mov x0, #202
  str x0, [sp, #552]
.L100:
  ldr x1, [sp, #544]
  ldr x2, [sp, #552]
  mul x0, x1, x2
  str x0, [sp, #560]
.L101:
  mov x0, #1
  str x0, [sp, #568]
.L102:
  ldr x1, [sp, #176]
  ldr x2, [sp, #568]
  sub x0, x1, x2
  str x0, [sp, #576]
.L103:
  mov x0, #2
  str x0, [sp, #584]
.L104:
  ldr x1, [sp, #576]
  ldr x2, [sp, #584]
  mul x0, x1, x2
  str x0, [sp, #592]
.L105:
  ldr x1, [sp, #560]
  ldr x2, [sp, #592]
  add x0, x1, x2
  str x0, [sp, #600]
.L106:
  ldr x1, [sp, #600]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #608]
.L107:
  ldr d1, [sp, #200]
  ldr d2, [sp, #208]
  fsub d0, d1, d2
  str d0, [sp, #616]
.L108:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #624]
.L109:
  ldr d1, [sp, #616]
  ldr d2, [sp, #624]
  fmul d0, d1, d2
  str d0, [sp, #632]
.L110:
  ldr x1, [sp, #608]
  ldr d0, [sp, #632]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L111:
  mov x0, #1
  str x0, [sp, #640]
.L112:
  ldr x1, [sp, #168]
  ldr x2, [sp, #640]
  add x0, x1, x2
  str x0, [sp, #168]
.L113:
  b .L89
.L114:
  mov x0, #1
  str x0, [sp, #648]
.L115:
  ldr x1, [sp, #176]
  ldr x2, [sp, #648]
  add x0, x1, x2
  str x0, [sp, #176]
.L116:
  b .L86
.L117:
  mov x0, #1
  str x0, [sp, #656]
.L118:
  ldr x1, [sp, #184]
  ldr x2, [sp, #656]
  add x0, x1, x2
  str x0, [sp, #184]
.L119:
  b .L83
.L120:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L121:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #664]
.L122:
  ldr d1, [sp, #664]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L123:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #672]
.L124:
  ldr d1, [sp, #672]
  ldr d2, [sp, #192]
  fmul d0, d1, d2
  str d0, [sp, #208]
.L125:
  mov x0, #1
  str x0, [sp, #184]
.L126:
  mov x0, #5
  str x0, [sp, #680]
.L127:
  ldr x1, [sp, #184]
  ldr x2, [sp, #680]
  cmp x1, x2
  b.gt .L163
.L128:
  mov x0, #1
  str x0, [sp, #176]
.L129:
  mov x0, #101
  str x0, [sp, #688]
.L130:
  ldr x1, [sp, #176]
  ldr x2, [sp, #688]
  cmp x1, x2
  b.gt .L160
.L131:
  mov x0, #1
  str x0, [sp, #168]
.L132:
  mov x0, #2
  str x0, [sp, #696]
.L133:
  ldr x1, [sp, #168]
  ldr x2, [sp, #696]
  cmp x1, x2
  b.gt .L157
.L134:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #704]
.L135:
  ldr d1, [sp, #704]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #712]
.L136:
  ldr d1, [sp, #712]
  ldr d2, [sp, #200]
  fmul d0, d1, d2
  str d0, [sp, #720]
.L137:
  ldr d1, [sp, #720]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L138:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #728]
.L139:
  ldr d1, [sp, #728]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L140:
  mov x0, #1
  str x0, [sp, #736]
.L141:
  ldr x1, [sp, #184]
  ldr x2, [sp, #736]
  sub x0, x1, x2
  str x0, [sp, #744]
.L142:
  mov x0, #202
  str x0, [sp, #752]
.L143:
  ldr x1, [sp, #744]
  ldr x2, [sp, #752]
  mul x0, x1, x2
  str x0, [sp, #760]
.L144:
  mov x0, #1
  str x0, [sp, #768]
.L145:
  ldr x1, [sp, #176]
  ldr x2, [sp, #768]
  sub x0, x1, x2
  str x0, [sp, #776]
.L146:
  mov x0, #2
  str x0, [sp, #784]
.L147:
  ldr x1, [sp, #776]
  ldr x2, [sp, #784]
  mul x0, x1, x2
  str x0, [sp, #792]
.L148:
  ldr x1, [sp, #760]
  ldr x2, [sp, #792]
  add x0, x1, x2
  str x0, [sp, #800]
.L149:
  ldr x1, [sp, #800]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #808]
.L150:
  ldr d1, [sp, #200]
  ldr d2, [sp, #208]
  fsub d0, d1, d2
  str d0, [sp, #816]
.L151:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #824]
.L152:
  ldr d1, [sp, #816]
  ldr d2, [sp, #824]
  fmul d0, d1, d2
  str d0, [sp, #832]
.L153:
  ldr x1, [sp, #808]
  ldr d0, [sp, #832]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L154:
  mov x0, #1
  str x0, [sp, #840]
.L155:
  ldr x1, [sp, #168]
  ldr x2, [sp, #840]
  add x0, x1, x2
  str x0, [sp, #168]
.L156:
  b .L132
.L157:
  mov x0, #1
  str x0, [sp, #848]
.L158:
  ldr x1, [sp, #176]
  ldr x2, [sp, #848]
  add x0, x1, x2
  str x0, [sp, #176]
.L159:
  b .L129
.L160:
  mov x0, #1
  str x0, [sp, #856]
.L161:
  ldr x1, [sp, #184]
  ldr x2, [sp, #856]
  add x0, x1, x2
  str x0, [sp, #184]
.L162:
  b .L126
.L163:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L164:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #864]
.L165:
  ldr d1, [sp, #864]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L166:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #872]
.L167:
  ldr d1, [sp, #872]
  ldr d2, [sp, #192]
  fmul d0, d1, d2
  str d0, [sp, #208]
.L168:
  mov x0, #1
  str x0, [sp, #184]
.L169:
  mov x0, #5
  str x0, [sp, #880]
.L170:
  ldr x1, [sp, #184]
  ldr x2, [sp, #880]
  cmp x1, x2
  b.gt .L206
.L171:
  mov x0, #1
  str x0, [sp, #176]
.L172:
  mov x0, #101
  str x0, [sp, #888]
.L173:
  ldr x1, [sp, #176]
  ldr x2, [sp, #888]
  cmp x1, x2
  b.gt .L203
.L174:
  mov x0, #1
  str x0, [sp, #168]
.L175:
  mov x0, #2
  str x0, [sp, #896]
.L176:
  ldr x1, [sp, #168]
  ldr x2, [sp, #896]
  cmp x1, x2
  b.gt .L200
.L177:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #904]
.L178:
  ldr d1, [sp, #904]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #912]
.L179:
  ldr d1, [sp, #912]
  ldr d2, [sp, #200]
  fmul d0, d1, d2
  str d0, [sp, #920]
.L180:
  ldr d1, [sp, #920]
  ldr d2, [sp, #192]
  fadd d0, d1, d2
  str d0, [sp, #200]
.L181:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #928]
.L182:
  ldr d1, [sp, #928]
  ldr d2, [sp, #192]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L183:
  mov x0, #1
  str x0, [sp, #936]
.L184:
  ldr x1, [sp, #184]
  ldr x2, [sp, #936]
  sub x0, x1, x2
  str x0, [sp, #944]
.L185:
  mov x0, #202
  str x0, [sp, #952]
.L186:
  ldr x1, [sp, #944]
  ldr x2, [sp, #952]
  mul x0, x1, x2
  str x0, [sp, #960]
.L187:
  mov x0, #1
  str x0, [sp, #968]
.L188:
  ldr x1, [sp, #176]
  ldr x2, [sp, #968]
  sub x0, x1, x2
  str x0, [sp, #976]
.L189:
  mov x0, #2
  str x0, [sp, #984]
.L190:
  ldr x1, [sp, #976]
  ldr x2, [sp, #984]
  mul x0, x1, x2
  str x0, [sp, #992]
.L191:
  ldr x1, [sp, #960]
  ldr x2, [sp, #992]
  add x0, x1, x2
  str x0, [sp, #1000]
.L192:
  ldr x1, [sp, #1000]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #1008]
.L193:
  ldr d1, [sp, #200]
  ldr d2, [sp, #208]
  fsub d0, d1, d2
  str d0, [sp, #1016]
.L194:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #1024]
.L195:
  ldr d1, [sp, #1016]
  ldr d2, [sp, #1024]
  fmul d0, d1, d2
  str d0, [sp, #1032]
.L196:
  ldr x1, [sp, #1008]
  ldr d0, [sp, #1032]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L197:
  mov x0, #1
  str x0, [sp, #1040]
.L198:
  ldr x1, [sp, #168]
  ldr x2, [sp, #1040]
  add x0, x1, x2
  str x0, [sp, #168]
.L199:
  b .L175
.L200:
  mov x0, #1
  str x0, [sp, #1048]
.L201:
  ldr x1, [sp, #176]
  ldr x2, [sp, #1048]
  add x0, x1, x2
  str x0, [sp, #176]
.L202:
  b .L172
.L203:
  mov x0, #1
  str x0, [sp, #1056]
.L204:
  ldr x1, [sp, #184]
  ldr x2, [sp, #1056]
  add x0, x1, x2
  str x0, [sp, #184]
.L205:
  b .L169
.L206:
  mov x0, #1
  str x0, [sp, #8]
.L207:
  movz x0, #49240
  movk x0, #160, lsl #16
  str x0, [sp, #1064]
.L208:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1064]
  cmp x1, x2
  b.gt .L374
.L209:
  mov x0, #1
  str x0, [sp, #32]
.L210:
  mov x0, #2
  str x0, [sp, #40]
.L211:
  mov x0, #2
  str x0, [sp, #16]
.L212:
  mov x0, #3
  str x0, [sp, #1072]
.L213:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1072]
  cmp x1, x2
  b.gt .L371
.L214:
  mov x0, #2
  str x0, [sp, #24]
.L215:
  mov x0, #99
  str x0, [sp, #1080]
.L216:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1080]
  cmp x1, x2
  b.gt .L368
.L217:
  mov x0, #1
  str x0, [sp, #1088]
.L218:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1088]
  sub x0, x1, x2
  str x0, [sp, #1096]
.L219:
  mov x0, #202
  str x0, [sp, #1104]
.L220:
  ldr x1, [sp, #1096]
  ldr x2, [sp, #1104]
  mul x0, x1, x2
  str x0, [sp, #1112]
.L221:
  mov x0, #2
  str x0, [sp, #1120]
.L222:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1120]
  mul x0, x1, x2
  str x0, [sp, #1128]
.L223:
  ldr x1, [sp, #1112]
  ldr x2, [sp, #1128]
  add x0, x1, x2
  str x0, [sp, #1136]
.L224:
  ldr x1, [sp, #1136]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #136]
.L225:
  mov x0, #1
  str x0, [sp, #1144]
.L226:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1144]
  sub x0, x1, x2
  str x0, [sp, #1152]
.L227:
  mov x0, #202
  str x0, [sp, #1160]
.L228:
  ldr x1, [sp, #1152]
  ldr x2, [sp, #1160]
  mul x0, x1, x2
  str x0, [sp, #1168]
.L229:
  mov x0, #2
  str x0, [sp, #1176]
.L230:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1176]
  sub x0, x1, x2
  str x0, [sp, #1184]
.L231:
  mov x0, #2
  str x0, [sp, #1192]
.L232:
  ldr x1, [sp, #1184]
  ldr x2, [sp, #1192]
  mul x0, x1, x2
  str x0, [sp, #1200]
.L233:
  ldr x1, [sp, #1168]
  ldr x2, [sp, #1200]
  add x0, x1, x2
  str x0, [sp, #1208]
.L234:
  ldr x1, [sp, #1208]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #144]
.L235:
  mov x0, #1
  str x0, [sp, #1216]
.L236:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1216]
  sub x0, x1, x2
  str x0, [sp, #1224]
.L237:
  mov x0, #202
  str x0, [sp, #1232]
.L238:
  ldr x1, [sp, #1224]
  ldr x2, [sp, #1232]
  mul x0, x1, x2
  str x0, [sp, #1240]
.L239:
  mov x0, #1
  str x0, [sp, #1248]
.L240:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1248]
  sub x0, x1, x2
  str x0, [sp, #1256]
.L241:
  mov x0, #2
  str x0, [sp, #1264]
.L242:
  ldr x1, [sp, #1256]
  ldr x2, [sp, #1264]
  mul x0, x1, x2
  str x0, [sp, #1272]
.L243:
  ldr x1, [sp, #1240]
  ldr x2, [sp, #1272]
  add x0, x1, x2
  str x0, [sp, #1280]
.L244:
  ldr x1, [sp, #1280]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #128]
.L245:
  mov x0, #202
  str x0, [sp, #1288]
.L246:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1288]
  mul x0, x1, x2
  str x0, [sp, #1296]
.L247:
  mov x0, #1
  str x0, [sp, #1304]
.L248:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1304]
  sub x0, x1, x2
  str x0, [sp, #1312]
.L249:
  mov x0, #2
  str x0, [sp, #1320]
.L250:
  ldr x1, [sp, #1312]
  ldr x2, [sp, #1320]
  mul x0, x1, x2
  str x0, [sp, #1328]
.L251:
  ldr x1, [sp, #1296]
  ldr x2, [sp, #1328]
  add x0, x1, x2
  str x0, [sp, #1336]
.L252:
  ldr x1, [sp, #1336]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #152]
.L253:
  mov x0, #2
  str x0, [sp, #1344]
.L254:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1344]
  sub x0, x1, x2
  str x0, [sp, #1352]
.L255:
  mov x0, #202
  str x0, [sp, #1360]
.L256:
  ldr x1, [sp, #1352]
  ldr x2, [sp, #1360]
  mul x0, x1, x2
  str x0, [sp, #1368]
.L257:
  mov x0, #1
  str x0, [sp, #1376]
.L258:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1376]
  sub x0, x1, x2
  str x0, [sp, #1384]
.L259:
  mov x0, #2
  str x0, [sp, #1392]
.L260:
  ldr x1, [sp, #1384]
  ldr x2, [sp, #1392]
  mul x0, x1, x2
  str x0, [sp, #1400]
.L261:
  ldr x1, [sp, #1368]
  ldr x2, [sp, #1400]
  add x0, x1, x2
  str x0, [sp, #1408]
.L262:
  ldr x1, [sp, #1408]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #160]
.L263:
  ldr x1, [sp, #136]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1416]
.L264:
  ldr x1, [sp, #144]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1424]
.L265:
  ldr d1, [sp, #1416]
  ldr d2, [sp, #1424]
  fsub d0, d1, d2
  str d0, [sp, #1432]
.L266:
  ldr x1, [sp, #24]
  ldr d0, [sp, #1432]
  adrp x0, _arr_du1@PAGE
  add x0, x0, _arr_du1@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L267:
  ldr x1, [sp, #136]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1440]
.L268:
  ldr x1, [sp, #144]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1448]
.L269:
  ldr d1, [sp, #1440]
  ldr d2, [sp, #1448]
  fsub d0, d1, d2
  str d0, [sp, #1456]
.L270:
  ldr x1, [sp, #24]
  ldr d0, [sp, #1456]
  adrp x0, _arr_du2@PAGE
  add x0, x0, _arr_du2@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L271:
  ldr x1, [sp, #136]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1464]
.L272:
  ldr x1, [sp, #144]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1472]
.L273:
  ldr d1, [sp, #1464]
  ldr d2, [sp, #1472]
  fsub d0, d1, d2
  str d0, [sp, #1480]
.L274:
  ldr x1, [sp, #24]
  ldr d0, [sp, #1480]
  adrp x0, _arr_du3@PAGE
  add x0, x0, _arr_du3@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L275:
  mov x0, #1
  str x0, [sp, #1488]
.L276:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1488]
  sub x0, x1, x2
  str x0, [sp, #1496]
.L277:
  mov x0, #202
  str x0, [sp, #1504]
.L278:
  ldr x1, [sp, #1496]
  ldr x2, [sp, #1504]
  mul x0, x1, x2
  str x0, [sp, #1512]
.L279:
  mov x0, #1
  str x0, [sp, #1520]
.L280:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1520]
  sub x0, x1, x2
  str x0, [sp, #1528]
.L281:
  mov x0, #2
  str x0, [sp, #1536]
.L282:
  ldr x1, [sp, #1528]
  ldr x2, [sp, #1536]
  mul x0, x1, x2
  str x0, [sp, #1544]
.L283:
  ldr x1, [sp, #1512]
  ldr x2, [sp, #1544]
  add x0, x1, x2
  str x0, [sp, #1552]
.L284:
  ldr x1, [sp, #1552]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #1560]
.L285:
  ldr x1, [sp, #128]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1568]
.L286:
  ldr x1, [sp, #24]
  adrp x0, _arr_du1@PAGE
  add x0, x0, _arr_du1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1576]
.L287:
  ldr d1, [sp, #48]
  ldr d2, [sp, #1576]
  fmul d0, d1, d2
  str d0, [sp, #1584]
.L288:
  ldr d1, [sp, #1568]
  ldr d2, [sp, #1584]
  fadd d0, d1, d2
  str d0, [sp, #1592]
.L289:
  ldr x1, [sp, #24]
  adrp x0, _arr_du2@PAGE
  add x0, x0, _arr_du2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1600]
.L290:
  ldr d1, [sp, #56]
  ldr d2, [sp, #1600]
  fmul d0, d1, d2
  str d0, [sp, #1608]
.L291:
  ldr d1, [sp, #1592]
  ldr d2, [sp, #1608]
  fadd d0, d1, d2
  str d0, [sp, #1616]
.L292:
  ldr x1, [sp, #24]
  adrp x0, _arr_du3@PAGE
  add x0, x0, _arr_du3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1624]
.L293:
  ldr d1, [sp, #64]
  ldr d2, [sp, #1624]
  fmul d0, d1, d2
  str d0, [sp, #1632]
.L294:
  ldr d1, [sp, #1616]
  ldr d2, [sp, #1632]
  fadd d0, d1, d2
  str d0, [sp, #1640]
.L295:
  ldr x1, [sp, #152]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1648]
.L296:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d0, x0
  str d0, [sp, #1656]
.L297:
  ldr x1, [sp, #128]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1664]
.L298:
  ldr d1, [sp, #1656]
  ldr d2, [sp, #1664]
  fmul d0, d1, d2
  str d0, [sp, #1672]
.L299:
  ldr d1, [sp, #1648]
  ldr d2, [sp, #1672]
  fsub d0, d1, d2
  str d0, [sp, #1680]
.L300:
  ldr x1, [sp, #160]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1688]
.L301:
  ldr d1, [sp, #1680]
  ldr d2, [sp, #1688]
  fadd d0, d1, d2
  str d0, [sp, #1696]
.L302:
  ldr d1, [sp, #120]
  ldr d2, [sp, #1696]
  fmul d0, d1, d2
  str d0, [sp, #1704]
.L303:
  ldr d1, [sp, #1640]
  ldr d2, [sp, #1704]
  fadd d0, d1, d2
  str d0, [sp, #1712]
.L304:
  ldr x1, [sp, #1560]
  ldr d0, [sp, #1712]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L305:
  mov x0, #1
  str x0, [sp, #1720]
.L306:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1720]
  sub x0, x1, x2
  str x0, [sp, #1728]
.L307:
  mov x0, #202
  str x0, [sp, #1736]
.L308:
  ldr x1, [sp, #1728]
  ldr x2, [sp, #1736]
  mul x0, x1, x2
  str x0, [sp, #1744]
.L309:
  mov x0, #1
  str x0, [sp, #1752]
.L310:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1752]
  sub x0, x1, x2
  str x0, [sp, #1760]
.L311:
  mov x0, #2
  str x0, [sp, #1768]
.L312:
  ldr x1, [sp, #1760]
  ldr x2, [sp, #1768]
  mul x0, x1, x2
  str x0, [sp, #1776]
.L313:
  ldr x1, [sp, #1744]
  ldr x2, [sp, #1776]
  add x0, x1, x2
  str x0, [sp, #1784]
.L314:
  ldr x1, [sp, #1784]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #1792]
.L315:
  ldr x1, [sp, #128]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1800]
.L316:
  ldr x1, [sp, #24]
  adrp x0, _arr_du1@PAGE
  add x0, x0, _arr_du1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1808]
.L317:
  ldr d1, [sp, #72]
  ldr d2, [sp, #1808]
  fmul d0, d1, d2
  str d0, [sp, #1816]
.L318:
  ldr d1, [sp, #1800]
  ldr d2, [sp, #1816]
  fadd d0, d1, d2
  str d0, [sp, #1824]
.L319:
  ldr x1, [sp, #24]
  adrp x0, _arr_du2@PAGE
  add x0, x0, _arr_du2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1832]
.L320:
  ldr d1, [sp, #80]
  ldr d2, [sp, #1832]
  fmul d0, d1, d2
  str d0, [sp, #1840]
.L321:
  ldr d1, [sp, #1824]
  ldr d2, [sp, #1840]
  fadd d0, d1, d2
  str d0, [sp, #1848]
.L322:
  ldr x1, [sp, #24]
  adrp x0, _arr_du3@PAGE
  add x0, x0, _arr_du3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1856]
.L323:
  ldr d1, [sp, #88]
  ldr d2, [sp, #1856]
  fmul d0, d1, d2
  str d0, [sp, #1864]
.L324:
  ldr d1, [sp, #1848]
  ldr d2, [sp, #1864]
  fadd d0, d1, d2
  str d0, [sp, #1872]
.L325:
  ldr x1, [sp, #152]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1880]
.L326:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d0, x0
  str d0, [sp, #1888]
.L327:
  ldr x1, [sp, #128]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1896]
.L328:
  ldr d1, [sp, #1888]
  ldr d2, [sp, #1896]
  fmul d0, d1, d2
  str d0, [sp, #1904]
.L329:
  ldr d1, [sp, #1880]
  ldr d2, [sp, #1904]
  fsub d0, d1, d2
  str d0, [sp, #1912]
.L330:
  ldr x1, [sp, #160]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1920]
.L331:
  ldr d1, [sp, #1912]
  ldr d2, [sp, #1920]
  fadd d0, d1, d2
  str d0, [sp, #1928]
.L332:
  ldr d1, [sp, #120]
  ldr d2, [sp, #1928]
  fmul d0, d1, d2
  str d0, [sp, #1936]
.L333:
  ldr d1, [sp, #1872]
  ldr d2, [sp, #1936]
  fadd d0, d1, d2
  str d0, [sp, #1944]
.L334:
  ldr x1, [sp, #1792]
  ldr d0, [sp, #1944]
  adrp x0, _arr_u2@PAGE
  add x0, x0, _arr_u2@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L335:
  mov x0, #1
  str x0, [sp, #1952]
.L336:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1952]
  sub x0, x1, x2
  str x0, [sp, #1960]
.L337:
  mov x0, #202
  str x0, [sp, #1968]
.L338:
  ldr x1, [sp, #1960]
  ldr x2, [sp, #1968]
  mul x0, x1, x2
  str x0, [sp, #1976]
.L339:
  mov x0, #1
  str x0, [sp, #1984]
.L340:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1984]
  sub x0, x1, x2
  str x0, [sp, #1992]
.L341:
  mov x0, #2
  str x0, [sp, #2000]
.L342:
  ldr x1, [sp, #1992]
  ldr x2, [sp, #2000]
  mul x0, x1, x2
  str x0, [sp, #2008]
.L343:
  ldr x1, [sp, #1976]
  ldr x2, [sp, #2008]
  add x0, x1, x2
  str x0, [sp, #2016]
.L344:
  ldr x1, [sp, #2016]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #2024]
.L345:
  ldr x1, [sp, #128]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2032]
.L346:
  ldr x1, [sp, #24]
  adrp x0, _arr_du1@PAGE
  add x0, x0, _arr_du1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2040]
.L347:
  ldr d1, [sp, #96]
  ldr d2, [sp, #2040]
  fmul d0, d1, d2
  str d0, [sp, #2048]
.L348:
  ldr d1, [sp, #2032]
  ldr d2, [sp, #2048]
  fadd d0, d1, d2
  str d0, [sp, #2056]
.L349:
  ldr x1, [sp, #24]
  adrp x0, _arr_du2@PAGE
  add x0, x0, _arr_du2@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2064]
.L350:
  ldr d1, [sp, #104]
  ldr d2, [sp, #2064]
  fmul d0, d1, d2
  str d0, [sp, #2072]
.L351:
  ldr d1, [sp, #2056]
  ldr d2, [sp, #2072]
  fadd d0, d1, d2
  str d0, [sp, #2080]
.L352:
  ldr x1, [sp, #24]
  adrp x0, _arr_du3@PAGE
  add x0, x0, _arr_du3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2088]
.L353:
  ldr d1, [sp, #112]
  ldr d2, [sp, #2088]
  fmul d0, d1, d2
  str d0, [sp, #2096]
.L354:
  ldr d1, [sp, #2080]
  ldr d2, [sp, #2096]
  fadd d0, d1, d2
  str d0, [sp, #2104]
.L355:
  ldr x1, [sp, #152]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2112]
.L356:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d0, x0
  str d0, [sp, #2120]
.L357:
  ldr x1, [sp, #128]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2128]
.L358:
  ldr d1, [sp, #2120]
  ldr d2, [sp, #2128]
  fmul d0, d1, d2
  str d0, [sp, #2136]
.L359:
  ldr d1, [sp, #2112]
  ldr d2, [sp, #2136]
  fsub d0, d1, d2
  str d0, [sp, #2144]
.L360:
  ldr x1, [sp, #160]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2152]
.L361:
  ldr d1, [sp, #2144]
  ldr d2, [sp, #2152]
  fadd d0, d1, d2
  str d0, [sp, #2160]
.L362:
  ldr d1, [sp, #120]
  ldr d2, [sp, #2160]
  fmul d0, d1, d2
  str d0, [sp, #2168]
.L363:
  ldr d1, [sp, #2104]
  ldr d2, [sp, #2168]
  fadd d0, d1, d2
  str d0, [sp, #2176]
.L364:
  ldr x1, [sp, #2024]
  ldr d0, [sp, #2176]
  adrp x0, _arr_u3@PAGE
  add x0, x0, _arr_u3@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L365:
  mov x0, #1
  str x0, [sp, #2184]
.L366:
  ldr x1, [sp, #24]
  ldr x2, [sp, #2184]
  add x0, x1, x2
  str x0, [sp, #24]
.L367:
  b .L215
.L368:
  mov x0, #1
  str x0, [sp, #2192]
.L369:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2192]
  add x0, x1, x2
  str x0, [sp, #16]
.L370:
  b .L212
.L371:
  mov x0, #1
  str x0, [sp, #2200]
.L372:
  ldr x1, [sp, #8]
  ldr x2, [sp, #2200]
  add x0, x1, x2
  str x0, [sp, #8]
.L373:
  b .L207
.L374:
  mov x0, #2
  str x0, [sp, #2208]
.L375:
  mov x0, #1
  str x0, [sp, #2216]
.L376:
  ldr x1, [sp, #2208]
  ldr x2, [sp, #2216]
  sub x0, x1, x2
  str x0, [sp, #2224]
.L377:
  mov x0, #202
  str x0, [sp, #2232]
.L378:
  ldr x1, [sp, #2224]
  ldr x2, [sp, #2232]
  mul x0, x1, x2
  str x0, [sp, #2240]
.L379:
  mov x0, #51
  str x0, [sp, #2248]
.L380:
  mov x0, #1
  str x0, [sp, #2256]
.L381:
  ldr x1, [sp, #2248]
  ldr x2, [sp, #2256]
  sub x0, x1, x2
  str x0, [sp, #2264]
.L382:
  mov x0, #2
  str x0, [sp, #2272]
.L383:
  ldr x1, [sp, #2264]
  ldr x2, [sp, #2272]
  mul x0, x1, x2
  str x0, [sp, #2280]
.L384:
  ldr x1, [sp, #2240]
  ldr x2, [sp, #2280]
  add x0, x1, x2
  str x0, [sp, #2288]
.L385:
  mov x0, #2
  str x0, [sp, #2296]
.L386:
  ldr x1, [sp, #2288]
  ldr x2, [sp, #2296]
  add x0, x1, x2
  str x0, [sp, #2304]
.L387:
  ldr x1, [sp, #2304]
  adrp x0, _arr_u1@PAGE
  add x0, x0, _arr_u1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2312]
.L388:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #2312]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_388@PAGE
  add x0, x0, .Lfmt_print_388@PAGEOFF
  bl _printf
  add sp, sp, #16
.L389:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print rep
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print kx
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x1, .Lname_kx@PAGE
  add x1, x1, .Lname_kx@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ky
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x1, .Lname_ky@PAGE
  add x1, x1, .Lname_ky@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print nl1
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x1, .Lname_nl1@PAGE
  add x1, x1, .Lname_nl1@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print nl2
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x1, .Lname_nl2@PAGE
  add x1, x1, .Lname_nl2@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print a11 (float)
  ldr d0, [sp, #48]
  sub sp, sp, #32
  adrp x1, .Lname_a11@PAGE
  add x1, x1, .Lname_a11@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a12 (float)
  ldr d0, [sp, #56]
  sub sp, sp, #32
  adrp x1, .Lname_a12@PAGE
  add x1, x1, .Lname_a12@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a13 (float)
  ldr d0, [sp, #64]
  sub sp, sp, #32
  adrp x1, .Lname_a13@PAGE
  add x1, x1, .Lname_a13@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a21 (float)
  ldr d0, [sp, #72]
  sub sp, sp, #32
  adrp x1, .Lname_a21@PAGE
  add x1, x1, .Lname_a21@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a22 (float)
  ldr d0, [sp, #80]
  sub sp, sp, #32
  adrp x1, .Lname_a22@PAGE
  add x1, x1, .Lname_a22@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a23 (float)
  ldr d0, [sp, #88]
  sub sp, sp, #32
  adrp x1, .Lname_a23@PAGE
  add x1, x1, .Lname_a23@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a31 (float)
  ldr d0, [sp, #96]
  sub sp, sp, #32
  adrp x1, .Lname_a31@PAGE
  add x1, x1, .Lname_a31@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a32 (float)
  ldr d0, [sp, #104]
  sub sp, sp, #32
  adrp x1, .Lname_a32@PAGE
  add x1, x1, .Lname_a32@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a33 (float)
  ldr d0, [sp, #112]
  sub sp, sp, #32
  adrp x1, .Lname_a33@PAGE
  add x1, x1, .Lname_a33@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print sig (float)
  ldr d0, [sp, #120]
  sub sp, sp, #32
  adrp x1, .Lname_sig@PAGE
  add x1, x1, .Lname_sig@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print idx
  ldr x9, [sp, #128]
  sub sp, sp, #16
  adrp x1, .Lname_idx@PAGE
  add x1, x1, .Lname_idx@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_yp
  ldr x9, [sp, #136]
  sub sp, sp, #16
  adrp x1, .Lname_idx_yp@PAGE
  add x1, x1, .Lname_idx_yp@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_ym
  ldr x9, [sp, #144]
  sub sp, sp, #16
  adrp x1, .Lname_idx_ym@PAGE
  add x1, x1, .Lname_idx_ym@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_xp
  ldr x9, [sp, #152]
  sub sp, sp, #16
  adrp x1, .Lname_idx_xp@PAGE
  add x1, x1, .Lname_idx_xp@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_xm
  ldr x9, [sp, #160]
  sub sp, sp, #16
  adrp x1, .Lname_idx_xm@PAGE
  add x1, x1, .Lname_idx_xm@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k1
  ldr x9, [sp, #168]
  sub sp, sp, #16
  adrp x1, .Lname_k1@PAGE
  add x1, x1, .Lname_k1@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k2
  ldr x9, [sp, #176]
  sub sp, sp, #16
  adrp x1, .Lname_k2@PAGE
  add x1, x1, .Lname_k2@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k3
  ldr x9, [sp, #184]
  sub sp, sp, #16
  adrp x1, .Lname_k3@PAGE
  add x1, x1, .Lname_k3@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #192]
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
  ldr d0, [sp, #200]
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
  ldr d0, [sp, #208]
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
  ldr x29, [sp, #2320]
  ldr x30, [sp, #2328]
  add sp, sp, #2336
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

.Lfmt_print_388:
  .asciz "%f\n"

.Lname_rep:
  .asciz "rep"
.Lname_kx:
  .asciz "kx"
.Lname_ky:
  .asciz "ky"
.Lname_nl1:
  .asciz "nl1"
.Lname_nl2:
  .asciz "nl2"
.Lname_a11:
  .asciz "a11"
.Lname_a12:
  .asciz "a12"
.Lname_a13:
  .asciz "a13"
.Lname_a21:
  .asciz "a21"
.Lname_a22:
  .asciz "a22"
.Lname_a23:
  .asciz "a23"
.Lname_a31:
  .asciz "a31"
.Lname_a32:
  .asciz "a32"
.Lname_a33:
  .asciz "a33"
.Lname_sig:
  .asciz "sig"
.Lname_idx:
  .asciz "idx"
.Lname_idx_yp:
  .asciz "idx_yp"
.Lname_idx_ym:
  .asciz "idx_ym"
.Lname_idx_xp:
  .asciz "idx_xp"
.Lname_idx_xm:
  .asciz "idx_xm"
.Lname_k1:
  .asciz "k1"
.Lname_k2:
  .asciz "k2"
.Lname_k3:
  .asciz "k3"
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
.global _arr_u1
.align 3
_arr_u1:
  .space 8088
.global _arr_u2
.align 3
_arr_u2:
  .space 8088
.global _arr_u3
.align 3
_arr_u3:
  .space 8088
.global _arr_du1
.align 3
_arr_du1:
  .space 816
.global _arr_du2
.align 3
_arr_du2:
  .space 816
.global _arr_du3
.align 3
_arr_du3:
  .space 816
