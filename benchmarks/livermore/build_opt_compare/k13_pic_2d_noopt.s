.global _main
.align 2

_main:
  sub sp, sp, #2608
  str x30, [sp, #2600]
  str x29, [sp, #2592]
  add x29, sp, #2592

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
  str x0, [sp, #2320]
  str x0, [sp, #2328]
  str x0, [sp, #2336]
  str x0, [sp, #2344]
  str x0, [sp, #2352]
  str x0, [sp, #2360]
  str x0, [sp, #2368]
  str x0, [sp, #2376]
  str x0, [sp, #2384]
  str x0, [sp, #2392]
  str x0, [sp, #2400]
  str x0, [sp, #2408]
  str x0, [sp, #2416]
  str x0, [sp, #2424]
  str x0, [sp, #2432]
  str x0, [sp, #2440]
  str x0, [sp, #2448]
  str x0, [sp, #2456]
  str x0, [sp, #2464]
  str x0, [sp, #2472]
  str x0, [sp, #2480]
  str x0, [sp, #2488]
  str x0, [sp, #2496]
  str x0, [sp, #2504]
  str x0, [sp, #2512]
  str x0, [sp, #2520]
  str x0, [sp, #2528]
  str x0, [sp, #2536]
  str x0, [sp, #2544]
  str x0, [sp, #2552]
  str x0, [sp, #2560]
  str x0, [sp, #2568]
  str x0, [sp, #2576]
  str x0, [sp, #2584]

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
  fmov d0, x0
  str d0, [sp, #56]
.L15:
  movz x0, #0
  movk x0, #16352, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L16:
  mov x0, #1
  str x0, [sp, #104]
.L17:
  mov x0, #4
  str x0, [sp, #120]
.L18:
  ldr x1, [sp, #104]
  ldr x2, [sp, #120]
  cmp x1, x2
  b.gt .L35
.L19:
  mov x0, #1
  str x0, [sp, #112]
.L20:
  mov x0, #64
  str x0, [sp, #128]
.L21:
  ldr x1, [sp, #112]
  ldr x2, [sp, #128]
  cmp x1, x2
  b.gt .L32
.L22:
  mov x0, #1
  str x0, [sp, #136]
.L23:
  ldr x1, [sp, #104]
  ldr x2, [sp, #136]
  sub x0, x1, x2
  str x0, [sp, #144]
.L24:
  mov x0, #64
  str x0, [sp, #152]
.L25:
  ldr x1, [sp, #144]
  ldr x2, [sp, #152]
  mul x0, x1, x2
  str x0, [sp, #160]
.L26:
  ldr x1, [sp, #160]
  ldr x2, [sp, #112]
  add x0, x1, x2
  str x0, [sp, #168]
.L27:
  ldr x1, [sp, #168]
  ldr d0, [sp, #56]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L28:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L29:
  mov x0, #1
  str x0, [sp, #176]
.L30:
  ldr x1, [sp, #112]
  ldr x2, [sp, #176]
  add x0, x1, x2
  str x0, [sp, #112]
.L31:
  b .L20
.L32:
  mov x0, #1
  str x0, [sp, #184]
.L33:
  ldr x1, [sp, #104]
  ldr x2, [sp, #184]
  add x0, x1, x2
  str x0, [sp, #104]
.L34:
  b .L17
.L35:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L36:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L37:
  ldr d1, [sp, #192]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L38:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #200]
.L39:
  ldr d1, [sp, #200]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L40:
  mov x0, #1
  str x0, [sp, #104]
.L41:
  mov x0, #64
  str x0, [sp, #208]
.L42:
  ldr x1, [sp, #104]
  ldr x2, [sp, #208]
  cmp x1, x2
  b.gt .L67
.L43:
  mov x0, #1
  str x0, [sp, #96]
.L44:
  mov x0, #64
  str x0, [sp, #216]
.L45:
  ldr x1, [sp, #96]
  ldr x2, [sp, #216]
  cmp x1, x2
  b.gt .L64
.L46:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #224]
.L47:
  ldr d1, [sp, #224]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #232]
.L48:
  ldr d1, [sp, #232]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #240]
.L49:
  ldr d1, [sp, #240]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L50:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #248]
.L51:
  ldr d1, [sp, #248]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L52:
  mov x0, #1
  str x0, [sp, #256]
.L53:
  ldr x1, [sp, #104]
  ldr x2, [sp, #256]
  sub x0, x1, x2
  str x0, [sp, #264]
.L54:
  mov x0, #64
  str x0, [sp, #272]
.L55:
  ldr x1, [sp, #264]
  ldr x2, [sp, #272]
  mul x0, x1, x2
  str x0, [sp, #280]
.L56:
  ldr x1, [sp, #280]
  ldr x2, [sp, #96]
  add x0, x1, x2
  str x0, [sp, #288]
.L57:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #296]
.L58:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #304]
.L59:
  ldr d1, [sp, #296]
  ldr d2, [sp, #304]
  fmul d0, d1, d2
  str d0, [sp, #312]
.L60:
  ldr x1, [sp, #288]
  ldr d0, [sp, #312]
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L61:
  mov x0, #1
  str x0, [sp, #320]
.L62:
  ldr x1, [sp, #96]
  ldr x2, [sp, #320]
  add x0, x1, x2
  str x0, [sp, #96]
.L63:
  b .L44
.L64:
  mov x0, #1
  str x0, [sp, #328]
.L65:
  ldr x1, [sp, #104]
  ldr x2, [sp, #328]
  add x0, x1, x2
  str x0, [sp, #104]
.L66:
  b .L41
.L67:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L68:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #336]
.L69:
  ldr d1, [sp, #336]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L70:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #344]
.L71:
  ldr d1, [sp, #344]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L72:
  mov x0, #1
  str x0, [sp, #104]
.L73:
  mov x0, #64
  str x0, [sp, #352]
.L74:
  ldr x1, [sp, #104]
  ldr x2, [sp, #352]
  cmp x1, x2
  b.gt .L99
.L75:
  mov x0, #1
  str x0, [sp, #96]
.L76:
  mov x0, #64
  str x0, [sp, #360]
.L77:
  ldr x1, [sp, #96]
  ldr x2, [sp, #360]
  cmp x1, x2
  b.gt .L96
.L78:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #368]
.L79:
  ldr d1, [sp, #368]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #376]
.L80:
  ldr d1, [sp, #376]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #384]
.L81:
  ldr d1, [sp, #384]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L82:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #392]
.L83:
  ldr d1, [sp, #392]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L84:
  mov x0, #1
  str x0, [sp, #400]
.L85:
  ldr x1, [sp, #104]
  ldr x2, [sp, #400]
  sub x0, x1, x2
  str x0, [sp, #408]
.L86:
  mov x0, #64
  str x0, [sp, #416]
.L87:
  ldr x1, [sp, #408]
  ldr x2, [sp, #416]
  mul x0, x1, x2
  str x0, [sp, #424]
.L88:
  ldr x1, [sp, #424]
  ldr x2, [sp, #96]
  add x0, x1, x2
  str x0, [sp, #432]
.L89:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #440]
.L90:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #448]
.L91:
  ldr d1, [sp, #440]
  ldr d2, [sp, #448]
  fmul d0, d1, d2
  str d0, [sp, #456]
.L92:
  ldr x1, [sp, #432]
  ldr d0, [sp, #456]
  adrp x0, _arr_c@PAGE
  add x0, x0, _arr_c@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L93:
  mov x0, #1
  str x0, [sp, #464]
.L94:
  ldr x1, [sp, #96]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #96]
.L95:
  b .L76
.L96:
  mov x0, #1
  str x0, [sp, #472]
.L97:
  ldr x1, [sp, #104]
  ldr x2, [sp, #472]
  add x0, x1, x2
  str x0, [sp, #104]
.L98:
  b .L73
.L99:
  mov x0, #1
  str x0, [sp, #104]
.L100:
  mov x0, #64
  str x0, [sp, #480]
.L101:
  ldr x1, [sp, #104]
  ldr x2, [sp, #480]
  cmp x1, x2
  b.gt .L118
.L102:
  mov x0, #1
  str x0, [sp, #96]
.L103:
  mov x0, #64
  str x0, [sp, #488]
.L104:
  ldr x1, [sp, #96]
  ldr x2, [sp, #488]
  cmp x1, x2
  b.gt .L115
.L105:
  mov x0, #1
  str x0, [sp, #496]
.L106:
  ldr x1, [sp, #104]
  ldr x2, [sp, #496]
  sub x0, x1, x2
  str x0, [sp, #504]
.L107:
  mov x0, #64
  str x0, [sp, #512]
.L108:
  ldr x1, [sp, #504]
  ldr x2, [sp, #512]
  mul x0, x1, x2
  str x0, [sp, #520]
.L109:
  ldr x1, [sp, #520]
  ldr x2, [sp, #96]
  add x0, x1, x2
  str x0, [sp, #528]
.L110:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #536]
.L111:
  ldr x1, [sp, #528]
  ldr d0, [sp, #536]
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L112:
  mov x0, #1
  str x0, [sp, #544]
.L113:
  ldr x1, [sp, #96]
  ldr x2, [sp, #544]
  add x0, x1, x2
  str x0, [sp, #96]
.L114:
  b .L103
.L115:
  mov x0, #1
  str x0, [sp, #552]
.L116:
  ldr x1, [sp, #104]
  ldr x2, [sp, #552]
  add x0, x1, x2
  str x0, [sp, #104]
.L117:
  b .L100
.L118:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L119:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #560]
.L120:
  ldr d1, [sp, #560]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L121:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #568]
.L122:
  ldr d1, [sp, #568]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L123:
  mov x0, #1
  str x0, [sp, #112]
.L124:
  mov x0, #1001
  str x0, [sp, #576]
.L125:
  ldr x1, [sp, #112]
  ldr x2, [sp, #576]
  cmp x1, x2
  b.gt .L139
.L126:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #584]
.L127:
  ldr d1, [sp, #584]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #592]
.L128:
  ldr d1, [sp, #592]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #600]
.L129:
  ldr d1, [sp, #600]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L130:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #608]
.L131:
  ldr d1, [sp, #608]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L132:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #616]
.L133:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #624]
.L134:
  ldr d1, [sp, #616]
  ldr d2, [sp, #624]
  fmul d0, d1, d2
  str d0, [sp, #632]
.L135:
  ldr x1, [sp, #112]
  ldr d0, [sp, #632]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L136:
  mov x0, #1
  str x0, [sp, #640]
.L137:
  ldr x1, [sp, #112]
  ldr x2, [sp, #640]
  add x0, x1, x2
  str x0, [sp, #112]
.L138:
  b .L124
.L139:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L140:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #648]
.L141:
  ldr d1, [sp, #648]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L142:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #656]
.L143:
  ldr d1, [sp, #656]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L144:
  mov x0, #1
  str x0, [sp, #112]
.L145:
  mov x0, #1001
  str x0, [sp, #664]
.L146:
  ldr x1, [sp, #112]
  ldr x2, [sp, #664]
  cmp x1, x2
  b.gt .L160
.L147:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #672]
.L148:
  ldr d1, [sp, #672]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #680]
.L149:
  ldr d1, [sp, #680]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #688]
.L150:
  ldr d1, [sp, #688]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L151:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #696]
.L152:
  ldr d1, [sp, #696]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L153:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #704]
.L154:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #712]
.L155:
  ldr d1, [sp, #704]
  ldr d2, [sp, #712]
  fmul d0, d1, d2
  str d0, [sp, #720]
.L156:
  ldr x1, [sp, #112]
  ldr d0, [sp, #720]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L157:
  mov x0, #1
  str x0, [sp, #728]
.L158:
  ldr x1, [sp, #112]
  ldr x2, [sp, #728]
  add x0, x1, x2
  str x0, [sp, #112]
.L159:
  b .L145
.L160:
  mov x0, #1
  str x0, [sp, #96]
.L161:
  mov x0, #96
  str x0, [sp, #736]
.L162:
  ldr x1, [sp, #96]
  ldr x2, [sp, #736]
  cmp x1, x2
  b.gt .L176
.L163:
  mov x0, #1
  str x0, [sp, #744]
.L164:
  ldr x1, [sp, #96]
  ldr x2, [sp, #744]
  sub x0, x1, x2
  str x0, [sp, #752]
.L165:
  mov x0, #64
  str x0, [sp, #760]
.L166:
  ldr x1, [sp, #752]
  ldr x2, [sp, #760]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  mul x0, x0, x2
  sub x0, x1, x0
  str x0, [sp, #768]
.L167:
  ldr x1, [sp, #96]
  ldr x2, [sp, #768]
  adrp x0, _arr_e@PAGE
  add x0, x0, _arr_e@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L168:
  mov x0, #1
  str x0, [sp, #776]
.L169:
  ldr x1, [sp, #96]
  ldr x2, [sp, #776]
  sub x0, x1, x2
  str x0, [sp, #784]
.L170:
  mov x0, #64
  str x0, [sp, #792]
.L171:
  ldr x1, [sp, #784]
  ldr x2, [sp, #792]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  mul x0, x0, x2
  sub x0, x1, x0
  str x0, [sp, #800]
.L172:
  ldr x1, [sp, #96]
  ldr x2, [sp, #800]
  adrp x0, _arr_f@PAGE
  add x0, x0, _arr_f@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L173:
  mov x0, #1
  str x0, [sp, #808]
.L174:
  ldr x1, [sp, #96]
  ldr x2, [sp, #808]
  add x0, x1, x2
  str x0, [sp, #96]
.L175:
  b .L161
.L176:
  mov x0, #1
  str x0, [sp, #16]
.L177:
  movz x0, #14096
  movk x0, #39, lsl #16
  str x0, [sp, #816]
.L178:
  ldr x1, [sp, #16]
  ldr x2, [sp, #816]
  cmp x1, x2
  b.gt .L436
.L179:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L180:
  movz x0, #0
  movk x0, #16352, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L181:
  mov x0, #1
  str x0, [sp, #104]
.L182:
  mov x0, #4
  str x0, [sp, #824]
.L183:
  ldr x1, [sp, #104]
  ldr x2, [sp, #824]
  cmp x1, x2
  b.gt .L200
.L184:
  mov x0, #1
  str x0, [sp, #112]
.L185:
  mov x0, #64
  str x0, [sp, #832]
.L186:
  ldr x1, [sp, #112]
  ldr x2, [sp, #832]
  cmp x1, x2
  b.gt .L197
.L187:
  mov x0, #1
  str x0, [sp, #840]
.L188:
  ldr x1, [sp, #104]
  ldr x2, [sp, #840]
  sub x0, x1, x2
  str x0, [sp, #848]
.L189:
  mov x0, #64
  str x0, [sp, #856]
.L190:
  ldr x1, [sp, #848]
  ldr x2, [sp, #856]
  mul x0, x1, x2
  str x0, [sp, #864]
.L191:
  ldr x1, [sp, #864]
  ldr x2, [sp, #112]
  add x0, x1, x2
  str x0, [sp, #872]
.L192:
  ldr x1, [sp, #872]
  ldr d0, [sp, #56]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L193:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L194:
  mov x0, #1
  str x0, [sp, #880]
.L195:
  ldr x1, [sp, #112]
  ldr x2, [sp, #880]
  add x0, x1, x2
  str x0, [sp, #112]
.L196:
  b .L185
.L197:
  mov x0, #1
  str x0, [sp, #888]
.L198:
  ldr x1, [sp, #104]
  ldr x2, [sp, #888]
  add x0, x1, x2
  str x0, [sp, #104]
.L199:
  b .L182
.L200:
  mov x0, #1
  str x0, [sp, #104]
.L201:
  mov x0, #64
  str x0, [sp, #896]
.L202:
  ldr x1, [sp, #104]
  ldr x2, [sp, #896]
  cmp x1, x2
  b.gt .L219
.L203:
  mov x0, #1
  str x0, [sp, #96]
.L204:
  mov x0, #64
  str x0, [sp, #904]
.L205:
  ldr x1, [sp, #96]
  ldr x2, [sp, #904]
  cmp x1, x2
  b.gt .L216
.L206:
  mov x0, #1
  str x0, [sp, #912]
.L207:
  ldr x1, [sp, #104]
  ldr x2, [sp, #912]
  sub x0, x1, x2
  str x0, [sp, #920]
.L208:
  mov x0, #64
  str x0, [sp, #928]
.L209:
  ldr x1, [sp, #920]
  ldr x2, [sp, #928]
  mul x0, x1, x2
  str x0, [sp, #936]
.L210:
  ldr x1, [sp, #936]
  ldr x2, [sp, #96]
  add x0, x1, x2
  str x0, [sp, #944]
.L211:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #952]
.L212:
  ldr x1, [sp, #944]
  ldr d0, [sp, #952]
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L213:
  mov x0, #1
  str x0, [sp, #960]
.L214:
  ldr x1, [sp, #96]
  ldr x2, [sp, #960]
  add x0, x1, x2
  str x0, [sp, #96]
.L215:
  b .L204
.L216:
  mov x0, #1
  str x0, [sp, #968]
.L217:
  ldr x1, [sp, #104]
  ldr x2, [sp, #968]
  add x0, x1, x2
  str x0, [sp, #104]
.L218:
  b .L201
.L219:
  mov x0, #1
  str x0, [sp, #8]
.L220:
  mov x0, #64
  str x0, [sp, #976]
.L221:
  ldr x1, [sp, #8]
  ldr x2, [sp, #976]
  cmp x1, x2
  b.gt .L433
.L222:
  mov x0, #1
  str x0, [sp, #984]
.L223:
  mov x0, #1
  str x0, [sp, #992]
.L224:
  ldr x1, [sp, #984]
  ldr x2, [sp, #992]
  sub x0, x1, x2
  str x0, [sp, #1000]
.L225:
  mov x0, #64
  str x0, [sp, #1008]
.L226:
  ldr x1, [sp, #1000]
  ldr x2, [sp, #1008]
  mul x0, x1, x2
  str x0, [sp, #1016]
.L227:
  ldr x1, [sp, #1016]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1024]
.L228:
  ldr x1, [sp, #1024]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1032]
.L229:
  ldr d0, [sp, #1032]
  fcvtzs x0, d0
  str x0, [sp, #1040]
.L230:
  ldr x0, [sp, #1040]
  str x0, [sp, #24]
.L231:
  mov x0, #2
  str x0, [sp, #1048]
.L232:
  mov x0, #1
  str x0, [sp, #1056]
.L233:
  ldr x1, [sp, #1048]
  ldr x2, [sp, #1056]
  sub x0, x1, x2
  str x0, [sp, #1064]
.L234:
  mov x0, #64
  str x0, [sp, #1072]
.L235:
  ldr x1, [sp, #1064]
  ldr x2, [sp, #1072]
  mul x0, x1, x2
  str x0, [sp, #1080]
.L236:
  ldr x1, [sp, #1080]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1088]
.L237:
  ldr x1, [sp, #1088]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1096]
.L238:
  ldr d0, [sp, #1096]
  fcvtzs x0, d0
  str x0, [sp, #1104]
.L239:
  ldr x0, [sp, #1104]
  str x0, [sp, #32]
.L240:
  mov x0, #63
  str x0, [sp, #1112]
.L241:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1112]
  and x0, x1, x2
  str x0, [sp, #24]
.L242:
  mov x0, #63
  str x0, [sp, #1120]
.L243:
  ldr x1, [sp, #32]
  ldr x2, [sp, #1120]
  and x0, x1, x2
  str x0, [sp, #32]
.L244:
  mov x0, #3
  str x0, [sp, #1128]
.L245:
  mov x0, #1
  str x0, [sp, #1136]
.L246:
  ldr x1, [sp, #1128]
  ldr x2, [sp, #1136]
  sub x0, x1, x2
  str x0, [sp, #1144]
.L247:
  mov x0, #64
  str x0, [sp, #1152]
.L248:
  ldr x1, [sp, #1144]
  ldr x2, [sp, #1152]
  mul x0, x1, x2
  str x0, [sp, #1160]
.L249:
  ldr x1, [sp, #1160]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1168]
.L250:
  mov x0, #3
  str x0, [sp, #1176]
.L251:
  mov x0, #1
  str x0, [sp, #1184]
.L252:
  ldr x1, [sp, #1176]
  ldr x2, [sp, #1184]
  sub x0, x1, x2
  str x0, [sp, #1192]
.L253:
  mov x0, #64
  str x0, [sp, #1200]
.L254:
  ldr x1, [sp, #1192]
  ldr x2, [sp, #1200]
  mul x0, x1, x2
  str x0, [sp, #1208]
.L255:
  ldr x1, [sp, #1208]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1216]
.L256:
  ldr x1, [sp, #1216]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1224]
.L257:
  mov x0, #1
  str x0, [sp, #1232]
.L258:
  ldr x1, [sp, #32]
  ldr x2, [sp, #1232]
  add x0, x1, x2
  str x0, [sp, #1240]
.L259:
  mov x0, #1
  str x0, [sp, #1248]
.L260:
  ldr x1, [sp, #1240]
  ldr x2, [sp, #1248]
  sub x0, x1, x2
  str x0, [sp, #1256]
.L261:
  mov x0, #64
  str x0, [sp, #1264]
.L262:
  ldr x1, [sp, #1256]
  ldr x2, [sp, #1264]
  mul x0, x1, x2
  str x0, [sp, #1272]
.L263:
  mov x0, #1
  str x0, [sp, #1280]
.L264:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1280]
  add x0, x1, x2
  str x0, [sp, #1288]
.L265:
  ldr x1, [sp, #1272]
  ldr x2, [sp, #1288]
  add x0, x1, x2
  str x0, [sp, #1296]
.L266:
  ldr x1, [sp, #1296]
  mov x0, #4097
  cmp x1, x0
  b.hs .Lbounds_err
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1304]
.L267:
  ldr d1, [sp, #1224]
  ldr d2, [sp, #1304]
  fadd d0, d1, d2
  str d0, [sp, #1312]
.L268:
  ldr x1, [sp, #1168]
  ldr d0, [sp, #1312]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L269:
  mov x0, #4
  str x0, [sp, #1320]
.L270:
  mov x0, #1
  str x0, [sp, #1328]
.L271:
  ldr x1, [sp, #1320]
  ldr x2, [sp, #1328]
  sub x0, x1, x2
  str x0, [sp, #1336]
.L272:
  mov x0, #64
  str x0, [sp, #1344]
.L273:
  ldr x1, [sp, #1336]
  ldr x2, [sp, #1344]
  mul x0, x1, x2
  str x0, [sp, #1352]
.L274:
  ldr x1, [sp, #1352]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1360]
.L275:
  mov x0, #4
  str x0, [sp, #1368]
.L276:
  mov x0, #1
  str x0, [sp, #1376]
.L277:
  ldr x1, [sp, #1368]
  ldr x2, [sp, #1376]
  sub x0, x1, x2
  str x0, [sp, #1384]
.L278:
  mov x0, #64
  str x0, [sp, #1392]
.L279:
  ldr x1, [sp, #1384]
  ldr x2, [sp, #1392]
  mul x0, x1, x2
  str x0, [sp, #1400]
.L280:
  ldr x1, [sp, #1400]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1408]
.L281:
  ldr x1, [sp, #1408]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1416]
.L282:
  mov x0, #1
  str x0, [sp, #1424]
.L283:
  ldr x1, [sp, #32]
  ldr x2, [sp, #1424]
  add x0, x1, x2
  str x0, [sp, #1432]
.L284:
  mov x0, #1
  str x0, [sp, #1440]
.L285:
  ldr x1, [sp, #1432]
  ldr x2, [sp, #1440]
  sub x0, x1, x2
  str x0, [sp, #1448]
.L286:
  mov x0, #64
  str x0, [sp, #1456]
.L287:
  ldr x1, [sp, #1448]
  ldr x2, [sp, #1456]
  mul x0, x1, x2
  str x0, [sp, #1464]
.L288:
  mov x0, #1
  str x0, [sp, #1472]
.L289:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1472]
  add x0, x1, x2
  str x0, [sp, #1480]
.L290:
  ldr x1, [sp, #1464]
  ldr x2, [sp, #1480]
  add x0, x1, x2
  str x0, [sp, #1488]
.L291:
  ldr x1, [sp, #1488]
  mov x0, #4097
  cmp x1, x0
  b.hs .Lbounds_err
  adrp x0, _arr_c@PAGE
  add x0, x0, _arr_c@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1496]
.L292:
  ldr d1, [sp, #1416]
  ldr d2, [sp, #1496]
  fadd d0, d1, d2
  str d0, [sp, #1504]
.L293:
  ldr x1, [sp, #1360]
  ldr d0, [sp, #1504]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L294:
  mov x0, #1
  str x0, [sp, #1512]
.L295:
  mov x0, #1
  str x0, [sp, #1520]
.L296:
  ldr x1, [sp, #1512]
  ldr x2, [sp, #1520]
  sub x0, x1, x2
  str x0, [sp, #1528]
.L297:
  mov x0, #64
  str x0, [sp, #1536]
.L298:
  ldr x1, [sp, #1528]
  ldr x2, [sp, #1536]
  mul x0, x1, x2
  str x0, [sp, #1544]
.L299:
  ldr x1, [sp, #1544]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1552]
.L300:
  mov x0, #1
  str x0, [sp, #1560]
.L301:
  mov x0, #1
  str x0, [sp, #1568]
.L302:
  ldr x1, [sp, #1560]
  ldr x2, [sp, #1568]
  sub x0, x1, x2
  str x0, [sp, #1576]
.L303:
  mov x0, #64
  str x0, [sp, #1584]
.L304:
  ldr x1, [sp, #1576]
  ldr x2, [sp, #1584]
  mul x0, x1, x2
  str x0, [sp, #1592]
.L305:
  ldr x1, [sp, #1592]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1600]
.L306:
  ldr x1, [sp, #1600]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1608]
.L307:
  mov x0, #3
  str x0, [sp, #1616]
.L308:
  mov x0, #1
  str x0, [sp, #1624]
.L309:
  ldr x1, [sp, #1616]
  ldr x2, [sp, #1624]
  sub x0, x1, x2
  str x0, [sp, #1632]
.L310:
  mov x0, #64
  str x0, [sp, #1640]
.L311:
  ldr x1, [sp, #1632]
  ldr x2, [sp, #1640]
  mul x0, x1, x2
  str x0, [sp, #1648]
.L312:
  ldr x1, [sp, #1648]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1656]
.L313:
  ldr x1, [sp, #1656]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1664]
.L314:
  ldr d1, [sp, #1608]
  ldr d2, [sp, #1664]
  fadd d0, d1, d2
  str d0, [sp, #1672]
.L315:
  ldr x1, [sp, #1552]
  ldr d0, [sp, #1672]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L316:
  mov x0, #2
  str x0, [sp, #1680]
.L317:
  mov x0, #1
  str x0, [sp, #1688]
.L318:
  ldr x1, [sp, #1680]
  ldr x2, [sp, #1688]
  sub x0, x1, x2
  str x0, [sp, #1696]
.L319:
  mov x0, #64
  str x0, [sp, #1704]
.L320:
  ldr x1, [sp, #1696]
  ldr x2, [sp, #1704]
  mul x0, x1, x2
  str x0, [sp, #1712]
.L321:
  ldr x1, [sp, #1712]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1720]
.L322:
  mov x0, #2
  str x0, [sp, #1728]
.L323:
  mov x0, #1
  str x0, [sp, #1736]
.L324:
  ldr x1, [sp, #1728]
  ldr x2, [sp, #1736]
  sub x0, x1, x2
  str x0, [sp, #1744]
.L325:
  mov x0, #64
  str x0, [sp, #1752]
.L326:
  ldr x1, [sp, #1744]
  ldr x2, [sp, #1752]
  mul x0, x1, x2
  str x0, [sp, #1760]
.L327:
  ldr x1, [sp, #1760]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1768]
.L328:
  ldr x1, [sp, #1768]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1776]
.L329:
  mov x0, #4
  str x0, [sp, #1784]
.L330:
  mov x0, #1
  str x0, [sp, #1792]
.L331:
  ldr x1, [sp, #1784]
  ldr x2, [sp, #1792]
  sub x0, x1, x2
  str x0, [sp, #1800]
.L332:
  mov x0, #64
  str x0, [sp, #1808]
.L333:
  ldr x1, [sp, #1800]
  ldr x2, [sp, #1808]
  mul x0, x1, x2
  str x0, [sp, #1816]
.L334:
  ldr x1, [sp, #1816]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1824]
.L335:
  ldr x1, [sp, #1824]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1832]
.L336:
  ldr d1, [sp, #1776]
  ldr d2, [sp, #1832]
  fadd d0, d1, d2
  str d0, [sp, #1840]
.L337:
  ldr x1, [sp, #1720]
  ldr d0, [sp, #1840]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L338:
  mov x0, #1
  str x0, [sp, #1848]
.L339:
  mov x0, #1
  str x0, [sp, #1856]
.L340:
  ldr x1, [sp, #1848]
  ldr x2, [sp, #1856]
  sub x0, x1, x2
  str x0, [sp, #1864]
.L341:
  mov x0, #64
  str x0, [sp, #1872]
.L342:
  ldr x1, [sp, #1864]
  ldr x2, [sp, #1872]
  mul x0, x1, x2
  str x0, [sp, #1880]
.L343:
  ldr x1, [sp, #1880]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1888]
.L344:
  ldr x1, [sp, #1888]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1896]
.L345:
  ldr d0, [sp, #1896]
  fcvtzs x0, d0
  str x0, [sp, #1904]
.L346:
  ldr x0, [sp, #1904]
  str x0, [sp, #40]
.L347:
  mov x0, #2
  str x0, [sp, #1912]
.L348:
  mov x0, #1
  str x0, [sp, #1920]
.L349:
  ldr x1, [sp, #1912]
  ldr x2, [sp, #1920]
  sub x0, x1, x2
  str x0, [sp, #1928]
.L350:
  mov x0, #64
  str x0, [sp, #1936]
.L351:
  ldr x1, [sp, #1928]
  ldr x2, [sp, #1936]
  mul x0, x1, x2
  str x0, [sp, #1944]
.L352:
  ldr x1, [sp, #1944]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #1952]
.L353:
  ldr x1, [sp, #1952]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1960]
.L354:
  ldr d0, [sp, #1960]
  fcvtzs x0, d0
  str x0, [sp, #1968]
.L355:
  ldr x0, [sp, #1968]
  str x0, [sp, #48]
.L356:
  mov x0, #63
  str x0, [sp, #1976]
.L357:
  ldr x1, [sp, #40]
  ldr x2, [sp, #1976]
  and x0, x1, x2
  str x0, [sp, #1984]
.L358:
  mov x0, #1
  str x0, [sp, #1992]
.L359:
  ldr x1, [sp, #1984]
  ldr x2, [sp, #1992]
  sub x0, x1, x2
  str x0, [sp, #40]
.L360:
  mov x0, #63
  str x0, [sp, #2000]
.L361:
  ldr x1, [sp, #48]
  ldr x2, [sp, #2000]
  and x0, x1, x2
  str x0, [sp, #2008]
.L362:
  mov x0, #1
  str x0, [sp, #2016]
.L363:
  ldr x1, [sp, #2008]
  ldr x2, [sp, #2016]
  sub x0, x1, x2
  str x0, [sp, #48]
.L364:
  mov x0, #1
  str x0, [sp, #2024]
.L365:
  mov x0, #1
  str x0, [sp, #2032]
.L366:
  ldr x1, [sp, #2024]
  ldr x2, [sp, #2032]
  sub x0, x1, x2
  str x0, [sp, #2040]
.L367:
  mov x0, #64
  str x0, [sp, #2048]
.L368:
  ldr x1, [sp, #2040]
  ldr x2, [sp, #2048]
  mul x0, x1, x2
  str x0, [sp, #2056]
.L369:
  ldr x1, [sp, #2056]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #2064]
.L370:
  mov x0, #1
  str x0, [sp, #2072]
.L371:
  mov x0, #1
  str x0, [sp, #2080]
.L372:
  ldr x1, [sp, #2072]
  ldr x2, [sp, #2080]
  sub x0, x1, x2
  str x0, [sp, #2088]
.L373:
  mov x0, #64
  str x0, [sp, #2096]
.L374:
  ldr x1, [sp, #2088]
  ldr x2, [sp, #2096]
  mul x0, x1, x2
  str x0, [sp, #2104]
.L375:
  ldr x1, [sp, #2104]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #2112]
.L376:
  ldr x1, [sp, #2112]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2120]
.L377:
  mov x0, #32
  str x0, [sp, #2128]
.L378:
  ldr x1, [sp, #40]
  ldr x2, [sp, #2128]
  add x0, x1, x2
  str x0, [sp, #2136]
.L379:
  ldr x1, [sp, #2136]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2144]
.L380:
  ldr d1, [sp, #2120]
  ldr d2, [sp, #2144]
  fadd d0, d1, d2
  str d0, [sp, #2152]
.L381:
  ldr x1, [sp, #2064]
  ldr d0, [sp, #2152]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L382:
  mov x0, #2
  str x0, [sp, #2160]
.L383:
  mov x0, #1
  str x0, [sp, #2168]
.L384:
  ldr x1, [sp, #2160]
  ldr x2, [sp, #2168]
  sub x0, x1, x2
  str x0, [sp, #2176]
.L385:
  mov x0, #64
  str x0, [sp, #2184]
.L386:
  ldr x1, [sp, #2176]
  ldr x2, [sp, #2184]
  mul x0, x1, x2
  str x0, [sp, #2192]
.L387:
  ldr x1, [sp, #2192]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #2200]
.L388:
  mov x0, #2
  str x0, [sp, #2208]
.L389:
  mov x0, #1
  str x0, [sp, #2216]
.L390:
  ldr x1, [sp, #2208]
  ldr x2, [sp, #2216]
  sub x0, x1, x2
  str x0, [sp, #2224]
.L391:
  mov x0, #64
  str x0, [sp, #2232]
.L392:
  ldr x1, [sp, #2224]
  ldr x2, [sp, #2232]
  mul x0, x1, x2
  str x0, [sp, #2240]
.L393:
  ldr x1, [sp, #2240]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #2248]
.L394:
  ldr x1, [sp, #2248]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2256]
.L395:
  mov x0, #32
  str x0, [sp, #2264]
.L396:
  ldr x1, [sp, #48]
  ldr x2, [sp, #2264]
  add x0, x1, x2
  str x0, [sp, #2272]
.L397:
  ldr x1, [sp, #2272]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2280]
.L398:
  ldr d1, [sp, #2256]
  ldr d2, [sp, #2280]
  fadd d0, d1, d2
  str d0, [sp, #2288]
.L399:
  ldr x1, [sp, #2200]
  ldr d0, [sp, #2288]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L400:
  mov x0, #32
  str x0, [sp, #2296]
.L401:
  ldr x1, [sp, #40]
  ldr x2, [sp, #2296]
  add x0, x1, x2
  str x0, [sp, #2304]
.L402:
  ldr x1, [sp, #2304]
  cmp x1, #97
  b.hs .Lbounds_err
  adrp x0, _arr_e@PAGE
  add x0, x0, _arr_e@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #2312]
.L403:
  ldr x1, [sp, #40]
  ldr x2, [sp, #2312]
  add x0, x1, x2
  str x0, [sp, #40]
.L404:
  mov x0, #32
  str x0, [sp, #2320]
.L405:
  ldr x1, [sp, #48]
  ldr x2, [sp, #2320]
  add x0, x1, x2
  str x0, [sp, #2328]
.L406:
  ldr x1, [sp, #2328]
  cmp x1, #97
  b.hs .Lbounds_err
  adrp x0, _arr_f@PAGE
  add x0, x0, _arr_f@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #2336]
.L407:
  ldr x1, [sp, #48]
  ldr x2, [sp, #2336]
  add x0, x1, x2
  str x0, [sp, #48]
.L408:
  mov x0, #1
  str x0, [sp, #2344]
.L409:
  ldr x1, [sp, #48]
  ldr x2, [sp, #2344]
  add x0, x1, x2
  str x0, [sp, #2352]
.L410:
  mov x0, #1
  str x0, [sp, #2360]
.L411:
  ldr x1, [sp, #2352]
  ldr x2, [sp, #2360]
  sub x0, x1, x2
  str x0, [sp, #2368]
.L412:
  mov x0, #64
  str x0, [sp, #2376]
.L413:
  ldr x1, [sp, #2368]
  ldr x2, [sp, #2376]
  mul x0, x1, x2
  str x0, [sp, #2384]
.L414:
  mov x0, #1
  str x0, [sp, #2392]
.L415:
  ldr x1, [sp, #40]
  ldr x2, [sp, #2392]
  add x0, x1, x2
  str x0, [sp, #2400]
.L416:
  ldr x1, [sp, #2384]
  ldr x2, [sp, #2400]
  add x0, x1, x2
  str x0, [sp, #2408]
.L417:
  mov x0, #1
  str x0, [sp, #2416]
.L418:
  ldr x1, [sp, #48]
  ldr x2, [sp, #2416]
  add x0, x1, x2
  str x0, [sp, #2424]
.L419:
  mov x0, #1
  str x0, [sp, #2432]
.L420:
  ldr x1, [sp, #2424]
  ldr x2, [sp, #2432]
  sub x0, x1, x2
  str x0, [sp, #2440]
.L421:
  mov x0, #64
  str x0, [sp, #2448]
.L422:
  ldr x1, [sp, #2440]
  ldr x2, [sp, #2448]
  mul x0, x1, x2
  str x0, [sp, #2456]
.L423:
  mov x0, #1
  str x0, [sp, #2464]
.L424:
  ldr x1, [sp, #40]
  ldr x2, [sp, #2464]
  add x0, x1, x2
  str x0, [sp, #2472]
.L425:
  ldr x1, [sp, #2456]
  ldr x2, [sp, #2472]
  add x0, x1, x2
  str x0, [sp, #2480]
.L426:
  ldr x1, [sp, #2480]
  mov x0, #6177
  cmp x1, x0
  b.hs .Lbounds_err
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2488]
.L427:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #2496]
.L428:
  ldr d1, [sp, #2488]
  ldr d2, [sp, #2496]
  fadd d0, d1, d2
  str d0, [sp, #2504]
.L429:
  ldr x1, [sp, #2408]
  mov x0, #6177
  cmp x1, x0
  b.hs .Lbounds_err
  ldr d0, [sp, #2504]
  adrp x0, _arr_h@PAGE
  add x0, x0, _arr_h@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L430:
  mov x0, #1
  str x0, [sp, #2512]
.L431:
  ldr x1, [sp, #8]
  ldr x2, [sp, #2512]
  add x0, x1, x2
  str x0, [sp, #8]
.L432:
  b .L220
.L433:
  mov x0, #1
  str x0, [sp, #2520]
.L434:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2520]
  add x0, x1, x2
  str x0, [sp, #16]
.L435:
  b .L177
.L436:
  mov x0, #1
  str x0, [sp, #2528]
.L437:
  mov x0, #1
  str x0, [sp, #2536]
.L438:
  ldr x1, [sp, #2528]
  ldr x2, [sp, #2536]
  sub x0, x1, x2
  str x0, [sp, #2544]
.L439:
  mov x0, #64
  str x0, [sp, #2552]
.L440:
  ldr x1, [sp, #2544]
  ldr x2, [sp, #2552]
  mul x0, x1, x2
  str x0, [sp, #2560]
.L441:
  mov x0, #1
  str x0, [sp, #2568]
.L442:
  ldr x1, [sp, #2560]
  ldr x2, [sp, #2568]
  add x0, x1, x2
  str x0, [sp, #2576]
.L443:
  ldr x1, [sp, #2576]
  adrp x0, _arr_p@PAGE
  add x0, x0, _arr_p@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2584]
.L444:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #2584]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_444@PAGE
  add x0, x0, .Lfmt_print_444@PAGEOFF
  bl _printf
  add sp, sp, #16
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
  ldr d0, [sp, #56]
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
  ldr d0, [sp, #64]
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
  ldr d0, [sp, #72]
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
  ldr d0, [sp, #80]
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
  ldr d0, [sp, #88]
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
  ldr x29, [sp, #2592]
  ldr x30, [sp, #2600]
  add sp, sp, #2608
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

.Lfmt_print_444:
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
