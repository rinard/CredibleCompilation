.global _main
.align 2

_main:
  sub sp, sp, #2864
  str x30, [sp, #2856]
  str x29, [sp, #2848]
  add x29, sp, #2848

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
  str x0, [sp, #2592]
  str x0, [sp, #2600]
  str x0, [sp, #2608]
  str x0, [sp, #2616]
  str x0, [sp, #2624]
  str x0, [sp, #2632]
  str x0, [sp, #2640]
  str x0, [sp, #2648]
  str x0, [sp, #2656]
  str x0, [sp, #2664]
  str x0, [sp, #2672]
  str x0, [sp, #2680]
  str x0, [sp, #2688]
  str x0, [sp, #2696]
  str x0, [sp, #2704]
  str x0, [sp, #2712]
  str x0, [sp, #2720]
  str x0, [sp, #2728]
  str x0, [sp, #2736]
  str x0, [sp, #2744]
  str x0, [sp, #2752]
  str x0, [sp, #2760]
  str x0, [sp, #2768]
  str x0, [sp, #2776]
  str x0, [sp, #2784]
  str x0, [sp, #2792]
  str x0, [sp, #2800]
  str x0, [sp, #2808]
  str x0, [sp, #2816]
  str x0, [sp, #2824]
  str x0, [sp, #2832]

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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L12:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L13:
  ldr d1, [sp, #96]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L14:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #104]
.L15:
  ldr d1, [sp, #104]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L16:
  mov x0, #1
  str x0, [sp, #16]
.L17:
  mov x0, #25
  str x0, [sp, #112]
.L18:
  ldr x1, [sp, #16]
  ldr x2, [sp, #112]
  cmp x1, x2
  b.gt .L43
.L19:
  mov x0, #1
  str x0, [sp, #24]
.L20:
  mov x0, #101
  str x0, [sp, #120]
.L21:
  ldr x1, [sp, #24]
  ldr x2, [sp, #120]
  cmp x1, x2
  b.gt .L40
.L22:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #128]
.L23:
  ldr d1, [sp, #128]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #136]
.L24:
  ldr d1, [sp, #136]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #144]
.L25:
  ldr d1, [sp, #144]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L26:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #152]
.L27:
  ldr d1, [sp, #152]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L28:
  mov x0, #1
  str x0, [sp, #160]
.L29:
  ldr x1, [sp, #16]
  ldr x2, [sp, #160]
  sub x0, x1, x2
  str x0, [sp, #168]
.L30:
  mov x0, #101
  str x0, [sp, #176]
.L31:
  ldr x1, [sp, #168]
  ldr x2, [sp, #176]
  mul x0, x1, x2
  str x0, [sp, #184]
.L32:
  ldr x1, [sp, #184]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #192]
.L33:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #200]
.L34:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #208]
.L35:
  ldr d1, [sp, #200]
  ldr d2, [sp, #208]
  fmul d0, d1, d2
  str d0, [sp, #216]
.L36:
  ldr x1, [sp, #192]
  ldr d0, [sp, #216]
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L37:
  mov x0, #1
  str x0, [sp, #224]
.L38:
  ldr x1, [sp, #24]
  ldr x2, [sp, #224]
  add x0, x1, x2
  str x0, [sp, #24]
.L39:
  b .L20
.L40:
  mov x0, #1
  str x0, [sp, #232]
.L41:
  ldr x1, [sp, #16]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #16]
.L42:
  b .L17
.L43:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L44:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #240]
.L45:
  ldr d1, [sp, #240]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L46:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #248]
.L47:
  ldr d1, [sp, #248]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L48:
  mov x0, #1
  str x0, [sp, #16]
.L49:
  mov x0, #7
  str x0, [sp, #256]
.L50:
  ldr x1, [sp, #16]
  ldr x2, [sp, #256]
  cmp x1, x2
  b.gt .L75
.L51:
  mov x0, #1
  str x0, [sp, #24]
.L52:
  mov x0, #101
  str x0, [sp, #264]
.L53:
  ldr x1, [sp, #24]
  ldr x2, [sp, #264]
  cmp x1, x2
  b.gt .L72
.L54:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #272]
.L55:
  ldr d1, [sp, #272]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #280]
.L56:
  ldr d1, [sp, #280]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #288]
.L57:
  ldr d1, [sp, #288]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L58:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #296]
.L59:
  ldr d1, [sp, #296]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L60:
  mov x0, #1
  str x0, [sp, #304]
.L61:
  ldr x1, [sp, #16]
  ldr x2, [sp, #304]
  sub x0, x1, x2
  str x0, [sp, #312]
.L62:
  mov x0, #101
  str x0, [sp, #320]
.L63:
  ldr x1, [sp, #312]
  ldr x2, [sp, #320]
  mul x0, x1, x2
  str x0, [sp, #328]
.L64:
  ldr x1, [sp, #328]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #336]
.L65:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #344]
.L66:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #352]
.L67:
  ldr d1, [sp, #344]
  ldr d2, [sp, #352]
  fmul d0, d1, d2
  str d0, [sp, #360]
.L68:
  ldr x1, [sp, #336]
  ldr d0, [sp, #360]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L69:
  mov x0, #1
  str x0, [sp, #368]
.L70:
  ldr x1, [sp, #24]
  ldr x2, [sp, #368]
  add x0, x1, x2
  str x0, [sp, #24]
.L71:
  b .L52
.L72:
  mov x0, #1
  str x0, [sp, #376]
.L73:
  ldr x1, [sp, #16]
  ldr x2, [sp, #376]
  add x0, x1, x2
  str x0, [sp, #16]
.L74:
  b .L49
.L75:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L76:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #384]
.L77:
  ldr d1, [sp, #384]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L78:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #392]
.L79:
  ldr d1, [sp, #392]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L80:
  mov x0, #1
  str x0, [sp, #16]
.L81:
  mov x0, #7
  str x0, [sp, #400]
.L82:
  ldr x1, [sp, #16]
  ldr x2, [sp, #400]
  cmp x1, x2
  b.gt .L123
.L83:
  mov x0, #1
  str x0, [sp, #24]
.L84:
  mov x0, #101
  str x0, [sp, #408]
.L85:
  ldr x1, [sp, #24]
  ldr x2, [sp, #408]
  cmp x1, x2
  b.gt .L120
.L86:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #416]
.L87:
  ldr d1, [sp, #416]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #424]
.L88:
  ldr d1, [sp, #424]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #432]
.L89:
  ldr d1, [sp, #432]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L90:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #440]
.L91:
  ldr d1, [sp, #440]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L92:
  mov x0, #1
  str x0, [sp, #448]
.L93:
  ldr x1, [sp, #16]
  ldr x2, [sp, #448]
  sub x0, x1, x2
  str x0, [sp, #456]
.L94:
  mov x0, #101
  str x0, [sp, #464]
.L95:
  ldr x1, [sp, #456]
  ldr x2, [sp, #464]
  mul x0, x1, x2
  str x0, [sp, #472]
.L96:
  ldr x1, [sp, #472]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #480]
.L97:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #488]
.L98:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #496]
.L99:
  ldr d1, [sp, #488]
  ldr d2, [sp, #496]
  fmul d0, d1, d2
  str d0, [sp, #504]
.L100:
  ldr x1, [sp, #480]
  ldr d0, [sp, #504]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L101:
  mov x0, #1
  str x0, [sp, #512]
.L102:
  ldr x1, [sp, #16]
  ldr x2, [sp, #512]
  sub x0, x1, x2
  str x0, [sp, #520]
.L103:
  mov x0, #101
  str x0, [sp, #528]
.L104:
  ldr x1, [sp, #520]
  ldr x2, [sp, #528]
  mul x0, x1, x2
  str x0, [sp, #536]
.L105:
  ldr x1, [sp, #536]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #544]
.L106:
  ldr x1, [sp, #544]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #552]
.L107:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #560]
.L108:
  ldr d1, [sp, #552]
  ldr d2, [sp, #560]
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L110
.L109:
  b .L117
.L110:
  mov x0, #1
  str x0, [sp, #568]
.L111:
  ldr x1, [sp, #16]
  ldr x2, [sp, #568]
  sub x0, x1, x2
  str x0, [sp, #576]
.L112:
  mov x0, #101
  str x0, [sp, #584]
.L113:
  ldr x1, [sp, #576]
  ldr x2, [sp, #584]
  mul x0, x1, x2
  str x0, [sp, #592]
.L114:
  ldr x1, [sp, #592]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #600]
.L115:
  movz x0, #43516
  movk x0, #54001, lsl #16
  movk x0, #25165, lsl #32
  movk x0, #16208, lsl #48
  fmov d0, x0
  str d0, [sp, #608]
.L116:
  ldr x1, [sp, #600]
  ldr d0, [sp, #608]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L117:
  mov x0, #1
  str x0, [sp, #616]
.L118:
  ldr x1, [sp, #24]
  ldr x2, [sp, #616]
  add x0, x1, x2
  str x0, [sp, #24]
.L119:
  b .L84
.L120:
  mov x0, #1
  str x0, [sp, #624]
.L121:
  ldr x1, [sp, #16]
  ldr x2, [sp, #624]
  add x0, x1, x2
  str x0, [sp, #16]
.L122:
  b .L81
.L123:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L124:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #632]
.L125:
  ldr d1, [sp, #632]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L126:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #640]
.L127:
  ldr d1, [sp, #640]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L128:
  mov x0, #1
  str x0, [sp, #16]
.L129:
  mov x0, #7
  str x0, [sp, #648]
.L130:
  ldr x1, [sp, #16]
  ldr x2, [sp, #648]
  cmp x1, x2
  b.gt .L155
.L131:
  mov x0, #1
  str x0, [sp, #24]
.L132:
  mov x0, #101
  str x0, [sp, #656]
.L133:
  ldr x1, [sp, #24]
  ldr x2, [sp, #656]
  cmp x1, x2
  b.gt .L152
.L134:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #664]
.L135:
  ldr d1, [sp, #664]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #672]
.L136:
  ldr d1, [sp, #672]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #680]
.L137:
  ldr d1, [sp, #680]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L138:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #688]
.L139:
  ldr d1, [sp, #688]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L140:
  mov x0, #1
  str x0, [sp, #696]
.L141:
  ldr x1, [sp, #16]
  ldr x2, [sp, #696]
  sub x0, x1, x2
  str x0, [sp, #704]
.L142:
  mov x0, #101
  str x0, [sp, #712]
.L143:
  ldr x1, [sp, #704]
  ldr x2, [sp, #712]
  mul x0, x1, x2
  str x0, [sp, #720]
.L144:
  ldr x1, [sp, #720]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #728]
.L145:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #736]
.L146:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #744]
.L147:
  ldr d1, [sp, #736]
  ldr d2, [sp, #744]
  fmul d0, d1, d2
  str d0, [sp, #752]
.L148:
  ldr x1, [sp, #728]
  ldr d0, [sp, #752]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L149:
  mov x0, #1
  str x0, [sp, #760]
.L150:
  ldr x1, [sp, #24]
  ldr x2, [sp, #760]
  add x0, x1, x2
  str x0, [sp, #24]
.L151:
  b .L132
.L152:
  mov x0, #1
  str x0, [sp, #768]
.L153:
  ldr x1, [sp, #16]
  ldr x2, [sp, #768]
  add x0, x1, x2
  str x0, [sp, #16]
.L154:
  b .L129
.L155:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L156:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #776]
.L157:
  ldr d1, [sp, #776]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L158:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #784]
.L159:
  ldr d1, [sp, #784]
  ldr d2, [sp, #72]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L160:
  mov x0, #1
  str x0, [sp, #16]
.L161:
  mov x0, #7
  str x0, [sp, #792]
.L162:
  ldr x1, [sp, #16]
  ldr x2, [sp, #792]
  cmp x1, x2
  b.gt .L187
.L163:
  mov x0, #1
  str x0, [sp, #24]
.L164:
  mov x0, #101
  str x0, [sp, #800]
.L165:
  ldr x1, [sp, #24]
  ldr x2, [sp, #800]
  cmp x1, x2
  b.gt .L184
.L166:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #808]
.L167:
  ldr d1, [sp, #808]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #816]
.L168:
  ldr d1, [sp, #816]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #824]
.L169:
  ldr d1, [sp, #824]
  ldr d2, [sp, #72]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L170:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #832]
.L171:
  ldr d1, [sp, #832]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L172:
  mov x0, #1
  str x0, [sp, #840]
.L173:
  ldr x1, [sp, #16]
  ldr x2, [sp, #840]
  sub x0, x1, x2
  str x0, [sp, #848]
.L174:
  mov x0, #101
  str x0, [sp, #856]
.L175:
  ldr x1, [sp, #848]
  ldr x2, [sp, #856]
  mul x0, x1, x2
  str x0, [sp, #864]
.L176:
  ldr x1, [sp, #864]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #872]
.L177:
  ldr d1, [sp, #80]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #880]
.L178:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #888]
.L179:
  ldr d1, [sp, #880]
  ldr d2, [sp, #888]
  fmul d0, d1, d2
  str d0, [sp, #896]
.L180:
  ldr x1, [sp, #872]
  ldr d0, [sp, #896]
  adrp x0, _arr_vs@PAGE
  add x0, x0, _arr_vs@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L181:
  mov x0, #1
  str x0, [sp, #904]
.L182:
  ldr x1, [sp, #24]
  ldr x2, [sp, #904]
  add x0, x1, x2
  str x0, [sp, #24]
.L183:
  b .L164
.L184:
  mov x0, #1
  str x0, [sp, #912]
.L185:
  ldr x1, [sp, #16]
  ldr x2, [sp, #912]
  add x0, x1, x2
  str x0, [sp, #16]
.L186:
  b .L161
.L187:
  mov x0, #1
  str x0, [sp, #8]
.L188:
  movz x0, #54696
  movk x0, #64, lsl #16
  str x0, [sp, #920]
.L189:
  ldr x1, [sp, #8]
  ldr x2, [sp, #920]
  cmp x1, x2
  b.gt .L471
.L190:
  movz x0, #16777
  movk x0, #58720, lsl #16
  movk x0, #8912, lsl #32
  movk x0, #16299, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L191:
  movz x0, #42467
  movk x0, #50331, lsl #16
  movk x0, #45088, lsl #32
  movk x0, #16306, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L192:
  mov x0, #2
  str x0, [sp, #16]
.L193:
  mov x0, #7
  str x0, [sp, #928]
.L194:
  ldr x1, [sp, #16]
  ldr x2, [sp, #928]
  cmp x1, x2
  b.gt .L468
.L195:
  mov x0, #2
  str x0, [sp, #24]
.L196:
  mov x0, #101
  str x0, [sp, #936]
.L197:
  ldr x1, [sp, #24]
  ldr x2, [sp, #936]
  cmp x1, x2
  b.gt .L465
.L198:
  mov x0, #7
  str x0, [sp, #944]
.L199:
  ldr x1, [sp, #944]
  ldr x2, [sp, #16]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L455
.L200:
  mov x0, #1
  str x0, [sp, #952]
.L201:
  ldr x1, [sp, #16]
  ldr x2, [sp, #952]
  sub x0, x1, x2
  str x0, [sp, #960]
.L202:
  mov x0, #101
  str x0, [sp, #968]
.L203:
  ldr x1, [sp, #960]
  ldr x2, [sp, #968]
  mul x0, x1, x2
  str x0, [sp, #976]
.L204:
  ldr x1, [sp, #976]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #984]
.L205:
  ldr x1, [sp, #984]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #992]
.L206:
  mov x0, #101
  str x0, [sp, #1000]
.L207:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1000]
  mul x0, x1, x2
  str x0, [sp, #1008]
.L208:
  ldr x1, [sp, #1008]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1016]
.L209:
  ldr x1, [sp, #1016]
  cmp x1, #708
  b.hs .Lbounds_err
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1024]
.L210:
  ldr d1, [sp, #992]
  ldr d2, [sp, #1024]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L213
.L211:
  ldr x0, [sp, #40]
  str x0, [sp, #64]
.L212:
  b .L214
.L213:
  ldr x0, [sp, #32]
  str x0, [sp, #64]
.L214:
  mov x0, #1
  str x0, [sp, #1032]
.L215:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1032]
  sub x0, x1, x2
  str x0, [sp, #1040]
.L216:
  mov x0, #101
  str x0, [sp, #1048]
.L217:
  ldr x1, [sp, #1040]
  ldr x2, [sp, #1048]
  mul x0, x1, x2
  str x0, [sp, #1056]
.L218:
  ldr x1, [sp, #1056]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1064]
.L219:
  ldr x1, [sp, #1064]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1072]
.L220:
  mov x0, #1
  str x0, [sp, #1080]
.L221:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1080]
  sub x0, x1, x2
  str x0, [sp, #1088]
.L222:
  mov x0, #101
  str x0, [sp, #1096]
.L223:
  ldr x1, [sp, #1088]
  ldr x2, [sp, #1096]
  mul x0, x1, x2
  str x0, [sp, #1104]
.L224:
  ldr x1, [sp, #1104]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1112]
.L225:
  mov x0, #1
  str x0, [sp, #1120]
.L226:
  ldr x1, [sp, #1112]
  ldr x2, [sp, #1120]
  sub x0, x1, x2
  str x0, [sp, #1128]
.L227:
  ldr x1, [sp, #1128]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1136]
.L228:
  ldr d1, [sp, #1072]
  ldr d2, [sp, #1136]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L261
.L229:
  mov x0, #101
  str x0, [sp, #1144]
.L230:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1144]
  mul x0, x1, x2
  str x0, [sp, #1152]
.L231:
  ldr x1, [sp, #1152]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1160]
.L232:
  ldr x1, [sp, #1160]
  cmp x1, #708
  b.hs .Lbounds_err
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1168]
.L233:
  mov x0, #1
  str x0, [sp, #1176]
.L234:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1176]
  sub x0, x1, x2
  str x0, [sp, #1184]
.L235:
  mov x0, #101
  str x0, [sp, #1192]
.L236:
  ldr x1, [sp, #1184]
  ldr x2, [sp, #1192]
  mul x0, x1, x2
  str x0, [sp, #1200]
.L237:
  ldr x1, [sp, #1200]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1208]
.L238:
  ldr x1, [sp, #1208]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1216]
.L239:
  ldr d1, [sp, #1168]
  ldr d2, [sp, #1216]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L246
.L240:
  mov x0, #101
  str x0, [sp, #1224]
.L241:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1224]
  mul x0, x1, x2
  str x0, [sp, #1232]
.L242:
  ldr x1, [sp, #1232]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1240]
.L243:
  ldr x1, [sp, #1240]
  cmp x1, #708
  b.hs .Lbounds_err
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1248]
.L244:
  ldr x0, [sp, #1248]
  str x0, [sp, #48]
.L245:
  b .L253
.L246:
  mov x0, #1
  str x0, [sp, #1256]
.L247:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1256]
  sub x0, x1, x2
  str x0, [sp, #1264]
.L248:
  mov x0, #101
  str x0, [sp, #1272]
.L249:
  ldr x1, [sp, #1264]
  ldr x2, [sp, #1272]
  mul x0, x1, x2
  str x0, [sp, #1280]
.L250:
  ldr x1, [sp, #1280]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1288]
.L251:
  ldr x1, [sp, #1288]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1296]
.L252:
  ldr x0, [sp, #1296]
  str x0, [sp, #48]
.L253:
  mov x0, #1
  str x0, [sp, #1304]
.L254:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1304]
  sub x0, x1, x2
  str x0, [sp, #1312]
.L255:
  mov x0, #101
  str x0, [sp, #1320]
.L256:
  ldr x1, [sp, #1312]
  ldr x2, [sp, #1320]
  mul x0, x1, x2
  str x0, [sp, #1328]
.L257:
  ldr x1, [sp, #1328]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1336]
.L258:
  ldr x1, [sp, #1336]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1344]
.L259:
  ldr x0, [sp, #1344]
  str x0, [sp, #56]
.L260:
  b .L302
.L261:
  mov x0, #101
  str x0, [sp, #1352]
.L262:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1352]
  mul x0, x1, x2
  str x0, [sp, #1360]
.L263:
  ldr x1, [sp, #1360]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1368]
.L264:
  mov x0, #1
  str x0, [sp, #1376]
.L265:
  ldr x1, [sp, #1368]
  ldr x2, [sp, #1376]
  sub x0, x1, x2
  str x0, [sp, #1384]
.L266:
  ldr x1, [sp, #1384]
  cmp x1, #708
  b.hs .Lbounds_err
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1392]
.L267:
  mov x0, #1
  str x0, [sp, #1400]
.L268:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1400]
  sub x0, x1, x2
  str x0, [sp, #1408]
.L269:
  mov x0, #101
  str x0, [sp, #1416]
.L270:
  ldr x1, [sp, #1408]
  ldr x2, [sp, #1416]
  mul x0, x1, x2
  str x0, [sp, #1424]
.L271:
  ldr x1, [sp, #1424]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1432]
.L272:
  mov x0, #1
  str x0, [sp, #1440]
.L273:
  ldr x1, [sp, #1432]
  ldr x2, [sp, #1440]
  sub x0, x1, x2
  str x0, [sp, #1448]
.L274:
  ldr x1, [sp, #1448]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1456]
.L275:
  ldr d1, [sp, #1392]
  ldr d2, [sp, #1456]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L284
.L276:
  mov x0, #101
  str x0, [sp, #1464]
.L277:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1464]
  mul x0, x1, x2
  str x0, [sp, #1472]
.L278:
  ldr x1, [sp, #1472]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1480]
.L279:
  mov x0, #1
  str x0, [sp, #1488]
.L280:
  ldr x1, [sp, #1480]
  ldr x2, [sp, #1488]
  sub x0, x1, x2
  str x0, [sp, #1496]
.L281:
  ldr x1, [sp, #1496]
  cmp x1, #708
  b.hs .Lbounds_err
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1504]
.L282:
  ldr x0, [sp, #1504]
  str x0, [sp, #48]
.L283:
  b .L293
.L284:
  mov x0, #1
  str x0, [sp, #1512]
.L285:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1512]
  sub x0, x1, x2
  str x0, [sp, #1520]
.L286:
  mov x0, #101
  str x0, [sp, #1528]
.L287:
  ldr x1, [sp, #1520]
  ldr x2, [sp, #1528]
  mul x0, x1, x2
  str x0, [sp, #1536]
.L288:
  ldr x1, [sp, #1536]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1544]
.L289:
  mov x0, #1
  str x0, [sp, #1552]
.L290:
  ldr x1, [sp, #1544]
  ldr x2, [sp, #1552]
  sub x0, x1, x2
  str x0, [sp, #1560]
.L291:
  ldr x1, [sp, #1560]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1568]
.L292:
  ldr x0, [sp, #1568]
  str x0, [sp, #48]
.L293:
  mov x0, #1
  str x0, [sp, #1576]
.L294:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1576]
  sub x0, x1, x2
  str x0, [sp, #1584]
.L295:
  mov x0, #101
  str x0, [sp, #1592]
.L296:
  ldr x1, [sp, #1584]
  ldr x2, [sp, #1592]
  mul x0, x1, x2
  str x0, [sp, #1600]
.L297:
  ldr x1, [sp, #1600]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1608]
.L298:
  mov x0, #1
  str x0, [sp, #1616]
.L299:
  ldr x1, [sp, #1608]
  ldr x2, [sp, #1616]
  sub x0, x1, x2
  str x0, [sp, #1624]
.L300:
  ldr x1, [sp, #1624]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1632]
.L301:
  ldr x0, [sp, #1632]
  str x0, [sp, #56]
.L302:
  mov x0, #1
  str x0, [sp, #1640]
.L303:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1640]
  sub x0, x1, x2
  str x0, [sp, #1648]
.L304:
  mov x0, #101
  str x0, [sp, #1656]
.L305:
  ldr x1, [sp, #1648]
  ldr x2, [sp, #1656]
  mul x0, x1, x2
  str x0, [sp, #1664]
.L306:
  ldr x1, [sp, #1664]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1672]
.L307:
  mov x0, #1
  str x0, [sp, #1680]
.L308:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1680]
  sub x0, x1, x2
  str x0, [sp, #1688]
.L309:
  mov x0, #101
  str x0, [sp, #1696]
.L310:
  ldr x1, [sp, #1688]
  ldr x2, [sp, #1696]
  mul x0, x1, x2
  str x0, [sp, #1704]
.L311:
  ldr x1, [sp, #1704]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1712]
.L312:
  ldr x1, [sp, #1712]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1720]
.L313:
  mov x0, #1
  str x0, [sp, #1728]
.L314:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1728]
  sub x0, x1, x2
  str x0, [sp, #1736]
.L315:
  mov x0, #101
  str x0, [sp, #1744]
.L316:
  ldr x1, [sp, #1736]
  ldr x2, [sp, #1744]
  mul x0, x1, x2
  str x0, [sp, #1752]
.L317:
  ldr x1, [sp, #1752]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1760]
.L318:
  ldr x1, [sp, #1760]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1768]
.L319:
  ldr d1, [sp, #1720]
  ldr d2, [sp, #1768]
  fmul d0, d1, d2
  str d0, [sp, #1776]
.L320:
  ldr d1, [sp, #48]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #1784]
.L321:
  ldr d1, [sp, #1776]
  ldr d2, [sp, #1784]
  fadd d0, d1, d2
  str d0, [sp, #1792]
.L322:
  ldr d0, [sp, #1792]
  fsqrt d0, d0
  str d0, [sp, #1800]
.L323:
  ldr d1, [sp, #1800]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #1808]
.L324:
  ldr d1, [sp, #1808]
  ldr d2, [sp, #56]
  fdiv d0, d1, d2
  str d0, [sp, #1816]
.L325:
  ldr x1, [sp, #1672]
  ldr d0, [sp, #1816]
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L326:
  mov x0, #101
  str x0, [sp, #1824]
.L327:
  ldr x1, [sp, #1824]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L447
.L328:
  mov x0, #1
  str x0, [sp, #1832]
.L329:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1832]
  sub x0, x1, x2
  str x0, [sp, #1840]
.L330:
  mov x0, #101
  str x0, [sp, #1848]
.L331:
  ldr x1, [sp, #1840]
  ldr x2, [sp, #1848]
  mul x0, x1, x2
  str x0, [sp, #1856]
.L332:
  ldr x1, [sp, #1856]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1864]
.L333:
  ldr x1, [sp, #1864]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1872]
.L334:
  mov x0, #2
  str x0, [sp, #1880]
.L335:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1880]
  sub x0, x1, x2
  str x0, [sp, #1888]
.L336:
  mov x0, #101
  str x0, [sp, #1896]
.L337:
  ldr x1, [sp, #1888]
  ldr x2, [sp, #1896]
  mul x0, x1, x2
  str x0, [sp, #1904]
.L338:
  ldr x1, [sp, #1904]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1912]
.L339:
  ldr x1, [sp, #1912]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1920]
.L340:
  ldr d1, [sp, #1872]
  ldr d2, [sp, #1920]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L382
.L341:
  mov x0, #1
  str x0, [sp, #1928]
.L342:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1928]
  sub x0, x1, x2
  str x0, [sp, #1936]
.L343:
  mov x0, #101
  str x0, [sp, #1944]
.L344:
  ldr x1, [sp, #1936]
  ldr x2, [sp, #1944]
  mul x0, x1, x2
  str x0, [sp, #1952]
.L345:
  ldr x1, [sp, #1952]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #1960]
.L346:
  mov x0, #1
  str x0, [sp, #1968]
.L347:
  ldr x1, [sp, #1960]
  ldr x2, [sp, #1968]
  add x0, x1, x2
  str x0, [sp, #1976]
.L348:
  ldr x1, [sp, #1976]
  cmp x1, #708
  b.hs .Lbounds_err
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1984]
.L349:
  mov x0, #1
  str x0, [sp, #1992]
.L350:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1992]
  sub x0, x1, x2
  str x0, [sp, #2000]
.L351:
  mov x0, #101
  str x0, [sp, #2008]
.L352:
  ldr x1, [sp, #2000]
  ldr x2, [sp, #2008]
  mul x0, x1, x2
  str x0, [sp, #2016]
.L353:
  ldr x1, [sp, #2016]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2024]
.L354:
  ldr x1, [sp, #2024]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2032]
.L355:
  ldr d1, [sp, #1984]
  ldr d2, [sp, #2032]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L366
.L356:
  mov x0, #1
  str x0, [sp, #2040]
.L357:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2040]
  sub x0, x1, x2
  str x0, [sp, #2048]
.L358:
  mov x0, #101
  str x0, [sp, #2056]
.L359:
  ldr x1, [sp, #2048]
  ldr x2, [sp, #2056]
  mul x0, x1, x2
  str x0, [sp, #2064]
.L360:
  ldr x1, [sp, #2064]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2072]
.L361:
  mov x0, #1
  str x0, [sp, #2080]
.L362:
  ldr x1, [sp, #2072]
  ldr x2, [sp, #2080]
  add x0, x1, x2
  str x0, [sp, #2088]
.L363:
  ldr x1, [sp, #2088]
  cmp x1, #708
  b.hs .Lbounds_err
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2096]
.L364:
  ldr x0, [sp, #2096]
  str x0, [sp, #48]
.L365:
  b .L373
.L366:
  mov x0, #1
  str x0, [sp, #2104]
.L367:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2104]
  sub x0, x1, x2
  str x0, [sp, #2112]
.L368:
  mov x0, #101
  str x0, [sp, #2120]
.L369:
  ldr x1, [sp, #2112]
  ldr x2, [sp, #2120]
  mul x0, x1, x2
  str x0, [sp, #2128]
.L370:
  ldr x1, [sp, #2128]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2136]
.L371:
  ldr x1, [sp, #2136]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2144]
.L372:
  ldr x0, [sp, #2144]
  str x0, [sp, #48]
.L373:
  mov x0, #1
  str x0, [sp, #2152]
.L374:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2152]
  sub x0, x1, x2
  str x0, [sp, #2160]
.L375:
  mov x0, #101
  str x0, [sp, #2168]
.L376:
  ldr x1, [sp, #2160]
  ldr x2, [sp, #2168]
  mul x0, x1, x2
  str x0, [sp, #2176]
.L377:
  ldr x1, [sp, #2176]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2184]
.L378:
  ldr x1, [sp, #2184]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2192]
.L379:
  ldr x0, [sp, #2192]
  str x0, [sp, #56]
.L380:
  ldr x0, [sp, #32]
  str x0, [sp, #64]
.L381:
  b .L422
.L382:
  mov x0, #2
  str x0, [sp, #2200]
.L383:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2200]
  sub x0, x1, x2
  str x0, [sp, #2208]
.L384:
  mov x0, #101
  str x0, [sp, #2216]
.L385:
  ldr x1, [sp, #2208]
  ldr x2, [sp, #2216]
  mul x0, x1, x2
  str x0, [sp, #2224]
.L386:
  ldr x1, [sp, #2224]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2232]
.L387:
  mov x0, #1
  str x0, [sp, #2240]
.L388:
  ldr x1, [sp, #2232]
  ldr x2, [sp, #2240]
  add x0, x1, x2
  str x0, [sp, #2248]
.L389:
  ldr x1, [sp, #2248]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2256]
.L390:
  mov x0, #2
  str x0, [sp, #2264]
.L391:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2264]
  sub x0, x1, x2
  str x0, [sp, #2272]
.L392:
  mov x0, #101
  str x0, [sp, #2280]
.L393:
  ldr x1, [sp, #2272]
  ldr x2, [sp, #2280]
  mul x0, x1, x2
  str x0, [sp, #2288]
.L394:
  ldr x1, [sp, #2288]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2296]
.L395:
  ldr x1, [sp, #2296]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2304]
.L396:
  ldr d1, [sp, #2256]
  ldr d2, [sp, #2304]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L407
.L397:
  mov x0, #2
  str x0, [sp, #2312]
.L398:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2312]
  sub x0, x1, x2
  str x0, [sp, #2320]
.L399:
  mov x0, #101
  str x0, [sp, #2328]
.L400:
  ldr x1, [sp, #2320]
  ldr x2, [sp, #2328]
  mul x0, x1, x2
  str x0, [sp, #2336]
.L401:
  ldr x1, [sp, #2336]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2344]
.L402:
  mov x0, #1
  str x0, [sp, #2352]
.L403:
  ldr x1, [sp, #2344]
  ldr x2, [sp, #2352]
  add x0, x1, x2
  str x0, [sp, #2360]
.L404:
  ldr x1, [sp, #2360]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2368]
.L405:
  ldr x0, [sp, #2368]
  str x0, [sp, #48]
.L406:
  b .L414
.L407:
  mov x0, #2
  str x0, [sp, #2376]
.L408:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2376]
  sub x0, x1, x2
  str x0, [sp, #2384]
.L409:
  mov x0, #101
  str x0, [sp, #2392]
.L410:
  ldr x1, [sp, #2384]
  ldr x2, [sp, #2392]
  mul x0, x1, x2
  str x0, [sp, #2400]
.L411:
  ldr x1, [sp, #2400]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2408]
.L412:
  ldr x1, [sp, #2408]
  adrp x0, _arr_vg@PAGE
  add x0, x0, _arr_vg@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2416]
.L413:
  ldr x0, [sp, #2416]
  str x0, [sp, #48]
.L414:
  mov x0, #2
  str x0, [sp, #2424]
.L415:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2424]
  sub x0, x1, x2
  str x0, [sp, #2432]
.L416:
  mov x0, #101
  str x0, [sp, #2440]
.L417:
  ldr x1, [sp, #2432]
  ldr x2, [sp, #2440]
  mul x0, x1, x2
  str x0, [sp, #2448]
.L418:
  ldr x1, [sp, #2448]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2456]
.L419:
  ldr x1, [sp, #2456]
  adrp x0, _arr_vf@PAGE
  add x0, x0, _arr_vf@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2464]
.L420:
  ldr x0, [sp, #2464]
  str x0, [sp, #56]
.L421:
  ldr x0, [sp, #40]
  str x0, [sp, #64]
.L422:
  mov x0, #1
  str x0, [sp, #2472]
.L423:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2472]
  sub x0, x1, x2
  str x0, [sp, #2480]
.L424:
  mov x0, #101
  str x0, [sp, #2488]
.L425:
  ldr x1, [sp, #2480]
  ldr x2, [sp, #2488]
  mul x0, x1, x2
  str x0, [sp, #2496]
.L426:
  ldr x1, [sp, #2496]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2504]
.L427:
  mov x0, #1
  str x0, [sp, #2512]
.L428:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2512]
  sub x0, x1, x2
  str x0, [sp, #2520]
.L429:
  mov x0, #101
  str x0, [sp, #2528]
.L430:
  ldr x1, [sp, #2520]
  ldr x2, [sp, #2528]
  mul x0, x1, x2
  str x0, [sp, #2536]
.L431:
  ldr x1, [sp, #2536]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2544]
.L432:
  ldr x1, [sp, #2544]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2552]
.L433:
  mov x0, #1
  str x0, [sp, #2560]
.L434:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2560]
  sub x0, x1, x2
  str x0, [sp, #2568]
.L435:
  mov x0, #101
  str x0, [sp, #2576]
.L436:
  ldr x1, [sp, #2568]
  ldr x2, [sp, #2576]
  mul x0, x1, x2
  str x0, [sp, #2584]
.L437:
  ldr x1, [sp, #2584]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2592]
.L438:
  ldr x1, [sp, #2592]
  adrp x0, _arr_vh@PAGE
  add x0, x0, _arr_vh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2600]
.L439:
  ldr d1, [sp, #2552]
  ldr d2, [sp, #2600]
  fmul d0, d1, d2
  str d0, [sp, #2608]
.L440:
  ldr d1, [sp, #48]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #2616]
.L441:
  ldr d1, [sp, #2608]
  ldr d2, [sp, #2616]
  fadd d0, d1, d2
  str d0, [sp, #2624]
.L442:
  ldr d0, [sp, #2624]
  fsqrt d0, d0
  str d0, [sp, #2632]
.L443:
  ldr d1, [sp, #2632]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #2640]
.L444:
  ldr d1, [sp, #2640]
  ldr d2, [sp, #56]
  fdiv d0, d1, d2
  str d0, [sp, #2648]
.L445:
  ldr x1, [sp, #2504]
  ldr d0, [sp, #2648]
  adrp x0, _arr_vs@PAGE
  add x0, x0, _arr_vs@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L446:
  b .L454
.L447:
  mov x0, #1
  str x0, [sp, #2656]
.L448:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2656]
  sub x0, x1, x2
  str x0, [sp, #2664]
.L449:
  mov x0, #101
  str x0, [sp, #2672]
.L450:
  ldr x1, [sp, #2664]
  ldr x2, [sp, #2672]
  mul x0, x1, x2
  str x0, [sp, #2680]
.L451:
  ldr x1, [sp, #2680]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2688]
.L452:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #2696]
.L453:
  ldr x1, [sp, #2688]
  ldr d0, [sp, #2696]
  adrp x0, _arr_vs@PAGE
  add x0, x0, _arr_vs@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L454:
  b .L462
.L455:
  mov x0, #1
  str x0, [sp, #2704]
.L456:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2704]
  sub x0, x1, x2
  str x0, [sp, #2712]
.L457:
  mov x0, #101
  str x0, [sp, #2720]
.L458:
  ldr x1, [sp, #2712]
  ldr x2, [sp, #2720]
  mul x0, x1, x2
  str x0, [sp, #2728]
.L459:
  ldr x1, [sp, #2728]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #2736]
.L460:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #2744]
.L461:
  ldr x1, [sp, #2736]
  ldr d0, [sp, #2744]
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L462:
  mov x0, #1
  str x0, [sp, #2752]
.L463:
  ldr x1, [sp, #24]
  ldr x2, [sp, #2752]
  add x0, x1, x2
  str x0, [sp, #24]
.L464:
  b .L196
.L465:
  mov x0, #1
  str x0, [sp, #2760]
.L466:
  ldr x1, [sp, #16]
  ldr x2, [sp, #2760]
  add x0, x1, x2
  str x0, [sp, #16]
.L467:
  b .L193
.L468:
  mov x0, #1
  str x0, [sp, #2768]
.L469:
  ldr x1, [sp, #8]
  ldr x2, [sp, #2768]
  add x0, x1, x2
  str x0, [sp, #8]
.L470:
  b .L188
.L471:
  mov x0, #4
  str x0, [sp, #2776]
.L472:
  mov x0, #1
  str x0, [sp, #2784]
.L473:
  ldr x1, [sp, #2776]
  ldr x2, [sp, #2784]
  sub x0, x1, x2
  str x0, [sp, #2792]
.L474:
  mov x0, #101
  str x0, [sp, #2800]
.L475:
  ldr x1, [sp, #2792]
  ldr x2, [sp, #2800]
  mul x0, x1, x2
  str x0, [sp, #2808]
.L476:
  mov x0, #51
  str x0, [sp, #2816]
.L477:
  ldr x1, [sp, #2808]
  ldr x2, [sp, #2816]
  add x0, x1, x2
  str x0, [sp, #2824]
.L478:
  ldr x1, [sp, #2824]
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #2832]
.L479:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #2832]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_479@PAGE
  add x0, x0, .Lfmt_print_479@PAGEOFF
  bl _printf
  add sp, sp, #16
.L480:
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
  // print ar (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x1, .Lname_ar@PAGE
  add x1, x1, .Lname_ar@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print br (float)
  ldr d0, [sp, #40]
  sub sp, sp, #32
  adrp x1, .Lname_br@PAGE
  add x1, x1, .Lname_br@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print r (float)
  ldr d0, [sp, #48]
  sub sp, sp, #32
  adrp x1, .Lname_r@PAGE
  add x1, x1, .Lname_r@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print s (float)
  ldr d0, [sp, #56]
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
  ldr d0, [sp, #64]
  sub sp, sp, #32
  adrp x1, .Lname_t@PAGE
  add x1, x1, .Lname_t@PAGEOFF
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

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #2848]
  ldr x30, [sp, #2856]
  add sp, sp, #2864
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

.Lfmt_print_479:
  .asciz "%f\n"

.Lname_rep:
  .asciz "rep"
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_ar:
  .asciz "ar"
.Lname_br:
  .asciz "br"
.Lname_r:
  .asciz "r"
.Lname_s:
  .asciz "s"
.Lname_t:
  .asciz "t"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_vy
.align 3
_arr_vy:
  .space 20208
.global _arr_vh
.align 3
_arr_vh:
  .space 5664
.global _arr_vf
.align 3
_arr_vf:
  .space 5664
.global _arr_vg
.align 3
_arr_vg:
  .space 5664
.global _arr_vs
.align 3
_arr_vs:
  .space 5664
