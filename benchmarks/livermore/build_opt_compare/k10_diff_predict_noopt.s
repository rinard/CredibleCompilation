.global _main
.align 2

_main:
  sub sp, sp, #1088
  str x30, [sp, #1080]
  str x29, [sp, #1072]
  add x29, sp, #1072

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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L10:
  ldr d1, [sp, #72]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #80]
.L12:
  ldr d1, [sp, #80]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L13:
  mov x0, #1
  str x0, [sp, #8]
.L14:
  mov x0, #2525
  str x0, [sp, #88]
.L15:
  ldr x1, [sp, #8]
  ldr x2, [sp, #88]
  cmp x1, x2
  b.gt .L29
.L16:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L17:
  ldr d1, [sp, #96]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #104]
.L18:
  ldr d1, [sp, #104]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #112]
.L19:
  ldr d1, [sp, #112]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L20:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #120]
.L21:
  ldr d1, [sp, #120]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L22:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #128]
.L23:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #136]
.L24:
  ldr d1, [sp, #128]
  ldr d2, [sp, #136]
  fmul d0, d1, d2
  str d0, [sp, #144]
.L25:
  ldr x1, [sp, #8]
  ldr d0, [sp, #144]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L26:
  mov x0, #1
  str x0, [sp, #152]
.L27:
  ldr x1, [sp, #8]
  ldr x2, [sp, #152]
  add x0, x1, x2
  str x0, [sp, #8]
.L28:
  b .L14
.L29:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L30:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #160]
.L31:
  ldr d1, [sp, #160]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L32:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #168]
.L33:
  ldr d1, [sp, #168]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L34:
  mov x0, #1
  str x0, [sp, #8]
.L35:
  mov x0, #2525
  str x0, [sp, #176]
.L36:
  ldr x1, [sp, #8]
  ldr x2, [sp, #176]
  cmp x1, x2
  b.gt .L50
.L37:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #184]
.L38:
  ldr d1, [sp, #184]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L39:
  ldr d1, [sp, #192]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #200]
.L40:
  ldr d1, [sp, #200]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L41:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #208]
.L42:
  ldr d1, [sp, #208]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L43:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #216]
.L44:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #224]
.L45:
  ldr d1, [sp, #216]
  ldr d2, [sp, #224]
  fmul d0, d1, d2
  str d0, [sp, #232]
.L46:
  ldr x1, [sp, #8]
  ldr d0, [sp, #232]
  adrp x0, _arr_cx@PAGE
  add x0, x0, _arr_cx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L47:
  mov x0, #1
  str x0, [sp, #240]
.L48:
  ldr x1, [sp, #8]
  ldr x2, [sp, #240]
  add x0, x1, x2
  str x0, [sp, #8]
.L49:
  b .L35
.L50:
  mov x0, #1
  str x0, [sp, #16]
.L51:
  movz x0, #28288
  movk x0, #742, lsl #16
  str x0, [sp, #248]
.L52:
  ldr x1, [sp, #16]
  ldr x2, [sp, #248]
  cmp x1, x2
  b.gt .L172
.L53:
  mov x0, #1
  str x0, [sp, #8]
.L54:
  mov x0, #101
  str x0, [sp, #256]
.L55:
  ldr x1, [sp, #8]
  ldr x2, [sp, #256]
  cmp x1, x2
  b.gt .L169
.L56:
  mov x0, #4
  str x0, [sp, #264]
.L57:
  mov x0, #101
  str x0, [sp, #272]
.L58:
  ldr x1, [sp, #264]
  ldr x2, [sp, #272]
  mul x0, x1, x2
  str x0, [sp, #280]
.L59:
  ldr x1, [sp, #280]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #288]
.L60:
  ldr x1, [sp, #288]
  adrp x0, _arr_cx@PAGE
  add x0, x0, _arr_cx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #296]
.L61:
  ldr x0, [sp, #296]
  str x0, [sp, #24]
.L62:
  mov x0, #4
  str x0, [sp, #304]
.L63:
  mov x0, #101
  str x0, [sp, #312]
.L64:
  ldr x1, [sp, #304]
  ldr x2, [sp, #312]
  mul x0, x1, x2
  str x0, [sp, #320]
.L65:
  ldr x1, [sp, #320]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #328]
.L66:
  ldr x1, [sp, #328]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #336]
.L67:
  ldr d1, [sp, #24]
  ldr d2, [sp, #336]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L68:
  mov x0, #4
  str x0, [sp, #344]
.L69:
  mov x0, #101
  str x0, [sp, #352]
.L70:
  ldr x1, [sp, #344]
  ldr x2, [sp, #352]
  mul x0, x1, x2
  str x0, [sp, #360]
.L71:
  ldr x1, [sp, #360]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #368]
.L72:
  ldr x1, [sp, #368]
  ldr d0, [sp, #24]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L73:
  mov x0, #5
  str x0, [sp, #376]
.L74:
  mov x0, #101
  str x0, [sp, #384]
.L75:
  ldr x1, [sp, #376]
  ldr x2, [sp, #384]
  mul x0, x1, x2
  str x0, [sp, #392]
.L76:
  ldr x1, [sp, #392]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #400]
.L77:
  ldr x1, [sp, #400]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #408]
.L78:
  ldr d1, [sp, #32]
  ldr d2, [sp, #408]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L79:
  mov x0, #5
  str x0, [sp, #416]
.L80:
  mov x0, #101
  str x0, [sp, #424]
.L81:
  ldr x1, [sp, #416]
  ldr x2, [sp, #424]
  mul x0, x1, x2
  str x0, [sp, #432]
.L82:
  ldr x1, [sp, #432]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #440]
.L83:
  ldr x1, [sp, #440]
  ldr d0, [sp, #32]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L84:
  mov x0, #6
  str x0, [sp, #448]
.L85:
  mov x0, #101
  str x0, [sp, #456]
.L86:
  ldr x1, [sp, #448]
  ldr x2, [sp, #456]
  mul x0, x1, x2
  str x0, [sp, #464]
.L87:
  ldr x1, [sp, #464]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #472]
.L88:
  ldr x1, [sp, #472]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #480]
.L89:
  ldr d1, [sp, #40]
  ldr d2, [sp, #480]
  fsub d0, d1, d2
  str d0, [sp, #24]
.L90:
  mov x0, #6
  str x0, [sp, #488]
.L91:
  mov x0, #101
  str x0, [sp, #496]
.L92:
  ldr x1, [sp, #488]
  ldr x2, [sp, #496]
  mul x0, x1, x2
  str x0, [sp, #504]
.L93:
  ldr x1, [sp, #504]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #512]
.L94:
  ldr x1, [sp, #512]
  ldr d0, [sp, #40]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L95:
  mov x0, #7
  str x0, [sp, #520]
.L96:
  mov x0, #101
  str x0, [sp, #528]
.L97:
  ldr x1, [sp, #520]
  ldr x2, [sp, #528]
  mul x0, x1, x2
  str x0, [sp, #536]
.L98:
  ldr x1, [sp, #536]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #544]
.L99:
  ldr x1, [sp, #544]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #552]
.L100:
  ldr d1, [sp, #24]
  ldr d2, [sp, #552]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L101:
  mov x0, #7
  str x0, [sp, #560]
.L102:
  mov x0, #101
  str x0, [sp, #568]
.L103:
  ldr x1, [sp, #560]
  ldr x2, [sp, #568]
  mul x0, x1, x2
  str x0, [sp, #576]
.L104:
  ldr x1, [sp, #576]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #584]
.L105:
  ldr x1, [sp, #584]
  ldr d0, [sp, #24]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L106:
  mov x0, #8
  str x0, [sp, #592]
.L107:
  mov x0, #101
  str x0, [sp, #600]
.L108:
  ldr x1, [sp, #592]
  ldr x2, [sp, #600]
  mul x0, x1, x2
  str x0, [sp, #608]
.L109:
  ldr x1, [sp, #608]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #616]
.L110:
  ldr x1, [sp, #616]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #624]
.L111:
  ldr d1, [sp, #32]
  ldr d2, [sp, #624]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L112:
  mov x0, #8
  str x0, [sp, #632]
.L113:
  mov x0, #101
  str x0, [sp, #640]
.L114:
  ldr x1, [sp, #632]
  ldr x2, [sp, #640]
  mul x0, x1, x2
  str x0, [sp, #648]
.L115:
  ldr x1, [sp, #648]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #656]
.L116:
  ldr x1, [sp, #656]
  ldr d0, [sp, #32]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L117:
  mov x0, #9
  str x0, [sp, #664]
.L118:
  mov x0, #101
  str x0, [sp, #672]
.L119:
  ldr x1, [sp, #664]
  ldr x2, [sp, #672]
  mul x0, x1, x2
  str x0, [sp, #680]
.L120:
  ldr x1, [sp, #680]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #688]
.L121:
  ldr x1, [sp, #688]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #696]
.L122:
  ldr d1, [sp, #40]
  ldr d2, [sp, #696]
  fsub d0, d1, d2
  str d0, [sp, #24]
.L123:
  mov x0, #9
  str x0, [sp, #704]
.L124:
  mov x0, #101
  str x0, [sp, #712]
.L125:
  ldr x1, [sp, #704]
  ldr x2, [sp, #712]
  mul x0, x1, x2
  str x0, [sp, #720]
.L126:
  ldr x1, [sp, #720]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #728]
.L127:
  ldr x1, [sp, #728]
  ldr d0, [sp, #40]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L128:
  mov x0, #10
  str x0, [sp, #736]
.L129:
  mov x0, #101
  str x0, [sp, #744]
.L130:
  ldr x1, [sp, #736]
  ldr x2, [sp, #744]
  mul x0, x1, x2
  str x0, [sp, #752]
.L131:
  ldr x1, [sp, #752]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #760]
.L132:
  ldr x1, [sp, #760]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #768]
.L133:
  ldr d1, [sp, #24]
  ldr d2, [sp, #768]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L134:
  mov x0, #10
  str x0, [sp, #776]
.L135:
  mov x0, #101
  str x0, [sp, #784]
.L136:
  ldr x1, [sp, #776]
  ldr x2, [sp, #784]
  mul x0, x1, x2
  str x0, [sp, #792]
.L137:
  ldr x1, [sp, #792]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #800]
.L138:
  ldr x1, [sp, #800]
  ldr d0, [sp, #24]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L139:
  mov x0, #11
  str x0, [sp, #808]
.L140:
  mov x0, #101
  str x0, [sp, #816]
.L141:
  ldr x1, [sp, #808]
  ldr x2, [sp, #816]
  mul x0, x1, x2
  str x0, [sp, #824]
.L142:
  ldr x1, [sp, #824]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #832]
.L143:
  ldr x1, [sp, #832]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #840]
.L144:
  ldr d1, [sp, #32]
  ldr d2, [sp, #840]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L145:
  mov x0, #11
  str x0, [sp, #848]
.L146:
  mov x0, #101
  str x0, [sp, #856]
.L147:
  ldr x1, [sp, #848]
  ldr x2, [sp, #856]
  mul x0, x1, x2
  str x0, [sp, #864]
.L148:
  ldr x1, [sp, #864]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #872]
.L149:
  ldr x1, [sp, #872]
  ldr d0, [sp, #32]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L150:
  mov x0, #13
  str x0, [sp, #880]
.L151:
  mov x0, #101
  str x0, [sp, #888]
.L152:
  ldr x1, [sp, #880]
  ldr x2, [sp, #888]
  mul x0, x1, x2
  str x0, [sp, #896]
.L153:
  ldr x1, [sp, #896]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #904]
.L154:
  mov x0, #12
  str x0, [sp, #912]
.L155:
  mov x0, #101
  str x0, [sp, #920]
.L156:
  ldr x1, [sp, #912]
  ldr x2, [sp, #920]
  mul x0, x1, x2
  str x0, [sp, #928]
.L157:
  ldr x1, [sp, #928]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #936]
.L158:
  ldr x1, [sp, #936]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #944]
.L159:
  ldr d1, [sp, #40]
  ldr d2, [sp, #944]
  fsub d0, d1, d2
  str d0, [sp, #952]
.L160:
  ldr x1, [sp, #904]
  ldr d0, [sp, #952]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L161:
  mov x0, #12
  str x0, [sp, #960]
.L162:
  mov x0, #101
  str x0, [sp, #968]
.L163:
  ldr x1, [sp, #960]
  ldr x2, [sp, #968]
  mul x0, x1, x2
  str x0, [sp, #976]
.L164:
  ldr x1, [sp, #976]
  ldr x2, [sp, #8]
  add x0, x1, x2
  str x0, [sp, #984]
.L165:
  ldr x1, [sp, #984]
  ldr d0, [sp, #40]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L166:
  mov x0, #1
  str x0, [sp, #992]
.L167:
  ldr x1, [sp, #8]
  ldr x2, [sp, #992]
  add x0, x1, x2
  str x0, [sp, #8]
.L168:
  b .L54
.L169:
  mov x0, #1
  str x0, [sp, #1000]
.L170:
  ldr x1, [sp, #16]
  ldr x2, [sp, #1000]
  add x0, x1, x2
  str x0, [sp, #16]
.L171:
  b .L51
.L172:
  mov x0, #5
  str x0, [sp, #1008]
.L173:
  mov x0, #1
  str x0, [sp, #1016]
.L174:
  ldr x1, [sp, #1008]
  ldr x2, [sp, #1016]
  sub x0, x1, x2
  str x0, [sp, #1024]
.L175:
  mov x0, #101
  str x0, [sp, #1032]
.L176:
  ldr x1, [sp, #1024]
  ldr x2, [sp, #1032]
  mul x0, x1, x2
  str x0, [sp, #1040]
.L177:
  mov x0, #51
  str x0, [sp, #1048]
.L178:
  ldr x1, [sp, #1040]
  ldr x2, [sp, #1048]
  add x0, x1, x2
  str x0, [sp, #1056]
.L179:
  ldr x1, [sp, #1056]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1064]
.L180:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #1064]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_180@PAGE
  add x0, x0, .Lfmt_print_180@PAGEOFF
  bl _printf
  add sp, sp, #16
.L181:
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
  // print ar (float)
  ldr d0, [sp, #24]
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
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x1, .Lname_br@PAGE
  add x1, x1, .Lname_br@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print cr (float)
  ldr d0, [sp, #40]
  sub sp, sp, #32
  adrp x1, .Lname_cr@PAGE
  add x1, x1, .Lname_cr@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #48]
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
  ldr d0, [sp, #56]
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
  ldr d0, [sp, #64]
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
  ldr x29, [sp, #1072]
  ldr x30, [sp, #1080]
  add sp, sp, #1088
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

.Lfmt_print_180:
  .asciz "%f\n"

.Lname_i:
  .asciz "i"
.Lname_rep:
  .asciz "rep"
.Lname_ar:
  .asciz "ar"
.Lname_br:
  .asciz "br"
.Lname_cr:
  .asciz "cr"
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
