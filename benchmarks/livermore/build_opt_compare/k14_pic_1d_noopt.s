.global _main
.align 2

_main:
  sub sp, sp, #1072
  str x30, [sp, #1064]
  str x29, [sp, #1056]
  add x29, sp, #1056

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
  mov x0, #39
  str x0, [sp, #80]
.L14:
  ldr x1, [sp, #8]
  ldr x2, [sp, #80]
  cmp x1, x2
  b.gt .L28
.L15:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #88]
.L16:
  ldr d1, [sp, #88]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #96]
.L17:
  ldr d1, [sp, #96]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #104]
.L18:
  ldr d1, [sp, #104]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L19:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #112]
.L20:
  ldr d1, [sp, #112]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L21:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #120]
.L22:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #128]
.L23:
  ldr d1, [sp, #120]
  ldr d2, [sp, #128]
  fmul d0, d1, d2
  str d0, [sp, #136]
.L24:
  ldr x1, [sp, #8]
  ldr d0, [sp, #136]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L25:
  mov x0, #1
  str x0, [sp, #144]
.L26:
  ldr x1, [sp, #8]
  ldr x2, [sp, #144]
  add x0, x1, x2
  str x0, [sp, #8]
.L27:
  b .L13
.L28:
  mov x0, #27
  str x0, [sp, #152]
.L29:
  ldr x1, [sp, #152]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #160]
.L30:
  ldr x0, [sp, #160]
  str x0, [sp, #32]
.L31:
  mov x0, #1
  str x0, [sp, #16]
.L32:
  mov x0, #1001
  str x0, [sp, #168]
.L33:
  ldr x1, [sp, #16]
  ldr x2, [sp, #168]
  cmp x1, x2
  b.gt .L45
.L34:
  mov x0, #1
  str x0, [sp, #176]
.L35:
  ldr x1, [sp, #16]
  ldr x2, [sp, #176]
  sub x0, x1, x2
  str x0, [sp, #184]
.L36:
  mov x0, #512
  str x0, [sp, #192]
.L37:
  ldr x1, [sp, #184]
  ldr x2, [sp, #192]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  mul x0, x0, x2
  sub x0, x1, x0
  str x0, [sp, #200]
.L38:
  ldr x0, [sp, #200]
  scvtf d0, x0
  str d0, [sp, #208]
.L39:
  movz x0, #0
  movk x0, #16376, lsl #48
  fmov d0, x0
  str d0, [sp, #216]
.L40:
  ldr d1, [sp, #208]
  ldr d2, [sp, #216]
  fadd d0, d1, d2
  str d0, [sp, #224]
.L41:
  ldr x1, [sp, #16]
  ldr d0, [sp, #224]
  adrp x0, _arr_grd@PAGE
  add x0, x0, _arr_grd@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L42:
  mov x0, #1
  str x0, [sp, #232]
.L43:
  ldr x1, [sp, #16]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #16]
.L44:
  b .L32
.L45:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L46:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #240]
.L47:
  ldr d1, [sp, #240]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L48:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #248]
.L49:
  ldr d1, [sp, #248]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L50:
  mov x0, #1
  str x0, [sp, #8]
.L51:
  mov x0, #1001
  str x0, [sp, #256]
.L52:
  ldr x1, [sp, #8]
  ldr x2, [sp, #256]
  cmp x1, x2
  b.gt .L66
.L53:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #264]
.L54:
  ldr d1, [sp, #264]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #272]
.L55:
  ldr d1, [sp, #272]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #280]
.L56:
  ldr d1, [sp, #280]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L57:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #288]
.L58:
  ldr d1, [sp, #288]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L59:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #296]
.L60:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #304]
.L61:
  ldr d1, [sp, #296]
  ldr d2, [sp, #304]
  fmul d0, d1, d2
  str d0, [sp, #312]
.L62:
  ldr x1, [sp, #8]
  ldr d0, [sp, #312]
  adrp x0, _arr_ex@PAGE
  add x0, x0, _arr_ex@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L63:
  mov x0, #1
  str x0, [sp, #320]
.L64:
  ldr x1, [sp, #8]
  ldr x2, [sp, #320]
  add x0, x1, x2
  str x0, [sp, #8]
.L65:
  b .L51
.L66:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #40]
.L67:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #328]
.L68:
  ldr d1, [sp, #328]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L69:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #336]
.L70:
  ldr d1, [sp, #336]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #56]
.L71:
  mov x0, #1
  str x0, [sp, #8]
.L72:
  mov x0, #1001
  str x0, [sp, #344]
.L73:
  ldr x1, [sp, #8]
  ldr x2, [sp, #344]
  cmp x1, x2
  b.gt .L87
.L74:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #352]
.L75:
  ldr d1, [sp, #352]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #360]
.L76:
  ldr d1, [sp, #360]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #368]
.L77:
  ldr d1, [sp, #368]
  ldr d2, [sp, #40]
  fadd d0, d1, d2
  str d0, [sp, #48]
.L78:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #376]
.L79:
  ldr d1, [sp, #376]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #40]
.L80:
  ldr d1, [sp, #48]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #384]
.L81:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #392]
.L82:
  ldr d1, [sp, #384]
  ldr d2, [sp, #392]
  fmul d0, d1, d2
  str d0, [sp, #400]
.L83:
  ldr x1, [sp, #8]
  ldr d0, [sp, #400]
  adrp x0, _arr_dex@PAGE
  add x0, x0, _arr_dex@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L84:
  mov x0, #1
  str x0, [sp, #408]
.L85:
  ldr x1, [sp, #8]
  ldr x2, [sp, #408]
  add x0, x1, x2
  str x0, [sp, #8]
.L86:
  b .L72
.L87:
  mov x0, #1
  str x0, [sp, #16]
.L88:
  mov x0, #1001
  str x0, [sp, #416]
.L89:
  ldr x1, [sp, #16]
  ldr x2, [sp, #416]
  cmp x1, x2
  b.gt .L109
.L90:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #424]
.L91:
  ldr x1, [sp, #16]
  ldr d0, [sp, #424]
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L92:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #432]
.L93:
  ldr x1, [sp, #16]
  ldr d0, [sp, #432]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L94:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #440]
.L95:
  ldr x1, [sp, #16]
  ldr d0, [sp, #440]
  adrp x0, _arr_xi@PAGE
  add x0, x0, _arr_xi@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L96:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #448]
.L97:
  ldr x1, [sp, #16]
  ldr d0, [sp, #448]
  adrp x0, _arr_ex1@PAGE
  add x0, x0, _arr_ex1@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L98:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #456]
.L99:
  ldr x1, [sp, #16]
  ldr d0, [sp, #456]
  adrp x0, _arr_dex1@PAGE
  add x0, x0, _arr_dex1@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L100:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #464]
.L101:
  ldr x1, [sp, #16]
  ldr d0, [sp, #464]
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L102:
  mov x0, #0
  str x0, [sp, #472]
.L103:
  ldr x1, [sp, #16]
  ldr x2, [sp, #472]
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L104:
  mov x0, #0
  str x0, [sp, #480]
.L105:
  ldr x1, [sp, #16]
  ldr x2, [sp, #480]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L106:
  mov x0, #1
  str x0, [sp, #488]
.L107:
  ldr x1, [sp, #16]
  ldr x2, [sp, #488]
  add x0, x1, x2
  str x0, [sp, #16]
.L108:
  b .L88
.L109:
  mov x0, #1
  str x0, [sp, #16]
.L110:
  mov x0, #2049
  str x0, [sp, #496]
.L111:
  ldr x1, [sp, #16]
  ldr x2, [sp, #496]
  cmp x1, x2
  b.gt .L117
.L112:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #504]
.L113:
  ldr x1, [sp, #16]
  ldr d0, [sp, #504]
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L114:
  mov x0, #1
  str x0, [sp, #512]
.L115:
  ldr x1, [sp, #16]
  ldr x2, [sp, #512]
  add x0, x1, x2
  str x0, [sp, #16]
.L116:
  b .L110
.L117:
  mov x0, #1
  str x0, [sp, #24]
.L118:
  movz x0, #31992
  movk x0, #28, lsl #16
  str x0, [sp, #520]
.L119:
  ldr x1, [sp, #24]
  ldr x2, [sp, #520]
  cmp x1, x2
  b.gt .L217
.L120:
  mov x0, #1
  str x0, [sp, #16]
.L121:
  mov x0, #2049
  str x0, [sp, #528]
.L122:
  ldr x1, [sp, #16]
  ldr x2, [sp, #528]
  cmp x1, x2
  b.gt .L128
.L123:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #536]
.L124:
  ldr x1, [sp, #16]
  ldr d0, [sp, #536]
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L125:
  mov x0, #1
  str x0, [sp, #544]
.L126:
  ldr x1, [sp, #16]
  ldr x2, [sp, #544]
  add x0, x1, x2
  str x0, [sp, #16]
.L127:
  b .L121
.L128:
  mov x0, #1
  str x0, [sp, #8]
.L129:
  mov x0, #1001
  str x0, [sp, #552]
.L130:
  ldr x1, [sp, #8]
  ldr x2, [sp, #552]
  cmp x1, x2
  b.gt .L150
.L131:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #560]
.L132:
  ldr x1, [sp, #8]
  ldr d0, [sp, #560]
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L133:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #568]
.L134:
  ldr x1, [sp, #8]
  ldr d0, [sp, #568]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L135:
  ldr x1, [sp, #8]
  adrp x0, _arr_grd@PAGE
  add x0, x0, _arr_grd@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #576]
.L136:
  ldr d0, [sp, #576]
  fcvtzs x0, d0
  str x0, [sp, #584]
.L137:
  ldr x1, [sp, #8]
  ldr x2, [sp, #584]
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L138:
  ldr x1, [sp, #8]
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #592]
.L139:
  ldr x0, [sp, #592]
  scvtf d0, x0
  str d0, [sp, #600]
.L140:
  ldr x1, [sp, #8]
  ldr d0, [sp, #600]
  adrp x0, _arr_xi@PAGE
  add x0, x0, _arr_xi@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L141:
  ldr x1, [sp, #8]
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #608]
.L142:
  ldr x1, [sp, #608]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_ex@PAGE
  add x0, x0, _arr_ex@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #616]
.L143:
  ldr x1, [sp, #8]
  ldr d0, [sp, #616]
  adrp x0, _arr_ex1@PAGE
  add x0, x0, _arr_ex1@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L144:
  ldr x1, [sp, #8]
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #624]
.L145:
  ldr x1, [sp, #624]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_dex@PAGE
  add x0, x0, _arr_dex@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #632]
.L146:
  ldr x1, [sp, #8]
  ldr d0, [sp, #632]
  adrp x0, _arr_dex1@PAGE
  add x0, x0, _arr_dex1@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L147:
  mov x0, #1
  str x0, [sp, #640]
.L148:
  ldr x1, [sp, #8]
  ldr x2, [sp, #640]
  add x0, x1, x2
  str x0, [sp, #8]
.L149:
  b .L129
.L150:
  mov x0, #1
  str x0, [sp, #8]
.L151:
  mov x0, #1001
  str x0, [sp, #648]
.L152:
  ldr x1, [sp, #8]
  ldr x2, [sp, #648]
  cmp x1, x2
  b.gt .L190
.L153:
  ldr x1, [sp, #8]
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #656]
.L154:
  ldr x1, [sp, #8]
  adrp x0, _arr_ex1@PAGE
  add x0, x0, _arr_ex1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #664]
.L155:
  ldr d1, [sp, #656]
  ldr d2, [sp, #664]
  fadd d0, d1, d2
  str d0, [sp, #672]
.L156:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #680]
.L157:
  ldr x1, [sp, #8]
  adrp x0, _arr_xi@PAGE
  add x0, x0, _arr_xi@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #688]
.L158:
  ldr d1, [sp, #680]
  ldr d2, [sp, #688]
  fsub d0, d1, d2
  str d0, [sp, #696]
.L159:
  ldr x1, [sp, #8]
  adrp x0, _arr_dex1@PAGE
  add x0, x0, _arr_dex1@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #704]
.L160:
  ldr d1, [sp, #696]
  ldr d2, [sp, #704]
  fmul d0, d1, d2
  str d0, [sp, #712]
.L161:
  ldr d1, [sp, #672]
  ldr d2, [sp, #712]
  fadd d0, d1, d2
  str d0, [sp, #720]
.L162:
  ldr x1, [sp, #8]
  ldr d0, [sp, #720]
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L163:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #728]
.L164:
  ldr x1, [sp, #8]
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #736]
.L165:
  ldr d1, [sp, #728]
  ldr d2, [sp, #736]
  fadd d0, d1, d2
  str d0, [sp, #744]
.L166:
  ldr d1, [sp, #744]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #752]
.L167:
  ldr x1, [sp, #8]
  ldr d0, [sp, #752]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L168:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #760]
.L169:
  ldr d0, [sp, #760]
  fcvtzs x0, d0
  str x0, [sp, #768]
.L170:
  ldr x1, [sp, #8]
  ldr x2, [sp, #768]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L171:
  ldr x1, [sp, #8]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #776]
.L172:
  ldr x1, [sp, #8]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #784]
.L173:
  ldr x0, [sp, #784]
  scvtf d0, x0
  str d0, [sp, #792]
.L174:
  ldr d1, [sp, #776]
  ldr d2, [sp, #792]
  fsub d0, d1, d2
  str d0, [sp, #800]
.L175:
  ldr x1, [sp, #8]
  ldr d0, [sp, #800]
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L176:
  ldr x1, [sp, #8]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #808]
.L177:
  mov x0, #2047
  str x0, [sp, #816]
.L178:
  ldr x1, [sp, #808]
  ldr x2, [sp, #816]
  and x0, x1, x2
  str x0, [sp, #824]
.L179:
  mov x0, #1
  str x0, [sp, #832]
.L180:
  ldr x1, [sp, #824]
  ldr x2, [sp, #832]
  add x0, x1, x2
  str x0, [sp, #840]
.L181:
  ldr x1, [sp, #8]
  ldr x2, [sp, #840]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L182:
  ldr x1, [sp, #8]
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #848]
.L183:
  ldr x1, [sp, #8]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #856]
.L184:
  ldr x0, [sp, #856]
  scvtf d0, x0
  str d0, [sp, #864]
.L185:
  ldr d1, [sp, #848]
  ldr d2, [sp, #864]
  fadd d0, d1, d2
  str d0, [sp, #872]
.L186:
  ldr x1, [sp, #8]
  ldr d0, [sp, #872]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L187:
  mov x0, #1
  str x0, [sp, #880]
.L188:
  ldr x1, [sp, #8]
  ldr x2, [sp, #880]
  add x0, x1, x2
  str x0, [sp, #8]
.L189:
  b .L151
.L190:
  mov x0, #1
  str x0, [sp, #8]
.L191:
  mov x0, #1001
  str x0, [sp, #888]
.L192:
  ldr x1, [sp, #8]
  ldr x2, [sp, #888]
  cmp x1, x2
  b.gt .L214
.L193:
  ldr x1, [sp, #8]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #896]
.L194:
  ldr x1, [sp, #8]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #904]
.L195:
  ldr x1, [sp, #904]
  cmp x1, #2050
  b.hs .Lbounds_err
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #912]
.L196:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #920]
.L197:
  ldr d1, [sp, #912]
  ldr d2, [sp, #920]
  fadd d0, d1, d2
  str d0, [sp, #928]
.L198:
  ldr x1, [sp, #8]
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #936]
.L199:
  ldr d1, [sp, #928]
  ldr d2, [sp, #936]
  fsub d0, d1, d2
  str d0, [sp, #944]
.L200:
  ldr x1, [sp, #896]
  cmp x1, #2050
  b.hs .Lbounds_err
  ldr d0, [sp, #944]
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L201:
  ldr x1, [sp, #8]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #952]
.L202:
  mov x0, #1
  str x0, [sp, #960]
.L203:
  ldr x1, [sp, #952]
  ldr x2, [sp, #960]
  add x0, x1, x2
  str x0, [sp, #968]
.L204:
  ldr x1, [sp, #8]
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #976]
.L205:
  mov x0, #1
  str x0, [sp, #984]
.L206:
  ldr x1, [sp, #976]
  ldr x2, [sp, #984]
  add x0, x1, x2
  str x0, [sp, #992]
.L207:
  ldr x1, [sp, #992]
  cmp x1, #2050
  b.hs .Lbounds_err
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1000]
.L208:
  ldr x1, [sp, #8]
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1008]
.L209:
  ldr d1, [sp, #1000]
  ldr d2, [sp, #1008]
  fadd d0, d1, d2
  str d0, [sp, #1016]
.L210:
  ldr x1, [sp, #968]
  cmp x1, #2050
  b.hs .Lbounds_err
  ldr d0, [sp, #1016]
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L211:
  mov x0, #1
  str x0, [sp, #1024]
.L212:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1024]
  add x0, x1, x2
  str x0, [sp, #8]
.L213:
  b .L191
.L214:
  mov x0, #1
  str x0, [sp, #1032]
.L215:
  ldr x1, [sp, #24]
  ldr x2, [sp, #1032]
  add x0, x1, x2
  str x0, [sp, #24]
.L216:
  b .L118
.L217:
  mov x0, #1
  str x0, [sp, #1040]
.L218:
  ldr x1, [sp, #1040]
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #1048]
.L219:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #1048]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_219@PAGE
  add x0, x0, .Lfmt_print_219@PAGEOFF
  bl _printf
  add sp, sp, #16
.L220:
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
  // print i
  ldr x9, [sp, #16]
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
  // print flx (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x1, .Lname_flx@PAGE
  add x1, x1, .Lname_flx@PAGEOFF
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
  ldr x29, [sp, #1056]
  ldr x30, [sp, #1064]
  add sp, sp, #1072
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

.Lfmt_print_219:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_i:
  .asciz "i"
.Lname_rep:
  .asciz "rep"
.Lname_flx:
  .asciz "flx"
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
.global _arr_grd
.align 3
_arr_grd:
  .space 8016
.global _arr_ex
.align 3
_arr_ex:
  .space 8016
.global _arr_dex
.align 3
_arr_dex:
  .space 8016
.global _arr_vx
.align 3
_arr_vx:
  .space 8016
.global _arr_xx
.align 3
_arr_xx:
  .space 8016
.global _arr_xi
.align 3
_arr_xi:
  .space 8016
.global _arr_ex1
.align 3
_arr_ex1:
  .space 8016
.global _arr_dex1
.align 3
_arr_dex1:
  .space 8016
.global _arr_rx
.align 3
_arr_rx:
  .space 8016
.global _arr_ix
.align 3
_arr_ix:
  .space 8016
.global _arr_ir
.align 3
_arr_ir:
  .space 8016
.global _arr_rh
.align 3
_arr_rh:
  .space 16400
