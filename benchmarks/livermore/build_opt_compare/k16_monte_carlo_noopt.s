.global _main
.align 2

_main:
  sub sp, sp, #1024
  str x30, [sp, #1016]
  str x29, [sp, #1008]
  add x29, sp, #1008

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
  str x0, [sp, #56]
.L7:
  mov x0, #0
  str x0, [sp, #64]
.L8:
  mov x0, #0
  str x0, [sp, #72]
.L9:
  mov x0, #0
  str x0, [sp, #80]
.L10:
  mov x0, #0
  str x0, [sp, #88]
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
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #120]
.L15:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #128]
.L16:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #136]
.L17:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #144]
.L18:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #152]
.L19:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #160]
.L20:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #168]
.L21:
  mov x0, #0
  str x0, [sp, #176]
.L22:
  mov x0, #0
  str x0, [sp, #184]
.L23:
  mov x0, #0
  str x0, [sp, #192]
.L24:
  mov x0, #75
  str x0, [sp, #104]
.L25:
  mov x0, #3
  str x0, [sp, #200]
.L26:
  ldr x1, [sp, #104]
  ldr x2, [sp, #200]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  str x0, [sp, #88]
.L27:
  ldr x1, [sp, #88]
  ldr x2, [sp, #88]
  add x0, x1, x2
  str x0, [sp, #96]
.L28:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #120]
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #128]
.L30:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #136]
.L31:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #152]
.L32:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #208]
.L33:
  ldr d1, [sp, #208]
  ldr d2, [sp, #152]
  fadd d0, d1, d2
  str d0, [sp, #160]
.L34:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #216]
.L35:
  ldr d1, [sp, #216]
  ldr d2, [sp, #152]
  fmul d0, d1, d2
  str d0, [sp, #168]
.L36:
  mov x0, #1
  str x0, [sp, #16]
.L37:
  mov x0, #300
  str x0, [sp, #224]
.L38:
  ldr x1, [sp, #16]
  ldr x2, [sp, #224]
  cmp x1, x2
  b.gt .L56
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #232]
.L40:
  ldr d1, [sp, #232]
  ldr d2, [sp, #152]
  fsub d0, d1, d2
  str d0, [sp, #240]
.L41:
  ldr d1, [sp, #240]
  ldr d2, [sp, #160]
  fmul d0, d1, d2
  str d0, [sp, #248]
.L42:
  ldr d1, [sp, #248]
  ldr d2, [sp, #152]
  fadd d0, d1, d2
  str d0, [sp, #160]
.L43:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #256]
.L44:
  ldr d1, [sp, #256]
  ldr d2, [sp, #152]
  fsub d0, d1, d2
  str d0, [sp, #152]
.L45:
  ldr d1, [sp, #160]
  ldr d2, [sp, #168]
  fsub d0, d1, d2
  str d0, [sp, #264]
.L46:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #272]
.L47:
  ldr d1, [sp, #264]
  ldr d2, [sp, #272]
  fmul d0, d1, d2
  str d0, [sp, #280]
.L48:
  ldr x1, [sp, #16]
  ldr d0, [sp, #280]
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L49:
  ldr d1, [sp, #160]
  ldr d2, [sp, #168]
  fsub d0, d1, d2
  str d0, [sp, #288]
.L50:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #296]
.L51:
  ldr d1, [sp, #288]
  ldr d2, [sp, #296]
  fmul d0, d1, d2
  str d0, [sp, #304]
.L52:
  ldr x1, [sp, #16]
  ldr d0, [sp, #304]
  adrp x0, _arr_plan@PAGE
  add x0, x0, _arr_plan@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L53:
  mov x0, #1
  str x0, [sp, #312]
.L54:
  ldr x1, [sp, #16]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #16]
.L55:
  b .L37
.L56:
  mov x0, #1
  str x0, [sp, #16]
.L57:
  mov x0, #300
  str x0, [sp, #320]
.L58:
  ldr x1, [sp, #16]
  ldr x2, [sp, #320]
  cmp x1, x2
  b.gt .L68
.L59:
  mov x0, #1
  str x0, [sp, #328]
.L60:
  ldr x1, [sp, #16]
  ldr x2, [sp, #328]
  sub x0, x1, x2
  str x0, [sp, #336]
.L61:
  mov x0, #1
  str x0, [sp, #344]
.L62:
  ldr x1, [sp, #104]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #352]
.L63:
  ldr x1, [sp, #336]
  ldr x2, [sp, #352]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  mul x0, x0, x2
  sub x0, x1, x0
  str x0, [sp, #360]
.L64:
  ldr x1, [sp, #16]
  ldr x2, [sp, #360]
  adrp x0, _arr_zone@PAGE
  add x0, x0, _arr_zone@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L65:
  mov x0, #1
  str x0, [sp, #368]
.L66:
  ldr x1, [sp, #16]
  ldr x2, [sp, #368]
  add x0, x1, x2
  str x0, [sp, #16]
.L67:
  b .L57
.L68:
  mov x0, #1
  str x0, [sp, #376]
.L69:
  mov x0, #5
  str x0, [sp, #384]
.L70:
  ldr x1, [sp, #376]
  ldr x2, [sp, #384]
  adrp x0, _arr_zone@PAGE
  add x0, x0, _arr_zone@PAGEOFF
  str x2, [x0, x1, lsl #3]
.L71:
  mov x0, #1
  str x0, [sp, #8]
.L72:
  movz x0, #38640
  movk x0, #10, lsl #16
  str x0, [sp, #392]
.L73:
  ldr x1, [sp, #8]
  ldr x2, [sp, #392]
  cmp x1, x2
  b.gt .L225
.L74:
  mov x0, #1
  str x0, [sp, #32]
.L75:
  mov x0, #1
  str x0, [sp, #24]
.L76:
  mov x0, #0
  str x0, [sp, #48]
.L77:
  mov x0, #0
  str x0, [sp, #56]
.L78:
  mov x0, #0
  str x0, [sp, #176]
.L79:
  mov x0, #1
  str x0, [sp, #192]
.L80:
  mov x0, #1
  str x0, [sp, #400]
.L81:
  ldr x1, [sp, #192]
  ldr x2, [sp, #400]
  cmp x1, x2
  b.ne .L222
.L82:
  mov x0, #0
  str x0, [sp, #192]
.L83:
  mov x0, #0
  str x0, [sp, #176]
.L84:
  ldr x1, [sp, #104]
  ldr x2, [sp, #104]
  add x0, x1, x2
  str x0, [sp, #408]
.L85:
  mov x0, #1
  str x0, [sp, #416]
.L86:
  ldr x1, [sp, #24]
  ldr x2, [sp, #416]
  sub x0, x1, x2
  str x0, [sp, #424]
.L87:
  ldr x1, [sp, #408]
  ldr x2, [sp, #424]
  mul x0, x1, x2
  str x0, [sp, #432]
.L88:
  mov x0, #1
  str x0, [sp, #440]
.L89:
  ldr x1, [sp, #432]
  ldr x2, [sp, #440]
  add x0, x1, x2
  str x0, [sp, #64]
.L90:
  mov x0, #1
  str x0, [sp, #40]
.L91:
  ldr x1, [sp, #40]
  ldr x2, [sp, #104]
  cmp x1, x2
  b.gt .L96
.L92:
  mov x0, #0
  str x0, [sp, #448]
.L93:
  ldr x1, [sp, #176]
  ldr x2, [sp, #448]
  cmp x1, x2
  b.ne .L96
.L94:
  mov x0, #1
  str x0, [sp, #456]
.L95:
  b .L97
.L96:
  mov x0, #0
  str x0, [sp, #456]
.L97:
  ldr x1, [sp, #456]
  mov x2, #0
  cmp x1, x2
  b.eq .L221
.L98:
  mov x0, #0
  str x0, [sp, #184]
.L99:
  mov x0, #1
  str x0, [sp, #464]
.L100:
  ldr x1, [sp, #48]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #48]
.L101:
  ldr x1, [sp, #64]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #472]
.L102:
  ldr x1, [sp, #472]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #72]
.L103:
  mov x0, #1
  str x0, [sp, #480]
.L104:
  ldr x1, [sp, #72]
  ldr x2, [sp, #480]
  sub x0, x1, x2
  str x0, [sp, #488]
.L105:
  ldr x1, [sp, #488]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_zone@PAGE
  add x0, x0, _arr_zone@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #496]
.L106:
  ldr x0, [sp, #496]
  str x0, [sp, #80]
.L107:
  ldr x1, [sp, #80]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L151
.L108:
  ldr x1, [sp, #80]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L149
.L109:
  mov x0, #1
  str x0, [sp, #504]
.L110:
  ldr x1, [sp, #56]
  ldr x2, [sp, #504]
  add x0, x1, x2
  str x0, [sp, #56]
.L111:
  mov x0, #1
  str x0, [sp, #512]
.L112:
  ldr x1, [sp, #80]
  ldr x2, [sp, #512]
  sub x0, x1, x2
  str x0, [sp, #520]
.L113:
  ldr x1, [sp, #520]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #528]
.L114:
  mov x0, #2
  str x0, [sp, #536]
.L115:
  ldr x1, [sp, #80]
  ldr x2, [sp, #536]
  sub x0, x1, x2
  str x0, [sp, #544]
.L116:
  ldr x1, [sp, #544]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #552]
.L117:
  mov x0, #3
  str x0, [sp, #560]
.L118:
  ldr x1, [sp, #80]
  ldr x2, [sp, #560]
  sub x0, x1, x2
  str x0, [sp, #568]
.L119:
  ldr x1, [sp, #568]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #576]
.L120:
  ldr d1, [sp, #136]
  ldr d2, [sp, #576]
  fsub d0, d1, d2
  str d0, [sp, #584]
.L121:
  ldr d1, [sp, #552]
  ldr d2, [sp, #584]
  fmul d0, d1, d2
  str d0, [sp, #592]
.L122:
  mov x0, #3
  str x0, [sp, #600]
.L123:
  ldr x1, [sp, #80]
  ldr x2, [sp, #600]
  sub x0, x1, x2
  str x0, [sp, #608]
.L124:
  ldr x1, [sp, #608]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #616]
.L125:
  ldr d1, [sp, #136]
  ldr d2, [sp, #616]
  fsub d0, d1, d2
  str d0, [sp, #624]
.L126:
  ldr d1, [sp, #592]
  ldr d2, [sp, #624]
  fmul d0, d1, d2
  str d0, [sp, #632]
.L127:
  mov x0, #4
  str x0, [sp, #640]
.L128:
  ldr x1, [sp, #80]
  ldr x2, [sp, #640]
  sub x0, x1, x2
  str x0, [sp, #648]
.L129:
  ldr x1, [sp, #648]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #656]
.L130:
  ldr d1, [sp, #128]
  ldr d2, [sp, #656]
  fsub d0, d1, d2
  str d0, [sp, #664]
.L131:
  mov x0, #4
  str x0, [sp, #672]
.L132:
  ldr x1, [sp, #80]
  ldr x2, [sp, #672]
  sub x0, x1, x2
  str x0, [sp, #680]
.L133:
  ldr x1, [sp, #680]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #688]
.L134:
  ldr d1, [sp, #128]
  ldr d2, [sp, #688]
  fsub d0, d1, d2
  str d0, [sp, #696]
.L135:
  ldr d1, [sp, #664]
  ldr d2, [sp, #696]
  fmul d0, d1, d2
  str d0, [sp, #704]
.L136:
  ldr d1, [sp, #632]
  ldr d2, [sp, #704]
  fadd d0, d1, d2
  str d0, [sp, #712]
.L137:
  mov x0, #5
  str x0, [sp, #720]
.L138:
  ldr x1, [sp, #80]
  ldr x2, [sp, #720]
  sub x0, x1, x2
  str x0, [sp, #728]
.L139:
  ldr x1, [sp, #728]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #736]
.L140:
  ldr d1, [sp, #120]
  ldr d2, [sp, #736]
  fsub d0, d1, d2
  str d0, [sp, #744]
.L141:
  mov x0, #5
  str x0, [sp, #752]
.L142:
  ldr x1, [sp, #80]
  ldr x2, [sp, #752]
  sub x0, x1, x2
  str x0, [sp, #760]
.L143:
  ldr x1, [sp, #760]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_d@PAGE
  add x0, x0, _arr_d@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #768]
.L144:
  ldr d1, [sp, #120]
  ldr d2, [sp, #768]
  fsub d0, d1, d2
  str d0, [sp, #776]
.L145:
  ldr d1, [sp, #744]
  ldr d2, [sp, #776]
  fmul d0, d1, d2
  str d0, [sp, #784]
.L146:
  ldr d1, [sp, #712]
  ldr d2, [sp, #784]
  fadd d0, d1, d2
  str d0, [sp, #792]
.L147:
  ldr d1, [sp, #528]
  ldr d2, [sp, #792]
  fsub d0, d1, d2
  str d0, [sp, #144]
.L148:
  b .L150
.L149:
  mov x0, #1
  str x0, [sp, #176]
.L150:
  b .L163
.L151:
  ldr x1, [sp, #80]
  ldr x2, [sp, #96]
  add x0, x1, x2
  str x0, [sp, #800]
.L152:
  ldr x1, [sp, #800]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L161
.L153:
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  add x0, x1, x2
  str x0, [sp, #808]
.L154:
  ldr x1, [sp, #808]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L158
.L155:
  ldr x1, [sp, #80]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_plan@PAGE
  add x0, x0, _arr_plan@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #816]
.L156:
  ldr d1, [sp, #816]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #144]
.L157:
  b .L160
.L158:
  ldr x1, [sp, #80]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_plan@PAGE
  add x0, x0, _arr_plan@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #824]
.L159:
  ldr d1, [sp, #824]
  ldr d2, [sp, #128]
  fsub d0, d1, d2
  str d0, [sp, #144]
.L160:
  b .L163
.L161:
  ldr x1, [sp, #80]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_plan@PAGE
  add x0, x0, _arr_plan@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #832]
.L162:
  ldr d1, [sp, #832]
  ldr d2, [sp, #136]
  fsub d0, d1, d2
  str d0, [sp, #144]
.L163:
  mov x0, #0
  str x0, [sp, #840]
.L164:
  ldr x1, [sp, #176]
  ldr x2, [sp, #840]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L166
.L165:
  b .L197
.L166:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #848]
.L167:
  ldr d1, [sp, #144]
  ldr d2, [sp, #848]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L185
.L168:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #856]
.L169:
  ldr d1, [sp, #856]
  ldr d2, [sp, #144]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L172
.L170:
  mov x0, #1
  str x0, [sp, #176]
.L171:
  b .L184
.L172:
  mov x0, #2
  str x0, [sp, #864]
.L173:
  ldr x1, [sp, #72]
  ldr x2, [sp, #864]
  sub x0, x1, x2
  str x0, [sp, #872]
.L174:
  ldr x1, [sp, #872]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_zone@PAGE
  add x0, x0, _arr_zone@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #880]
.L175:
  ldr x0, [sp, #880]
  str x0, [sp, #112]
.L176:
  mov x0, #0
  str x0, [sp, #888]
.L177:
  ldr x1, [sp, #888]
  ldr x2, [sp, #112]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L183
.L178:
  mov x0, #0
  str x0, [sp, #896]
.L179:
  ldr x1, [sp, #112]
  ldr x2, [sp, #896]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L181
.L180:
  b .L182
.L181:
  mov x0, #1
  str x0, [sp, #176]
.L182:
  b .L184
.L183:
  mov x0, #1
  str x0, [sp, #184]
.L184:
  b .L197
.L185:
  mov x0, #2
  str x0, [sp, #904]
.L186:
  ldr x1, [sp, #72]
  ldr x2, [sp, #904]
  sub x0, x1, x2
  str x0, [sp, #912]
.L187:
  ldr x1, [sp, #912]
  cmp x1, #301
  b.hs .Lbounds_err
  adrp x0, _arr_zone@PAGE
  add x0, x0, _arr_zone@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #920]
.L188:
  ldr x0, [sp, #920]
  str x0, [sp, #112]
.L189:
  mov x0, #0
  str x0, [sp, #928]
.L190:
  ldr x1, [sp, #112]
  ldr x2, [sp, #928]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L196
.L191:
  mov x0, #0
  str x0, [sp, #936]
.L192:
  ldr x1, [sp, #112]
  ldr x2, [sp, #936]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L194
.L193:
  b .L195
.L194:
  mov x0, #1
  str x0, [sp, #176]
.L195:
  b .L197
.L196:
  mov x0, #1
  str x0, [sp, #184]
.L197:
  mov x0, #0
  str x0, [sp, #944]
.L198:
  ldr x1, [sp, #176]
  ldr x2, [sp, #944]
  cmp x1, x2
  b.ne .L203
.L199:
  mov x0, #0
  str x0, [sp, #952]
.L200:
  ldr x1, [sp, #184]
  ldr x2, [sp, #952]
  cmp x1, x2
  b.ne .L203
.L201:
  mov x0, #1
  str x0, [sp, #960]
.L202:
  b .L204
.L203:
  mov x0, #0
  str x0, [sp, #960]
.L204:
  ldr x1, [sp, #960]
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L206
.L205:
  b .L218
.L206:
  mov x0, #1
  str x0, [sp, #968]
.L207:
  ldr x1, [sp, #24]
  ldr x2, [sp, #968]
  add x0, x1, x2
  str x0, [sp, #24]
.L208:
  mov x0, #1
  str x0, [sp, #976]
.L209:
  ldr x1, [sp, #976]
  adrp x0, _arr_zone@PAGE
  add x0, x0, _arr_zone@PAGEOFF
  ldr x0, [x0, x1, lsl #3]
  str x0, [sp, #984]
.L210:
  ldr x1, [sp, #984]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L212
.L211:
  b .L213
.L212:
  mov x0, #1
  str x0, [sp, #24]
.L213:
  ldr x1, [sp, #32]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L216
.L214:
  mov x0, #1
  str x0, [sp, #176]
.L215:
  b .L218
.L216:
  mov x0, #1
  str x0, [sp, #192]
.L217:
  mov x0, #1
  str x0, [sp, #176]
.L218:
  mov x0, #1
  str x0, [sp, #992]
.L219:
  ldr x1, [sp, #40]
  ldr x2, [sp, #992]
  add x0, x1, x2
  str x0, [sp, #40]
.L220:
  b .L91
.L221:
  b .L80
.L222:
  mov x0, #1
  str x0, [sp, #1000]
.L223:
  ldr x1, [sp, #8]
  ldr x2, [sp, #1000]
  add x0, x1, x2
  str x0, [sp, #8]
.L224:
  b .L72
.L225:
  // print "%ld\n"
  sub sp, sp, #16
  ldr x1, [sp, #48]
  str x1, [sp, #0]
  adrp x0, .Lfmt_print_225@PAGE
  add x0, x0, .Lfmt_print_225@PAGEOFF
  bl _printf
  add sp, sp, #16
.L226:
  // print "%ld\n"
  sub sp, sp, #16
  ldr x1, [sp, #56]
  str x1, [sp, #0]
  adrp x0, .Lfmt_print_226@PAGE
  add x0, x0, .Lfmt_print_226@PAGEOFF
  bl _printf
  add sp, sp, #16
.L227:
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
  // print m
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x1, .Lname_m@PAGE
  add x1, x1, .Lname_m@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i1
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x1, .Lname_i1@PAGE
  add x1, x1, .Lname_i1@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x1, .Lname_k@PAGE
  add x1, x1, .Lname_k@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k2
  ldr x9, [sp, #48]
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
  ldr x9, [sp, #56]
  sub sp, sp, #16
  adrp x1, .Lname_k3@PAGE
  add x1, x1, .Lname_k3@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j2
  ldr x9, [sp, #64]
  sub sp, sp, #16
  adrp x1, .Lname_j2@PAGE
  add x1, x1, .Lname_j2@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j4
  ldr x9, [sp, #72]
  sub sp, sp, #16
  adrp x1, .Lname_j4@PAGE
  add x1, x1, .Lname_j4@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j5
  ldr x9, [sp, #80]
  sub sp, sp, #16
  adrp x1, .Lname_j5@PAGE
  add x1, x1, .Lname_j5@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ii
  ldr x9, [sp, #88]
  sub sp, sp, #16
  adrp x1, .Lname_ii@PAGE
  add x1, x1, .Lname_ii@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print lb
  ldr x9, [sp, #96]
  sub sp, sp, #16
  adrp x1, .Lname_lb@PAGE
  add x1, x1, .Lname_lb@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print n
  ldr x9, [sp, #104]
  sub sp, sp, #16
  adrp x1, .Lname_n@PAGE
  add x1, x1, .Lname_n@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print zval
  ldr x9, [sp, #112]
  sub sp, sp, #16
  adrp x1, .Lname_zval@PAGE
  add x1, x1, .Lname_zval@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r (float)
  ldr d0, [sp, #120]
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
  ldr d0, [sp, #128]
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
  ldr d0, [sp, #136]
  sub sp, sp, #32
  adrp x1, .Lname_t@PAGE
  add x1, x1, .Lname_t@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print tmp (float)
  ldr d0, [sp, #144]
  sub sp, sp, #32
  adrp x1, .Lname_tmp@PAGE
  add x1, x1, .Lname_tmp@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #152]
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
  ldr d0, [sp, #160]
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
  ldr d0, [sp, #168]
  sub sp, sp, #32
  adrp x1, .Lname_fizz@PAGE
  add x1, x1, .Lname_fizz@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print kbreak
  ldr x9, [sp, #176]
  sub sp, sp, #16
  adrp x1, .Lname_kbreak@PAGE
  add x1, x1, .Lname_kbreak@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print kcont
  ldr x9, [sp, #184]
  sub sp, sp, #16
  adrp x1, .Lname_kcont@PAGE
  add x1, x1, .Lname_kcont@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print restart
  ldr x9, [sp, #192]
  sub sp, sp, #16
  adrp x1, .Lname_restart@PAGE
  add x1, x1, .Lname_restart@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #1008]
  ldr x30, [sp, #1016]
  add sp, sp, #1024
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

.Lfmt_print_225:
  .asciz "%ld\n"
.Lfmt_print_226:
  .asciz "%ld\n"

.Lname_rep:
  .asciz "rep"
.Lname_i:
  .asciz "i"
.Lname_m:
  .asciz "m"
.Lname_i1:
  .asciz "i1"
.Lname_k:
  .asciz "k"
.Lname_k2:
  .asciz "k2"
.Lname_k3:
  .asciz "k3"
.Lname_j2:
  .asciz "j2"
.Lname_j4:
  .asciz "j4"
.Lname_j5:
  .asciz "j5"
.Lname_ii:
  .asciz "ii"
.Lname_lb:
  .asciz "lb"
.Lname_n:
  .asciz "n"
.Lname_zval:
  .asciz "zval"
.Lname_r:
  .asciz "r"
.Lname_s:
  .asciz "s"
.Lname_t:
  .asciz "t"
.Lname_tmp:
  .asciz "tmp"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"
.Lname_kbreak:
  .asciz "kbreak"
.Lname_kcont:
  .asciz "kcont"
.Lname_restart:
  .asciz "restart"

.section __DATA,__data
.global _arr_d
.align 3
_arr_d:
  .space 2408
.global _arr_plan
.align 3
_arr_plan:
  .space 2408
.global _arr_zone
.align 3
_arr_zone:
  .space 2408
