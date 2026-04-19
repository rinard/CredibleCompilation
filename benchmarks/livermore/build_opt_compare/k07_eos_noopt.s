.global _main
.align 2

_main:
  sub sp, sp, #864
  str x30, [sp, #856]
  str x29, [sp, #848]
  add x29, sp, #848

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
  mov x0, #39
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
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
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
  mov x0, #28
  str x0, [sp, #160]
.L30:
  ldr x1, [sp, #160]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #168]
.L31:
  ldr x0, [sp, #168]
  str x0, [sp, #40]
.L32:
  mov x0, #30
  str x0, [sp, #176]
.L33:
  ldr x1, [sp, #176]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #184]
.L34:
  ldr x0, [sp, #184]
  str x0, [sp, #24]
.L35:
  mov x0, #36
  str x0, [sp, #192]
.L36:
  ldr x1, [sp, #192]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #200]
.L37:
  ldr x0, [sp, #200]
  str x0, [sp, #32]
.L38:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #208]
.L40:
  ldr d1, [sp, #208]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #216]
.L42:
  ldr d1, [sp, #216]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L43:
  mov x0, #1
  str x0, [sp, #8]
.L44:
  mov x0, #1001
  str x0, [sp, #224]
.L45:
  ldr x1, [sp, #8]
  ldr x2, [sp, #224]
  cmp x1, x2
  b.gt .L59
.L46:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #232]
.L47:
  ldr d1, [sp, #232]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #240]
.L48:
  ldr d1, [sp, #240]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #248]
.L49:
  ldr d1, [sp, #248]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L50:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #256]
.L51:
  ldr d1, [sp, #256]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L52:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #264]
.L53:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #272]
.L54:
  ldr d1, [sp, #264]
  ldr d2, [sp, #272]
  fmul d0, d1, d2
  str d0, [sp, #280]
.L55:
  ldr x1, [sp, #8]
  ldr d0, [sp, #280]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L56:
  mov x0, #1
  str x0, [sp, #288]
.L57:
  ldr x1, [sp, #8]
  ldr x2, [sp, #288]
  add x0, x1, x2
  str x0, [sp, #8]
.L58:
  b .L44
.L59:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L60:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #296]
.L61:
  ldr d1, [sp, #296]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #304]
.L63:
  ldr d1, [sp, #304]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L64:
  mov x0, #1
  str x0, [sp, #8]
.L65:
  mov x0, #1001
  str x0, [sp, #312]
.L66:
  ldr x1, [sp, #8]
  ldr x2, [sp, #312]
  cmp x1, x2
  b.gt .L80
.L67:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #320]
.L68:
  ldr d1, [sp, #320]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #328]
.L69:
  ldr d1, [sp, #328]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #336]
.L70:
  ldr d1, [sp, #336]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L71:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #344]
.L72:
  ldr d1, [sp, #344]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L73:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #352]
.L74:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #360]
.L75:
  ldr d1, [sp, #352]
  ldr d2, [sp, #360]
  fmul d0, d1, d2
  str d0, [sp, #368]
.L76:
  ldr x1, [sp, #8]
  ldr d0, [sp, #368]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L77:
  mov x0, #1
  str x0, [sp, #376]
.L78:
  ldr x1, [sp, #8]
  ldr x2, [sp, #376]
  add x0, x1, x2
  str x0, [sp, #8]
.L79:
  b .L65
.L80:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L81:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #384]
.L82:
  ldr d1, [sp, #384]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L83:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #392]
.L84:
  ldr d1, [sp, #392]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L85:
  mov x0, #1
  str x0, [sp, #8]
.L86:
  mov x0, #1001
  str x0, [sp, #400]
.L87:
  ldr x1, [sp, #8]
  ldr x2, [sp, #400]
  cmp x1, x2
  b.gt .L101
.L88:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #408]
.L89:
  ldr d1, [sp, #408]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #416]
.L90:
  ldr d1, [sp, #416]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #424]
.L91:
  ldr d1, [sp, #424]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L92:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #432]
.L93:
  ldr d1, [sp, #432]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L94:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #440]
.L95:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #448]
.L96:
  ldr d1, [sp, #440]
  ldr d2, [sp, #448]
  fmul d0, d1, d2
  str d0, [sp, #456]
.L97:
  ldr x1, [sp, #8]
  ldr d0, [sp, #456]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L98:
  mov x0, #1
  str x0, [sp, #464]
.L99:
  ldr x1, [sp, #8]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #8]
.L100:
  b .L86
.L101:
  mov x0, #1
  str x0, [sp, #8]
.L102:
  mov x0, #1001
  str x0, [sp, #472]
.L103:
  ldr x1, [sp, #8]
  ldr x2, [sp, #472]
  cmp x1, x2
  b.gt .L109
.L104:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #480]
.L105:
  ldr x1, [sp, #8]
  ldr d0, [sp, #480]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L106:
  mov x0, #1
  str x0, [sp, #488]
.L107:
  ldr x1, [sp, #8]
  ldr x2, [sp, #488]
  add x0, x1, x2
  str x0, [sp, #8]
.L108:
  b .L102
.L109:
  mov x0, #1
  str x0, [sp, #16]
.L110:
  movz x0, #3200
  movk x0, #175, lsl #16
  str x0, [sp, #496]
.L111:
  ldr x1, [sp, #16]
  ldr x2, [sp, #496]
  cmp x1, x2
  b.gt .L159
.L112:
  mov x0, #1
  str x0, [sp, #8]
.L113:
  mov x0, #995
  str x0, [sp, #504]
.L114:
  ldr x1, [sp, #8]
  ldr x2, [sp, #504]
  cmp x1, x2
  b.gt .L156
.L115:
  ldr x1, [sp, #8]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #512]
.L116:
  ldr x1, [sp, #8]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #520]
.L117:
  ldr x1, [sp, #8]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #528]
.L118:
  ldr d1, [sp, #24]
  ldr d2, [sp, #528]
  fmul d0, d1, d2
  str d0, [sp, #536]
.L119:
  ldr d1, [sp, #520]
  ldr d2, [sp, #536]
  fadd d0, d1, d2
  str d0, [sp, #544]
.L120:
  ldr d1, [sp, #24]
  ldr d2, [sp, #544]
  fmul d0, d1, d2
  str d0, [sp, #552]
.L121:
  ldr d1, [sp, #512]
  ldr d2, [sp, #552]
  fadd d0, d1, d2
  str d0, [sp, #560]
.L122:
  mov x0, #3
  str x0, [sp, #568]
.L123:
  ldr x1, [sp, #8]
  ldr x2, [sp, #568]
  add x0, x1, x2
  str x0, [sp, #576]
.L124:
  ldr x1, [sp, #576]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #584]
.L125:
  mov x0, #2
  str x0, [sp, #592]
.L126:
  ldr x1, [sp, #8]
  ldr x2, [sp, #592]
  add x0, x1, x2
  str x0, [sp, #600]
.L127:
  ldr x1, [sp, #600]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #608]
.L128:
  mov x0, #1
  str x0, [sp, #616]
.L129:
  ldr x1, [sp, #8]
  ldr x2, [sp, #616]
  add x0, x1, x2
  str x0, [sp, #624]
.L130:
  ldr x1, [sp, #624]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #632]
.L131:
  ldr d1, [sp, #24]
  ldr d2, [sp, #632]
  fmul d0, d1, d2
  str d0, [sp, #640]
.L132:
  ldr d1, [sp, #608]
  ldr d2, [sp, #640]
  fadd d0, d1, d2
  str d0, [sp, #648]
.L133:
  ldr d1, [sp, #24]
  ldr d2, [sp, #648]
  fmul d0, d1, d2
  str d0, [sp, #656]
.L134:
  ldr d1, [sp, #584]
  ldr d2, [sp, #656]
  fadd d0, d1, d2
  str d0, [sp, #664]
.L135:
  mov x0, #6
  str x0, [sp, #672]
.L136:
  ldr x1, [sp, #8]
  ldr x2, [sp, #672]
  add x0, x1, x2
  str x0, [sp, #680]
.L137:
  ldr x1, [sp, #680]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #688]
.L138:
  mov x0, #5
  str x0, [sp, #696]
.L139:
  ldr x1, [sp, #8]
  ldr x2, [sp, #696]
  add x0, x1, x2
  str x0, [sp, #704]
.L140:
  ldr x1, [sp, #704]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #712]
.L141:
  mov x0, #4
  str x0, [sp, #720]
.L142:
  ldr x1, [sp, #8]
  ldr x2, [sp, #720]
  add x0, x1, x2
  str x0, [sp, #728]
.L143:
  ldr x1, [sp, #728]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #736]
.L144:
  ldr d1, [sp, #40]
  ldr d2, [sp, #736]
  fmul d0, d1, d2
  str d0, [sp, #744]
.L145:
  ldr d1, [sp, #712]
  ldr d2, [sp, #744]
  fadd d0, d1, d2
  str d0, [sp, #752]
.L146:
  ldr d1, [sp, #40]
  ldr d2, [sp, #752]
  fmul d0, d1, d2
  str d0, [sp, #760]
.L147:
  ldr d1, [sp, #688]
  ldr d2, [sp, #760]
  fadd d0, d1, d2
  str d0, [sp, #768]
.L148:
  ldr d1, [sp, #32]
  ldr d2, [sp, #768]
  fmul d0, d1, d2
  str d0, [sp, #776]
.L149:
  ldr d1, [sp, #664]
  ldr d2, [sp, #776]
  fadd d0, d1, d2
  str d0, [sp, #784]
.L150:
  ldr d1, [sp, #32]
  ldr d2, [sp, #784]
  fmul d0, d1, d2
  str d0, [sp, #792]
.L151:
  ldr d1, [sp, #560]
  ldr d2, [sp, #792]
  fadd d0, d1, d2
  str d0, [sp, #800]
.L152:
  ldr x1, [sp, #8]
  ldr d0, [sp, #800]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L153:
  mov x0, #1
  str x0, [sp, #808]
.L154:
  ldr x1, [sp, #8]
  ldr x2, [sp, #808]
  add x0, x1, x2
  str x0, [sp, #8]
.L155:
  b .L113
.L156:
  mov x0, #1
  str x0, [sp, #816]
.L157:
  ldr x1, [sp, #16]
  ldr x2, [sp, #816]
  add x0, x1, x2
  str x0, [sp, #16]
.L158:
  b .L110
.L159:
  mov x0, #1
  str x0, [sp, #824]
.L160:
  ldr x1, [sp, #824]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #832]
.L161:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #832]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_161@PAGE
  add x0, x0, .Lfmt_print_161@PAGEOFF
  bl _printf
  add sp, sp, #16
.L162:
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
  // print r (float)
  ldr d0, [sp, #24]
  sub sp, sp, #32
  adrp x1, .Lname_r@PAGE
  add x1, x1, .Lname_r@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x1, .Lname_t@PAGE
  add x1, x1, .Lname_t@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print q (float)
  ldr d0, [sp, #40]
  sub sp, sp, #32
  adrp x1, .Lname_q@PAGE
  add x1, x1, .Lname_q@PAGEOFF
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
  ldr x29, [sp, #848]
  ldr x30, [sp, #856]
  add sp, sp, #864
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

.Lfmt_print_161:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_r:
  .asciz "r"
.Lname_t:
  .asciz "t"
.Lname_q:
  .asciz "q"
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
.global _arr_u
.align 3
_arr_u:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
