.global _main
.align 2

_main:
  sub sp, sp, #688
  str x30, [sp, #680]
  str x29, [sp, #672]
  add x29, sp, #672

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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L8:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L10:
  ldr d1, [sp, #64]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #48]
.L11:
  mov x0, #1
  str x0, [sp, #8]
.L12:
  mov x0, #39
  str x0, [sp, #72]
.L13:
  ldr x1, [sp, #8]
  ldr x2, [sp, #72]
  cmp x1, x2
  b.gt .L27
.L14:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #80]
.L15:
  ldr d1, [sp, #80]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #88]
.L16:
  ldr d1, [sp, #88]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #96]
.L17:
  ldr d1, [sp, #96]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L18:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #104]
.L19:
  ldr d1, [sp, #104]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L20:
  ldr d1, [sp, #40]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #112]
.L21:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #120]
.L22:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fmul d0, d1, d2
  str d0, [sp, #128]
.L23:
  ldr x1, [sp, #8]
  ldr d0, [sp, #128]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L24:
  mov x0, #1
  str x0, [sp, #136]
.L25:
  ldr x1, [sp, #8]
  ldr x2, [sp, #136]
  add x0, x1, x2
  str x0, [sp, #8]
.L26:
  b .L12
.L27:
  mov x0, #26
  str x0, [sp, #144]
.L28:
  ldr x1, [sp, #144]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #152]
.L29:
  ldr x0, [sp, #152]
  str x0, [sp, #24]
.L30:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L31:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #160]
.L32:
  ldr d1, [sp, #160]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L33:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #168]
.L34:
  ldr d1, [sp, #168]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #48]
.L35:
  mov x0, #1
  str x0, [sp, #8]
.L36:
  mov x0, #1001
  str x0, [sp, #176]
.L37:
  ldr x1, [sp, #8]
  ldr x2, [sp, #176]
  cmp x1, x2
  b.gt .L51
.L38:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #184]
.L39:
  ldr d1, [sp, #184]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L40:
  ldr d1, [sp, #192]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #200]
.L41:
  ldr d1, [sp, #200]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L42:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #208]
.L43:
  ldr d1, [sp, #208]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L44:
  ldr d1, [sp, #40]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #216]
.L45:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #224]
.L46:
  ldr d1, [sp, #216]
  ldr d2, [sp, #224]
  fmul d0, d1, d2
  str d0, [sp, #232]
.L47:
  ldr x1, [sp, #8]
  ldr d0, [sp, #232]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L48:
  mov x0, #1
  str x0, [sp, #240]
.L49:
  ldr x1, [sp, #8]
  ldr x2, [sp, #240]
  add x0, x1, x2
  str x0, [sp, #8]
.L50:
  b .L36
.L51:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L52:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #248]
.L53:
  ldr d1, [sp, #248]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L54:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #256]
.L55:
  ldr d1, [sp, #256]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #48]
.L56:
  mov x0, #1
  str x0, [sp, #8]
.L57:
  mov x0, #1001
  str x0, [sp, #264]
.L58:
  ldr x1, [sp, #8]
  ldr x2, [sp, #264]
  cmp x1, x2
  b.gt .L78
.L59:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #272]
.L60:
  ldr d1, [sp, #272]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #280]
.L61:
  ldr d1, [sp, #280]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #288]
.L62:
  ldr d1, [sp, #288]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L63:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #296]
.L64:
  ldr d1, [sp, #296]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L65:
  ldr d1, [sp, #40]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #304]
.L66:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #312]
.L67:
  ldr d1, [sp, #304]
  ldr d2, [sp, #312]
  fmul d0, d1, d2
  str d0, [sp, #320]
.L68:
  ldr x1, [sp, #8]
  ldr d0, [sp, #320]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L69:
  ldr x1, [sp, #8]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #328]
.L70:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #336]
.L71:
  ldr d1, [sp, #328]
  ldr d2, [sp, #336]
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L73
.L72:
  b .L75
.L73:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #344]
.L74:
  ldr x1, [sp, #8]
  ldr d0, [sp, #344]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L75:
  mov x0, #1
  str x0, [sp, #352]
.L76:
  ldr x1, [sp, #8]
  ldr x2, [sp, #352]
  add x0, x1, x2
  str x0, [sp, #8]
.L77:
  b .L57
.L78:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L79:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #360]
.L80:
  ldr d1, [sp, #360]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L81:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #368]
.L82:
  ldr d1, [sp, #368]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #48]
.L83:
  mov x0, #1
  str x0, [sp, #8]
.L84:
  mov x0, #1001
  str x0, [sp, #376]
.L85:
  ldr x1, [sp, #8]
  ldr x2, [sp, #376]
  cmp x1, x2
  b.gt .L105
.L86:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #384]
.L87:
  ldr d1, [sp, #384]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #392]
.L88:
  ldr d1, [sp, #392]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #400]
.L89:
  ldr d1, [sp, #400]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L90:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #408]
.L91:
  ldr d1, [sp, #408]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L92:
  ldr d1, [sp, #40]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #416]
.L93:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #424]
.L94:
  ldr d1, [sp, #416]
  ldr d2, [sp, #424]
  fmul d0, d1, d2
  str d0, [sp, #432]
.L95:
  ldr x1, [sp, #8]
  ldr d0, [sp, #432]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L96:
  ldr x1, [sp, #8]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #440]
.L97:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #448]
.L98:
  ldr d1, [sp, #440]
  ldr d2, [sp, #448]
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L100
.L99:
  b .L102
.L100:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d0, x0
  str d0, [sp, #456]
.L101:
  ldr x1, [sp, #8]
  ldr d0, [sp, #456]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L102:
  mov x0, #1
  str x0, [sp, #464]
.L103:
  ldr x1, [sp, #8]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #8]
.L104:
  b .L84
.L105:
  mov x0, #1
  str x0, [sp, #8]
.L106:
  mov x0, #1001
  str x0, [sp, #472]
.L107:
  ldr x1, [sp, #8]
  ldr x2, [sp, #472]
  cmp x1, x2
  b.gt .L115
.L108:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #480]
.L109:
  ldr x1, [sp, #8]
  ldr d0, [sp, #480]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L110:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #488]
.L111:
  ldr x1, [sp, #8]
  ldr d0, [sp, #488]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L112:
  mov x0, #1
  str x0, [sp, #496]
.L113:
  ldr x1, [sp, #8]
  ldr x2, [sp, #496]
  add x0, x1, x2
  str x0, [sp, #8]
.L114:
  b .L106
.L115:
  mov x0, #1
  str x0, [sp, #16]
.L116:
  movz x0, #39104
  movk x0, #11, lsl #16
  str x0, [sp, #504]
.L117:
  ldr x1, [sp, #16]
  ldr x2, [sp, #504]
  cmp x1, x2
  b.gt .L146
.L118:
  movz x0, #0
  movk x0, #16436, lsl #48
  fmov d0, x0
  str d0, [sp, #24]
.L119:
  mov x0, #101
  str x0, [sp, #512]
.L120:
  movz x0, #18350
  movk x0, #31457, lsl #16
  movk x0, #44564, lsl #32
  movk x0, #16367, lsl #48
  fmov d0, x0
  str d0, [sp, #520]
.L121:
  ldr d1, [sp, #520]
  ldr d2, [sp, #24]
  fmul d0, d1, d2
  str d0, [sp, #528]
.L122:
  mov x0, #101
  str x0, [sp, #536]
.L123:
  ldr x1, [sp, #536]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #544]
.L124:
  ldr d1, [sp, #528]
  ldr d2, [sp, #544]
  fmul d0, d1, d2
  str d0, [sp, #552]
.L125:
  ldr x1, [sp, #512]
  ldr d0, [sp, #552]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L126:
  mov x0, #1
  str x0, [sp, #8]
.L127:
  mov x0, #101
  str x0, [sp, #560]
.L128:
  ldr x1, [sp, #8]
  ldr x2, [sp, #560]
  cmp x1, x2
  b.gt .L143
.L129:
  ldr x1, [sp, #8]
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #568]
.L130:
  ldr x1, [sp, #8]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #576]
.L131:
  ldr d1, [sp, #568]
  ldr d2, [sp, #576]
  fdiv d0, d1, d2
  str d0, [sp, #584]
.L132:
  ldr x1, [sp, #8]
  ldr d0, [sp, #584]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L133:
  ldr x1, [sp, #8]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #592]
.L134:
  ldr x1, [sp, #8]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #600]
.L135:
  ldr d0, [sp, #600]
  stp x29, x30, [sp, #-16]!
  bl _exp
  ldp x29, x30, [sp], #16
  str d0, [sp, #608]
.L136:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #616]
.L137:
  ldr d1, [sp, #608]
  ldr d2, [sp, #616]
  fsub d0, d1, d2
  str d0, [sp, #624]
.L138:
  ldr d1, [sp, #592]
  ldr d2, [sp, #624]
  fdiv d0, d1, d2
  str d0, [sp, #632]
.L139:
  ldr x1, [sp, #8]
  ldr d0, [sp, #632]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L140:
  mov x0, #1
  str x0, [sp, #640]
.L141:
  ldr x1, [sp, #8]
  ldr x2, [sp, #640]
  add x0, x1, x2
  str x0, [sp, #8]
.L142:
  b .L127
.L143:
  mov x0, #1
  str x0, [sp, #648]
.L144:
  ldr x1, [sp, #16]
  ldr x2, [sp, #648]
  add x0, x1, x2
  str x0, [sp, #16]
.L145:
  b .L116
.L146:
  mov x0, #51
  str x0, [sp, #656]
.L147:
  ldr x1, [sp, #656]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #664]
.L148:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #664]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_148@PAGE
  add x0, x0, .Lfmt_print_148@PAGEOFF
  bl _printf
  add sp, sp, #16
.L149:
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
  // print expmax (float)
  ldr d0, [sp, #24]
  sub sp, sp, #32
  adrp x1, .Lname_expmax@PAGE
  add x1, x1, .Lname_expmax@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #32]
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
  ldr d0, [sp, #40]
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
  ldr d0, [sp, #48]
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
  ldr x29, [sp, #672]
  ldr x30, [sp, #680]
  add sp, sp, #688
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

.Lfmt_print_148:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_expmax:
  .asciz "expmax"
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
.global _arr_v
.align 3
_arr_v:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_w
.align 3
_arr_w:
  .space 8016
