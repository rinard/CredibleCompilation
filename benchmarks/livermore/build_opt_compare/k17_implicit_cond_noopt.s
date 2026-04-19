.global _main
.align 2

_main:
  sub sp, sp, #752
  str x30, [sp, #744]
  str x29, [sp, #736]
  add x29, sp, #736

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
  mov x0, #101
  str x0, [sp, #40]
.L18:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #104]
.L19:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #144]
.L20:
  ldr d1, [sp, #144]
  ldr d2, [sp, #104]
  fadd d0, d1, d2
  str d0, [sp, #112]
.L21:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #152]
.L22:
  ldr d1, [sp, #152]
  ldr d2, [sp, #104]
  fmul d0, d1, d2
  str d0, [sp, #120]
.L23:
  mov x0, #1
  str x0, [sp, #48]
.L24:
  ldr x1, [sp, #48]
  ldr x2, [sp, #40]
  cmp x1, x2
  b.gt .L62
.L25:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #160]
.L26:
  ldr d1, [sp, #160]
  ldr d2, [sp, #104]
  fsub d0, d1, d2
  str d0, [sp, #168]
.L27:
  ldr d1, [sp, #168]
  ldr d2, [sp, #112]
  fmul d0, d1, d2
  str d0, [sp, #176]
.L28:
  ldr d1, [sp, #176]
  ldr d2, [sp, #104]
  fadd d0, d1, d2
  str d0, [sp, #112]
.L29:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #184]
.L30:
  ldr d1, [sp, #184]
  ldr d2, [sp, #104]
  fsub d0, d1, d2
  str d0, [sp, #104]
.L31:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L32:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #200]
.L33:
  ldr d1, [sp, #192]
  ldr d2, [sp, #200]
  fmul d0, d1, d2
  str d0, [sp, #208]
.L34:
  ldr x1, [sp, #48]
  ldr d0, [sp, #208]
  adrp x0, _arr_vsp@PAGE
  add x0, x0, _arr_vsp@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L35:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #216]
.L36:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #224]
.L37:
  ldr d1, [sp, #216]
  ldr d2, [sp, #224]
  fmul d0, d1, d2
  str d0, [sp, #232]
.L38:
  ldr x1, [sp, #48]
  ldr d0, [sp, #232]
  adrp x0, _arr_vstp@PAGE
  add x0, x0, _arr_vstp@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L39:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #240]
.L40:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #248]
.L41:
  ldr d1, [sp, #240]
  ldr d2, [sp, #248]
  fmul d0, d1, d2
  str d0, [sp, #256]
.L42:
  ldr x1, [sp, #48]
  ldr d0, [sp, #256]
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L43:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #264]
.L44:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #272]
.L45:
  ldr d1, [sp, #264]
  ldr d2, [sp, #272]
  fmul d0, d1, d2
  str d0, [sp, #280]
.L46:
  ldr x1, [sp, #48]
  ldr d0, [sp, #280]
  adrp x0, _arr_vxnd@PAGE
  add x0, x0, _arr_vxnd@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L47:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #288]
.L48:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #296]
.L49:
  ldr d1, [sp, #288]
  ldr d2, [sp, #296]
  fmul d0, d1, d2
  str d0, [sp, #304]
.L50:
  ldr x1, [sp, #48]
  ldr d0, [sp, #304]
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L51:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #312]
.L52:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #320]
.L53:
  ldr d1, [sp, #312]
  ldr d2, [sp, #320]
  fmul d0, d1, d2
  str d0, [sp, #328]
.L54:
  ldr x1, [sp, #48]
  ldr d0, [sp, #328]
  adrp x0, _arr_vlr@PAGE
  add x0, x0, _arr_vlr@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L55:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fsub d0, d1, d2
  str d0, [sp, #336]
.L56:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #344]
.L57:
  ldr d1, [sp, #336]
  ldr d2, [sp, #344]
  fmul d0, d1, d2
  str d0, [sp, #352]
.L58:
  ldr x1, [sp, #48]
  ldr d0, [sp, #352]
  adrp x0, _arr_vlin@PAGE
  add x0, x0, _arr_vlin@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L59:
  mov x0, #1
  str x0, [sp, #360]
.L60:
  ldr x1, [sp, #48]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #48]
.L61:
  b .L24
.L62:
  mov x0, #1
  str x0, [sp, #8]
.L63:
  movz x0, #44864
  movk x0, #351, lsl #16
  str x0, [sp, #368]
.L64:
  ldr x1, [sp, #8]
  ldr x2, [sp, #368]
  cmp x1, x2
  b.gt .L149
.L65:
  mov x0, #1
  str x0, [sp, #376]
.L66:
  ldr x1, [sp, #40]
  ldr x2, [sp, #376]
  sub x0, x1, x2
  str x0, [sp, #16]
.L67:
  mov x0, #0
  str x0, [sp, #24]
.L68:
  mov x0, #0
  str x0, [sp, #384]
.L69:
  mov x0, #1
  str x0, [sp, #392]
.L70:
  ldr x1, [sp, #384]
  ldr x2, [sp, #392]
  sub x0, x1, x2
  str x0, [sp, #32]
.L71:
  movz x0, #0
  movk x0, #16404, lsl #48
  fmov d0, x0
  str d0, [sp, #400]
.L72:
  movz x0, #0
  movk x0, #16392, lsl #48
  fmov d0, x0
  str d0, [sp, #408]
.L73:
  ldr d1, [sp, #400]
  ldr d2, [sp, #408]
  fdiv d0, d1, d2
  str d0, [sp, #56]
.L74:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #416]
.L75:
  movz x0, #0
  movk x0, #16392, lsl #48
  fmov d0, x0
  str d0, [sp, #424]
.L76:
  ldr d1, [sp, #416]
  ldr d2, [sp, #424]
  fdiv d0, d1, d2
  str d0, [sp, #64]
.L77:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #432]
.L78:
  movz x0, #49807
  movk x0, #10485, lsl #16
  movk x0, #36700, lsl #32
  movk x0, #16392, lsl #48
  fmov d0, x0
  str d0, [sp, #440]
.L79:
  ldr d1, [sp, #432]
  ldr d2, [sp, #440]
  fdiv d0, d1, d2
  str d0, [sp, #72]
.L80:
  mov x0, #1
  str x0, [sp, #128]
.L81:
  mov x0, #0
  str x0, [sp, #136]
.L82:
  mov x0, #0
  str x0, [sp, #448]
.L83:
  ldr x1, [sp, #136]
  ldr x2, [sp, #448]
  cmp x1, x2
  b.ne .L146
.L84:
  mov x0, #0
  str x0, [sp, #456]
.L85:
  ldr x1, [sp, #128]
  ldr x2, [sp, #456]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L125
.L86:
  mov x0, #1
  str x0, [sp, #464]
.L87:
  ldr x1, [sp, #16]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #472]
.L88:
  ldr x1, [sp, #472]
  cmp x1, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vlr@PAGE
  add x0, x0, _arr_vlr@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #480]
.L89:
  ldr d1, [sp, #64]
  ldr d2, [sp, #480]
  fmul d0, d1, d2
  str d0, [sp, #488]
.L90:
  mov x0, #1
  str x0, [sp, #496]
.L91:
  ldr x1, [sp, #16]
  ldr x2, [sp, #496]
  add x0, x1, x2
  str x0, [sp, #504]
.L92:
  ldr x1, [sp, #504]
  cmp x1, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vlin@PAGE
  add x0, x0, _arr_vlin@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #512]
.L93:
  ldr d1, [sp, #488]
  ldr d2, [sp, #512]
  fadd d0, d1, d2
  str d0, [sp, #80]
.L94:
  mov x0, #1
  str x0, [sp, #520]
.L95:
  ldr x1, [sp, #16]
  ldr x2, [sp, #520]
  add x0, x1, x2
  str x0, [sp, #528]
.L96:
  ldr x1, [sp, #528]
  cmp x1, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #536]
.L97:
  ldr x0, [sp, #536]
  str x0, [sp, #88]
.L98:
  mov x0, #1
  str x0, [sp, #544]
.L99:
  ldr x1, [sp, #16]
  ldr x2, [sp, #544]
  add x0, x1, x2
  str x0, [sp, #552]
.L100:
  ldr x1, [sp, #552]
  cmp x1, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #72]
  adrp x0, _arr_vxnd@PAGE
  add x0, x0, _arr_vxnd@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L101:
  ldr d1, [sp, #56]
  ldr d2, [sp, #80]
  fmul d0, d1, d2
  str d0, [sp, #96]
.L102:
  ldr d1, [sp, #96]
  ldr d2, [sp, #64]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L123
.L103:
  ldr d1, [sp, #96]
  ldr d2, [sp, #88]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L121
.L104:
  mov x0, #1
  str x0, [sp, #560]
.L105:
  ldr x1, [sp, #16]
  ldr x2, [sp, #560]
  add x0, x1, x2
  str x0, [sp, #568]
.L106:
  ldr x1, [sp, #568]
  cmp x1, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #80]
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L107:
  ldr d1, [sp, #80]
  ldr d2, [sp, #80]
  fadd d0, d1, d2
  str d0, [sp, #576]
.L108:
  ldr d1, [sp, #576]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #72]
.L109:
  mov x0, #1
  str x0, [sp, #584]
.L110:
  ldr x1, [sp, #16]
  ldr x2, [sp, #584]
  add x0, x1, x2
  str x0, [sp, #592]
.L111:
  ldr d1, [sp, #80]
  ldr d2, [sp, #80]
  fadd d0, d1, d2
  str d0, [sp, #600]
.L112:
  ldr d1, [sp, #600]
  ldr d2, [sp, #88]
  fsub d0, d1, d2
  str d0, [sp, #608]
.L113:
  ldr x1, [sp, #592]
  cmp x1, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #608]
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L114:
  ldr x0, [sp, #72]
  str x0, [sp, #64]
.L115:
  ldr x1, [sp, #16]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #16]
.L116:
  ldr x1, [sp, #16]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L119
.L117:
  mov x0, #1
  str x0, [sp, #128]
.L118:
  b .L120
.L119:
  mov x0, #1
  str x0, [sp, #136]
.L120:
  b .L122
.L121:
  mov x0, #0
  str x0, [sp, #128]
.L122:
  b .L124
.L123:
  mov x0, #0
  str x0, [sp, #128]
.L124:
  b .L145
.L125:
  mov x0, #1
  str x0, [sp, #616]
.L126:
  ldr x1, [sp, #16]
  ldr x2, [sp, #616]
  add x0, x1, x2
  str x0, [sp, #624]
.L127:
  ldr x1, [sp, #624]
  cmp x1, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vsp@PAGE
  add x0, x0, _arr_vsp@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #632]
.L128:
  ldr d1, [sp, #64]
  ldr d2, [sp, #632]
  fmul d0, d1, d2
  str d0, [sp, #640]
.L129:
  mov x0, #1
  str x0, [sp, #648]
.L130:
  ldr x1, [sp, #16]
  ldr x2, [sp, #648]
  add x0, x1, x2
  str x0, [sp, #656]
.L131:
  ldr x1, [sp, #656]
  cmp x1, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vstp@PAGE
  add x0, x0, _arr_vstp@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #664]
.L132:
  ldr d1, [sp, #640]
  ldr d2, [sp, #664]
  fadd d0, d1, d2
  str d0, [sp, #72]
.L133:
  mov x0, #1
  str x0, [sp, #672]
.L134:
  ldr x1, [sp, #16]
  ldr x2, [sp, #672]
  add x0, x1, x2
  str x0, [sp, #680]
.L135:
  ldr x1, [sp, #680]
  cmp x1, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #72]
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L136:
  ldr x0, [sp, #72]
  str x0, [sp, #64]
.L137:
  mov x0, #1
  str x0, [sp, #688]
.L138:
  ldr x1, [sp, #16]
  ldr x2, [sp, #688]
  add x0, x1, x2
  str x0, [sp, #696]
.L139:
  ldr x1, [sp, #696]
  cmp x1, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #72]
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L140:
  ldr x1, [sp, #16]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #16]
.L141:
  ldr x1, [sp, #16]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L144
.L142:
  mov x0, #1
  str x0, [sp, #128]
.L143:
  b .L145
.L144:
  mov x0, #1
  str x0, [sp, #136]
.L145:
  b .L82
.L146:
  mov x0, #1
  str x0, [sp, #704]
.L147:
  ldr x1, [sp, #8]
  ldr x2, [sp, #704]
  add x0, x1, x2
  str x0, [sp, #8]
.L148:
  b .L63
.L149:
  mov x0, #51
  str x0, [sp, #712]
.L150:
  ldr x1, [sp, #712]
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #720]
.L151:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #720]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_151@PAGE
  add x0, x0, .Lfmt_print_151@PAGEOFF
  bl _printf
  add sp, sp, #16
.L152:
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
  // print j
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x1, .Lname_j@PAGE
  add x1, x1, .Lname_j@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ink
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x1, .Lname_ink@PAGE
  add x1, x1, .Lname_ink@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print n
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x1, .Lname_n@PAGE
  add x1, x1, .Lname_n@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x1, .Lname_k@PAGE
  add x1, x1, .Lname_k@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print scale (float)
  ldr d0, [sp, #56]
  sub sp, sp, #32
  adrp x1, .Lname_scale@PAGE
  add x1, x1, .Lname_scale@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print xnm (float)
  ldr d0, [sp, #64]
  sub sp, sp, #32
  adrp x1, .Lname_xnm@PAGE
  add x1, x1, .Lname_xnm@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print e6 (float)
  ldr d0, [sp, #72]
  sub sp, sp, #32
  adrp x1, .Lname_e6@PAGE
  add x1, x1, .Lname_e6@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print e3 (float)
  ldr d0, [sp, #80]
  sub sp, sp, #32
  adrp x1, .Lname_e3@PAGE
  add x1, x1, .Lname_e3@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print xnei (float)
  ldr d0, [sp, #88]
  sub sp, sp, #32
  adrp x1, .Lname_xnei@PAGE
  add x1, x1, .Lname_xnei@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print xnc (float)
  ldr d0, [sp, #96]
  sub sp, sp, #32
  adrp x1, .Lname_xnc@PAGE
  add x1, x1, .Lname_xnc@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #104]
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
  ldr d0, [sp, #112]
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
  ldr d0, [sp, #120]
  sub sp, sp, #32
  adrp x1, .Lname_fizz@PAGE
  add x1, x1, .Lname_fizz@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print phase
  ldr x9, [sp, #128]
  sub sp, sp, #16
  adrp x1, .Lname_phase@PAGE
  add x1, x1, .Lname_phase@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print done
  ldr x9, [sp, #136]
  sub sp, sp, #16
  adrp x1, .Lname_done@PAGE
  add x1, x1, .Lname_done@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #736]
  ldr x30, [sp, #744]
  add sp, sp, #752
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

.Lfmt_print_151:
  .asciz "%f\n"

.Lname_rep:
  .asciz "rep"
.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
.Lname_ink:
  .asciz "ink"
.Lname_n:
  .asciz "n"
.Lname_k:
  .asciz "k"
.Lname_scale:
  .asciz "scale"
.Lname_xnm:
  .asciz "xnm"
.Lname_e6:
  .asciz "e6"
.Lname_e3:
  .asciz "e3"
.Lname_xnei:
  .asciz "xnei"
.Lname_xnc:
  .asciz "xnc"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"
.Lname_phase:
  .asciz "phase"
.Lname_done:
  .asciz "done"

.section __DATA,__data
.global _arr_vsp
.align 3
_arr_vsp:
  .space 816
.global _arr_vstp
.align 3
_arr_vstp:
  .space 816
.global _arr_vxne
.align 3
_arr_vxne:
  .space 816
.global _arr_vxnd
.align 3
_arr_vxnd:
  .space 816
.global _arr_ve3
.align 3
_arr_ve3:
  .space 816
.global _arr_vlr
.align 3
_arr_vlr:
  .space 816
.global _arr_vlin
.align 3
_arr_vlin:
  .space 816
