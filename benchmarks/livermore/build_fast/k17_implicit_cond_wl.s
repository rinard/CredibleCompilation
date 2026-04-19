.global _main
.align 2

_main:
  sub sp, sp, #560
  str x30, [sp, #552]
  str x29, [sp, #544]
  add x29, sp, #544
  // Save callee-saved registers
  str x19, [sp, #456]
  str x20, [sp, #464]
  str d15, [sp, #472]
  str d14, [sp, #480]
  str d13, [sp, #488]
  str d12, [sp, #496]
  str d11, [sp, #504]
  str d10, [sp, #512]
  str d9, [sp, #520]
  str d8, [sp, #528]

  // Initialize all variables to 0
  mov x0, #0

  mov x9, #0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  mov x11, #0
  mov x10, #0
  str x0, [sp, #56]
  str x0, [sp, #64]
  str x0, [sp, #72]
  str x0, [sp, #80]
  str x0, [sp, #88]
  fmov d15, x0
  str x0, [sp, #104]
  str x0, [sp, #112]
  fmov d14, x0
  mov x13, #0
  mov x12, #0
  fmov d3, x0
  fmov d13, x0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  fmov d5, x0
  mov x3, #0
  fmov d4, x0
  mov x20, #0
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]
  mov x8, #0
  mov x7, #0
  mov x6, #0
  str x0, [sp, #296]
  str x0, [sp, #304]
  str x0, [sp, #312]
  str x0, [sp, #320]
  str x0, [sp, #328]
  mov x5, #0
  str x0, [sp, #344]
  str x0, [sp, #352]
  str x0, [sp, #360]
  mov x4, #0
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

.L0:
  mov x0, #0
  mov x9, x0
.L1:
  mov x0, #0
  mov x19, x0
.L2:
  mov x0, #0
  mov x15, x0
.L3:
  mov x0, #0
  mov x14, x0
.L4:
  mov x0, #0
  mov x11, x0
.L5:
  mov x0, #0
  mov x10, x0
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
  fmov d15, x0
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
  fmov d14, x0
.L15:
  mov x0, #0
  mov x13, x0
.L16:
  mov x0, #0
  mov x12, x0
.L17:
  mov x0, #101
  mov x11, x0
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
  fmov d3, x0
.L20:
  ldr d2, [sp, #104]
  fadd d0, d3, d2
  str d0, [sp, #112]
.L21:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L22:
  ldr d2, [sp, #104]
  fmul d14, d3, d2
.L23:
  mov x0, #1
  mov x10, x0
.L24:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d13, x0
.L25:
  mov x0, #0
  fmov d12, x0
.L26:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d11, x0
.L27:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L28:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d9, x0
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d8, x0
.L30:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d7, x0
.L31:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L32:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d5, x0
.L33:
  mov x0, #1
  mov x3, x0
.L34:
  cmp x10, x11
  b.gt .L61
.L35:
  ldr d2, [sp, #104]
  fsub d3, d13, d2
.L36:
  ldr d0, [sp, #104]
  ldr d2, [sp, #112]
  fmadd d0, d3, d2, d0
  str d0, [sp, #112]
.L37:
  ldr d2, [sp, #104]
  fsub d0, d12, d2
  str d0, [sp, #104]
.L38:
  ldr d1, [sp, #112]
  fsub d4, d1, d14
.L39:
  fmul d3, d4, d11
.L40:
  adrp x0, _arr_vsp@PAGE
  add x0, x0, _arr_vsp@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L41:
.L42:
  fmul d3, d4, d10
.L43:
  adrp x0, _arr_vstp@PAGE
  add x0, x0, _arr_vstp@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L44:
.L45:
  fmul d3, d4, d9
.L46:
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L47:
.L48:
  fmul d3, d4, d8
.L49:
  adrp x0, _arr_vxnd@PAGE
  add x0, x0, _arr_vxnd@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L50:
.L51:
  fmul d3, d4, d7
.L52:
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L53:
.L54:
  fmul d3, d4, d6
.L55:
  adrp x0, _arr_vlr@PAGE
  add x0, x0, _arr_vlr@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L56:
  fmov d3, d4
.L57:
  fmul d3, d3, d5
.L58:
  adrp x0, _arr_vlin@PAGE
  add x0, x0, _arr_vlin@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L59:
  add x10, x10, x3
.L60:
  b .L34
.L61:
  mov x0, #1
  mov x9, x0
.L62:
  mov x0, #23048
  mov x20, x0
.L63:
  mov x0, #1
  str x0, [sp, #248]
.L64:
  mov x0, #0
  str x0, [sp, #256]
.L65:
  mov x0, #1
  str x0, [sp, #264]
.L66:
  movz x0, #0
  movk x0, #16404, lsl #48
  fmov d8, x0
.L67:
  movz x0, #0
  movk x0, #16392, lsl #48
  fmov d7, x0
.L68:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L69:
  movz x0, #0
  movk x0, #16392, lsl #48
  fmov d5, x0
.L70:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16368, lsl #48
  fmov d4, x0
.L71:
  movz x0, #49807
  movk x0, #10485, lsl #16
  movk x0, #36700, lsl #32
  movk x0, #16392, lsl #48
  fmov d3, x0
.L72:
  mov x0, #0
  mov x8, x0
.L73:
  mov x0, #0
  mov x7, x0
.L74:
  mov x0, #1
  mov x6, x0
.L75:
  mov x0, #1
  str x0, [sp, #296]
.L76:
  mov x0, #1
  str x0, [sp, #304]
.L77:
  mov x0, #1
  str x0, [sp, #312]
.L78:
  mov x0, #1
  str x0, [sp, #320]
.L79:
  mov x0, #1
  str x0, [sp, #328]
.L80:
  mov x0, #1
  mov x5, x0
.L81:
  mov x0, #1
  str x0, [sp, #344]
.L82:
  mov x0, #1
  str x0, [sp, #352]
.L83:
  mov x0, #1
  str x0, [sp, #360]
.L84:
  mov x0, #1
  mov x4, x0
.L85:
  cmp x9, x20
  b.gt .L147
.L86:
  mov x0, #100
  mov x19, x0
.L87:
  movz x0, #65535
  movk x0, #65535, lsl #16
  movk x0, #65535, lsl #32
  movk x0, #65535, lsl #48
  mov x14, x0
.L88:
  fdiv d0, d8, d7
  str d0, [sp, #56]
.L89:
  fdiv d0, d6, d5
  str d0, [sp, #64]
.L90:
  fdiv d0, d4, d3
  str d0, [sp, #72]
.L91:
  mov x0, #1
  mov x13, x0
.L92:
  mov x0, #0
  mov x12, x0
.L93:
  cmp x12, x8
  b.ne .L145
.L94:
  mov x1, x13
  mov x2, x7
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L128
.L95:
  add x3, x19, x6
.L96:
  cmp x3, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vlr@PAGE
  add x0, x0, _arr_vlr@PAGEOFF
  ldr d9, [x0, x3, lsl #3]
.L97:
  ldr d1, [sp, #64]
  fmul d10, d1, d9
.L98:
  mov x0, x3
  mov x3, x0
.L99:
  cmp x3, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vlin@PAGE
  add x0, x0, _arr_vlin@PAGEOFF
  ldr d9, [x0, x3, lsl #3]
.L100:
  fadd d0, d10, d9
  str d0, [sp, #80]
.L101:
  mov x0, x3
  mov x3, x0
.L102:
  cmp x3, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  ldr d9, [x0, x3, lsl #3]
.L103:
  str d9, [sp, #88]
.L104:
  mov x0, x3
  mov x3, x0
.L105:
  cmp x3, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #72]
  adrp x0, _arr_vxnd@PAGE
  add x0, x0, _arr_vxnd@PAGEOFF
  str d0, [x0, x3, lsl #3]
.L106:
  ldr d1, [sp, #56]
  ldr d2, [sp, #80]
  fmul d15, d1, d2
.L107:
  fmov d1, d15
  ldr d2, [sp, #64]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L126
.L108:
  fmov d1, d15
  ldr d2, [sp, #88]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L124
.L109:
  mov x0, x3
  mov x3, x0
.L110:
  cmp x3, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #80]
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  str d0, [x0, x3, lsl #3]
.L111:
  ldr d1, [sp, #80]
  ldr d2, [sp, #80]
  fadd d9, d1, d2
.L112:
  ldr d2, [sp, #64]
  fsub d0, d9, d2
  str d0, [sp, #72]
.L113:
  mov x0, x3
  mov x3, x0
.L114:
  ldr d1, [sp, #80]
  ldr d2, [sp, #80]
  fadd d9, d1, d2
.L115:
  ldr d2, [sp, #88]
  fsub d9, d9, d2
.L116:
  cmp x3, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  str d9, [x0, x3, lsl #3]
.L117:
  ldr x0, [sp, #72]
  str x0, [sp, #64]
.L118:
  add x19, x19, x14
.L119:
  mov x1, x19
  mov x2, x15
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L122
.L120:
  mov x0, #1
  mov x13, x0
.L121:
  b .L123
.L122:
  mov x0, #1
  mov x12, x0
.L123:
  b .L125
.L124:
  mov x0, #0
  mov x13, x0
.L125:
  b .L127
.L126:
  mov x0, #0
  mov x13, x0
.L127:
  b .L144
.L128:
  add x3, x19, x5
.L129:
  cmp x3, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vsp@PAGE
  add x0, x0, _arr_vsp@PAGEOFF
  ldr d9, [x0, x3, lsl #3]
.L130:
  ldr d1, [sp, #64]
  fmul d10, d1, d9
.L131:
  mov x0, x3
  mov x3, x0
.L132:
  cmp x3, #102
  b.hs .Lbounds_err
  adrp x0, _arr_vstp@PAGE
  add x0, x0, _arr_vstp@PAGEOFF
  ldr d9, [x0, x3, lsl #3]
.L133:
  fadd d0, d10, d9
  str d0, [sp, #72]
.L134:
  mov x0, x3
  mov x3, x0
.L135:
  cmp x3, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #72]
  adrp x0, _arr_vxne@PAGE
  add x0, x0, _arr_vxne@PAGEOFF
  str d0, [x0, x3, lsl #3]
.L136:
  ldr x0, [sp, #72]
  str x0, [sp, #64]
.L137:
  mov x0, x3
  mov x3, x0
.L138:
  cmp x3, #102
  b.hs .Lbounds_err
  ldr d0, [sp, #72]
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  str d0, [x0, x3, lsl #3]
.L139:
  add x19, x19, x14
.L140:
  mov x1, x19
  mov x2, x15
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L143
.L141:
  mov x0, #1
  mov x13, x0
.L142:
  b .L144
.L143:
  mov x0, #1
  mov x12, x0
.L144:
  b .L93
.L145:
  add x9, x9, x4
.L146:
  b .L85
.L147:
  mov x0, #51
  mov x3, x0
.L148:
  adrp x0, _arr_ve3@PAGE
  add x0, x0, _arr_ve3@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L149:
  str x9, [sp, #8]
  str x15, [sp, #24]
  str x14, [sp, #32]
  str x11, [sp, #40]
  str x10, [sp, #48]
  str x13, [sp, #128]
  str x12, [sp, #136]
  str d3, [sp, #144]
  str d7, [sp, #200]
  str d6, [sp, #208]
  str d5, [sp, #216]
  str x3, [sp, #224]
  str d4, [sp, #232]
  str x8, [sp, #272]
  str x7, [sp, #280]
  str x6, [sp, #288]
  str x5, [sp, #336]
  str x4, [sp, #368]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_149@PAGE
  add x0, x0, .Lfmt_print_149@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x9, [sp, #8]
  ldr x15, [sp, #24]
  ldr x14, [sp, #32]
  ldr x11, [sp, #40]
  ldr x10, [sp, #48]
  ldr x13, [sp, #128]
  ldr x12, [sp, #136]
  ldr d3, [sp, #144]
  ldr d7, [sp, #200]
  ldr d6, [sp, #208]
  ldr d5, [sp, #216]
  ldr x3, [sp, #224]
  ldr d4, [sp, #232]
  ldr x8, [sp, #272]
  ldr x7, [sp, #280]
  ldr x6, [sp, #288]
  ldr x5, [sp, #336]
  ldr x4, [sp, #368]
.L150:
  mov x0, x9
  str x0, [sp, #376]
.L151:
  mov x0, x19
  str x0, [sp, #384]
.L152:
  mov x0, x15
  str x0, [sp, #392]
.L153:
  mov x0, x14
  str x0, [sp, #400]
.L154:
  mov x0, x11
  str x0, [sp, #408]
.L155:
  mov x0, x10
  str x0, [sp, #416]
.L156:
  str d15, [sp, #424]
.L157:
  str d14, [sp, #432]
.L158:
  mov x0, x13
  str x0, [sp, #440]
.L159:
  mov x0, x12
  str x0, [sp, #448]
.L160:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print rep
  ldr x9, [sp, #376]
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
  ldr x9, [sp, #384]
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
  ldr x9, [sp, #392]
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
  ldr x9, [sp, #400]
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
  ldr x9, [sp, #408]
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
  ldr x9, [sp, #416]
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
  ldr d0, [sp, #424]
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
  ldr d0, [sp, #432]
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
  ldr x9, [sp, #440]
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
  ldr x9, [sp, #448]
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
  // Restore callee-saved registers
  ldr x19, [sp, #456]
  ldr x20, [sp, #464]
  ldr d15, [sp, #472]
  ldr d14, [sp, #480]
  ldr d13, [sp, #488]
  ldr d12, [sp, #496]
  ldr d11, [sp, #504]
  ldr d10, [sp, #512]
  ldr d9, [sp, #520]
  ldr d8, [sp, #528]
  ldr x29, [sp, #544]
  ldr x30, [sp, #552]
  add sp, sp, #560
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

.Lfmt_print_149:
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
