.global _main
.align 2

_main:
  sub sp, sp, #608
  str x30, [sp, #600]
  str x29, [sp, #592]
  add x29, sp, #592
  // Save callee-saved registers
  stp x22, x28, [sp, #448]
  stp x27, x24, [sp, #464]
  stp x23, x26, [sp, #480]
  stp x25, x21, [sp, #496]
  str x20, [sp, #512]
  str x19, [sp, #520]
  str d15, [sp, #528]
  str d14, [sp, #536]
  str d13, [sp, #544]
  str d12, [sp, #552]
  str d11, [sp, #560]
  str d10, [sp, #568]
  str d9, [sp, #576]
  str d8, [sp, #584]

  // Initialize all variables to 0
  mov x0, #0

  mov x22, #0
  str x0, [sp, #16]
  mov x28, #0
  mov x27, #0
  mov x24, #0
  mov x23, #0
  str x0, [sp, #56]
  str x0, [sp, #64]
  str x0, [sp, #72]
  str x0, [sp, #80]
  str x0, [sp, #88]
  fmov d15, x0
  str x0, [sp, #104]
  str x0, [sp, #112]
  fmov d14, x0
  mov x26, #0
  mov x25, #0
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
  mov x21, #0
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]
  mov x20, #0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
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

.L0:
  mov x0, #0
  mov x22, x0
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #0
  mov x28, x0
.L3:
  mov x0, #0
  mov x27, x0
.L4:
  mov x0, #0
  mov x24, x0
.L5:
  mov x0, #0
  mov x23, x0
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
  mov x26, x0
.L16:
  mov x0, #0
  mov x25, x0
.L17:
  mov x0, #101
  mov x24, x0
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
  mov x23, x0
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
  mov x1, x23
  mov x2, x24
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L62
.L35:
  ldr d2, [sp, #104]
  fsub d3, d13, d2
.L36:
  ldr d2, [sp, #112]
  fmul d3, d3, d2
.L37:
  ldr d2, [sp, #104]
  fadd d0, d3, d2
  str d0, [sp, #112]
.L38:
  ldr d2, [sp, #104]
  fsub d0, d12, d2
  str d0, [sp, #104]
.L39:
  ldr d1, [sp, #112]
  fsub d4, d1, d14
.L40:
  fmul d3, d4, d11
.L41:
  mov x1, x23
  adrp x8, _arr_vsp@PAGE
  add x8, x8, _arr_vsp@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L42:
.L43:
  fmul d3, d4, d10
.L44:
  mov x1, x23
  adrp x8, _arr_vstp@PAGE
  add x8, x8, _arr_vstp@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L45:
.L46:
  fmul d3, d4, d9
.L47:
  mov x1, x23
  adrp x8, _arr_vxne@PAGE
  add x8, x8, _arr_vxne@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L48:
.L49:
  fmul d3, d4, d8
.L50:
  mov x1, x23
  adrp x8, _arr_vxnd@PAGE
  add x8, x8, _arr_vxnd@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L51:
.L52:
  fmul d3, d4, d7
.L53:
  mov x1, x23
  adrp x8, _arr_ve3@PAGE
  add x8, x8, _arr_ve3@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L54:
.L55:
  fmul d3, d4, d6
.L56:
  mov x1, x23
  adrp x8, _arr_vlr@PAGE
  add x8, x8, _arr_vlr@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L57:
  fmov d3, d4
.L58:
  fmul d3, d3, d5
.L59:
  mov x1, x23
  adrp x8, _arr_vlin@PAGE
  add x8, x8, _arr_vlin@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L60:
  add x23, x23, x3
.L61:
  b .L34
.L62:
  mov x0, #1
  mov x22, x0
.L63:
  movz x0, #44864
  movk x0, #351, lsl #16
  mov x21, x0
.L64:
  mov x0, #1
  str x0, [sp, #248]
.L65:
  mov x0, #0
  str x0, [sp, #256]
.L66:
  mov x0, #1
  str x0, [sp, #264]
.L67:
  movz x0, #0
  movk x0, #16404, lsl #48
  fmov d8, x0
.L68:
  movz x0, #0
  movk x0, #16392, lsl #48
  fmov d7, x0
.L69:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L70:
  movz x0, #0
  movk x0, #16392, lsl #48
  fmov d5, x0
.L71:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16368, lsl #48
  fmov d4, x0
.L72:
  movz x0, #49807
  movk x0, #10485, lsl #16
  movk x0, #36700, lsl #32
  movk x0, #16392, lsl #48
  fmov d3, x0
.L73:
  mov x0, #0
  mov x20, x0
.L74:
  mov x0, #0
  mov x19, x0
.L75:
  mov x0, #1
  mov x15, x0
.L76:
  mov x0, #1
  mov x14, x0
.L77:
  mov x0, #1
  mov x13, x0
.L78:
  mov x0, #1
  mov x12, x0
.L79:
  mov x0, #1
  mov x11, x0
.L80:
  mov x0, #1
  mov x10, x0
.L81:
  mov x0, #1
  mov x9, x0
.L82:
  mov x0, #1
  mov x7, x0
.L83:
  mov x0, #1
  mov x6, x0
.L84:
  mov x0, #1
  mov x5, x0
.L85:
  mov x0, #1
  mov x4, x0
.L86:
  mov x1, x22
  mov x2, x21
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L148
.L87:
  mov x0, #100
  str x0, [sp, #16]
.L88:
  movz x0, #65535
  movk x0, #65535, lsl #16
  movk x0, #65535, lsl #32
  movk x0, #65535, lsl #48
  mov x27, x0
.L89:
  fdiv d0, d8, d7
  str d0, [sp, #56]
.L90:
  fdiv d0, d6, d5
  str d0, [sp, #64]
.L91:
  fdiv d0, d4, d3
  str d0, [sp, #72]
.L92:
  mov x0, #1
  mov x26, x0
.L93:
  mov x0, #0
  mov x25, x0
.L94:
  mov x1, x25
  mov x2, x20
  cmp x1, x2
  cset w0, eq
  eor w0, w0, #1
  cbnz w0, .L146
.L95:
  mov x1, x26
  mov x2, x19
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L129
.L96:
  ldr x1, [sp, #16]
  add x3, x1, x15
.L97:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vlr@PAGE
  add x8, x8, _arr_vlr@PAGEOFF
  ldr d9, [x8, x1, lsl #3]
.L98:
  ldr d1, [sp, #64]
  fmul d10, d1, d9
.L99:
  ldr x1, [sp, #16]
  add x3, x1, x14
.L100:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vlin@PAGE
  add x8, x8, _arr_vlin@PAGEOFF
  ldr d9, [x8, x1, lsl #3]
.L101:
  fadd d0, d10, d9
  str d0, [sp, #80]
.L102:
  ldr x1, [sp, #16]
  add x3, x1, x13
.L103:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vxne@PAGE
  add x8, x8, _arr_vxne@PAGEOFF
  ldr d9, [x8, x1, lsl #3]
.L104:
  str d9, [sp, #88]
.L105:
  ldr x1, [sp, #16]
  add x3, x1, x12
.L106:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  ldr d0, [sp, #72]
  adrp x8, _arr_vxnd@PAGE
  add x8, x8, _arr_vxnd@PAGEOFF
  str d0, [x8, x1, lsl #3]
.L107:
  ldr d1, [sp, #56]
  ldr d2, [sp, #80]
  fmul d15, d1, d2
.L108:
  fmov d1, d15
  ldr d2, [sp, #64]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L127
.L109:
  fmov d1, d15
  ldr d2, [sp, #88]
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L125
.L110:
  ldr x1, [sp, #16]
  add x3, x1, x11
.L111:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  ldr d0, [sp, #80]
  adrp x8, _arr_ve3@PAGE
  add x8, x8, _arr_ve3@PAGEOFF
  str d0, [x8, x1, lsl #3]
.L112:
  ldr d1, [sp, #80]
  ldr d2, [sp, #80]
  fadd d9, d1, d2
.L113:
  ldr d2, [sp, #64]
  fsub d0, d9, d2
  str d0, [sp, #72]
.L114:
  ldr x1, [sp, #16]
  add x3, x1, x10
.L115:
  ldr d1, [sp, #80]
  ldr d2, [sp, #80]
  fadd d9, d1, d2
.L116:
  ldr d2, [sp, #88]
  fsub d9, d9, d2
.L117:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vxne@PAGE
  add x8, x8, _arr_vxne@PAGEOFF
  str d9, [x8, x1, lsl #3]
.L118:
  ldr x0, [sp, #72]
  str x0, [sp, #64]
.L119:
  ldr x1, [sp, #16]
  add x0, x1, x27
  str x0, [sp, #16]
.L120:
  ldr x1, [sp, #16]
  mov x2, x28
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L123
.L121:
  mov x0, #1
  mov x26, x0
.L122:
  b .L124
.L123:
  mov x0, #1
  mov x25, x0
.L124:
  b .L126
.L125:
  mov x0, #0
  mov x26, x0
.L126:
  b .L128
.L127:
  mov x0, #0
  mov x26, x0
.L128:
  b .L145
.L129:
  ldr x1, [sp, #16]
  add x3, x1, x9
.L130:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vsp@PAGE
  add x8, x8, _arr_vsp@PAGEOFF
  ldr d9, [x8, x1, lsl #3]
.L131:
  ldr d1, [sp, #64]
  fmul d10, d1, d9
.L132:
  ldr x1, [sp, #16]
  add x3, x1, x7
.L133:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_vstp@PAGE
  add x8, x8, _arr_vstp@PAGEOFF
  ldr d9, [x8, x1, lsl #3]
.L134:
  fadd d0, d10, d9
  str d0, [sp, #72]
.L135:
  ldr x1, [sp, #16]
  add x3, x1, x6
.L136:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  ldr d0, [sp, #72]
  adrp x8, _arr_vxne@PAGE
  add x8, x8, _arr_vxne@PAGEOFF
  str d0, [x8, x1, lsl #3]
.L137:
  ldr x0, [sp, #72]
  str x0, [sp, #64]
.L138:
  ldr x1, [sp, #16]
  add x3, x1, x5
.L139:
  mov x1, x3
  cmp x1, #102
  cset w0, lt
  cbz x0, .Lbounds_err
  ldr d0, [sp, #72]
  adrp x8, _arr_ve3@PAGE
  add x8, x8, _arr_ve3@PAGEOFF
  str d0, [x8, x1, lsl #3]
.L140:
  ldr x1, [sp, #16]
  add x0, x1, x27
  str x0, [sp, #16]
.L141:
  ldr x1, [sp, #16]
  mov x2, x28
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L144
.L142:
  mov x0, #1
  mov x26, x0
.L143:
  b .L145
.L144:
  mov x0, #1
  mov x25, x0
.L145:
  b .L94
.L146:
  add x22, x22, x4
.L147:
  b .L86
.L148:
  mov x0, x22
  str x0, [sp, #376]
.L149:
  mov x0, x28
  str x0, [sp, #384]
.L150:
  mov x0, x27
  str x0, [sp, #392]
.L151:
  mov x0, x24
  str x0, [sp, #400]
.L152:
  mov x0, x23
  str x0, [sp, #408]
.L153:
  str d15, [sp, #416]
.L154:
  str d14, [sp, #424]
.L155:
  mov x0, x26
  str x0, [sp, #432]
.L156:
  mov x0, x25
  str x0, [sp, #440]
.L157:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print rep
  ldr x9, [sp, #376]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j
  ldr x9, [sp, #384]
  sub sp, sp, #16
  adrp x8, .Lname_j@PAGE
  add x8, x8, .Lname_j@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ink
  ldr x9, [sp, #392]
  sub sp, sp, #16
  adrp x8, .Lname_ink@PAGE
  add x8, x8, .Lname_ink@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print n
  ldr x9, [sp, #400]
  sub sp, sp, #16
  adrp x8, .Lname_n@PAGE
  add x8, x8, .Lname_n@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #408]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print scale (float)
  ldr d0, [sp, #56]
  sub sp, sp, #32
  adrp x8, .Lname_scale@PAGE
  add x8, x8, .Lname_scale@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print xnm (float)
  ldr d0, [sp, #64]
  sub sp, sp, #32
  adrp x8, .Lname_xnm@PAGE
  add x8, x8, .Lname_xnm@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print e6 (float)
  ldr d0, [sp, #72]
  sub sp, sp, #32
  adrp x8, .Lname_e6@PAGE
  add x8, x8, .Lname_e6@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print e3 (float)
  ldr d0, [sp, #80]
  sub sp, sp, #32
  adrp x8, .Lname_e3@PAGE
  add x8, x8, .Lname_e3@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print xnei (float)
  ldr d0, [sp, #88]
  sub sp, sp, #32
  adrp x8, .Lname_xnei@PAGE
  add x8, x8, .Lname_xnei@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print xnc (float)
  ldr d0, [sp, #416]
  sub sp, sp, #32
  adrp x8, .Lname_xnc@PAGE
  add x8, x8, .Lname_xnc@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #104]
  sub sp, sp, #32
  adrp x8, .Lname_fuzz@PAGE
  add x8, x8, .Lname_fuzz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print buzz (float)
  ldr d0, [sp, #112]
  sub sp, sp, #32
  adrp x8, .Lname_buzz@PAGE
  add x8, x8, .Lname_buzz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fizz (float)
  ldr d0, [sp, #424]
  sub sp, sp, #32
  adrp x8, .Lname_fizz@PAGE
  add x8, x8, .Lname_fizz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print phase
  ldr x9, [sp, #432]
  sub sp, sp, #16
  adrp x8, .Lname_phase@PAGE
  add x8, x8, .Lname_phase@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print done
  ldr x9, [sp, #440]
  sub sp, sp, #16
  adrp x8, .Lname_done@PAGE
  add x8, x8, .Lname_done@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  // Restore callee-saved registers
  ldp x22, x28, [sp, #448]
  ldp x27, x24, [sp, #464]
  ldp x23, x26, [sp, #480]
  ldp x25, x21, [sp, #496]
  ldr x20, [sp, #512]
  ldr x19, [sp, #520]
  ldr d15, [sp, #528]
  ldr d14, [sp, #536]
  ldr d13, [sp, #544]
  ldr d12, [sp, #552]
  ldr d11, [sp, #560]
  ldr d10, [sp, #568]
  ldr d9, [sp, #576]
  ldr d8, [sp, #584]
  ldr x29, [sp, #592]
  ldr x30, [sp, #600]
  add sp, sp, #608
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
