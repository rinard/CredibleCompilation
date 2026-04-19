.global _main
.align 2

_main:
  sub sp, sp, #432
  str x30, [sp, #424]
  str x29, [sp, #416]
  add x29, sp, #416
  // Save callee-saved registers
  stp x25, x24, [sp, #304]
  stp x23, x22, [sp, #320]
  stp x21, x20, [sp, #336]
  str x19, [sp, #352]
  stp d9, d12, [sp, #368]
  stp d11, d10, [sp, #384]
  stp d8, d13, [sp, #400]

  // Initialize all variables to 0
  mov x0, #0

  mov x25, #0
  mov x24, #0
  mov x23, #0
  fmov d9, x0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  fmov d8, x0
  fmov d7, x0
  mov x22, #0
  mov x21, #0
  mov x20, #0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  fmov d13, x0
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]
  str x0, [sp, #272]
  str x0, [sp, #280]
  str x0, [sp, #288]
  str x0, [sp, #296]

.L0:
  mov x0, #0
  mov x25, x0
.L1:
  mov x0, #0
  mov x24, x0
.L2:
  mov x0, #0
  mov x23, x0
.L3:
  mov x0, #0
  fmov d9, x0
.L4:
  mov x0, #0
  fmov d12, x0
.L5:
  mov x0, #0
  fmov d11, x0
.L6:
  mov x0, #0
  fmov d10, x0
.L7:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L8:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L9:
  fadd d11, d3, d12
.L10:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L11:
  fmul d10, d3, d12
.L12:
  mov x0, #1
  mov x25, x0
.L13:
  mov x0, #39
  mov x4, x0
.L14:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L15:
  mov x0, #0
  fmov d5, x0
.L16:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L17:
  mov x0, #1
  mov x3, x0
.L18:
  mov x1, x25
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L28
.L19:
  fsub d3, d6, d12
.L20:
  fmul d3, d3, d11
.L21:
  fadd d11, d3, d12
.L22:
  fsub d12, d5, d12
.L23:
  fsub d3, d11, d10
.L24:
  fmul d3, d3, d4
.L25:
  mov x1, x25
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L26:
  add x25, x25, x3
.L27:
  b .L18
.L28:
  mov x0, #27
  mov x3, x0
.L29:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L30:
  fmov d9, d3
.L31:
  mov x0, #1
  mov x24, x0
.L32:
  mov x0, #1001
  mov x7, x0
.L33:
  mov x0, #1
  mov x6, x0
.L34:
  mov x0, #512
  mov x5, x0
.L35:
  movz x0, #0
  movk x0, #16376, lsl #48
  fmov d4, x0
.L36:
  mov x0, #1
  mov x4, x0
.L37:
  mov x1, x24
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L45
.L38:
  sub x3, x24, x6
.L39:
  cbz x5, .Ldiv_by_zero
  sdiv x0, x3, x5
  mul x0, x0, x5
  sub x3, x3, x0
.L40:
  mov x0, x3
  scvtf d3, x0
.L41:
  fadd d3, d3, d4
.L42:
  mov x1, x24
  adrp x8, _arr_grd@PAGE
  add x8, x8, _arr_grd@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L43:
  add x24, x24, x4
.L44:
  b .L37
.L45:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L46:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L47:
  fadd d11, d3, d12
.L48:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L49:
  fmul d10, d3, d12
.L50:
  mov x0, #1
  mov x25, x0
.L51:
  mov x0, #1001
  mov x4, x0
.L52:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L53:
  mov x0, #0
  fmov d5, x0
.L54:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L55:
  mov x0, #1
  mov x3, x0
.L56:
  mov x1, x25
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L66
.L57:
  fsub d3, d6, d12
.L58:
  fmul d3, d3, d11
.L59:
  fadd d11, d3, d12
.L60:
  fsub d12, d5, d12
.L61:
  fsub d3, d11, d10
.L62:
  fmul d3, d3, d4
.L63:
  mov x1, x25
  adrp x8, _arr_ex@PAGE
  add x8, x8, _arr_ex@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L64:
  add x25, x25, x3
.L65:
  b .L56
.L66:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L67:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L68:
  fadd d11, d3, d12
.L69:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L70:
  fmul d10, d3, d12
.L71:
  mov x0, #1
  mov x25, x0
.L72:
  mov x0, #1001
  mov x4, x0
.L73:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L74:
  mov x0, #0
  fmov d5, x0
.L75:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L76:
  mov x0, #1
  mov x3, x0
.L77:
  mov x1, x25
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L87
.L78:
  fsub d3, d6, d12
.L79:
  fmul d3, d3, d11
.L80:
  fadd d11, d3, d12
.L81:
  fsub d12, d5, d12
.L82:
  fsub d3, d11, d10
.L83:
  fmul d3, d3, d4
.L84:
  mov x1, x25
  adrp x8, _arr_dex@PAGE
  add x8, x8, _arr_dex@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L85:
  add x25, x25, x3
.L86:
  b .L77
.L87:
  mov x0, #1
  mov x24, x0
.L88:
  mov x0, #1001
  mov x6, x0
.L89:
  mov x0, #0
  fmov d8, x0
.L90:
  mov x0, #0
  fmov d7, x0
.L91:
  mov x0, #0
  fmov d6, x0
.L92:
  mov x0, #0
  fmov d5, x0
.L93:
  mov x0, #0
  fmov d4, x0
.L94:
  mov x0, #0
  fmov d3, x0
.L95:
  mov x0, #0
  mov x5, x0
.L96:
  mov x0, #0
  mov x4, x0
.L97:
  mov x0, #1
  mov x3, x0
.L98:
  mov x1, x24
  mov x2, x6
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L109
.L99:
  mov x1, x24
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  str d8, [x8, x1, lsl #3]
.L100:
  mov x1, x24
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d7, [x8, x1, lsl #3]
.L101:
  mov x1, x24
  adrp x8, _arr_xi@PAGE
  add x8, x8, _arr_xi@PAGEOFF
  str d6, [x8, x1, lsl #3]
.L102:
  mov x1, x24
  adrp x8, _arr_ex1@PAGE
  add x8, x8, _arr_ex1@PAGEOFF
  str d5, [x8, x1, lsl #3]
.L103:
  mov x1, x24
  adrp x8, _arr_dex1@PAGE
  add x8, x8, _arr_dex1@PAGEOFF
  str d4, [x8, x1, lsl #3]
.L104:
  mov x1, x24
  adrp x8, _arr_rx@PAGE
  add x8, x8, _arr_rx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L105:
  mov x1, x24
  mov x2, x5
  adrp x8, _arr_ix@PAGE
  add x8, x8, _arr_ix@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L106:
  mov x1, x24
  mov x2, x4
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L107:
  add x24, x24, x3
.L108:
  b .L98
.L109:
  mov x0, #1
  mov x24, x0
.L110:
  mov x0, #2049
  mov x4, x0
.L111:
  mov x0, #0
  fmov d3, x0
.L112:
  mov x0, #1
  mov x3, x0
.L113:
  mov x1, x24
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L117
.L114:
  mov x1, x24
  adrp x8, _arr_rh@PAGE
  add x8, x8, _arr_rh@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L115:
  add x24, x24, x3
.L116:
  b .L113
.L117:
  mov x0, #1
  mov x23, x0
.L118:
  movz x0, #31992
  movk x0, #28, lsl #16
  mov x22, x0
.L119:
  mov x0, #2049
  mov x21, x0
.L120:
  mov x0, #0
  fmov d8, x0
.L121:
  mov x0, #1
  mov x20, x0
.L122:
  mov x0, #1001
  mov x19, x0
.L123:
  mov x0, #0
  fmov d7, x0
.L124:
  mov x0, #0
  fmov d6, x0
.L125:
  mov x0, #1
  mov x15, x0
.L126:
  mov x0, #1001
  mov x14, x0
.L127:
  mov x0, #2047
  mov x13, x0
.L128:
  mov x0, #1
  mov x12, x0
.L129:
  mov x0, #1
  mov x11, x0
.L130:
  mov x0, #1001
  mov x10, x0
.L131:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d5, x0
.L132:
  mov x0, #1
  mov x9, x0
.L133:
  mov x0, #1
  mov x7, x0
.L134:
  mov x0, #1
  mov x6, x0
.L135:
  mov x0, #1
  mov x5, x0
.L136:
  mov x1, x23
  mov x2, x22
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L217
.L137:
  mov x0, #1
  mov x24, x0
.L138:
  mov x1, x24
  mov x2, x21
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L142
.L139:
  mov x1, x24
  adrp x8, _arr_rh@PAGE
  add x8, x8, _arr_rh@PAGEOFF
  str d8, [x8, x1, lsl #3]
.L140:
  add x24, x24, x20
.L141:
  b .L138
.L142:
  mov x0, #1
  mov x25, x0
.L143:
  mov x1, x25
  mov x2, x19
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L160
.L144:
  mov x1, x25
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  str d7, [x8, x1, lsl #3]
.L145:
  mov x1, x25
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d6, [x8, x1, lsl #3]
.L146:
  mov x1, x25
  adrp x8, _arr_grd@PAGE
  add x8, x8, _arr_grd@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L147:
  fcvtzs x0, d3
  mov x3, x0
.L148:
  mov x1, x25
  mov x2, x3
  adrp x8, _arr_ix@PAGE
  add x8, x8, _arr_ix@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L149:
  mov x1, x25
  adrp x8, _arr_ix@PAGE
  add x8, x8, _arr_ix@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L150:
  mov x0, x3
  scvtf d3, x0
.L151:
  mov x1, x25
  adrp x8, _arr_xi@PAGE
  add x8, x8, _arr_xi@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L152:
  mov x1, x25
  adrp x8, _arr_ix@PAGE
  add x8, x8, _arr_ix@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L153:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_ex@PAGE
  add x8, x8, _arr_ex@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L154:
  mov x1, x25
  adrp x8, _arr_ex1@PAGE
  add x8, x8, _arr_ex1@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L155:
  mov x1, x25
  adrp x8, _arr_ix@PAGE
  add x8, x8, _arr_ix@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L156:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_dex@PAGE
  add x8, x8, _arr_dex@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L157:
  mov x1, x25
  adrp x8, _arr_dex1@PAGE
  add x8, x8, _arr_dex1@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L158:
  add x25, x25, x15
.L159:
  b .L143
.L160:
  mov x0, #1
  mov x25, x0
.L161:
  mov x1, x25
  mov x2, x14
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L196
.L162:
  mov x1, x25
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L163:
  mov x1, x25
  adrp x8, _arr_ex1@PAGE
  add x8, x8, _arr_ex1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L164:
  fadd d13, d4, d3
.L165:
  mov x1, x25
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L166:
  mov x1, x25
  adrp x8, _arr_xi@PAGE
  add x8, x8, _arr_xi@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L167:
  fsub d4, d4, d3
.L168:
  mov x1, x25
  adrp x8, _arr_dex1@PAGE
  add x8, x8, _arr_dex1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L169:
  fmul d3, d4, d3
.L170:
  fadd d3, d13, d3
.L171:
  mov x1, x25
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L172:
  mov x1, x25
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L173:
  mov x1, x25
  adrp x8, _arr_vx@PAGE
  add x8, x8, _arr_vx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L174:
  fadd d3, d4, d3
.L175:
  fadd d3, d3, d9
.L176:
  mov x1, x25
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L177:
  mov x1, x25
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L178:
  fcvtzs x0, d3
  mov x3, x0
.L179:
  mov x1, x25
  mov x2, x3
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L180:
  mov x1, x25
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L181:
  mov x1, x25
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L182:
  mov x0, x3
  scvtf d3, x0
.L183:
  fsub d3, d4, d3
.L184:
  mov x1, x25
  adrp x8, _arr_rx@PAGE
  add x8, x8, _arr_rx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L185:
  mov x1, x25
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L186:
  and x3, x3, x13
.L187:
  add x3, x3, x12
.L188:
  mov x1, x25
  mov x2, x3
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L189:
  mov x1, x25
  adrp x8, _arr_rx@PAGE
  add x8, x8, _arr_rx@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L190:
  mov x1, x25
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L191:
  mov x0, x3
  scvtf d3, x0
.L192:
  fadd d3, d4, d3
.L193:
  mov x1, x25
  adrp x8, _arr_xx@PAGE
  add x8, x8, _arr_xx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L194:
  add x25, x25, x11
.L195:
  b .L161
.L196:
  mov x0, #1
  mov x25, x0
.L197:
  mov x1, x25
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L215
.L198:
  mov x1, x25
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x4, x0
.L199:
  mov x1, x25
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L200:
  mov x1, x3
  cmp x1, #2050
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_rh@PAGE
  add x8, x8, _arr_rh@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L201:
  fadd d4, d3, d5
.L202:
  mov x1, x25
  adrp x8, _arr_rx@PAGE
  add x8, x8, _arr_rx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L203:
  fsub d3, d4, d3
.L204:
  mov x1, x4
  cmp x1, #2050
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_rh@PAGE
  add x8, x8, _arr_rh@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L205:
  mov x1, x25
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L206:
  add x4, x3, x9
.L207:
  mov x1, x25
  adrp x8, _arr_ir@PAGE
  add x8, x8, _arr_ir@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L208:
  add x3, x3, x7
.L209:
  mov x1, x3
  cmp x1, #2050
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_rh@PAGE
  add x8, x8, _arr_rh@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L210:
  mov x1, x25
  adrp x8, _arr_rx@PAGE
  add x8, x8, _arr_rx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L211:
  fadd d3, d4, d3
.L212:
  mov x1, x4
  cmp x1, #2050
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_rh@PAGE
  add x8, x8, _arr_rh@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L213:
  add x25, x25, x6
.L214:
  b .L197
.L215:
  add x23, x23, x5
.L216:
  b .L136
.L217:
  mov x0, x25
  str x0, [sp, #248]
.L218:
  mov x0, x24
  str x0, [sp, #256]
.L219:
  mov x0, x23
  str x0, [sp, #264]
.L220:
  str d9, [sp, #272]
.L221:
  str d12, [sp, #280]
.L222:
  str d11, [sp, #288]
.L223:
  str d10, [sp, #296]
.L224:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #248]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i
  ldr x9, [sp, #256]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #264]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print flx (float)
  ldr d0, [sp, #272]
  sub sp, sp, #32
  adrp x8, .Lname_flx@PAGE
  add x8, x8, .Lname_flx@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #280]
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
  ldr d0, [sp, #288]
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
  ldr d0, [sp, #296]
  sub sp, sp, #32
  adrp x8, .Lname_fizz@PAGE
  add x8, x8, .Lname_fizz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32

  // Exit with code 0
  mov x0, #0
  // Restore callee-saved registers
  ldp x25, x24, [sp, #304]
  ldp x23, x22, [sp, #320]
  ldp x21, x20, [sp, #336]
  ldr x19, [sp, #352]
  ldp d9, d12, [sp, #368]
  ldp d11, d10, [sp, #384]
  ldp d8, d13, [sp, #400]
  ldr x29, [sp, #416]
  ldr x30, [sp, #424]
  add sp, sp, #432
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
