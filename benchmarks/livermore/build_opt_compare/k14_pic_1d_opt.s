.global _main
.align 2

_main:
  sub sp, sp, #416
  str x30, [sp, #408]
  str x29, [sp, #400]
  add x29, sp, #400
  // Save callee-saved registers
  str x23, [sp, #304]
  str x22, [sp, #312]
  str x21, [sp, #320]
  str x24, [sp, #328]
  str x20, [sp, #336]
  str x19, [sp, #344]
  str d8, [sp, #352]
  str d11, [sp, #360]
  str d10, [sp, #368]
  str d9, [sp, #376]
  str d12, [sp, #384]
  str d13, [sp, #392]

  // Initialize all variables to 0
  mov x0, #0

  mov x23, #0
  mov x22, #0
  mov x21, #0
  fmov d8, x0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  fmov d12, x0
  fmov d7, x0
  mov x24, #0
  mov x20, #0
  mov x19, #0
  mov x15, #0
  mov x14, #0
  mov x13, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x8, #0
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
  mov x23, x0
.L1:
  mov x0, #0
  mov x22, x0
.L2:
  mov x0, #0
  mov x21, x0
.L3:
  mov x0, #0
  fmov d8, x0
.L4:
  mov x0, #0
  fmov d11, x0
.L5:
  mov x0, #0
  fmov d10, x0
.L6:
  mov x0, #0
  fmov d9, x0
.L7:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L8:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L9:
  fadd d10, d3, d11
.L10:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L11:
  fmul d9, d3, d11
.L12:
  mov x0, #1
  mov x23, x0
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
  cmp x23, x4
  b.gt .L27
.L19:
  fsub d3, d6, d11
.L20:
  fmadd d10, d3, d10, d11
.L21:
  fsub d11, d5, d11
.L22:
  fsub d3, d10, d9
.L23:
  fmul d3, d3, d4
.L24:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L25:
  add x23, x23, x3
.L26:
  b .L18
.L27:
  mov x0, #27
  mov x3, x0
.L28:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L29:
  fmov d8, d3
.L30:
  mov x0, #1
  mov x22, x0
.L31:
  mov x0, #1001
  mov x7, x0
.L32:
  mov x0, #1
  mov x6, x0
.L33:
  mov x0, #512
  mov x5, x0
.L34:
  movz x0, #0
  movk x0, #16376, lsl #48
  fmov d4, x0
.L35:
  mov x0, #1
  mov x4, x0
.L36:
  cmp x22, x7
  b.gt .L44
.L37:
  sub x3, x22, x6
.L38:
  cbz x5, .Ldiv_by_zero
  sdiv x0, x3, x5
  mul x0, x0, x5
  sub x3, x3, x0
.L39:
  mov x0, x3
  scvtf d3, x0
.L40:
  fadd d3, d3, d4
.L41:
  adrp x0, _arr_grd@PAGE
  add x0, x0, _arr_grd@PAGEOFF
  str d3, [x0, x22, lsl #3]
.L42:
  add x22, x22, x4
.L43:
  b .L36
.L44:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L45:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L46:
  fadd d10, d3, d11
.L47:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L48:
  fmul d9, d3, d11
.L49:
  mov x0, #1
  mov x23, x0
.L50:
  mov x0, #1001
  mov x4, x0
.L51:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L52:
  mov x0, #0
  fmov d5, x0
.L53:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L54:
  mov x0, #1
  mov x3, x0
.L55:
  cmp x23, x4
  b.gt .L64
.L56:
  fsub d3, d6, d11
.L57:
  fmadd d10, d3, d10, d11
.L58:
  fsub d11, d5, d11
.L59:
  fsub d3, d10, d9
.L60:
  fmul d3, d3, d4
.L61:
  adrp x0, _arr_ex@PAGE
  add x0, x0, _arr_ex@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L62:
  add x23, x23, x3
.L63:
  b .L55
.L64:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L65:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L66:
  fadd d10, d3, d11
.L67:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L68:
  fmul d9, d3, d11
.L69:
  mov x0, #1
  mov x23, x0
.L70:
  mov x0, #1001
  mov x4, x0
.L71:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L72:
  mov x0, #0
  fmov d5, x0
.L73:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L74:
  mov x0, #1
  mov x3, x0
.L75:
  cmp x23, x4
  b.gt .L84
.L76:
  fsub d3, d6, d11
.L77:
  fmadd d10, d3, d10, d11
.L78:
  fsub d11, d5, d11
.L79:
  fsub d3, d10, d9
.L80:
  fmul d3, d3, d4
.L81:
  adrp x0, _arr_dex@PAGE
  add x0, x0, _arr_dex@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L82:
  add x23, x23, x3
.L83:
  b .L75
.L84:
  mov x0, #1
  mov x22, x0
.L85:
  mov x0, #1001
  mov x6, x0
.L86:
  mov x0, #0
  fmov d12, x0
.L87:
  mov x0, #0
  fmov d7, x0
.L88:
  mov x0, #0
  fmov d6, x0
.L89:
  mov x0, #0
  fmov d5, x0
.L90:
  mov x0, #0
  fmov d4, x0
.L91:
  mov x0, #0
  fmov d3, x0
.L92:
  mov x0, #0
  mov x5, x0
.L93:
  mov x0, #0
  mov x4, x0
.L94:
  mov x0, #1
  mov x3, x0
.L95:
  cmp x22, x6
  b.gt .L106
.L96:
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  str d12, [x0, x22, lsl #3]
.L97:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d7, [x0, x22, lsl #3]
.L98:
  adrp x0, _arr_xi@PAGE
  add x0, x0, _arr_xi@PAGEOFF
  str d6, [x0, x22, lsl #3]
.L99:
  adrp x0, _arr_ex1@PAGE
  add x0, x0, _arr_ex1@PAGEOFF
  str d5, [x0, x22, lsl #3]
.L100:
  adrp x0, _arr_dex1@PAGE
  add x0, x0, _arr_dex1@PAGEOFF
  str d4, [x0, x22, lsl #3]
.L101:
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  str d3, [x0, x22, lsl #3]
.L102:
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  str x5, [x0, x22, lsl #3]
.L103:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  str x4, [x0, x22, lsl #3]
.L104:
  add x22, x22, x3
.L105:
  b .L95
.L106:
  mov x0, #1
  mov x22, x0
.L107:
  mov x0, #2049
  mov x4, x0
.L108:
  mov x0, #0
  fmov d3, x0
.L109:
  mov x0, #1
  mov x3, x0
.L110:
  cmp x22, x4
  b.gt .L114
.L111:
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d3, [x0, x22, lsl #3]
.L112:
  add x22, x22, x3
.L113:
  b .L110
.L114:
  mov x0, #1
  mov x21, x0
.L115:
  movz x0, #31992
  movk x0, #28, lsl #16
  mov x24, x0
.L116:
  mov x0, #2049
  mov x20, x0
.L117:
  mov x0, #0
  fmov d12, x0
.L118:
  mov x0, #1
  mov x19, x0
.L119:
  mov x0, #1001
  mov x15, x0
.L120:
  mov x0, #0
  fmov d7, x0
.L121:
  mov x0, #0
  fmov d6, x0
.L122:
  mov x0, #1
  mov x14, x0
.L123:
  mov x0, #1001
  mov x13, x0
.L124:
  mov x0, #2047
  mov x12, x0
.L125:
  mov x0, #1
  mov x11, x0
.L126:
  mov x0, #1
  mov x10, x0
.L127:
  mov x0, #1001
  mov x9, x0
.L128:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d5, x0
.L129:
  mov x0, #1
  mov x8, x0
.L130:
  mov x0, #1
  mov x7, x0
.L131:
  mov x0, #1
  mov x6, x0
.L132:
  mov x0, #1
  mov x5, x0
.L133:
  cmp x21, x24
  b.gt .L213
.L134:
  mov x0, #1
  mov x22, x0
.L135:
  cmp x22, x20
  b.gt .L139
.L136:
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d12, [x0, x22, lsl #3]
.L137:
  add x22, x22, x19
.L138:
  b .L135
.L139:
  mov x0, #1
  mov x23, x0
.L140:
  cmp x23, x15
  b.gt .L157
.L141:
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  str d7, [x0, x23, lsl #3]
.L142:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d6, [x0, x23, lsl #3]
.L143:
  adrp x0, _arr_grd@PAGE
  add x0, x0, _arr_grd@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L144:
  fcvtzs x0, d3
  mov x3, x0
.L145:
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  str x3, [x0, x23, lsl #3]
.L146:
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L147:
  mov x0, x3
  scvtf d3, x0
.L148:
  adrp x0, _arr_xi@PAGE
  add x0, x0, _arr_xi@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L149:
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L150:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_ex@PAGE
  add x0, x0, _arr_ex@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L151:
  adrp x0, _arr_ex1@PAGE
  add x0, x0, _arr_ex1@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L152:
  adrp x0, _arr_ix@PAGE
  add x0, x0, _arr_ix@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L153:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_dex@PAGE
  add x0, x0, _arr_dex@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L154:
  adrp x0, _arr_dex1@PAGE
  add x0, x0, _arr_dex1@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L155:
  add x23, x23, x14
.L156:
  b .L140
.L157:
  mov x0, #1
  mov x23, x0
.L158:
  cmp x23, x13
  b.gt .L192
.L159:
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  ldr d4, [x0, x23, lsl #3]
.L160:
  adrp x0, _arr_ex1@PAGE
  add x0, x0, _arr_ex1@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L161:
  fadd d13, d4, d3
.L162:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d4, [x0, x23, lsl #3]
.L163:
  adrp x0, _arr_xi@PAGE
  add x0, x0, _arr_xi@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L164:
  fsub d4, d4, d3
.L165:
  adrp x0, _arr_dex1@PAGE
  add x0, x0, _arr_dex1@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L166:
  fmadd d3, d4, d3, d13
.L167:
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L168:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d4, [x0, x23, lsl #3]
.L169:
  adrp x0, _arr_vx@PAGE
  add x0, x0, _arr_vx@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L170:
  fadd d3, d4, d3
.L171:
  fadd d3, d3, d8
.L172:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L173:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L174:
  fcvtzs x0, d3
  mov x3, x0
.L175:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  str x3, [x0, x23, lsl #3]
.L176:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d4, [x0, x23, lsl #3]
.L177:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L178:
  mov x0, x3
  scvtf d3, x0
.L179:
  fsub d3, d4, d3
.L180:
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L181:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L182:
  and x3, x3, x12
.L183:
  add x3, x3, x11
.L184:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  str x3, [x0, x23, lsl #3]
.L185:
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  ldr d4, [x0, x23, lsl #3]
.L186:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L187:
  mov x0, x3
  scvtf d3, x0
.L188:
  fadd d3, d4, d3
.L189:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  str d3, [x0, x23, lsl #3]
.L190:
  add x23, x23, x10
.L191:
  b .L158
.L192:
  mov x0, #1
  mov x23, x0
.L193:
  cmp x23, x9
  b.gt .L211
.L194:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x4, [x0, x23, lsl #3]
.L195:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L196:
  cmp x3, #2050
  b.hs .Lbounds_err
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L197:
  fadd d4, d3, d5
.L198:
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L199:
  fsub d3, d4, d3
.L200:
  cmp x4, #2050
  b.hs .Lbounds_err
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d3, [x0, x4, lsl #3]
.L201:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L202:
  add x4, x3, x8
.L203:
  adrp x0, _arr_ir@PAGE
  add x0, x0, _arr_ir@PAGEOFF
  ldr x3, [x0, x23, lsl #3]
.L204:
  add x3, x3, x7
.L205:
  cmp x3, #2050
  b.hs .Lbounds_err
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L206:
  adrp x0, _arr_rx@PAGE
  add x0, x0, _arr_rx@PAGEOFF
  ldr d3, [x0, x23, lsl #3]
.L207:
  fadd d3, d4, d3
.L208:
  cmp x4, #2050
  b.hs .Lbounds_err
  adrp x0, _arr_rh@PAGE
  add x0, x0, _arr_rh@PAGEOFF
  str d3, [x0, x4, lsl #3]
.L209:
  add x23, x23, x6
.L210:
  b .L193
.L211:
  add x21, x21, x5
.L212:
  b .L133
.L213:
  mov x0, #1
  mov x3, x0
.L214:
  adrp x0, _arr_xx@PAGE
  add x0, x0, _arr_xx@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L215:
  str d3, [sp, #64]
  str x4, [sp, #72]
  str d6, [sp, #80]
  str d5, [sp, #88]
  str d4, [sp, #96]
  str x3, [sp, #104]
  str x7, [sp, #112]
  str x6, [sp, #120]
  str x5, [sp, #128]
  str d7, [sp, #144]
  str x15, [sp, #176]
  str x14, [sp, #184]
  str x13, [sp, #192]
  str x12, [sp, #200]
  str x11, [sp, #208]
  str x10, [sp, #216]
  str x9, [sp, #224]
  str x8, [sp, #232]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_215@PAGE
  add x0, x0, .Lfmt_print_215@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d3, [sp, #64]
  ldr x4, [sp, #72]
  ldr d6, [sp, #80]
  ldr d5, [sp, #88]
  ldr d4, [sp, #96]
  ldr x3, [sp, #104]
  ldr x7, [sp, #112]
  ldr x6, [sp, #120]
  ldr x5, [sp, #128]
  ldr d7, [sp, #144]
  ldr x15, [sp, #176]
  ldr x14, [sp, #184]
  ldr x13, [sp, #192]
  ldr x12, [sp, #200]
  ldr x11, [sp, #208]
  ldr x10, [sp, #216]
  ldr x9, [sp, #224]
  ldr x8, [sp, #232]
.L216:
  mov x0, x23
  str x0, [sp, #248]
.L217:
  mov x0, x22
  str x0, [sp, #256]
.L218:
  mov x0, x21
  str x0, [sp, #264]
.L219:
  str d8, [sp, #272]
.L220:
  str d11, [sp, #280]
.L221:
  str d10, [sp, #288]
.L222:
  str d9, [sp, #296]
.L223:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #248]
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
  ldr x9, [sp, #256]
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
  ldr x9, [sp, #264]
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
  ldr d0, [sp, #272]
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
  ldr d0, [sp, #280]
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
  ldr d0, [sp, #288]
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
  ldr d0, [sp, #296]
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
  // Restore callee-saved registers
  ldr x23, [sp, #304]
  ldr x22, [sp, #312]
  ldr x21, [sp, #320]
  ldr x24, [sp, #328]
  ldr x20, [sp, #336]
  ldr x19, [sp, #344]
  ldr d8, [sp, #352]
  ldr d11, [sp, #360]
  ldr d10, [sp, #368]
  ldr d9, [sp, #376]
  ldr d12, [sp, #384]
  ldr d13, [sp, #392]
  ldr x29, [sp, #400]
  ldr x30, [sp, #408]
  add sp, sp, #416
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

.Lfmt_print_215:
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
