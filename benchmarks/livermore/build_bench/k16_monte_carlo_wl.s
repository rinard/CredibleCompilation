.global _main
.align 2

_main:
  sub sp, sp, #736
  str x30, [sp, #728]
  str x29, [sp, #720]
  add x29, sp, #720
  // Save callee-saved registers
  str x28, [sp, #568]
  str x27, [sp, #576]
  str x26, [sp, #584]
  str x25, [sp, #592]
  str x24, [sp, #600]
  str x23, [sp, #608]
  str x22, [sp, #616]
  str x21, [sp, #624]
  str x20, [sp, #632]
  str x19, [sp, #640]
  str d11, [sp, #648]
  str d10, [sp, #656]
  str d9, [sp, #664]
  str d12, [sp, #672]
  str d8, [sp, #680]
  str d14, [sp, #688]
  str d13, [sp, #696]
  str d15, [sp, #704]

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
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d12, x0
  fmov d8, x0
  fmov d7, x0
  fmov d6, x0
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  str x0, [sp, #200]
  fmov d3, x0
  mov x4, #0
  fmov d14, x0
  fmov d13, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  fmov d15, x0
  mov x7, #0
  mov x6, #0
  str x0, [sp, #288]
  mov x5, #0
  str x0, [sp, #304]
  str x0, [sp, #312]
  str x0, [sp, #320]
  str x0, [sp, #328]
  str x0, [sp, #336]
  str x0, [sp, #344]
  str x0, [sp, #352]
  str x0, [sp, #360]
  str x0, [sp, #368]
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  mov x23, #0
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
  str x0, [sp, #512]
  str x0, [sp, #520]
  str x0, [sp, #528]
  str x0, [sp, #536]
  str x0, [sp, #544]
  str x0, [sp, #552]
  str x0, [sp, #560]

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
  fmov d11, x0
.L15:
  mov x0, #0
  fmov d10, x0
.L16:
  mov x0, #0
  fmov d9, x0
.L17:
  mov x0, #0
  fmov d12, x0
.L18:
  mov x0, #0
  fmov d8, x0
.L19:
  mov x0, #0
  fmov d7, x0
.L20:
  mov x0, #0
  fmov d6, x0
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
  mov x0, #25
  str x0, [sp, #88]
.L27:
  mov x0, #50
  str x0, [sp, #96]
.L28:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d11, x0
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L30:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d9, x0
.L31:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d8, x0
.L32:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L33:
  fadd d7, d3, d8
.L34:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L35:
  fmul d6, d3, d8
.L36:
  mov x0, #1
  str x0, [sp, #16]
.L37:
  mov x0, #300
  mov x4, x0
.L38:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d14, x0
.L39:
  mov x0, #0
  fmov d13, x0
.L40:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d5, x0
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L42:
  mov x0, #1
  mov x3, x0
.L43:
  ldr x1, [sp, #16]
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L56
.L44:
  fsub d3, d14, d8
.L45:
  fmul d3, d3, d7
.L46:
  fadd d7, d3, d8
.L47:
  fsub d8, d13, d8
.L48:
  fsub d15, d7, d6
.L49:
  fmul d3, d15, d5
.L50:
  ldr x1, [sp, #16]
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L51:
  fmov d3, d15
.L52:
  fmul d3, d3, d4
.L53:
  ldr x1, [sp, #16]
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L54:
  ldr x1, [sp, #16]
  add x0, x1, x3
  str x0, [sp, #16]
.L55:
  b .L43
.L56:
  mov x0, #1
  str x0, [sp, #16]
.L57:
  mov x0, #300
  mov x7, x0
.L58:
  mov x0, #1
  mov x6, x0
.L59:
  mov x0, #1
  str x0, [sp, #288]
.L60:
  mov x0, #1
  mov x5, x0
.L61:
  ldr x1, [sp, #16]
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L68
.L62:
  ldr x1, [sp, #16]
  sub x4, x1, x6
.L63:
  mov x0, #76
  mov x3, x0
.L64:
  cbz x3, .Ldiv_by_zero
  sdiv x0, x4, x3
  mul x0, x0, x3
  sub x3, x4, x0
.L65:
  ldr x1, [sp, #16]
  mov x2, x3
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L66:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L67:
  b .L61
.L68:
  mov x0, #1
  mov x4, x0
.L69:
  mov x0, #5
  mov x3, x0
.L70:
  mov x1, x4
  mov x2, x3
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L71:
  mov x0, #1
  str x0, [sp, #8]
.L72:
  movz x0, #38640
  movk x0, #10, lsl #16
  str x0, [sp, #304]
.L73:
  mov x0, #1
  str x0, [sp, #312]
.L74:
  mov x0, #1
  str x0, [sp, #320]
.L75:
  mov x0, #1
  str x0, [sp, #328]
.L76:
  mov x0, #0
  str x0, [sp, #336]
.L77:
  mov x0, #1
  str x0, [sp, #344]
.L78:
  mov x0, #1
  str x0, [sp, #352]
.L79:
  mov x0, #1
  str x0, [sp, #360]
.L80:
  mov x0, #1
  str x0, [sp, #368]
.L81:
  mov x0, #2
  mov x28, x0
.L82:
  mov x0, #3
  mov x27, x0
.L83:
  mov x0, #3
  mov x26, x0
.L84:
  mov x0, #4
  mov x25, x0
.L85:
  mov x0, #4
  mov x24, x0
.L86:
  mov x0, #5
  mov x23, x0
.L87:
  mov x0, #5
  mov x22, x0
.L88:
  mov x0, #0
  mov x21, x0
.L89:
  mov x0, #0
  fmov d5, x0
.L90:
  mov x0, #0
  fmov d4, x0
.L91:
  mov x0, #2
  mov x20, x0
.L92:
  mov x0, #0
  mov x19, x0
.L93:
  mov x0, #0
  mov x15, x0
.L94:
  mov x0, #2
  mov x14, x0
.L95:
  mov x0, #0
  mov x13, x0
.L96:
  mov x0, #0
  mov x12, x0
.L97:
  mov x0, #0
  mov x11, x0
.L98:
  mov x0, #0
  mov x10, x0
.L99:
  mov x0, #1
  mov x9, x0
.L100:
  mov x0, #1
  mov x7, x0
.L101:
  mov x0, #1
  mov x6, x0
.L102:
  mov x0, #1
  mov x5, x0
.L103:
  ldr x1, [sp, #8]
  ldr x2, [sp, #304]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L225
.L104:
  mov x0, #1
  str x0, [sp, #32]
.L105:
  mov x0, #1
  str x0, [sp, #24]
.L106:
  mov x0, #0
  str x0, [sp, #48]
.L107:
  mov x0, #0
  str x0, [sp, #56]
.L108:
  mov x0, #0
  str x0, [sp, #176]
.L109:
  mov x0, #1
  str x0, [sp, #192]
.L110:
  ldr x1, [sp, #192]
  ldr x2, [sp, #312]
  cmp x1, x2
  cset w0, eq
  eor w0, w0, #1
  cbnz w0, .L223
.L111:
  mov x0, #0
  str x0, [sp, #192]
.L112:
  mov x0, #0
  str x0, [sp, #176]
.L113:
  mov x0, #150
  mov x4, x0
.L114:
  ldr x1, [sp, #24]
  ldr x2, [sp, #320]
  sub x3, x1, x2
.L115:
  mul x3, x4, x3
.L116:
  ldr x2, [sp, #328]
  add x0, x3, x2
  str x0, [sp, #64]
.L117:
  mov x0, #1
  str x0, [sp, #40]
.L118:
  ldr x1, [sp, #40]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L122
.L119:
  ldr x1, [sp, #176]
  ldr x2, [sp, #336]
  cmp x1, x2
  cset w0, eq
  eor w0, w0, #1
  cbnz w0, .L122
.L120:
  mov x0, #1
  mov x3, x0
.L121:
  b .L123
.L122:
  mov x0, #0
  mov x3, x0
.L123:
  mov x1, x3
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  eor w0, w0, #1
  cbnz w0, .L222
.L124:
  mov x0, #0
  str x0, [sp, #184]
.L125:
  ldr x1, [sp, #48]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #48]
.L126:
  ldr x1, [sp, #64]
  ldr x2, [sp, #40]
  add x3, x1, x2
.L127:
  ldr x2, [sp, #40]
  add x0, x3, x2
  str x0, [sp, #72]
.L128:
  ldr x1, [sp, #72]
  ldr x2, [sp, #352]
  sub x3, x1, x2
.L129:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L130:
  mov x0, x3
  str x0, [sp, #80]
.L131:
  ldr x1, [sp, #80]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L166
.L132:
  ldr x1, [sp, #80]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L164
.L133:
  ldr x1, [sp, #56]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #56]
.L134:
  ldr x1, [sp, #80]
  ldr x2, [sp, #368]
  sub x3, x1, x2
.L135:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d12, [x8, x1, lsl #3]
.L136:
  ldr x1, [sp, #80]
  sub x3, x1, x28
.L137:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d13, [x8, x1, lsl #3]
.L138:
  ldr x1, [sp, #80]
  sub x3, x1, x27
.L139:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L140:
  fsub d3, d9, d3
.L141:
  fmul d13, d13, d3
.L142:
  ldr x1, [sp, #80]
  sub x3, x1, x26
.L143:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L144:
  fsub d3, d9, d3
.L145:
  fmul d13, d13, d3
.L146:
  ldr x1, [sp, #80]
  sub x3, x1, x25
.L147:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L148:
  fsub d14, d10, d3
.L149:
  ldr x1, [sp, #80]
  sub x3, x1, x24
.L150:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L151:
  fsub d3, d10, d3
.L152:
  fmul d3, d14, d3
.L153:
  fadd d13, d13, d3
.L154:
  ldr x1, [sp, #80]
  sub x3, x1, x23
.L155:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L156:
  fsub d14, d11, d3
.L157:
  ldr x1, [sp, #80]
  sub x3, x1, x22
.L158:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L159:
  fsub d3, d11, d3
.L160:
  fmul d3, d14, d3
.L161:
  fadd d3, d13, d3
.L162:
  fsub d12, d12, d3
.L163:
  b .L165
.L164:
  mov x0, #1
  str x0, [sp, #176]
.L165:
  b .L178
.L166:
  ldr x1, [sp, #80]
  ldr x2, [sp, #96]
  add x3, x1, x2
.L167:
  mov x1, x3
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L176
.L168:
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  add x3, x1, x2
.L169:
  mov x1, x3
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L173
.L170:
  ldr x1, [sp, #80]
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L171:
  fsub d12, d3, d11
.L172:
  b .L175
.L173:
  ldr x1, [sp, #80]
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L174:
  fsub d12, d3, d10
.L175:
  b .L178
.L176:
  ldr x1, [sp, #80]
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L177:
  fsub d12, d3, d9
.L178:
  ldr x1, [sp, #176]
  mov x2, x21
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L180
.L179:
  b .L203
.L180:
  fmov d1, d12
  fmov d2, d5
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L194
.L181:
  fmov d1, d4
  fmov d2, d12
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L184
.L182:
  mov x0, #1
  str x0, [sp, #176]
.L183:
  b .L193
.L184:
  ldr x1, [sp, #72]
  sub x3, x1, x20
.L185:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L186:
  mov x0, x3
  str x0, [sp, #112]
.L187:
  mov x1, x19
  ldr x2, [sp, #112]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L192
.L188:
  ldr x1, [sp, #112]
  mov x2, x15
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L190
.L189:
  b .L191
.L190:
  mov x0, #1
  str x0, [sp, #176]
.L191:
  b .L193
.L192:
  mov x0, #1
  str x0, [sp, #184]
.L193:
  b .L203
.L194:
  ldr x1, [sp, #72]
  sub x3, x1, x14
.L195:
  mov x1, x3
  cmp x1, #301
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L196:
  mov x0, x3
  str x0, [sp, #112]
.L197:
  ldr x1, [sp, #112]
  mov x2, x13
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L202
.L198:
  ldr x1, [sp, #112]
  mov x2, x12
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L200
.L199:
  b .L201
.L200:
  mov x0, #1
  str x0, [sp, #176]
.L201:
  b .L203
.L202:
  mov x0, #1
  str x0, [sp, #184]
.L203:
  ldr x1, [sp, #176]
  mov x2, x11
  cmp x1, x2
  cset w0, eq
  eor w0, w0, #1
  cbnz w0, .L207
.L204:
  ldr x1, [sp, #184]
  mov x2, x10
  cmp x1, x2
  cset w0, eq
  eor w0, w0, #1
  cbnz w0, .L207
.L205:
  mov x0, #1
  mov x3, x0
.L206:
  b .L208
.L207:
  mov x0, #0
  mov x3, x0
.L208:
  mov x1, x3
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L210
.L209:
  b .L220
.L210:
  ldr x1, [sp, #24]
  add x0, x1, x9
  str x0, [sp, #24]
.L211:
  mov x1, x7
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L212:
  mov x1, x3
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L214
.L213:
  b .L215
.L214:
  mov x0, #1
  str x0, [sp, #24]
.L215:
  ldr x1, [sp, #32]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L218
.L216:
  mov x0, #1
  str x0, [sp, #176]
.L217:
  b .L220
.L218:
  mov x0, #1
  str x0, [sp, #192]
.L219:
  mov x0, #1
  str x0, [sp, #176]
.L220:
  ldr x1, [sp, #40]
  add x0, x1, x6
  str x0, [sp, #40]
.L221:
  b .L118
.L222:
  b .L110
.L223:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L224:
  b .L103
.L225:
  str d11, [sp, #512]
.L226:
  str d10, [sp, #520]
.L227:
  str d9, [sp, #528]
.L228:
  str d12, [sp, #536]
.L229:
  str d8, [sp, #544]
.L230:
  str d7, [sp, #552]
.L231:
  str d6, [sp, #560]
.L232:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print rep
  ldr x9, [sp, #8]
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
  // print m
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_m@PAGE
  add x8, x8, .Lname_m@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i1
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_i1@PAGE
  add x8, x8, .Lname_i1@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k2
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x8, .Lname_k2@PAGE
  add x8, x8, .Lname_k2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k3
  ldr x9, [sp, #56]
  sub sp, sp, #16
  adrp x8, .Lname_k3@PAGE
  add x8, x8, .Lname_k3@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j2
  ldr x9, [sp, #64]
  sub sp, sp, #16
  adrp x8, .Lname_j2@PAGE
  add x8, x8, .Lname_j2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j4
  ldr x9, [sp, #72]
  sub sp, sp, #16
  adrp x8, .Lname_j4@PAGE
  add x8, x8, .Lname_j4@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j5
  ldr x9, [sp, #80]
  sub sp, sp, #16
  adrp x8, .Lname_j5@PAGE
  add x8, x8, .Lname_j5@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ii
  ldr x9, [sp, #88]
  sub sp, sp, #16
  adrp x8, .Lname_ii@PAGE
  add x8, x8, .Lname_ii@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print lb
  ldr x9, [sp, #96]
  sub sp, sp, #16
  adrp x8, .Lname_lb@PAGE
  add x8, x8, .Lname_lb@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print n
  ldr x9, [sp, #104]
  sub sp, sp, #16
  adrp x8, .Lname_n@PAGE
  add x8, x8, .Lname_n@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print zval
  ldr x9, [sp, #112]
  sub sp, sp, #16
  adrp x8, .Lname_zval@PAGE
  add x8, x8, .Lname_zval@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r (float)
  ldr d0, [sp, #512]
  sub sp, sp, #32
  adrp x8, .Lname_r@PAGE
  add x8, x8, .Lname_r@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print s (float)
  ldr d0, [sp, #520]
  sub sp, sp, #32
  adrp x8, .Lname_s@PAGE
  add x8, x8, .Lname_s@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #528]
  sub sp, sp, #32
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print tmp (float)
  ldr d0, [sp, #536]
  sub sp, sp, #32
  adrp x8, .Lname_tmp@PAGE
  add x8, x8, .Lname_tmp@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #544]
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
  ldr d0, [sp, #552]
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
  ldr d0, [sp, #560]
  sub sp, sp, #32
  adrp x8, .Lname_fizz@PAGE
  add x8, x8, .Lname_fizz@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print kbreak
  ldr x9, [sp, #176]
  sub sp, sp, #16
  adrp x8, .Lname_kbreak@PAGE
  add x8, x8, .Lname_kbreak@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print kcont
  ldr x9, [sp, #184]
  sub sp, sp, #16
  adrp x8, .Lname_kcont@PAGE
  add x8, x8, .Lname_kcont@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print restart
  ldr x9, [sp, #192]
  sub sp, sp, #16
  adrp x8, .Lname_restart@PAGE
  add x8, x8, .Lname_restart@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  // Restore callee-saved registers
  ldr x28, [sp, #568]
  ldr x27, [sp, #576]
  ldr x26, [sp, #584]
  ldr x25, [sp, #592]
  ldr x24, [sp, #600]
  ldr x23, [sp, #608]
  ldr x22, [sp, #616]
  ldr x21, [sp, #624]
  ldr x20, [sp, #632]
  ldr x19, [sp, #640]
  ldr d11, [sp, #648]
  ldr d10, [sp, #656]
  ldr d9, [sp, #664]
  ldr d12, [sp, #672]
  ldr d8, [sp, #680]
  ldr d14, [sp, #688]
  ldr d13, [sp, #696]
  ldr d15, [sp, #704]
  ldr x29, [sp, #720]
  ldr x30, [sp, #728]
  add sp, sp, #736
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
