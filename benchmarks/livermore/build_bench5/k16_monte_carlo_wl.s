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
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  str x0, [sp, #392]
  mov x23, #0
  str x0, [sp, #408]
  mov x22, #0
  str x0, [sp, #424]
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
  cmp x1, x4
  b.gt .L55
.L44:
  fsub d3, d14, d8
.L45:
  fmadd d7, d3, d7, d8
.L46:
  fsub d8, d13, d8
.L47:
  fsub d15, d7, d6
.L48:
  fmul d3, d15, d5
.L49:
  ldr x1, [sp, #16]
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L50:
  fmov d3, d15
.L51:
  fmul d3, d3, d4
.L52:
  ldr x1, [sp, #16]
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L53:
  ldr x1, [sp, #16]
  add x0, x1, x3
  str x0, [sp, #16]
.L54:
  b .L43
.L55:
  mov x0, #1
  str x0, [sp, #16]
.L56:
  mov x0, #300
  mov x7, x0
.L57:
  mov x0, #1
  mov x6, x0
.L58:
  mov x0, #1
  str x0, [sp, #288]
.L59:
  mov x0, #1
  mov x5, x0
.L60:
  ldr x1, [sp, #16]
  cmp x1, x7
  b.gt .L67
.L61:
  ldr x1, [sp, #16]
  sub x4, x1, x6
.L62:
  mov x0, #76
  mov x3, x0
.L63:
  cbz x3, .Ldiv_by_zero
  sdiv x0, x4, x3
  mul x0, x0, x3
  sub x3, x4, x0
.L64:
  ldr x1, [sp, #16]
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  str x3, [x8, x1, lsl #3]
.L65:
  ldr x1, [sp, #16]
  add x0, x1, x5
  str x0, [sp, #16]
.L66:
  b .L60
.L67:
  mov x0, #1
  mov x4, x0
.L68:
  mov x0, #5
  mov x3, x0
.L69:
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  str x3, [x8, x4, lsl #3]
.L70:
  mov x0, #1
  str x0, [sp, #8]
.L71:
  movz x0, #38640
  movk x0, #10, lsl #16
  str x0, [sp, #304]
.L72:
  mov x0, #1
  str x0, [sp, #312]
.L73:
  mov x0, #1
  str x0, [sp, #320]
.L74:
  mov x0, #1
  str x0, [sp, #328]
.L75:
  mov x0, #0
  str x0, [sp, #336]
.L76:
  mov x0, #1
  str x0, [sp, #344]
.L77:
  mov x0, #1
  mov x28, x0
.L78:
  mov x0, #1
  mov x27, x0
.L79:
  mov x0, #1
  mov x26, x0
.L80:
  mov x0, #2
  mov x25, x0
.L81:
  mov x0, #3
  mov x24, x0
.L82:
  mov x0, #3
  str x0, [sp, #392]
.L83:
  mov x0, #4
  mov x23, x0
.L84:
  mov x0, #4
  str x0, [sp, #408]
.L85:
  mov x0, #5
  mov x22, x0
.L86:
  mov x0, #5
  str x0, [sp, #424]
.L87:
  mov x0, #0
  mov x21, x0
.L88:
  mov x0, #0
  fmov d5, x0
.L89:
  mov x0, #0
  fmov d4, x0
.L90:
  mov x0, #2
  mov x20, x0
.L91:
  mov x0, #0
  mov x19, x0
.L92:
  mov x0, #0
  mov x15, x0
.L93:
  mov x0, #2
  mov x14, x0
.L94:
  mov x0, #0
  mov x13, x0
.L95:
  mov x0, #0
  mov x12, x0
.L96:
  mov x0, #0
  mov x11, x0
.L97:
  mov x0, #0
  mov x10, x0
.L98:
  mov x0, #1
  mov x9, x0
.L99:
  mov x0, #1
  mov x7, x0
.L100:
  mov x0, #1
  mov x6, x0
.L101:
  mov x0, #1
  mov x5, x0
.L102:
  ldr x1, [sp, #8]
  ldr x2, [sp, #304]
  cmp x1, x2
  b.gt .L222
.L103:
  mov x0, #1
  str x0, [sp, #32]
.L104:
  mov x0, #1
  str x0, [sp, #24]
.L105:
  mov x0, #0
  str x0, [sp, #48]
.L106:
  mov x0, #0
  str x0, [sp, #56]
.L107:
  mov x0, #0
  str x0, [sp, #176]
.L108:
  mov x0, #1
  str x0, [sp, #192]
.L109:
  ldr x1, [sp, #192]
  ldr x2, [sp, #312]
  cmp x1, x2
  b.ne .L220
.L110:
  mov x0, #0
  str x0, [sp, #192]
.L111:
  mov x0, #0
  str x0, [sp, #176]
.L112:
  mov x0, #150
  mov x4, x0
.L113:
  ldr x1, [sp, #24]
  ldr x2, [sp, #320]
  sub x3, x1, x2
.L114:
  mul x3, x4, x3
.L115:
  ldr x2, [sp, #328]
  add x0, x3, x2
  str x0, [sp, #64]
.L116:
  mov x0, #1
  str x0, [sp, #40]
.L117:
  ldr x1, [sp, #40]
  ldr x2, [sp, #104]
  cmp x1, x2
  b.gt .L121
.L118:
  ldr x1, [sp, #176]
  ldr x2, [sp, #336]
  cmp x1, x2
  b.ne .L121
.L119:
  mov x0, #1
  mov x3, x0
.L120:
  b .L122
.L121:
  mov x0, #0
  mov x3, x0
.L122:
  mov x2, #0
  cmp x3, x2
  b.eq .L219
.L123:
  mov x0, #0
  str x0, [sp, #184]
.L124:
  ldr x1, [sp, #48]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #48]
.L125:
  ldr x1, [sp, #64]
  ldr x2, [sp, #40]
  add x3, x1, x2
.L126:
  ldr x2, [sp, #40]
  add x0, x3, x2
  str x0, [sp, #72]
.L127:
  ldr x1, [sp, #72]
  sub x3, x1, x28
.L128:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x3, [x8, x3, lsl #3]
.L129:
  str x3, [sp, #80]
.L130:
  ldr x1, [sp, #80]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L163
.L131:
  ldr x1, [sp, #80]
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L161
.L132:
  ldr x1, [sp, #56]
  add x0, x1, x27
  str x0, [sp, #56]
.L133:
  ldr x1, [sp, #80]
  sub x3, x1, x26
.L134:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d13, [x8, x3, lsl #3]
.L135:
  ldr x1, [sp, #80]
  sub x3, x1, x25
.L136:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d12, [x8, x3, lsl #3]
.L137:
  ldr x1, [sp, #80]
  sub x3, x1, x24
.L138:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L139:
  fsub d3, d9, d3
.L140:
  fmul d12, d12, d3
.L141:
.L142:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L143:
  fsub d3, d9, d3
.L144:
  fmul d14, d12, d3
.L145:
  ldr x1, [sp, #80]
  sub x3, x1, x23
.L146:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L147:
  fsub d12, d10, d3
.L148:
.L149:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L150:
  fsub d3, d10, d3
.L151:
  fmadd d14, d12, d3, d14
.L152:
  ldr x1, [sp, #80]
  sub x3, x1, x22
.L153:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L154:
  fsub d12, d11, d3
.L155:
.L156:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_d@PAGE
  add x8, x8, _arr_d@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L157:
  fsub d3, d11, d3
.L158:
  fmadd d3, d12, d3, d14
.L159:
  fsub d12, d13, d3
.L160:
  b .L162
.L161:
  mov x0, #1
  str x0, [sp, #176]
.L162:
  b .L175
.L163:
  ldr x1, [sp, #80]
  ldr x2, [sp, #96]
  add x3, x1, x2
.L164:
  mov x1, x3
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L173
.L165:
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  add x3, x1, x2
.L166:
  mov x1, x3
  ldr x2, [sp, #104]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L170
.L167:
  ldr x1, [sp, #80]
  cmp x1, #301
  b.ge .Lbounds_err
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L168:
  fsub d12, d3, d11
.L169:
  b .L172
.L170:
  ldr x1, [sp, #80]
  cmp x1, #301
  b.ge .Lbounds_err
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L171:
  fsub d12, d3, d10
.L172:
  b .L175
.L173:
  ldr x1, [sp, #80]
  cmp x1, #301
  b.ge .Lbounds_err
  adrp x8, _arr_plan@PAGE
  add x8, x8, _arr_plan@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L174:
  fsub d12, d3, d9
.L175:
  ldr x1, [sp, #176]
  mov x2, x21
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L177
.L176:
  b .L200
.L177:
  fmov d1, d12
  fmov d2, d5
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L191
.L178:
  fmov d1, d4
  fmov d2, d12
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L181
.L179:
  mov x0, #1
  str x0, [sp, #176]
.L180:
  b .L190
.L181:
  ldr x1, [sp, #72]
  sub x3, x1, x20
.L182:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x3, [x8, x3, lsl #3]
.L183:
  str x3, [sp, #112]
.L184:
  mov x1, x19
  ldr x2, [sp, #112]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L189
.L185:
  ldr x1, [sp, #112]
  mov x2, x15
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L187
.L186:
  b .L188
.L187:
  mov x0, #1
  str x0, [sp, #176]
.L188:
  b .L190
.L189:
  mov x0, #1
  str x0, [sp, #184]
.L190:
  b .L200
.L191:
  ldr x1, [sp, #72]
  sub x3, x1, x14
.L192:
  cmp x3, #301
  b.ge .Lbounds_err
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x3, [x8, x3, lsl #3]
.L193:
  str x3, [sp, #112]
.L194:
  ldr x1, [sp, #112]
  mov x2, x13
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L199
.L195:
  ldr x1, [sp, #112]
  mov x2, x12
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L197
.L196:
  b .L198
.L197:
  mov x0, #1
  str x0, [sp, #176]
.L198:
  b .L200
.L199:
  mov x0, #1
  str x0, [sp, #184]
.L200:
  ldr x1, [sp, #176]
  cmp x1, x11
  b.ne .L204
.L201:
  ldr x1, [sp, #184]
  cmp x1, x10
  b.ne .L204
.L202:
  mov x0, #1
  mov x3, x0
.L203:
  b .L205
.L204:
  mov x0, #0
  mov x3, x0
.L205:
  mov x1, x3
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L207
.L206:
  b .L217
.L207:
  ldr x1, [sp, #24]
  add x0, x1, x9
  str x0, [sp, #24]
.L208:
  adrp x8, _arr_zone@PAGE
  add x8, x8, _arr_zone@PAGEOFF
  ldr x3, [x8, x7, lsl #3]
.L209:
  mov x1, x3
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L211
.L210:
  b .L212
.L211:
  mov x0, #1
  str x0, [sp, #24]
.L212:
  ldr x1, [sp, #32]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L215
.L213:
  mov x0, #1
  str x0, [sp, #176]
.L214:
  b .L217
.L215:
  mov x0, #1
  str x0, [sp, #192]
.L216:
  mov x0, #1
  str x0, [sp, #176]
.L217:
  ldr x1, [sp, #40]
  add x0, x1, x6
  str x0, [sp, #40]
.L218:
  b .L117
.L219:
  b .L109
.L220:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L221:
  b .L102
.L222:
  str d6, [sp, #168]
  str d7, [sp, #160]
  // printint k2
  ldr x1, [sp, #48]
  sub sp, sp, #16
  str x1, [sp]
  adrp x0, .Lfmt_printint@PAGE
  add x0, x0, .Lfmt_printint@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d6, [sp, #168]
  ldr d7, [sp, #160]
.L223:
  str d6, [sp, #168]
  str d7, [sp, #160]
  // printint k3
  ldr x1, [sp, #56]
  sub sp, sp, #16
  str x1, [sp]
  adrp x0, .Lfmt_printint@PAGE
  add x0, x0, .Lfmt_printint@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d6, [sp, #168]
  ldr d7, [sp, #160]
.L224:
  str d11, [sp, #512]
.L225:
  str d10, [sp, #520]
.L226:
  str d9, [sp, #528]
.L227:
  str d12, [sp, #536]
.L228:
  str d8, [sp, #544]
.L229:
  str d7, [sp, #552]
.L230:
  str d6, [sp, #560]
.L231:
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
.Lfmt_printint:
  .asciz "%ld\n"
.Lfmt_printfloat:
  .asciz "%f\n"
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
