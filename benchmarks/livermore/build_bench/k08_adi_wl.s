.global _main
.align 2

_main:
  sub sp, sp, #784
  str x30, [sp, #776]
  str x29, [sp, #768]
  add x29, sp, #768
  // Save callee-saved registers
  str x28, [sp, #624]
  str x27, [sp, #632]
  str x26, [sp, #640]
  str x25, [sp, #648]
  str x24, [sp, #656]
  str x23, [sp, #664]
  str x22, [sp, #672]
  str x21, [sp, #680]
  str x20, [sp, #688]
  str x19, [sp, #696]
  str d13, [sp, #704]
  str d12, [sp, #712]
  str d11, [sp, #720]
  str d10, [sp, #728]
  str d9, [sp, #736]
  str d15, [sp, #744]
  str d14, [sp, #752]
  str d8, [sp, #760]

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
  fmov d13, x0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  str x0, [sp, #128]
  str x0, [sp, #136]
  str x0, [sp, #144]
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  fmov d15, x0
  fmov d14, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
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
  mov x28, #0
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  mov x23, #0
  mov x22, #0
  mov x21, #0
  mov x20, #0
  fmov d8, x0
  mov x19, #0
  fmov d7, x0
  str x0, [sp, #568]
  str x0, [sp, #576]
  str x0, [sp, #584]
  str x0, [sp, #592]
  str x0, [sp, #600]
  str x0, [sp, #608]
  str x0, [sp, #616]

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
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #72]
.L9:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #80]
.L10:
  mov x0, #0
  fmov d13, x0
.L11:
  mov x0, #0
  fmov d12, x0
.L12:
  mov x0, #0
  fmov d11, x0
.L13:
  mov x0, #0
  fmov d10, x0
.L14:
  mov x0, #0
  fmov d9, x0
.L15:
  mov x0, #0
  str x0, [sp, #128]
.L16:
  mov x0, #0
  str x0, [sp, #136]
.L17:
  mov x0, #0
  str x0, [sp, #144]
.L18:
  mov x0, #0
  str x0, [sp, #152]
.L19:
  mov x0, #0
  str x0, [sp, #160]
.L20:
  mov x0, #0
  str x0, [sp, #168]
.L21:
  mov x0, #0
  str x0, [sp, #176]
.L22:
  mov x0, #0
  str x0, [sp, #184]
.L23:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #192]
.L24:
  mov x0, #0
  fmov d15, x0
.L25:
  mov x0, #0
  fmov d14, x0
.L26:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L27:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L28:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L30:
  ldr d2, [sp, #192]
  fmul d14, d3, d2
.L31:
  mov x0, #1
  str x0, [sp, #128]
.L32:
  mov x0, #39
  mov x4, x0
.L33:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L34:
  mov x0, #0
  fmov d5, x0
.L35:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L36:
  mov x0, #1
  mov x3, x0
.L37:
  ldr x1, [sp, #128]
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L47
.L38:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L39:
  fmul d3, d3, d15
.L40:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L41:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L42:
  fsub d3, d15, d14
.L43:
  fmul d3, d3, d4
.L44:
  ldr x1, [sp, #128]
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L45:
  ldr x1, [sp, #128]
  add x0, x1, x3
  str x0, [sp, #128]
.L46:
  b .L37
.L47:
  mov x0, #1
  mov x3, x0
.L48:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L49:
  str d3, [sp, #48]
.L50:
  mov x0, #2
  mov x3, x0
.L51:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L52:
  str d3, [sp, #56]
.L53:
  mov x0, #3
  mov x3, x0
.L54:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L55:
  str d3, [sp, #64]
.L56:
  mov x0, #4
  mov x3, x0
.L57:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L58:
  str d3, [sp, #72]
.L59:
  mov x0, #5
  mov x3, x0
.L60:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L61:
  str d3, [sp, #80]
.L62:
  mov x0, #6
  mov x3, x0
.L63:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L64:
  fmov d13, d3
.L65:
  mov x0, #7
  mov x3, x0
.L66:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L67:
  fmov d12, d3
.L68:
  mov x0, #8
  mov x3, x0
.L69:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L70:
  fmov d11, d3
.L71:
  mov x0, #9
  mov x3, x0
.L72:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L73:
  fmov d10, d3
.L74:
  mov x0, #34
  mov x3, x0
.L75:
  mov x1, x3
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L76:
  fmov d9, d3
.L77:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L78:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L79:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L80:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L81:
  ldr d2, [sp, #192]
  fmul d14, d3, d2
.L82:
  mov x0, #1
  str x0, [sp, #184]
.L83:
  mov x0, #5
  mov x15, x0
.L84:
  mov x0, #101
  mov x14, x0
.L85:
  mov x0, #2
  mov x13, x0
.L86:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L87:
  mov x0, #0
  fmov d5, x0
.L88:
  mov x0, #1
  mov x12, x0
.L89:
  mov x0, #202
  mov x11, x0
.L90:
  mov x0, #1
  mov x10, x0
.L91:
  mov x0, #2
  mov x9, x0
.L92:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L93:
  mov x0, #1
  mov x7, x0
.L94:
  mov x0, #1
  mov x6, x0
.L95:
  mov x0, #1
  mov x5, x0
.L96:
  ldr x1, [sp, #184]
  mov x2, x15
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L120
.L97:
  mov x0, #1
  str x0, [sp, #176]
.L98:
  ldr x1, [sp, #176]
  mov x2, x14
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L118
.L99:
  mov x0, #1
  str x0, [sp, #168]
.L100:
  ldr x1, [sp, #168]
  mov x2, x13
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L116
.L101:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L102:
  fmul d3, d3, d15
.L103:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L104:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L105:
  ldr x1, [sp, #184]
  sub x3, x1, x12
.L106:
  mul x4, x3, x11
.L107:
  ldr x1, [sp, #176]
  sub x3, x1, x10
.L108:
  mul x3, x3, x9
.L109:
  add x3, x4, x3
.L110:
  ldr x2, [sp, #168]
  add x3, x3, x2
.L111:
  fsub d3, d15, d14
.L112:
  fmul d3, d3, d4
.L113:
  mov x1, x3
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L114:
  ldr x1, [sp, #168]
  add x0, x1, x7
  str x0, [sp, #168]
.L115:
  b .L100
.L116:
  ldr x1, [sp, #176]
  add x0, x1, x6
  str x0, [sp, #176]
.L117:
  b .L98
.L118:
  ldr x1, [sp, #184]
  add x0, x1, x5
  str x0, [sp, #184]
.L119:
  b .L96
.L120:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L121:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L122:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L123:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L124:
  ldr d2, [sp, #192]
  fmul d14, d3, d2
.L125:
  mov x0, #1
  str x0, [sp, #184]
.L126:
  mov x0, #5
  mov x15, x0
.L127:
  mov x0, #101
  mov x14, x0
.L128:
  mov x0, #2
  mov x13, x0
.L129:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L130:
  mov x0, #0
  fmov d5, x0
.L131:
  mov x0, #1
  mov x12, x0
.L132:
  mov x0, #202
  mov x11, x0
.L133:
  mov x0, #1
  mov x10, x0
.L134:
  mov x0, #2
  mov x9, x0
.L135:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L136:
  mov x0, #1
  mov x7, x0
.L137:
  mov x0, #1
  mov x6, x0
.L138:
  mov x0, #1
  mov x5, x0
.L139:
  ldr x1, [sp, #184]
  mov x2, x15
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L163
.L140:
  mov x0, #1
  str x0, [sp, #176]
.L141:
  ldr x1, [sp, #176]
  mov x2, x14
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L161
.L142:
  mov x0, #1
  str x0, [sp, #168]
.L143:
  ldr x1, [sp, #168]
  mov x2, x13
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L159
.L144:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L145:
  fmul d3, d3, d15
.L146:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L147:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L148:
  ldr x1, [sp, #184]
  sub x3, x1, x12
.L149:
  mul x4, x3, x11
.L150:
  ldr x1, [sp, #176]
  sub x3, x1, x10
.L151:
  mul x3, x3, x9
.L152:
  add x3, x4, x3
.L153:
  ldr x2, [sp, #168]
  add x3, x3, x2
.L154:
  fsub d3, d15, d14
.L155:
  fmul d3, d3, d4
.L156:
  mov x1, x3
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L157:
  ldr x1, [sp, #168]
  add x0, x1, x7
  str x0, [sp, #168]
.L158:
  b .L143
.L159:
  ldr x1, [sp, #176]
  add x0, x1, x6
  str x0, [sp, #176]
.L160:
  b .L141
.L161:
  ldr x1, [sp, #184]
  add x0, x1, x5
  str x0, [sp, #184]
.L162:
  b .L139
.L163:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L164:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L165:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L166:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L167:
  ldr d2, [sp, #192]
  fmul d14, d3, d2
.L168:
  mov x0, #1
  str x0, [sp, #184]
.L169:
  mov x0, #5
  mov x15, x0
.L170:
  mov x0, #101
  mov x14, x0
.L171:
  mov x0, #2
  mov x13, x0
.L172:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L173:
  mov x0, #0
  fmov d5, x0
.L174:
  mov x0, #1
  mov x12, x0
.L175:
  mov x0, #202
  mov x11, x0
.L176:
  mov x0, #1
  mov x10, x0
.L177:
  mov x0, #2
  mov x9, x0
.L178:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L179:
  mov x0, #1
  mov x7, x0
.L180:
  mov x0, #1
  mov x6, x0
.L181:
  mov x0, #1
  mov x5, x0
.L182:
  ldr x1, [sp, #184]
  mov x2, x15
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L206
.L183:
  mov x0, #1
  str x0, [sp, #176]
.L184:
  ldr x1, [sp, #176]
  mov x2, x14
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L204
.L185:
  mov x0, #1
  str x0, [sp, #168]
.L186:
  ldr x1, [sp, #168]
  mov x2, x13
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L202
.L187:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L188:
  fmul d3, d3, d15
.L189:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L190:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L191:
  ldr x1, [sp, #184]
  sub x3, x1, x12
.L192:
  mul x4, x3, x11
.L193:
  ldr x1, [sp, #176]
  sub x3, x1, x10
.L194:
  mul x3, x3, x9
.L195:
  add x3, x4, x3
.L196:
  ldr x2, [sp, #168]
  add x3, x3, x2
.L197:
  fsub d3, d15, d14
.L198:
  fmul d3, d3, d4
.L199:
  mov x1, x3
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L200:
  ldr x1, [sp, #168]
  add x0, x1, x7
  str x0, [sp, #168]
.L201:
  b .L186
.L202:
  ldr x1, [sp, #176]
  add x0, x1, x6
  str x0, [sp, #176]
.L203:
  b .L184
.L204:
  ldr x1, [sp, #184]
  add x0, x1, x5
  str x0, [sp, #184]
.L205:
  b .L182
.L206:
  mov x0, #1
  str x0, [sp, #8]
.L207:
  movz x0, #49240
  movk x0, #160, lsl #16
  str x0, [sp, #344]
.L208:
  mov x0, #3
  str x0, [sp, #352]
.L209:
  mov x0, #99
  str x0, [sp, #360]
.L210:
  mov x0, #1
  str x0, [sp, #368]
.L211:
  mov x0, #202
  str x0, [sp, #376]
.L212:
  mov x0, #2
  str x0, [sp, #384]
.L213:
  mov x0, #1
  str x0, [sp, #392]
.L214:
  mov x0, #202
  str x0, [sp, #400]
.L215:
  mov x0, #2
  str x0, [sp, #408]
.L216:
  mov x0, #2
  str x0, [sp, #416]
.L217:
  mov x0, #1
  str x0, [sp, #424]
.L218:
  mov x0, #202
  str x0, [sp, #432]
.L219:
  mov x0, #1
  str x0, [sp, #440]
.L220:
  mov x0, #2
  str x0, [sp, #448]
.L221:
  mov x0, #202
  str x0, [sp, #456]
.L222:
  mov x0, #1
  str x0, [sp, #464]
.L223:
  mov x0, #2
  mov x28, x0
.L224:
  mov x0, #2
  mov x27, x0
.L225:
  mov x0, #202
  mov x26, x0
.L226:
  mov x0, #1
  mov x25, x0
.L227:
  mov x0, #2
  mov x24, x0
.L228:
  mov x0, #1
  mov x23, x0
.L229:
  mov x0, #202
  mov x22, x0
.L230:
  mov x0, #1
  mov x21, x0
.L231:
  mov x0, #2
  mov x20, x0
.L232:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d8, x0
.L233:
  mov x0, #1
  mov x19, x0
.L234:
  mov x0, #202
  mov x15, x0
.L235:
  mov x0, #1
  mov x14, x0
.L236:
  mov x0, #2
  mov x13, x0
.L237:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d7, x0
.L238:
  mov x0, #1
  mov x12, x0
.L239:
  mov x0, #202
  mov x11, x0
.L240:
  mov x0, #1
  mov x10, x0
.L241:
  mov x0, #2
  mov x9, x0
.L242:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d6, x0
.L243:
  mov x0, #1
  mov x7, x0
.L244:
  mov x0, #1
  mov x6, x0
.L245:
  mov x0, #1
  mov x5, x0
.L246:
  ldr x1, [sp, #8]
  ldr x2, [sp, #344]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L374
.L247:
  mov x0, #1
  str x0, [sp, #32]
.L248:
  mov x0, #2
  str x0, [sp, #40]
.L249:
  mov x0, #2
  str x0, [sp, #16]
.L250:
  ldr x1, [sp, #16]
  ldr x2, [sp, #352]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L372
.L251:
  mov x0, #2
  str x0, [sp, #24]
.L252:
  ldr x1, [sp, #24]
  ldr x2, [sp, #360]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L370
.L253:
  ldr x1, [sp, #16]
  ldr x2, [sp, #368]
  sub x3, x1, x2
.L254:
  ldr x2, [sp, #376]
  mul x4, x3, x2
.L255:
  ldr x1, [sp, #24]
  ldr x2, [sp, #384]
  mul x3, x1, x2
.L256:
  add x3, x4, x3
.L257:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #136]
.L258:
  ldr x1, [sp, #16]
  ldr x2, [sp, #392]
  sub x3, x1, x2
.L259:
  ldr x2, [sp, #400]
  mul x4, x3, x2
.L260:
  ldr x1, [sp, #24]
  ldr x2, [sp, #408]
  sub x3, x1, x2
.L261:
  ldr x2, [sp, #416]
  mul x3, x3, x2
.L262:
  add x3, x4, x3
.L263:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #144]
.L264:
  ldr x1, [sp, #16]
  ldr x2, [sp, #424]
  sub x3, x1, x2
.L265:
  ldr x2, [sp, #432]
  mul x4, x3, x2
.L266:
  ldr x1, [sp, #24]
  ldr x2, [sp, #440]
  sub x3, x1, x2
.L267:
  ldr x2, [sp, #448]
  mul x3, x3, x2
.L268:
  add x3, x4, x3
.L269:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #128]
.L270:
  ldr x1, [sp, #16]
  ldr x2, [sp, #456]
  mul x4, x1, x2
.L271:
  ldr x1, [sp, #24]
  ldr x2, [sp, #464]
  sub x3, x1, x2
.L272:
  mul x3, x3, x28
.L273:
  add x3, x4, x3
.L274:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #152]
.L275:
  ldr x1, [sp, #16]
  sub x3, x1, x27
.L276:
  mul x4, x3, x26
.L277:
  ldr x1, [sp, #24]
  sub x3, x1, x25
.L278:
  mul x3, x3, x24
.L279:
  add x3, x4, x3
.L280:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #160]
.L281:
  ldr x1, [sp, #136]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L282:
  ldr x1, [sp, #144]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L283:
  fsub d3, d4, d3
.L284:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L285:
  ldr x1, [sp, #136]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L286:
  ldr x1, [sp, #144]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L287:
  fsub d3, d4, d3
.L288:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L289:
  ldr x1, [sp, #136]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L290:
  ldr x1, [sp, #144]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L291:
  fsub d3, d4, d3
.L292:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L293:
  ldr x1, [sp, #16]
  sub x3, x1, x23
.L294:
  mul x4, x3, x22
.L295:
  ldr x1, [sp, #24]
  sub x3, x1, x21
.L296:
  mul x3, x3, x20
.L297:
  add x3, x4, x3
.L298:
  ldr x2, [sp, #40]
  add x3, x3, x2
.L299:
  ldr x1, [sp, #128]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L300:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L301:
  ldr d1, [sp, #48]
  fmul d3, d1, d3
.L302:
  fadd d4, d4, d3
.L303:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L304:
  ldr d1, [sp, #56]
  fmul d3, d1, d3
.L305:
  fadd d4, d4, d3
.L306:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L307:
  ldr d1, [sp, #64]
  fmul d3, d1, d3
.L308:
  fadd d5, d4, d3
.L309:
  ldr x1, [sp, #152]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L310:
  ldr x1, [sp, #128]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L311:
  fmul d3, d8, d3
.L312:
  fsub d4, d4, d3
.L313:
  ldr x1, [sp, #160]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L314:
  fadd d3, d4, d3
.L315:
  fmul d3, d9, d3
.L316:
  fadd d3, d5, d3
.L317:
  mov x1, x3
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L318:
  ldr x1, [sp, #16]
  sub x3, x1, x19
.L319:
  mul x4, x3, x15
.L320:
  ldr x1, [sp, #24]
  sub x3, x1, x14
.L321:
  mul x3, x3, x13
.L322:
  add x3, x4, x3
.L323:
  ldr x2, [sp, #40]
  add x3, x3, x2
.L324:
  ldr x1, [sp, #128]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L325:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L326:
  ldr d1, [sp, #72]
  fmul d3, d1, d3
.L327:
  fadd d4, d4, d3
.L328:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L329:
  ldr d1, [sp, #80]
  fmul d3, d1, d3
.L330:
  fadd d4, d4, d3
.L331:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L332:
  fmul d3, d13, d3
.L333:
  fadd d5, d4, d3
.L334:
  ldr x1, [sp, #152]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L335:
  ldr x1, [sp, #128]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L336:
  fmul d3, d7, d3
.L337:
  fsub d4, d4, d3
.L338:
  ldr x1, [sp, #160]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L339:
  fadd d3, d4, d3
.L340:
  fmul d3, d9, d3
.L341:
  fadd d3, d5, d3
.L342:
  mov x1, x3
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L343:
  ldr x1, [sp, #16]
  sub x3, x1, x12
.L344:
  mul x4, x3, x11
.L345:
  ldr x1, [sp, #24]
  sub x3, x1, x10
.L346:
  mul x3, x3, x9
.L347:
  add x3, x4, x3
.L348:
  ldr x2, [sp, #40]
  add x3, x3, x2
.L349:
  ldr x1, [sp, #128]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L350:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L351:
  fmul d3, d12, d3
.L352:
  fadd d4, d4, d3
.L353:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L354:
  fmul d3, d11, d3
.L355:
  fadd d4, d4, d3
.L356:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L357:
  fmul d3, d10, d3
.L358:
  fadd d5, d4, d3
.L359:
  ldr x1, [sp, #152]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L360:
  ldr x1, [sp, #128]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L361:
  fmul d3, d6, d3
.L362:
  fsub d4, d4, d3
.L363:
  ldr x1, [sp, #160]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L364:
  fadd d3, d4, d3
.L365:
  fmul d3, d9, d3
.L366:
  fadd d3, d5, d3
.L367:
  mov x1, x3
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L368:
  ldr x1, [sp, #24]
  add x0, x1, x7
  str x0, [sp, #24]
.L369:
  b .L252
.L370:
  ldr x1, [sp, #16]
  add x0, x1, x6
  str x0, [sp, #16]
.L371:
  b .L250
.L372:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L373:
  b .L246
.L374:
  str d13, [sp, #568]
.L375:
  str d12, [sp, #576]
.L376:
  str d11, [sp, #584]
.L377:
  str d10, [sp, #592]
.L378:
  str d9, [sp, #600]
.L379:
  str d15, [sp, #608]
.L380:
  str d14, [sp, #616]
.L381:
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
  // print kx
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_kx@PAGE
  add x8, x8, .Lname_kx@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ky
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_ky@PAGE
  add x8, x8, .Lname_ky@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print nl1
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_nl1@PAGE
  add x8, x8, .Lname_nl1@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print nl2
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_nl2@PAGE
  add x8, x8, .Lname_nl2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print a11 (float)
  ldr d0, [sp, #48]
  sub sp, sp, #32
  adrp x8, .Lname_a11@PAGE
  add x8, x8, .Lname_a11@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a12 (float)
  ldr d0, [sp, #56]
  sub sp, sp, #32
  adrp x8, .Lname_a12@PAGE
  add x8, x8, .Lname_a12@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a13 (float)
  ldr d0, [sp, #64]
  sub sp, sp, #32
  adrp x8, .Lname_a13@PAGE
  add x8, x8, .Lname_a13@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a21 (float)
  ldr d0, [sp, #72]
  sub sp, sp, #32
  adrp x8, .Lname_a21@PAGE
  add x8, x8, .Lname_a21@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a22 (float)
  ldr d0, [sp, #80]
  sub sp, sp, #32
  adrp x8, .Lname_a22@PAGE
  add x8, x8, .Lname_a22@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a23 (float)
  ldr d0, [sp, #568]
  sub sp, sp, #32
  adrp x8, .Lname_a23@PAGE
  add x8, x8, .Lname_a23@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a31 (float)
  ldr d0, [sp, #576]
  sub sp, sp, #32
  adrp x8, .Lname_a31@PAGE
  add x8, x8, .Lname_a31@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a32 (float)
  ldr d0, [sp, #584]
  sub sp, sp, #32
  adrp x8, .Lname_a32@PAGE
  add x8, x8, .Lname_a32@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print a33 (float)
  ldr d0, [sp, #592]
  sub sp, sp, #32
  adrp x8, .Lname_a33@PAGE
  add x8, x8, .Lname_a33@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print sig (float)
  ldr d0, [sp, #600]
  sub sp, sp, #32
  adrp x8, .Lname_sig@PAGE
  add x8, x8, .Lname_sig@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print idx
  ldr x9, [sp, #128]
  sub sp, sp, #16
  adrp x8, .Lname_idx@PAGE
  add x8, x8, .Lname_idx@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_yp
  ldr x9, [sp, #136]
  sub sp, sp, #16
  adrp x8, .Lname_idx_yp@PAGE
  add x8, x8, .Lname_idx_yp@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_ym
  ldr x9, [sp, #144]
  sub sp, sp, #16
  adrp x8, .Lname_idx_ym@PAGE
  add x8, x8, .Lname_idx_ym@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_xp
  ldr x9, [sp, #152]
  sub sp, sp, #16
  adrp x8, .Lname_idx_xp@PAGE
  add x8, x8, .Lname_idx_xp@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print idx_xm
  ldr x9, [sp, #160]
  sub sp, sp, #16
  adrp x8, .Lname_idx_xm@PAGE
  add x8, x8, .Lname_idx_xm@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k1
  ldr x9, [sp, #168]
  sub sp, sp, #16
  adrp x8, .Lname_k1@PAGE
  add x8, x8, .Lname_k1@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k2
  ldr x9, [sp, #176]
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
  ldr x9, [sp, #184]
  sub sp, sp, #16
  adrp x8, .Lname_k3@PAGE
  add x8, x8, .Lname_k3@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #192]
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
  ldr d0, [sp, #608]
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
  ldr d0, [sp, #616]
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
  ldr x28, [sp, #624]
  ldr x27, [sp, #632]
  ldr x26, [sp, #640]
  ldr x25, [sp, #648]
  ldr x24, [sp, #656]
  ldr x23, [sp, #664]
  ldr x22, [sp, #672]
  ldr x21, [sp, #680]
  ldr x20, [sp, #688]
  ldr x19, [sp, #696]
  ldr d13, [sp, #704]
  ldr d12, [sp, #712]
  ldr d11, [sp, #720]
  ldr d10, [sp, #728]
  ldr d9, [sp, #736]
  ldr d15, [sp, #744]
  ldr d14, [sp, #752]
  ldr d8, [sp, #760]
  ldr x29, [sp, #768]
  ldr x30, [sp, #776]
  add sp, sp, #784
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
.Lname_kx:
  .asciz "kx"
.Lname_ky:
  .asciz "ky"
.Lname_nl1:
  .asciz "nl1"
.Lname_nl2:
  .asciz "nl2"
.Lname_a11:
  .asciz "a11"
.Lname_a12:
  .asciz "a12"
.Lname_a13:
  .asciz "a13"
.Lname_a21:
  .asciz "a21"
.Lname_a22:
  .asciz "a22"
.Lname_a23:
  .asciz "a23"
.Lname_a31:
  .asciz "a31"
.Lname_a32:
  .asciz "a32"
.Lname_a33:
  .asciz "a33"
.Lname_sig:
  .asciz "sig"
.Lname_idx:
  .asciz "idx"
.Lname_idx_yp:
  .asciz "idx_yp"
.Lname_idx_ym:
  .asciz "idx_ym"
.Lname_idx_xp:
  .asciz "idx_xp"
.Lname_idx_xm:
  .asciz "idx_xm"
.Lname_k1:
  .asciz "k1"
.Lname_k2:
  .asciz "k2"
.Lname_k3:
  .asciz "k3"
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
.global _arr_u1
.align 3
_arr_u1:
  .space 8088
.global _arr_u2
.align 3
_arr_u2:
  .space 8088
.global _arr_u3
.align 3
_arr_u3:
  .space 8088
.global _arr_du1
.align 3
_arr_du1:
  .space 816
.global _arr_du2
.align 3
_arr_du2:
  .space 816
.global _arr_du3
.align 3
_arr_du3:
  .space 816
