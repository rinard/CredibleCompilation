.global _main
.align 2

_main:
  sub sp, sp, #896
  str x30, [sp, #888]
  str x29, [sp, #880]
  add x29, sp, #880
  // Save callee-saved registers
  str x28, [sp, #736]
  str x27, [sp, #744]
  str x26, [sp, #752]
  str x25, [sp, #760]
  str x24, [sp, #768]
  str x23, [sp, #776]
  str x22, [sp, #784]
  str x21, [sp, #792]
  str x20, [sp, #800]
  str x19, [sp, #808]
  str d13, [sp, #816]
  str d12, [sp, #824]
  str d11, [sp, #832]
  str d10, [sp, #840]
  str d9, [sp, #848]
  str d15, [sp, #856]
  str d14, [sp, #864]
  str d8, [sp, #872]

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
  mov x28, #0
  str x0, [sp, #424]
  mov x27, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  str x0, [sp, #464]
  mov x23, #0
  mov x22, #0
  mov x21, #0
  str x0, [sp, #496]
  mov x20, #0
  str x0, [sp, #512]
  mov x19, #0
  str x0, [sp, #528]
  fmov d8, x0
  str x0, [sp, #544]
  str x0, [sp, #552]
  fmov d7, x0
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
  cmp x1, x4
  b.gt .L46
.L38:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L39:
  ldr d0, [sp, #192]
  fmadd d15, d3, d15, d0
.L40:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L41:
  fsub d3, d15, d14
.L42:
  fmul d3, d3, d4
.L43:
  ldr x1, [sp, #128]
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L44:
  ldr x1, [sp, #128]
  add x0, x1, x3
  str x0, [sp, #128]
.L45:
  b .L37
.L46:
  mov x0, #1
  mov x3, x0
.L47:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L48:
  str d3, [sp, #48]
.L49:
  mov x0, #2
  mov x3, x0
.L50:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L51:
  str d3, [sp, #56]
.L52:
  mov x0, #3
  mov x3, x0
.L53:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L54:
  str d3, [sp, #64]
.L55:
  mov x0, #4
  mov x3, x0
.L56:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L57:
  str d3, [sp, #72]
.L58:
  mov x0, #5
  mov x3, x0
.L59:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L60:
  str d3, [sp, #80]
.L61:
  mov x0, #6
  mov x3, x0
.L62:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L63:
  fmov d13, d3
.L64:
  mov x0, #7
  mov x3, x0
.L65:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L66:
  fmov d12, d3
.L67:
  mov x0, #8
  mov x3, x0
.L68:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L69:
  fmov d11, d3
.L70:
  mov x0, #9
  mov x3, x0
.L71:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L72:
  fmov d10, d3
.L73:
  mov x0, #34
  mov x3, x0
.L74:
  adrp x8, _arr_spacer@PAGE
  add x8, x8, _arr_spacer@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L75:
  fmov d9, d3
.L76:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L77:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L78:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L79:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L80:
  ldr d2, [sp, #192]
  fmul d14, d3, d2
.L81:
  mov x0, #1
  str x0, [sp, #184]
.L82:
  mov x0, #5
  mov x15, x0
.L83:
  mov x0, #101
  mov x14, x0
.L84:
  mov x0, #2
  mov x13, x0
.L85:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L86:
  mov x0, #0
  fmov d5, x0
.L87:
  mov x0, #1
  mov x12, x0
.L88:
  mov x0, #202
  mov x11, x0
.L89:
  mov x0, #1
  mov x10, x0
.L90:
  mov x0, #2
  mov x9, x0
.L91:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L92:
  mov x0, #1
  mov x7, x0
.L93:
  mov x0, #1
  mov x6, x0
.L94:
  mov x0, #1
  mov x5, x0
.L95:
  ldr x1, [sp, #184]
  cmp x1, x15
  b.gt .L118
.L96:
  mov x0, #1
  str x0, [sp, #176]
.L97:
  ldr x1, [sp, #176]
  cmp x1, x14
  b.gt .L116
.L98:
  mov x0, #1
  str x0, [sp, #168]
.L99:
  ldr x1, [sp, #168]
  cmp x1, x13
  b.gt .L114
.L100:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L101:
  ldr d0, [sp, #192]
  fmadd d15, d3, d15, d0
.L102:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L103:
  ldr x1, [sp, #184]
  sub x3, x1, x12
.L104:
  mul x4, x3, x11
.L105:
  ldr x1, [sp, #176]
  sub x3, x1, x10
.L106:
  mul x3, x3, x9
.L107:
  add x3, x4, x3
.L108:
  ldr x2, [sp, #168]
  add x3, x3, x2
.L109:
  fsub d3, d15, d14
.L110:
  fmul d3, d3, d4
.L111:
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L112:
  ldr x1, [sp, #168]
  add x0, x1, x7
  str x0, [sp, #168]
.L113:
  b .L99
.L114:
  ldr x1, [sp, #176]
  add x0, x1, x6
  str x0, [sp, #176]
.L115:
  b .L97
.L116:
  ldr x1, [sp, #184]
  add x0, x1, x5
  str x0, [sp, #184]
.L117:
  b .L95
.L118:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L119:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L120:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L121:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L122:
  ldr d2, [sp, #192]
  fmul d14, d3, d2
.L123:
  mov x0, #1
  str x0, [sp, #184]
.L124:
  mov x0, #5
  mov x15, x0
.L125:
  mov x0, #101
  mov x14, x0
.L126:
  mov x0, #2
  mov x13, x0
.L127:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L128:
  mov x0, #0
  fmov d5, x0
.L129:
  mov x0, #1
  mov x12, x0
.L130:
  mov x0, #202
  mov x11, x0
.L131:
  mov x0, #1
  mov x10, x0
.L132:
  mov x0, #2
  mov x9, x0
.L133:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L134:
  mov x0, #1
  mov x7, x0
.L135:
  mov x0, #1
  mov x6, x0
.L136:
  mov x0, #1
  mov x5, x0
.L137:
  ldr x1, [sp, #184]
  cmp x1, x15
  b.gt .L160
.L138:
  mov x0, #1
  str x0, [sp, #176]
.L139:
  ldr x1, [sp, #176]
  cmp x1, x14
  b.gt .L158
.L140:
  mov x0, #1
  str x0, [sp, #168]
.L141:
  ldr x1, [sp, #168]
  cmp x1, x13
  b.gt .L156
.L142:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L143:
  ldr d0, [sp, #192]
  fmadd d15, d3, d15, d0
.L144:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L145:
  ldr x1, [sp, #184]
  sub x3, x1, x12
.L146:
  mul x4, x3, x11
.L147:
  ldr x1, [sp, #176]
  sub x3, x1, x10
.L148:
  mul x3, x3, x9
.L149:
  add x3, x4, x3
.L150:
  ldr x2, [sp, #168]
  add x3, x3, x2
.L151:
  fsub d3, d15, d14
.L152:
  fmul d3, d3, d4
.L153:
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L154:
  ldr x1, [sp, #168]
  add x0, x1, x7
  str x0, [sp, #168]
.L155:
  b .L141
.L156:
  ldr x1, [sp, #176]
  add x0, x1, x6
  str x0, [sp, #176]
.L157:
  b .L139
.L158:
  ldr x1, [sp, #184]
  add x0, x1, x5
  str x0, [sp, #184]
.L159:
  b .L137
.L160:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #192]
.L161:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L162:
  ldr d2, [sp, #192]
  fadd d15, d3, d2
.L163:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L164:
  ldr d2, [sp, #192]
  fmul d14, d3, d2
.L165:
  mov x0, #1
  str x0, [sp, #184]
.L166:
  mov x0, #5
  mov x15, x0
.L167:
  mov x0, #101
  mov x14, x0
.L168:
  mov x0, #2
  mov x13, x0
.L169:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L170:
  mov x0, #0
  fmov d5, x0
.L171:
  mov x0, #1
  mov x12, x0
.L172:
  mov x0, #202
  mov x11, x0
.L173:
  mov x0, #1
  mov x10, x0
.L174:
  mov x0, #2
  mov x9, x0
.L175:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L176:
  mov x0, #1
  mov x7, x0
.L177:
  mov x0, #1
  mov x6, x0
.L178:
  mov x0, #1
  mov x5, x0
.L179:
  ldr x1, [sp, #184]
  cmp x1, x15
  b.gt .L202
.L180:
  mov x0, #1
  str x0, [sp, #176]
.L181:
  ldr x1, [sp, #176]
  cmp x1, x14
  b.gt .L200
.L182:
  mov x0, #1
  str x0, [sp, #168]
.L183:
  ldr x1, [sp, #168]
  cmp x1, x13
  b.gt .L198
.L184:
  ldr d2, [sp, #192]
  fsub d3, d6, d2
.L185:
  ldr d0, [sp, #192]
  fmadd d15, d3, d15, d0
.L186:
  ldr d2, [sp, #192]
  fsub d0, d5, d2
  str d0, [sp, #192]
.L187:
  ldr x1, [sp, #184]
  sub x3, x1, x12
.L188:
  mul x4, x3, x11
.L189:
  ldr x1, [sp, #176]
  sub x3, x1, x10
.L190:
  mul x3, x3, x9
.L191:
  add x3, x4, x3
.L192:
  ldr x2, [sp, #168]
  add x3, x3, x2
.L193:
  fsub d3, d15, d14
.L194:
  fmul d3, d3, d4
.L195:
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L196:
  ldr x1, [sp, #168]
  add x0, x1, x7
  str x0, [sp, #168]
.L197:
  b .L183
.L198:
  ldr x1, [sp, #176]
  add x0, x1, x6
  str x0, [sp, #176]
.L199:
  b .L181
.L200:
  ldr x1, [sp, #184]
  add x0, x1, x5
  str x0, [sp, #184]
.L201:
  b .L179
.L202:
  mov x0, #1
  str x0, [sp, #8]
.L203:
  movz x0, #49240
  movk x0, #160, lsl #16
  str x0, [sp, #344]
.L204:
  mov x0, #3
  str x0, [sp, #352]
.L205:
  mov x0, #99
  str x0, [sp, #360]
.L206:
  mov x0, #1
  str x0, [sp, #368]
.L207:
  mov x0, #202
  str x0, [sp, #376]
.L208:
  mov x0, #2
  str x0, [sp, #384]
.L209:
  mov x0, #1
  str x0, [sp, #392]
.L210:
  mov x0, #202
  str x0, [sp, #400]
.L211:
  mov x0, #2
  str x0, [sp, #408]
.L212:
  mov x0, #2
  mov x28, x0
.L213:
  mov x0, #1
  str x0, [sp, #424]
.L214:
  mov x0, #202
  mov x27, x0
.L215:
  mov x0, #1
  mov x26, x0
.L216:
  mov x0, #2
  mov x25, x0
.L217:
  mov x0, #202
  mov x24, x0
.L218:
  mov x0, #1
  str x0, [sp, #464]
.L219:
  mov x0, #2
  mov x23, x0
.L220:
  mov x0, #2
  mov x22, x0
.L221:
  mov x0, #202
  mov x21, x0
.L222:
  mov x0, #1
  str x0, [sp, #496]
.L223:
  mov x0, #2
  mov x20, x0
.L224:
  mov x0, #1
  str x0, [sp, #512]
.L225:
  mov x0, #202
  mov x19, x0
.L226:
  mov x0, #1
  str x0, [sp, #528]
.L227:
  mov x0, #2
  mov x15, x0
.L228:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d8, x0
.L229:
  mov x0, #1
  str x0, [sp, #544]
.L230:
  mov x0, #202
  mov x14, x0
.L231:
  mov x0, #1
  str x0, [sp, #552]
.L232:
  mov x0, #2
  mov x13, x0
.L233:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d7, x0
.L234:
  mov x0, #1
  str x0, [sp, #568]
.L235:
  mov x0, #202
  mov x12, x0
.L236:
  mov x0, #1
  str x0, [sp, #576]
.L237:
  mov x0, #2
  mov x11, x0
.L238:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d6, x0
.L239:
  mov x0, #1
  mov x10, x0
.L240:
  mov x0, #1
  mov x9, x0
.L241:
  mov x0, #1
  mov x7, x0
.L242:
  ldr x1, [sp, #8]
  ldr x2, [sp, #344]
  cmp x1, x2
  b.gt .L355
.L243:
  mov x0, #1
  str x0, [sp, #32]
.L244:
  mov x0, #2
  str x0, [sp, #40]
.L245:
  mov x0, #2
  str x0, [sp, #16]
.L246:
  ldr x1, [sp, #16]
  ldr x2, [sp, #352]
  cmp x1, x2
  b.gt .L353
.L247:
  mov x0, #2
  str x0, [sp, #24]
.L248:
  ldr x1, [sp, #24]
  ldr x2, [sp, #360]
  cmp x1, x2
  b.gt .L351
.L249:
  ldr x1, [sp, #16]
  ldr x2, [sp, #368]
  sub x5, x1, x2
.L250:
  ldr x2, [sp, #376]
  mul x4, x5, x2
.L251:
  ldr x1, [sp, #24]
  ldr x2, [sp, #384]
  mul x3, x1, x2
.L252:
  add x3, x4, x3
.L253:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #136]
.L254:
.L255:
  ldr x2, [sp, #400]
  mul x4, x5, x2
.L256:
  ldr x1, [sp, #24]
  ldr x2, [sp, #408]
  sub x3, x1, x2
.L257:
  mul x3, x3, x28
.L258:
  add x3, x4, x3
.L259:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #144]
.L260:
  mov x6, x5
.L261:
  mul x5, x6, x27
.L262:
  ldr x1, [sp, #24]
  sub x4, x1, x26
.L263:
  mul x3, x4, x25
.L264:
  add x3, x5, x3
.L265:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #128]
.L266:
  ldr x1, [sp, #16]
  mul x5, x1, x24
.L267:
.L268:
  mul x3, x4, x23
.L269:
  add x3, x5, x3
.L270:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #152]
.L271:
  ldr x1, [sp, #16]
  sub x3, x1, x22
.L272:
  mul x5, x3, x21
.L273:
.L274:
  mul x3, x4, x20
.L275:
  add x3, x5, x3
.L276:
  ldr x2, [sp, #32]
  add x0, x3, x2
  str x0, [sp, #160]
.L277:
  ldr x1, [sp, #136]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L278:
  ldr x1, [sp, #144]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L279:
  fsub d3, d4, d3
.L280:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L281:
  ldr x1, [sp, #136]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L282:
  ldr x1, [sp, #144]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L283:
  fsub d3, d4, d3
.L284:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L285:
  ldr x1, [sp, #136]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L286:
  ldr x1, [sp, #144]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L287:
  fsub d3, d4, d3
.L288:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L289:
.L290:
  mul x5, x6, x19
.L291:
.L292:
  mul x3, x4, x15
.L293:
  add x3, x5, x3
.L294:
  ldr x2, [sp, #40]
  add x3, x3, x2
.L295:
  ldr x1, [sp, #128]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L296:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L297:
  ldr d1, [sp, #48]
  fmadd d4, d1, d3, d4
.L298:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L299:
  ldr d1, [sp, #56]
  fmadd d4, d1, d3, d4
.L300:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L301:
  ldr d1, [sp, #64]
  fmadd d5, d1, d3, d4
.L302:
  ldr x1, [sp, #152]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L303:
  ldr x1, [sp, #128]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L304:
  fmsub d4, d8, d3, d4
.L305:
  ldr x1, [sp, #160]
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L306:
  fadd d3, d4, d3
.L307:
  fmadd d3, d9, d3, d5
.L308:
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L309:
.L310:
  mul x5, x6, x14
.L311:
.L312:
  mul x3, x4, x13
.L313:
  add x3, x5, x3
.L314:
  ldr x2, [sp, #40]
  add x3, x3, x2
.L315:
  ldr x1, [sp, #128]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L316:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L317:
  ldr d1, [sp, #72]
  fmadd d4, d1, d3, d4
.L318:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L319:
  ldr d1, [sp, #80]
  fmadd d4, d1, d3, d4
.L320:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L321:
  fmadd d5, d13, d3, d4
.L322:
  ldr x1, [sp, #152]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L323:
  ldr x1, [sp, #128]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L324:
  fmsub d4, d7, d3, d4
.L325:
  ldr x1, [sp, #160]
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L326:
  fadd d3, d4, d3
.L327:
  fmadd d3, d9, d3, d5
.L328:
  adrp x8, _arr_u2@PAGE
  add x8, x8, _arr_u2@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L329:
  mov x3, x6
.L330:
  mul x3, x3, x12
.L331:
.L332:
  mul x4, x4, x11
.L333:
  add x3, x3, x4
.L334:
  ldr x2, [sp, #40]
  add x3, x3, x2
.L335:
  ldr x1, [sp, #128]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L336:
  ldr x1, [sp, #24]
  adrp x8, _arr_du1@PAGE
  add x8, x8, _arr_du1@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L337:
  fmadd d4, d12, d3, d4
.L338:
  ldr x1, [sp, #24]
  adrp x8, _arr_du2@PAGE
  add x8, x8, _arr_du2@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L339:
  fmadd d4, d11, d3, d4
.L340:
  ldr x1, [sp, #24]
  adrp x8, _arr_du3@PAGE
  add x8, x8, _arr_du3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L341:
  fmadd d5, d10, d3, d4
.L342:
  ldr x1, [sp, #152]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L343:
  ldr x1, [sp, #128]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L344:
  fmsub d4, d6, d3, d4
.L345:
  ldr x1, [sp, #160]
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L346:
  fadd d3, d4, d3
.L347:
  fmadd d3, d9, d3, d5
.L348:
  adrp x8, _arr_u3@PAGE
  add x8, x8, _arr_u3@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L349:
  ldr x1, [sp, #24]
  add x0, x1, x10
  str x0, [sp, #24]
.L350:
  b .L248
.L351:
  ldr x1, [sp, #16]
  add x0, x1, x9
  str x0, [sp, #16]
.L352:
  b .L246
.L353:
  ldr x1, [sp, #8]
  add x0, x1, x7
  str x0, [sp, #8]
.L354:
  b .L242
.L355:
  mov x0, #2
  str x0, [sp, #584]
.L356:
  mov x0, #1
  str x0, [sp, #592]
.L357:
  mov x0, #1
  str x0, [sp, #600]
.L358:
  mov x0, #202
  str x0, [sp, #608]
.L359:
  mov x0, #202
  str x0, [sp, #616]
.L360:
  mov x0, #51
  str x0, [sp, #624]
.L361:
  mov x0, #1
  str x0, [sp, #632]
.L362:
  mov x0, #50
  str x0, [sp, #640]
.L363:
  mov x0, #2
  str x0, [sp, #648]
.L364:
  mov x0, #100
  str x0, [sp, #656]
.L365:
  mov x0, #302
  str x0, [sp, #664]
.L366:
  mov x0, #2
  str x0, [sp, #672]
.L367:
  mov x0, #304
  mov x3, x0
.L368:
  adrp x8, _arr_u1@PAGE
  add x8, x8, _arr_u1@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L369:
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
.L370:
  str d13, [sp, #680]
.L371:
  str d12, [sp, #688]
.L372:
  str d11, [sp, #696]
.L373:
  str d10, [sp, #704]
.L374:
  str d9, [sp, #712]
.L375:
  str d15, [sp, #720]
.L376:
  str d14, [sp, #728]
.L377:
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
  ldr d0, [sp, #680]
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
  ldr d0, [sp, #688]
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
  ldr d0, [sp, #696]
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
  ldr d0, [sp, #704]
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
  ldr d0, [sp, #712]
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
  ldr d0, [sp, #720]
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
  ldr d0, [sp, #728]
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
  ldr x28, [sp, #736]
  ldr x27, [sp, #744]
  ldr x26, [sp, #752]
  ldr x25, [sp, #760]
  ldr x24, [sp, #768]
  ldr x23, [sp, #776]
  ldr x22, [sp, #784]
  ldr x21, [sp, #792]
  ldr x20, [sp, #800]
  ldr x19, [sp, #808]
  ldr d13, [sp, #816]
  ldr d12, [sp, #824]
  ldr d11, [sp, #832]
  ldr d10, [sp, #840]
  ldr d9, [sp, #848]
  ldr d15, [sp, #856]
  ldr d14, [sp, #864]
  ldr d8, [sp, #872]
  ldr x29, [sp, #880]
  ldr x30, [sp, #888]
  add sp, sp, #896
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
