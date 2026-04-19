.global _main
.align 2

_main:
  sub sp, sp, #608
  str x30, [sp, #600]
  str x29, [sp, #592]
  add x29, sp, #592
  // Save callee-saved registers
  str d8, [sp, #536]
  str d9, [sp, #544]
  str d12, [sp, #552]
  str d11, [sp, #560]
  str d10, [sp, #568]

  // Initialize all variables to 0
  mov x0, #0

  mov x11, #0
  mov x10, #0
  fmov d7, x0
  fmov d8, x0
  fmov d9, x0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  fmov d3, x0
  mov x4, #0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  mov x3, #0
  mov x9, #0
  mov x7, #0
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
  mov x6, #0
  mov x5, #0
  str x0, [sp, #472]
  str x0, [sp, #480]
  str x0, [sp, #488]
  str x0, [sp, #496]
  str x0, [sp, #504]
  str x0, [sp, #512]
  str x0, [sp, #520]
  str x0, [sp, #528]

.L0:
  mov x0, #0
  mov x11, x0
.L1:
  mov x0, #0
  mov x10, x0
.L2:
  mov x0, #0
  fmov d7, x0
.L3:
  mov x0, #0
  fmov d8, x0
.L4:
  mov x0, #0
  fmov d9, x0
.L5:
  mov x0, #0
  fmov d6, x0
.L6:
  mov x0, #0
  fmov d5, x0
.L7:
  mov x0, #0
  fmov d4, x0
.L8:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d6, x0
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L10:
  fadd d5, d3, d6
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L12:
  fmul d4, d3, d6
.L13:
  mov x0, #1
  mov x11, x0
.L14:
  mov x0, #2525
  mov x4, x0
.L15:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L16:
  mov x0, #0
  fmov d11, x0
.L17:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L18:
  mov x0, #1
  mov x3, x0
.L19:
  mov x1, x11
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L29
.L20:
  fsub d3, d12, d6
.L21:
  fmul d3, d3, d5
.L22:
  fadd d5, d3, d6
.L23:
  fsub d6, d11, d6
.L24:
  fsub d3, d5, d4
.L25:
  fmul d3, d3, d10
.L26:
  mov x1, x11
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L27:
  add x11, x11, x3
.L28:
  b .L19
.L29:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d6, x0
.L30:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L31:
  fadd d5, d3, d6
.L32:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L33:
  fmul d4, d3, d6
.L34:
  mov x0, #1
  mov x11, x0
.L35:
  mov x0, #2525
  mov x4, x0
.L36:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L37:
  mov x0, #0
  fmov d11, x0
.L38:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L39:
  mov x0, #1
  mov x3, x0
.L40:
  mov x1, x11
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L50
.L41:
  fsub d3, d12, d6
.L42:
  fmul d3, d3, d5
.L43:
  fadd d5, d3, d6
.L44:
  fsub d6, d11, d6
.L45:
  fsub d3, d5, d4
.L46:
  fmul d3, d3, d10
.L47:
  mov x1, x11
  adrp x8, _arr_cx@PAGE
  add x8, x8, _arr_cx@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L48:
  add x11, x11, x3
.L49:
  b .L40
.L50:
  mov x0, #1
  mov x10, x0
.L51:
  movz x0, #28288
  movk x0, #742, lsl #16
  mov x9, x0
.L52:
  mov x0, #101
  mov x7, x0
.L53:
  mov x0, #4
  str x0, [sp, #136]
.L54:
  mov x0, #101
  str x0, [sp, #144]
.L55:
  mov x0, #4
  str x0, [sp, #152]
.L56:
  mov x0, #101
  str x0, [sp, #160]
.L57:
  mov x0, #4
  str x0, [sp, #168]
.L58:
  mov x0, #101
  str x0, [sp, #176]
.L59:
  mov x0, #5
  str x0, [sp, #184]
.L60:
  mov x0, #101
  str x0, [sp, #192]
.L61:
  mov x0, #5
  str x0, [sp, #200]
.L62:
  mov x0, #101
  str x0, [sp, #208]
.L63:
  mov x0, #6
  str x0, [sp, #216]
.L64:
  mov x0, #101
  str x0, [sp, #224]
.L65:
  mov x0, #6
  str x0, [sp, #232]
.L66:
  mov x0, #101
  str x0, [sp, #240]
.L67:
  mov x0, #7
  str x0, [sp, #248]
.L68:
  mov x0, #101
  str x0, [sp, #256]
.L69:
  mov x0, #7
  str x0, [sp, #264]
.L70:
  mov x0, #101
  str x0, [sp, #272]
.L71:
  mov x0, #8
  str x0, [sp, #280]
.L72:
  mov x0, #101
  str x0, [sp, #288]
.L73:
  mov x0, #8
  str x0, [sp, #296]
.L74:
  mov x0, #101
  str x0, [sp, #304]
.L75:
  mov x0, #9
  str x0, [sp, #312]
.L76:
  mov x0, #101
  str x0, [sp, #320]
.L77:
  mov x0, #9
  str x0, [sp, #328]
.L78:
  mov x0, #101
  str x0, [sp, #336]
.L79:
  mov x0, #10
  str x0, [sp, #344]
.L80:
  mov x0, #101
  str x0, [sp, #352]
.L81:
  mov x0, #10
  str x0, [sp, #360]
.L82:
  mov x0, #101
  str x0, [sp, #368]
.L83:
  mov x0, #11
  str x0, [sp, #376]
.L84:
  mov x0, #101
  str x0, [sp, #384]
.L85:
  mov x0, #11
  str x0, [sp, #392]
.L86:
  mov x0, #101
  str x0, [sp, #400]
.L87:
  mov x0, #13
  str x0, [sp, #408]
.L88:
  mov x0, #101
  str x0, [sp, #416]
.L89:
  mov x0, #12
  str x0, [sp, #424]
.L90:
  mov x0, #101
  str x0, [sp, #432]
.L91:
  mov x0, #12
  str x0, [sp, #440]
.L92:
  mov x0, #101
  str x0, [sp, #448]
.L93:
  mov x0, #1
  mov x6, x0
.L94:
  mov x0, #1
  mov x5, x0
.L95:
  mov x1, x10
  mov x2, x9
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L172
.L96:
  mov x0, #1
  mov x11, x0
.L97:
  mov x1, x11
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L170
.L98:
  mov x0, #404
  mov x3, x0
.L99:
  add x3, x3, x11
.L100:
  mov x1, x3
  adrp x8, _arr_cx@PAGE
  add x8, x8, _arr_cx@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L101:
  fmov d7, d3
.L102:
  mov x0, #404
  mov x3, x0
.L103:
  add x3, x3, x11
.L104:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L105:
  fsub d8, d7, d3
.L106:
  mov x0, #404
  mov x3, x0
.L107:
  add x3, x3, x11
.L108:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d7, [x8, x1, lsl #3]
.L109:
  mov x0, #505
  mov x3, x0
.L110:
  add x3, x3, x11
.L111:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L112:
  fsub d9, d8, d3
.L113:
  mov x0, #505
  mov x3, x0
.L114:
  add x3, x3, x11
.L115:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d8, [x8, x1, lsl #3]
.L116:
  mov x0, #606
  mov x3, x0
.L117:
  add x3, x3, x11
.L118:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L119:
  fsub d7, d9, d3
.L120:
  mov x0, #606
  mov x3, x0
.L121:
  add x3, x3, x11
.L122:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d9, [x8, x1, lsl #3]
.L123:
  mov x0, #707
  mov x3, x0
.L124:
  add x3, x3, x11
.L125:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L126:
  fsub d8, d7, d3
.L127:
  mov x0, #707
  mov x3, x0
.L128:
  add x3, x3, x11
.L129:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d7, [x8, x1, lsl #3]
.L130:
  mov x0, #808
  mov x3, x0
.L131:
  add x3, x3, x11
.L132:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L133:
  fsub d9, d8, d3
.L134:
  mov x0, #808
  mov x3, x0
.L135:
  add x3, x3, x11
.L136:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d8, [x8, x1, lsl #3]
.L137:
  mov x0, #909
  mov x3, x0
.L138:
  add x3, x3, x11
.L139:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L140:
  fsub d7, d9, d3
.L141:
  mov x0, #909
  mov x3, x0
.L142:
  add x3, x3, x11
.L143:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d9, [x8, x1, lsl #3]
.L144:
  mov x0, #1010
  mov x3, x0
.L145:
  add x3, x3, x11
.L146:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L147:
  fsub d8, d7, d3
.L148:
  mov x0, #1010
  mov x3, x0
.L149:
  add x3, x3, x11
.L150:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d7, [x8, x1, lsl #3]
.L151:
  mov x0, #1111
  mov x3, x0
.L152:
  add x3, x3, x11
.L153:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L154:
  fsub d9, d8, d3
.L155:
  mov x0, #1111
  mov x3, x0
.L156:
  add x3, x3, x11
.L157:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d8, [x8, x1, lsl #3]
.L158:
  mov x0, #1313
  mov x3, x0
.L159:
  add x4, x3, x11
.L160:
  mov x0, #1212
  mov x3, x0
.L161:
  add x3, x3, x11
.L162:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L163:
  fsub d3, d9, d3
.L164:
  mov x1, x4
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L165:
  mov x0, #1212
  mov x3, x0
.L166:
  add x3, x3, x11
.L167:
  mov x1, x3
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d9, [x8, x1, lsl #3]
.L168:
  add x11, x11, x6
.L169:
  b .L97
.L170:
  add x10, x10, x5
.L171:
  b .L95
.L172:
  mov x0, x11
  str x0, [sp, #472]
.L173:
  mov x0, x10
  str x0, [sp, #480]
.L174:
  str d7, [sp, #488]
.L175:
  str d8, [sp, #496]
.L176:
  str d9, [sp, #504]
.L177:
  str d6, [sp, #512]
.L178:
  str d5, [sp, #520]
.L179:
  str d4, [sp, #528]
.L180:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #472]
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
  ldr x9, [sp, #480]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ar (float)
  ldr d0, [sp, #488]
  sub sp, sp, #32
  adrp x8, .Lname_ar@PAGE
  add x8, x8, .Lname_ar@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print br (float)
  ldr d0, [sp, #496]
  sub sp, sp, #32
  adrp x8, .Lname_br@PAGE
  add x8, x8, .Lname_br@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print cr (float)
  ldr d0, [sp, #504]
  sub sp, sp, #32
  adrp x8, .Lname_cr@PAGE
  add x8, x8, .Lname_cr@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #512]
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
  ldr d0, [sp, #520]
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
  ldr d0, [sp, #528]
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
  ldr d8, [sp, #536]
  ldr d9, [sp, #544]
  ldr d12, [sp, #552]
  ldr d11, [sp, #560]
  ldr d10, [sp, #568]
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
.Lname_i:
  .asciz "i"
.Lname_rep:
  .asciz "rep"
.Lname_ar:
  .asciz "ar"
.Lname_br:
  .asciz "br"
.Lname_cr:
  .asciz "cr"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_px
.align 3
_arr_px:
  .space 20208
.global _arr_cx
.align 3
_arr_cx:
  .space 20208
