.global _main
.align 2

_main:
  sub sp, sp, #720
  str x30, [sp, #712]
  str x29, [sp, #704]
  add x29, sp, #704
  // Save callee-saved registers
  str d8, [sp, #664]
  str d9, [sp, #672]
  str d12, [sp, #680]
  str d11, [sp, #688]
  str d10, [sp, #696]

  // Initialize all variables to 0
  mov x0, #0

  mov x10, #0
  mov x9, #0
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
  mov x11, #0
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

.L0:
  mov x0, #0
  mov x10, x0
.L1:
  mov x0, #0
  mov x9, x0
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
  mov x10, x0
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
  cmp x10, x4
  b.gt .L28
.L20:
  fsub d3, d12, d6
.L21:
  fmadd d5, d3, d5, d6
.L22:
  fsub d6, d11, d6
.L23:
  fsub d3, d5, d4
.L24:
  fmul d3, d3, d10
.L25:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x10, lsl #3]
.L26:
  add x10, x10, x3
.L27:
  b .L19
.L28:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d6, x0
.L29:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L30:
  fadd d5, d3, d6
.L31:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L32:
  fmul d4, d3, d6
.L33:
  mov x0, #1
  mov x10, x0
.L34:
  mov x0, #2525
  mov x4, x0
.L35:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L36:
  mov x0, #0
  fmov d11, x0
.L37:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L38:
  mov x0, #1
  mov x3, x0
.L39:
  cmp x10, x4
  b.gt .L48
.L40:
  fsub d3, d12, d6
.L41:
  fmadd d5, d3, d5, d6
.L42:
  fsub d6, d11, d6
.L43:
  fsub d3, d5, d4
.L44:
  fmul d3, d3, d10
.L45:
  adrp x8, _arr_cx@PAGE
  add x8, x8, _arr_cx@PAGEOFF
  str d3, [x8, x10, lsl #3]
.L46:
  add x10, x10, x3
.L47:
  b .L39
.L48:
  mov x0, #1
  mov x9, x0
.L49:
  movz x0, #28288
  movk x0, #742, lsl #16
  mov x11, x0
.L50:
  mov x0, #101
  mov x7, x0
.L51:
  mov x0, #4
  str x0, [sp, #136]
.L52:
  mov x0, #101
  str x0, [sp, #144]
.L53:
  mov x0, #4
  str x0, [sp, #152]
.L54:
  mov x0, #101
  str x0, [sp, #160]
.L55:
  mov x0, #4
  str x0, [sp, #168]
.L56:
  mov x0, #101
  str x0, [sp, #176]
.L57:
  mov x0, #5
  str x0, [sp, #184]
.L58:
  mov x0, #101
  str x0, [sp, #192]
.L59:
  mov x0, #5
  str x0, [sp, #200]
.L60:
  mov x0, #101
  str x0, [sp, #208]
.L61:
  mov x0, #6
  str x0, [sp, #216]
.L62:
  mov x0, #101
  str x0, [sp, #224]
.L63:
  mov x0, #6
  str x0, [sp, #232]
.L64:
  mov x0, #101
  str x0, [sp, #240]
.L65:
  mov x0, #7
  str x0, [sp, #248]
.L66:
  mov x0, #101
  str x0, [sp, #256]
.L67:
  mov x0, #7
  str x0, [sp, #264]
.L68:
  mov x0, #101
  str x0, [sp, #272]
.L69:
  mov x0, #8
  str x0, [sp, #280]
.L70:
  mov x0, #101
  str x0, [sp, #288]
.L71:
  mov x0, #8
  str x0, [sp, #296]
.L72:
  mov x0, #101
  str x0, [sp, #304]
.L73:
  mov x0, #9
  str x0, [sp, #312]
.L74:
  mov x0, #101
  str x0, [sp, #320]
.L75:
  mov x0, #9
  str x0, [sp, #328]
.L76:
  mov x0, #101
  str x0, [sp, #336]
.L77:
  mov x0, #10
  str x0, [sp, #344]
.L78:
  mov x0, #101
  str x0, [sp, #352]
.L79:
  mov x0, #10
  str x0, [sp, #360]
.L80:
  mov x0, #101
  str x0, [sp, #368]
.L81:
  mov x0, #11
  str x0, [sp, #376]
.L82:
  mov x0, #101
  str x0, [sp, #384]
.L83:
  mov x0, #11
  str x0, [sp, #392]
.L84:
  mov x0, #101
  str x0, [sp, #400]
.L85:
  mov x0, #13
  str x0, [sp, #408]
.L86:
  mov x0, #101
  str x0, [sp, #416]
.L87:
  mov x0, #12
  str x0, [sp, #424]
.L88:
  mov x0, #101
  str x0, [sp, #432]
.L89:
  mov x0, #12
  str x0, [sp, #440]
.L90:
  mov x0, #101
  str x0, [sp, #448]
.L91:
  mov x0, #1
  mov x6, x0
.L92:
  mov x0, #1
  mov x5, x0
.L93:
  cmp x9, x11
  b.gt .L170
.L94:
  mov x0, #1
  mov x10, x0
.L95:
  cmp x10, x7
  b.gt .L168
.L96:
  mov x0, #404
  mov x3, x0
.L97:
  add x3, x3, x10
.L98:
  adrp x8, _arr_cx@PAGE
  add x8, x8, _arr_cx@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L99:
  fmov d7, d3
.L100:
  mov x0, #404
  str x0, [sp, #472]
.L101:
.L102:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L103:
  fsub d8, d7, d3
.L104:
  mov x0, #404
  str x0, [sp, #480]
.L105:
.L106:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d7, [x8, x3, lsl #3]
.L107:
  mov x0, #505
  mov x3, x0
.L108:
  add x3, x3, x10
.L109:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L110:
  fsub d9, d8, d3
.L111:
  mov x0, #505
  str x0, [sp, #488]
.L112:
.L113:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d8, [x8, x3, lsl #3]
.L114:
  mov x0, #606
  mov x3, x0
.L115:
  add x3, x3, x10
.L116:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L117:
  fsub d7, d9, d3
.L118:
  mov x0, #606
  str x0, [sp, #496]
.L119:
.L120:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d9, [x8, x3, lsl #3]
.L121:
  mov x0, #707
  mov x3, x0
.L122:
  add x3, x3, x10
.L123:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L124:
  fsub d8, d7, d3
.L125:
  mov x0, #707
  str x0, [sp, #504]
.L126:
.L127:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d7, [x8, x3, lsl #3]
.L128:
  mov x0, #808
  mov x3, x0
.L129:
  add x3, x3, x10
.L130:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L131:
  fsub d9, d8, d3
.L132:
  mov x0, #808
  str x0, [sp, #512]
.L133:
.L134:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d8, [x8, x3, lsl #3]
.L135:
  mov x0, #909
  mov x3, x0
.L136:
  add x3, x3, x10
.L137:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L138:
  fsub d7, d9, d3
.L139:
  mov x0, #909
  str x0, [sp, #520]
.L140:
.L141:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d9, [x8, x3, lsl #3]
.L142:
  mov x0, #1010
  mov x3, x0
.L143:
  add x3, x3, x10
.L144:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L145:
  fsub d8, d7, d3
.L146:
  mov x0, #1010
  str x0, [sp, #528]
.L147:
.L148:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d7, [x8, x3, lsl #3]
.L149:
  mov x0, #1111
  mov x3, x0
.L150:
  add x3, x3, x10
.L151:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L152:
  fsub d9, d8, d3
.L153:
  mov x0, #1111
  str x0, [sp, #536]
.L154:
.L155:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d8, [x8, x3, lsl #3]
.L156:
  mov x0, #1313
  mov x3, x0
.L157:
  add x4, x3, x10
.L158:
  mov x0, #1212
  mov x3, x0
.L159:
  add x3, x3, x10
.L160:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L161:
  fsub d3, d9, d3
.L162:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d3, [x8, x4, lsl #3]
.L163:
  mov x0, #1212
  str x0, [sp, #544]
.L164:
.L165:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  str d9, [x8, x3, lsl #3]
.L166:
  add x10, x10, x6
.L167:
  b .L95
.L168:
  add x9, x9, x5
.L169:
  b .L93
.L170:
  mov x0, #5
  str x0, [sp, #552]
.L171:
  mov x0, #1
  str x0, [sp, #560]
.L172:
  mov x0, #4
  str x0, [sp, #568]
.L173:
  mov x0, #101
  str x0, [sp, #576]
.L174:
  mov x0, #404
  str x0, [sp, #584]
.L175:
  mov x0, #51
  str x0, [sp, #592]
.L176:
  mov x0, #455
  mov x3, x0
.L177:
  adrp x8, _arr_px@PAGE
  add x8, x8, _arr_px@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L178:
  str d4, [sp, #64]
  str d5, [sp, #56]
  str d6, [sp, #48]
  str d7, [sp, #24]
  str x9, [sp, #16]
  str x10, [sp, #8]
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d4, [sp, #64]
  ldr d5, [sp, #56]
  ldr d6, [sp, #48]
  ldr d7, [sp, #24]
  ldr x9, [sp, #16]
  ldr x10, [sp, #8]
.L179:
  str x10, [sp, #600]
.L180:
  str x9, [sp, #608]
.L181:
  str d7, [sp, #616]
.L182:
  str d8, [sp, #624]
.L183:
  str d9, [sp, #632]
.L184:
  str d6, [sp, #640]
.L185:
  str d5, [sp, #648]
.L186:
  str d4, [sp, #656]
.L187:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #600]
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
  ldr x9, [sp, #608]
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
  ldr d0, [sp, #616]
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
  ldr d0, [sp, #624]
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
  ldr d0, [sp, #632]
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
  ldr d0, [sp, #640]
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
  ldr d0, [sp, #648]
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
  ldr d0, [sp, #656]
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
  ldr d8, [sp, #664]
  ldr d9, [sp, #672]
  ldr d12, [sp, #680]
  ldr d11, [sp, #688]
  ldr d10, [sp, #696]
  ldr x29, [sp, #704]
  ldr x30, [sp, #712]
  add sp, sp, #720
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
