.global _main
.align 2

_main:
  sub sp, sp, #480
  str x30, [sp, #472]
  str x29, [sp, #464]
  add x29, sp, #464
  // Save callee-saved registers
  str x28, [sp, #368]
  str x27, [sp, #376]
  str x26, [sp, #384]
  str x25, [sp, #392]
  str x24, [sp, #400]
  str x23, [sp, #408]
  str x22, [sp, #416]
  str x21, [sp, #424]
  str x20, [sp, #432]
  str x19, [sp, #440]
  str d9, [sp, #448]
  str d8, [sp, #456]

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  mov x4, #0
  fmov d3, x0
  mov x3, #0
  mov x9, #0
  mov x8, #0
  fmov d6, x0
  fmov d5, x0
  mov x7, #0
  mov x6, #0
  fmov d4, x0
  mov x5, #0
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
  str x0, [sp, #248]
  mov x13, #0
  mov x12, #0
  mov x11, #0
  str x0, [sp, #280]
  mov x10, #0
  str x0, [sp, #296]
  str x0, [sp, #304]
  str x0, [sp, #312]
  str x0, [sp, #320]
  str x0, [sp, #328]
  str x0, [sp, #336]
  str x0, [sp, #344]
  str x0, [sp, #352]
  str x0, [sp, #360]

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
  fmov d9, x0
.L5:
  mov x0, #0
  fmov d8, x0
.L6:
  mov x0, #0
  fmov d7, x0
.L7:
  mov x0, #1
  str x0, [sp, #24]
.L8:
  mov x0, #2525
  mov x4, x0
.L9:
  mov x0, #0
  fmov d3, x0
.L10:
  mov x0, #1
  mov x3, x0
.L11:
  ldr x1, [sp, #24]
  cmp x1, x4
  b.gt .L15
.L12:
  ldr x1, [sp, #24]
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d3, [x0, x1, lsl #3]
.L13:
  ldr x1, [sp, #24]
  add x0, x1, x3
  str x0, [sp, #24]
.L14:
  b .L11
.L15:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L16:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L17:
  fadd d8, d3, d9
.L18:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L19:
  fmul d7, d3, d9
.L20:
  mov x0, #1
  str x0, [sp, #16]
.L21:
  mov x0, #101
  mov x9, x0
.L22:
  mov x0, #25
  mov x8, x0
.L23:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L24:
  mov x0, #0
  fmov d5, x0
.L25:
  mov x0, #1
  mov x7, x0
.L26:
  mov x0, #25
  mov x6, x0
.L27:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L28:
  mov x0, #1
  mov x5, x0
.L29:
  mov x0, #1
  mov x4, x0
.L30:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L46
.L31:
  mov x0, #1
  str x0, [sp, #8]
.L32:
  ldr x1, [sp, #8]
  cmp x1, x8
  b.gt .L44
.L33:
  fsub d3, d6, d9
.L34:
  fmadd d8, d3, d8, d9
.L35:
  fsub d9, d5, d9
.L36:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L37:
  mul x3, x3, x6
.L38:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L39:
  fsub d3, d8, d7
.L40:
  fmul d3, d3, d4
.L41:
  adrp x0, _arr_cx@PAGE
  add x0, x0, _arr_cx@PAGEOFF
  str d3, [x0, x3, lsl #3]
.L42:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L43:
  b .L32
.L44:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L45:
  b .L30
.L46:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L47:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L48:
  fadd d8, d3, d9
.L49:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L50:
  fmul d7, d3, d9
.L51:
  mov x0, #1
  str x0, [sp, #16]
.L52:
  mov x0, #25
  mov x9, x0
.L53:
  mov x0, #101
  mov x8, x0
.L54:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L55:
  mov x0, #0
  fmov d5, x0
.L56:
  mov x0, #1
  mov x7, x0
.L57:
  mov x0, #101
  mov x6, x0
.L58:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L59:
  mov x0, #1
  mov x5, x0
.L60:
  mov x0, #1
  mov x4, x0
.L61:
  ldr x1, [sp, #16]
  cmp x1, x9
  b.gt .L77
.L62:
  mov x0, #1
  str x0, [sp, #8]
.L63:
  ldr x1, [sp, #8]
  cmp x1, x8
  b.gt .L75
.L64:
  fsub d3, d6, d9
.L65:
  fmadd d8, d3, d8, d9
.L66:
  fsub d9, d5, d9
.L67:
  ldr x1, [sp, #16]
  sub x3, x1, x7
.L68:
  mul x3, x3, x6
.L69:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L70:
  fsub d3, d8, d7
.L71:
  fmul d3, d3, d4
.L72:
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  str d3, [x0, x3, lsl #3]
.L73:
  ldr x1, [sp, #8]
  add x0, x1, x5
  str x0, [sp, #8]
.L74:
  b .L63
.L75:
  ldr x1, [sp, #16]
  add x0, x1, x4
  str x0, [sp, #16]
.L76:
  b .L61
.L77:
  mov x0, #1
  str x0, [sp, #32]
.L78:
  mov x0, #2476
  mov x28, x0
.L79:
  mov x0, #101
  mov x27, x0
.L80:
  mov x0, #25
  mov x26, x0
.L81:
  mov x0, #1
  mov x25, x0
.L82:
  mov x0, #25
  mov x24, x0
.L83:
  mov x0, #0
  fmov d6, x0
.L84:
  mov x0, #1
  mov x23, x0
.L85:
  mov x0, #1
  mov x22, x0
.L86:
  mov x0, #25
  mov x21, x0
.L87:
  mov x0, #25
  mov x20, x0
.L88:
  mov x0, #101
  mov x19, x0
.L89:
  mov x0, #1
  mov x15, x0
.L90:
  mov x0, #25
  mov x14, x0
.L91:
  mov x0, #1
  str x0, [sp, #248]
.L92:
  mov x0, #25
  mov x13, x0
.L93:
  mov x0, #1
  mov x12, x0
.L94:
  mov x0, #101
  mov x11, x0
.L95:
  mov x0, #1
  str x0, [sp, #280]
.L96:
  mov x0, #25
  mov x10, x0
.L97:
  mov x0, #1
  mov x9, x0
.L98:
  mov x0, #1
  mov x8, x0
.L99:
  mov x0, #1
  mov x7, x0
.L100:
  mov x0, #1
  mov x6, x0
.L101:
  ldr x1, [sp, #32]
  cmp x1, x28
  b.gt .L145
.L102:
  mov x0, #1
  str x0, [sp, #16]
.L103:
  ldr x1, [sp, #16]
  cmp x1, x27
  b.gt .L114
.L104:
  mov x0, #1
  str x0, [sp, #8]
.L105:
  ldr x1, [sp, #8]
  cmp x1, x26
  b.gt .L112
.L106:
  ldr x1, [sp, #16]
  sub x3, x1, x25
.L107:
  mul x3, x3, x24
.L108:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L109:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d6, [x0, x3, lsl #3]
.L110:
  ldr x1, [sp, #8]
  add x0, x1, x23
  str x0, [sp, #8]
.L111:
  b .L105
.L112:
  ldr x1, [sp, #16]
  add x0, x1, x22
  str x0, [sp, #16]
.L113:
  b .L103
.L114:
  mov x0, #1
  str x0, [sp, #24]
.L115:
  ldr x1, [sp, #24]
  cmp x1, x21
  b.gt .L143
.L116:
  mov x0, #1
  str x0, [sp, #8]
.L117:
  ldr x1, [sp, #8]
  cmp x1, x20
  b.gt .L141
.L118:
  mov x0, #1
  str x0, [sp, #16]
.L119:
  ldr x1, [sp, #16]
  cmp x1, x19
  b.gt .L139
.L120:
  ldr x1, [sp, #16]
  sub x3, x1, x15
.L121:
  mul x4, x3, x14
.L122:
  ldr x2, [sp, #8]
  add x5, x4, x2
.L123:
  mov x0, x3
  mov x4, x0
.L124:
  mul x3, x4, x13
.L125:
  ldr x2, [sp, #8]
  add x3, x3, x2
.L126:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d5, [x0, x3, lsl #3]
.L127:
  ldr x1, [sp, #8]
  sub x3, x1, x12
.L128:
  mul x3, x3, x11
.L129:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L130:
  adrp x0, _arr_vy@PAGE
  add x0, x0, _arr_vy@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L131:
  mov x0, x4
  mov x3, x0
.L132:
  mul x3, x3, x10
.L133:
  ldr x2, [sp, #24]
  add x3, x3, x2
.L134:
  adrp x0, _arr_cx@PAGE
  add x0, x0, _arr_cx@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L135:
  fmadd d3, d4, d3, d5
.L136:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  str d3, [x0, x5, lsl #3]
.L137:
  ldr x1, [sp, #16]
  add x0, x1, x9
  str x0, [sp, #16]
.L138:
  b .L119
.L139:
  ldr x1, [sp, #8]
  add x0, x1, x8
  str x0, [sp, #8]
.L140:
  b .L117
.L141:
  ldr x1, [sp, #24]
  add x0, x1, x7
  str x0, [sp, #24]
.L142:
  b .L115
.L143:
  ldr x1, [sp, #32]
  add x0, x1, x6
  str x0, [sp, #32]
.L144:
  b .L101
.L145:
  mov x0, #51
  str x0, [sp, #296]
.L146:
  mov x0, #1
  str x0, [sp, #304]
.L147:
  mov x0, #50
  str x0, [sp, #312]
.L148:
  mov x0, #25
  str x0, [sp, #320]
.L149:
  mov x0, #1250
  str x0, [sp, #328]
.L150:
  mov x0, #13
  str x0, [sp, #336]
.L151:
  mov x0, #1263
  mov x3, x0
.L152:
  adrp x0, _arr_px@PAGE
  add x0, x0, _arr_px@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L153:
  str d7, [sp, #56]
  str x4, [sp, #64]
  str d3, [sp, #72]
  str x3, [sp, #80]
  str x9, [sp, #88]
  str x8, [sp, #96]
  str d6, [sp, #104]
  str d5, [sp, #112]
  str x7, [sp, #120]
  str x6, [sp, #128]
  str d4, [sp, #136]
  str x5, [sp, #144]
  str x15, [sp, #232]
  str x14, [sp, #240]
  str x13, [sp, #256]
  str x12, [sp, #264]
  str x11, [sp, #272]
  str x10, [sp, #288]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_153@PAGE
  add x0, x0, .Lfmt_print_153@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d7, [sp, #56]
  ldr x4, [sp, #64]
  ldr d3, [sp, #72]
  ldr x3, [sp, #80]
  ldr x9, [sp, #88]
  ldr x8, [sp, #96]
  ldr d6, [sp, #104]
  ldr d5, [sp, #112]
  ldr x7, [sp, #120]
  ldr x6, [sp, #128]
  ldr d4, [sp, #136]
  ldr x5, [sp, #144]
  ldr x15, [sp, #232]
  ldr x14, [sp, #240]
  ldr x13, [sp, #256]
  ldr x12, [sp, #264]
  ldr x11, [sp, #272]
  ldr x10, [sp, #288]
.L154:
  str d9, [sp, #344]
.L155:
  str d8, [sp, #352]
.L156:
  str d7, [sp, #360]
.L157:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #8]
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
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x1, .Lname_j@PAGE
  add x1, x1, .Lname_j@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x1, .Lname_k@PAGE
  add x1, x1, .Lname_k@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #344]
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
  ldr d0, [sp, #352]
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
  ldr d0, [sp, #360]
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
  ldr x28, [sp, #368]
  ldr x27, [sp, #376]
  ldr x26, [sp, #384]
  ldr x25, [sp, #392]
  ldr x24, [sp, #400]
  ldr x23, [sp, #408]
  ldr x22, [sp, #416]
  ldr x21, [sp, #424]
  ldr x20, [sp, #432]
  ldr x19, [sp, #440]
  ldr d9, [sp, #448]
  ldr d8, [sp, #456]
  ldr x29, [sp, #464]
  ldr x30, [sp, #472]
  add sp, sp, #480
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

.Lfmt_print_153:
  .asciz "%f\n"

.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
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
.global _arr_vy
.align 3
_arr_vy:
  .space 20208
