.global _main
.align 2

_main:
  sub sp, sp, #256
  str x30, [sp, #248]
  str x29, [sp, #240]
  add x29, sp, #240
  // Save callee-saved registers
  str d9, [sp, #200]
  str d8, [sp, #208]
  str d10, [sp, #216]
  str d12, [sp, #224]
  str d11, [sp, #232]

  // Initialize all variables to 0
  mov x0, #0

  mov x10, #0
  mov x9, #0
  fmov d6, x0
  fmov d9, x0
  fmov d8, x0
  fmov d7, x0
  fmov d3, x0
  mov x4, #0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  fmov d10, x0
  fmov d12, x0
  fmov d11, x0
  mov x8, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #152]
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]

.L0:
  mov x0, #0
  mov x10, x0
.L1:
  mov x0, #0
  mov x9, x0
.L2:
  mov x0, #0
  fmov d6, x0
.L3:
  mov x0, #0
  fmov d9, x0
.L4:
  mov x0, #0
  fmov d8, x0
.L5:
  mov x0, #0
  fmov d7, x0
.L6:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L8:
  fadd d8, d3, d9
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L10:
  fmul d7, d3, d9
.L11:
  mov x0, #1
  mov x10, x0
.L12:
  mov x0, #39
  mov x4, x0
.L13:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L14:
  mov x0, #0
  fmov d5, x0
.L15:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L16:
  mov x0, #1
  mov x3, x0
.L17:
  cmp x10, x4
  b.gt .L26
.L18:
  fsub d3, d6, d9
.L19:
  fmadd d8, d3, d8, d9
.L20:
  fsub d9, d5, d9
.L21:
  fsub d3, d8, d7
.L22:
  fmul d3, d3, d4
.L23:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L24:
  add x10, x10, x3
.L25:
  b .L17
.L26:
  mov x0, #26
  mov x3, x0
.L27:
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L28:
  fmov d6, d3
.L29:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L30:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L31:
  fadd d8, d3, d9
.L32:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L33:
  fmul d7, d3, d9
.L34:
  mov x0, #1
  mov x10, x0
.L35:
  mov x0, #1001
  mov x4, x0
.L36:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L37:
  mov x0, #0
  fmov d5, x0
.L38:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L39:
  mov x0, #1
  mov x3, x0
.L40:
  cmp x10, x4
  b.gt .L49
.L41:
  fsub d3, d10, d9
.L42:
  fmadd d8, d3, d8, d9
.L43:
  fsub d9, d5, d9
.L44:
  fsub d3, d8, d7
.L45:
  fmul d3, d3, d4
.L46:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L47:
  add x10, x10, x3
.L48:
  b .L40
.L49:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L50:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L51:
  fadd d8, d3, d9
.L52:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L53:
  fmul d7, d3, d9
.L54:
  mov x0, #1
  mov x10, x0
.L55:
  mov x0, #1001
  mov x4, x0
.L56:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L57:
  mov x0, #0
  fmov d11, x0
.L58:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L59:
  mov x0, #0
  fmov d5, x0
.L60:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d4, x0
.L61:
  mov x0, #1
  mov x3, x0
.L62:
  cmp x10, x4
  b.gt .L75
.L63:
  fsub d3, d12, d9
.L64:
  fmadd d8, d3, d8, d9
.L65:
  fsub d9, d11, d9
.L66:
  fsub d3, d8, d7
.L67:
  fmul d3, d3, d10
.L68:
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L69:
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d3, [x0, x10, lsl #3]
.L70:
  fmov d1, d3
  fmov d2, d5
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L72
.L71:
  b .L73
.L72:
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  str d4, [x0, x10, lsl #3]
.L73:
  add x10, x10, x3
.L74:
  b .L62
.L75:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d9, x0
.L76:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L77:
  fadd d8, d3, d9
.L78:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L79:
  fmul d7, d3, d9
.L80:
  mov x0, #1
  mov x10, x0
.L81:
  mov x0, #1001
  mov x4, x0
.L82:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d12, x0
.L83:
  mov x0, #0
  fmov d11, x0
.L84:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d10, x0
.L85:
  mov x0, #0
  fmov d5, x0
.L86:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d4, x0
.L87:
  mov x0, #1
  mov x3, x0
.L88:
  cmp x10, x4
  b.gt .L101
.L89:
  fsub d3, d12, d9
.L90:
  fmadd d8, d3, d8, d9
.L91:
  fsub d9, d11, d9
.L92:
  fsub d3, d8, d7
.L93:
  fmul d3, d3, d10
.L94:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L95:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x10, lsl #3]
.L96:
  fmov d1, d3
  fmov d2, d5
  fcmp d1, d2
  cset w0, ls
  cbnz w0, .L98
.L97:
  b .L99
.L98:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d4, [x0, x10, lsl #3]
.L99:
  add x10, x10, x3
.L100:
  b .L88
.L101:
  mov x0, #1
  mov x10, x0
.L102:
  mov x0, #1001
  mov x4, x0
.L103:
  mov x0, #0
  fmov d4, x0
.L104:
  mov x0, #0
  fmov d3, x0
.L105:
  mov x0, #1
  mov x3, x0
.L106:
  cmp x10, x4
  b.gt .L111
.L107:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d4, [x0, x10, lsl #3]
.L108:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L109:
  add x10, x10, x3
.L110:
  b .L106
.L111:
  mov x0, #1
  mov x9, x0
.L112:
  movz x0, #39104
  movk x0, #11, lsl #16
  mov x8, x0
.L113:
  mov x0, #101
  mov x7, x0
.L114:
  movz x0, #18350
  movk x0, #31457, lsl #16
  movk x0, #44564, lsl #32
  movk x0, #16367, lsl #48
  fmov d10, x0
.L115:
  mov x0, #101
  mov x6, x0
.L116:
  mov x0, #101
  mov x5, x0
.L117:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d5, x0
.L118:
  mov x0, #1
  mov x4, x0
.L119:
  mov x0, #1
  mov x3, x0
.L120:
  cmp x9, x8
  b.gt .L142
.L121:
  movz x0, #0
  movk x0, #16436, lsl #48
  fmov d6, x0
.L122:
  fmul d4, d10, d6
.L123:
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d3, [x0, x6, lsl #3]
.L124:
  fmul d3, d4, d3
.L125:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  str d3, [x0, x7, lsl #3]
.L126:
  mov x0, #1
  mov x10, x0
.L127:
  cmp x10, x5
  b.gt .L140
.L128:
  adrp x0, _arr_u@PAGE
  add x0, x0, _arr_u@PAGEOFF
  ldr d4, [x0, x10, lsl #3]
.L129:
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d3, [x0, x10, lsl #3]
.L130:
  fdiv d3, d4, d3
.L131:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L132:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d4, [x0, x10, lsl #3]
.L133:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d3, [x0, x10, lsl #3]
.L134:
  str x10, [sp, #8]
  str x9, [sp, #16]
  str d6, [sp, #24]
  str d7, [sp, #48]
  str x4, [sp, #64]
  str d5, [sp, #72]
  str d4, [sp, #80]
  str x3, [sp, #88]
  str x8, [sp, #120]
  str x7, [sp, #128]
  str x6, [sp, #136]
  str x5, [sp, #144]
  fmov d0, d3
  stp x29, x30, [sp, #-16]!
  bl _exp
  ldp x29, x30, [sp], #16
  fmov d3, d0
  ldr x10, [sp, #8]
  ldr x9, [sp, #16]
  ldr d6, [sp, #24]
  ldr d7, [sp, #48]
  ldr x4, [sp, #64]
  ldr d5, [sp, #72]
  ldr d4, [sp, #80]
  ldr x3, [sp, #88]
  ldr x8, [sp, #120]
  ldr x7, [sp, #128]
  ldr x6, [sp, #136]
  ldr x5, [sp, #144]
.L135:
  fsub d3, d3, d5
.L136:
  fdiv d3, d4, d3
.L137:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d3, [x0, x10, lsl #3]
.L138:
  add x10, x10, x4
.L139:
  b .L127
.L140:
  add x9, x9, x3
.L141:
  b .L120
.L142:
  mov x0, #51
  mov x3, x0
.L143:
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L144:
  str x10, [sp, #8]
  str x9, [sp, #16]
  str d6, [sp, #24]
  str d7, [sp, #48]
  str d3, [sp, #56]
  str x4, [sp, #64]
  str d5, [sp, #72]
  str d4, [sp, #80]
  str x3, [sp, #88]
  str x8, [sp, #120]
  str x7, [sp, #128]
  str x6, [sp, #136]
  str x5, [sp, #144]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_144@PAGE
  add x0, x0, .Lfmt_print_144@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x10, [sp, #8]
  ldr x9, [sp, #16]
  ldr d6, [sp, #24]
  ldr d7, [sp, #48]
  ldr d3, [sp, #56]
  ldr x4, [sp, #64]
  ldr d5, [sp, #72]
  ldr d4, [sp, #80]
  ldr x3, [sp, #88]
  ldr x8, [sp, #120]
  ldr x7, [sp, #128]
  ldr x6, [sp, #136]
  ldr x5, [sp, #144]
.L145:
  mov x0, x10
  str x0, [sp, #152]
.L146:
  mov x0, x9
  str x0, [sp, #160]
.L147:
  str d6, [sp, #168]
.L148:
  str d9, [sp, #176]
.L149:
  str d8, [sp, #184]
.L150:
  str d7, [sp, #192]
.L151:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #152]
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
  ldr x9, [sp, #160]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print expmax (float)
  ldr d0, [sp, #168]
  sub sp, sp, #32
  adrp x1, .Lname_expmax@PAGE
  add x1, x1, .Lname_expmax@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #176]
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
  ldr d0, [sp, #184]
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
  ldr d0, [sp, #192]
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
  ldr d9, [sp, #200]
  ldr d8, [sp, #208]
  ldr d10, [sp, #216]
  ldr d12, [sp, #224]
  ldr d11, [sp, #232]
  ldr x29, [sp, #240]
  ldr x30, [sp, #248]
  add sp, sp, #256
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

.Lfmt_print_144:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_expmax:
  .asciz "expmax"
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
.global _arr_u
.align 3
_arr_u:
  .space 8016
.global _arr_v
.align 3
_arr_v:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_w
.align 3
_arr_w:
  .space 8016
