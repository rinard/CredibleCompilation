.global _main
.align 2

_main:
  sub sp, sp, #512
  str x30, [sp, #504]
  str x29, [sp, #496]
  add x29, sp, #496
  // Save callee-saved registers
  stp x26, x28, [sp, #360]
  stp x25, x27, [sp, #376]
  stp x24, x23, [sp, #392]
  stp x22, x21, [sp, #408]
  stp x20, x19, [sp, #424]
  stp d13, d12, [sp, #440]
  stp d11, d10, [sp, #456]
  stp d9, d8, [sp, #472]

  // Initialize all variables to 0
  mov x0, #0

  mov x26, #0
  mov x28, #0
  mov x25, #0
  str x0, [sp, #32]
  str x0, [sp, #40]
  mov x27, #0
  fmov d13, x0
  fmov d12, x0
  fmov d11, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x24, #0
  fmov d10, x0
  fmov d9, x0
  mov x23, #0
  fmov d8, x0
  fmov d7, x0
  mov x22, #0
  str x0, [sp, #184]
  str x0, [sp, #192]
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
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #304]
  str x0, [sp, #312]
  str x0, [sp, #320]
  str x0, [sp, #328]
  str x0, [sp, #336]
  str x0, [sp, #344]
  str x0, [sp, #352]

.L0:
  mov x0, #0
  mov x26, x0
.L1:
  mov x0, #0
  mov x28, x0
.L2:
  mov x0, #0
  mov x25, x0
.L3:
  mov x0, #0
  str x0, [sp, #32]
.L4:
  mov x0, #0
  str x0, [sp, #40]
.L5:
  mov x0, #0
  mov x27, x0
.L6:
  mov x0, #0
  fmov d13, x0
.L7:
  mov x0, #0
  fmov d12, x0
.L8:
  mov x0, #0
  fmov d11, x0
.L9:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d13, x0
.L10:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L11:
  fadd d12, d3, d13
.L12:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L13:
  fmul d11, d3, d13
.L14:
  mov x0, #1
  mov x26, x0
.L15:
  mov x0, #1001
  mov x4, x0
.L16:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L17:
  mov x0, #0
  fmov d5, x0
.L18:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L19:
  mov x0, #1
  mov x3, x0
.L20:
  mov x1, x26
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L30
.L21:
  fsub d3, d6, d13
.L22:
  fmul d3, d3, d12
.L23:
  fadd d12, d3, d13
.L24:
  fsub d13, d5, d13
.L25:
  fsub d3, d12, d11
.L26:
  fmul d3, d3, d4
.L27:
  mov x1, x26
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L28:
  add x26, x26, x3
.L29:
  b .L20
.L30:
  mov x0, #1
  mov x25, x0
.L31:
  movz x0, #26200
  movk x0, #175, lsl #16
  mov x24, x0
.L32:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L33:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d9, x0
.L34:
  mov x0, #1001
  mov x23, x0
.L35:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L36:
  mov x0, #0
  fmov d7, x0
.L37:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L38:
  mov x0, #1
  mov x22, x0
.L39:
  mov x0, #2
  str x0, [sp, #184]
.L40:
  mov x0, #2
  str x0, [sp, #192]
.L41:
  mov x0, #1
  mov x21, x0
.L42:
  mov x0, #1
  mov x20, x0
.L43:
  mov x0, #1
  mov x19, x0
.L44:
  mov x0, #1
  mov x15, x0
.L45:
  mov x0, #2
  mov x14, x0
.L46:
  mov x0, #0
  mov x13, x0
.L47:
  mov x0, #2
  mov x12, x0
.L48:
  mov x0, #2
  mov x11, x0
.L49:
  mov x0, #1
  mov x10, x0
.L50:
  mov x0, #1
  mov x9, x0
.L51:
  mov x0, #1
  mov x7, x0
.L52:
  mov x0, #1
  mov x6, x0
.L53:
  mov x0, #2
  mov x5, x0
.L54:
  mov x0, #1
  mov x4, x0
.L55:
  mov x1, x25
  mov x2, x24
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L120
.L56:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d13, x0
.L57:
  fadd d12, d10, d13
.L58:
  fmul d11, d9, d13
.L59:
  mov x0, #1
  mov x26, x0
.L60:
  mov x1, x26
  mov x2, x23
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L70
.L61:
  fsub d3, d8, d13
.L62:
  fmul d3, d3, d12
.L63:
  fadd d12, d3, d13
.L64:
  fsub d13, d7, d13
.L65:
  fsub d3, d12, d11
.L66:
  fmul d3, d3, d6
.L67:
  mov x1, x26
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L68:
  add x26, x26, x22
.L69:
  b .L60
.L70:
  mov x0, #101
  str x0, [sp, #32]
.L71:
  mov x0, #0
  mov x27, x0
.L72:
  mov x0, #0
  str x0, [sp, #40]
.L73:
  mov x0, #101
  mov x27, x0
.L74:
  mov x0, #50
  str x0, [sp, #32]
.L75:
  mov x0, #101
  mov x28, x0
.L76:
  mov x0, #2
  mov x26, x0
.L77:
  mov x1, x26
  mov x2, x27
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L94
.L78:
  add x28, x28, x21
.L79:
  mov x1, x26
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d5, [x8, x1, lsl #3]
.L80:
  mov x1, x26
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L81:
  sub x3, x26, x20
.L82:
  mov x1, x3
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L83:
  fmul d3, d4, d3
.L84:
  fsub d5, d5, d3
.L85:
  add x3, x26, x19
.L86:
  mov x1, x3
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L87:
  add x3, x26, x15
.L88:
  mov x1, x3
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L89:
  fmul d3, d4, d3
.L90:
  fsub d3, d5, d3
.L91:
  mov x1, x28
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L92:
  add x26, x26, x14
.L93:
  b .L77
.L94:
  mov x1, x13
  ldr x2, [sp, #32]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L118
.L95:
  mov x0, x27
  str x0, [sp, #40]
.L96:
  ldr x2, [sp, #32]
  add x27, x27, x2
.L97:
  ldr x1, [sp, #32]
  cbz x12, .Ldiv_by_zero
  sdiv x0, x1, x12
  str x0, [sp, #32]
.L98:
  mov x0, x27
  mov x28, x0
.L99:
  ldr x1, [sp, #40]
  add x26, x1, x11
.L100:
  mov x1, x26
  mov x2, x27
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L117
.L101:
  add x28, x28, x10
.L102:
  mov x1, x26
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d5, [x8, x1, lsl #3]
.L103:
  mov x1, x26
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L104:
  sub x3, x26, x9
.L105:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L106:
  fmul d3, d4, d3
.L107:
  fsub d5, d5, d3
.L108:
  add x3, x26, x7
.L109:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x1, lsl #3]
.L110:
  add x3, x26, x6
.L111:
  mov x1, x3
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L112:
  fmul d3, d4, d3
.L113:
  fsub d3, d5, d3
.L114:
  mov x1, x28
  cmp x1, #1002
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L115:
  add x26, x26, x5
.L116:
  b .L100
.L117:
  b .L94
.L118:
  add x25, x25, x4
.L119:
  b .L55
.L120:
  mov x0, x26
  str x0, [sp, #304]
.L121:
  mov x0, x28
  str x0, [sp, #312]
.L122:
  mov x0, x25
  str x0, [sp, #320]
.L123:
  mov x0, x27
  str x0, [sp, #328]
.L124:
  str d13, [sp, #336]
.L125:
  str d12, [sp, #344]
.L126:
  str d11, [sp, #352]
.L127:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #304]
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
  ldr x9, [sp, #312]
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
  ldr x9, [sp, #320]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ii
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_ii@PAGE
  add x8, x8, .Lname_ii@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ipnt
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_ipnt@PAGE
  add x8, x8, .Lname_ipnt@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ipntp
  ldr x9, [sp, #328]
  sub sp, sp, #16
  adrp x8, .Lname_ipntp@PAGE
  add x8, x8, .Lname_ipntp@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #336]
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
  ldr d0, [sp, #344]
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
  ldr d0, [sp, #352]
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
  ldp x26, x28, [sp, #360]
  ldp x25, x27, [sp, #376]
  ldp x24, x23, [sp, #392]
  ldp x22, x21, [sp, #408]
  ldp x20, x19, [sp, #424]
  ldp d13, d12, [sp, #440]
  ldp d11, d10, [sp, #456]
  ldp d9, d8, [sp, #472]
  ldr x29, [sp, #496]
  ldr x30, [sp, #504]
  add sp, sp, #512
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
.Lname_ii:
  .asciz "ii"
.Lname_ipnt:
  .asciz "ipnt"
.Lname_ipntp:
  .asciz "ipntp"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_v
.align 3
_arr_v:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
