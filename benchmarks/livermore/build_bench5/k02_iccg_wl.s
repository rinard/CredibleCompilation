.global _main
.align 2

_main:
  sub sp, sp, #528
  str x30, [sp, #520]
  str x29, [sp, #512]
  add x29, sp, #512
  // Save callee-saved registers
  str x23, [sp, #376]
  str x27, [sp, #384]
  str x22, [sp, #392]
  str x26, [sp, #400]
  str x25, [sp, #408]
  str x24, [sp, #416]
  str x28, [sp, #424]
  str x21, [sp, #432]
  str x20, [sp, #440]
  str x19, [sp, #448]
  str d12, [sp, #456]
  str d11, [sp, #464]
  str d10, [sp, #472]
  str d13, [sp, #480]
  str d9, [sp, #488]
  str d8, [sp, #496]

  // Initialize all variables to 0
  mov x0, #0

  mov x23, #0
  mov x27, #0
  mov x22, #0
  mov x26, #0
  mov x25, #0
  mov x24, #0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x28, #0
  fmov d13, x0
  fmov d9, x0
  mov x21, #0
  fmov d8, x0
  fmov d7, x0
  mov x20, #0
  str x0, [sp, #184]
  str x0, [sp, #192]
  mov x19, #0
  mov x15, #0
  mov x14, #0
  str x0, [sp, #224]
  mov x13, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
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

.L0:
  mov x0, #0
  mov x23, x0
.L1:
  mov x0, #0
  mov x27, x0
.L2:
  mov x0, #0
  mov x22, x0
.L3:
  mov x0, #0
  mov x26, x0
.L4:
  mov x0, #0
  mov x25, x0
.L5:
  mov x0, #0
  mov x24, x0
.L6:
  mov x0, #0
  fmov d12, x0
.L7:
  mov x0, #0
  fmov d11, x0
.L8:
  mov x0, #0
  fmov d10, x0
.L9:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L10:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L11:
  fadd d11, d3, d12
.L12:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L13:
  fmul d10, d3, d12
.L14:
  mov x0, #1
  mov x23, x0
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
  cmp x23, x4
  b.gt .L29
.L21:
  fsub d3, d6, d12
.L22:
  fmadd d11, d3, d11, d12
.L23:
  fsub d12, d5, d12
.L24:
  fsub d3, d11, d10
.L25:
  fmul d3, d3, d4
.L26:
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  str d3, [x8, x23, lsl #3]
.L27:
  add x23, x23, x3
.L28:
  b .L20
.L29:
  mov x0, #1
  mov x22, x0
.L30:
  movz x0, #26200
  movk x0, #175, lsl #16
  mov x28, x0
.L31:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d13, x0
.L32:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d9, x0
.L33:
  mov x0, #1001
  mov x21, x0
.L34:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L35:
  mov x0, #0
  fmov d7, x0
.L36:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d6, x0
.L37:
  mov x0, #1
  mov x20, x0
.L38:
  mov x0, #2
  str x0, [sp, #184]
.L39:
  mov x0, #2
  str x0, [sp, #192]
.L40:
  mov x0, #1
  mov x19, x0
.L41:
  mov x0, #1
  mov x15, x0
.L42:
  mov x0, #1
  mov x14, x0
.L43:
  mov x0, #1
  str x0, [sp, #224]
.L44:
  mov x0, #2
  mov x13, x0
.L45:
  mov x0, #0
  mov x12, x0
.L46:
  mov x0, #2
  mov x11, x0
.L47:
  mov x0, #2
  mov x10, x0
.L48:
  mov x0, #1
  mov x9, x0
.L49:
  mov x0, #1
  mov x7, x0
.L50:
  mov x0, #1
  mov x6, x0
.L51:
  mov x0, #1
  str x0, [sp, #288]
.L52:
  mov x0, #2
  mov x5, x0
.L53:
  mov x0, #1
  mov x4, x0
.L54:
  cmp x22, x28
  b.gt .L114
.L55:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d12, x0
.L56:
  fadd d11, d13, d12
.L57:
  fmul d10, d9, d12
.L58:
  mov x0, #1
  mov x23, x0
.L59:
  cmp x23, x21
  b.gt .L68
.L60:
  fsub d3, d8, d12
.L61:
  fmadd d11, d3, d11, d12
.L62:
  fsub d12, d7, d12
.L63:
  fsub d3, d11, d10
.L64:
  fmul d3, d3, d6
.L65:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x23, lsl #3]
.L66:
  add x23, x23, x20
.L67:
  b .L59
.L68:
  mov x0, #101
  mov x26, x0
.L69:
  mov x0, #0
  mov x24, x0
.L70:
  mov x0, #0
  mov x25, x0
.L71:
  mov x0, #101
  mov x24, x0
.L72:
  mov x0, #50
  mov x26, x0
.L73:
  mov x0, #101
  mov x27, x0
.L74:
  mov x0, #2
  mov x23, x0
.L75:
  cmp x23, x24
  b.gt .L90
.L76:
  add x27, x27, x19
.L77:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d5, [x8, x23, lsl #3]
.L78:
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x23, lsl #3]
.L79:
  sub x3, x23, x15
.L80:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L81:
  fmsub d5, d4, d3, d5
.L82:
  add x3, x23, x14
.L83:
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L84:
.L85:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L86:
  fmsub d3, d4, d3, d5
.L87:
  cmp x27, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x27, lsl #3]
.L88:
  add x23, x23, x13
.L89:
  b .L75
.L90:
  cmp x12, x26
  b.ge .L112
.L91:
  mov x25, x24
.L92:
  add x24, x24, x26
.L93:
  cbz x11, .Ldiv_by_zero
  sdiv x26, x26, x11
.L94:
  mov x27, x24
.L95:
  add x23, x25, x10
.L96:
  cmp x23, x24
  b.gt .L111
.L97:
  add x27, x27, x9
.L98:
  cmp x23, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d5, [x8, x23, lsl #3]
.L99:
  cmp x23, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x23, lsl #3]
.L100:
  sub x3, x23, x7
.L101:
  cmp x3, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L102:
  fmsub d5, d4, d3, d5
.L103:
  add x3, x23, x6
.L104:
  cmp x3, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_v@PAGE
  add x8, x8, _arr_v@PAGEOFF
  ldr d4, [x8, x3, lsl #3]
.L105:
.L106:
  cmp x3, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L107:
  fmsub d3, d4, d3, d5
.L108:
  cmp x27, #1002
  b.ge .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x27, lsl #3]
.L109:
  add x23, x23, x5
.L110:
  b .L96
.L111:
  b .L90
.L112:
  add x22, x22, x4
.L113:
  b .L54
.L114:
  mov x0, #1
  mov x3, x0
.L115:
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L116:
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
.L117:
  str x23, [sp, #304]
.L118:
  str x27, [sp, #312]
.L119:
  str x22, [sp, #320]
.L120:
  str x26, [sp, #328]
.L121:
  str x25, [sp, #336]
.L122:
  str x24, [sp, #344]
.L123:
  str d12, [sp, #352]
.L124:
  str d11, [sp, #360]
.L125:
  str d10, [sp, #368]
.L126:
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
  ldr x9, [sp, #328]
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
  ldr x9, [sp, #336]
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
  ldr x9, [sp, #344]
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
  ldr d0, [sp, #352]
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
  ldr d0, [sp, #360]
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
  ldr d0, [sp, #368]
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
  ldr x23, [sp, #376]
  ldr x27, [sp, #384]
  ldr x22, [sp, #392]
  ldr x26, [sp, #400]
  ldr x25, [sp, #408]
  ldr x24, [sp, #416]
  ldr x28, [sp, #424]
  ldr x21, [sp, #432]
  ldr x20, [sp, #440]
  ldr x19, [sp, #448]
  ldr d12, [sp, #456]
  ldr d11, [sp, #464]
  ldr d10, [sp, #472]
  ldr d13, [sp, #480]
  ldr d9, [sp, #488]
  ldr d8, [sp, #496]
  ldr x29, [sp, #512]
  ldr x30, [sp, #520]
  add sp, sp, #528
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
