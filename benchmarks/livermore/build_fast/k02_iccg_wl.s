.global _main
.align 2

_main:
  sub sp, sp, #512
  str x30, [sp, #504]
  str x29, [sp, #496]
  add x29, sp, #496
  // Save callee-saved registers
  str x22, [sp, #376]
  str x26, [sp, #384]
  str x21, [sp, #392]
  str x25, [sp, #400]
  str x24, [sp, #408]
  str x23, [sp, #416]
  str x27, [sp, #424]
  str x20, [sp, #432]
  str x19, [sp, #440]
  str d12, [sp, #448]
  str d11, [sp, #456]
  str d10, [sp, #464]
  str d13, [sp, #472]
  str d9, [sp, #480]
  str d8, [sp, #488]

  // Initialize all variables to 0
  mov x0, #0

  mov x22, #0
  mov x26, #0
  mov x21, #0
  mov x25, #0
  mov x24, #0
  mov x23, #0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  mov x27, #0
  fmov d13, x0
  fmov d9, x0
  mov x20, #0
  fmov d8, x0
  fmov d7, x0
  mov x19, #0
  str x0, [sp, #184]
  str x0, [sp, #192]
  mov x15, #0
  mov x14, #0
  mov x13, #0
  str x0, [sp, #224]
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x8, #0
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
  mov x22, x0
.L1:
  mov x0, #0
  mov x26, x0
.L2:
  mov x0, #0
  mov x21, x0
.L3:
  mov x0, #0
  mov x25, x0
.L4:
  mov x0, #0
  mov x24, x0
.L5:
  mov x0, #0
  mov x23, x0
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
  mov x22, x0
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
  cmp x22, x4
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
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  str d3, [x0, x22, lsl #3]
.L27:
  add x22, x22, x3
.L28:
  b .L20
.L29:
  mov x0, #1
  mov x21, x0
.L30:
  mov x0, #11495
  mov x27, x0
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
  mov x20, x0
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
  mov x19, x0
.L38:
  mov x0, #2
  str x0, [sp, #184]
.L39:
  mov x0, #2
  str x0, [sp, #192]
.L40:
  mov x0, #1
  mov x15, x0
.L41:
  mov x0, #1
  mov x14, x0
.L42:
  mov x0, #1
  mov x13, x0
.L43:
  mov x0, #1
  str x0, [sp, #224]
.L44:
  mov x0, #2
  mov x12, x0
.L45:
  mov x0, #0
  mov x11, x0
.L46:
  mov x0, #2
  mov x10, x0
.L47:
  mov x0, #2
  mov x9, x0
.L48:
  mov x0, #1
  mov x8, x0
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
  cmp x21, x27
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
  mov x22, x0
.L59:
  cmp x22, x20
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
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x22, lsl #3]
.L66:
  add x22, x22, x19
.L67:
  b .L59
.L68:
  mov x0, #101
  mov x25, x0
.L69:
  mov x0, #0
  mov x23, x0
.L70:
  mov x0, #0
  mov x24, x0
.L71:
  mov x0, #101
  mov x23, x0
.L72:
  mov x0, #50
  mov x25, x0
.L73:
  mov x0, #101
  mov x26, x0
.L74:
  mov x0, #2
  mov x22, x0
.L75:
  cmp x22, x23
  b.gt .L90
.L76:
  add x26, x26, x15
.L77:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d5, [x0, x22, lsl #3]
.L78:
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d4, [x0, x22, lsl #3]
.L79:
  sub x3, x22, x14
.L80:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L81:
  fmsub d5, d4, d3, d5
.L82:
  add x3, x22, x13
.L83:
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L84:
  mov x0, x3
  mov x3, x0
.L85:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L86:
  fmsub d3, d4, d3, d5
.L87:
  cmp x26, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x26, lsl #3]
.L88:
  add x22, x22, x12
.L89:
  b .L75
.L90:
  cmp x11, x25
  b.ge .L112
.L91:
  mov x0, x23
  mov x24, x0
.L92:
  add x23, x23, x25
.L93:
  cbz x10, .Ldiv_by_zero
  sdiv x25, x25, x10
.L94:
  mov x0, x23
  mov x26, x0
.L95:
  add x22, x24, x9
.L96:
  cmp x22, x23
  b.gt .L111
.L97:
  add x26, x26, x8
.L98:
  cmp x22, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d5, [x0, x22, lsl #3]
.L99:
  cmp x22, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d4, [x0, x22, lsl #3]
.L100:
  sub x3, x22, x7
.L101:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L102:
  fmsub d5, d4, d3, d5
.L103:
  add x3, x22, x6
.L104:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d4, [x0, x3, lsl #3]
.L105:
  mov x0, x3
  mov x3, x0
.L106:
  cmp x3, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L107:
  fmsub d3, d4, d3, d5
.L108:
  cmp x26, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x26, lsl #3]
.L109:
  add x22, x22, x5
.L110:
  b .L96
.L111:
  b .L90
.L112:
  add x21, x21, x4
.L113:
  b .L54
.L114:
  mov x0, #1
  mov x3, x0
.L115:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L116:
  str d3, [sp, #80]
  str x4, [sp, #88]
  str d6, [sp, #96]
  str d5, [sp, #104]
  str d4, [sp, #112]
  str x3, [sp, #120]
  str d7, [sp, #168]
  str x15, [sp, #200]
  str x14, [sp, #208]
  str x13, [sp, #216]
  str x12, [sp, #232]
  str x11, [sp, #240]
  str x10, [sp, #248]
  str x9, [sp, #256]
  str x8, [sp, #264]
  str x7, [sp, #272]
  str x6, [sp, #280]
  str x5, [sp, #296]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_116@PAGE
  add x0, x0, .Lfmt_print_116@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d3, [sp, #80]
  ldr x4, [sp, #88]
  ldr d6, [sp, #96]
  ldr d5, [sp, #104]
  ldr d4, [sp, #112]
  ldr x3, [sp, #120]
  ldr d7, [sp, #168]
  ldr x15, [sp, #200]
  ldr x14, [sp, #208]
  ldr x13, [sp, #216]
  ldr x12, [sp, #232]
  ldr x11, [sp, #240]
  ldr x10, [sp, #248]
  ldr x9, [sp, #256]
  ldr x8, [sp, #264]
  ldr x7, [sp, #272]
  ldr x6, [sp, #280]
  ldr x5, [sp, #296]
.L117:
  mov x0, x22
  str x0, [sp, #304]
.L118:
  mov x0, x26
  str x0, [sp, #312]
.L119:
  mov x0, x21
  str x0, [sp, #320]
.L120:
  mov x0, x25
  str x0, [sp, #328]
.L121:
  mov x0, x24
  str x0, [sp, #336]
.L122:
  mov x0, x23
  str x0, [sp, #344]
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
  adrp x1, .Lname_k@PAGE
  add x1, x1, .Lname_k@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i
  ldr x9, [sp, #312]
  sub sp, sp, #16
  adrp x1, .Lname_i@PAGE
  add x1, x1, .Lname_i@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #320]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ii
  ldr x9, [sp, #328]
  sub sp, sp, #16
  adrp x1, .Lname_ii@PAGE
  add x1, x1, .Lname_ii@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ipnt
  ldr x9, [sp, #336]
  sub sp, sp, #16
  adrp x1, .Lname_ipnt@PAGE
  add x1, x1, .Lname_ipnt@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ipntp
  ldr x9, [sp, #344]
  sub sp, sp, #16
  adrp x1, .Lname_ipntp@PAGE
  add x1, x1, .Lname_ipntp@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #352]
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
  ldr d0, [sp, #360]
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
  ldr d0, [sp, #368]
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
  ldr x22, [sp, #376]
  ldr x26, [sp, #384]
  ldr x21, [sp, #392]
  ldr x25, [sp, #400]
  ldr x24, [sp, #408]
  ldr x23, [sp, #416]
  ldr x27, [sp, #424]
  ldr x20, [sp, #432]
  ldr x19, [sp, #440]
  ldr d12, [sp, #448]
  ldr d11, [sp, #456]
  ldr d10, [sp, #464]
  ldr d13, [sp, #472]
  ldr d9, [sp, #480]
  ldr d8, [sp, #488]
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

.Lfmt_print_116:
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
