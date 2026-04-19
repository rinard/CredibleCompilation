.global _main
.align 2

_main:
  sub sp, sp, #416
  str x30, [sp, #408]
  str x29, [sp, #400]
  add x29, sp, #400
  // Save callee-saved registers
  stp x19, x21, [sp, #320]
  str x20, [sp, #336]
  stp d12, d11, [sp, #352]
  stp d10, d9, [sp, #368]
  stp d8, d13, [sp, #384]

  // Initialize all variables to 0
  mov x0, #0

  mov x19, #0
  mov x21, #0
  mov x20, #0
  mov x15, #0
  mov x14, #0
  fmov d12, x0
  fmov d11, x0
  fmov d10, x0
  fmov d9, x0
  fmov d3, x0
  mov x4, #0
  fmov d6, x0
  fmov d5, x0
  fmov d4, x0
  mov x3, #0
  str x0, [sp, #128]
  str x0, [sp, #136]
  str x0, [sp, #144]
  str x0, [sp, #152]
  mov x13, #0
  fmov d8, x0
  fmov d7, x0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  fmov d13, x0
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]
  str x0, [sp, #272]
  str x0, [sp, #280]
  str x0, [sp, #288]
  str x0, [sp, #296]
  str x0, [sp, #304]
  str x0, [sp, #312]

.L0:
  mov x0, #0
  mov x19, x0
.L1:
  mov x0, #0
  mov x21, x0
.L2:
  mov x0, #0
  mov x20, x0
.L3:
  mov x0, #0
  mov x15, x0
.L4:
  mov x0, #0
  mov x14, x0
.L5:
  mov x0, #0
  fmov d12, x0
.L6:
  mov x0, #0
  fmov d11, x0
.L7:
  mov x0, #0
  fmov d10, x0
.L8:
  mov x0, #0
  fmov d9, x0
.L9:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L10:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L11:
  fadd d10, d3, d11
.L12:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L13:
  fmul d9, d3, d11
.L14:
  mov x0, #1
  mov x19, x0
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
  mov x1, x19
  mov x2, x4
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L30
.L21:
  fsub d3, d6, d11
.L22:
  fmul d3, d3, d10
.L23:
  fadd d10, d3, d11
.L24:
  fsub d11, d5, d11
.L25:
  fsub d3, d10, d9
.L26:
  fmul d3, d3, d4
.L27:
  mov x1, x19
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L28:
  add x19, x19, x3
.L29:
  b .L20
.L30:
  mov x0, #1001
  str x0, [sp, #128]
.L31:
  mov x0, #7
  str x0, [sp, #136]
.L32:
  mov x0, #994
  str x0, [sp, #144]
.L33:
  mov x0, #2
  str x0, [sp, #152]
.L34:
  mov x0, #497
  mov x15, x0
.L35:
  mov x0, #1
  mov x14, x0
.L36:
  movz x0, #43344
  movk x0, #171, lsl #16
  mov x13, x0
.L37:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d8, x0
.L38:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d7, x0
.L39:
  mov x0, #1001
  mov x12, x0
.L40:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d6, x0
.L41:
  mov x0, #0
  fmov d5, x0
.L42:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L43:
  mov x0, #1
  mov x11, x0
.L44:
  mov x0, #1001
  mov x10, x0
.L45:
  mov x0, #6
  mov x9, x0
.L46:
  mov x0, #1001
  mov x7, x0
.L47:
  mov x0, #1
  mov x6, x0
.L48:
  mov x0, #5
  mov x5, x0
.L49:
  mov x0, #5
  mov x4, x0
.L50:
  mov x0, #1
  mov x3, x0
.L51:
  mov x1, x14
  mov x2, x13
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L87
.L52:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L53:
  fadd d10, d8, d11
.L54:
  fmul d9, d7, d11
.L55:
  mov x0, #1
  mov x19, x0
.L56:
  mov x1, x19
  mov x2, x12
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L66
.L57:
  fsub d3, d6, d11
.L58:
  fmul d3, d3, d10
.L59:
  fadd d10, d3, d11
.L60:
  fsub d11, d5, d11
.L61:
  fsub d3, d10, d9
.L62:
  fmul d3, d3, d4
.L63:
  mov x1, x19
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L64:
  add x19, x19, x11
.L65:
  b .L56
.L66:
  mov x0, #7
  mov x19, x0
.L67:
  mov x1, x19
  mov x2, x10
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L85
.L68:
  sub x20, x19, x9
.L69:
  mov x1, x19
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L70:
  fmov d12, d3
.L71:
  mov x0, #5
  mov x21, x0
.L72:
  mov x1, x21
  mov x2, x7
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L80
.L73:
  mov x1, x20
  cmp x1, #1202
  cset w0, lt
  cbz x0, .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr d13, [x8, x1, lsl #3]
.L74:
  mov x1, x21
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L75:
  fmul d3, d13, d3
.L76:
  fsub d12, d12, d3
.L77:
  add x20, x20, x6
.L78:
  add x21, x21, x5
.L79:
  b .L72
.L80:
  mov x1, x4
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr d3, [x8, x1, lsl #3]
.L81:
  fmul d3, d3, d12
.L82:
  mov x1, x19
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str d3, [x8, x1, lsl #3]
.L83:
  add x19, x19, x15
.L84:
  b .L67
.L85:
  add x14, x14, x3
.L86:
  b .L51
.L87:
  mov x0, x19
  str x0, [sp, #248]
.L88:
  mov x0, x21
  str x0, [sp, #256]
.L89:
  mov x0, x20
  str x0, [sp, #264]
.L90:
  mov x0, x15
  str x0, [sp, #272]
.L91:
  mov x0, x14
  str x0, [sp, #280]
.L92:
  str d12, [sp, #288]
.L93:
  str d11, [sp, #296]
.L94:
  str d10, [sp, #304]
.L95:
  str d9, [sp, #312]
.L96:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #248]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j
  ldr x9, [sp, #256]
  sub sp, sp, #16
  adrp x8, .Lname_j@PAGE
  add x8, x8, .Lname_j@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print lw
  ldr x9, [sp, #264]
  sub sp, sp, #16
  adrp x8, .Lname_lw@PAGE
  add x8, x8, .Lname_lw@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print m
  ldr x9, [sp, #272]
  sub sp, sp, #16
  adrp x8, .Lname_m@PAGE
  add x8, x8, .Lname_m@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #280]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print temp (float)
  ldr d0, [sp, #288]
  sub sp, sp, #32
  adrp x8, .Lname_temp@PAGE
  add x8, x8, .Lname_temp@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #296]
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
  ldr d0, [sp, #304]
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
  ldr d0, [sp, #312]
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
  ldp x19, x21, [sp, #320]
  ldr x20, [sp, #336]
  ldp d12, d11, [sp, #352]
  ldp d10, d9, [sp, #368]
  ldp d8, d13, [sp, #384]
  ldr x29, [sp, #400]
  ldr x30, [sp, #408]
  add sp, sp, #416
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
.Lname_j:
  .asciz "j"
.Lname_lw:
  .asciz "lw"
.Lname_m:
  .asciz "m"
.Lname_rep:
  .asciz "rep"
.Lname_temp:
  .asciz "temp"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 9616
