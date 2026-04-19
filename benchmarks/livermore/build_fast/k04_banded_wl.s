.global _main
.align 2

_main:
  sub sp, sp, #400
  str x30, [sp, #392]
  str x29, [sp, #384]
  add x29, sp, #384
  // Save callee-saved registers
  str x20, [sp, #320]
  str x19, [sp, #328]
  str d12, [sp, #336]
  str d11, [sp, #344]
  str d10, [sp, #352]
  str d9, [sp, #360]
  str d13, [sp, #368]
  str d8, [sp, #376]

  // Initialize all variables to 0
  mov x0, #0

  mov x15, #0
  mov x20, #0
  mov x19, #0
  mov x14, #0
  mov x13, #0
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
  mov x12, #0
  fmov d13, x0
  fmov d8, x0
  mov x11, #0
  fmov d7, x0
  mov x10, #0
  mov x9, #0
  mov x8, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
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
  mov x15, x0
.L1:
  mov x0, #0
  mov x20, x0
.L2:
  mov x0, #0
  mov x19, x0
.L3:
  mov x0, #0
  mov x14, x0
.L4:
  mov x0, #0
  mov x13, x0
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
  mov x15, x0
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
  cmp x15, x4
  b.gt .L29
.L21:
  fsub d3, d6, d11
.L22:
  fmadd d10, d3, d10, d11
.L23:
  fsub d11, d5, d11
.L24:
  fsub d3, d10, d9
.L25:
  fmul d3, d3, d4
.L26:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L27:
  add x15, x15, x3
.L28:
  b .L20
.L29:
  mov x0, #1001
  str x0, [sp, #128]
.L30:
  mov x0, #7
  str x0, [sp, #136]
.L31:
  mov x0, #994
  str x0, [sp, #144]
.L32:
  mov x0, #2
  str x0, [sp, #152]
.L33:
  mov x0, #497
  mov x14, x0
.L34:
  mov x0, #1
  mov x13, x0
.L35:
  mov x0, #11250
  mov x12, x0
.L36:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d13, x0
.L37:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d8, x0
.L38:
  mov x0, #1001
  mov x11, x0
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d7, x0
.L40:
  mov x0, #0
  fmov d6, x0
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d5, x0
.L42:
  mov x0, #1
  mov x10, x0
.L43:
  mov x0, #1001
  mov x9, x0
.L44:
  mov x0, #6
  mov x8, x0
.L45:
  mov x0, #1001
  mov x7, x0
.L46:
  mov x0, #1
  mov x6, x0
.L47:
  mov x0, #5
  mov x5, x0
.L48:
  mov x0, #5
  mov x4, x0
.L49:
  mov x0, #1
  mov x3, x0
.L50:
  cmp x13, x12
  b.gt .L84
.L51:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d11, x0
.L52:
  fadd d10, d13, d11
.L53:
  fmul d9, d8, d11
.L54:
  mov x0, #1
  mov x15, x0
.L55:
  cmp x15, x11
  b.gt .L64
.L56:
  fsub d3, d7, d11
.L57:
  fmadd d10, d3, d10, d11
.L58:
  fsub d11, d6, d11
.L59:
  fsub d3, d10, d9
.L60:
  fmul d3, d3, d5
.L61:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L62:
  add x15, x15, x10
.L63:
  b .L55
.L64:
  mov x0, #7
  mov x15, x0
.L65:
  cmp x15, x9
  b.gt .L82
.L66:
  sub x19, x15, x8
.L67:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x15, lsl #3]
.L68:
  fmov d12, d3
.L69:
  mov x0, #5
  mov x20, x0
.L70:
  cmp x20, x7
  b.gt .L77
.L71:
  cmp x19, #1202
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d4, [x0, x19, lsl #3]
.L72:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d3, [x0, x20, lsl #3]
.L73:
  fmsub d12, d4, d3, d12
.L74:
  add x19, x19, x6
.L75:
  add x20, x20, x5
.L76:
  b .L70
.L77:
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d3, [x0, x4, lsl #3]
.L78:
  fmul d3, d3, d12
.L79:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d3, [x0, x15, lsl #3]
.L80:
  add x15, x15, x14
.L81:
  b .L65
.L82:
  add x13, x13, x3
.L83:
  b .L50
.L84:
  mov x0, #7
  mov x3, x0
.L85:
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d3, [x0, x3, lsl #3]
.L86:
  str x15, [sp, #8]
  str x14, [sp, #32]
  str x13, [sp, #40]
  str d3, [sp, #80]
  str x4, [sp, #88]
  str d6, [sp, #96]
  str d5, [sp, #104]
  str d4, [sp, #112]
  str x3, [sp, #120]
  str x12, [sp, #160]
  str x11, [sp, #184]
  str d7, [sp, #192]
  str x10, [sp, #200]
  str x9, [sp, #208]
  str x8, [sp, #216]
  str x7, [sp, #224]
  str x6, [sp, #232]
  str x5, [sp, #240]
  // print "%f\n"
  sub sp, sp, #16
  fmov d0, d3
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_86@PAGE
  add x0, x0, .Lfmt_print_86@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr x15, [sp, #8]
  ldr x14, [sp, #32]
  ldr x13, [sp, #40]
  ldr d3, [sp, #80]
  ldr x4, [sp, #88]
  ldr d6, [sp, #96]
  ldr d5, [sp, #104]
  ldr d4, [sp, #112]
  ldr x3, [sp, #120]
  ldr x12, [sp, #160]
  ldr x11, [sp, #184]
  ldr d7, [sp, #192]
  ldr x10, [sp, #200]
  ldr x9, [sp, #208]
  ldr x8, [sp, #216]
  ldr x7, [sp, #224]
  ldr x6, [sp, #232]
  ldr x5, [sp, #240]
.L87:
  mov x0, x15
  str x0, [sp, #248]
.L88:
  mov x0, x20
  str x0, [sp, #256]
.L89:
  mov x0, x19
  str x0, [sp, #264]
.L90:
  mov x0, x14
  str x0, [sp, #272]
.L91:
  mov x0, x13
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
  adrp x1, .Lname_k@PAGE
  add x1, x1, .Lname_k@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j
  ldr x9, [sp, #256]
  sub sp, sp, #16
  adrp x1, .Lname_j@PAGE
  add x1, x1, .Lname_j@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print lw
  ldr x9, [sp, #264]
  sub sp, sp, #16
  adrp x1, .Lname_lw@PAGE
  add x1, x1, .Lname_lw@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print m
  ldr x9, [sp, #272]
  sub sp, sp, #16
  adrp x1, .Lname_m@PAGE
  add x1, x1, .Lname_m@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #280]
  sub sp, sp, #16
  adrp x1, .Lname_rep@PAGE
  add x1, x1, .Lname_rep@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print temp (float)
  ldr d0, [sp, #288]
  sub sp, sp, #32
  adrp x1, .Lname_temp@PAGE
  add x1, x1, .Lname_temp@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print fuzz (float)
  ldr d0, [sp, #296]
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
  ldr d0, [sp, #304]
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
  ldr d0, [sp, #312]
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
  ldr x20, [sp, #320]
  ldr x19, [sp, #328]
  ldr d12, [sp, #336]
  ldr d11, [sp, #344]
  ldr d10, [sp, #352]
  ldr d9, [sp, #360]
  ldr d13, [sp, #368]
  ldr d8, [sp, #376]
  ldr x29, [sp, #384]
  ldr x30, [sp, #392]
  add sp, sp, #400
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

.Lfmt_print_86:
  .asciz "%f\n"

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
