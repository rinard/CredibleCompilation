.global _main
.align 2

_main:
  sub sp, sp, #432
  str x30, [sp, #424]
  str x29, [sp, #416]
  add x29, sp, #416

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
  str x0, [sp, #88]
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]
  str x0, [sp, #120]
  str x0, [sp, #128]
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

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #24]
.L3:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #32]
.L4:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #40]
.L5:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #24]
.L6:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L7:
  ldr d1, [sp, #48]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L8:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L9:
  ldr d1, [sp, #56]
  ldr d2, [sp, #24]
  fmul d0, d1, d2
  str d0, [sp, #40]
.L10:
  mov x0, #1
  str x0, [sp, #8]
.L11:
  mov x0, #1001
  str x0, [sp, #64]
.L12:
  ldr x1, [sp, #8]
  ldr x2, [sp, #64]
  cmp x1, x2
  b.gt .L26
.L13:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L14:
  ldr d1, [sp, #72]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #80]
.L15:
  ldr d1, [sp, #80]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #88]
.L16:
  ldr d1, [sp, #88]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L17:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #96]
.L18:
  ldr d1, [sp, #96]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #24]
.L19:
  ldr d1, [sp, #32]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #104]
.L20:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #112]
.L21:
  ldr d1, [sp, #104]
  ldr d2, [sp, #112]
  fmul d0, d1, d2
  str d0, [sp, #120]
.L22:
  ldr x1, [sp, #8]
  ldr d0, [sp, #120]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L23:
  mov x0, #1
  str x0, [sp, #128]
.L24:
  ldr x1, [sp, #8]
  ldr x2, [sp, #128]
  add x0, x1, x2
  str x0, [sp, #8]
.L25:
  b .L11
.L26:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #24]
.L27:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #136]
.L28:
  ldr d1, [sp, #136]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L29:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #144]
.L30:
  ldr d1, [sp, #144]
  ldr d2, [sp, #24]
  fmul d0, d1, d2
  str d0, [sp, #40]
.L31:
  mov x0, #1
  str x0, [sp, #8]
.L32:
  mov x0, #1001
  str x0, [sp, #152]
.L33:
  ldr x1, [sp, #8]
  ldr x2, [sp, #152]
  cmp x1, x2
  b.gt .L47
.L34:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #160]
.L35:
  ldr d1, [sp, #160]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #168]
.L36:
  ldr d1, [sp, #168]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #176]
.L37:
  ldr d1, [sp, #176]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L38:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #184]
.L39:
  ldr d1, [sp, #184]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #24]
.L40:
  ldr d1, [sp, #32]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #200]
.L42:
  ldr d1, [sp, #192]
  ldr d2, [sp, #200]
  fmul d0, d1, d2
  str d0, [sp, #208]
.L43:
  ldr x1, [sp, #8]
  ldr d0, [sp, #208]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L44:
  mov x0, #1
  str x0, [sp, #216]
.L45:
  ldr x1, [sp, #8]
  ldr x2, [sp, #216]
  add x0, x1, x2
  str x0, [sp, #8]
.L46:
  b .L32
.L47:
  mov x0, #1
  str x0, [sp, #16]
.L48:
  movz x0, #36752
  movk x0, #118, lsl #16
  str x0, [sp, #224]
.L49:
  ldr x1, [sp, #16]
  ldr x2, [sp, #224]
  cmp x1, x2
  b.gt .L88
.L50:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #24]
.L51:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #232]
.L52:
  ldr d1, [sp, #232]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L53:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #240]
.L54:
  ldr d1, [sp, #240]
  ldr d2, [sp, #24]
  fmul d0, d1, d2
  str d0, [sp, #40]
.L55:
  mov x0, #1
  str x0, [sp, #8]
.L56:
  mov x0, #1001
  str x0, [sp, #248]
.L57:
  ldr x1, [sp, #8]
  ldr x2, [sp, #248]
  cmp x1, x2
  b.gt .L71
.L58:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #256]
.L59:
  ldr d1, [sp, #256]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #264]
.L60:
  ldr d1, [sp, #264]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #272]
.L61:
  ldr d1, [sp, #272]
  ldr d2, [sp, #24]
  fadd d0, d1, d2
  str d0, [sp, #32]
.L62:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #280]
.L63:
  ldr d1, [sp, #280]
  ldr d2, [sp, #24]
  fsub d0, d1, d2
  str d0, [sp, #24]
.L64:
  ldr d1, [sp, #32]
  ldr d2, [sp, #40]
  fsub d0, d1, d2
  str d0, [sp, #288]
.L65:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #296]
.L66:
  ldr d1, [sp, #288]
  ldr d2, [sp, #296]
  fmul d0, d1, d2
  str d0, [sp, #304]
.L67:
  ldr x1, [sp, #8]
  ldr d0, [sp, #304]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L68:
  mov x0, #1
  str x0, [sp, #312]
.L69:
  ldr x1, [sp, #8]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #8]
.L70:
  b .L56
.L71:
  mov x0, #2
  str x0, [sp, #8]
.L72:
  mov x0, #1001
  str x0, [sp, #320]
.L73:
  ldr x1, [sp, #8]
  ldr x2, [sp, #320]
  cmp x1, x2
  b.gt .L85
.L74:
  ldr x1, [sp, #8]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #328]
.L75:
  ldr x1, [sp, #8]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #336]
.L76:
  mov x0, #1
  str x0, [sp, #344]
.L77:
  ldr x1, [sp, #8]
  ldr x2, [sp, #344]
  sub x0, x1, x2
  str x0, [sp, #352]
.L78:
  ldr x1, [sp, #352]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #360]
.L79:
  ldr d1, [sp, #336]
  ldr d2, [sp, #360]
  fsub d0, d1, d2
  str d0, [sp, #368]
.L80:
  ldr d1, [sp, #328]
  ldr d2, [sp, #368]
  fmul d0, d1, d2
  str d0, [sp, #376]
.L81:
  ldr x1, [sp, #8]
  ldr d0, [sp, #376]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L82:
  mov x0, #1
  str x0, [sp, #384]
.L83:
  ldr x1, [sp, #8]
  ldr x2, [sp, #384]
  add x0, x1, x2
  str x0, [sp, #8]
.L84:
  b .L72
.L85:
  mov x0, #1
  str x0, [sp, #392]
.L86:
  ldr x1, [sp, #16]
  ldr x2, [sp, #392]
  add x0, x1, x2
  str x0, [sp, #16]
.L87:
  b .L48
.L88:
  mov x0, #501
  str x0, [sp, #400]
.L89:
  ldr x1, [sp, #400]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #408]
.L90:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #408]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_90@PAGE
  add x0, x0, .Lfmt_print_90@PAGEOFF
  bl _printf
  add sp, sp, #16
.L91:
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
  // print rep
  ldr x9, [sp, #16]
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
  ldr d0, [sp, #24]
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
  ldr d0, [sp, #32]
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
  ldr d0, [sp, #40]
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
  ldr x29, [sp, #416]
  ldr x30, [sp, #424]
  add sp, sp, #432
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

.Lfmt_print_90:
  .asciz "%f\n"

.Lname_i:
  .asciz "i"
.Lname_rep:
  .asciz "rep"
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
.global _arr_z
.align 3
_arr_z:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
