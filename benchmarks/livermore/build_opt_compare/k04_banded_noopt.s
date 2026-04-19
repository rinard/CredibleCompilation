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
  str x0, [sp, #24]
.L3:
  mov x0, #0
  str x0, [sp, #32]
.L4:
  mov x0, #0
  str x0, [sp, #40]
.L5:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #48]
.L6:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #56]
.L7:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #64]
.L8:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #72]
.L9:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L10:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #80]
.L11:
  ldr d1, [sp, #80]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L12:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #88]
.L13:
  ldr d1, [sp, #88]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #72]
.L14:
  mov x0, #1
  str x0, [sp, #8]
.L15:
  mov x0, #1001
  str x0, [sp, #96]
.L16:
  ldr x1, [sp, #8]
  ldr x2, [sp, #96]
  cmp x1, x2
  b.gt .L30
.L17:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #104]
.L18:
  ldr d1, [sp, #104]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #112]
.L19:
  ldr d1, [sp, #112]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #120]
.L20:
  ldr d1, [sp, #120]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L21:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #128]
.L22:
  ldr d1, [sp, #128]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #56]
.L23:
  ldr d1, [sp, #64]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #136]
.L24:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #144]
.L25:
  ldr d1, [sp, #136]
  ldr d2, [sp, #144]
  fmul d0, d1, d2
  str d0, [sp, #152]
.L26:
  ldr x1, [sp, #8]
  ldr d0, [sp, #152]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L27:
  mov x0, #1
  str x0, [sp, #160]
.L28:
  ldr x1, [sp, #8]
  ldr x2, [sp, #160]
  add x0, x1, x2
  str x0, [sp, #8]
.L29:
  b .L15
.L30:
  mov x0, #1001
  str x0, [sp, #168]
.L31:
  mov x0, #7
  str x0, [sp, #176]
.L32:
  ldr x1, [sp, #168]
  ldr x2, [sp, #176]
  sub x0, x1, x2
  str x0, [sp, #184]
.L33:
  mov x0, #2
  str x0, [sp, #192]
.L34:
  ldr x1, [sp, #184]
  ldr x2, [sp, #192]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  str x0, [sp, #32]
.L35:
  mov x0, #1
  str x0, [sp, #40]
.L36:
  movz x0, #43344
  movk x0, #171, lsl #16
  str x0, [sp, #200]
.L37:
  ldr x1, [sp, #40]
  ldr x2, [sp, #200]
  cmp x1, x2
  b.gt .L87
.L38:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #208]
.L40:
  ldr d1, [sp, #208]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #216]
.L42:
  ldr d1, [sp, #216]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #72]
.L43:
  mov x0, #1
  str x0, [sp, #8]
.L44:
  mov x0, #1001
  str x0, [sp, #224]
.L45:
  ldr x1, [sp, #8]
  ldr x2, [sp, #224]
  cmp x1, x2
  b.gt .L59
.L46:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #232]
.L47:
  ldr d1, [sp, #232]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #240]
.L48:
  ldr d1, [sp, #240]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #248]
.L49:
  ldr d1, [sp, #248]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L50:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #256]
.L51:
  ldr d1, [sp, #256]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #56]
.L52:
  ldr d1, [sp, #64]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #264]
.L53:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #272]
.L54:
  ldr d1, [sp, #264]
  ldr d2, [sp, #272]
  fmul d0, d1, d2
  str d0, [sp, #280]
.L55:
  ldr x1, [sp, #8]
  ldr d0, [sp, #280]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L56:
  mov x0, #1
  str x0, [sp, #288]
.L57:
  ldr x1, [sp, #8]
  ldr x2, [sp, #288]
  add x0, x1, x2
  str x0, [sp, #8]
.L58:
  b .L44
.L59:
  mov x0, #7
  str x0, [sp, #8]
.L60:
  mov x0, #1001
  str x0, [sp, #296]
.L61:
  ldr x1, [sp, #8]
  ldr x2, [sp, #296]
  cmp x1, x2
  b.gt .L84
.L62:
  mov x0, #6
  str x0, [sp, #304]
.L63:
  ldr x1, [sp, #8]
  ldr x2, [sp, #304]
  sub x0, x1, x2
  str x0, [sp, #24]
.L64:
  ldr x1, [sp, #8]
  cmp x1, #1202
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #312]
.L65:
  ldr x0, [sp, #312]
  str x0, [sp, #48]
.L66:
  mov x0, #5
  str x0, [sp, #16]
.L67:
  mov x0, #1001
  str x0, [sp, #320]
.L68:
  ldr x1, [sp, #16]
  ldr x2, [sp, #320]
  cmp x1, x2
  b.gt .L78
.L69:
  ldr x1, [sp, #24]
  cmp x1, #1202
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #328]
.L70:
  ldr x1, [sp, #16]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #336]
.L71:
  ldr d1, [sp, #328]
  ldr d2, [sp, #336]
  fmul d0, d1, d2
  str d0, [sp, #344]
.L72:
  ldr d1, [sp, #48]
  ldr d2, [sp, #344]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L73:
  mov x0, #1
  str x0, [sp, #352]
.L74:
  ldr x1, [sp, #24]
  ldr x2, [sp, #352]
  add x0, x1, x2
  str x0, [sp, #24]
.L75:
  mov x0, #5
  str x0, [sp, #360]
.L76:
  ldr x1, [sp, #16]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #16]
.L77:
  b .L67
.L78:
  mov x0, #5
  str x0, [sp, #368]
.L79:
  ldr x1, [sp, #368]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #376]
.L80:
  ldr d1, [sp, #376]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #384]
.L81:
  ldr x1, [sp, #8]
  cmp x1, #1202
  b.hs .Lbounds_err
  ldr d0, [sp, #384]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L82:
  ldr x1, [sp, #8]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #8]
.L83:
  b .L60
.L84:
  mov x0, #1
  str x0, [sp, #392]
.L85:
  ldr x1, [sp, #40]
  ldr x2, [sp, #392]
  add x0, x1, x2
  str x0, [sp, #40]
.L86:
  b .L36
.L87:
  mov x0, #7
  str x0, [sp, #400]
.L88:
  ldr x1, [sp, #400]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #408]
.L89:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #408]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_89@PAGE
  add x0, x0, .Lfmt_print_89@PAGEOFF
  bl _printf
  add sp, sp, #16
.L90:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #8]
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
  // print lw
  ldr x9, [sp, #24]
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
  ldr x9, [sp, #32]
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
  ldr x9, [sp, #40]
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
  ldr d0, [sp, #48]
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
  ldr d0, [sp, #56]
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
  ldr d0, [sp, #64]
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
  ldr d0, [sp, #72]
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

.Lfmt_print_89:
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
