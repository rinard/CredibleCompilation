.global _main
.align 2

_main:
  sub sp, sp, #368
  str x30, [sp, #360]
  str x29, [sp, #352]
  add x29, sp, #352

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
  fmov d0, x0
  str d0, [sp, #32]
.L4:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #40]
.L5:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #48]
.L6:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L7:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L8:
  ldr d1, [sp, #56]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L9:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #64]
.L10:
  ldr d1, [sp, #64]
  ldr d2, [sp, #32]
  fmul d0, d1, d2
  str d0, [sp, #48]
.L11:
  mov x0, #1
  str x0, [sp, #16]
.L12:
  mov x0, #4096
  str x0, [sp, #72]
.L13:
  ldr x1, [sp, #16]
  ldr x2, [sp, #72]
  cmp x1, x2
  b.gt .L27
.L14:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #80]
.L15:
  ldr d1, [sp, #80]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #88]
.L16:
  ldr d1, [sp, #88]
  ldr d2, [sp, #40]
  fmul d0, d1, d2
  str d0, [sp, #96]
.L17:
  ldr d1, [sp, #96]
  ldr d2, [sp, #32]
  fadd d0, d1, d2
  str d0, [sp, #40]
.L18:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #104]
.L19:
  ldr d1, [sp, #104]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L20:
  ldr d1, [sp, #40]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #112]
.L21:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #120]
.L22:
  ldr d1, [sp, #112]
  ldr d2, [sp, #120]
  fmul d0, d1, d2
  str d0, [sp, #128]
.L23:
  ldr x1, [sp, #16]
  ldr d0, [sp, #128]
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L24:
  mov x0, #1
  str x0, [sp, #136]
.L25:
  ldr x1, [sp, #16]
  ldr x2, [sp, #136]
  add x0, x1, x2
  str x0, [sp, #16]
.L26:
  b .L12
.L27:
  mov x0, #1
  str x0, [sp, #24]
.L28:
  movz x0, #28488
  movk x0, #42, lsl #16
  str x0, [sp, #144]
.L29:
  ldr x1, [sp, #24]
  ldr x2, [sp, #144]
  cmp x1, x2
  b.gt .L69
.L30:
  mov x0, #1
  str x0, [sp, #8]
.L31:
  mov x0, #1001
  str x0, [sp, #152]
.L32:
  ldr x1, [sp, #8]
  ldr x2, [sp, #152]
  cmp x1, x2
  b.gt .L38
.L33:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #160]
.L34:
  ldr x1, [sp, #8]
  ldr d0, [sp, #160]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L35:
  mov x0, #1
  str x0, [sp, #168]
.L36:
  ldr x1, [sp, #8]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #8]
.L37:
  b .L31
.L38:
  mov x0, #1
  str x0, [sp, #176]
.L39:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d0, x0
  str d0, [sp, #184]
.L40:
  ldr x1, [sp, #176]
  ldr d0, [sp, #184]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L41:
  mov x0, #2
  str x0, [sp, #8]
.L42:
  mov x0, #64
  str x0, [sp, #192]
.L43:
  ldr x1, [sp, #8]
  ldr x2, [sp, #192]
  cmp x1, x2
  b.gt .L66
.L44:
  mov x0, #1
  str x0, [sp, #16]
.L45:
  mov x0, #1
  str x0, [sp, #200]
.L46:
  ldr x1, [sp, #8]
  ldr x2, [sp, #200]
  sub x0, x1, x2
  str x0, [sp, #208]
.L47:
  ldr x1, [sp, #16]
  ldr x2, [sp, #208]
  cmp x1, x2
  b.gt .L63
.L48:
  ldr x1, [sp, #8]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #216]
.L49:
  mov x0, #1
  str x0, [sp, #224]
.L50:
  ldr x1, [sp, #8]
  ldr x2, [sp, #224]
  sub x0, x1, x2
  str x0, [sp, #232]
.L51:
  mov x0, #64
  str x0, [sp, #240]
.L52:
  ldr x1, [sp, #232]
  ldr x2, [sp, #240]
  mul x0, x1, x2
  str x0, [sp, #248]
.L53:
  ldr x1, [sp, #248]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #256]
.L54:
  ldr x1, [sp, #256]
  mov x0, #4097
  cmp x1, x0
  b.hs .Lbounds_err
  adrp x0, _arr_b@PAGE
  add x0, x0, _arr_b@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #264]
.L55:
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  sub x0, x1, x2
  str x0, [sp, #272]
.L56:
  ldr x1, [sp, #272]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #280]
.L57:
  ldr d1, [sp, #264]
  ldr d2, [sp, #280]
  fmul d0, d1, d2
  str d0, [sp, #288]
.L58:
  ldr d1, [sp, #216]
  ldr d2, [sp, #288]
  fadd d0, d1, d2
  str d0, [sp, #296]
.L59:
  ldr x1, [sp, #8]
  ldr d0, [sp, #296]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L60:
  mov x0, #1
  str x0, [sp, #304]
.L61:
  ldr x1, [sp, #16]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #16]
.L62:
  b .L45
.L63:
  mov x0, #1
  str x0, [sp, #312]
.L64:
  ldr x1, [sp, #8]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #8]
.L65:
  b .L42
.L66:
  mov x0, #1
  str x0, [sp, #320]
.L67:
  ldr x1, [sp, #24]
  ldr x2, [sp, #320]
  add x0, x1, x2
  str x0, [sp, #24]
.L68:
  b .L28
.L69:
  mov x0, #64
  str x0, [sp, #328]
.L70:
  ldr x1, [sp, #328]
  adrp x0, _arr_w@PAGE
  add x0, x0, _arr_w@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #336]
.L71:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #336]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_71@PAGE
  add x0, x0, .Lfmt_print_71@PAGEOFF
  bl _printf
  add sp, sp, #16
.L72:
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
  // print k
  ldr x9, [sp, #16]
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
  ldr x9, [sp, #24]
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
  ldr d0, [sp, #32]
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
  ldr d0, [sp, #40]
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
  ldr d0, [sp, #48]
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
  ldr x29, [sp, #352]
  ldr x30, [sp, #360]
  add sp, sp, #368
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

.Lfmt_print_71:
  .asciz "%f\n"

.Lname_i:
  .asciz "i"
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
.global _arr_b
.align 3
_arr_b:
  .space 32776
.global _arr_w
.align 3
_arr_w:
  .space 8016
