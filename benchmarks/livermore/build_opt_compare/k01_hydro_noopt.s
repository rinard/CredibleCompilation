.global _main
.align 2

_main:
  sub sp, sp, #544
  str x30, [sp, #536]
  str x29, [sp, #528]
  add x29, sp, #528

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
  str x0, [sp, #416]
  str x0, [sp, #424]
  str x0, [sp, #432]
  str x0, [sp, #440]
  str x0, [sp, #448]
  str x0, [sp, #456]
  str x0, [sp, #464]
  str x0, [sp, #472]
  str x0, [sp, #480]
  str x0, [sp, #488]
  str x0, [sp, #496]
  str x0, [sp, #504]
  str x0, [sp, #512]
  str x0, [sp, #520]

.L0:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #8]
.L1:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #16]
.L2:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #24]
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
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #72]
.L10:
  ldr d1, [sp, #72]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #80]
.L12:
  ldr d1, [sp, #80]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L13:
  mov x0, #1
  str x0, [sp, #32]
.L14:
  mov x0, #39
  str x0, [sp, #88]
.L15:
  ldr x1, [sp, #32]
  ldr x2, [sp, #88]
  cmp x1, x2
  b.gt .L29
.L16:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #96]
.L17:
  ldr d1, [sp, #96]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #104]
.L18:
  ldr d1, [sp, #104]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #112]
.L19:
  ldr d1, [sp, #112]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L20:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #120]
.L21:
  ldr d1, [sp, #120]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L22:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #128]
.L23:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #136]
.L24:
  ldr d1, [sp, #128]
  ldr d2, [sp, #136]
  fmul d0, d1, d2
  str d0, [sp, #144]
.L25:
  ldr x1, [sp, #32]
  ldr d0, [sp, #144]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L26:
  mov x0, #1
  str x0, [sp, #152]
.L27:
  ldr x1, [sp, #32]
  ldr x2, [sp, #152]
  add x0, x1, x2
  str x0, [sp, #32]
.L28:
  b .L14
.L29:
  mov x0, #28
  str x0, [sp, #160]
.L30:
  ldr x1, [sp, #160]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #168]
.L31:
  ldr x0, [sp, #168]
  str x0, [sp, #8]
.L32:
  mov x0, #30
  str x0, [sp, #176]
.L33:
  ldr x1, [sp, #176]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #184]
.L34:
  ldr x0, [sp, #184]
  str x0, [sp, #16]
.L35:
  mov x0, #36
  str x0, [sp, #192]
.L36:
  ldr x1, [sp, #192]
  adrp x0, _arr_spacer@PAGE
  add x0, x0, _arr_spacer@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #200]
.L37:
  ldr x0, [sp, #200]
  str x0, [sp, #24]
.L38:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L39:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #208]
.L40:
  ldr d1, [sp, #208]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L41:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #216]
.L42:
  ldr d1, [sp, #216]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L43:
  mov x0, #1
  str x0, [sp, #32]
.L44:
  mov x0, #1001
  str x0, [sp, #224]
.L45:
  ldr x1, [sp, #32]
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
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #240]
.L48:
  ldr d1, [sp, #240]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #248]
.L49:
  ldr d1, [sp, #248]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L50:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #256]
.L51:
  ldr d1, [sp, #256]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L52:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
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
  ldr x1, [sp, #32]
  ldr d0, [sp, #280]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L56:
  mov x0, #1
  str x0, [sp, #288]
.L57:
  ldr x1, [sp, #32]
  ldr x2, [sp, #288]
  add x0, x1, x2
  str x0, [sp, #32]
.L58:
  b .L44
.L59:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L60:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #296]
.L61:
  ldr d1, [sp, #296]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L62:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #304]
.L63:
  ldr d1, [sp, #304]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L64:
  mov x0, #1
  str x0, [sp, #32]
.L65:
  mov x0, #1012
  str x0, [sp, #312]
.L66:
  ldr x1, [sp, #32]
  ldr x2, [sp, #312]
  cmp x1, x2
  b.gt .L80
.L67:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #320]
.L68:
  ldr d1, [sp, #320]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #328]
.L69:
  ldr d1, [sp, #328]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #336]
.L70:
  ldr d1, [sp, #336]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L71:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #344]
.L72:
  ldr d1, [sp, #344]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L73:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #352]
.L74:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #360]
.L75:
  ldr d1, [sp, #352]
  ldr d2, [sp, #360]
  fmul d0, d1, d2
  str d0, [sp, #368]
.L76:
  ldr x1, [sp, #32]
  ldr d0, [sp, #368]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L77:
  mov x0, #1
  str x0, [sp, #376]
.L78:
  ldr x1, [sp, #32]
  ldr x2, [sp, #376]
  add x0, x1, x2
  str x0, [sp, #32]
.L79:
  b .L65
.L80:
  mov x0, #1
  str x0, [sp, #40]
.L81:
  movz x0, #63672
  movk x0, #398, lsl #16
  str x0, [sp, #384]
.L82:
  ldr x1, [sp, #40]
  ldr x2, [sp, #384]
  cmp x1, x2
  b.gt .L105
.L83:
  mov x0, #1
  str x0, [sp, #32]
.L84:
  mov x0, #1001
  str x0, [sp, #392]
.L85:
  ldr x1, [sp, #32]
  ldr x2, [sp, #392]
  cmp x1, x2
  b.gt .L102
.L86:
  ldr x1, [sp, #32]
  adrp x0, _arr_y@PAGE
  add x0, x0, _arr_y@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #400]
.L87:
  mov x0, #10
  str x0, [sp, #408]
.L88:
  ldr x1, [sp, #32]
  ldr x2, [sp, #408]
  add x0, x1, x2
  str x0, [sp, #416]
.L89:
  ldr x1, [sp, #416]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #424]
.L90:
  ldr d1, [sp, #16]
  ldr d2, [sp, #424]
  fmul d0, d1, d2
  str d0, [sp, #432]
.L91:
  mov x0, #11
  str x0, [sp, #440]
.L92:
  ldr x1, [sp, #32]
  ldr x2, [sp, #440]
  add x0, x1, x2
  str x0, [sp, #448]
.L93:
  ldr x1, [sp, #448]
  adrp x0, _arr_z@PAGE
  add x0, x0, _arr_z@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #456]
.L94:
  ldr d1, [sp, #24]
  ldr d2, [sp, #456]
  fmul d0, d1, d2
  str d0, [sp, #464]
.L95:
  ldr d1, [sp, #432]
  ldr d2, [sp, #464]
  fadd d0, d1, d2
  str d0, [sp, #472]
.L96:
  ldr d1, [sp, #400]
  ldr d2, [sp, #472]
  fmul d0, d1, d2
  str d0, [sp, #480]
.L97:
  ldr d1, [sp, #8]
  ldr d2, [sp, #480]
  fadd d0, d1, d2
  str d0, [sp, #488]
.L98:
  ldr x1, [sp, #32]
  ldr d0, [sp, #488]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L99:
  mov x0, #1
  str x0, [sp, #496]
.L100:
  ldr x1, [sp, #32]
  ldr x2, [sp, #496]
  add x0, x1, x2
  str x0, [sp, #32]
.L101:
  b .L84
.L102:
  mov x0, #1
  str x0, [sp, #504]
.L103:
  ldr x1, [sp, #40]
  ldr x2, [sp, #504]
  add x0, x1, x2
  str x0, [sp, #40]
.L104:
  b .L81
.L105:
  mov x0, #1
  str x0, [sp, #512]
.L106:
  ldr x1, [sp, #512]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #520]
.L107:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #520]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_107@PAGE
  add x0, x0, .Lfmt_print_107@PAGEOFF
  bl _printf
  add sp, sp, #16
.L108:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print q (float)
  ldr d0, [sp, #8]
  sub sp, sp, #32
  adrp x1, .Lname_q@PAGE
  add x1, x1, .Lname_q@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print r (float)
  ldr d0, [sp, #16]
  sub sp, sp, #32
  adrp x1, .Lname_r@PAGE
  add x1, x1, .Lname_r@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #24]
  sub sp, sp, #32
  adrp x1, .Lname_t@PAGE
  add x1, x1, .Lname_t@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print k
  ldr x9, [sp, #32]
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
  // print fuzz (float)
  ldr d0, [sp, #48]
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
  ldr d0, [sp, #56]
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
  ldr d0, [sp, #64]
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
  ldr x29, [sp, #528]
  ldr x30, [sp, #536]
  add sp, sp, #544
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

.Lfmt_print_107:
  .asciz "%f\n"

.Lname_q:
  .asciz "q"
.Lname_r:
  .asciz "r"
.Lname_t:
  .asciz "t"
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
.global _arr_spacer
.align 3
_arr_spacer:
  .space 320
.global _arr_y
.align 3
_arr_y:
  .space 8016
.global _arr_z
.align 3
_arr_z:
  .space 8104
.global _arr_x
.align 3
_arr_x:
  .space 8016
