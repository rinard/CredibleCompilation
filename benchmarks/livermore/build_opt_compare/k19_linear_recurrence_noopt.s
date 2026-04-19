.global _main
.align 2

_main:
  sub sp, sp, #496
  str x30, [sp, #488]
  str x29, [sp, #480]
  add x29, sp, #480

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
  str x0, [sp, #8]
.L14:
  mov x0, #101
  str x0, [sp, #88]
.L15:
  ldr x1, [sp, #8]
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
  ldr x1, [sp, #8]
  ldr d0, [sp, #144]
  adrp x0, _arr_sa@PAGE
  add x0, x0, _arr_sa@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L26:
  mov x0, #1
  str x0, [sp, #152]
.L27:
  ldr x1, [sp, #8]
  ldr x2, [sp, #152]
  add x0, x1, x2
  str x0, [sp, #8]
.L28:
  b .L14
.L29:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #48]
.L30:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #160]
.L31:
  ldr d1, [sp, #160]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L32:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #168]
.L33:
  ldr d1, [sp, #168]
  ldr d2, [sp, #48]
  fmul d0, d1, d2
  str d0, [sp, #64]
.L34:
  mov x0, #1
  str x0, [sp, #8]
.L35:
  mov x0, #101
  str x0, [sp, #176]
.L36:
  ldr x1, [sp, #8]
  ldr x2, [sp, #176]
  cmp x1, x2
  b.gt .L50
.L37:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #184]
.L38:
  ldr d1, [sp, #184]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #192]
.L39:
  ldr d1, [sp, #192]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #200]
.L40:
  ldr d1, [sp, #200]
  ldr d2, [sp, #48]
  fadd d0, d1, d2
  str d0, [sp, #56]
.L41:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #208]
.L42:
  ldr d1, [sp, #208]
  ldr d2, [sp, #48]
  fsub d0, d1, d2
  str d0, [sp, #48]
.L43:
  ldr d1, [sp, #56]
  ldr d2, [sp, #64]
  fsub d0, d1, d2
  str d0, [sp, #216]
.L44:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #224]
.L45:
  ldr d1, [sp, #216]
  ldr d2, [sp, #224]
  fmul d0, d1, d2
  str d0, [sp, #232]
.L46:
  ldr x1, [sp, #8]
  ldr d0, [sp, #232]
  adrp x0, _arr_sb@PAGE
  add x0, x0, _arr_sb@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L47:
  mov x0, #1
  str x0, [sp, #240]
.L48:
  ldr x1, [sp, #8]
  ldr x2, [sp, #240]
  add x0, x1, x2
  str x0, [sp, #8]
.L49:
  b .L35
.L50:
  mov x0, #1
  str x0, [sp, #8]
.L51:
  mov x0, #1001
  str x0, [sp, #248]
.L52:
  ldr x1, [sp, #8]
  ldr x2, [sp, #248]
  cmp x1, x2
  b.gt .L58
.L53:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #256]
.L54:
  ldr x1, [sp, #8]
  ldr d0, [sp, #256]
  adrp x0, _arr_b5@PAGE
  add x0, x0, _arr_b5@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L55:
  mov x0, #1
  str x0, [sp, #264]
.L56:
  ldr x1, [sp, #8]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #8]
.L57:
  b .L51
.L58:
  mov x0, #1
  str x0, [sp, #24]
.L59:
  movz x0, #6976
  movk x0, #459, lsl #16
  str x0, [sp, #272]
.L60:
  ldr x1, [sp, #24]
  ldr x2, [sp, #272]
  cmp x1, x2
  b.gt .L100
.L61:
  movz x0, #0
  movk x0, #16352, lsl #48
  fmov d0, x0
  str d0, [sp, #32]
.L62:
  mov x0, #0
  str x0, [sp, #40]
.L63:
  mov x0, #1
  str x0, [sp, #8]
.L64:
  mov x0, #101
  str x0, [sp, #280]
.L65:
  ldr x1, [sp, #8]
  ldr x2, [sp, #280]
  cmp x1, x2
  b.gt .L78
.L66:
  ldr x1, [sp, #8]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #288]
.L67:
  ldr x1, [sp, #8]
  adrp x0, _arr_sa@PAGE
  add x0, x0, _arr_sa@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #296]
.L68:
  ldr x1, [sp, #8]
  adrp x0, _arr_sb@PAGE
  add x0, x0, _arr_sb@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #304]
.L69:
  ldr d1, [sp, #32]
  ldr d2, [sp, #304]
  fmul d0, d1, d2
  str d0, [sp, #312]
.L70:
  ldr d1, [sp, #296]
  ldr d2, [sp, #312]
  fadd d0, d1, d2
  str d0, [sp, #320]
.L71:
  ldr x1, [sp, #288]
  ldr d0, [sp, #320]
  adrp x0, _arr_b5@PAGE
  add x0, x0, _arr_b5@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L72:
  ldr x1, [sp, #8]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #328]
.L73:
  ldr x1, [sp, #328]
  adrp x0, _arr_b5@PAGE
  add x0, x0, _arr_b5@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #336]
.L74:
  ldr d1, [sp, #336]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L75:
  mov x0, #1
  str x0, [sp, #344]
.L76:
  ldr x1, [sp, #8]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #8]
.L77:
  b .L64
.L78:
  mov x0, #1
  str x0, [sp, #16]
.L79:
  mov x0, #101
  str x0, [sp, #352]
.L80:
  ldr x1, [sp, #16]
  ldr x2, [sp, #352]
  cmp x1, x2
  b.gt .L97
.L81:
  mov x0, #101
  str x0, [sp, #360]
.L82:
  ldr x1, [sp, #360]
  ldr x2, [sp, #16]
  sub x0, x1, x2
  str x0, [sp, #368]
.L83:
  mov x0, #1
  str x0, [sp, #376]
.L84:
  ldr x1, [sp, #368]
  ldr x2, [sp, #376]
  add x0, x1, x2
  str x0, [sp, #8]
.L85:
  ldr x1, [sp, #8]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #384]
.L86:
  ldr x1, [sp, #8]
  adrp x0, _arr_sa@PAGE
  add x0, x0, _arr_sa@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #392]
.L87:
  ldr x1, [sp, #8]
  adrp x0, _arr_sb@PAGE
  add x0, x0, _arr_sb@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #400]
.L88:
  ldr d1, [sp, #32]
  ldr d2, [sp, #400]
  fmul d0, d1, d2
  str d0, [sp, #408]
.L89:
  ldr d1, [sp, #392]
  ldr d2, [sp, #408]
  fadd d0, d1, d2
  str d0, [sp, #416]
.L90:
  ldr x1, [sp, #384]
  ldr d0, [sp, #416]
  adrp x0, _arr_b5@PAGE
  add x0, x0, _arr_b5@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L91:
  ldr x1, [sp, #8]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #424]
.L92:
  ldr x1, [sp, #424]
  adrp x0, _arr_b5@PAGE
  add x0, x0, _arr_b5@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #432]
.L93:
  ldr d1, [sp, #432]
  ldr d2, [sp, #32]
  fsub d0, d1, d2
  str d0, [sp, #32]
.L94:
  mov x0, #1
  str x0, [sp, #440]
.L95:
  ldr x1, [sp, #16]
  ldr x2, [sp, #440]
  add x0, x1, x2
  str x0, [sp, #16]
.L96:
  b .L79
.L97:
  mov x0, #1
  str x0, [sp, #448]
.L98:
  ldr x1, [sp, #24]
  ldr x2, [sp, #448]
  add x0, x1, x2
  str x0, [sp, #24]
.L99:
  b .L59
.L100:
  mov x0, #51
  str x0, [sp, #456]
.L101:
  ldr x1, [sp, #456]
  adrp x0, _arr_b5@PAGE
  add x0, x0, _arr_b5@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #464]
.L102:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #464]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_102@PAGE
  add x0, x0, .Lfmt_print_102@PAGEOFF
  bl _printf
  add sp, sp, #16
.L103:
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
  // print i
  ldr x9, [sp, #16]
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
  // print stb5 (float)
  ldr d0, [sp, #32]
  sub sp, sp, #32
  adrp x1, .Lname_stb5@PAGE
  add x1, x1, .Lname_stb5@PAGEOFF
  str x1, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print kb5i
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x1, .Lname_kb5i@PAGE
  add x1, x1, .Lname_kb5i@PAGEOFF
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
  ldr x29, [sp, #480]
  ldr x30, [sp, #488]
  add sp, sp, #496
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

.Lfmt_print_102:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_i:
  .asciz "i"
.Lname_rep:
  .asciz "rep"
.Lname_stb5:
  .asciz "stb5"
.Lname_kb5i:
  .asciz "kb5i"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_sa
.align 3
_arr_sa:
  .space 816
.global _arr_sb
.align 3
_arr_sb:
  .space 816
.global _arr_b5
.align 3
_arr_b5:
  .space 8016
