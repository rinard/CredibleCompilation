.global _main
.align 2

_main:
  sub sp, sp, #288
  str x30, [sp, #280]
  str x29, [sp, #272]
  add x29, sp, #272
  // Save callee-saved registers
  str x19, [sp, #240]
  str d8, [sp, #248]
  str d10, [sp, #256]
  str d9, [sp, #264]

  // Initialize all variables to 0
  mov x0, #0

  mov x15, #0
  mov x19, #0
  mov x13, #0
  fmov d8, x0
  mov x14, #0
  fmov d7, x0
  fmov d6, x0
  fmov d5, x0
  fmov d3, x0
  mov x4, #0
  fmov d10, x0
  fmov d9, x0
  fmov d4, x0
  mov x3, #0
  mov x12, #0
  mov x11, #0
  mov x10, #0
  mov x9, #0
  mov x7, #0
  mov x6, #0
  mov x5, #0
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  str x0, [sp, #200]
  str x0, [sp, #208]
  str x0, [sp, #216]
  str x0, [sp, #224]
  str x0, [sp, #232]

.L0:
  mov x0, #0
  mov x15, x0
.L1:
  mov x0, #0
  mov x19, x0
.L2:
  mov x0, #0
  mov x13, x0
.L3:
  mov x0, #0
  fmov d8, x0
.L4:
  mov x0, #0
  mov x14, x0
.L5:
  mov x0, #0
  fmov d7, x0
.L6:
  mov x0, #0
  fmov d6, x0
.L7:
  mov x0, #0
  fmov d5, x0
.L8:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L9:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L10:
  fadd d6, d3, d7
.L11:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L12:
  fmul d5, d3, d7
.L13:
  mov x0, #1
  mov x15, x0
.L14:
  mov x0, #101
  mov x4, x0
.L15:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L16:
  mov x0, #0
  fmov d9, x0
.L17:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L18:
  mov x0, #1
  mov x3, x0
.L19:
  cmp x15, x4
  b.gt .L28
.L20:
  fsub d3, d10, d7
.L21:
  fmadd d6, d3, d6, d7
.L22:
  fsub d7, d9, d7
.L23:
  fsub d3, d6, d5
.L24:
  fmul d3, d3, d4
.L25:
  adrp x8, _arr_sa@PAGE
  add x8, x8, _arr_sa@PAGEOFF
  str d3, [x8, x15, lsl #3]
.L26:
  add x15, x15, x3
.L27:
  b .L19
.L28:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d7, x0
.L29:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d3, x0
.L30:
  fadd d6, d3, d7
.L31:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d3, x0
.L32:
  fmul d5, d3, d7
.L33:
  mov x0, #1
  mov x15, x0
.L34:
  mov x0, #101
  mov x4, x0
.L35:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d10, x0
.L36:
  mov x0, #0
  fmov d9, x0
.L37:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d4, x0
.L38:
  mov x0, #1
  mov x3, x0
.L39:
  cmp x15, x4
  b.gt .L48
.L40:
  fsub d3, d10, d7
.L41:
  fmadd d6, d3, d6, d7
.L42:
  fsub d7, d9, d7
.L43:
  fsub d3, d6, d5
.L44:
  fmul d3, d3, d4
.L45:
  adrp x8, _arr_sb@PAGE
  add x8, x8, _arr_sb@PAGEOFF
  str d3, [x8, x15, lsl #3]
.L46:
  add x15, x15, x3
.L47:
  b .L39
.L48:
  mov x0, #1
  mov x15, x0
.L49:
  mov x0, #1001
  mov x4, x0
.L50:
  mov x0, #0
  fmov d3, x0
.L51:
  mov x0, #1
  mov x3, x0
.L52:
  cmp x15, x4
  b.gt .L56
.L53:
  adrp x8, _arr_b5@PAGE
  add x8, x8, _arr_b5@PAGEOFF
  str d3, [x8, x15, lsl #3]
.L54:
  add x15, x15, x3
.L55:
  b .L52
.L56:
  mov x0, #1
  mov x13, x0
.L57:
  movz x0, #6976
  movk x0, #459, lsl #16
  mov x12, x0
.L58:
  mov x0, #101
  mov x11, x0
.L59:
  mov x0, #1
  mov x10, x0
.L60:
  mov x0, #101
  mov x9, x0
.L61:
  mov x0, #101
  mov x7, x0
.L62:
  mov x0, #1
  mov x6, x0
.L63:
  mov x0, #1
  mov x5, x0
.L64:
  mov x0, #1
  mov x4, x0
.L65:
  cmp x13, x12
  b.gt .L95
.L66:
  movz x0, #0
  movk x0, #16352, lsl #48
  fmov d8, x0
.L67:
  mov x0, #1
  mov x15, x0
.L68:
  cmp x15, x11
  b.gt .L79
.L69:
  add x3, x15, x14
.L70:
  adrp x8, _arr_sa@PAGE
  add x8, x8, _arr_sa@PAGEOFF
  ldr d4, [x8, x15, lsl #3]
.L71:
  adrp x8, _arr_sb@PAGE
  add x8, x8, _arr_sb@PAGEOFF
  ldr d3, [x8, x15, lsl #3]
.L72:
  fmadd d3, d8, d3, d4
.L73:
  adrp x8, _arr_b5@PAGE
  add x8, x8, _arr_b5@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L74:
.L75:
  adrp x8, _arr_b5@PAGE
  add x8, x8, _arr_b5@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L76:
  fsub d8, d3, d8
.L77:
  add x15, x15, x10
.L78:
  b .L68
.L79:
  mov x0, #1
  mov x19, x0
.L80:
  cmp x19, x9
  b.gt .L93
.L81:
  sub x3, x7, x19
.L82:
  add x15, x3, x6
.L83:
  add x3, x15, x14
.L84:
  adrp x8, _arr_sa@PAGE
  add x8, x8, _arr_sa@PAGEOFF
  ldr d4, [x8, x15, lsl #3]
.L85:
  adrp x8, _arr_sb@PAGE
  add x8, x8, _arr_sb@PAGEOFF
  ldr d3, [x8, x15, lsl #3]
.L86:
  fmadd d3, d8, d3, d4
.L87:
  adrp x8, _arr_b5@PAGE
  add x8, x8, _arr_b5@PAGEOFF
  str d3, [x8, x3, lsl #3]
.L88:
  add x3, x15, x14
.L89:
  adrp x8, _arr_b5@PAGE
  add x8, x8, _arr_b5@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L90:
  fsub d8, d3, d8
.L91:
  add x19, x19, x5
.L92:
  b .L80
.L93:
  add x13, x13, x4
.L94:
  b .L65
.L95:
  mov x0, #51
  mov x3, x0
.L96:
  adrp x8, _arr_b5@PAGE
  add x8, x8, _arr_b5@PAGEOFF
  ldr d3, [x8, x3, lsl #3]
.L97:
  str d5, [sp, #64]
  str d6, [sp, #56]
  str d7, [sp, #48]
  str x14, [sp, #40]
  str x13, [sp, #24]
  str x15, [sp, #8]
  // printfloat __d3
  fmov d0, d3
  sub sp, sp, #16
  str d0, [sp]
  adrp x0, .Lfmt_printfloat@PAGE
  add x0, x0, .Lfmt_printfloat@PAGEOFF
  bl _printf
  add sp, sp, #16
  ldr d5, [sp, #64]
  ldr d6, [sp, #56]
  ldr d7, [sp, #48]
  ldr x14, [sp, #40]
  ldr x13, [sp, #24]
  ldr x15, [sp, #8]
.L98:
  str x15, [sp, #176]
.L99:
  str x19, [sp, #184]
.L100:
  str x13, [sp, #192]
.L101:
  str d8, [sp, #200]
.L102:
  str x14, [sp, #208]
.L103:
  str d7, [sp, #216]
.L104:
  str d6, [sp, #224]
.L105:
  str d5, [sp, #232]
.L106:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #176]
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
  ldr x9, [sp, #184]
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
  ldr x9, [sp, #192]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print stb5 (float)
  ldr d0, [sp, #200]
  sub sp, sp, #32
  adrp x8, .Lname_stb5@PAGE
  add x8, x8, .Lname_stb5@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print kb5i
  ldr x9, [sp, #208]
  sub sp, sp, #16
  adrp x8, .Lname_kb5i@PAGE
  add x8, x8, .Lname_kb5i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #216]
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
  ldr d0, [sp, #224]
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
  ldr d0, [sp, #232]
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
  ldr x19, [sp, #240]
  ldr d8, [sp, #248]
  ldr d10, [sp, #256]
  ldr d9, [sp, #264]
  ldr x29, [sp, #272]
  ldr x30, [sp, #280]
  add sp, sp, #288
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
