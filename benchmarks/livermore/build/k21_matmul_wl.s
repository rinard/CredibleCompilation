.global _main
.align 2

_main:
  sub sp, sp, #144
  str x30, [sp, #136]
  str x29, [sp, #128]
  add x29, sp, #128

  // Initialize all variables to 0
  mov x0, #0

  mov x5, #0
  mov x7, #0
  mov x6, #0
  mov x4, #0
  fmov d4, xzr
  mov x3, #0
  fmov d3, xzr
  fmov d2, xzr
  mov x9, #0
  str x0, [sp, #80]
  str x0, [sp, #88]
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]

.L0:
  mov x5, #0
.L1:
  mov x7, #0
.L2:
  mov x6, #0
.L3:
  mov x4, #0
.L4:
  mov x0, #0
  fmov d4, x0
.L5:
  mov x5, #0
.L6:
  mov x3, #32
.L7:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L35
.L8:
  mov x7, #0
.L9:
  mov x3, #32
.L10:
  mov x1, x7
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L32
.L11:
  mov x3, #32
.L12:
  mov x1, x5
  mov x2, x3
  mul x0, x1, x2
  mov x3, x0
.L13:
  mov x1, x3
  mov x2, x7
  add x0, x1, x2
  mov x4, x0
.L14:
  mov x1, x5
  mov x2, x7
  add x0, x1, x2
  mov x3, x0
.L15:
  mov x0, x3
  scvtf d0, x0
  fmov d3, d0
.L16:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d2, x0
.L17:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L18:
  mov x1, x4
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_a@PAGE
  add x8, x8, _arr_a@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L19:
  mov x3, #32
.L20:
  mov x1, x5
  mov x2, x3
  mul x0, x1, x2
  mov x3, x0
.L21:
  mov x1, x3
  mov x2, x7
  add x0, x1, x2
  mov x9, x0
.L22:
  mov x1, x5
  mov x2, x7
  sub x0, x1, x2
  mov x4, x0
.L23:
  mov x3, #32
.L24:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x3, x0
.L25:
  mov x0, x3
  scvtf d0, x0
  fmov d3, d0
.L26:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d2, x0
.L27:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L28:
  mov x1, x9
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_b@PAGE
  add x8, x8, _arr_b@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L29:
  mov x3, #1
.L30:
  mov x1, x7
  mov x2, x3
  add x0, x1, x2
  mov x7, x0
.L31:
  b .L9
.L32:
  mov x3, #1
.L33:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L34:
  b .L6
.L35:
  mov x4, #0
.L36:
  mov x3, #1000
.L37:
  mov x1, x4
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L74
.L38:
  mov x5, #0
.L39:
  mov x3, #32
.L40:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L71
.L41:
  mov x7, #0
.L42:
  mov x3, #32
.L43:
  mov x1, x7
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L68
.L44:
  mov x0, #0
  fmov d4, x0
.L45:
  mov x6, #0
.L46:
  mov x3, #32
.L47:
  mov x1, x6
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L61
.L48:
  mov x3, #32
.L49:
  mov x1, x5
  mov x2, x3
  mul x0, x1, x2
  mov x3, x0
.L50:
  mov x1, x3
  mov x2, x6
  add x0, x1, x2
  mov x3, x0
.L51:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_a@PAGE
  add x8, x8, _arr_a@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d3, d0
.L52:
  mov x3, #32
.L53:
  mov x1, x6
  mov x2, x3
  mul x0, x1, x2
  mov x3, x0
.L54:
  mov x1, x3
  mov x2, x7
  add x0, x1, x2
  mov x3, x0
.L55:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_b@PAGE
  add x8, x8, _arr_b@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L56:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L57:
  fmov d1, d4
  // __d2 already in d2
  fadd d0, d1, d2
  fmov d4, d0
.L58:
  mov x3, #1
.L59:
  mov x1, x6
  mov x2, x3
  add x0, x1, x2
  mov x6, x0
.L60:
  b .L46
.L61:
  mov x3, #32
.L62:
  mov x1, x5
  mov x2, x3
  mul x0, x1, x2
  mov x3, x0
.L63:
  mov x1, x3
  mov x2, x7
  add x0, x1, x2
  mov x3, x0
.L64:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d4
  fmov x2, d0
  adrp x8, _arr_c@PAGE
  add x8, x8, _arr_c@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L65:
  mov x3, #1
.L66:
  mov x1, x7
  mov x2, x3
  add x0, x1, x2
  mov x7, x0
.L67:
  b .L42
.L68:
  mov x3, #1
.L69:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L70:
  b .L39
.L71:
  mov x3, #1
.L72:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x4, x0
.L73:
  b .L36
.L74:
  str x5, [sp, #80]
.L75:
  str x7, [sp, #88]
.L76:
  str x6, [sp, #96]
.L77:
  str x4, [sp, #104]
.L78:
  str d4, [sp, #112]
.L79:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #80]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print j
  ldr x9, [sp, #88]
  sub sp, sp, #16
  adrp x8, .Lname_j@PAGE
  add x8, x8, .Lname_j@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print k
  ldr x9, [sp, #96]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print rep
  ldr x9, [sp, #104]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print s (float)
  ldr d0, [sp, #112]
  sub sp, sp, #32
  adrp x8, .Lname_s@PAGE
  add x8, x8, .Lname_s@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #128]
  ldr x30, [sp, #136]
  add sp, sp, #144
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
.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_rep:
  .asciz "rep"
.Lname_s:
  .asciz "s"

.section __DATA,__data
.global _arr_a
.align 3
_arr_a:
  .space 8192
.global _arr_b
.align 3
_arr_b:
  .space 8192
.global _arr_c
.align 3
_arr_c:
  .space 8192
