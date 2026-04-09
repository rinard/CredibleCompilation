.global _main
.align 2

_main:
  sub sp, sp, #128
  str x30, [sp, #120]
  str x29, [sp, #112]
  add x29, sp, #112

  // Initialize all variables to 0
  mov x0, #0

  mov x5, #0
  mov x6, #0
  mov x4, #0
  fmov d5, xzr
  fmov d4, xzr
  mov x3, #0
  fmov d3, xzr
  fmov d2, xzr
  str x0, [sp, #72]
  str x0, [sp, #80]
  str x0, [sp, #88]
  str x0, [sp, #96]
  str x0, [sp, #104]

.L0:
  mov x5, #0
.L1:
  mov x6, #0
.L2:
  mov x4, #0
.L3:
  mov x0, #0
  fmov d5, x0
.L4:
  mov x0, #0
  fmov d4, x0
.L5:
  mov x5, #0
.L6:
  mov x3, #1024
.L7:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L17
.L8:
  mov x3, #1024
.L9:
  mov x1, x3
  mov x2, x5
  sub x0, x1, x2
  mov x3, x0
.L10:
  mov x0, x3
  scvtf d0, x0
  fmov d3, d0
.L11:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d2, x0
.L12:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L13:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L14:
  mov x3, #1
.L15:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L16:
  b .L6
.L17:
  mov x4, #0
.L18:
  mov x3, #10000
.L19:
  mov x1, x4
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L39
.L20:
  mov x6, #0
.L21:
  mov x3, #0
.L22:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L23:
  fmov d5, d2
.L24:
  mov x5, #1
.L25:
  mov x3, #1024
.L26:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L36
.L27:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L28:
  fmov d4, d2
.L29:
  fmov d1, d4
  fmov d2, d5
  fcmp d1, d2
  cset w0, mi
  cbnz w0, .L31
.L30:
  b .L33
.L31:
  mov x6, x5
.L32:
  fmov d5, d4
.L33:
  mov x3, #1
.L34:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L35:
  b .L25
.L36:
  mov x3, #1
.L37:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x4, x0
.L38:
  b .L18
.L39:
  str x5, [sp, #72]
.L40:
  str x6, [sp, #80]
.L41:
  str x4, [sp, #88]
.L42:
  str d5, [sp, #96]
.L43:
  str d4, [sp, #104]
.L44:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print k
  ldr x9, [sp, #72]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print m
  ldr x9, [sp, #80]
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
  ldr x9, [sp, #88]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print xm (float)
  ldr d0, [sp, #96]
  sub sp, sp, #32
  adrp x8, .Lname_xm@PAGE
  add x8, x8, .Lname_xm@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print xk (float)
  ldr d0, [sp, #104]
  sub sp, sp, #32
  adrp x8, .Lname_xk@PAGE
  add x8, x8, .Lname_xk@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #112]
  ldr x30, [sp, #120]
  add sp, sp, #128
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
.Lname_m:
  .asciz "m"
.Lname_rep:
  .asciz "rep"
.Lname_xm:
  .asciz "xm"
.Lname_xk:
  .asciz "xk"

.section __DATA,__data
.global _arr_x
.align 3
_arr_x:
  .space 8192
