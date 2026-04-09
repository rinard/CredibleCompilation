.global _main
.align 2

_main:
  sub sp, sp, #144
  str x30, [sp, #136]
  str x29, [sp, #128]
  add x29, sp, #128

  // Initialize all variables to 0
  mov x0, #0

  fmov d7, xzr
  fmov d6, xzr
  fmov d5, xzr
  mov x5, #0
  mov x4, #0
  mov x3, #0
  fmov d3, xzr
  fmov d2, xzr
  fmov d4, xzr
  str x0, [sp, #80]
  str x0, [sp, #88]
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]

.L0:
  mov x0, #0
  fmov d7, x0
.L1:
  mov x0, #0
  fmov d6, x0
.L2:
  mov x0, #0
  fmov d5, x0
.L3:
  mov x5, #0
.L4:
  mov x4, #0
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
  cbnz w0, .L21
.L8:
  mov x0, x5
  scvtf d0, x0
  fmov d3, d0
.L9:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d2, x0
.L10:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L11:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L12:
  mov x0, x5
  scvtf d0, x0
  fmov d3, d0
.L13:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16276, lsl #48
  fmov d2, x0
.L14:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d3, d0
.L15:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d2, x0
.L16:
  fmov d1, d3
  // __d2 already in d2
  fadd d0, d1, d2
  fmov d2, d0
.L17:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L18:
  mov x3, #1
.L19:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L20:
  b .L6
.L21:
  movz x0, #0
  movk x0, #16376, lsl #48
  fmov d7, x0
.L22:
  movz x0, #0
  movk x0, #16384, lsl #48
  fmov d6, x0
.L23:
  movz x0, #0
  movk x0, #16392, lsl #48
  fmov d5, x0
.L24:
  mov x4, #0
.L25:
  mov x3, #10000
.L26:
  mov x1, x4
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L49
.L27:
  mov x5, #0
.L28:
  mov x3, #1000
.L29:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L46
.L30:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d4, d0
.L31:
  mov x3, #10
.L32:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x3, x0
.L33:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L34:
  fmov d1, d6
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d3, d0
.L35:
  mov x3, #11
.L36:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x3, x0
.L37:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L38:
  fmov d1, d5
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L39:
  fmov d1, d3
  // __d2 already in d2
  fadd d0, d1, d2
  fmov d2, d0
.L40:
  fmov d1, d4
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L41:
  fmov d1, d7
  // __d2 already in d2
  fadd d0, d1, d2
  fmov d2, d0
.L42:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L43:
  mov x3, #1
.L44:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L45:
  b .L28
.L46:
  mov x3, #1
.L47:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x4, x0
.L48:
  b .L25
.L49:
  str d7, [sp, #80]
.L50:
  str d6, [sp, #88]
.L51:
  str d5, [sp, #96]
.L52:
  str x5, [sp, #104]
.L53:
  str x4, [sp, #112]
.L54:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print q (float)
  ldr d0, [sp, #80]
  sub sp, sp, #32
  adrp x8, .Lname_q@PAGE
  add x8, x8, .Lname_q@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print r (float)
  ldr d0, [sp, #88]
  sub sp, sp, #32
  adrp x8, .Lname_r@PAGE
  add x8, x8, .Lname_r@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print t (float)
  ldr d0, [sp, #96]
  sub sp, sp, #32
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32
  // print k
  ldr x9, [sp, #104]
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
  ldr x9, [sp, #112]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

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

.section __DATA,__data
.global _arr_y
.align 3
_arr_y:
  .space 8192
.global _arr_z
.align 3
_arr_z:
  .space 8192
.global _arr_x
.align 3
_arr_x:
  .space 8192
