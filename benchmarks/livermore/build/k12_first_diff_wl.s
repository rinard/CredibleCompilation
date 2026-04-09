.global _main
.align 2

_main:
  sub sp, sp, #80
  str x30, [sp, #72]
  str x29, [sp, #64]
  add x29, sp, #64

  // Initialize all variables to 0
  mov x0, #0

  mov x5, #0
  mov x4, #0
  mov x3, #0
  fmov d3, xzr
  fmov d2, xzr
  str x0, [sp, #48]
  str x0, [sp, #56]

.L0:
  mov x5, #0
.L1:
  mov x4, #0
.L2:
  mov x5, #0
.L3:
  mov x3, #1024
.L4:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L12
.L5:
  mov x0, x5
  scvtf d0, x0
  fmov d3, d0
.L6:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16260, lsl #48
  fmov d2, x0
.L7:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L8:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L9:
  mov x3, #1
.L10:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L11:
  b .L3
.L12:
  mov x4, #0
.L13:
  mov x3, #10000
.L14:
  mov x1, x4
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L30
.L15:
  mov x5, #0
.L16:
  mov x3, #1023
.L17:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L27
.L18:
  mov x3, #1
.L19:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x3, x0
.L20:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d3, d0
.L21:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L22:
  fmov d1, d3
  // __d2 already in d2
  fsub d0, d1, d2
  fmov d2, d0
.L23:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L24:
  mov x3, #1
.L25:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L26:
  b .L16
.L27:
  mov x3, #1
.L28:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x4, x0
.L29:
  b .L13
.L30:
  str x5, [sp, #48]
.L31:
  str x4, [sp, #56]
.L32:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #48]
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
  ldr x9, [sp, #56]
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
  ldr x29, [sp, #64]
  ldr x30, [sp, #72]
  add sp, sp, #80
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
.Lname_rep:
  .asciz "rep"

.section __DATA,__data
.global _arr_y
.align 3
_arr_y:
  .space 8192
.global _arr_x
.align 3
_arr_x:
  .space 8192
