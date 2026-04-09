.global _main
.align 2

_main:
  sub sp, sp, #96
  str x30, [sp, #88]
  str x29, [sp, #80]
  add x29, sp, #80

  // Initialize all variables to 0
  mov x0, #0

  mov x5, #0
  mov x4, #0
  fmov d4, xzr
  mov x3, #0
  fmov d3, xzr
  fmov d2, xzr
  str x0, [sp, #56]
  str x0, [sp, #64]
  str x0, [sp, #72]

.L0:
  mov x5, #0
.L1:
  mov x4, #0
.L2:
  mov x0, #0
  fmov d4, x0
.L3:
  mov x5, #0
.L4:
  mov x3, #1024
.L5:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L17
.L6:
  mov x0, x5
  scvtf d0, x0
  fmov d3, d0
.L7:
  movz x0, #43516
  movk x0, #54001, lsl #16
  movk x0, #25165, lsl #32
  movk x0, #16208, lsl #48
  fmov d2, x0
.L8:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L9:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L10:
  mov x0, x5
  scvtf d0, x0
  fmov d3, d0
.L11:
  movz x0, #43516
  movk x0, #54001, lsl #16
  movk x0, #25165, lsl #32
  movk x0, #16224, lsl #48
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
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L14:
  mov x3, #1
.L15:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L16:
  b .L4
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
  cbnz w0, .L34
.L20:
  mov x0, #0
  fmov d4, x0
.L21:
  mov x5, #0
.L22:
  mov x3, #1024
.L23:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L31
.L24:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d3, d0
.L25:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L26:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L27:
  fmov d1, d4
  // __d2 already in d2
  fadd d0, d1, d2
  fmov d4, d0
.L28:
  mov x3, #1
.L29:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L30:
  b .L22
.L31:
  mov x3, #1
.L32:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x4, x0
.L33:
  b .L18
.L34:
  str x5, [sp, #56]
.L35:
  str x4, [sp, #64]
.L36:
  str d4, [sp, #72]
.L37:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #56]
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
  ldr x9, [sp, #64]
  sub sp, sp, #16
  adrp x8, .Lname_rep@PAGE
  add x8, x8, .Lname_rep@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print q (float)
  ldr d0, [sp, #72]
  sub sp, sp, #32
  adrp x8, .Lname_q@PAGE
  add x8, x8, .Lname_q@PAGEOFF
  str x8, [sp]
  str d0, [sp, #8]
  adrp x0, .Lfmt_float@PAGE
  add x0, x0, .Lfmt_float@PAGEOFF
  bl _printf
  add sp, sp, #32

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #80]
  ldr x30, [sp, #88]
  add sp, sp, #96
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
.Lname_q:
  .asciz "q"

.section __DATA,__data
.global _arr_x
.align 3
_arr_x:
  .space 8192
.global _arr_z
.align 3
_arr_z:
  .space 8192
