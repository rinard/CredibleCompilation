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
  mov x3, #0
  fmov d3, xzr
  fmov d2, xzr
  fmov d4, xzr
  str x0, [sp, #56]
  str x0, [sp, #64]

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
  cbnz w0, .L22
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
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L9:
  mov x0, x5
  scvtf d0, x0
  fmov d3, d0
.L10:
  movz x0, #5243
  movk x0, #18350, lsl #16
  movk x0, #31457, lsl #32
  movk x0, #16276, lsl #48
  fmov d2, x0
.L11:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d3, d0
.L12:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d2, x0
.L13:
  fmov d1, d3
  // __d2 already in d2
  fadd d0, d1, d2
  fmov d2, d0
.L14:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L15:
  mov x0, x5
  scvtf d0, x0
  fmov d3, d0
.L16:
  movz x0, #32506
  movk x0, #48234, lsl #16
  movk x0, #37748, lsl #32
  movk x0, #16232, lsl #48
  fmov d2, x0
.L17:
  fmov d1, d3
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L18:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L19:
  mov x3, #1
.L20:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L21:
  b .L3
.L22:
  mov x4, #0
.L23:
  mov x3, #10000
.L24:
  mov x1, x4
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L42
.L25:
  mov x5, #1
.L26:
  mov x3, #1024
.L27:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L39
.L28:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_z@PAGE
  add x8, x8, _arr_z@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d4, d0
.L29:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_y@PAGE
  add x8, x8, _arr_y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d3, d0
.L30:
  mov x3, #1
.L31:
  mov x1, x5
  mov x2, x3
  sub x0, x1, x2
  mov x3, x0
.L32:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  fmov d0, x0
  fmov d2, d0
.L33:
  fmov d1, d3
  // __d2 already in d2
  fsub d0, d1, d2
  fmov d2, d0
.L34:
  fmov d1, d4
  // __d2 already in d2
  fmul d0, d1, d2
  fmov d2, d0
.L35:
  mov x1, x5
  cmp x1, #1024
  b.hs .Lbounds_err
  fmov d0, d2
  fmov x2, d0
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L36:
  mov x3, #1
.L37:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L38:
  b .L26
.L39:
  mov x3, #1
.L40:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x4, x0
.L41:
  b .L23
.L42:
  str x5, [sp, #56]
.L43:
  str x4, [sp, #64]
.L44:
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

.section __DATA,__data
.global _arr_x
.align 3
_arr_x:
  .space 8192
.global _arr_y
.align 3
_arr_y:
  .space 8192
.global _arr_z
.align 3
_arr_z:
  .space 8192
