.global _main
.align 2

_main:
  sub sp, sp, #80
  str x30, [sp, #72]
  str x29, [sp, #64]
  add x29, sp, #64

  // Initialize all variables to 0
  mov x0, #0

  mov x6, #0
  mov x5, #0
  mov x3, #0
  mov x4, #0
  str x0, [sp, #40]
  str x0, [sp, #48]

.L0:
  mov x6, #0
.L1:
  mov x5, #0
.L2:
  mov x6, #0
.L3:
  mov x3, #1024
.L4:
  mov x1, x6
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L9
.L5:
  mov x1, x6
  cmp x1, #1024
  b.hs .Lbounds_err
  mov x2, x6
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L6:
  mov x3, #1
.L7:
  mov x1, x6
  mov x2, x3
  add x0, x1, x2
  mov x6, x0
.L8:
  b .L3
.L9:
  mov x5, #0
.L10:
  mov x3, #10000
.L11:
  mov x1, x5
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L27
.L12:
  mov x6, #1
.L13:
  mov x3, #1024
.L14:
  mov x1, x6
  mov x2, x3
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L24
.L15:
  mov x1, x6
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x4, x0
.L16:
  mov x3, #1
.L17:
  mov x1, x6
  mov x2, x3
  sub x0, x1, x2
  mov x3, x0
.L18:
  mov x1, x3
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  mov x3, x0
.L19:
  mov x1, x4
  mov x2, x3
  add x0, x1, x2
  mov x3, x0
.L20:
  mov x1, x6
  cmp x1, #1024
  b.hs .Lbounds_err
  mov x2, x3
  adrp x8, _arr_x@PAGE
  add x8, x8, _arr_x@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L21:
  mov x3, #1
.L22:
  mov x1, x6
  mov x2, x3
  add x0, x1, x2
  mov x6, x0
.L23:
  b .L13
.L24:
  mov x3, #1
.L25:
  mov x1, x5
  mov x2, x3
  add x0, x1, x2
  mov x5, x0
.L26:
  b .L10
.L27:
  str x6, [sp, #40]
.L28:
  str x5, [sp, #48]
.L29:
  b .Lhalt

.Lhalt:
  // Save register values to stack for printf
  // Print observable variables
  // print i
  ldr x9, [sp, #40]
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
  ldr x9, [sp, #48]
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
.global _arr_x
.align 3
_arr_x:
  .space 8192
