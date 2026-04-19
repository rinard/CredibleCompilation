.global _main
.align 2

_main:
  sub sp, sp, #624
  str x30, [sp, #616]
  str x29, [sp, #608]
  add x29, sp, #608

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
  str x0, [sp, #528]
  str x0, [sp, #536]
  str x0, [sp, #544]
  str x0, [sp, #552]
  str x0, [sp, #560]
  str x0, [sp, #568]
  str x0, [sp, #576]
  str x0, [sp, #584]
  str x0, [sp, #592]

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
  str x0, [sp, #32]
.L4:
  mov x0, #0
  str x0, [sp, #40]
.L5:
  mov x0, #0
  str x0, [sp, #48]
.L6:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #56]
.L7:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #64]
.L8:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #72]
.L9:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L10:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #80]
.L11:
  ldr d1, [sp, #80]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L12:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #88]
.L13:
  ldr d1, [sp, #88]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #72]
.L14:
  mov x0, #1
  str x0, [sp, #8]
.L15:
  mov x0, #1001
  str x0, [sp, #96]
.L16:
  ldr x1, [sp, #8]
  ldr x2, [sp, #96]
  cmp x1, x2
  b.gt .L30
.L17:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #104]
.L18:
  ldr d1, [sp, #104]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #112]
.L19:
  ldr d1, [sp, #112]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #120]
.L20:
  ldr d1, [sp, #120]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L21:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #128]
.L22:
  ldr d1, [sp, #128]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #56]
.L23:
  ldr d1, [sp, #64]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #136]
.L24:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #144]
.L25:
  ldr d1, [sp, #136]
  ldr d2, [sp, #144]
  fmul d0, d1, d2
  str d0, [sp, #152]
.L26:
  ldr x1, [sp, #8]
  ldr d0, [sp, #152]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L27:
  mov x0, #1
  str x0, [sp, #160]
.L28:
  ldr x1, [sp, #8]
  ldr x2, [sp, #160]
  add x0, x1, x2
  str x0, [sp, #8]
.L29:
  b .L15
.L30:
  mov x0, #1
  str x0, [sp, #24]
.L31:
  movz x0, #26200
  movk x0, #175, lsl #16
  str x0, [sp, #168]
.L32:
  ldr x1, [sp, #24]
  ldr x2, [sp, #168]
  cmp x1, x2
  b.gt .L120
.L33:
  movz x0, #21378
  movk x0, #18463, lsl #16
  movk x0, #14814, lsl #32
  movk x0, #16212, lsl #48
  fmov d0, x0
  str d0, [sp, #56]
.L34:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #176]
.L35:
  ldr d1, [sp, #176]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L36:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16369, lsl #48
  fmov d0, x0
  str d0, [sp, #184]
.L37:
  ldr d1, [sp, #184]
  ldr d2, [sp, #56]
  fmul d0, d1, d2
  str d0, [sp, #72]
.L38:
  mov x0, #1
  str x0, [sp, #8]
.L39:
  mov x0, #1001
  str x0, [sp, #192]
.L40:
  ldr x1, [sp, #8]
  ldr x2, [sp, #192]
  cmp x1, x2
  b.gt .L54
.L41:
  movz x0, #0
  movk x0, #16368, lsl #48
  fmov d0, x0
  str d0, [sp, #200]
.L42:
  ldr d1, [sp, #200]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #208]
.L43:
  ldr d1, [sp, #208]
  ldr d2, [sp, #64]
  fmul d0, d1, d2
  str d0, [sp, #216]
.L44:
  ldr d1, [sp, #216]
  ldr d2, [sp, #56]
  fadd d0, d1, d2
  str d0, [sp, #64]
.L45:
  mov x0, #0
  fmov d0, x0
  str d0, [sp, #224]
.L46:
  ldr d1, [sp, #224]
  ldr d2, [sp, #56]
  fsub d0, d1, d2
  str d0, [sp, #56]
.L47:
  ldr d1, [sp, #64]
  ldr d2, [sp, #72]
  fsub d0, d1, d2
  str d0, [sp, #232]
.L48:
  movz x0, #39322
  movk x0, #39321, lsl #16
  movk x0, #39321, lsl #32
  movk x0, #16313, lsl #48
  fmov d0, x0
  str d0, [sp, #240]
.L49:
  ldr d1, [sp, #232]
  ldr d2, [sp, #240]
  fmul d0, d1, d2
  str d0, [sp, #248]
.L50:
  ldr x1, [sp, #8]
  ldr d0, [sp, #248]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L51:
  mov x0, #1
  str x0, [sp, #256]
.L52:
  ldr x1, [sp, #8]
  ldr x2, [sp, #256]
  add x0, x1, x2
  str x0, [sp, #8]
.L53:
  b .L39
.L54:
  mov x0, #101
  str x0, [sp, #32]
.L55:
  mov x0, #0
  str x0, [sp, #48]
.L56:
  ldr x0, [sp, #48]
  str x0, [sp, #40]
.L57:
  ldr x1, [sp, #48]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #48]
.L58:
  mov x0, #2
  str x0, [sp, #264]
.L59:
  ldr x1, [sp, #32]
  ldr x2, [sp, #264]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  str x0, [sp, #32]
.L60:
  ldr x0, [sp, #48]
  str x0, [sp, #16]
.L61:
  mov x0, #2
  str x0, [sp, #272]
.L62:
  ldr x1, [sp, #40]
  ldr x2, [sp, #272]
  add x0, x1, x2
  str x0, [sp, #8]
.L63:
  ldr x1, [sp, #8]
  ldr x2, [sp, #48]
  cmp x1, x2
  b.gt .L85
.L64:
  mov x0, #1
  str x0, [sp, #280]
.L65:
  ldr x1, [sp, #16]
  ldr x2, [sp, #280]
  add x0, x1, x2
  str x0, [sp, #16]
.L66:
  ldr x1, [sp, #8]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #288]
.L67:
  ldr x1, [sp, #8]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #296]
.L68:
  mov x0, #1
  str x0, [sp, #304]
.L69:
  ldr x1, [sp, #8]
  ldr x2, [sp, #304]
  sub x0, x1, x2
  str x0, [sp, #312]
.L70:
  ldr x1, [sp, #312]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #320]
.L71:
  ldr d1, [sp, #296]
  ldr d2, [sp, #320]
  fmul d0, d1, d2
  str d0, [sp, #328]
.L72:
  ldr d1, [sp, #288]
  ldr d2, [sp, #328]
  fsub d0, d1, d2
  str d0, [sp, #336]
.L73:
  mov x0, #1
  str x0, [sp, #344]
.L74:
  ldr x1, [sp, #8]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #352]
.L75:
  ldr x1, [sp, #352]
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #360]
.L76:
  mov x0, #1
  str x0, [sp, #368]
.L77:
  ldr x1, [sp, #8]
  ldr x2, [sp, #368]
  add x0, x1, x2
  str x0, [sp, #376]
.L78:
  ldr x1, [sp, #376]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #384]
.L79:
  ldr d1, [sp, #360]
  ldr d2, [sp, #384]
  fmul d0, d1, d2
  str d0, [sp, #392]
.L80:
  ldr d1, [sp, #336]
  ldr d2, [sp, #392]
  fsub d0, d1, d2
  str d0, [sp, #400]
.L81:
  ldr x1, [sp, #16]
  cmp x1, #1002
  b.hs .Lbounds_err
  ldr d0, [sp, #400]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L82:
  mov x0, #2
  str x0, [sp, #408]
.L83:
  ldr x1, [sp, #8]
  ldr x2, [sp, #408]
  add x0, x1, x2
  str x0, [sp, #8]
.L84:
  b .L63
.L85:
  mov x0, #0
  str x0, [sp, #416]
.L86:
  ldr x1, [sp, #416]
  ldr x2, [sp, #32]
  cmp x1, x2
  b.ge .L117
.L87:
  ldr x0, [sp, #48]
  str x0, [sp, #40]
.L88:
  ldr x1, [sp, #48]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #48]
.L89:
  mov x0, #2
  str x0, [sp, #424]
.L90:
  ldr x1, [sp, #32]
  ldr x2, [sp, #424]
  cbz x2, .Ldiv_by_zero
  sdiv x0, x1, x2
  str x0, [sp, #32]
.L91:
  ldr x0, [sp, #48]
  str x0, [sp, #16]
.L92:
  mov x0, #2
  str x0, [sp, #432]
.L93:
  ldr x1, [sp, #40]
  ldr x2, [sp, #432]
  add x0, x1, x2
  str x0, [sp, #8]
.L94:
  ldr x1, [sp, #8]
  ldr x2, [sp, #48]
  cmp x1, x2
  b.gt .L116
.L95:
  mov x0, #1
  str x0, [sp, #440]
.L96:
  ldr x1, [sp, #16]
  ldr x2, [sp, #440]
  add x0, x1, x2
  str x0, [sp, #16]
.L97:
  ldr x1, [sp, #8]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #448]
.L98:
  ldr x1, [sp, #8]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #456]
.L99:
  mov x0, #1
  str x0, [sp, #464]
.L100:
  ldr x1, [sp, #8]
  ldr x2, [sp, #464]
  sub x0, x1, x2
  str x0, [sp, #472]
.L101:
  ldr x1, [sp, #472]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #480]
.L102:
  ldr d1, [sp, #456]
  ldr d2, [sp, #480]
  fmul d0, d1, d2
  str d0, [sp, #488]
.L103:
  ldr d1, [sp, #448]
  ldr d2, [sp, #488]
  fsub d0, d1, d2
  str d0, [sp, #496]
.L104:
  mov x0, #1
  str x0, [sp, #504]
.L105:
  ldr x1, [sp, #8]
  ldr x2, [sp, #504]
  add x0, x1, x2
  str x0, [sp, #512]
.L106:
  ldr x1, [sp, #512]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_v@PAGE
  add x0, x0, _arr_v@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #520]
.L107:
  mov x0, #1
  str x0, [sp, #528]
.L108:
  ldr x1, [sp, #8]
  ldr x2, [sp, #528]
  add x0, x1, x2
  str x0, [sp, #536]
.L109:
  ldr x1, [sp, #536]
  cmp x1, #1002
  b.hs .Lbounds_err
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #544]
.L110:
  ldr d1, [sp, #520]
  ldr d2, [sp, #544]
  fmul d0, d1, d2
  str d0, [sp, #552]
.L111:
  ldr d1, [sp, #496]
  ldr d2, [sp, #552]
  fsub d0, d1, d2
  str d0, [sp, #560]
.L112:
  ldr x1, [sp, #16]
  cmp x1, #1002
  b.hs .Lbounds_err
  ldr d0, [sp, #560]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  str d0, [x0, x1, lsl #3]
.L113:
  mov x0, #2
  str x0, [sp, #568]
.L114:
  ldr x1, [sp, #8]
  ldr x2, [sp, #568]
  add x0, x1, x2
  str x0, [sp, #8]
.L115:
  b .L94
.L116:
  b .L85
.L117:
  mov x0, #1
  str x0, [sp, #576]
.L118:
  ldr x1, [sp, #24]
  ldr x2, [sp, #576]
  add x0, x1, x2
  str x0, [sp, #24]
.L119:
  b .L31
.L120:
  mov x0, #1
  str x0, [sp, #584]
.L121:
  ldr x1, [sp, #584]
  adrp x0, _arr_x@PAGE
  add x0, x0, _arr_x@PAGEOFF
  ldr d0, [x0, x1, lsl #3]
  str d0, [sp, #592]
.L122:
  // print "%f\n"
  sub sp, sp, #16
  ldr d0, [sp, #592]
  str d0, [sp, #0]
  adrp x0, .Lfmt_print_122@PAGE
  add x0, x0, .Lfmt_print_122@PAGEOFF
  bl _printf
  add sp, sp, #16
.L123:
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
  // print ii
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x1, .Lname_ii@PAGE
  add x1, x1, .Lname_ii@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ipnt
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x1, .Lname_ipnt@PAGE
  add x1, x1, .Lname_ipnt@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print ipntp
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x1, .Lname_ipntp@PAGE
  add x1, x1, .Lname_ipntp@PAGEOFF
  str x1, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print fuzz (float)
  ldr d0, [sp, #56]
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
  ldr d0, [sp, #64]
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
  ldr d0, [sp, #72]
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
  ldr x29, [sp, #608]
  ldr x30, [sp, #616]
  add sp, sp, #624
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

.Lfmt_print_122:
  .asciz "%f\n"

.Lname_k:
  .asciz "k"
.Lname_i:
  .asciz "i"
.Lname_rep:
  .asciz "rep"
.Lname_ii:
  .asciz "ii"
.Lname_ipnt:
  .asciz "ipnt"
.Lname_ipntp:
  .asciz "ipntp"
.Lname_fuzz:
  .asciz "fuzz"
.Lname_buzz:
  .asciz "buzz"
.Lname_fizz:
  .asciz "fizz"

.section __DATA,__data
.global _arr_v
.align 3
_arr_v:
  .space 8016
.global _arr_x
.align 3
_arr_x:
  .space 8016
