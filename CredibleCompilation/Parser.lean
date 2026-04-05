import CredibleCompilation.WhileLang
import CredibleCompilation.ExecChecker
import CredibleCompilation.ConstPropOpt

/-!
# Parser for the While Language

Parses a string into a `Program`. No verification on the translation.

## Concrete syntax

```
var x : int, y : int, flag : bool;
x := 0;
y := 1;
while (x < 10) {
  y := y * x;
  x := x + 1
};
if (flag) { skip } else { y := 0 }
```
-/

-- ============================================================
-- § 1. Tokenizer
-- ============================================================

inductive Token where
  | ident  : String → Token
  | num    : Int → Token
  | kw     : String → Token
  | op     : String → Token
  | lparen | rparen | lbrace | rbrace | lbracket | rbracket | comma | semi | colon : Token
  deriving Repr, DecidableEq

private def keywords : List String :=
  ["var", "array", "int", "bool", "if", "else", "while", "skip", "true", "false"]

private def spanDigits : List Char → List Char × List Char
  | c :: rest => if c.isDigit then let (d, r) := spanDigits rest; (c :: d, r) else ([], c :: rest)
  | [] => ([], [])

private def spanAlphaNum : List Char → List Char × List Char
  | c :: rest =>
    if c.isAlphanum || c == '_' then let (d, r) := spanAlphaNum rest; (c :: d, r)
    else ([], c :: rest)
  | [] => ([], [])

partial def tokenize (s : String) : Except String (List Token) :=
  go s.toList ([] : List Token)
where
  go : List Char → List Token → Except String (List Token)
    | [], acc => .ok acc.reverse
    | c :: rest, acc =>
      if c == ' ' || c == '\n' || c == '\r' || c == '\t' then go rest acc
      else if c == '(' then go rest (.lparen :: acc)
      else if c == ')' then go rest (.rparen :: acc)
      else if c == '{' then go rest (.lbrace :: acc)
      else if c == '}' then go rest (.rbrace :: acc)
      else if c == '[' then go rest (.lbracket :: acc)
      else if c == ']' then go rest (.rbracket :: acc)
      else if c == ',' then go rest (.comma :: acc)
      else if c == ';' then go rest (.semi :: acc)
      else if c == '+' then go rest (.op "+" :: acc)
      else if c == '*' then go rest (.op "*" :: acc)
      else if c == '/' then go rest (.op "/" :: acc)
      else if c == '%' then go rest (.op "%" :: acc)
      else if c == '-' then go rest (.op "-" :: acc)
      else if c == ':' then
        match rest with
        | '=' :: rest' => go rest' (.op ":=" :: acc)
        | _ => go rest (.colon :: acc)
      else if c == '<' then
        match rest with
        | '=' :: rest' => go rest' (.op "<=" :: acc)
        | _ => go rest (.op "<" :: acc)
      else if c == '>' then
        match rest with
        | '=' :: rest' => go rest' (.op ">=" :: acc)
        | _ => go rest (.op ">" :: acc)
      else if c == '=' then
        match rest with
        | '=' :: rest' => go rest' (.op "==" :: acc)
        | _ => .error "unexpected '=', did you mean ':=' or '=='?"
      else if c == '!' then
        match rest with
        | '=' :: rest' => go rest' (.op "!=" :: acc)
        | _ => go rest (.op "!" :: acc)
      else if c == '&' then
        match rest with
        | '&' :: rest' => go rest' (.op "&&" :: acc)
        | _ => .error "unexpected '&', did you mean '&&'?"
      else if c == '|' then
        match rest with
        | '|' :: rest' => go rest' (.op "||" :: acc)
        | _ => .error "unexpected '|', did you mean '||'?"
      else if c.isDigit then
        let (digits, rest') := spanDigits (c :: rest)
        let n := digits.foldl (fun acc d => acc * 10 + d.toNat - '0'.toNat) 0
        go rest' (.num (Int.ofNat n) :: acc)
      else if c.isAlpha || c == '_' then
        let (chars, rest') := spanAlphaNum (c :: rest)
        let word := String.ofList chars
        if keywords.contains word then go rest' (.kw word :: acc)
        else go rest' (.ident word :: acc)
      else .error s!"unexpected character '{c}'"

-- ============================================================
-- § 2. Parser (mutual recursive)
-- ============================================================

mutual

partial def parseAtom (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.num n :: rest => .ok (.lit n, rest)
  | Token.ident x :: Token.lbracket :: rest => do
    let (idx, rest') ← parseExpr rest
    match rest' with
    | Token.rbracket :: rest'' => .ok (.arrRead x idx, rest'')
    | _ => .error "expected ']' after array index"
  | Token.ident x :: rest => .ok (.var x, rest)
  | Token.lparen :: rest => do
    let (e, rest') ← parseExpr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (e, rest'')
    | _ => .error "expected ')'"
  | Token.op "-" :: Token.num n :: rest => .ok (.lit (-n), rest)
  | tok :: _ => .error s!"expected expression, got {repr tok}"
  | [] => .error "expected expression, got end of input"

partial def parseTerm (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseAtom toks
  parseTerm' e rest

partial def parseTerm' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "*" :: rest => do let (rhs, rest') ← parseAtom rest; parseTerm' (.bin .mul lhs rhs) rest'
  | Token.op "/" :: rest => do let (rhs, rest') ← parseAtom rest; parseTerm' (.bin .div lhs rhs) rest'
  | Token.op "%" :: rest => do let (rhs, rest') ← parseAtom rest; parseTerm' (.bin .mod lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseExpr (toks : List Token) : Except String (SExpr × List Token) := do
  let (e, rest) ← parseTerm toks
  parseExpr' e rest

partial def parseExpr' (lhs : SExpr) (toks : List Token) : Except String (SExpr × List Token) :=
  match toks with
  | Token.op "+" :: rest => do let (rhs, rest') ← parseTerm rest; parseExpr' (.bin .add lhs rhs) rest'
  | Token.op "-" :: rest => do let (rhs, rest') ← parseTerm rest; parseExpr' (.bin .sub lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBAtom (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.kw "true" :: rest => .ok (.cmp .eq (.lit 0) (.lit 0), rest)
  | Token.kw "false" :: rest => .ok (.cmp .ne (.lit 0) (.lit 0), rest)
  | Token.lparen :: rest => do
    -- Try as boolean expression first
    match parseBOr rest with
    | .ok (b, Token.rparen :: rest'') => .ok (b, rest'')
    | _ =>
      -- Fall back: parenthesized int expr, then comparison op
      let (e1, rest') ← parseExpr (Token.lparen :: rest)
      match rest' with
      | Token.op "<" :: rest'' =>  do let (e2, r) ← parseExpr rest''; .ok (.cmp .lt e1 e2, r)
      | Token.op "<=" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .le e1 e2, r)
      | Token.op "==" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .eq e1 e2, r)
      | Token.op "!=" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .ne e1 e2, r)
      | Token.op ">" :: rest'' =>  do let (e2, r) ← parseExpr rest''; .ok (.cmp .lt e2 e1, r)
      | Token.op ">=" :: rest'' => do let (e2, r) ← parseExpr rest''; .ok (.cmp .le e2 e1, r)
      | _ => .error "expected ')' after boolean expression"
  | Token.op "!" :: rest => do
    let (b, rest') ← parseBAtom rest
    .ok (.not b, rest')
  | _ => do
    let (e1, rest) ← parseExpr toks
    match rest with
    | Token.op "<" :: rest' =>  do let (e2, r) ← parseExpr rest'; .ok (.cmp .lt e1 e2, r)
    | Token.op "<=" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .le e1 e2, r)
    | Token.op "==" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .eq e1 e2, r)
    | Token.op "!=" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .ne e1 e2, r)
    | Token.op ">" :: rest' =>  do let (e2, r) ← parseExpr rest'; .ok (.cmp .lt e2 e1, r)
    | Token.op ">=" :: rest' => do let (e2, r) ← parseExpr rest'; .ok (.cmp .le e2 e1, r)
    | _ =>
      match e1 with
      | .var x => .ok (.bvar x, rest)
      | _ => .error "expected comparison operator after expression"

partial def parseBNot (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.op "!" :: rest => do let (b, rest') ← parseBNot rest; .ok (.not b, rest')
  | _ => parseBAtom toks

partial def parseBand (toks : List Token) : Except String (SBool × List Token) := do
  let (b, rest) ← parseBNot toks
  parseBand' b rest

partial def parseBand' (lhs : SBool) (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.op "&&" :: rest => do let (rhs, rest') ← parseBNot rest; parseBand' (.and lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBOr (toks : List Token) : Except String (SBool × List Token) := do
  let (b, rest) ← parseBand toks
  parseBOr' b rest

partial def parseBOr' (lhs : SBool) (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.op "||" :: rest => do let (rhs, rest') ← parseBand rest; parseBOr' (.or lhs rhs) rest'
  | _ => .ok (lhs, toks)

partial def parseBExprParen (toks : List Token) : Except String (SBool × List Token) :=
  match toks with
  | Token.lparen :: rest => do
    let (b, rest') ← parseBOr rest
    match rest' with
    | Token.rparen :: rest'' => .ok (b, rest'')
    | _ => .error "expected ')' after condition"
  | _ => parseBOr toks

partial def parseStmtAtom (toks : List Token) : Except String (Stmt × List Token) :=
  match toks with
  | Token.kw "skip" :: rest => .ok (.skip, rest)
  | Token.ident x :: Token.lbracket :: rest => do
    let (idx, rest') ← parseExpr rest
    match rest' with
    | Token.rbracket :: Token.op ":=" :: rest'' => do
      let (val, rest''') ← parseExpr rest''
      .ok (.arrWrite x idx val, rest''')
    | _ => .error "expected '] :=' for array write"
  | Token.ident x :: Token.op ":=" :: rest =>
    match rest with
    | Token.kw "true" :: _ | Token.kw "false" :: _ | Token.op "!" :: _ => do
      let (b, rest') ← parseBOr rest
      .ok (.bassign x b, rest')
    | Token.lparen :: _ => do
      -- Ambiguous: could be parenthesized int expr or parenthesized bool expr.
      -- Try boolean first (it handles both since comparison falls through to expr).
      match parseBOr rest with
      | .ok (b, rest') => .ok (.bassign x b, rest')
      | .error _ => do
        let (e, rest') ← parseExpr rest
        .ok (.assign x e, rest')
    | _ => do
      let (e, rest') ← parseExpr rest
      match rest' with
      | Token.op "<" :: _ | Token.op "<=" :: _ | Token.op ">" :: _ | Token.op ">=" :: _
      | Token.op "==" :: _ | Token.op "!=" :: _
      | Token.op "&&" :: _ | Token.op "||" :: _ => do
        let (b, rest'') ← parseBOr rest
        .ok (.bassign x b, rest'')
      | _ => .ok (.assign x e, rest')
  | Token.kw "if" :: rest => do
    let (cond, rest') ← parseBExprParen rest
    match rest' with
    | Token.lbrace :: rest'' => do
      let (s1, rest''') ← parseStmt rest''
      match rest''' with
      | Token.rbrace :: Token.kw "else" :: Token.lbrace :: rest4 => do
        let (s2, rest5) ← parseStmt rest4
        match rest5 with
        | Token.rbrace :: rest6 => .ok (.ite cond s1 s2, rest6)
        | _ => .error "expected '}' after else branch"
      | _ => .error "expected '} else {'"
    | _ => .error "expected '{' after if condition"
  | Token.kw "while" :: rest => do
    let (cond, rest') ← parseBExprParen rest
    match rest' with
    | Token.lbrace :: rest'' => do
      let (body, rest''') ← parseStmt rest''
      match rest''' with
      | Token.rbrace :: rest4 => .ok (.loop cond body, rest4)
      | _ => .error "expected '}' after while body"
    | _ => .error "expected '{' after while condition"
  | tok :: _ => .error s!"expected statement, got {repr tok}"
  | [] => .error "expected statement, got end of input"

partial def parseStmt (toks : List Token) : Except String (Stmt × List Token) := do
  let (s, rest) ← parseStmtAtom toks
  parseStmt' s rest

partial def parseStmt' (lhs : Stmt) (toks : List Token) : Except String (Stmt × List Token) :=
  match toks with
  | Token.semi :: Token.rbrace :: rest => .ok (lhs, Token.rbrace :: rest)
  | Token.semi :: rest => do
    let (rhs, rest') ← parseStmtAtom rest
    parseStmt' (.seq lhs rhs) rest'
  | _ => .ok (lhs, toks)

end

-- ============================================================
-- § 3. Declaration and program parser
-- ============================================================

private def parseDecl (toks : List Token) : Except String ((Var × VarTy) × List Token) :=
  match toks with
  | Token.ident x :: Token.colon :: Token.kw "int" :: rest => .ok ((x, .int), rest)
  | Token.ident x :: Token.colon :: Token.kw "bool" :: rest => .ok ((x, .bool), rest)
  | Token.ident _ :: Token.colon :: tok :: _ => .error s!"expected 'int' or 'bool', got {repr tok}"
  | Token.ident _ :: tok :: _ => .error s!"expected ':', got {repr tok}"
  | tok :: _ => .error s!"expected variable name, got {repr tok}"
  | [] => .error "expected declaration"

private partial def parseDecls' (acc : List (Var × VarTy)) (toks : List Token)
    : Except String (List (Var × VarTy) × List Token) :=
  match toks with
  | Token.comma :: rest => do let (d, rest') ← parseDecl rest; parseDecls' (acc ++ [d]) rest'
  | Token.semi :: rest => .ok (acc, rest)
  | tok :: _ => .error s!"expected ',' or ';' after declaration, got {repr tok}"
  | [] => .error "expected ';' after declarations"

private partial def parseDecls (toks : List Token) : Except String (List (Var × VarTy) × List Token) :=
  match toks with
  | Token.kw "var" :: rest => do
    let (d, rest') ← parseDecl rest
    parseDecls' [d] rest'
  | tok :: _ => .error s!"expected 'var', got {repr tok}"
  | [] => .error "expected 'var'"

/-- Parse a single array declaration: `name[size]`. -/
private def parseArrayDecl (toks : List Token)
    : Except String ((ArrayName × Nat) × List Token) :=
  match toks with
  | Token.ident name :: Token.lbracket :: Token.num n :: Token.rbracket :: rest =>
    if n ≥ 0 then .ok ((name, n.toNat), rest)
    else .error s!"array size must be non-negative, got {n}"
  | Token.ident _ :: Token.lbracket :: Token.num _ :: tok :: _ =>
    .error s!"expected ']' after array size, got {repr tok}"
  | Token.ident _ :: Token.lbracket :: tok :: _ =>
    .error s!"expected array size (integer), got {repr tok}"
  | Token.ident _ :: tok :: _ => .error s!"expected '[' after array name, got {repr tok}"
  | tok :: _ => .error s!"expected array name, got {repr tok}"
  | [] => .error "expected array declaration"

private partial def parseArrayDecls' (acc : List (ArrayName × Nat)) (toks : List Token)
    : Except String (List (ArrayName × Nat) × List Token) :=
  match toks with
  | Token.comma :: rest => do let (d, rest') ← parseArrayDecl rest; parseArrayDecls' (acc ++ [d]) rest'
  | Token.semi :: rest => .ok (acc, rest)
  | tok :: _ => .error s!"expected ',' or ';' after array declaration, got {repr tok}"
  | [] => .error "expected ';' after array declarations"

private partial def parseArrayDecls (toks : List Token)
    : Except String (List (ArrayName × Nat) × List Token) :=
  match toks with
  | Token.kw "array" :: rest => do
    let (d, rest') ← parseArrayDecl rest
    parseArrayDecls' [d] rest'
  | _ => .ok ([], toks)  -- array declarations are optional

/-- Parse a string into a `Program`. -/
def parseProgram (input : String) : Except String Program := do
  let toks ← tokenize input
  let (decls, rest) ← parseDecls toks
  let (arrayDecls, rest'') ← parseArrayDecls rest
  let (body, rest') ← parseStmt rest''
  if rest'.isEmpty then .ok { decls, arrayDecls, body }
  else .error s!"unexpected tokens after program"

-- ============================================================
-- § 4. Tests
-- ============================================================

#eval! parseProgram "var x : int, y : int; x := 0; y := x + 1"

#eval! parseProgram "
  var n : int, s : int, i : int;
  s := 0;
  i := 1;
  while (i <= n) {
    s := s + i;
    i := i + 1
  }
"

#eval! parseProgram "
  var r : int, n : int;
  r := 1;
  while (n != 0) {
    r := r * n;
    n := n - 1
  }
"

#eval! parseProgram "
  var a : int, b : int, m : int;
  if (a < b) { m := b } else { m := a }
"

#eval! parseProgram "
  var x : int, flag : bool;
  x := 5;
  flag := x < 10
"

-- End-to-end: parse → compile → optimize → check
#eval! do
  let prog ← parseProgram "
    var n : int, s : int, i : int;
    s := 0;
    i := 1;
    while (i <= n) {
      s := s + i;
      i := i + 1
    }
  "
  return (prog.compile.code.toList, checkCertificateVerboseExec (ConstPropOpt.optimize prog.compile))
