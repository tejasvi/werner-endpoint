import Lean

/-!
# Raw-literal elaborators for generated certificate data (untrusted)

These term elaborators build data terms directly from a string in the source: raw natural-number literals,
`Int.ofNat` / `Int.negSucc` constructors and `List.cons` / `List.nil` applications. Elaborating a large generated
data module then costs no `OfNat` instance synthesis per literal. The string never appears in the kernel term.
Soundness does not depend on these elaborators: the kernel checks every statement about the terms they produce.
-/

namespace NPT.Cert.Lit

open Lean Elab Term Meta

/-- The integer `z` as `Int.ofNat n` or `Int.negSucc n` with a raw literal `n`. -/
def intExpr (z : Int) : Expr :=
  if z ≥ 0 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit z.toNat)
  else mkApp (mkConst ``Int.negSucc) (mkRawNatLit ((-z).toNat - 1))

/-- A list literal of type `List α` from element expressions. -/
def listExpr (α : Expr) (lvl : Level) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [lvl]) α x acc) (mkApp (mkConst ``List.nil [lvl]) α)

/-- Parse a whitespace-separated list of (possibly negative) decimal integers. -/
def parseInts (s : String) : Except String (List Int) :=
  (((s.replace "\n" " ").splitOn " ").filter (· ≠ "")).mapM fun (t : String) =>
    match t.toInt? with
    | some z => Except.ok z
    | none => Except.error s!"bad integer token {t}"

/-- `int_list% "1 -2 3"` : `List Int`. -/
elab "int_list% " s:str : term => do
  match parseInts s.getString with
  | .ok zs => return listExpr (mkConst ``Int) Level.zero (zs.map intExpr)
  | .error e => throwError "int_list%: {e}"

/-- `nat_list% "1 2 3"` : `List Nat`. -/
elab "nat_list% " s:str : term => do
  match parseInts s.getString with
  | .ok zs =>
    if zs.any (· < 0) then throwError "nat_list%: negative entry"
    return listExpr (mkConst ``Nat) Level.zero (zs.map fun z => mkRawNatLit z.toNat)
  | .error e => throwError "nat_list%: {e}"

/-- `int_rows% "1 2 | 3 | 4 5 6"` : `List (List Int)` (rows separated by `|`; an empty row is allowed). -/
elab "int_rows% " s:str : term => do
  let rows := s.getString.splitOn "|"
  let mut rs : List Expr := []
  for r in rows do
    match parseInts r with
    | .ok zs => rs := rs ++ [listExpr (mkConst ``Int) Level.zero (zs.map intExpr)]
    | .error e => throwError "int_rows%: {e}"
  return listExpr (mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)) Level.zero rs

/-- `nat_lit% "123"` : the raw literal `123`. -/
elab "nat_lit% " s:str : term => do
  match s.getString.toNat? with
  | some n => return mkRawNatLit n
  | none => throwError "nat_lit%: not a natural number"

/-- `int_lit% "-123"` : the integer as constructor term. -/
elab "int_lit% " s:str : term => do
  match s.getString.toInt? with
  | some z => return intExpr z
  | none => throwError "int_lit%: not an integer"

/-- `nni_list% "i j z | i j z"` : `List (Nat × Nat × Int)`. -/
elab "nni_list% " s:str : term => do
  let natT : Expr := Lean.mkConst ``Nat
  let intT : Expr := Lean.mkConst ``Int
  let niT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) natT intT
  let nniT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) natT niT
  let mut es : List Expr := []
  for r in (s.getString.splitOn "|") do
    match parseInts r with
    | .ok [i, j, z] =>
      if i < 0 || j < 0 then throwError "nni_list%: negative index"
      let inner := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) natT intT (mkRawNatLit j.toNat) (intExpr z)
      es := es ++ [mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) natT niT (mkRawNatLit i.toNat) inner]
    | .ok [] => pure ()
    | .ok _ => throwError "nni_list%: expected triples"
    | .error e => throwError "nni_list%: {e}"
  return listExpr nniT Level.zero es

end NPT.Cert.Lit
