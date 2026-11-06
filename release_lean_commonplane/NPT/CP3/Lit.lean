import Lean

/-!
# Raw-literal elaborators for the common-plane certificate data (untrusted)

Linear-time variants of `NPT.Cert.Lit`: the terms are built directly from a string in the source, with raw
natural-number literals, `Int.ofNat` / `Int.negSucc` constructors and `List.cons` / `List.nil` applications, so a large
generated data module costs no `OfNat` instance synthesis per literal. The string never appears in the kernel term.
Soundness does not depend on these elaborators: the kernel checks every statement about the terms they produce.
-/

namespace NPT.CP3.Lit

open Lean Elab Term Meta

/-- The integer `z` as `Int.ofNat n` or `Int.negSucc n` with a raw literal `n`. -/
def intExpr (z : Int) : Expr :=
  if z ≥ 0 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit z.toNat)
  else mkApp (mkConst ``Int.negSucc) (mkRawNatLit ((-z).toNat - 1))

/-- A list literal of type `List α` (universe 0) from element expressions. -/
def listExpr (α : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) α x acc) (mkApp (mkConst ``List.nil [Level.zero]) α)

/-- Parse a whitespace-separated list of (possibly negative) decimal integers. -/
def parseInts (s : String) : Except String (Array Int) := do
  let mut out : Array Int := #[]
  for t in (s.replace "\n" " ").splitOn " " do
    if t ≠ "" then
      match t.toInt? with
      | some z => out := out.push z
      | none => throw s!"bad integer token {t}"
  return out

def intT : Expr := mkConst ``Int
def natT : Expr := mkConst ``Nat
def listT (α : Expr) : Expr := mkApp (mkConst ``List [Level.zero]) α

def intRow (r : String) : Except String Expr := do
  return listExpr intT ((← parseInts r).map intExpr)

def natRow (r : String) : Except String Expr := do
  let zs ← parseInts r
  if zs.any (· < 0) then throw "negative entry"
  return listExpr natT (zs.map fun z => mkRawNatLit z.toNat)

def liftE {α : Type} (tag : String) : Except String α → TermElabM α
  | .ok a => pure a
  | .error e => throwError "{tag}: {e}"

/-- `ilist% "1 -2 3"` : `List Int`. -/
elab "ilist% " s:str : term => liftE "ilist%" (intRow s.getString)

/-- `nlist% "1 2 3"` : `List Nat`. -/
elab "nlist% " s:str : term => liftE "nlist%" (natRow s.getString)

/-- `nlit% "123"` : the raw literal `123`. -/
elab "nlit% " s:str : term => do
  match s.getString.toNat? with
  | some n => return mkRawNatLit n
  | none => throwError "nlit%: not a natural number"

/-- `ilit% "-123"` : the integer as constructor term. -/
elab "ilit% " s:str : term => do
  match s.getString.toInt? with
  | some z => return intExpr z
  | none => throwError "ilit%: not an integer"

/-- `irows% "1 2 | 3 | 4 5 6"` : `List (List Int)` (rows separated by `|`; an empty row is allowed). -/
elab "irows% " s:str : term => do
  let rows ← liftE "irows%" ((s.getString.splitOn "|").toArray.mapM intRow)
  return listExpr (listT intT) rows

/-- `nrows% "1 2 | 3"` : `List (List Nat)`. -/
elab "nrows% " s:str : term => do
  let rows ← liftE "nrows%" ((s.getString.splitOn "|").toArray.mapM natRow)
  return listExpr (listT natT) rows

/-- `irowss% "1 2 | 3 || || 4"` : `List (List (List Int))`: groups separated by `||`, rows inside a group by `|`.
A group consisting of a single row without entries is the empty list (no rows). -/
elab "irowss% " s:str : term => do
  let mut groups : Array Expr := #[]
  for g in s.getString.splitOn "||" do
    let ints ← liftE "irowss%" ((g.splitOn "|").toArray.mapM parseInts)
    if ints.size == 1 && ints[0]!.isEmpty then
      groups := groups.push (listExpr (listT intT) #[])
    else
      groups := groups.push (listExpr (listT intT) (ints.map fun zs => listExpr intT (zs.map intExpr)))
  return listExpr (listT (listT intT)) groups

end NPT.CP3.Lit
