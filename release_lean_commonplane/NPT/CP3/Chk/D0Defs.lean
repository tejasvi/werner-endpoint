import NPT.CP3.Chk.Defs
import NPT.CP3.Data.Vars
import NPT.CP3.Data.VarsD0
import NPT.Cert.BrauerTab

/-!
# NPT.CP3.Chk.D0Defs — list-level checkers of the variable-block data (kernel-evaluated)

For variable `v` (`vars[v]`, hints `d0[v]`), with `n = W.length` rows (multi-indices over `dims`, `flatMI` order) and
`m` columns:
* `cosetsOK v`: every coset entry `(new, s)` has `s` a permutation of `0..3` and `new[s[q]] = st[q]`; the `new` are
  pairwise distinct; `#cosets · #stab = 24`;
* `stabOK v`: `stab` is the list of `p < 24` (`NPT.Brauer.permL`) with `st[p q] = st[q]` for all `q`;
* `winvOK v`: `W⁺ W = I` for `W⁺ = rinv / rden` supported on the rows `piv`;
* `bsigOK v`: `Π_σ W = W B_σ` for every `σ` in `stab`, with `(Π_σ W)[μ] = W[μ ∘ σ]` (site slots permuted, aux fixed)
  and `B_σ = bsig / bden`;
* `spanOK v`: `cden · Σ_σ B_σ E_ab B_σᵀ = |stab| · bden² · Σ_j coef[(a,b)][j] S_j` for every upper position `(a, b)`.
-/

namespace NPT.CP3.Chk

open NPT.CP3.Data

/-- Permutation `p` of `NPT.Brauer.permL` as a list (`p q` is entry `q`). -/
def permOf (p : Nat) : List Nat := NPT.Brauer.permL.getD p []

/-- `st ∘ p = st`. -/
def isStab (st : List Nat) (p : Nat) : Bool :=
  (List.range 4).all fun q => st.getD ((permOf p).getD q 0) 0 == st.getD q 0

/-- Mixed-radix digits of `a` over `dims` (factor 0 most significant). -/
def digits : List Nat → Nat → List Nat
  | [], _ => []
  | d :: ds, a => (a / ds.foldr (· * ·) 1) % d :: digits ds a

/-- Mixed-radix value of `μ` over `dims` (factor 0 most significant). -/
def undigits : List Nat → List Nat → Nat
  | d :: ds, x :: xs => x * ds.foldr (· * ·) 1 + undigits ds xs
  | _, _ => 0

/-- Row index of `μ ∘ σ`: site slots `q < 4` read slot `σ q`, the aux slot is kept. -/
def permRow (dims : List Nat) (p : Nat) (a : Nat) : Nat :=
  let μ := digits dims a
  undigits dims ((List.range 4).map (fun q => μ.getD ((permOf p).getD q 0) 0) ++ [μ.getD 4 0])

/-- The variable block and its hints. -/
def vb (v : Nat) : VarB := vars.getD v default
def dv (v : Nat) : VarD0 := d0.getD v default
/-- Number of columns of `W`. -/
def mv (v : Nat) : Nat := ((vb v).W.getD 0 []).length

def isPerm4 (s : List Nat) : Bool := s.length == 4 && (List.range 4).all fun q => s.contains q

def cosetsOK (v : Nat) : Bool :=
  let b := vb v
  b.cosets.all (fun e => isPerm4 e.2 && e.1.length == 4 &&
      (List.range 4).all fun q => e.1.getD (e.2.getD q 0) 0 == b.st.getD q 0) &&
    decide (b.cosets.map Prod.fst).Nodup && b.cosets.length * (dv v).stab.length == 24

def stabOK (v : Nat) : Bool := (dv v).stab == (List.range 24).filter (isStab (vb v).st)

/-- Shapes: `W` is `n × m` with `n = ∏ dims` (5 factors), `piv` has `m` rows below `n`, `rinv` is `m × m`. -/
def wshapeOK (v : Nat) : Bool :=
  let b := vb v
  b.dims.length == 5 && shapeOK b.W (b.dims.foldr (· * ·) 1) (mv v) && (dv v).piv.length == mv v &&
    (dv v).piv.all (· < b.W.length) && shapeOK (dv v).rinv (mv v) (mv v) && 0 < (dv v).rden

def winvOK (v : Nat) : Bool :=
  let W := (vb v).W
  let Wp := (dv v).piv.map fun a => W.getD a []
  (List.range (mv v)).all fun j => (List.range (mv v)).all fun c =>
    decide (dot ((dv v).rinv.getD j []) (Wp.map fun row => row.getD c 0) = if j = c then ((dv v).rden : Int) else 0)

/-- Shapes of the `B_σ` data. -/
def bsigShapeOK (v : Nat) : Bool :=
  (dv v).bsig.length == (dv v).stab.length && 0 < (dv v).bden && (dv v).bsig.all (fun B => shapeOK B (mv v) (mv v))

/-- `Π_σ W = W B_σ` for the `t`-th stabilizer element. -/
def bsigOK1 (v t : Nat) : Bool :=
  (List.range (vb v).W.length).all fun a =>
    (List.range (mv v)).all fun c =>
      decide (dot ((vb v).W.getD a []) (((dv v).bsig.getD t []).map fun r => r.getD c 0) =
        ((dv v).bden : Int) * mget (vb v).W (permRow (vb v).dims ((dv v).stab.getD t 0) a) c)

/-- Entry `(u, w)` of `B E_ab Bᵀ` (`E_ab = e_a e_bᵀ + e_b e_aᵀ` for `a ≠ b`, `e_a e_aᵀ` for `a = b`). -/
def bebt (B : List (List Int)) (a b u w : Nat) : Int :=
  if a = b then mget B u a * mget B w a else mget B u a * mget B w b + mget B u b * mget B w a

/-- Shapes of the span data. -/
def spanShapeOK (v : Nat) : Bool :=
  (dv v).coef.length == (ups (mv v)).length && (dv v).coef.all (fun r => r.length == (vb v).S.length) &&
    0 < (dv v).cden && (vb v).S.all (fun S => shapeOK S (mv v) (mv v))

/-- The averaged unit of the `p`-th upper position `(a, b)` is `Σ_j coef[p][j] / cden · S_j`:
`cden · Σ_σ B_σ E_ab B_σᵀ = |stab| · bden² · Σ_j coef[p][j] S_j` entrywise. -/
def spanOK1 (v p : Nat) : Bool :=
  (List.range (mv v)).all fun u => (List.range (mv v)).all fun w =>
    decide (((dv v).cden : Int) * lsum ((dv v).bsig.map fun B =>
        bebt B ((ups (mv v)).getD p (0, 0)).1 ((ups (mv v)).getD p (0, 0)).2 u w) =
      ((dv v).stab.length : Int) * (((dv v).bden : Int) * (dv v).bden) *
        lsum ((((dv v).coef.getD p []).zip (vb v).S).map fun cs => cs.1 * mget cs.2 u w))

/-- The light D0 checks of variable `v`. -/
def d0LightOK (v : Nat) : Bool :=
  cosetsOK v && stabOK v && wshapeOK v && winvOK v && bsigShapeOK v && spanShapeOK v

/-- All D0 checks of variable `v`. -/
def d0OK (v : Nat) : Bool :=
  d0LightOK v && (List.range (dv v).stab.length).all (bsigOK1 v) && (List.range (ups (mv v)).length).all (spanOK1 v)

end NPT.CP3.Chk
