import NPT.CP3.Chk.D0Defs
import NPT.CP3.Data.Site
import NPT.CP3.Data.AuxMaps
import NPT.CP3.Data.Inter

/-!
# NPT.CP3.Chk.D2Defs — the bosonic range of each tuple, and the intertwiners (list level)

For a sorted cut-`()` tuple `v < 175` with true dimensions `dims` (4 site factors, then the aux factor):
* `digL dims l t = t / placeValL dims l % dims[l]` is digit `l` of the flat index `t` (factor 0 most significant);
* `piflI l k g` is the integer intertwiner of factor `l` with label `k` at `g`: `piSite[k][g]` for the sites, the aux
  block permutation `auxM[0][k][g]` for `l = 4`;
* `P24 v t s = Σ_{g<24} Π_{l<5} piflI l (τ_v l) g (digit_l t) (digit_l s)` is `24 ·` the averaged representation;
* `d2OK v` checks `rden · P24 v s t = Σ_j W[t][j] Σ_k rinv[j][k] P24 v s (piv k)` for all `s, t < n`, i.e.
  `Pᵀ = W (W⁺ Pᵀ)` with `W⁺ = rinv / rden` on the rows `piv`.
* `interSiteOK l g`: `J_l[y ∘ g] = J_l[y] · piSite[l][g]` for all 81 digit strings `y` (row `y ∘ g` of `J` is row `y` of
  `VG ℚ 3 0 g * J`); `interAuxOK li g`: the same for the selection matrix of aux block `li` (16 strings).
-/

namespace NPT.CP3.Chk

open NPT.CP3.Data

/-- Product of a list of integers. -/
def lprod : List Int → Int
  | [] => 1
  | a :: as => a * lprod as

/-- Place value of factor `l` over `dims`: `∏_{l' > l} dims[l']`. -/
def placeValL (dims : List Nat) (l : Nat) : Nat := (dims.drop (l + 1)).foldr (· * ·) 1

/-- Digit `l` of the flat index `t` over `dims`. -/
def digL (dims : List Nat) (l t : Nat) : Nat := t / placeValL dims l % dims.getD l 1

/-- Label of factor `l` of tuple `v`: site label for `l < 4`, aux block for `l = 4`. -/
def tauV (v l : Nat) : Nat := if l < 4 then (vb v).st.getD l 0 else (vb v).ai

/-- Integer intertwiner entry of factor `l`, label `k`, permutation `g`. -/
def piflI (l k g a b : Nat) : Int :=
  if l < 4 then mget ((piSite.getD k []).getD g []) a b else mget (((auxM.getD 0 []).getD k []).getD g []) a b

/-- `24 ·` the averaged representation for factor dimensions `dims` and labels `tau`, entry `(t, s)`. -/
def P24b (dims : List Nat) (tau : Nat → Nat) (t s : Nat) : Int :=
  lsum ((List.range 24).map fun g =>
    lprod ((List.range 5).map fun l => piflI l (tau l) g (digL dims l t) (digL dims l s)))

/-- `24 ·` the averaged representation of tuple `v`, entry `(t, s)`. -/
def P24 (v t s : Nat) : Int := P24b (vb v).dims (tauV v) t s

/-- The bosonic range check for a tuple record `b` with hints `h` (the row products `ps`, `u` are shared over `t`). -/
def d2OKb (b : VarB) (h : VarD0) : Bool :=
  let tau := fun l => if l < 4 then b.st.getD l 0 else b.ai
  (List.range b.W.length).all fun s =>
    let ps := h.piv.map fun p => P24b b.dims tau s p
    let u := h.rinv.map fun row => dot row ps
    (List.range b.W.length).all fun t => decide ((h.rden : Int) * P24b b.dims tau s t = dot (b.W.getD t []) u)

/-- The bosonic range check of tuple `v`. -/
def d2OK (v : Nat) : Bool := d2OKb (vb v) (dv v)

/-- Flat index of `y ∘ g` (digit `s` of the result is digit `g s` of `y`) for 4 replicas in base `nb`. -/
def flatPerm (nb g y : Nat) : Nat :=
  undigits [nb, nb, nb, nb]
    ((List.range 4).map fun s => (digits [nb, nb, nb, nb] y).getD ((permOf g).getD s 0) 0)

/-- Site intertwining: `J_l[y ∘ g] = J_l[y] · piSite[l][g]` for every row `y < 81` and column. -/
def interSiteOK (l g : Nat) : Bool :=
  (List.range 81).all fun y =>
    (List.range ((siteDims.getD 0 []).getD l 0)).all fun μ =>
      decide (mget ((siteJ.getD 0 []).getD l []) (flatPerm 3 g y) μ =
        dot (((siteJ.getD 0 []).getD l []).getD y []) (((piSite.getD l []).getD g []).map fun r => r.getD μ 0))

/-- Row `y` of the selection matrix of an aux block (`1` at the position of `y`). -/
def selRow (blk : List Nat) (y : Nat) : List Int := blk.map fun z => if z = y then 1 else 0

/-- Aux intertwining: `Sel[y ∘ g] = Sel[y] · auxM[0][li][g]` for every string `y < 16` and column. -/
def interAuxOK (li g : Nat) : Bool :=
  (List.range 16).all fun y =>
    (List.range ((auxBlocks.getD 0 []).getD li []).length).all fun j =>
      decide ((if ((auxBlocks.getD 0 []).getD li []).getD j 0 = flatPerm 2 g y then (1 : Int) else 0) =
        dot (selRow ((auxBlocks.getD 0 []).getD li []) y) ((((auxM.getD 0 []).getD li []).getD g []).map fun r => r.getD j 0))

/-- All intertwining checks (4 site labels, 5 aux blocks, 24 permutations). -/
def interOK : Bool :=
  (List.range 4).all (fun l => (List.range 24).all (interSiteOK l)) &&
    (List.range 5).all (fun li => (List.range 24).all (interAuxOK li))

/-- Shapes for the intertwining sums: `piSite[k][g]` and `auxM[0][li][g]` are square of the module dimension, and every
row of `J_k` has length `0` (outside the weight space) or `d_k`. -/
def interShapeOK : Bool :=
  (List.range 4).all (fun k =>
    (List.range 24).all (fun g => shapeOK ((piSite.getD k []).getD g []) ((siteDims.getD 0 []).getD k 0)
      ((siteDims.getD 0 []).getD k 0)) &&
    (List.range 81).all (fun y => (((siteJ.getD 0 []).getD k []).getD y []).length == 0 ||
      (((siteJ.getD 0 []).getD k []).getD y []).length == (siteDims.getD 0 []).getD k 0)) &&
  (List.range 5).all (fun li => (List.range 24).all (fun g =>
    shapeOK (((auxM.getD 0 []).getD li []).getD g []) ((auxBlocks.getD 0 []).getD li []).length
      ((auxBlocks.getD 0 []).getD li []).length))

end NPT.CP3.Chk
