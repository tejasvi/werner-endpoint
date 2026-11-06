import NPT.CP3.D1Core
import NPT.CP3.Data.Vars
import NPT.CP3.Data.Site
import NPT.CP3.Data.AuxMaps
import NPT.CP3.Data.E
import NPT.CP3.Data.CertG
import NPT.CP3.Data.Obj

/-!
# NPT.CP3.D3Core — the integer computation behind check D3 (core Lean only, compiled for `native_decide`)

For a coordinate `(v, j)` the objective coordinates (`ca`, `cb`, `2 cab`) and the 146 used equality rows are
recomputed from the module data, as xbuild.py does (`exact_part`, `modular_part`):
* `G = W S_j Wᵀ` laid out per factor (`gArr`, `t0Arr` of `NPT.CP3.D1Core`);
* `objT4`: the four site axes contracted with the doubled objective site functional `zr2num = zsObj2 · ifgNum`
  (`576 ·` the rational one); `objVal k` then contracts the aux pair with `zaA`, `zaB`, `2 zaAB`;
* `eqT4`: the four site axes contracted with all six rows of `eqNum` (`192 ·` the rational delete map) at once;
  `eqVal e` picks row `erows[e] = qi · 70 + u` (word tuple `sortedQ[qi]`, unit `u`), sums the coset transposes
  (word `q[s_c[m]]` at site `m`) and contracts the aux pair with row `u` of `auxMst`;
* `d3OKj v j`: `|cosets| · objVal k · cDen = 16 · 162⁴ · 576⁴ · tN k (off + j)` for `k < 3`, and
  `Ecol[off + j][e] = eqVal e` for `e < 146`.
-/

namespace NPT.CP3.D3

open NPT.CP3.Ctr NPT.CP3.D1 NPT.CP3.Data

/-- `576 ·` the objective site functional on the 23 cut-`()` site Gram coordinates. -/
def zr2num (t : Nat) : Int := sumRange 24 fun p => zsObj2.getD p 0 * (ifgNum.getD p []).getD t 0

/-- The 23 values of `zr2num`. -/
def zrA : Array Int := Array.ofFn (n := 23) fun t => zr2num t.val

/-- Aux unit index of entry `(a, b)` of cut-`()` aux block `li`. -/
def aunitI (li a b : Nat) : Nat :=
  words.idxOf (((auxBlocks.getD 0 []).getD li []).getD a 0, ((auxBlocks.getD 0 []).getD li []).getD b 0)

/-- Objective aux functionals on units: `zaA`, `zaB`, `2 zaAB`. -/
def zaKI (k e : Nat) : Int :=
  match k with
  | 0 => zaA.getD e 0
  | 1 => zaB.getD e 0
  | _ => 2 * zaAB.getD e 0

/-- `cDen · (ca, cb, 2 cab)` at coordinate `i`. -/
def tNI (k i : Nat) : Int :=
  match k with
  | 0 => caN.getD i 0
  | 1 => cbN.getD i 0
  | _ => 2 * cabN.getD i 0

/-- Site Gram offset of the label of site `l` of `v`. -/
def offL (v : VarB) (l : Nat) : Nat := (siteOff.getD 0 []).getD (v.st.getD l 0) 0

/-- Objective site matrix of site `l` (one output row). -/
def objM (v : VarB) (l : Nat) (_t x : Nat) : Int := zrA.getD (offL v l + x) 0

/-- Equality site matrix of site `l` (six output rows, the three-replica words). -/
def eqM (v : VarB) (l : Nat) (q x : Nat) : Int := (eqNum.getD q []).getD (offL v l + x) 0

/-- The four site axes of `T0` contracted with the objective site functional. -/
def objT4 (v : VarB) (T0 : Array Int) : Array Int :=
  lift4 (sq v.dims 0) (sq v.dims 1) (sq v.dims 2) (sq v.dims 3) (sq v.dims 4) 1 1 1 1
    (objM v 0) (objM v 1) (objM v 2) (objM v 3) T0

/-- The four site axes of `T0` contracted with the six word rows. -/
def eqT4 (v : VarB) (T0 : Array Int) : Array Int :=
  lift4 (sq v.dims 0) (sq v.dims 1) (sq v.dims 2) (sq v.dims 3) (sq v.dims 4) 6 6 6 6
    (eqM v 0) (eqM v 1) (eqM v 2) (eqM v 3) T0

/-- Objective value `k`: the aux pair contracted with `zaKI k`. -/
def objVal (v : VarB) (T4 : Array Int) (k : Nat) : Int :=
  sumRange (sq v.dims 4) fun x4 =>
    T4.getD x4 0 * zaKI k (aunitI v.ai (x4 / v.dims.getD 4 1) (x4 % v.dims.getD 4 1))

/-- Word at site `m` for coset `c` of `v` and word tuple `q`. -/
def wq (v : VarB) (q : List Nat) (c m : Nat) : Nat := q.getD (((v.cosets.getD c default).2).getD m m) 0

/-- Equality value of used row `e`. -/
def eqVal (v : VarB) (T4 : Array Int) (e : Nat) : Int :=
  sumRange v.cosets.length fun c =>
    sumRange (sq v.dims 4) fun x4 =>
      T4.getD ((((wq v (sortedQ.getD (erows.getD e 0 / 70) []) c 0 * 6 +
          wq v (sortedQ.getD (erows.getD e 0 / 70) []) c 1) * 6 +
          wq v (sortedQ.getD (erows.getD e 0 / 70) []) c 2) * 6 +
          wq v (sortedQ.getD (erows.getD e 0 / 70) []) c 3) * sq v.dims 4 + x4) 0 *
        (auxMst.getD (erows.getD e 0 % 70) []).getD (aunitI v.ai (x4 / v.dims.getD 4 1) (x4 % v.dims.getD 4 1)) 0

/-- The D3 check of coordinate `(v, j)` (variable record `v`). -/
def d3OKj (v : VarB) (j : Nat) : Bool :=
  let T0 := t0Arr v (gArr v j)
  let To := objT4 v T0
  let Te := eqT4 v T0
  (List.range 3).all (fun k => decide ((v.cosets.length : Int) * objVal v To k * cDen =
      16 * 162 ^ 4 * 576 ^ 4 * tNI k (v.off + j))) &&
    (List.range 146).all (fun e => decide ((Ecol.getD (v.off + j) []).getD e 0 = eqVal v Te e))

/-- The D3 check of tuple `v` (all of its basis matrices). -/
def d3OK (v : Nat) : Bool := (List.range (vars.getD v default).S.length).all (d3OKj (vars.getD v default))

end NPT.CP3.D3
