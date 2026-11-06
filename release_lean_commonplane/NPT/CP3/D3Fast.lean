import NPT.CP3.D1Core

/-!
# NPT.CP3.D3Fast — the D3 check with the module data passed as one record (core Lean, compiled to native code)

The computation of `NPT.CP3.D3Core`, term for term, except that every data constant is a field of the record `D3Raw`
and the objective site values `zrA` are computed once per run and passed as `Z`. The module imports no data module,
so it can be compiled into a shared library with `NPT.CP3.D1Core` and `NPT.CP3.Data.Types`. `NPT.CP3.D3Equiv`
shows `d3Range rawD a b = (List.range' a (b - a)).all NPT.CP3.D3.d3OK` by `rfl`.
-/

namespace NPT.CP3.D3F

open NPT.CP3.Ctr NPT.CP3.D1 NPT.CP3.Data

/-- The module data read by the D3 check. -/
structure D3Raw where
  vars : List VarB
  Ecol : List (List Int)
  zsObj2 : List Int
  ifgNum : List (List Int)
  siteOff : List (List Nat)
  eqNum : List (List Int)
  auxBlocks : List (List (List Nat))
  words : List (Nat × Nat)
  zaA : List Int
  zaB : List Int
  zaAB : List Int
  caN : List Int
  cbN : List Int
  cabN : List Int
  sortedQ : List (List Nat)
  erows : List Nat
  auxMst : List (List Int)
  cDen : Nat

def zr2num (R : D3Raw) (t : Nat) : Int := sumRange 24 fun p => R.zsObj2.getD p 0 * (R.ifgNum.getD p []).getD t 0

def zrA (R : D3Raw) : Array Int := Array.ofFn (n := 23) fun t => zr2num R t.val

def aunitI (R : D3Raw) (li a b : Nat) : Nat :=
  R.words.idxOf (((R.auxBlocks.getD 0 []).getD li []).getD a 0, ((R.auxBlocks.getD 0 []).getD li []).getD b 0)

def zaKI (R : D3Raw) (k e : Nat) : Int :=
  match k with
  | 0 => R.zaA.getD e 0
  | 1 => R.zaB.getD e 0
  | _ => 2 * R.zaAB.getD e 0

def tNI (R : D3Raw) (k i : Nat) : Int :=
  match k with
  | 0 => R.caN.getD i 0
  | 1 => R.cbN.getD i 0
  | _ => 2 * R.cabN.getD i 0

def offL (R : D3Raw) (v : VarB) (l : Nat) : Nat := (R.siteOff.getD 0 []).getD (v.st.getD l 0) 0

def objM (R : D3Raw) (Z : Array Int) (v : VarB) (l : Nat) (_t x : Nat) : Int := Z.getD (offL R v l + x) 0

def eqM (R : D3Raw) (v : VarB) (l : Nat) (q x : Nat) : Int := (R.eqNum.getD q []).getD (offL R v l + x) 0

def objT4 (R : D3Raw) (Z : Array Int) (v : VarB) (T0 : Array Int) : Array Int :=
  lift4 (sq v.dims 0) (sq v.dims 1) (sq v.dims 2) (sq v.dims 3) (sq v.dims 4) 1 1 1 1
    (objM R Z v 0) (objM R Z v 1) (objM R Z v 2) (objM R Z v 3) T0

def eqT4 (R : D3Raw) (v : VarB) (T0 : Array Int) : Array Int :=
  lift4 (sq v.dims 0) (sq v.dims 1) (sq v.dims 2) (sq v.dims 3) (sq v.dims 4) 6 6 6 6
    (eqM R v 0) (eqM R v 1) (eqM R v 2) (eqM R v 3) T0

def objVal (R : D3Raw) (v : VarB) (T4 : Array Int) (k : Nat) : Int :=
  sumRange (sq v.dims 4) fun x4 =>
    T4.getD x4 0 * zaKI R k (aunitI R v.ai (x4 / v.dims.getD 4 1) (x4 % v.dims.getD 4 1))

def wq (v : VarB) (q : List Nat) (c m : Nat) : Nat := q.getD (((v.cosets.getD c default).2).getD m m) 0

def eqVal (R : D3Raw) (v : VarB) (T4 : Array Int) (e : Nat) : Int :=
  sumRange v.cosets.length fun c =>
    sumRange (sq v.dims 4) fun x4 =>
      T4.getD ((((wq v (R.sortedQ.getD (R.erows.getD e 0 / 70) []) c 0 * 6 +
          wq v (R.sortedQ.getD (R.erows.getD e 0 / 70) []) c 1) * 6 +
          wq v (R.sortedQ.getD (R.erows.getD e 0 / 70) []) c 2) * 6 +
          wq v (R.sortedQ.getD (R.erows.getD e 0 / 70) []) c 3) * sq v.dims 4 + x4) 0 *
        (R.auxMst.getD (R.erows.getD e 0 % 70) []).getD
          (aunitI R v.ai (x4 / v.dims.getD 4 1) (x4 % v.dims.getD 4 1)) 0

def d3OKj (R : D3Raw) (Z : Array Int) (v : VarB) (j : Nat) : Bool :=
  let T0 := t0Arr v (gArr v j)
  let To := objT4 R Z v T0
  let Te := eqT4 R v T0
  (List.range 3).all (fun k => decide ((v.cosets.length : Int) * objVal R v To k * R.cDen =
      16 * 162 ^ 4 * 576 ^ 4 * tNI R k (v.off + j))) &&
    (List.range 146).all (fun e => decide ((R.Ecol.getD (v.off + j) []).getD e 0 = eqVal R v Te e))

def d3OK (R : D3Raw) (Z : Array Int) (v : Nat) : Bool :=
  (List.range (R.vars.getD v default).S.length).all (d3OKj R Z (R.vars.getD v default))

/-- The D3 check of the tuples `a ≤ v < b`. -/
def d3Range (R : D3Raw) (a b : Nat) : Bool :=
  let Z := zrA R
  (List.range' a (b - a)).all (d3OK R Z)

end NPT.CP3.D3F
