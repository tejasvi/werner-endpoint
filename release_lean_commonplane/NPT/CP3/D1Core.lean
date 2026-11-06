/-
NPT.CP3.D1Core — the integer computation behind check D1 (core Lean only, so that it can be compiled to native code).

For a coordinate `i` (variable `v`, basis index `j`) and every active block `k`, the block coefficient `F_k[i]` is
recomputed from the module data, as xbuild.py does:
* `gArr`: `G = W S_j Wᵀ` over the true dimensions of `v` (flat `n × n`);
* `t0Arr`: `G` laid out per factor; axis `q` is the pair `(a_q, b_q)` of site `q` (`d_q²` values), the auxiliary pair
  last;
* `t4Arr`: the four site axes lifted to cut-`(3,)` Gram coordinates by the integer Fourier rows `phiNum` (`lift4`);
* `xInv`: the auxiliary pair whose cut-`(3,)` coordinate (`auxDest`) is a given one;
* `fOut3` / `fOut0`: `F_k[i] = V_kᵀ H V_k`, `H` summed over the cosets of `v` (cut `(3,)` / cut `()`);
* `fData`: `fScale[cut] ·` the symmetric matrix of the row of `k` in `Fc[i]` (`0` if absent);
* `checkCoord i`: `fOut = fData` for every block; `checkRange a b` for `a ≤ i < b`.
-/
import NPT.CP3.Data.Types

namespace NPT.CP3.Ctr

/-- Accumulating loop for `sumRange`. -/
def sumGo (f : Nat → Int) : Nat → Int → Int
  | 0, acc => acc
  | k + 1, acc => sumGo f k (acc + f k)

/-- `Σ_{x < n} f x`, computed by a loop. -/
def sumRange (n : Nat) (f : Nat → Int) : Int := sumGo f n 0

/-- Contract the middle axis of a flat tensor of shape `(B, n, A)` with an `n' × n` matrix `M`. -/
def contract (B n A n' : Nat) (M : Nat → Nat → Int) (T : Array Int) : Array Int :=
  Array.ofFn (n := B * n' * A) fun i =>
    let y := i.val / A % n'
    let b := i.val / (n' * A) * n
    let a := i.val % A
    sumRange n fun x => M y x * T.getD ((b + x) * A + a) 0

/-- Four contractions on the first four axes of a tensor of shape `(n0, n1, n2, n3, n4)`. -/
def lift4 (n0 n1 n2 n3 n4 m0 m1 m2 m3 : Nat) (M0 M1 M2 M3 : Nat → Nat → Int) (T : Array Int) : Array Int :=
  let T1 := contract 1 n0 (n1 * n2 * n3 * n4) m0 M0 T
  let T2 := contract m0 n1 (n2 * n3 * n4) m1 M1 T1
  let T3 := contract (m0 * m1) n2 (n3 * n4) m2 M2 T2
  contract (m0 * m1 * m2) n3 n4 m3 M3 T3

end NPT.CP3.Ctr

namespace NPT.CP3.D1

open NPT.CP3.Ctr NPT.CP3.Data

/-- The raw lists the computation reads. -/
structure Raw where
  vars : List VarB
  outs : List OutB
  Fc : List (List (List Int))
  fScale : List Nat
  phiNum : List (List Int)
  siteOff : List (List Nat)
  auxOff : List Nat
  auxDest : List Nat

/-- Flat integer array of a list matrix (`r × c`, row-major). -/
def flatOf (A : List (List Int)) (r c : Nat) : Array Int :=
  Array.ofFn (n := r * c) fun t => (A.getD (t.val / c) []).getD (t.val % c) 0

/-- Mixed-radix flat index of five digits (factor 0 most significant). -/
def flat5 (d : List Nat) (a0 a1 a2 a3 a4 : Nat) : Nat :=
  (((a0 * d.getD 1 1 + a1) * d.getD 2 1 + a2) * d.getD 3 1 + a3) * d.getD 4 1 + a4

/-- Digit `l` of a flat index in the mixed radix `d` (factor 0 most significant, five factors). -/
def digit (d : List Nat) (p l : Nat) : Nat :=
  match l with
  | 0 => p / (d.getD 1 1 * d.getD 2 1 * d.getD 3 1 * d.getD 4 1) % d.getD 0 1
  | 1 => p / (d.getD 2 1 * d.getD 3 1 * d.getD 4 1) % d.getD 1 1
  | 2 => p / (d.getD 3 1 * d.getD 4 1) % d.getD 2 1
  | 3 => p / d.getD 4 1 % d.getD 3 1
  | _ => p % d.getD 4 1

/-- Number of entries of a box. -/
def boxN (d : List Nat) : Nat := d.getD 0 1 * d.getD 1 1 * d.getD 2 1 * d.getD 3 1 * d.getD 4 1

/-- `d_q²`. -/
def sq (d : List Nat) (q : Nat) : Nat := d.getD q 1 * d.getD q 1

/-- `G = W S Wᵀ` (flat `n × n`). -/
def gArr (v : VarB) (j : Nat) : Array Int :=
  let n := boxN v.dims
  let m := (v.W.getD 0 []).length
  let Wa := flatOf v.W n m
  let Sa := flatOf (v.S.getD j []) m m
  let WS := Array.ofFn (n := n * m) fun t =>
    sumRange m fun u => Wa.getD (t.val / m * m + u) 0 * Sa.getD (u * m + t.val % m) 0
  Array.ofFn (n := n * n) fun t =>
    sumRange m fun u => WS.getD (t.val / n * m + u) 0 * Wa.getD (t.val % n * m + u) 0

/-- `G` laid out per factor: axis `q` is the pair `x_q = a_q d_q + b_q` of site `q`, the auxiliary pair last. -/
def t0Arr (v : VarB) (G : Array Int) : Array Int :=
  let d := v.dims
  let n := boxN d
  let s1 := sq d 1
  let s2 := sq d 2
  let s3 := sq d 3
  let n4 := sq d 4
  Array.ofFn (n := sq d 0 * s1 * s2 * s3 * n4) fun t =>
    let x0 := t.val / (n4 * s3 * s2 * s1)
    let x1 := t.val / (n4 * s3 * s2) % s1
    let x2 := t.val / (n4 * s3) % s2
    let x3 := t.val / n4 % s3
    let x4 := t.val % n4
    let fa := flat5 d (x0 / d.getD 0 1) (x1 / d.getD 1 1) (x2 / d.getD 2 1) (x3 / d.getD 3 1) (x4 / d.getD 4 1)
    let fb := flat5 d (x0 % d.getD 0 1) (x1 % d.getD 1 1) (x2 % d.getD 2 1) (x3 % d.getD 3 1) (x4 % d.getD 4 1)
    G.getD (fa * n + fb) 0

/-- The four site axes lifted to cut-`(3,)` Gram coordinates (23 each). -/
def t4Arr (R : Raw) (phA : Array Int) (v : VarB) (T0 : Array Int) : Array Int :=
  let d := v.dims
  let off0 := R.siteOff.getD 0 []
  let b0 := off0.getD (v.st.getD 0 0) 0
  let b1 := off0.getD (v.st.getD 1 0) 0
  let b2 := off0.getD (v.st.getD 2 0) 0
  let b3 := off0.getD (v.st.getD 3 0) 0
  lift4 (sq d 0) (sq d 1) (sq d 2) (sq d 3) (sq d 4) 23 23 23 23
    (fun t x => phA.getD (t * 23 + b0 + x) 0) (fun t x => phA.getD (t * 23 + b1 + x) 0)
    (fun t x => phA.getD (t * 23 + b2 + x) 0) (fun t x => phA.getD (t * 23 + b3 + x) 0) T0

/-- `xInv[e']`: the auxiliary pair `x` of `v` with `auxDest[auxOff[ai] + x] = e'` (`n4` if none). -/
def xInv (R : Raw) (v : VarB) : Array Nat :=
  let n4 := sq v.dims 4
  let base := R.auxOff.getD v.ai 0
  Array.ofFn (n := 70) fun e =>
    ((List.range n4).find? fun x => R.auxDest.getD (base + x) 0 == e.val).getD n4

/-- Site permutation of a coset as a function (`s[q]`). -/
def sOf (s : List Nat) (q : Nat) : Nat := s.getD q q

/-- The zero `m × m` list matrix. -/
def zeroM (m : Nat) : List (List Int) := (List.range m).map fun _ => (List.range m).map fun _ => 0

/-- `Vᵀ H V` for a flat `n' × n'` array `H` and an `n' × m` list `V`. -/
def vhv (H : Array Int) (V : List (List Int)) (n' m : Nat) : List (List Int) :=
  let Va := flatOf V n' m
  let X := Array.ofFn (n := n' * m) fun t =>
    let rb := t.val / m * n'
    let c := t.val % m
    sumRange n' fun q => H.getD (rb + q) 0 * Va.getD (q * m + c) 0
  (List.range m).map fun u => (List.range m).map fun w =>
    sumRange n' fun p => Va.getD (p * m + u) 0 * X.getD (p * m + w) 0

/-- Cut-`(3,)` block coefficient (integer) of block `o` at the coordinate `(v, j)`, given the lifted array. -/
def fOut3 (R : Raw) (v : VarB) (T4 : Array Int) (XI : Array Nat) (o : OutB) : List (List Int) :=
  let d := o.dims
  let n' := boxN d
  let n4 := sq v.dims 4
  let off1 := R.siteOff.getD 1 []
  let base := R.auxOff.getD o.ai 0
  let da := d.getD 4 1
  if (List.range (da * da)).any fun t => XI.getD (base + t) n4 < n4 then
    let dig := Array.ofFn (n := n' * 5) fun t => digit d (t.val / 5) (t.val % 5)
    let rb := Array.ofFn (n := n' * 4) fun t =>
      off1.getD (o.st.getD (t.val % 4) 0) 0 + digit d (t.val / 4) (t.val % 4) * d.getD (t.val % 4) 1
    let cs := v.cosets.toArray
    let nc := cs.size
    let ax := Array.ofFn (n := nc * 4) fun t => sOf (cs.getD (t.val / 4) default).2 (t.val % 4)
    let H := Array.ofFn (n := n' * n') fun t =>
      let p := t.val / n'
      let q := t.val % n'
      let x4 := XI.getD (base + dig.getD (p * 5 + 4) 0 * da + dig.getD (q * 5 + 4) 0) n4
      if x4 < n4 then
        sumRange nc fun c =>
          T4.getD (((((rb.getD (p * 4 + ax.getD (c * 4) 0) 0 + dig.getD (q * 5 + ax.getD (c * 4) 0) 0) * 23 +
            (rb.getD (p * 4 + ax.getD (c * 4 + 1) 0) 0 + dig.getD (q * 5 + ax.getD (c * 4 + 1) 0) 0)) * 23 +
            (rb.getD (p * 4 + ax.getD (c * 4 + 2) 0) 0 + dig.getD (q * 5 + ax.getD (c * 4 + 2) 0) 0)) * 23 +
            (rb.getD (p * 4 + ax.getD (c * 4 + 3) 0) 0 + dig.getD (q * 5 + ax.getD (c * 4 + 3) 0) 0)) * n4 + x4) 0
      else 0
    vhv H o.V n' o.m
  else zeroM o.m

/-- Cut-`()` block coefficient (integer) of block `o` at the coordinate `(v, j)`. -/
def fOut0 (v : VarB) (G : Array Int) (o : OutB) : List (List Int) :=
  if v.ai == o.ai && v.cosets.any (fun c => c.1 == o.st) then
    let d := o.dims
    let n' := boxN d
    let n := boxN v.dims
    let H := Array.ofFn (n := n' * n') fun t =>
      let p := t.val / n'
      let q := t.val % n'
      (v.cosets.map fun c =>
        if c.1 == o.st then
          let s := c.2
          let fa := flat5 v.dims (digit d p (sOf s 0)) (digit d p (sOf s 1)) (digit d p (sOf s 2))
            (digit d p (sOf s 3)) (digit d p 4)
          let fb := flat5 v.dims (digit d q (sOf s 0)) (digit d q (sOf s 1)) (digit d q (sOf s 2))
            (digit d q (sOf s 3)) (digit d q 4)
          G.getD (fa * n + fb) 0
        else 0).sum
    vhv H o.V n' o.m
  else zeroM o.m

/-- The upper-triangle positions `(u, v)`, `u ≤ v < m`, in the order `(0,0), (0,1), …, (0,m−1), (1,1), …` (as
`NPT.CP3.Chk.ups`). -/
def ups (m : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap fun u => (List.range (m - u)).map fun t => (u, u + t)

/-- Value of the first entry with key `q` (0 if none), as `NPT.CP3.Chk.lookupZ`. -/
def lookupZ (E : List ((Nat × Nat) × Int)) (q : Nat × Nat) : Int :=
  ((E.find? fun e => decide (e.1 = q)).map Prod.snd).getD 0

/-- The data `F_k[i]` (integer): `fScale[cut k] ·` the symmetric matrix of the row of `k` in `Fc[i]`, written as
`NPT.CP3.Sem.Fmat` reads it. -/
def fData (R : Raw) (rows : List (List Int)) (k : Nat) (o : OutB) : List (List Int) :=
  let row := ((rows.find? fun r => decide (r.headD (-1) = (k : Int))).map List.tail).getD []
  let g : Int := Int.ofNat (R.fScale.getD o.cut 1)
  let m := o.m
  (List.range m).map fun u => (List.range m).map fun w =>
    g * lookupZ ((ups m).zip row) (min u w, max u w)

/-- The variable owning coordinate `i`, and `j = i - off`. -/
def varOf (R : Raw) (i : Nat) : Option (VarB × Nat) :=
  (R.vars.find? fun v => v.off ≤ i && i < v.off + v.S.length).map fun v => (v, i - v.off)

/-- **Check D1 at coordinate `i`:** every block coefficient equals the recomputed one. -/
def checkCoord (R : Raw) (phA : Array Int) (outsA : Array OutB) (i : Nat) : Bool :=
  match varOf R i with
  | none => false
  | some (v, j) =>
    let G := gArr v j
    let T4 := t4Arr R phA v (t0Arr v G)
    let XI := xInv R v
    let rows := R.Fc.getD i []
    (List.range outsA.size).all fun k =>
      let o := outsA.getD k default
      let F := if o.cut = 0 then fOut0 v G o else fOut3 R v T4 XI o
      F == fData R rows k o

/-- **Check D1 on the coordinates `a ≤ i < b`.** -/
def checkRange (R : Raw) (a b : Nat) : Bool :=
  let phA := flatOf R.phiNum 23 23
  let outsA := R.outs.toArray
  (List.range' a (b - a)).all (checkCoord R phA outsA)

end NPT.CP3.D1
