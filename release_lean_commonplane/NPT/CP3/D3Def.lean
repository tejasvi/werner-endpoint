/-
NPT.CP3.D3Def — the local functionals of the objective and of the equality rows in Gram coordinates, and the coordinate
functionals `cobjFlat`, `cEFlat` (flat sums over the box of each variable) that the D3 check compares with the
certificate's `cvec` and `Erow`.

* Sites: `ellO la` is the doubled objective functional `zsObj2 · IFG` (`X ↦ Tr((2I − F₀₃) X)`) on the Gram coordinates
  of label `la`; `ellE q la` is `eqNum[q] / eqDen` (the coefficient of the three-replica word `q` after deleting replica
  0) on the same coordinates. Entry `(a, b)` is coordinate `siteOff[0][la] + a · d + b`.
* Aux: `ellAO k li a b` and `ellAE u li a b` are the functionals on the unit `(blk a, blk b)` of block `li`: `zaA`,
  `zaB`, `2 zaAB` for the objective (`ca`, `cb`, `2 cab`) and row `u` of the Stiefel contrast `auxMst`.
* `cobjFlat k v j = |cosets v| Σ_{a,b} (W S_j Wᵀ)[a,b] Π_l ellO(st_l)[a_l,b_l] · ellAO k (ai)[a_4,b_4]`;
  `cEFlat e v j = Σ_c Σ_{a,b} (W S_j Wᵀ)[a,b] Π_m ellE(q[σ_c m], st_m)[a_m,b_m] · ellAE u (ai)[a_4,b_4]`, where
  `erows[e] = qi · 70 + u`, `q = sortedQ[qi]` and `σ_c m = cosets[c].2[m]`; digits are `digL dims`.
-/
import NPT.CP3.Cosets

open Matrix BigOperators Finset

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-- Doubled objective site functional on the 23 cut-() site Gram coordinates: `zsObj2 · IFG`. -/
def zr2 (t : ℕ) : ℚ :=
  (∑ p ∈ Finset.range 24, (zsObj2.getD p 0 : ℚ) * ((ifgNum.getD p []).getD t 0 : ℚ)) / ifgDen

/-- Gram coordinate of entry `(a, b)` of site label `la` (cut `()`). -/
def scoord (la a b : ℕ) : ℕ := (siteOff.getD 0 []).getD la 0 + a * sdim 0 la + b

/-- Objective site functional of label `la`, entry `(a, b)`. -/
def ellO (la a b : ℕ) : ℚ := zr2 (scoord la a b)

/-- Equality site functional of word `q` (index into `permL3`) and label `la`, entry `(a, b)`. -/
def ellE (q la a b : ℕ) : ℚ := ((eqNum.getD q []).getD (scoord la a b) 0 : ℚ) / eqDen

/-- Index of the aux unit `(x, y)` in `words`. -/
def unitIdx (x y : ℕ) : ℕ := words.idxOf (x, y)

/-- Unit index of entry `(a, b)` of aux block `li` (cut `()`). -/
def aunit (li a b : ℕ) : ℕ := unitIdx ((ablk 0 li).getD a 0) ((ablk 0 li).getD b 0)

/-- Objective aux functionals on units: `ca` (`zaA`), `cb` (`zaB`), `2 cab` (`2 zaAB`). -/
def zaK (k e : ℕ) : ℚ :=
  match k with
  | 0 => (zaA.getD e 0 : ℚ)
  | 1 => (zaB.getD e 0 : ℚ)
  | _ => 2 * (zaAB.getD e 0 : ℚ)

/-- Objective aux functional `k` of block `li`, entry `(a, b)`. -/
def ellAO (k li a b : ℕ) : ℚ := zaK k (aunit li a b)

/-- Equality aux functional of unit `u` (row `u` of the Stiefel contrast on units) of block `li`, entry `(a, b)`. -/
def ellAE (u li a b : ℕ) : ℚ := ((auxMst.getD u []).getD (aunit li a b) 0 : ℚ)

/-- The Gram form `W S_j Wᵀ` of variable `v` (flat, rational). -/
def Gflat (v j : ℕ) : Fin (nV v) → Fin (nV v) → ℚ := Wq v * Sq v j * (Wq v)ᵀ

/-- **Objective coordinate functional** `k` of `(v, j)`. -/
def cobjFlat (k v j : ℕ) : ℚ :=
  (ncos v : ℚ) * ∑ a : Fin (nV v), ∑ b : Fin (nV v), Gflat v j a b *
    ((∏ l ∈ Finset.range 4, ellO ((vb v).st.getD l 0) (digL (vb v).dims l a) (digL (vb v).dims l b)) *
      ellAO k (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b))

/-- Word tuple and unit of equality row `e` (`erows[e] = qi · 70 + u`). -/
def eQ (e : ℕ) : List ℕ := sortedQ.getD (erows.getD e 0 / 70) []
def eU (e : ℕ) : ℕ := erows.getD e 0 % 70

/-- **Equality coordinate functional** of row `e` at `(v, j)` (sum over the cosets). -/
def cEFlat (e v j : ℕ) : ℚ :=
  ∑ c ∈ Finset.range (ncos v), ∑ a : Fin (nV v), ∑ b : Fin (nV v), Gflat v j a b *
    ((∏ m ∈ Finset.range 4, ellE ((eQ e).getD ((cosE v c).2.getD m m) 0) ((vb v).st.getD m 0)
        (digL (vb v).dims m a) (digL (vb v).dims m b)) *
      ellAE (eU e) (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b))

end NPT.CP3.Inst
