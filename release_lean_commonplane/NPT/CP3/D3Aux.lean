/-
NPT.CP3.D3Aux — the local trace facts of the objective and of the equality rows on the auxiliary factor.

A `Dig 2 4` identity for all `X` gives `TraceAt` on the auxiliary factor (`traceAt_aux`); by linearity it suffices at
the matrix units, where both sides are entries: `G[y, x]` and the data functional at the unit `(x, y)` when `x, y` lie
in the same charge block (`aux_collapse`). The unit identities are kernel checks: the objective factors
`2 Π₀ F₀₃ Π₀`, `2 Π₁ F₀₃ Π₁`, `2 (Π₀ F₀₃ Π₁ + Π₁ F₀₃ Π₀)` against `zaA`, `zaB`, `2 zaAB`, and the Stiefel contrast
`2 E − I₀ ⊗ Tr₀ E` against `auxMst`.
-/
import NPT.CP3.D3Site

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-! ### Transport between the auxiliary factor and `Dig 2 4` -/

lemma not4 : ¬ ((4 : Fin 5).val < 4) := by decide

/-- Auxiliary factor relabelling `Dig (nfC 4) 4 ≃ Dig 2 4`. -/
def digA : Dig (nfC 4) 4 ≃ Dig 2 4 where
  toFun x := Fin.cast (nfC_aux not4) ∘ x
  invFun x := Fin.cast (nfC_aux not4).symm ∘ x
  left_inv x := by funext r; simp
  right_inv x := by funext r; simp

/-- Padded column relabelling `Fin (dpad 4) ≃ Fin 6`. -/
def finA : Fin (dpad 4) ≃ Fin 6 := finCongr (dpad_aux not4)

lemma PD0_M_aux (la : Fin 5) : (PD 0).M 4 la = (MaC 0 la).submatrix digA finA := by
  ext x a
  exact dif_neg not4

lemma VG0_aux (p : Fin 24) : VG ℂ (nfC 4) 0 p = (VG ℂ 2 0 p).submatrix digA digA := by
  ext x y
  simp only [Matrix.submatrix_apply, Phys.SymAux.VG0_apply]
  have key : (digA x = digA y ∘ pinvf p) ↔ x = y ∘ pinvf p :=
    (Function.Injective.comp_left (Fin.cast_injective (nfC_aux not4))).eq_iff
  by_cases h : x = y ∘ pinvf p
  · rw [if_pos h, if_pos (key.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (key.1 h'))]

/-- **Aux trace facts transported**: a `Dig 2 4` identity for all `X` gives `TraceAt` on the auxiliary factor. -/
theorem traceAt_aux (G2 : Matrix (Dig 2 4) (Dig 2 4) ℂ) (ell2 : Fin 5 → Matrix (Fin 6) (Fin 6) ℂ)
    (h : ∀ X2 : Matrix (Dig 2 4) (Dig 2 4) ℂ,
      (G2 * X2).trace = ∑ la : Fin 5, pairing (ell2 la) ((MaC 0 la)ᵀ * X2 * MaC 0 la))
    (X : Matrix (Dig (nfC 4) 4) (Dig (nfC 4) 4) ℂ) :
    TraceAt (PD 0).fam 4 (G2.submatrix digA digA) (fun la => (ell2 la).submatrix finA finA) X := by
  have hX : X = (X.submatrix digA.symm digA.symm).submatrix digA digA := by
    ext a b; simp
  unfold TraceAt
  rw [hX, Matrix.submatrix_mul_equiv, trace_submatrix_equiv, h]
  refine Finset.sum_congr rfl fun la _ => ?_
  have hg : gramLoc (PD 0).fam 4 la ((X.submatrix digA.symm digA.symm).submatrix digA digA) =
      ((MaC 0 la)ᵀ * X.submatrix digA.symm digA.symm * MaC 0 la).submatrix finA finA := by
    show ((PD 0).M 4 la)ᵀ * (X.submatrix digA.symm digA.symm).submatrix digA digA * (PD 0).M 4 la = _
    rw [PD0_M_aux la, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [hg, pairing_submatrix_equiv]

/-- The `Dig 2 4` identity for all `X` from the matrix units. -/
theorem aux_all_of_units (G2 : Matrix (Dig 2 4) (Dig 2 4) ℂ) (ell2 : Fin 5 → Matrix (Fin 6) (Fin 6) ℂ)
    (h : ∀ x y : Dig 2 4, G2 y x = ∑ la : Fin 5, pairing (ell2 la) (fun a b => MaC 0 la x a * MaC 0 la y b))
    (X2 : Matrix (Dig 2 4) (Dig 2 4) ℂ) :
    (G2 * X2).trace = ∑ la : Fin 5, pairing (ell2 la) ((MaC 0 la)ᵀ * X2 * MaC 0 la) := by
  induction X2 using Matrix.induction_on' with
  | h_zero => simp [pairing]
  | h_add A B hA hB =>
    rw [Matrix.mul_add, Matrix.trace_add, hA, hB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [Matrix.mul_add, Matrix.add_mul, pairing_add]
  | h_std_basis x y c =>
    have hs : Matrix.single x y c = c • Matrix.single x y (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    have hgram : ∀ la : Fin 5, (MaC 0 la)ᵀ * Matrix.single x y (1 : ℂ) * MaC 0 la =
        fun a b => MaC 0 la x a * MaC 0 la y b := by
      intro la; ext a b
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply]
      rw [Finset.sum_eq_single y]
      · rw [Finset.sum_eq_single x]
        · simp
        · intro j _ hj
          rw [if_neg (fun h => hj h.1.symm), mul_zero]
        · intro h'; exact absurd (Finset.mem_univ _) h'
      · intro j _ hj
        rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (fun h => hj h.2.symm), mul_zero]), zero_mul]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    have ht : (G2 * Matrix.single x y (1 : ℂ)).trace = G2 y x := by
      rw [Matrix.trace_mul_single]; simp
    rw [hs, Matrix.mul_smul, Matrix.trace_smul, ht, h x y, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, pairing_smul, hgram]

/-! ### Charge blocks -/

/-- Charge block (number of `1` digits) and position of an aux string (cut `()`). -/
def blkOf (z : Dig 2 4) : ℕ := ∑ r : Fin 4, (z r).val
def posOf (z : Dig 2 4) : ℕ := (ablk 0 (blkOf z)).idxOf (Sem.flat z)

lemma blk_lt : ∀ z : Dig 2 4, blkOf z < 5 := by decide
lemma pos_lt : ∀ z : Dig 2 4, posOf z < 6 := by decide

def Bf (z : Dig 2 4) : Fin 5 := ⟨blkOf z, blk_lt z⟩
def Pf (z : Dig 2 4) : Fin 6 := ⟨posOf z, pos_lt z⟩

lemma MaC_mem : ∀ la : Fin 5, ∀ z : Dig 2 4, ∀ a : Fin 6,
    (a.val < (ablk 0 la).length ∧ (ablk 0 la).getD a 0 = Sem.flat z) ↔ (la = Bf z ∧ a = Pf z) := by
  decide +kernel

lemma pos_in : ∀ z : Dig 2 4, posOf z < (ablk 0 (blkOf z)).length := by decide +kernel

lemma MaC_unit (la : Fin 5) (z : Dig 2 4) (a : Fin 6) : MaC 0 la z a = if la = Bf z ∧ a = Pf z then 1 else 0 := by
  unfold MaC
  by_cases h : la = Bf z ∧ a = Pf z
  · have h' := (MaC_mem la z a).2 h
    rw [if_pos h'.1, if_pos h'.2, if_pos h]
  · rw [if_neg h]
    by_cases h1 : a.val < (ablk 0 la).length
    · rw [if_pos h1, if_neg (fun h2 => h ((MaC_mem la z a).1 ⟨h1, h2⟩))]
    · rw [if_neg h1]

/-- **Unit collapse**: the data side at the unit `(x, y)`. -/
theorem aux_collapse (ell2 : Fin 5 → Matrix (Fin 6) (Fin 6) ℂ) (x y : Dig 2 4) :
    ∑ la : Fin 5, pairing (ell2 la) (fun a b => MaC 0 la x a * MaC 0 la y b) =
      if Bf x = Bf y then ell2 (Bf x) (Pf x) (Pf y) else 0 := by
  simp only [pairing, MaC_unit]
  rw [Finset.sum_eq_single (Bf x)]
  · rw [Finset.sum_eq_single (Pf x)]
    · rw [Finset.sum_eq_single (Pf y)]
      · by_cases hxy : Bf x = Bf y
        · simp [hxy]
        · simp [hxy]
      · intro b _ hb
        simp [hb]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => by simp [ha]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro la _ hla
    exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by simp [hla]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/-- Masked `6 × 6` aux matrices of block `la` (cut `()`). -/
noncomputable def mask6 (f : ℕ → ℕ → ℕ → ℂ) (la : Fin 5) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun a b => if a.val < (ablk 0 la).length ∧ b.val < (ablk 0 la).length then f la a b else 0

/-- The unit identity from a decided entry identity. -/
theorem aux_unit_of (G2 : Matrix (Dig 2 4) (Dig 2 4) ℂ) (f : ℕ → ℕ → ℕ → ℂ)
    (h : ∀ x y : Dig 2 4, G2 y x = if blkOf x = blkOf y then f (blkOf x) (posOf x) (posOf y) else 0)
    (x y : Dig 2 4) :
    G2 y x = ∑ la : Fin 5, pairing (mask6 f la) (fun a b => MaC 0 la x a * MaC 0 la y b) := by
  rw [aux_collapse, h x y]
  by_cases hxy : blkOf x = blkOf y
  · have hB : Bf x = Bf y := Fin.ext hxy
    rw [if_pos hxy, if_pos hB]
    unfold mask6
    have hx := pos_in x
    have hy := pos_in y
    rw [hxy] at hx
    rw [if_pos ⟨by show posOf x < _; rw [show (Bf x).val = blkOf y from hxy]; exact hx,
      by show posOf y < _; rw [show (Bf x).val = blkOf y from hxy]; exact hy⟩]
    rfl
  · have hB : ¬ Bf x = Bf y := fun e => hxy (congrArg Fin.val e)
    rw [if_neg hxy, if_neg hB]

/-! ### The objective on the auxiliary factor -/

/-- Integer objective aux factors: `2 Π₀ F₀₃ Π₀`, `2 Π₁ F₀₃ Π₁`, `2 (Π₀ F₀₃ Π₁ + Π₁ F₀₃ Π₀)`. -/
def GAfac (k : ℕ) (z z' : Dig 2 4) : ℤ :=
  match k with
  | 0 => if z 3 = 0 ∧ z' 3 = 0 then 2 else 0
  | 1 => if z 3 = 1 ∧ z' 3 = 1 then 2 else 0
  | _ => if z 3 ≠ z' 3 then 2 else 0

def GAi (k : ℕ) (z z' : Dig 2 4) : ℤ := GAfac k z z' * (if z = z' ∘ pinvf 21 then 1 else 0)

noncomputable def GAc (k : ℕ) : Matrix (Dig 2 4) (Dig 2 4) ℂ := fun z z' => (GAi k z z' : ℂ)

/-- Integer objective aux functionals on units (`zaA`, `zaB`, `2 zaAB`). -/
def zaKi (k e : ℕ) : ℤ :=
  match k with
  | 0 => zaA.getD e 0
  | 1 => zaB.getD e 0
  | _ => 2 * zaAB.getD e 0

lemma zaK_eq (k e : ℕ) : zaK k e = (zaKi k e : ℚ) := by
  unfold zaK zaKi
  rcases k with _ | _ | k <;> push_cast <;> rfl

lemma obj_aux_int : ∀ k : Fin 3, ∀ x y : Dig 2 4,
    GAi k y x = if blkOf x = blkOf y then zaKi k (aunit (blkOf x) (posOf x) (posOf y)) else 0 := by
  decide +kernel

theorem obj_aux2 (k : Fin 3) (X2 : Matrix (Dig 2 4) (Dig 2 4) ℂ) :
    (GAc k * X2).trace = ∑ la : Fin 5,
      pairing (mask6 (fun li a b => ((ellAO k li a b : ℚ) : ℂ)) la) ((MaC 0 la)ᵀ * X2 * MaC 0 la) := by
  refine aux_all_of_units _ _ (aux_unit_of _ _ (fun x y => ?_)) X2
  unfold GAc
  rw [obj_aux_int k x y]
  split_ifs
  · simp [ellAO, zaK_eq]
  · simp

/-! ### The equality rows on the auxiliary factor -/

/-- The aux unit `u` of `words`, as strings. -/
def unitStr (z : ℕ) : Dig 2 4 := fun r => Fin.ofNat 2 (z / 2 ^ (3 - r.val))
def xU (u : ℕ) : Dig 2 4 := unitStr (words.getD u (0, 0)).1
def yU (u : ℕ) : Dig 2 4 := unitStr (words.getD u (0, 0)).2

/-- The coefficient functional of the aux unit `u`. -/
def unitFA (u : ℕ) : Dig 2 4 → Dig 2 4 → ℂ := fun x y => if x = xU u ∧ y = yU u then 1 else 0

lemma stK_int : ∀ u : Fin 70, ∀ x y : Dig 2 4,
    (2 * (if x = xU u ∧ y = yU u then 1 else 0) -
      (if xU u (csl 0) = yU u (csl 0) ∧ x ∘ cord 0 = xU u ∘ cord 0 ∧ y ∘ cord 0 = yU u ∘ cord 0 ∧
        x (csl 0) = y (csl 0) then 1 else 0) : ℤ) =
      if blkOf x = blkOf y then (auxMst.getD u []).getD (aunit (blkOf x) (posOf x) (posOf y)) 0 else 0 := by
  decide +kernel

lemma trace_unitFA (u : ℕ) (X : Matrix (Dig 2 4) (Dig 2 4) ℂ) :
    (Gk (stK (n := 2) (csl 0) (cord 0)) (unitFA u) * X).trace = applyK (stK (csl 0) (cord 0)) X (xU u) (yU u) := by
  rw [trace_Gk]
  rw [Finset.sum_eq_single (xU u)]
  · rw [Finset.sum_eq_single (yU u)]
    · simp [unitFA]
    · intro y _ hy; simp [unitFA, hy]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro x _ hx
    exact Finset.sum_eq_zero fun y _ => by simp [unitFA, hx]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem eq_aux2 (u : Fin 70) (X2 : Matrix (Dig 2 4) (Dig 2 4) ℂ) :
    (Gk (stK (n := 2) (csl 0) (cord 0)) (unitFA u) * X2).trace = ∑ la : Fin 5,
      pairing (mask6 (fun li a b => ((ellAE u li a b : ℚ) : ℂ)) la) ((MaC 0 la)ᵀ * X2 * MaC 0 la) := by
  refine aux_all_of_units _ _ (aux_unit_of _ _ (fun x y => ?_)) X2
  have e : Gk (stK (n := 2) (csl 0) (cord 0)) (unitFA u) y x = stK (csl 0) (cord 0) (xU u) (yU u) x y := by
    unfold Gk
    rw [Finset.sum_eq_single (xU u)]
    · rw [Finset.sum_eq_single (yU u)]
      · simp [unitFA]
      · intro y' _ hy'; simp [unitFA, hy']
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro x' _ hx'
      exact Finset.sum_eq_zero fun y' _ => by simp [unitFA, hx']
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [e]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (stK_int u x y)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_one, Int.cast_zero] at h
  unfold stK idK etK
  rw [h]
  split_ifs
  · simp [ellAE]
  · rfl

end NPT.CP3.Inst
