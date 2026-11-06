/-
NPT.CP3.Inst — the tuple data of the checked certificate (`NPT.CP3.Sem.D0Facts`) as padded `TupleData`.

For a sorted cut-() tuple `v` the flat data (`Wq`, `Wl`, `Bq`, `Sq`, `coefq`, the stabilizer list) are padded to the
Gram index `MI` (`PadB`). The finite facts that tie the flat and padded forms together (`BoxOK`, the action of the
stabilizer on flat positions, the stabilizer fixing the tuple) are decided per tuple; `bridge_ok` collects them.
-/
import NPT.CP3.ChecksD0
import NPT.CP3.PadB
import NPT.CP3.Assemble

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Sem NPT.CP3.Chk

/-- True dimensions of tuple `v` (`[d_st0, d_st1, d_st2, d_st3, auxdim]`). -/
def dimsF (v : ℕ) : Fin 5 → ℕ := fun l => (vb v).dims.getD l.val 0

/-- The tuple of `v`: site labels `st`, auxiliary block `ai`. -/
def tupF (v : ℕ) : Fin 5 → Fin 5 := fun l => Fin.ofNat 5 (if l.val < 4 then (vb v).st.getD l.val 0 else (vb v).ai)

/-- The `t`-th stabilizer element of `v` as a site permutation. -/
def σof (v t : ℕ) : Equiv.Perm (Fin 4) := permE (Fin.ofNat 24 ((dv v).stab.getD t 0))

/-- Its action on flat positions (`permRow`; identity where `permRow` would leave the range). -/
def πof (v t : ℕ) (a : Fin (nV v)) : Fin (nV v) :=
  if h : permRow (vb v).dims ((dv v).stab.getD t 0) a.val < nV v then ⟨_, h⟩ else a

/-- Rational matrices as complex matrices. -/
noncomputable def cq' {ι κ : Type*} (M : Matrix ι κ ℚ) : Matrix ι κ ℂ := M.map fun q => (q : ℂ)

lemma cq'_mul {ι κ μ : Type*} [Fintype κ] (A : Matrix ι κ ℚ) (B : Matrix κ μ ℚ) : cq' (A * B) = cq' A * cq' B := by
  ext i j; simp [cq', Matrix.mul_apply]

lemma cq'_one {ι : Type*} [DecidableEq ι] : cq' (1 : Matrix ι ι ℚ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [cq', Matrix.one_apply, h]

/-- The finite bridge facts of tuple `v` (decided per tuple). -/
structure BridgeOK (v : ℕ) : Prop where
  box : BoxOK (dimsF v) (nV v)
  perm : ∀ t < (dv v).stab.length, ∀ μ : MI,
    flatPos (dimsF v) (n := nV v) (permMI (σof v t) μ) = (flatPos (dimsF v) (n := nV v) μ).map (πof v t)
  prow : ∀ t < (dv v).stab.length, ∀ a < nV v, permRow (vb v).dims ((dv v).stab.getD t 0) a < nV v
  fix : ∀ t < (dv v).stab.length, (fun l => tupF v (sigHat (σof v t) l)) = tupF v
  stab_pos : (dv v).stab.length ≠ 0

/-- The bridge facts as a decidable conjunction (for chunked kernel decisions). -/
def BridgeB (v : ℕ) : Prop :=
  BoxOK (dimsF v) (nV v) ∧
  (∀ t < (dv v).stab.length, ∀ μ : MI,
    flatPos (dimsF v) (n := nV v) (permMI (σof v t) μ) = (flatPos (dimsF v) (n := nV v) μ).map (πof v t)) ∧
  (∀ t < (dv v).stab.length, ∀ a < nV v, permRow (vb v).dims ((dv v).stab.getD t 0) a < nV v) ∧
  (∀ t < (dv v).stab.length, (fun l => tupF v (sigHat (σof v t) l)) = tupF v) ∧
  (dv v).stab.length ≠ 0

instance (v : ℕ) : Decidable (BridgeB v) := by unfold BridgeB; infer_instance

lemma bridgeOK_of (v : ℕ) (h : BridgeB v) : BridgeOK v := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Padded `W`. -/
noncomputable def Wc (v : ℕ) : Matrix MI (Fin (mV v)) ℂ := padR (dimsF v) (n := nV v) (cq' (Wq v))
/-- Padded `W⁺`. -/
noncomputable def Wpc (v : ℕ) : Matrix (Fin (mV v)) MI ℂ := padC (dimsF v) (n := nV v) (cq' (Wl v))

lemma hWp (v : ℕ) (hb : BridgeOK v) (hd : D0Facts v) : Wpc v * Wc v = 1 := by
  unfold Wpc Wc
  rw [hWp_of_flat hb.box (cq' (Wq v)) (cq' (Wl v))]
  rw [← cq'_mul, hd.1, cq'_one]

lemma hflat (v t : ℕ) (hb : BridgeOK v) (hd : D0Facts v) (ht : t < (dv v).stab.length) (a : Fin (nV v))
    (j : Fin (mV v)) : cq' (Wq v) (πof v t a) j = (cq' (Wq v) * cq' (Bq v t)) a j := by
  have hlt := hb.prow t ht a.val a.isLt
  have hπ : πof v t a = ⟨_, hlt⟩ := dif_pos hlt
  rw [hπ, ← cq'_mul, ← hd.2.1 t ht]
  simp only [cq', Matrix.map_apply, Pq, Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨_, hlt⟩]
  · simp
  · intro b _ hb'
    rw [if_neg (fun h => hb' (Fin.ext h.symm))]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

lemma hB (v t : ℕ) (hb : BridgeOK v) (hd : D0Facts v) (ht : t < (dv v).stab.length) :
    Qperm (σof v t) * Wc v = Wc v * cq' (Bq v t) := by
  unfold Wc
  exact hB_of_flat (σof v t) (πof v t) (hb.perm t ht) (cq' (Wq v)) (cq' (Bq v t)) (hflat v t hb hd ht)

/-! ### The span certificate in the form of `stab_coord` -/

lemma cq'_transpose {ι κ : Type*} (A : Matrix ι κ ℚ) : cq' Aᵀ = (cq' A)ᵀ := rfl

lemma cq'_add {ι κ : Type*} (A B : Matrix ι κ ℚ) : cq' (A + B) = cq' A + cq' B := by
  ext i j; simp [cq']

lemma cq'_smul {ι κ : Type*} (q : ℚ) (A : Matrix ι κ ℚ) : cq' (q • A) = (q : ℂ) • cq' A := by
  ext i j; simp [cq']

lemma cq'_sum {ι κ α : Type*} (s : Finset α) (f : α → Matrix ι κ ℚ) : cq' (∑ x ∈ s, f x) = ∑ x ∈ s, cq' (f x) := by
  ext i j; simp [cq', Matrix.sum_apply]

/-- The symmetric unit of `Coord` as the cast of the data's `Eu`. -/
lemma symU_eq_Eu {m : ℕ} (a b : Fin m) (hab : a.val < b.val) : symU (K := ℂ) a b = cq' (Eu m a b) := by
  have hne : (a : ℕ) ≠ b := Nat.ne_of_lt hab
  ext x y
  simp only [symU, Matrix.add_apply, single_apply, cq', Matrix.map_apply, Eu, if_neg hne]
  by_cases h1 : a = x <;> by_cases h2 : b = y <;> by_cases h3 : b = x <;> by_cases h4 : a = y <;>
    simp_all [Fin.ext_iff, eq_comm]

lemma symU_diag {m : ℕ} (a : Fin m) : symU (K := ℂ) a a = (2 : ℂ) • cq' (Eu m a a) := by
  ext x y
  simp only [symU, Matrix.add_apply, single_apply, cq', Matrix.map_apply, Eu, if_pos rfl, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h1 : a = x <;> by_cases h2 : a = y <;> simp_all [Fin.ext_iff, eq_comm] <;> ring

lemma symU_comm {K : Type*} [Field K] {m : ℕ} (a b : Fin m) : symU (K := K) a b = symU b a := by
  unfold symU; exact add_comm _ _

/-- Coefficients for `stab_coord`. -/
noncomputable def cc (v : ℕ) (a b : Fin (mV v)) (j : Fin (vb v).S.length) : ℂ :=
  (if a = b then 2 else 1) * ((dv v).stab.length : ℂ) * (coefq v (min a.val b.val) (max a.val b.val) j : ℂ)

lemma span_upper (v : ℕ) (hd : D0Facts v) (a b : Fin (mV v)) (hab : a.val ≤ b.val) :
    ∑ i : Fin (dv v).stab.length, cq' (Bq v i) * cq' (Eu (mV v) a b) * (cq' (Bq v i))ᵀ =
      ((dv v).stab.length : ℂ) • ∑ j : Fin (vb v).S.length, (coefq v a b j : ℂ) • cq' (Sq v j) := by
  have h := hd.2.2.2.1 a b hab b.isLt
  have h' := congrArg cq' h
  rw [cq'_sum, cq'_smul, cq'_sum] at h'
  simp only [cq'_mul, cq'_transpose, cq'_smul] at h'
  rw [Finset.sum_range (fun t => cq' (Bq v t) * cq' (Eu (mV v) a b) * (cq' (Bq v t))ᵀ),
    Finset.sum_range (fun j => (coefq v a b j : ℂ) • cq' (Sq v j))] at h'
  simpa using h'

lemma hc_of_d0 (v : ℕ) (hd : D0Facts v) (a b : Fin (mV v)) :
    ∑ i : Fin (dv v).stab.length, cq' (Bq v i) * symU a b * (cq' (Bq v i))ᵀ =
      ∑ j : Fin (vb v).S.length, cc v a b j • cq' (Sq v j) := by
  rcases lt_trichotomy a.val b.val with hlt | heq | hgt
  · rw [symU_eq_Eu a b hlt, span_upper v hd a b hlt.le, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hab : a ≠ b := fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt hlt)
    simp only [cc, if_neg hab, one_mul, smul_smul, min_eq_left hlt.le, max_eq_right hlt.le]
  · have hab : a = b := Fin.ext heq
    subst hab
    rw [symU_diag]
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    rw [span_upper v hd a a le_rfl, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cc, smul_smul, min_self, max_self, ite_true]
  · rw [symU_comm, symU_eq_Eu b a hgt, span_upper v hd b a hgt.le, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hab : a ≠ b := fun h => absurd (congrArg Fin.val h) (Nat.ne_of_gt hgt)
    simp only [cc, if_neg hab, one_mul, smul_smul, min_eq_right hgt.le, max_eq_left hgt.le]

/-- The `TupleData` of tuple `v`, given its bridge facts, its D0 facts and its bosonic-range fact. -/
noncomputable def mkTuple (P : PadData) (πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ)
    (v : ℕ) (hb : BridgeOK v) (hd : D0Facts v)
    (hK : (Pav πp (tupF v))ᵀ = Wc v * (Wpc v * (Pav πp (tupF v))ᵀ)) : TupleData P πp where
  τ := tupF v
  m := mV v
  W := Wc v
  Wp := Wpc v
  K := Wpc v * (Pav πp (tupF v))ᵀ
  hWp := hWp v hb hd
  hK := hK
  n := (dv v).stab.length
  σs := fun t => σof v t
  hσ := fun t => hb.fix t t.isLt
  B := fun t => cq' (Bq v t)
  hB := fun t => hB v t hb hd t.isLt
  nb := (vb v).S.length
  S := fun j => cq' (Sq v j)
  c := cc v
  hc := hc_of_d0 v hd
  hn := hb.stab_pos
  off := (vb v).off

end NPT.CP3.Inst
