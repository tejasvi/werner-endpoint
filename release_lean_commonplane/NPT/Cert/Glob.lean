/-
NPT.Cert.Glob — global word operators on four replicas of a multi-factor system, and the walled-Brauer
star algebras `A_S = span {V_w^{Γ_S}}` (one per cut `S`), for an arbitrary finite factor type `L` with
local dimensions `nf : L → ℕ`.
-/
import NPT.Cert.BrauerData
import NPT.Cert.CondExp

open Matrix BigOperators Finset NPT.Brauer

namespace NPT.Cert

/-! ### Kronecker products over factors -/

section Kron

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Kronecker product over the factors `l : L`. -/
def kron {ι κ : L → Type*} (A : (l : L) → Matrix (ι l) (κ l) ℂ) :
    Matrix ((l : L) → ι l) ((l : L) → κ l) ℂ :=
  fun i j => ∏ l, A l (i l) (j l)

variable {ι κ μ : L → Type*} [∀ l, Fintype (κ l)] [∀ l, DecidableEq (κ l)]

lemma kron_mul (A : (l : L) → Matrix (ι l) (κ l) ℂ) (B : (l : L) → Matrix (κ l) (μ l) ℂ) :
    kron A * kron B = kron (fun l => A l * B l) := by
  ext i j
  simp only [kron, mul_apply]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.prod_mul_distrib]

lemma kron_smul (c : L → ℂ) (A : (l : L) → Matrix (ι l) (κ l) ℂ) :
    kron (fun l => c l • A l) = (∏ l, c l) • kron A := by
  ext i j
  simp only [kron, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

lemma kron_conjTranspose (A : (l : L) → Matrix (ι l) (κ l) ℂ) :
    (kron A)ᴴ = kron (fun l => (A l)ᴴ) := by
  ext i j
  simp only [kron, conjTranspose_apply, star_prod]

lemma kron_one [∀ l, DecidableEq (ι l)] : kron (fun l => (1 : Matrix (ι l) (ι l) ℂ)) = 1 := by
  ext i j
  simp only [kron, one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨l, hl⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ l) (ite_eq_right hl)

end Kron

/-! ### Local facts: transposes and the identity -/

lemma SelOp_conjTranspose {n m : ℕ} (α β : Fin m → Fin m) :
    (SelOp ℂ n α β)ᴴ = SelOp ℂ n β α := by
  unfold SelOp
  rw [conjTranspose_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [conjTranspose_single, star_one]

lemma SelOp_id {n m : ℕ} : SelOp ℂ n (id : Fin m → Fin m) id = 1 := by
  ext i j
  simp only [SelOp, Matrix.sum_apply, single_apply, one_apply, Function.comp_id]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun x _ => by
      by_cases hx : i = x
      · subst hx; simp [h]
      · rw [ite_eq_right]
        rintro ⟨h1, -⟩
        exact hx h1.symm

lemma sel_inv_ok : ∀ S : Fin 16, ∀ p : Fin 24, ∀ s : Fin 4,
    bSel S.val p s = pinvf p (aSel S.val (pinvIdx p) s) ∧
    aSel S.val p s = pinvf p (bSel S.val (pinvIdx p) s) := by decide +kernel

lemma VG_conjTranspose {n S : ℕ} (hS : S < 16) (p : Fin 24) :
    (VG ℂ n S p)ᴴ = VG ℂ n S (pinvIdx p) := by
  unfold VG
  rw [SelOp_conjTranspose, ← SelOp_reindex (permE p).symm (aSel S (pinvIdx p))]
  congr 1
  · funext s; exact (sel_inv_ok ⟨S, hS⟩ p s).1
  · funext s; exact (sel_inv_ok ⟨S, hS⟩ p s).2

lemma sel_one_ok : ∀ S : Fin 16, ∀ s : Fin 4, aSel S.val 0 s = s ∧ bSel S.val 0 s = s := by
  decide +kernel

lemma VG_zero {n S : ℕ} (hS : S < 16) : VG ℂ n S 0 = 1 := by
  unfold VG
  have ha : aSel S 0 = id := funext fun s => (sel_one_ok ⟨S, hS⟩ s).1
  have hb : bSel S 0 = id := funext fun s => (sel_one_ok ⟨S, hS⟩ s).2
  rw [ha, hb, SelOp_id]

/-! ### Cut tables -/

/-- The product table of each cut used. -/
def ptabOf : ℕ → PTab
  | 0 => ptab0
  | 1 => ptab1
  | 4 => ptab4
  | 8 => ptab8
  | 3 => ptab3
  | 5 => ptab5
  | 12 => ptab12
  | _ => []

/-- Cuts used (bit masks). -/
def cutsUsed : List ℕ := [0, 1, 4, 8, 3, 5, 12]

lemma cutsUsed_lt {S : ℕ} (hS : S ∈ cutsUsed) : S < 16 := by
  simp only [cutsUsed, List.mem_cons, List.not_mem_nil, or_false] at hS
  omega

lemma ptabOf_ok {S : ℕ} (hS : S ∈ cutsUsed) (p q : Fin 24) : PCertOK S (ptabOf S) p q := by
  simp only [cutsUsed, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ptab0_ok p q
  · exact ptab1_ok p q
  · exact ptab4_ok p q
  · exact ptab8_ok p q
  · exact ptab3_ok p q
  · exact ptab5_ok p q
  · exact ptab12_ok p q

/-- Local product rule for the cuts used. -/
lemma VG_mul {n S : ℕ} (hS : S ∈ cutsUsed) (p q : Fin 24) :
    VG ℂ n S p * VG ℂ n S q = ((n : ℂ) ^ eD (ptabOf S) p q) • VG ℂ n S (rD (ptabOf S) p q) :=
  VG_mul_of_ok (ptabOf_ok hS p q)

/-! ### Global word operators and the algebras `A_S` -/

section Global

variable {L : Type*} [Fintype L] [DecidableEq L] (nf : L → ℕ)

/-- Global four-replica index (factor-major): `i l r` = digit of replica `r` at factor `l`. -/
abbrev GI := (l : L) → Dig (nf l) 4

/-- Global word operator `V_w^{Γ_S} = ⊗_l VG S (w l)`. -/
def VW (S : ℕ) (w : L → Fin 24) : Matrix (GI nf) (GI nf) ℂ := kron fun l => VG ℂ (nf l) S (w l)

variable {nf}

lemma VW_mul {S : ℕ} (hS : S ∈ cutsUsed) (w u : L → Fin 24) :
    VW nf S w * VW nf S u =
      (∏ l, ((nf l : ℂ) ^ eD (ptabOf S) (w l) (u l))) • VW nf S (fun l => rD (ptabOf S) (w l) (u l)) := by
  unfold VW
  rw [kron_mul, ← kron_smul]
  congr 1
  funext l
  exact VG_mul hS (w l) (u l)

lemma VW_conjTranspose {S : ℕ} (hS : S < 16) (w : L → Fin 24) :
    (VW nf S w)ᴴ = VW nf S (fun l => pinvIdx (w l)) := by
  unfold VW
  rw [kron_conjTranspose]
  congr 1
  funext l
  exact VG_conjTranspose hS (w l)

lemma VW_zero {S : ℕ} (hS : S < 16) : VW nf S (fun _ => 0) = 1 := by
  unfold VW
  simp only [VG_zero hS]
  exact kron_one

/-- `span {V_w^{Γ_S}}`. -/
def spanS (S : ℕ) : Submodule ℂ (Matrix (GI nf) (GI nf) ℂ) := Submodule.span ℂ (Set.range (VW nf S))

lemma VW_mem (S : ℕ) (w : L → Fin 24) : VW nf S w ∈ spanS (nf := nf) S :=
  Submodule.subset_span ⟨w, rfl⟩

/-- A span of a set closed under products (into the span) is closed under products. -/
lemma span_mul_mem {A : Type*} [Ring A] [Algebra ℂ A] (G : Set A)
    (hG : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ Submodule.span ℂ G) {x y : A}
    (hx : x ∈ Submodule.span ℂ G) (hy : y ∈ Submodule.span ℂ G) : x * y ∈ Submodule.span ℂ G := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb => exact hG a ha b hb
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

lemma spanS_mul_mem {S : ℕ} (hS : S ∈ cutsUsed) {x y : Matrix (GI nf) (GI nf) ℂ}
    (hx : x ∈ spanS (nf := nf) S) (hy : y ∈ spanS (nf := nf) S) : x * y ∈ spanS (nf := nf) S := by
  refine span_mul_mem _ ?_ hx hy
  rintro _ ⟨w, rfl⟩ _ ⟨u, rfl⟩
  rw [VW_mul hS]
  exact Submodule.smul_mem _ _ (VW_mem S _)

lemma spanS_star_mem {S : ℕ} (hS : S < 16) {x : Matrix (GI nf) (GI nf) ℂ}
    (hx : x ∈ spanS (nf := nf) S) : xᴴ ∈ spanS (nf := nf) S := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, rfl⟩ := ha
    rw [VW_conjTranspose hS]
    exact VW_mem S _
  | zero => simp
  | add x z _ _ h1 h2 => rw [conjTranspose_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [conjTranspose_smul]; exact Submodule.smul_mem _ _ h

lemma one_mem_spanS {S : ℕ} (hS : S < 16) : (1 : Matrix (GI nf) (GI nf) ℂ) ∈ spanS (nf := nf) S := by
  rw [← VW_zero (nf := nf) hS]
  exact VW_mem S _

/-- The walled-Brauer star algebra `A_S` of a cut. -/
def AS (S : ℕ) (hS : S ∈ cutsUsed) : StarSubalgebra ℂ (Matrix (GI nf) (GI nf) ℂ) :=
  { (spanS (nf := nf) S).toSubalgebra (one_mem_spanS (cutsUsed_lt hS))
      (fun _ _ hx hy => spanS_mul_mem hS hx hy) with
    star_mem' := fun hx => by
      simpa [Matrix.star_eq_conjTranspose] using spanS_star_mem (cutsUsed_lt hS) hx }

lemma mem_AS {S : ℕ} (hS : S ∈ cutsUsed) {x : Matrix (GI nf) (GI nf) ℂ} :
    x ∈ AS (nf := nf) S hS ↔ x ∈ spanS (nf := nf) S := Iff.rfl

end Global

/-! ### Block matrices with entries in a star algebra -/

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `(r, s)` block of a block matrix. -/
def blockOf {R : ℕ} (M : Matrix (Fin R × ι) (Fin R × ι) ℂ) (r s : Fin R) : Matrix ι ι ℂ :=
  fun i j => M (r, i) (s, j)

/-- Block matrices all of whose blocks lie in `𝒜` form a star subalgebra. -/
def blockAlg (𝒜 : StarSubalgebra ℂ (Matrix ι ι ℂ)) (R : ℕ) :
    StarSubalgebra ℂ (Matrix (Fin R × ι) (Fin R × ι) ℂ) where
  carrier := {M | ∀ r s, blockOf M r s ∈ 𝒜}
  mul_mem' := by
    intro M N hM hN r s
    have : blockOf (M * N) r s = ∑ t, blockOf M r t * blockOf N t s := by
      ext i j
      simp only [blockOf, mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
    rw [this]
    exact 𝒜.sum_mem fun t _ => 𝒜.mul_mem (hM r t) (hN t s)
  one_mem' := by
    intro r s
    by_cases h : r = s
    · subst h
      have : blockOf (1 : Matrix (Fin R × ι) (Fin R × ι) ℂ) r r = 1 := by
        ext i j; simp [blockOf, one_apply, Prod.ext_iff]
      rw [this]; exact 𝒜.one_mem
    · have : blockOf (1 : Matrix (Fin R × ι) (Fin R × ι) ℂ) r s = 0 := by
        ext i j; simp [blockOf, one_apply, Prod.ext_iff, h]
      rw [this]; exact 𝒜.zero_mem
  add_mem' := by
    intro M N hM hN r s
    have : blockOf (M + N) r s = blockOf M r s + blockOf N r s := rfl
    rw [this]; exact 𝒜.add_mem (hM r s) (hN r s)
  zero_mem' := by
    intro r s
    have : blockOf (0 : Matrix (Fin R × ι) (Fin R × ι) ℂ) r s = 0 := rfl
    rw [this]; exact 𝒜.zero_mem
  algebraMap_mem' := by
    intro c r s
    rw [Algebra.algebraMap_eq_smul_one]
    by_cases h : r = s
    · subst h
      have : blockOf (c • (1 : Matrix (Fin R × ι) (Fin R × ι) ℂ)) r r = c • 1 := by
        ext i j; simp [blockOf, one_apply, Prod.ext_iff]
      rw [this]; exact 𝒜.smul_mem 𝒜.one_mem c
    · have : blockOf (c • (1 : Matrix (Fin R × ι) (Fin R × ι) ℂ)) r s = 0 := by
        ext i j; simp [blockOf, one_apply, Prod.ext_iff, h]
      rw [this]; exact 𝒜.zero_mem
  star_mem' := by
    intro M hM r s
    have : blockOf (star M) r s = star (blockOf M s r) := by
      ext i j; simp [blockOf]
    rw [this]; exact star_mem (hM s r)

end Block

end NPT.Cert
