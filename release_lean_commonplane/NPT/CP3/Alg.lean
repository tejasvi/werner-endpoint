/-
NPT.CP3.Alg — the star algebras of the common-plane relaxation.

Four replicas of five factors: sites `l < 4` of dimension 3 and the auxiliary qubit `l = 4`. At a cut `S` the
algebra `A'_S` is spanned by Kronecker products whose site factors are the partially transposed permutation
operators `VG S p` and whose auxiliary factor is an arbitrary matrix (no twirl on the auxiliary factor). The
partial transpose on replica 3 is the entry rule 1 of `NPT.Cert.RuleData` (positions `0 1 2 7 | 4 5 6 3`, cut 8);
it maps `A'_0` onto `A'_8` and Hilbert–Schmidt projections onto projections. With Lemma P (`condexp_posSemidef`)
this gives positivity of the projected moment operator and of its partial transpose.
-/
import NPT.Cert.RuleData
import NPT.Cert.CondExp
import NPT.Cert.Sem

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.CP3

/-- Local dimensions: sites `l < 4` have dimension 3, the auxiliary factor `l = 4` dimension 2. -/
abbrev nfC : Fin 5 → ℕ := nf 4 3

/-- Global four-replica index of the common-plane relaxation. -/
abbrev GC := GI nfC

/-- Local matrices of the factors. -/
abbrev LocM := (l : Fin 5) → Matrix (Dig (nfC l) 4) (Dig (nfC l) 4) ℂ

/-- Generators at cut `S`: Kronecker products with site factors `VG S (w l)` and an arbitrary auxiliary factor. -/
def genA (S : ℕ) : Set (Matrix GC GC ℂ) :=
  {M | ∃ (w : Fin 5 → Fin 24) (F : LocM), (∀ l : Fin 5, l.val < 4 → F l = VG ℂ (nfC l) S (w l)) ∧ M = kron F}

/-- `A'_S = span (genA S)`. -/
def spanA (S : ℕ) : Submodule ℂ (Matrix GC GC ℂ) := Submodule.span ℂ (genA S)

lemma kron_mem_spanA {S : ℕ} (w : Fin 5 → Fin 24) {F : LocM}
    (hF : ∀ l : Fin 5, l.val < 4 → F l = VG ℂ (nfC l) S (w l)) : kron F ∈ spanA S :=
  Submodule.subset_span ⟨w, F, hF, rfl⟩

lemma genA_mul {S : ℕ} (hS : S ∈ cutsUsed) {x y : Matrix GC GC ℂ} (hx : x ∈ genA S) (hy : y ∈ genA S) :
    x * y ∈ spanA S := by
  obtain ⟨w, F, hF, rfl⟩ := hx
  obtain ⟨w', F', hF', rfl⟩ := hy
  rw [kron_mul]
  set c : Fin 5 → ℂ := fun l => if l.val < 4 then (nfC l : ℂ) ^ eD (ptabOf S) (w l) (w' l) else 1 with hc
  set G : LocM := fun l => if l.val < 4 then VG ℂ (nfC l) S (rD (ptabOf S) (w l) (w' l)) else F l * F' l with hG
  have hFG : (fun l => F l * F' l) = fun l => c l • G l := by
    funext l
    by_cases h : l.val < 4
    · simp only [hc, hG, if_pos h, hF l h, hF' l h]
      exact VG_mul hS (w l) (w' l)
    · simp only [hc, hG, if_neg h, one_smul]
  rw [hFG, kron_smul]
  refine Submodule.smul_mem _ _ (kron_mem_spanA (fun l => rD (ptabOf S) (w l) (w' l)) fun l h => ?_)
  simp only [hG, if_pos h]

lemma spanA_mul_mem {S : ℕ} (hS : S ∈ cutsUsed) {x y : Matrix GC GC ℂ} (hx : x ∈ spanA S) (hy : y ∈ spanA S) :
    x * y ∈ spanA S :=
  span_mul_mem _ (fun _ ha _ hb => genA_mul hS ha hb) hx hy

lemma spanA_star_mem {S : ℕ} (hS : S < 16) {x : Matrix GC GC ℂ} (hx : x ∈ spanA S) : xᴴ ∈ spanA S := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, F, hF, rfl⟩ := ha
    rw [kron_conjTranspose]
    refine kron_mem_spanA (fun l => pinvIdx (w l)) fun l h => ?_
    simp only [hF l h]
    exact VG_conjTranspose hS (w l)
  | zero => simp
  | add x z _ _ h1 h2 => rw [conjTranspose_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [conjTranspose_smul]; exact Submodule.smul_mem _ _ h

lemma one_mem_spanA {S : ℕ} (hS : S < 16) : (1 : Matrix GC GC ℂ) ∈ spanA S := by
  rw [← kron_one]
  refine kron_mem_spanA (fun _ => 0) fun l _ => ?_
  exact (VG_zero hS).symm

/-- The star algebra `A'_S`. -/
def AA (S : ℕ) (hS : S ∈ cutsUsed) : StarSubalgebra ℂ (Matrix GC GC ℂ) :=
  { (spanA S).toSubalgebra (one_mem_spanA (cutsUsed_lt hS)) (fun _ _ hx hy => spanA_mul_mem hS hx hy) with
    star_mem' := fun hx => by
      simpa [Matrix.star_eq_conjTranspose] using spanA_star_mem (cutsUsed_lt hS) hx }

lemma mem_AA {S : ℕ} (hS : S ∈ cutsUsed) {x : Matrix GC GC ℂ} : x ∈ AA S hS ↔ x ∈ spanA S := Iff.rfl

lemma cut0 : (0 : ℕ) ∈ cutsUsed := by decide
lemma cut8 : (8 : ℕ) ∈ cutsUsed := by decide

/-! ### Projections, Lemma P and the bimodule property -/

/-- **Lemma P** for `A'_S`: the projection of a PSD matrix is PSD. -/
theorem psd_of_isProj {S : ℕ} (hS : S ∈ cutsUsed) {X Y : Matrix GC GC ℂ} (hX : X.PosSemidef)
    (hY : IsProj (spanA S) X Y) : Y.PosSemidef :=
  condexp_posSemidef (AA S hS) hX hY.1 hY.2

/-- Left multiplication by an element of `A'_S` commutes with the projection. -/
theorem isProj_mul_left {S : ℕ} (hS : S ∈ cutsUsed) {X Y A : Matrix GC GC ℂ} (hY : IsProj (spanA S) X Y)
    (hA : A ∈ spanA S) : IsProj (spanA S) (A * X) (A * Y) := by
  refine ⟨spanA_mul_mem hS hA hY.1, fun Z hZ => ?_⟩
  have hAZ : Aᴴ * Z ∈ spanA S := spanA_mul_mem hS (spanA_star_mem (cutsUsed_lt hS) hA) hZ
  have e : ∀ M : Matrix GC GC ℂ, (Zᴴ * (A * M)).trace = ((Aᴴ * Z)ᴴ * M).trace := by
    intro M; rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, e, hY.2 _ hAZ]

/-- Right multiplication by an element of `A'_S` commutes with the projection. -/
theorem isProj_mul_right {S : ℕ} (hS : S ∈ cutsUsed) {X Y A : Matrix GC GC ℂ} (hY : IsProj (spanA S) X Y)
    (hA : A ∈ spanA S) : IsProj (spanA S) (X * A) (Y * A) := by
  refine ⟨spanA_mul_mem hS hY.1 hA, fun Z hZ => ?_⟩
  have hZA : Z * Aᴴ ∈ spanA S := spanA_mul_mem hS hZ (spanA_star_mem (cutsUsed_lt hS) hA)
  have e : ∀ M : Matrix GC GC ℂ, (Zᴴ * (M * A)).trace = ((Z * Aᴴ)ᴴ * M).trace := by
    intro M
    rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc]
  rw [e, e, hY.2 _ hZA]

/-! ### The partial transpose on replica 3 (entry rule 1) -/

lemma rule1_ok : RuleOK 1 := ruleTab_ok ⟨1, by decide⟩
lemma rcut1 : rcut 1 = 8 := by decide
lemma rfq1 : ∀ p : Fin 24, rfq 1 p = p := by decide
lemma rbq1 : ∀ q : Fin 24, rbq 1 q = q := by decide

/-- `M ↦ M^{Γ₃}`: partial transpose of replica 3 on every factor. -/
def gam3 (M : Matrix GC GC ℂ) : Matrix GC GC ℂ := ruleG (rkp 1) (rlp 1) M

/-- The inverse rule (also the partial transpose on replica 3). -/
def gam3i (M : Matrix GC GC ℂ) : Matrix GC GC ℂ := ruleG rule1_ok.pos.ikp rule1_ok.pos.ilp M

lemma gam3_genA {x : Matrix GC GC ℂ} (hx : x ∈ genA 0) : gam3 x ∈ genA 8 := by
  obtain ⟨w, F, hF, rfl⟩ := hx
  refine ⟨w, fun l => ruleL (rkp 1) (rlp 1) (F l), fun l h => ?_, ruleG_kron _ _ _⟩
  simp only [hF l h]
  rw [rule1_ok.ruleL_V (w l), rcut1, rfq1]

lemma gam3i_genA {x : Matrix GC GC ℂ} (hx : x ∈ genA 8) : gam3i x ∈ genA 0 := by
  obtain ⟨w, F, hF, rfl⟩ := hx
  refine ⟨w, fun l => ruleL rule1_ok.pos.ikp rule1_ok.pos.ilp (F l), fun l h => ?_, ruleG_kron _ _ _⟩
  simp only [hF l h]
  have := rule1_ok.ruleL_inv_V (n := nfC l) (w l)
  rw [rcut1, rbq1] at this
  exact this

lemma gam3_mem {Y : Matrix GC GC ℂ} (hY : Y ∈ spanA 0) : gam3 Y ∈ spanA 8 := by
  induction hY using Submodule.span_induction with
  | mem a ha => exact Submodule.subset_span (gam3_genA ha)
  | zero => exact Submodule.zero_mem _
  | add x z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c x _ h' => exact Submodule.smul_mem _ c h'

lemma gam3i_mem {N : Matrix GC GC ℂ} (hN : N ∈ spanA 8) : gam3i N ∈ spanA 0 := by
  induction hN using Submodule.span_induction with
  | mem a ha => exact Submodule.subset_span (gam3i_genA ha)
  | zero => exact Submodule.zero_mem _
  | add x z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c x _ h' => exact Submodule.smul_mem _ c h'

/-- `Γ₃` maps the projection onto `A'_0` to the projection onto `A'_8`. -/
theorem isProj_gam3 {X Y : Matrix GC GC ℂ} (hY : IsProj (spanA 0) X Y) :
    IsProj (spanA 8) (gam3 X) (gam3 Y) :=
  hY.map (ruleGL (rkp 1) (rlp 1)) (fun _ h => gam3_mem h)
    (fun N hN => ⟨gam3i N, gam3i_mem hN, fun Z => rule1_ok.pos.trace_ruleG N Z⟩)

/-- Positivity of the partially transposed projection, from positivity of `X^{Γ₃}`. -/
theorem psd_gam3_of_isProj {X Y : Matrix GC GC ℂ} (hY : IsProj (spanA 0) X Y) (hX : (gam3 X).PosSemidef) :
    (gam3 Y).PosSemidef :=
  psd_of_isProj cut8 hX (isProj_gam3 hY)

end NPT.CP3
