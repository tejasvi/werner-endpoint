/-
NPT.Cert.SoundPrep — auxiliary facts for the soundness theorem: linearity of the block, rule and kernel
maps over sums, physical blocks are PSD for consistent rules, the objective operator lies in the word
algebra, and class constancy of invariant coefficients.
-/
import NPT.Cert.BlkSign
import NPT.Cert.EqInt
import NPT.Cert.Assembly
import NPT.Cert.SymDefs

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.Cert

variable {k d : ℕ}

/-! ### Linearity over finite sums -/

lemma blockM_sum {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ} {R : ℕ}
    (ri : Fin R → Fin R → ℕ) (fam : Fin R → Fin R → ℕ) {ι : Type*} (s : Finset ι)
    (X : ι → ℕ → Matrix (GI nf) (GI nf) ℂ) :
    blockM ri fam (fun f => ∑ i ∈ s, X i f) = ∑ i ∈ s, blockM ri fam (X i) := by
  ext a b
  simp only [blockM, ruleG, Matrix.sum_apply]

lemma applyG_sum {L : Type*} [Fintype L] [DecidableEq L] {nf mo : L → ℕ}
    (κ : (l : L) → LKer (nf l) (mo l)) {ι : Type*} (s : Finset ι) (X : ι → Matrix (GI nf) (GI nf) ℂ) :
    applyG κ (∑ i ∈ s, X i) = ∑ i ∈ s, applyG κ (X i) :=
  map_sum (applyGL κ) X s

/-! ### Physical blocks -/

/-- Row pattern `r` of a type as a code function. -/
def patOf (t : TypeD) (r : ℕ) (s : Fin 4) : Fin 4 := Fin.ofNat 4 ((t.pat.getD r []).getD s.val 0)

/-- A type whose entry rules are verified rules consistent with its row patterns has PSD physical blocks. -/
theorem blockM_phys_psd {R : ℕ} (t : TypeD) (ri : Fin R → Fin R → ℕ) (fam : Fin R → Fin R → ℕ)
    (hok : ∀ r s, RuleOK (ri r s))
    (hcons : ∀ r s, Phys.Consistent (fam r s) (patOf t r) (patOf t s) (rkp (ri r s)) (rlp (ri r s)))
    (a b : Phys.V1 k d → ℂ) :
    (blockM ri fam (fun f => Phys.Xf f a b)).PosSemidef := by
  have e : blockM ri fam (fun f => Phys.Xf f a b) =
      vecMulVec (fun x : Fin R × GI (nf k d) => Phys.patVec (patOf t x.1) a b x.2)
        (star fun x : Fin R × GI (nf k d) => Phys.patVec (patOf t x.1) a b x.2) := by
    ext x y
    simp only [blockM]
    rw [show rkp (ri x.1 y.1) = (hok x.1 y.1).pos.kp from rfl,
      show rlp (ri x.1 y.1) = (hok x.1 y.1).pos.lp from rfl,
      Phys.phys_rule (hok x.1 y.1).pos (hcons x.1 y.1) a b]
    simp [vecMulVec_apply]
  rw [e]
  exact posSemidef_vecMulVec_self_star _

/-! ### The objective operator -/

lemma VG21_conjTranspose {n : ℕ} : (VG ℂ n 0 21)ᴴ = VG ℂ n 0 21 := by
  rw [VG_conjTranspose (by norm_num)]
  rfl

lemma Oobj_local_mem (l : Fin (k + 1)) :
    (if l.val < k then (2 : ℂ) • VG ℂ (nf k d l) 0 0 - VG ℂ (nf k d l) 0 21 else VG ℂ (nf k d l) 0 21) ∈
      Submodule.span ℂ (Set.range (VG ℂ (nf k d l) 0)) := by
  split_ifs
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.subset_span ⟨21, rfl⟩)
  · exact Submodule.subset_span ⟨21, rfl⟩

lemma Oobj_mem : Phys.Oobj k d ∈ spanS (nf := nf k d) 0 :=
  kron_mem_span (fun l => VG ℂ (nf k d l) 0) (fun l => Oobj_local_mem l)

lemma Oobj_conjTranspose : (Phys.Oobj k d)ᴴ = Phys.Oobj k d := by
  unfold Phys.Oobj
  rw [kron_conjTranspose]
  congr 1
  funext l
  split_ifs
  · rw [conjTranspose_sub, conjTranspose_smul, VG_zero (by norm_num), conjTranspose_one, VG21_conjTranspose]
    simp [VG_zero (by norm_num : (0 : ℕ) < 16)]
  · exact VG21_conjTranspose

lemma trace_Oobj_proj {X Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}
    (h : IsProj (spanS (nf := nf k d) 0) X Y) :
    (Phys.Oobj k d * Y).trace = (Phys.Oobj k d * X).trace := by
  have := h.2 _ Oobj_mem
  rwa [Oobj_conjTranspose] at this

/-! ### Class constancy -/

lemma class_const (C : CertD) (hid : IdFact C) {f : ℕ} (hf : f < 3) (c : (Fin (C.k + 1) → Fin 24) → ℂ)
    (hinv : ∀ (g1 g2 : Fin 24) (σ : Fin C.k → Fin C.k) (ε : Bool) (w : Fin (C.k + 1) → Fin 24),
      inG f g1 = true → inG f g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w)
    (w : Fin (C.k + 1) → Fin 24) : c w = c (hid.rep f (hid.cls f w)) := by
  rw [← hid.hrep f hf w]
  exact (hinv _ _ _ _ w (hid.hG f hf w).1 (hid.hG f hf w).2 (hid.hσ f hf w)).symm

/-! ### Small facts for the main assembly -/

lemma siteAct_sum (σ : Equiv.Perm (Fin k)) {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (GI (nf k d)) (GI (nf k d)) ℂ) : siteAct σ (∑ i ∈ s, M i) = ∑ i ∈ s, siteAct σ (M i) := by
  ext i j; simp only [siteAct, Matrix.sum_apply]

lemma conjM_sum {ι' : Type*} {ι : Type*} (s : Finset ι) (M : ι → Matrix ι' ι' ℂ) :
    conjM (∑ i ∈ s, M i) = ∑ i ∈ s, conjM (M i) := by
  ext a b; simp only [conjM, Matrix.map_apply, Matrix.sum_apply, star_sum]

lemma Xf_transpose (f : ℕ) (a b : Phys.V1 k d → ℂ) : (Phys.Xf f a b)ᵀ = conjM (Phys.Xf f a b) := by
  ext i j
  simp only [Phys.Xf, transpose_apply, conjM, Matrix.map_apply, vecMulVec_apply, Pi.star_apply, star_mul',
    star_star]
  ring

lemma permRows_comp (σ τ : Equiv.Perm (Fin k)) (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    permRows σ (permRows τ A) = permRows (σ * τ) A := by
  ext x α; simp only [permRows, Equiv.Perm.coe_mul]; rfl

lemma map_star_map_star (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) : (A.map star).map star = A := by
  ext x α; simp

lemma permRows_map_star (σ : Equiv.Perm (Fin k)) (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    (permRows σ A).map star = permRows σ (A.map star) := rfl

lemma csl_cord_0 : csl 0 = 0 ∧ cord 0 = ![1, 2, 3] := by
  refine ⟨by decide, funext fun u => by fin_cases u <;> decide⟩
lemma csl_cord_1 : csl 1 = 3 ∧ cord 1 = ![0, 1, 2] := by
  refine ⟨by decide, funext fun u => by fin_cases u <;> decide⟩
lemma csl_cord_2 : csl 2 = 2 ∧ cord 2 = ![0, 1, 3] := by
  refine ⟨by decide, funext fun u => by fin_cases u <;> decide⟩
lemma csl_cord_3 : csl 3 = 1 ∧ cord 3 = ![0, 2, 3] := by
  refine ⟨by decide, funext fun u => by fin_cases u <;> decide⟩
lemma csl_cord_4 : csl 4 = 1 ∧ cord 4 = ![3, 0, 2] := by
  refine ⟨by decide, funext fun u => by fin_cases u <;> decide⟩

lemma gram_trace (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ) (hA : Aᴴ * A = (c : ℂ) • 1) :
    ∑ x, ∑ α, Complex.normSq (A x α) = 2 * c := by
  have h := congrArg Matrix.trace hA
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Matrix.smul_apply, one_apply,
    if_true, smul_eq_mul, mul_one, Fin.sum_univ_two] at h
  have e : ∀ x α, star (A x α) * A x α = (Complex.normSq (A x α) : ℂ) := by
    intro x α; rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [e] at h
  rw [Finset.sum_comm, Fin.sum_univ_two]
  have h' : ((∑ x, Complex.normSq (A x 0) + ∑ x, Complex.normSq (A x 1) : ℝ) : ℂ) = ((2 * c : ℝ) : ℂ) := by
    push_cast; rw [h]; ring
  exact_mod_cast h'

end NPT.Cert
