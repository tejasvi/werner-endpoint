/-
NPT.Cert.BlkSign — the sign of a multiplier type's contribution: with `B = W Z Wᵀ` (`Z` PSD) and a PSD
block operator `M`, `Σ_{r,s} ⟨B_rs, Jᵀ M_rs J⟩ ≥ 0`.
-/
import NPT.Cert.SemLink
import NPT.Cert.BlockPos

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.Cert

lemma trace_mul_psd_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hH := hA.1
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set D := diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) with hD
  have hspec : A = U * D * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  rw [hspec]
  have hc : (U * D * star U * B).trace = (D * (star U * B * U)).trace := by
    rw [show U * D * star U * B = U * (D * star U * B) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hc, Matrix.trace]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [hD, Matrix.diag_apply, Matrix.diagonal_mul]
  have hpsd : (star U * B * U).PosSemidef := by
    have := hB.conjTranspose_mul_mul_same U
    simpa [Matrix.star_eq_conjTranspose] using this
  have hdi : 0 ≤ (star U * B * U) i i := hpsd.diag_nonneg
  have hli : (0 : ℂ) ≤ ((hH.eigenvalues i : ℝ) : ℂ) := by
    have := hA.eigenvalues_nonneg i
    exact_mod_cast this
  exact mul_nonneg hli hdi

/-- `Σ_{a,c} Z a c · Q a c ≥ 0` for PSD `Z`, `Q`. -/
lemma sum_mul_psd_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {Z Q : Matrix ι ι ℂ}
    (hZ : Z.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ ∑ a, ∑ c, Z a c * Q a c := by
  have h := trace_mul_psd_nonneg hZ.transpose hQ
  simp only [Matrix.trace, Matrix.diag, mul_apply, transpose_apply] at h
  rw [Finset.sum_comm] at h
  exact h

namespace Sem.CertD

variable (C : CertD)

/-- The multiplier block of type `t`. -/
def blkZ (t : TypeD) : NPT.Cert.PBlock := C.Z.getD t.zi default

/-- `W` rows of type `t` as a complex matrix on `(row, module multi-index)`. -/
noncomputable def Wc (t : TypeD) (R : ℕ) :
    Matrix (Fin R × ((l : Fin (C.k + 1)) → Fin (C.tdim t l))) (Fin (C.blkZ t).n) ℂ :=
  fun x a => ((t.W.getD (x.1.val * ∏ l, C.tdim t l + flatMI (C.tdim t) x.2) []).getD a.val 0 : ℂ)

lemma Bc_eq (t : TypeD) {R : ℕ} (r s : Fin R) (μ ν : (l : Fin (C.k + 1)) → Fin (C.tdim t l)) :
    C.Bc t r s μ ν = ∑ a, ∑ c, C.Wc t R (r, μ) a * (C.blkZ t).Zmat C.Lden a c * C.Wc t R (s, ν) c := by
  unfold Bc Bq Wc blkZ
  push_cast
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [NPT.Cert.PBlock.Zmat, zq]

lemma star_cq {ι κ : Type*} (M : Matrix ι κ ℚ) (i : ι) (j : κ) : star (cq M i j) = cq M i j := by
  simp only [cq, Matrix.map_apply]
  exact map_ratCast (starRingEnd ℂ) _

lemma star_JG (t : TypeD) (i : GI (nf C.k C.d)) (μ : (l : Fin (C.k + 1)) → Fin (C.tdim t l)) :
    star (C.JG t i μ) = C.JG t i μ := by
  simp only [JG, kron, star_prod, Jt]
  exact Finset.prod_congr rfl fun l _ => star_cq _ _ _

lemma star_Wc (t : TypeD) (R : ℕ) (x) (a) : star (C.Wc t R x a) = C.Wc t R x a := by
  simp only [Wc]
  exact map_intCast (starRingEnd ℂ) _

/-- Block-diagonal module matrix `I_R ⊗ J`. -/
noncomputable def Gblk (t : TypeD) (R : ℕ) :
    Matrix (Fin R × GI (nf C.k C.d)) (Fin R × ((l : Fin (C.k + 1)) → Fin (C.tdim t l))) ℂ :=
  fun x y => if x.1 = y.1 then C.JG t x.2 y.2 else 0

lemma Gblk_conjTranspose (t : TypeD) (R : ℕ) : (C.Gblk t R)ᴴ = (C.Gblk t R)ᵀ := by
  ext x y
  simp only [conjTranspose_apply, transpose_apply, Gblk]
  split_ifs
  · exact star_JG C t _ _
  · exact star_zero _

lemma Wc_conjTranspose (t : TypeD) (R : ℕ) : (C.Wc t R)ᴴ = (C.Wc t R)ᵀ := by
  ext x y
  simp only [conjTranspose_apply, transpose_apply]
  exact star_Wc C t R _ _

lemma Gblk_entry (t : TypeD) {R : ℕ} (M : Matrix (Fin R × GI (nf C.k C.d)) (Fin R × GI (nf C.k C.d)) ℂ)
    (r s : Fin R) (μ ν : (l : Fin (C.k + 1)) → Fin (C.tdim t l)) :
    ((C.Gblk t R)ᵀ * M * C.Gblk t R) (r, μ) (s, ν) = ((C.JG t)ᵀ * blockOf M r s * C.JG t) μ ν := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s (fun s' _ hs' => Finset.sum_eq_zero fun j _ => by simp [Gblk, hs'])
    (by simp)]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Gblk, if_true]
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single r (fun r' _ hr' => Finset.sum_eq_zero fun i _ => by
    simp [transpose_apply, Gblk, hr']) (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [transpose_apply, Gblk, blockOf]

/-- `Σ_{x,y} A x y · N x y = Tr(Aᵀ N)`. -/
lemma sum_entry_mul {ι : Type*} [Fintype ι] (A N : Matrix ι ι ℂ) :
    ∑ x, ∑ y, A x y * N x y = (Aᵀ * N).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

/-- **Sign of a multiplier type.** -/
theorem blk_type_nonneg (t : TypeD) {R : ℕ} (ri : Fin R → Fin R → ℕ) (fam : Fin R → Fin R → ℕ)
    (hkp : ∀ r s, posOf (ruleOf t r.val s.val).kpos = rkp (ri r s))
    (hlp : ∀ r s, posOf (ruleOf t r.val s.val).lpos = rlp (ri r s))
    (Y : ℕ → Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ)
    (hM : (blockM ri fam Y).PosSemidef) (hZ : ((C.blkZ t).Zmat C.Lden).PosSemidef) :
    0 ≤ ∑ r : Fin R, ∑ s : Fin R, C.blkOp t r.val s.val (Y (fam r s)) := by
  set Z := (C.blkZ t).Zmat C.Lden
  set Wm := C.Wc t R
  set G := C.Gblk t R
  set N := Gᵀ * blockM ri fam Y * G
  have hN : N.PosSemidef := by
    have := hM.conjTranspose_mul_mul_same G
    rwa [Gblk_conjTranspose] at this
  have hQ : (Wmᵀ * N * Wm).PosSemidef := by
    have := hN.conjTranspose_mul_mul_same Wm
    rwa [Wc_conjTranspose] at this
  have e1 : ∑ r : Fin R, ∑ s : Fin R, C.blkOp t r.val s.val (Y (fam r s)) =
      ∑ x, ∑ y, (Wm * Z * Wmᵀ) x y * N x y := by
    simp only [blkOp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    rw [Bc_eq C t r s μ ν]
    have hNe : N (r, μ) (s, ν) = ((C.JG t)ᵀ * blockOf (blockM ri fam Y) r s * C.JG t) μ ν :=
      Gblk_entry C t _ r s μ ν
    rw [hNe, blockOf_blockM, hkp, hlp]
    congr 1
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have e2 : (Wm * (Zᵀ * Wmᵀ) * N).trace = (Zᵀ * (Wmᵀ * N * Wm)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, sum_entry_mul, transpose_mul, transpose_mul, transpose_transpose, e2]
  exact trace_mul_psd_nonneg hZ.transpose hQ

end Sem.CertD

end NPT.Cert
