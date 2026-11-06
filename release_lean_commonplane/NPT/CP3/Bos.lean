/-
NPT.CP3.Bos — the coordinates of the Gram forms of the projected moment, for padded module families.

* Bosonic range: if the modules intertwine the replica permutations (`VG 0 g * M = M * π(g)` on every factor), the
  Gram form `H` of a bosonic operator satisfies `H = Pᵀ H P` with the averaged representation `P` on the Gram index.
* With data `W`, `W⁺`, `K` (`W⁺ W = 1`, `Pᵀ = W K`) this gives `H = W S Wᵀ` (`gram_coord`), and with the stabilizer
  data `B_σ` and the span certificate, `S = Σ_j y_j S_j` (`stab_coord`).
All products here are on `GC`/`GIx nfC` (index built on `Fin 5`), never on EP3's `Fin (4 + 1)` types.
-/
import NPT.CP3.Site
import NPT.CP3.Coord

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg

namespace NPT.CP3

/-- The constant word `g` on every factor, typed on `GC`. -/
def VWcC (g : Fin 24) : Matrix GC GC ℂ := kronR (fun l => VG ℂ (nfC l) 0 g)

lemma VWcC_mul (g : Fin 24) (X : Matrix GC GC ℂ) : VWcC g * X = VWc (k := 4) (d := 3) g * X := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rfl

lemma mul_VWcC (g : Fin 24) (X : Matrix GC GC ℂ) : X * VWcC g = X * VWc (k := 4) (d := 3) g := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rfl

lemma VWcC_Yp (g : Fin 24) (A : MatA) : VWcC g * Yp A = Yp A := by
  rw [VWcC_mul]; exact VWc_Yp g A

lemma Yp_VWcC (g : Fin 24) (A : MatA) : Yp A * VWcC g = Yp A := by
  rw [mul_VWcC]; exact Yp_VWc g A

lemma VWcC_transpose (g : Fin 24) : (VWcC g)ᵀ = VWcC (pinvIdx g) := by
  unfold VWcC
  rw [kronR_transpose]
  congr 1
  funext l
  exact SymAvg.VG_transpose g

/-- Intertwining of a padded module family with the replica permutations, factor by factor. -/
def Intertw (P : PadData) (πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ) : Prop :=
  ∀ l k g, VG ℂ (nfC l) 0 g * P.M l k = P.M l k * πp l k g

/-- The representation of `g` on the Gram index of the tuple `τ`. -/
def Rep (πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ) (τ : Fin 5 → Fin 5) (g : Fin 24) :
    Matrix MI MI ℂ := kronR (fun l => πp l (τ l) g)

lemma Jt_intertw (P : PadData) {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    (h : Intertw P πp) (τ : Tup P.fam) (g : Fin 24) : VWcC g * Jt P.fam τ = Jt P.fam τ * Rep πp τ g := by
  unfold VWcC Jt Rep
  rw [kronR_mul, kronR_mul]
  congr 1
  funext l
  exact h l (τ l) g

/-- The averaged representation `P = (1/24) Σ_g π(g)` on the Gram index of `τ`. -/
noncomputable def Pav (πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ)
    (τ : Fin 5 → Fin 5) : Matrix MI MI ℂ := (1 / 24 : ℂ) • ∑ g : Fin 24, Rep πp τ g

lemma gram_right (P : PadData) {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    (h : Intertw P πp) (τ : Tup P.fam) (A : MatA) (g : Fin 24) :
    gram P.fam τ (Yp A) = gram P.fam τ (Yp A) * Rep πp τ g := by
  unfold gram
  conv_lhs => rw [← Yp_VWcC g A]
  rw [← Matrix.mul_assoc (Jt P.fam τ)ᵀ (Yp A) (VWcC g),
    Matrix.mul_assoc ((Jt P.fam τ)ᵀ * Yp A) (VWcC g) (Jt P.fam τ), Jt_intertw P h τ g,
    Matrix.mul_assoc ((Jt P.fam τ)ᵀ * Yp A) (Jt P.fam τ) (Rep πp τ g)]

lemma gram_left (P : PadData) {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    (h : Intertw P πp) (τ : Tup P.fam) (A : MatA) (g : Fin 24) :
    gram P.fam τ (Yp A) = (Rep πp τ (pinvIdx g))ᵀ * gram P.fam τ (Yp A) := by
  unfold gram
  conv_lhs => rw [← VWcC_Yp g A]
  have hT : (Jt P.fam τ)ᵀ * VWcC g = (Rep πp τ (pinvIdx g))ᵀ * (Jt P.fam τ)ᵀ := by
    have e := Jt_intertw P h τ (pinvIdx g)
    rw [← VWcC_transpose] at e
    have e2 := congrArg Matrix.transpose e
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at e2
  rw [← Matrix.mul_assoc ((Jt P.fam τ)ᵀ), hT, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

lemma sum_pinv (f : Fin 24 → Matrix MI MI ℂ) : ∑ g, f (pinvIdx g) = ∑ g, f g :=
  Fintype.sum_equiv ⟨pinvIdx, pinvIdx, fun x => pinv_pinv x, fun x => pinv_pinv x⟩ _ _ fun _ => rfl

/-- **Bosonic invariance of the Gram forms**: `H = Pᵀ H P`. -/
theorem gram_bos (P : PadData) {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    (h : Intertw P πp) (τ : Tup P.fam) (A : MatA) :
    gram P.fam τ (Yp A) = (Pav πp τ)ᵀ * gram P.fam τ (Yp A) * Pav πp τ := by
  set H := gram P.fam τ (Yp A) with hH
  have hHP : H * Pav πp τ = H := by
    unfold Pav
    rw [Matrix.mul_smul, Matrix.mul_sum]
    have : ∑ g : Fin 24, H * Rep πp τ g = ∑ _g : Fin 24, H :=
      Finset.sum_congr rfl fun g _ => (gram_right P h τ A g).symm
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  have hPH : (Pav πp τ)ᵀ * H = H := by
    unfold Pav
    rw [Matrix.transpose_smul, Matrix.transpose_sum, Matrix.smul_mul, Matrix.sum_mul]
    have : ∑ g : Fin 24, (Rep πp τ g)ᵀ * H = ∑ _g : Fin 24, H := by
      rw [← sum_pinv]
      exact Finset.sum_congr rfl fun g _ => (gram_left P h τ A g).symm
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  rw [Matrix.mul_assoc, hHP, hPH]

lemma gram_Yp_transpose (P : PadData) (τ : Tup P.fam) (A : MatA) :
    (gram P.fam τ (Yp A))ᵀ = gram P.fam τ (Yp A) := by
  unfold gram
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Yp_transpose, Matrix.mul_assoc]

/-- **Coordinates in the bosonic range** (G3): `H = W (W⁺ H W⁺ᵀ) Wᵀ`. -/
theorem gram_range (P : PadData) {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    (h : Intertw P πp) (τ : Tup P.fam) {r : Type*} [Fintype r] [DecidableEq r] (W : Matrix MI r ℂ)
    (Wp K : Matrix r MI ℂ) (hWp : Wp * W = 1) (hK : (Pav πp τ)ᵀ = W * K) (A : MatA) :
    gram P.fam τ (Yp A) = W * (Wp * gram P.fam τ (Yp A) * Wpᵀ) * Wᵀ :=
  gram_coord _ _ W Wp K (gram_Yp_transpose P τ A) (gram_bos P h τ A) hWp hK

/-- The permutation matrix of `permMI σ` (`(Q H Qᵀ) μ ν = H (permMI σ μ) (permMI σ ν)`). -/
def Qperm (σ : Equiv.Perm (Fin 4)) : Matrix MI MI ℂ := fun μ μ' => if μ' = permMI σ μ then 1 else 0

lemma Qperm_mul_apply (σ : Equiv.Perm (Fin 4)) {r : Type*} [Fintype r] (X : Matrix MI r ℂ) (μ : MI) (j : r) :
    (Qperm σ * X) μ j = X (permMI σ μ) j := by
  simp [Qperm, Matrix.mul_apply]

lemma Qperm_conj (σ : Equiv.Perm (Fin 4)) (H : Matrix MI MI ℂ) (μ ν : MI) :
    (Qperm σ * H * (Qperm σ)ᵀ) μ ν = H (permMI σ μ) (permMI σ ν) := by
  simp [Qperm, Matrix.mul_apply, Matrix.transpose_apply]

/-- **Stabilizer step** (G4, first half): the coordinates `S = W⁺ H W⁺ᵀ` satisfy `S = B S Bᵀ` for each stabilizer
element with `Q_σ W = W B_σ`. -/
theorem coord_stab (P : PadData) (σ : Equiv.Perm (Fin 4)) (τ : Tup P.fam) (hτ : (fun l => τ (sigHat σ l)) = τ)
    (A : MatA) {r : Type*} [Fintype r] [DecidableEq r] (W : Matrix MI r ℂ) (Wp : Matrix r MI ℂ) (hWp : Wp * W = 1)
    (B : Matrix r r ℂ) (hB : Qperm σ * W = W * B)
    (hH : gram P.fam τ (Yp A) = W * (Wp * gram P.fam τ (Yp A) * Wpᵀ) * Wᵀ) :
    B * (Wp * gram P.fam τ (Yp A) * Wpᵀ) * Bᵀ = Wp * gram P.fam τ (Yp A) * Wpᵀ := by
  set H := gram P.fam τ (Yp A)
  set S := Wp * H * Wpᵀ
  have hQ : Qperm σ * H * (Qperm σ)ᵀ = H := by
    ext μ ν
    rw [Qperm_conj]
    exact (gram_stab P σ τ hτ (Yp_site_entry σ A) μ ν).symm
  have h1 : W * (B * S * Bᵀ) * Wᵀ = H := by
    calc W * (B * S * Bᵀ) * Wᵀ = (W * B) * S * (W * B)ᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (Qperm σ * W) * S * (Qperm σ * W)ᵀ := by rw [hB]
      _ = Qperm σ * (W * S * Wᵀ) * (Qperm σ)ᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Qperm σ * H * (Qperm σ)ᵀ := by rw [← hH]
      _ = H := hQ
  have e : Wp * (W * (B * S * Bᵀ) * Wᵀ) * Wpᵀ = (Wp * W) * (B * S * Bᵀ) * (Wp * W)ᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  calc B * S * Bᵀ = Wp * (W * (B * S * Bᵀ) * Wᵀ) * Wpᵀ := by
        rw [e, hWp, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    _ = S := by rw [h1]

end NPT.CP3
