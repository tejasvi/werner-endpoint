/-
NPT.CP3.Lift — the Kronecker lifting (G2) and the factorization of product functionals on `A'_0` (`NPT.CP3.Alg`).

For module families `F` (cut `()`) and `F'` (cut `(3,)`) over `ℂ` on the five factors of `GC`:
* `gam3 = ptG nfC`: entry rule 1 is the partial transpose on replica 3 of every factor;
* `lift_b`: for every `Y ∈ A'_0` and every cut-`(3,)` tuple `τ'`, `J'_τ'ᵀ Y^{Γ₃} J'_τ' = Σ_τ phiMap Φ τ' τ (J_τᵀ Y J_τ)`,
  given the Fourier fact at the 24 operators `VG 0 p` of every site and at every matrix of the auxiliary factor;
* `lift_c`: for a Kronecker product `O = kron G` and every `Y ∈ A'_0`, `Tr(O Y) = Σ_τ ⟨⊗_l ℓ_l(τ l), J_τᵀ Y J_τ⟩`, given the
  local trace identities at the same letters.
Both local facts are linear in the letter, so on the auxiliary factor the matrix units suffice (`fourierAt_of_single`,
`traceAt_of_single`); on a site the Fourier fact at `VG 0 p` is the cut-`(3,)` Gram form of `VG 8 p` (`fourierAt_VG`).
-/
import NPT.CP3.Kron
import NPT.CP3.Alg

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem

namespace NPT.CP3

/-! ### Linearity -/

section Generic

variable {R : Type*} [CommRing R]
variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ}
variable {F F' : ModFam nf R}

lemma ptLoc_add {n : ℕ} (A B : Matrix (Dig n 4) (Dig n 4) R) : ptLoc (A + B) = ptLoc A + ptLoc B := rfl
lemma ptLoc_smul {n : ℕ} (c : R) (A : Matrix (Dig n 4) (Dig n 4) R) : ptLoc (c • A) = c • ptLoc A := rfl
lemma ptLoc_zero {n : ℕ} : ptLoc (0 : Matrix (Dig n 4) (Dig n 4) R) = 0 := rfl

lemma gramLoc_add (l : L) (i : Fin (F.nI l)) (A B : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) :
    gramLoc F l i (A + B) = gramLoc F l i A + gramLoc F l i B := by
  unfold gramLoc; rw [Matrix.mul_add, Matrix.add_mul]

lemma gramLoc_smul (l : L) (i : Fin (F.nI l)) (c : R) (A : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) :
    gramLoc F l i (c • A) = c • gramLoc F l i A := by
  unfold gramLoc; rw [Matrix.mul_smul, Matrix.smul_mul]

lemma gramLoc_zero (l : L) (i : Fin (F.nI l)) : gramLoc F l i (0 : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) = 0 := by
  unfold gramLoc; rw [Matrix.mul_zero, Matrix.zero_mul]

lemma gram_add (τ : Tup F) (A B : Matrix (GIx nf) (GIx nf) R) : gram F τ (A + B) = gram F τ A + gram F τ B := by
  unfold gram; rw [Matrix.mul_add, Matrix.add_mul]

lemma gram_smul (τ : Tup F) (c : R) (A : Matrix (GIx nf) (GIx nf) R) : gram F τ (c • A) = c • gram F τ A := by
  unfold gram; rw [Matrix.mul_smul, Matrix.smul_mul]

lemma gram_zero (τ : Tup F) : gram F τ (0 : Matrix (GIx nf) (GIx nf) R) = 0 := by
  unfold gram; rw [Matrix.mul_zero, Matrix.zero_mul]

lemma phiMap_add (Φ : PhiF F F') (τ' : Tup F') (τ : Tup F) (A B : Matrix (GIdx F τ) (GIdx F τ) R) :
    phiMap Φ τ' τ (A + B) = phiMap Φ τ' τ A + phiMap Φ τ' τ B := by
  ext a' b'
  simp only [phiMap, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma phiMap_smul (Φ : PhiF F F') (τ' : Tup F') (τ : Tup F) (c : R) (A : Matrix (GIdx F τ) (GIdx F τ) R) :
    phiMap Φ τ' τ (c • A) = c • phiMap Φ τ' τ A := by
  ext a' b'
  simp only [phiMap, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma phiMap_zero (Φ : PhiF F F') (τ' : Tup F') (τ : Tup F) :
    phiMap Φ τ' τ (0 : Matrix (GIdx F τ) (GIdx F τ) R) = 0 := by
  ext a' b'
  simp only [phiMap, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

lemma pairing_add {ι : Type*} [Fintype ι] (G A B : Matrix ι ι R) : pairing G (A + B) = pairing G A + pairing G B := by
  simp only [pairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma pairing_smul {ι : Type*} [Fintype ι] (G : Matrix ι ι R) (c : R) (A : Matrix ι ι R) :
    pairing G (c • A) = c * pairing G A := by
  simp only [pairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma pairing_zero {ι : Type*} [Fintype ι] (G : Matrix ι ι R) : pairing G 0 = 0 := by
  simp only [pairing, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

lemma trace_kronR {ι : L → Type*} [∀ l, Fintype (ι l)] [∀ l, DecidableEq (ι l)] (B : (l : L) → Matrix (ι l) (ι l) R) :
    (kronR B).trace = ∏ l, (B l).trace := by
  simp only [Matrix.trace, Matrix.diag, kronR]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]

/-! ### Local facts: linear in the letter -/

lemma fourierAt_add (Φ : PhiF F F') (l : L) {A B : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R}
    (hA : FourierAt Φ l A) (hB : FourierAt Φ l B) : FourierAt Φ l (A + B) := by
  intro κ
  ext a' b'
  rw [ptLoc_add, gramLoc_add, Matrix.add_apply, hA κ, hB κ]
  simp only [Matrix.add_apply, gramLoc_add, mul_add, Finset.sum_add_distrib]

lemma fourierAt_smul (Φ : PhiF F F') (l : L) (c : R) {A : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R}
    (hA : FourierAt Φ l A) : FourierAt Φ l (c • A) := by
  intro κ
  ext a' b'
  rw [ptLoc_smul, gramLoc_smul, Matrix.smul_apply, hA κ]
  simp only [Matrix.smul_apply, smul_eq_mul, gramLoc_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun la _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma fourierAt_zero (Φ : PhiF F F') (l : L) : FourierAt Φ l (0 : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) := by
  intro κ
  rw [ptLoc_zero, gramLoc_zero]
  ext a' b'
  simp only [Matrix.zero_apply, gramLoc_zero, mul_zero, Finset.sum_const_zero]

/-- The Fourier fact holds at every letter of factor `l` once it holds at the matrix units. -/
theorem fourierAt_of_single (Φ : PhiF F F') (l : L)
    (h : ∀ x y : Dig (nf l) 4, FourierAt Φ l (Matrix.single x y (1 : R))) (X : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) :
    FourierAt Φ l X := by
  induction X using Matrix.induction_on' with
  | h_zero => exact fourierAt_zero Φ l
  | h_add A B hA hB => exact fourierAt_add Φ l hA hB
  | h_std_basis x y c =>
    rw [show Matrix.single x y c = c • Matrix.single x y (1 : R) by rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    exact fourierAt_smul Φ l c (h x y)

/-- The local trace identity of factor `l` at a letter `X`: `Tr(G X) = Σ_λ ⟨ℓ(λ), M_λᵀ X M_λ⟩`. -/
def TraceAt (F : ModFam nf R) (l : L) (G : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R)
    (ell : (la : Fin (F.nI l)) → Matrix (Fin (F.dI l la)) (Fin (F.dI l la)) R)
    (X : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) : Prop :=
  (G * X).trace = ∑ la : Fin (F.nI l), pairing (ell la) (gramLoc F l la X)

/-- The local trace identity holds at every letter once it holds at the matrix units. -/
theorem traceAt_of_single (l : L) (G : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R)
    (ell : (la : Fin (F.nI l)) → Matrix (Fin (F.dI l la)) (Fin (F.dI l la)) R)
    (h : ∀ x y : Dig (nf l) 4, TraceAt F l G ell (Matrix.single x y (1 : R))) (X : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) :
    TraceAt F l G ell X := by
  induction X using Matrix.induction_on' with
  | h_zero =>
    unfold TraceAt
    simp only [Matrix.mul_zero, Matrix.trace_zero, gramLoc_zero, pairing_zero, Finset.sum_const_zero]
  | h_add A B hA hB =>
    unfold TraceAt at *
    rw [Matrix.mul_add, Matrix.trace_add, hA, hB, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun la _ => by rw [gramLoc_add, pairing_add]
  | h_std_basis x y c =>
    have h1 := h x y
    unfold TraceAt at *
    rw [show Matrix.single x y c = c • Matrix.single x y (1 : R) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
      Matrix.mul_smul, Matrix.trace_smul, h1, Finset.smul_sum]
    exact Finset.sum_congr rfl fun la _ => by rw [gramLoc_smul, pairing_smul, smul_eq_mul]

end Generic

/-! ### Rule 1 is the partial transpose on replica 3 -/

lemma rkp1 (s : Fin 4) : rkp 1 s = if s = 3 then Fin.natAdd 4 3 else Fin.castAdd 4 s := by
  revert s; decide

lemma rlp1 (s : Fin 4) : rlp 1 s = if s = 3 then Fin.castAdd 4 3 else Fin.natAdd 4 s := by
  revert s; decide

lemma append_rkp1 {α : Type*} (i j : Fin 4 → α) : Fin.append i j ∘ rkp 1 = Function.update i 3 (j 3) := by
  funext s
  rw [Function.comp_apply, rkp1]
  by_cases hs : s = 3
  · subst hs; rw [if_pos rfl, Fin.append_right, Function.update_self]
  · rw [if_neg hs, Fin.append_left, Function.update_of_ne hs]

lemma append_rlp1 {α : Type*} (i j : Fin 4 → α) : Fin.append i j ∘ rlp 1 = Function.update j 3 (i 3) := by
  funext s
  rw [Function.comp_apply, rlp1]
  by_cases hs : s = 3
  · subst hs; rw [if_pos rfl, Fin.append_left, Function.update_self]
  · rw [if_neg hs, Fin.append_right, Function.update_of_ne hs]

lemma ruleL_rule1 {n : ℕ} (M : Matrix (Dig n 4) (Dig n 4) ℂ) : ruleL (rkp 1) (rlp 1) M = ptLoc M := by
  ext i j
  simp only [ruleL, ptLoc, append_rkp1, append_rlp1]

/-- `Y^{Γ₃}` of `NPT.CP3.Alg` is `ptG`. -/
lemma gam3_eq_ptG (M : Matrix GC GC ℂ) : gam3 M = ptG nfC M := by
  ext i j
  simp only [gam3, ruleG, ptG, append_rkp1, append_rlp1]

lemma kron_eq_kronR {L : Type*} [Fintype L] [DecidableEq L] {ι κ : L → Type*} (A : (l : L) → Matrix (ι l) (κ l) ℂ) :
    kron A = kronR A := rfl

lemma gam3_add (A B : Matrix GC GC ℂ) : gam3 (A + B) = gam3 A + gam3 B := rfl
lemma gam3_smul (c : ℂ) (A : Matrix GC GC ℂ) : gam3 (c • A) = c • gam3 A := rfl
lemma gam3_zero : gam3 (0 : Matrix GC GC ℂ) = 0 := rfl

lemma fin5_eq4 : ∀ l : Fin 5, ¬ l.val < 4 → l = 4 := by decide

/-- On a site the Fourier fact at `VG 0 p` is a statement about the cut-`(3,)` operator `VG 8 p`. -/
lemma fourierAt_VG {F F' : ModFam nfC ℂ} (Φ : PhiF F F') (l : Fin 5) (p : Fin 24) :
    FourierAt Φ l (VG ℂ (nfC l) 0 p) ↔ ∀ κ : Fin (F'.nI l), gramLoc F' l κ (VG ℂ (nfC l) 8 p) =
      fun a' b' => ∑ la : Fin (F.nI l), ∑ a, ∑ b, Φ l κ a' b' la a b * gramLoc F l la (VG ℂ (nfC l) 0 p) a b := by
  unfold FourierAt
  rw [ptLoc_VG]

/-! ### (b) Kronecker lifting on `A'_0` -/

/-- **(b)** For every `Y ∈ A'_0` and every cut-`(3,)` tuple `τ'`: `J'_τ'ᵀ Y^{Γ₃} J'_τ' = Σ_τ phiMap Φ τ' τ (J_τᵀ Y J_τ)`, the
sum over all cut-`()` tuples. Hypotheses: the Fourier fact at `VG 0 p` (all `p`) on the sites and at every matrix of the
auxiliary factor. -/
theorem lift_b (F F' : ModFam nfC ℂ) (Φ : PhiF F F')
    (hsite : ∀ l : Fin 5, l.val < 4 → ∀ p : Fin 24, FourierAt Φ l (VG ℂ (nfC l) 0 p))
    (haux : ∀ X, FourierAt Φ 4 X) {Y : Matrix GC GC ℂ} (hY : Y ∈ spanA 0) (τ' : Tup F') :
    gram F' τ' (gam3 Y) = ∑ τ : Tup F, phiMap Φ τ' τ (gram F τ Y) := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, A, hA, rfl⟩ := hx
    have hX : ∀ l, FourierAt Φ l (A l) := by
      intro l
      by_cases h : l.val < 4
      · rw [hA l h]; exact hsite l h (w l)
      · obtain rfl := fin5_eq4 l h; exact haux _
    rw [gam3_eq_ptG, kron_eq_kronR]
    exact word_lift Φ A hX τ'
  | zero =>
    rw [gam3_zero, gram_zero]
    simp only [gram_zero, phiMap_zero, Finset.sum_const_zero]
  | add x z _ _ h1 h2 =>
    rw [gam3_add, gram_add, h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by rw [gram_add, phiMap_add]
  | smul c x _ h =>
    rw [gam3_smul, gram_smul, h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [gram_smul, phiMap_smul]

/-! ### (c) Product functionals on `A'_0` -/

/-- **(c)** For a Kronecker product `O = kron G` and every `Y ∈ A'_0`:
`Tr(O Y) = Σ_τ ⟨⊗_l ℓ_l(τ l), J_τᵀ Y J_τ⟩`. Hypotheses: the local trace identity at `VG 0 p` (all `p`) on the sites and at
every matrix of the auxiliary factor. -/
theorem lift_c (F : ModFam nfC ℂ) (G : LocM)
    (ell : (l : Fin 5) → (la : Fin (F.nI l)) → Matrix (Fin (F.dI l la)) (Fin (F.dI l la)) ℂ)
    (hsite : ∀ l : Fin 5, l.val < 4 → ∀ p : Fin 24, TraceAt F l (G l) (ell l) (VG ℂ (nfC l) 0 p))
    (haux : ∀ X, TraceAt F 4 (G 4) (ell 4) X) {Y : Matrix GC GC ℂ} (hY : Y ∈ spanA 0) :
    (kron G * Y).trace = ∑ τ : Tup F, pairing (kronR fun l => ell l (τ l)) (gram F τ Y) := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, A, hA, rfl⟩ := hx
    have hl : ∀ l, (G l * A l).trace = ∑ la, pairing (ell l la) (gramLoc F l la (A l)) := by
      intro l
      by_cases h : l.val < 4
      · rw [hA l h]; exact hsite l h (w l)
      · obtain rfl := fin5_eq4 l h; exact haux _
    rw [kron_eq_kronR, kron_eq_kronR, kronR_mul, trace_kronR, Finset.prod_congr rfl fun l _ => hl l,
      Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun τ _ => by rw [gram_kronR, pairing_kronR]
  | zero =>
    simp only [Matrix.mul_zero, Matrix.trace_zero, gram_zero, pairing_zero, Finset.sum_const_zero]
  | add x z _ _ h1 h2 =>
    rw [Matrix.mul_add, Matrix.trace_add, h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by rw [gram_add, pairing_add]
  | smul c x _ h =>
    rw [Matrix.mul_smul, Matrix.trace_smul, h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [gram_smul, pairing_smul, smul_eq_mul]

end NPT.CP3
