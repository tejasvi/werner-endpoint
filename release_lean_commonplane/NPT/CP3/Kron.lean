/-
NPT.CP3.Kron — Gram forms of four-replica operators on modules, Kronecker lifting through per-factor Fourier maps
(cut () → cut (3,)), and factorization of product functionals (G1, G2 of the coordinate route). Generic over a
commutative ring `R`, a finite factor type `L` with local dimensions `nf`, and module families given as data; the CP3
instance is `L = Fin 5`, `nf = nf 4 3`, `R = ℝ`.
-/
import NPT.Cert.Glob
import NPT.Cert.Sem

open Matrix BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Brauer

namespace NPT.CP3

section Generic

variable {R : Type*} [CommRing R]
variable {L : Type*} [Fintype L] [DecidableEq L] (nf : L → ℕ)

/-- Global four-replica index (as `NPT.Cert.GI`). -/
abbrev GIx := (l : L) → Dig (nf l) 4

/-- Kronecker product over the factors, any commutative ring (`kron` of `NPT.Cert.Glob` is the case `R = ℂ`). -/
def kronR {ι κ : L → Type*} (A : (l : L) → Matrix (ι l) (κ l) R) : Matrix ((l : L) → ι l) ((l : L) → κ l) R :=
  fun i j => ∏ l, A l (i l) (j l)

/-- Partial transpose on replica 3 of a four-replica matrix of one factor (swap the replica-3 digits). -/
def ptLoc {n : ℕ} (M : Matrix (Dig n 4) (Dig n 4) R) : Matrix (Dig n 4) (Dig n 4) R :=
  fun x y => M (Function.update x 3 (y 3)) (Function.update y 3 (x 3))

/-- Partial transpose on replica 3 of a global matrix (every factor), `Y ↦ Y^{Γ₃}` (cut bit mask 8). -/
def ptG (M : Matrix (GIx nf) (GIx nf) R) : Matrix (GIx nf) (GIx nf) R :=
  fun i j => M (fun l => Function.update (i l) 3 (j l 3)) (fun l => Function.update (j l) 3 (i l 3))

variable {nf}

lemma kronR_mul {ι κ μ : L → Type*} [∀ l, Fintype (κ l)] [∀ l, DecidableEq (κ l)]
    (A : (l : L) → Matrix (ι l) (κ l) R) (B : (l : L) → Matrix (κ l) (μ l) R) :
    kronR A * kronR B = kronR (fun l => A l * B l) := by
  ext i j
  simp only [kronR, mul_apply]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.prod_mul_distrib]

lemma kronR_transpose {ι κ : L → Type*} (A : (l : L) → Matrix (ι l) (κ l) R) :
    (kronR A)ᵀ = kronR (fun l => (A l)ᵀ) := rfl

lemma ptG_kronR (A : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) :
    ptG nf (kronR A) = kronR (fun l => ptLoc (A l)) := rfl

lemma ptG_sum {W : Type*} (s : Finset W) (c : W → R) (M : W → Matrix (GIx nf) (GIx nf) R) :
    ptG nf (∑ w ∈ s, c w • M w) = ∑ w ∈ s, c w • ptG nf (M w) := by
  ext i j
  simp only [ptG, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-! ### Modules, tuples, Gram forms -/

/-- A family of modules per factor: `nI l` modules, the `i`-th of dimension `dI l i`, as columns `M l i`. -/
structure ModFam (nf : L → ℕ) (R : Type*) where
  nI : L → ℕ
  dI : (l : L) → Fin (nI l) → ℕ
  M : (l : L) → (i : Fin (nI l)) → Matrix (Dig (nf l) 4) (Fin (dI l i)) R

variable (F : ModFam nf R)

/-- A tuple: one module per factor. -/
abbrev Tup := (l : L) → Fin (F.nI l)

/-- Gram index of a tuple. -/
abbrev GIdx (τ : Tup F) := (l : L) → Fin (F.dI l (τ l))

/-- Module of a tuple, `J_τ = ⊗_l M_l(τ l)`. -/
def Jt (τ : Tup F) : Matrix (GIx nf) (GIdx F τ) R := kronR fun l => F.M l (τ l)

/-- Gram form of a tuple, `H_τ(Y) = J_τᵀ Y J_τ`. -/
def gram (τ : Tup F) (Y : Matrix (GIx nf) (GIx nf) R) : Matrix (GIdx F τ) (GIdx F τ) R := (Jt F τ)ᵀ * Y * Jt F τ

/-- Local Gram form of one factor: `M_l(i)ᵀ X M_l(i)`. -/
def gramLoc (l : L) (i : Fin (F.nI l)) (X : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) :
    Matrix (Fin (F.dI l i)) (Fin (F.dI l i)) R := (F.M l i)ᵀ * X * F.M l i

lemma gram_kronR (τ : Tup F) (X : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) :
    gram F τ (kronR X) = kronR (fun l => gramLoc F l (τ l) (X l)) := by
  unfold gram Jt gramLoc
  rw [kronR_transpose, kronR_mul, kronR_mul]

lemma gram_sum (τ : Tup F) {W : Type*} (s : Finset W) (c : W → R) (M : W → Matrix (GIx nf) (GIx nf) R) :
    gram F τ (∑ w ∈ s, c w • M w) = ∑ w ∈ s, c w • gram F τ (M w) := by
  unfold gram
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ### Kronecker lifting (G2) -/

variable (F' : ModFam nf R)

/-- Per-factor Fourier coefficients from the cut-() Gram coordinates of factor `l` to the cut-(3,) ones. -/
abbrev PhiF := (l : L) → (κ : Fin (F'.nI l)) → Fin (F'.dI l κ) → Fin (F'.dI l κ) →
    (la : Fin (F.nI l)) → Fin (F.dI l la) → Fin (F.dI l la) → R

variable {F F'}

/-- The lifted map `(⊗_l Φ_l)` from the Gram form of a cut-() tuple `τ` to the cut-(3,) tuple `τ'`. -/
def phiMap (Φ : PhiF F F') (τ' : Tup F') (τ : Tup F) (G : Matrix (GIdx F τ) (GIdx F τ) R) :
    Matrix (GIdx F' τ') (GIdx F' τ') R :=
  fun a' b' => ∑ a : GIdx F τ, ∑ b : GIdx F τ, (∏ l, Φ l (τ' l) (a' l) (b' l) (τ l) (a l) (b l)) * G a b

lemma phiMap_sum (Φ : PhiF F F') (τ' : Tup F') (τ : Tup F) {W : Type*} (s : Finset W) (c : W → R)
    (G : W → Matrix (GIdx F τ) (GIdx F τ) R) :
    phiMap Φ τ' τ (∑ w ∈ s, c w • G w) = ∑ w ∈ s, c w • phiMap Φ τ' τ (G w) := by
  ext a' b'
  simp only [phiMap, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  calc ∑ a : GIdx F τ, ∑ b : GIdx F τ, ∑ w ∈ s, (∏ l, Φ l (τ' l) (a' l) (b' l) (τ l) (a l) (b l)) * (c w * G w a b)
      = ∑ a : GIdx F τ, ∑ w ∈ s, ∑ b : GIdx F τ,
          (∏ l, Φ l (τ' l) (a' l) (b' l) (τ l) (a l) (b l)) * (c w * G w a b) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w ∈ s, ∑ a : GIdx F τ, ∑ b : GIdx F τ,
          (∏ l, Φ l (τ' l) (a' l) (b' l) (τ l) (a l) (b l)) * (c w * G w a b) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
          ring

/-- The per-factor Fourier fact at one letter `X` of factor `l`: for every cut-(3,) module `κ`,
`M'_κᵀ X^{Γ₃} M'_κ = Σ_λ Φ_l[κ, λ](M_λᵀ X M_λ)`. -/
def FourierAt (Φ : PhiF F F') (l : L) (X : Matrix (Dig (nf l) 4) (Dig (nf l) 4) R) : Prop :=
  ∀ κ : Fin (F'.nI l), gramLoc F' l κ (ptLoc X) =
    fun a' b' => ∑ la : Fin (F.nI l), ∑ a, ∑ b, Φ l κ a' b' la a b * gramLoc F l la X a b

/-- Splitting a sum over dependent functions into tuple and coordinates. -/
def tupSplit (F : ModFam nf R) :
    ((l : L) → Σ la : Fin (F.nI l), Fin (F.dI l la) × Fin (F.dI l la)) ≃
      Σ τ : Tup F, GIdx F τ × GIdx F τ where
  toFun x := ⟨fun l => (x l).1, fun l => (x l).2.1, fun l => (x l).2.2⟩
  invFun y := fun l => ⟨y.1 l, y.2.1 l, y.2.2 l⟩
  left_inv x := rfl
  right_inv y := rfl

/-- **Kronecker lifting for one word.** -/
lemma word_lift (Φ : PhiF F F') (X : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R)
    (hX : ∀ l, FourierAt Φ l (X l)) (τ' : Tup F') :
    gram F' τ' (ptG nf (kronR X)) = ∑ τ : Tup F, phiMap Φ τ' τ (gram F τ (kronR X)) := by
  rw [ptG_kronR, gram_kronR]
  simp_rw [gram_kronR]
  ext a' b'
  have hl : ∀ l, gramLoc F' l (τ' l) (ptLoc (X l)) (a' l) (b' l) =
      ∑ z : (Σ la : Fin (F.nI l), Fin (F.dI l la) × Fin (F.dI l la)),
        Φ l (τ' l) (a' l) (b' l) z.1 z.2.1 z.2.2 * gramLoc F l z.1 (X l) z.2.1 z.2.2 := by
    intro l
    rw [hX l (τ' l), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [Fintype.sum_prod_type]
  simp only [kronR, Matrix.sum_apply, phiMap]
  simp_rw [hl]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
  rw [← Fintype.sum_equiv (tupSplit F).symm _ _ (fun _ => rfl)]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [tupSplit, Equiv.coe_fn_symm_mk]
  rw [Finset.prod_mul_distrib]

/-- **Kronecker lifting.** If every letter of every factor satisfies the Fourier fact, then for every finite
combination `Y` of words (Kronecker products of letters) and every cut-(3,) tuple `τ'`,
`J'_τ'ᵀ Y^{Γ₃} J'_τ' = Σ_τ phiMap τ' τ (J_τᵀ Y J_τ)`, the sum over all cut-() tuples. -/
theorem kron_lift (Φ : PhiF F F') (Letter : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R → Prop)
    (hF : ∀ l X, Letter l X → FourierAt Φ l X)
    {W : Type*} (s : Finset W) (c : W → R) (word : W → (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R)
    (hw : ∀ w ∈ s, ∀ l, Letter l (word w l)) (τ' : Tup F') :
    gram F' τ' (ptG nf (∑ w ∈ s, c w • kronR (word w))) =
      ∑ τ : Tup F, phiMap Φ τ' τ (gram F τ (∑ w ∈ s, c w • kronR (word w))) := by
  rw [ptG_sum, gram_sum]
  simp_rw [gram_sum, phiMap_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hws => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact word_lift Φ (word w) (fun l => hF l _ (hw w hws l)) τ'

/-! ### Product functionals (G2, objective and equality rows) -/

/-- Entrywise pairing `⟨G, X⟩ = Σ G[x, y] X[x, y]` (`Tr(O X) = ⟨Oᵀ, X⟩`). -/
def pairing {ι : Type*} [Fintype ι] (G X : Matrix ι ι R) : R := ∑ x, ∑ y, G x y * X x y

lemma pairing_sum {ι : Type*} [Fintype ι] (G : Matrix ι ι R) {W : Type*} (s : Finset W) (c : W → R)
    (M : W → Matrix ι ι R) : pairing G (∑ w ∈ s, c w • M w) = ∑ w ∈ s, c w * pairing G (M w) := by
  simp only [pairing, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  calc ∑ x, ∑ y, ∑ w ∈ s, G x y * (c w * M w x y) = ∑ x, ∑ w ∈ s, ∑ y, G x y * (c w * M w x y) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w ∈ s, ∑ x, ∑ y, G x y * (c w * M w x y) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
          ring

/-- Pairs of dependent functions as one function into pairs. -/
def prodSplit (ι : L → Type*) : ((l : L) → ι l × ι l) ≃ ((l : L) → ι l) × ((l : L) → ι l) where
  toFun z := (fun l => (z l).1, fun l => (z l).2)
  invFun p := fun l => (p.1 l, p.2 l)
  left_inv z := rfl
  right_inv p := rfl

lemma pairing_kronR {ι : L → Type*} [∀ l, Fintype (ι l)] [∀ l, DecidableEq (ι l)]
    (G X : (l : L) → Matrix (ι l) (ι l) R) : pairing (kronR G) (kronR X) = ∏ l, pairing (G l) (X l) := by
  have hl : ∀ l, pairing (G l) (X l) = ∑ z : ι l × ι l, G l z.1 z.2 * X l z.1 z.2 := fun l => by
    unfold pairing; rw [Fintype.sum_prod_type]
  simp_rw [hl]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
  rw [← Fintype.sum_equiv (prodSplit ι).symm _ _ (fun _ => rfl), Fintype.sum_prod_type]
  unfold pairing kronR
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

/-- **Factorization of a product functional.** If on every letter of factor `l` the functional `⟨G_l, ·⟩` is
`Σ_λ ⟨ℓ_l(λ), M_λᵀ · M_λ⟩`, then on every finite combination `Y` of words
`⟨⊗ G_l, Y⟩ = Σ_τ ⟨⊗ ℓ_l(τ l), J_τᵀ Y J_τ⟩`. -/
theorem pairing_factor (G : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R)
    (ell : (l : L) → (la : Fin (F.nI l)) → Matrix (Fin (F.dI l la)) (Fin (F.dI l la)) R)
    (Letter : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R → Prop)
    (hG : ∀ l X, Letter l X → pairing (G l) X = ∑ la : Fin (F.nI l), pairing (ell l la) (gramLoc F l la X))
    {W : Type*} (s : Finset W) (c : W → R) (word : W → (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) R)
    (hw : ∀ w ∈ s, ∀ l, Letter l (word w l)) :
    pairing (kronR G) (∑ w ∈ s, c w • kronR (word w)) =
      ∑ τ : Tup F, pairing (kronR fun l => ell l (τ l)) (gram F τ (∑ w ∈ s, c w • kronR (word w))) := by
  rw [pairing_sum]
  simp_rw [gram_sum, pairing_sum, gram_kronR, pairing_kronR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hws => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.prod_congr rfl fun l _ => hG l _ (hw w hws l)]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]

end Generic

/-! ### Partial transposes of the letters -/

section Letters

variable {R : Type*} [CommRing R]

lemma SelOp_apply {n : ℕ} (α β : Fin 4 → Fin 4) (u v : Dig n 4) :
    SelOp R n α β u v = ∑ z : Dig n 4, if z ∘ α = u ∧ z ∘ β = v then (1 : R) else 0 := by
  unfold SelOp
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Matrix.single_apply]

lemma inS8 (s : Fin 4) : inS 8 s = decide (s = 3) := by fin_cases s <;> rfl
lemma inS0 (s : Fin 4) : inS 0 s = false := by fin_cases s <;> rfl

/-- **The partial transpose of a permutation operator on replica 3 is the cut-(3,) operator:**
`(V_p)^{Γ₃} = VG n 8 p`. -/
theorem ptLoc_VG (n : ℕ) (p : Fin 24) : ptLoc (VG R n 0 p) = VG R n 8 p := by
  ext x y
  unfold ptLoc VG
  rw [SelOp_apply, SelOp_apply]
  set X' := Function.update x 3 (y 3) with hX'
  set Y' := Function.update y 3 (x 3) with hY'
  have ha0 : aSel 0 p = pinvf p := funext fun s => by simp [aSel, inS0]
  have hb0 : bSel 0 p = id := funext fun s => by simp [bSel, inS0]
  rw [ha0, hb0]
  -- the cut-() side: only `z = Y'` contributes
  have h0 : (∑ z : Dig n 4, if z ∘ pinvf p = X' ∧ z ∘ id = Y' then (1 : R) else 0) =
      if Y' ∘ pinvf p = X' then 1 else 0 := by
    rw [Finset.sum_eq_single Y']
    · simp
    · intro z _ hz; rw [if_neg]; rintro ⟨_, h⟩; exact hz h
    · intro h; exact absurd (Finset.mem_univ Y') h
  rw [h0]
  -- the cut-(3,) side: the condition pins `z = Y'`
  have hc : ∀ z : Dig n 4, (z ∘ aSel 8 p = x ∧ z ∘ bSel 8 p = y) ↔ (z = Y' ∧ Y' ∘ pinvf p = X') := by
    intro z
    constructor
    · rintro ⟨h1, h2⟩
      have hz : z = Y' := by
        funext s
        by_cases hs : s = 3
        · subst hs
          have := congrFun h1 3
          simp only [Function.comp_apply, aSel, inS8, decide_true, if_true] at this
          rw [hY', Function.update_self]; exact this
        · have := congrFun h2 s
          simp only [Function.comp_apply, bSel, inS8, hs, decide_false, Bool.false_eq_true, ↓reduceIte] at this
          rw [hY', Function.update_of_ne hs]; exact this
      refine ⟨hz, ?_⟩
      subst hz
      funext s
      by_cases hs : s = 3
      · subst hs
        have := congrFun h2 3
        simp only [Function.comp_apply, bSel, inS8, decide_true, if_true] at this
        rw [Function.comp_apply, hX', Function.update_self]; exact this
      · have := congrFun h1 s
        simp only [Function.comp_apply, aSel, inS8, hs, decide_false, Bool.false_eq_true, ↓reduceIte] at this
        rw [Function.comp_apply, hX', Function.update_of_ne hs]; exact this
    · rintro ⟨rfl, h⟩
      constructor
      · funext s
        by_cases hs : s = 3
        · subst hs
          simp only [Function.comp_apply, aSel, inS8, decide_true, if_true]
          rw [hY', Function.update_self]
        · have := congrFun h s
          simp only [Function.comp_apply] at this
          simp only [Function.comp_apply, aSel, inS8, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [this, hX', Function.update_of_ne hs]
      · funext s
        by_cases hs : s = 3
        · subst hs
          have := congrFun h 3
          simp only [Function.comp_apply] at this
          simp only [Function.comp_apply, bSel, inS8, decide_true, if_true]
          rw [this, hX', Function.update_self]
        · simp only [Function.comp_apply, bSel, inS8, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [hY', Function.update_of_ne hs]
  simp_rw [hc]
  by_cases hP : Y' ∘ pinvf p = X'
  · rw [if_pos hP, Finset.sum_eq_single Y']
    · simp [hP]
    · intro z _ hz; rw [if_neg]; rintro ⟨h, _⟩; exact hz h
    · intro h; exact absurd (Finset.mem_univ Y') h
  · rw [if_neg hP]
    refine (Finset.sum_eq_zero fun z _ => ?_).symm
    rw [if_neg]; rintro ⟨_, h⟩; exact hP h

/-- The partial transpose of a matrix unit of one factor is a matrix unit. -/
theorem ptLoc_single {n : ℕ} (x y : Dig n 4) :
    ptLoc (Matrix.single x y (1 : R)) =
      Matrix.single (Function.update x 3 (y 3)) (Function.update y 3 (x 3)) 1 := by
  ext u v
  unfold ptLoc
  rw [Matrix.single_apply, Matrix.single_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    subst h1 h2
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self, and_self]
  · rintro ⟨h1, h2⟩
    subst h1 h2
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self, and_self]

end Letters

end NPT.CP3
