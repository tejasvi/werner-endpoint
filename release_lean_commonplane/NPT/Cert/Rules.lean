/-
NPT.Cert.Rules — entry-rule maps (ep3core `entry_op`) on four-replica operators: the rule
`ruleOp M [i; j] = M[k; l]` (positions of `(k, l)` read from `(i, j)` through a bijection of the eight
index positions) maps selection operators to selection operators, permutation operators onto the
partially transposed operators of a cut (data-certified), and is a Hilbert–Schmidt unitary.
-/
import NPT.Cert.Glob
import NPT.Cert.Proj

open Matrix BigOperators Finset NPT.Brauer

namespace NPT.Cert

/-- A position map `Fin 4 ⊕ Fin 4 → Fin 8` as a function on `Fin (4 + 4)`. -/
abbrev Pos := Fin (4 + 4) → Fin (4 + 4)

/-- Local rule operator: `ruleL kp lp M [i; j] = M[(i,j) ∘ kp; (i,j) ∘ lp]`. -/
def ruleL {n : ℕ} (kp lp : Fin 4 → Fin (4 + 4)) (M : Matrix (Dig n 4) (Dig n 4) ℂ) :
    Matrix (Dig n 4) (Dig n 4) ℂ :=
  fun i j => M (Fin.append i j ∘ kp) (Fin.append i j ∘ lp)

section Global

variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ}

/-- Global rule operator (the same rule on every factor). -/
def ruleG (kp lp : Fin 4 → Fin (4 + 4)) (M : Matrix (GI nf) (GI nf) ℂ) : Matrix (GI nf) (GI nf) ℂ :=
  fun i j => M (fun l => Fin.append (i l) (j l) ∘ kp) (fun l => Fin.append (i l) (j l) ∘ lp)

lemma ruleG_kron (kp lp : Fin 4 → Fin (4 + 4)) (A : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) ℂ) :
    ruleG kp lp (kron A) = kron fun l => ruleL kp lp (A l) := rfl

/-- `ruleG` as a linear map. -/
def ruleGL (kp lp : Fin 4 → Fin (4 + 4)) : Matrix (GI nf) (GI nf) ℂ →ₗ[ℂ] Matrix (GI nf) (GI nf) ℂ where
  toFun := ruleG kp lp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Global

lemma append_comp {α β : Type*} {m : ℕ} (f : α → β) (g h : Fin m → α) :
    Fin.append (f ∘ g) (f ∘ h) = f ∘ Fin.append g h := by
  funext u
  refine Fin.addCases (fun a => ?_) (fun b => ?_) u
  · simp only [Function.comp_apply]; rw [Fin.append_left, Fin.append_left]; rfl
  · simp only [Function.comp_apply]; rw [Fin.append_right, Fin.append_right]; rfl

/-- Position data of a rule: `kp, lp` and the inverse `inv` of `pos = Fin.append kp lp`. -/
structure RulePos where
  kp : Fin 4 → Fin (4 + 4)
  lp : Fin 4 → Fin (4 + 4)
  inv : Pos
  h1 : ∀ c, Fin.append kp lp (inv c) = c
  h2 : ∀ u, inv (Fin.append kp lp u) = u

namespace RulePos

variable (P : RulePos)

/-- The inverse rule. -/
def ikp : Fin 4 → Fin (4 + 4) := P.inv ∘ Fin.castAdd 4
def ilp : Fin 4 → Fin (4 + 4) := P.inv ∘ Fin.natAdd 4

lemma append_inv : Fin.append P.ikp P.ilp = P.inv := by
  funext u
  refine Fin.addCases (fun a => ?_) (fun b => ?_) u
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- Digit-level inversion: reading `(i, j)` through `pos` and then through `inv` gives back `(i, j)`. -/
lemma read_inv {α : Type*} (i j : Fin 4 → α) :
    Fin.append (Fin.append i j ∘ P.kp) (Fin.append i j ∘ P.lp) ∘ P.inv = Fin.append i j := by
  rw [append_comp]
  funext c
  simp [P.h1 c]

lemma read_inv' {α : Type*} (k l : Fin 4 → α) :
    Fin.append (Fin.append k l ∘ P.ikp) (Fin.append k l ∘ P.ilp) ∘ Fin.append P.kp P.lp =
      Fin.append k l := by
  rw [append_comp, append_inv]
  funext u
  simp [P.h2 u]

lemma left_read {α : Type*} (i j : Fin 4 → α) :
    Fin.append (Fin.append i j ∘ P.kp) (Fin.append i j ∘ P.lp) ∘ P.ikp = i := by
  funext a
  have := congrFun (P.read_inv i j) (Fin.castAdd 4 a)
  rw [Fin.append_left] at this
  exact this

lemma right_read {α : Type*} (i j : Fin 4 → α) :
    Fin.append (Fin.append i j ∘ P.kp) (Fin.append i j ∘ P.lp) ∘ P.ilp = j := by
  funext a
  have := congrFun (P.read_inv i j) (Fin.natAdd 4 a)
  rw [Fin.append_right] at this
  exact this

lemma left_read' {α : Type*} (k l : Fin 4 → α) :
    Fin.append (Fin.append k l ∘ P.ikp) (Fin.append k l ∘ P.ilp) ∘ P.kp = k := by
  funext a
  have := congrFun (P.read_inv' k l) (Fin.castAdd 4 a)
  simp only [Function.comp_apply] at this ⊢
  rw [Fin.append_left, Fin.append_left] at this
  exact this

lemma right_read' {α : Type*} (k l : Fin 4 → α) :
    Fin.append (Fin.append k l ∘ P.ikp) (Fin.append k l ∘ P.ilp) ∘ P.lp = l := by
  funext a
  have := congrFun (P.read_inv' k l) (Fin.natAdd 4 a)
  simp only [Function.comp_apply] at this ⊢
  rw [Fin.append_right, Fin.append_right] at this
  exact this


/-- The inverse rule as position data. -/
def symm : RulePos where
  kp := P.ikp
  lp := P.ilp
  inv := Fin.append P.kp P.lp
  h1 c := by rw [append_inv]; exact P.h2 c
  h2 u := by rw [append_inv]; exact P.h1 u

lemma symm_ikp : P.symm.ikp = P.kp := by
  funext s; show Fin.append P.kp P.lp (Fin.castAdd 4 s) = P.kp s; rw [Fin.append_left]
lemma symm_ilp : P.symm.ilp = P.lp := by
  funext s; show Fin.append P.kp P.lp (Fin.natAdd 4 s) = P.lp s; rw [Fin.append_right]

/-- A rule maps selection operators to selection operators. -/
lemma ruleL_SelOp {n : ℕ} (α β : Fin 4 → Fin 4) :
    ruleL P.kp P.lp (SelOp ℂ n α β) =
      SelOp ℂ n (Fin.append α β ∘ P.ikp) (Fin.append α β ∘ P.ilp) := by
  ext i j
  simp only [ruleL, SelOp, Matrix.sum_apply, single_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have key : (x ∘ α = Fin.append i j ∘ P.kp ∧ x ∘ β = Fin.append i j ∘ P.lp) ↔
      (x ∘ (Fin.append α β ∘ P.ikp) = i ∧ x ∘ (Fin.append α β ∘ P.ilp) = j) := by
    constructor
    · rintro ⟨h1, h2⟩
      have hx : x ∘ Fin.append α β = Fin.append (Fin.append i j ∘ P.kp) (Fin.append i j ∘ P.lp) := by
        rw [← h1, ← h2, append_comp]
      constructor
      · rw [← Function.comp_assoc, hx]; exact P.left_read i j
      · rw [← Function.comp_assoc, hx]; exact P.right_read i j
    · rintro ⟨h1, h2⟩
      have hx : Fin.append i j = (x ∘ Fin.append α β) ∘ P.inv := by
        rw [← h1, ← h2]
        show Fin.append ((x ∘ Fin.append α β) ∘ P.ikp) ((x ∘ Fin.append α β) ∘ P.ilp) = _
        rw [append_comp, append_inv]
      constructor
      · rw [hx]; funext a
        simp only [Function.comp_apply]
        rw [show P.kp a = Fin.append P.kp P.lp (Fin.castAdd 4 a) from (Fin.append_left _ _ _).symm,
          P.h2, Fin.append_left]
      · rw [hx]; funext a
        simp only [Function.comp_apply]
        rw [show P.lp a = Fin.append P.kp P.lp (Fin.natAdd 4 a) from (Fin.append_right _ _ _).symm,
          P.h2, Fin.append_right]
  by_cases h : x ∘ α = Fin.append i j ∘ P.kp ∧ x ∘ β = Fin.append i j ∘ P.lp
  · rw [ite_eq_left h, ite_eq_left (key.1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (key.2 h'))]

section Global

variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ}

lemma ruleG_inv (M : Matrix (GI nf) (GI nf) ℂ) : ruleG P.ikp P.ilp (ruleG P.kp P.lp M) = M := by
  ext k l
  simp only [ruleG]
  congr 1
  · funext x; exact P.left_read' (k x) (l x)
  · funext x; exact P.right_read' (k x) (l x)

/-- The pair map `(i, j) ↦ (k, l)` as an equivalence of global index pairs. -/
def pairEquiv : (GI nf × GI nf) ≃ (GI nf × GI nf) where
  toFun ij := (fun x => Fin.append (ij.1 x) (ij.2 x) ∘ P.kp, fun x => Fin.append (ij.1 x) (ij.2 x) ∘ P.lp)
  invFun kl := (fun x => Fin.append (kl.1 x) (kl.2 x) ∘ P.ikp, fun x => Fin.append (kl.1 x) (kl.2 x) ∘ P.ilp)
  left_inv ij := by
    obtain ⟨i, j⟩ := ij
    simp only [Prod.mk.injEq]
    exact ⟨funext fun x => P.left_read (i x) (j x), funext fun x => P.right_read (i x) (j x)⟩
  right_inv kl := by
    obtain ⟨k, l⟩ := kl
    simp only [Prod.mk.injEq]
    exact ⟨funext fun x => P.left_read' (k x) (l x), funext fun x => P.right_read' (k x) (l x)⟩

/-- `ruleG` is a Hilbert–Schmidt unitary with inverse the inverse rule. -/
lemma trace_ruleG (N Z : Matrix (GI nf) (GI nf) ℂ) :
    (Nᴴ * ruleG P.kp P.lp Z).trace = ((ruleG P.ikp P.ilp N)ᴴ * Z).trace := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv P.pairEquiv _ _ fun ij => ?_
  obtain ⟨i, j⟩ := ij
  have hi : (fun x => Fin.append (Fin.append (i x) (j x) ∘ P.kp) (Fin.append (i x) (j x) ∘ P.lp) ∘ P.ikp)
      = i := funext fun x => P.left_read (i x) (j x)
  have hj : (fun x => Fin.append (Fin.append (i x) (j x) ∘ P.kp) (Fin.append (i x) (j x) ∘ P.lp) ∘ P.ilp)
      = j := funext fun x => P.right_read (i x) (j x)
  simp only [ruleG, pairEquiv, Equiv.coe_fn_mk, hi, hj]

end Global

end RulePos

end NPT.Cert
