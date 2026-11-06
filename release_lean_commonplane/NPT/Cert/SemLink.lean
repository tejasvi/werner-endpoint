/-
NPT.Cert.SemLink — the semantic functional of `NPT.Cert.Sem` (list data, rational arithmetic) expressed
through the operator calculus: per word, the block entries are `⟨B, Jᵀ ruleG(V_w) J⟩` and the objective is
`Tr(O V_w)/(2^k (2d^k)^4)`; by linearity, coefficient sums become functionals of the moment operators.
-/
import NPT.Cert.RuleData
import NPT.Cert.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert

/-! ### Rational → complex -/

/-- Entrywise cast of a rational matrix. -/
noncomputable def cq {ι κ : Type*} (M : Matrix ι κ ℚ) : Matrix ι κ ℂ := M.map (algebraMap ℚ ℂ)

lemma cq_mul {ι κ μ : Type*} [Fintype κ] (A : Matrix ι κ ℚ) (B : Matrix κ μ ℚ) :
    cq (A * B) = cq A * cq B := Matrix.map_mul

lemma cq_transpose {ι κ : Type*} (A : Matrix ι κ ℚ) : cq Aᵀ = (cq A)ᵀ := rfl

lemma cq_SelOp {n m : ℕ} (α β : Fin m → Fin m) : cq (SelOp ℚ n α β) = SelOp ℂ n α β := by
  ext i j
  rw [cq, Matrix.map_apply]
  simp only [SelOp, Matrix.sum_apply, single_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

lemma cq_VG {n S : ℕ} (p : Fin 24) : cq (VG ℚ n S p) = VG ℂ n S p := cq_SelOp _ _

lemma cq_ruleOp {n : ℕ} (kp lp : Fin 4 → Fin (4 + 4)) (M : Matrix (Dig n 4) (Dig n 4) ℚ) :
    cq (ruleOp kp lp M) = ruleL kp lp (cq M) := rfl

lemma cq_trace {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : ((trace A : ℚ) : ℂ) = trace (cq A) := by
  simp only [Matrix.trace, Matrix.diag, cq, Matrix.map_apply]
  push_cast
  rfl

/-- The local block map, cast to `ℂ`, through the rule operator. -/
lemma cq_Kmat (n : ℕ) (J : List (List Int)) (dim : ℕ) (kpos lpos : List ℕ) (p : Fin 24) :
    cq (Kmat n J dim kpos lpos p) =
      (cq (Jm n 4 J dim))ᵀ * ruleL (posOf kpos) (posOf lpos) (VG ℂ n 0 p) * cq (Jm n 4 J dim) := by
  unfold Kmat
  rw [cq_mul, cq_mul, cq_transpose, cq_ruleOp, cq_VG]

/-! ### Kronecker facts -/

section KronFacts

variable {L : Type*} [Fintype L] [DecidableEq L]

lemma kron_transpose {ι κ : L → Type*} (A : (l : L) → Matrix (ι l) (κ l) ℂ) :
    (kron A)ᵀ = kron fun l => (A l)ᵀ := rfl

lemma trace_kron {ι : L → Type*} [∀ l, Fintype (ι l)] [∀ l, DecidableEq (ι l)]
    (A : (l : L) → Matrix (ι l) (ι l) ℂ) : trace (kron A) = ∏ l, trace (A l) := by
  simp only [Matrix.trace, Matrix.diag, kron]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]

end KronFacts

/-! ### Blocks -/

namespace Sem.CertD

variable (C : CertD)

/-- Module matrix of type `t` at factor `l`, as a complex matrix. -/
noncomputable def Jt (t : TypeD) (l : Fin (C.k + 1)) :
    Matrix (Dig (nf C.k C.d l) 4) (Fin (C.tdim t l)) ℂ :=
  cq (Jm (nf C.k C.d l) 4 (C.mods.getD (t.mods.getD l.val 0) default).J (C.tdim t l))

/-- Global module matrix `J = ⊗_l J_l` of type `t`. -/
noncomputable def JG (t : TypeD) : Matrix (GI (nf C.k C.d)) ((l : Fin (C.k + 1)) → Fin (C.tdim t l)) ℂ :=
  kron (C.Jt t)

/-- The rule of entry `(r, s)` of type `t`. -/
def ruleOf (t : TypeD) (r s : ℕ) : RuleD := (t.rules.getD r []).getD s default

/-- Complex block entry `B^t_{rs}[μ, ν]`. -/
noncomputable def Bc (t : TypeD) (r s : ℕ) (μ ν : (l : Fin (C.k + 1)) → Fin (C.tdim t l)) : ℂ :=
  (C.Bq t r s (flatMI (C.tdim t) μ) (flatMI (C.tdim t) ν) : ℂ)

/-- The block functional of one entry on a moment operator. -/
noncomputable def blkOp (t : TypeD) (r s : ℕ) (M : Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ) : ℂ :=
  ∑ μ, ∑ ν, C.Bc t r s μ ν *
    ((C.JG t)ᵀ * ruleG (posOf (ruleOf t r s).kpos) (posOf (ruleOf t r s).lpos) M * C.JG t) μ ν

lemma JG_rule_VW (t : TypeD) (kp lp : Fin 4 → Fin (4 + 4)) (w : Fin (C.k + 1) → Fin 24) :
    (C.JG t)ᵀ * ruleG kp lp (VW (nf C.k C.d) 0 w) * C.JG t =
      kron fun l => (C.Jt t l)ᵀ * ruleL kp lp (VG ℂ (nf C.k C.d l) 0 (w l)) * C.Jt t l := by
  unfold JG VW
  rw [kron_transpose, ruleG_kron, kron_mul, kron_mul]

/-- **Per-word block link.** -/
lemma blk_eq (t : TypeD) (r s : ℕ) (w : Fin (C.k + 1) → Fin 24) :
    ((C.blk t r s w : ℚ) : ℂ) = C.blkOp t r s (VW (nf C.k C.d) 0 w) := by
  unfold blk blkOp
  rw [JG_rule_VW]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  simp only [kron]
  refine Finset.prod_congr rfl fun l _ => ?_
  have := congrFun (congrFun (cq_Kmat (nf C.k C.d l) (C.mods.getD (t.mods.getD l.val 0) default).J
    (C.tdim t l) (ruleOf t r s).kpos (ruleOf t r s).lpos (w l)) (μ l)) (ν l)
  rw [cq, Matrix.map_apply] at this
  exact this

lemma blkOp_add (t : TypeD) (r s : ℕ) (M N : Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ) :
    C.blkOp t r s (M + N) = C.blkOp t r s M + C.blkOp t r s N := by
  unfold blkOp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← mul_add]
  congr 1
  have : ruleG (posOf (ruleOf t r s).kpos) (posOf (ruleOf t r s).lpos) (M + N) =
      ruleG (posOf (ruleOf t r s).kpos) (posOf (ruleOf t r s).lpos) M +
        ruleG (posOf (ruleOf t r s).kpos) (posOf (ruleOf t r s).lpos) N := rfl
  rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]

lemma blkOp_smul (t : TypeD) (r s : ℕ) (a : ℂ) (M : Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ) :
    C.blkOp t r s (a • M) = a * C.blkOp t r s M := by
  unfold blkOp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have : ruleG (posOf (ruleOf t r s).kpos) (posOf (ruleOf t r s).lpos) (a • M) =
      a • ruleG (posOf (ruleOf t r s).kpos) (posOf (ruleOf t r s).lpos) M := rfl
  rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Linear block link**: coefficient sums of block entries are block functionals of the moments. -/
lemma sum_blk (t : TypeD) (r s : ℕ) (c : (Fin (C.k + 1) → Fin 24) → ℂ) :
    ∑ w, c w * ((C.blk t r s w : ℚ) : ℂ) = C.blkOp t r s (∑ w, c w • VW (nf C.k C.d) 0 w) := by
  simp only [blk_eq]
  induction (Finset.univ : Finset (Fin (C.k + 1) → Fin 24)) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold blkOp
    have h0 : ruleG (posOf (ruleOf t r s).kpos) (posOf (ruleOf t r s).lpos)
        (0 : Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ) = 0 := rfl
    simp [h0]
  | insert w s hw ih => rw [Finset.sum_insert hw, Finset.sum_insert hw, blkOp_add, blkOp_smul, ih]

end Sem.CertD

/-! ### Objective -/

namespace Sem.CertD

variable (C : CertD)

lemma trace_fun_congr {n n' : ℕ} (h : n = n') (F : ∀ m : ℕ, ℂ) : F n = F n' := by subst h; rfl

lemma Oobj_mul_VW (w : Fin (C.k + 1) → Fin 24) :
    Phys.Oobj C.k C.d * VW (nf C.k C.d) 0 w =
      kron fun l => (if l.val < C.k then (2 : ℂ) • VG ℂ (nf C.k C.d l) 0 0 - VG ℂ (nf C.k C.d l) 0 21
        else VG ℂ (nf C.k C.d l) 0 21) * VG ℂ (nf C.k C.d l) 0 (w l) := by
  unfold Phys.Oobj VW
  rw [kron_mul]

/-- **Per-word objective link.** -/
lemma obj_eq (w : Fin (C.k + 1) → Fin 24) :
    ((C.obj w : ℚ) : ℂ) = (Phys.Oobj C.k C.d * VW (nf C.k C.d) 0 w).trace /
      (2 ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4) := by
  rw [Oobj_mul_VW, trace_kron, Fin.prod_univ_castSucc]
  unfold obj
  push_cast
  congr 1
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i.castSucc : Fin (C.k + 1)).val < C.k := by simp
    rw [if_pos hi, Matrix.sub_mul, Matrix.smul_mul, VG_zero (by norm_num), Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    simp only [cq_trace, cq_mul, cq_VG]
    have h := Phys.nf_site C.k C.d i
    exact (trace_fun_congr h (fun m => 2 * (VG ℂ m 0 (w i.castSucc)).trace -
      (VG ℂ m 0 21 * VG ℂ m 0 (w i.castSucc)).trace)).symm
  · rw [if_neg (lt_irrefl C.k)]
    simp only [cq_trace, cq_mul, cq_VG]
    exact (trace_fun_congr (Phys.nf_aux C.k C.d) (fun m =>
      (VG ℂ m 0 21 * VG ℂ m 0 (w (Fin.last C.k))).trace)).symm

lemma sum_obj (c : (Fin (C.k + 1) → Fin 24) → ℂ) :
    ∑ w, c w * ((C.obj w : ℚ) : ℂ) = (Phys.Oobj C.k C.d * ∑ w, c w • VW (nf C.k C.d) 0 w).trace /
      (2 ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4) := by
  simp only [obj_eq, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Finset.sum_div, mul_div_assoc]

end Sem.CertD

end NPT.Cert
