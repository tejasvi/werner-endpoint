/-
NPT.K4.Phys5 — the physical side for five moment families (five-family certificate): `31` aaab, `22` aabb, `13` bbba,
`40` aaaa, `04` bbbb.

`famPat5` / `famLet5` / `inG5` extend `Phys.famPat` / `Sem.famLet` / `Sem.inG` (equal for `f < 3`; for `40` and `04`
the family group is all of `S_4`), and `Xf5 f = |w_f⟩⟨w_f|` with the pattern vector of `famPat5 f`.  The physical
facts used by the soundness proof are restated for `Xf5`, with the proofs of `NPT.Cert.Phys` (all generic in the
pattern): site permutations, conjugation, transpose, invariance under `G_f`, physical entries of consistent rules
(`phys_rule5`), PSD physical blocks with record rules (`blockR_phys_psd5`), traces (`trace_Xf5`).
-/
import NPT.K4.Rule5
import NPT.K4.Traces
import NPT.Cert.PhysSym

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Phys NPT.Cert.Phys.SymAux
open scoped ComplexOrder

namespace NPT.K4

/-- Patterns of the five families (codes 0 = a, 2 = b). -/
def famPat5 (f : ℕ) : Fin 4 → Fin 4 :=
  match f with
  | 0 => ![0, 0, 0, 2]
  | 1 => ![0, 0, 2, 2]
  | 2 => ![2, 2, 2, 0]
  | 3 => ![0, 0, 0, 0]
  | _ => ![2, 2, 2, 2]

/-- Letters of the five families (true = a). -/
def famLet5 (f : ℕ) : List Bool :=
  match f with
  | 0 => [true, true, true, false]
  | 1 => [true, true, false, false]
  | 2 => [false, false, false, true]
  | 3 => [true, true, true, true]
  | _ => [false, false, false, false]

/-- `g ∈ G_f` for the five families (`L[g[i]] = L[i]`). -/
def inG5 (f : ℕ) (g : Fin 24) : Bool :=
  (List.finRange 4).all fun i => (famLet5 f).getD (pf g i).val false == (famLet5 f).getD i.val false

lemma famPat5_lt3 {f : ℕ} (hf : f < 3) : famPat5 f = famPat f := by interval_cases f <;> rfl

lemma inG5_lt3 {f : ℕ} (hf : f < 3) : inG5 f = inG f := by interval_cases f <;> rfl

variable {k d : ℕ}

/-- Family moment operator for five families. -/
def Xf5 (f : ℕ) (a b : V1 k d → ℂ) : Matrix (GI (nf k d)) (GI (nf k d)) ℂ :=
  vecMulVec (patVec (famPat5 f) a b) (star (patVec (famPat5 f) a b))

lemma Xf5_lt3 {f : ℕ} (hf : f < 3) (a b : V1 k d → ℂ) : Xf5 f a b = Xf f a b := by
  unfold Xf5 Xf; rw [famPat5_lt3 hf]

theorem siteAct_Xf5 (σ : Equiv.Perm (Fin k)) (f : ℕ) (A B : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    siteAct σ (Xf5 f (vecOf A) (vecOf B)) = Xf5 f (vecOf (permRows σ A)) (vecOf (permRows σ B)) := by
  have hw : ∀ i, patVec (famPat5 f) (vecOf A) (vecOf B) (permIdx σ i) =
      patVec (famPat5 f) (vecOf (permRows σ A)) (vecOf (permRows σ B)) i := by
    intro i
    unfold patVec
    refine Finset.prod_congr rfl fun r _ => ?_
    exact chi_congr _ (vecOf_repl_permIdx σ A i r) (vecOf_repl_permIdx σ B i r)
  ext i j
  simp only [siteAct, Xf5, vecMulVec_apply, Pi.star_apply, hw]

theorem conjM_Xf5 (f : ℕ) (a b : V1 k d → ℂ) :
    conjM (Xf5 f a b) = Xf5 f (fun v => star (a v)) (fun v => star (b v)) := by
  have hchi : ∀ c u, chi c (fun v => star (a v)) (fun v => star (b v)) u = star (chi c a b u) := by
    intro c u; fin_cases c <;> simp [chi]
  have hw : ∀ i, patVec (famPat5 f) (fun v => star (a v)) (fun v => star (b v)) i =
      star (patVec (famPat5 f) a b i) := by
    intro i; simp only [patVec, hchi, star_prod]
  ext i j
  simp only [conjM, Xf5, Matrix.map_apply, vecMulVec_apply, Pi.star_apply, hw, star_mul', star_star]

lemma Xf5_transpose (f : ℕ) (a b : V1 k d → ℂ) : (Xf5 f a b)ᵀ = conjM (Xf5 f a b) := by
  ext i j
  simp only [Xf5, transpose_apply, conjM, Matrix.map_apply, vecMulVec_apply, Pi.star_apply, star_mul',
    star_star]
  ring

lemma famPat5_inG5 : ∀ f : Fin 5, ∀ g : Fin 24, ∀ r : Fin 4,
    inG5 f.val g = true → famPat5 f.val (pf g r) = famPat5 f.val r := by decide +kernel

lemma famPat5_pf {f : ℕ} (hf : f < 5) {g : Fin 24} (hg : inG5 f g = true) (r : Fin 4) :
    famPat5 f (pf g r) = famPat5 f r := famPat5_inG5 ⟨f, hf⟩ g r hg

lemma famPat5_pinvf {f : ℕ} (hf : f < 5) {h : Fin 24} (hh : inG5 f h = true) (r : Fin 4) :
    famPat5 f (pinvf h r) = famPat5 f r := by
  have := famPat5_pf hf hh (pinvf h r)
  rw [pf_pinvf] at this
  exact this.symm

theorem VWc_Xf5 {f : ℕ} (hf : f < 5) (g h : Fin 24) (hg : inG5 f g = true) (hh : inG5 f h = true)
    (a b : V1 k d → ℂ) : VWc g * Xf5 f a b * VWc h = Xf5 f a b := by
  ext i j
  rw [mul_VWc_apply, VWc_mul_apply]
  simp only [Xf5, vecMulVec_apply, Pi.star_apply]
  rw [patVec_relabel (famPat5 f) a b (pf g) (pinvf g) (pinvf_pf g) (pf_pinvf g) (famPat5_pf hf hg) i,
    patVec_relabel (famPat5 f) a b (pinvf h) (pf h) (pf_pinvf h) (pinvf_pf h) (famPat5_pinvf hf hh) j]

/-! ### Physical entries and blocks -/

/-- Source codes of a five-family entry (as `Phys.srcCode`). -/
def srcCode5 (f : ℕ) (u : Fin (4 + 4)) : Fin 4 :=
  Fin.append (famPat5 f) (fun r => conjCode (famPat5 f r)) u

/-- Consistency of an entry rule with a five-family moment and the row patterns (decidable). -/
def Consistent5 (f : ℕ) (pr ps : Fin 4 → Fin 4) (kp lp : Fin 4 → Fin (4 + 4)) : Prop :=
  ∀ u, srcCode5 f u = tgtCode pr ps (Fin.append kp lp u)

instance (f : ℕ) (pr ps : Fin 4 → Fin 4) (kp lp : Fin 4 → Fin (4 + 4)) :
    Decidable (Consistent5 f pr ps kp lp) := by unfold Consistent5; infer_instance

/-- **Physical entry** for five families (proof of `Phys.phys_rule`). -/
theorem phys_rule5 (P : RulePos) {f : ℕ} {pr ps : Fin 4 → Fin 4}
    (hc : Consistent5 f pr ps P.kp P.lp) (a b : V1 k d → ℂ) :
    ruleG P.kp P.lp (Xf5 f a b) = vecMulVec (patVec pr a b) (star (patVec ps a b)) := by
  ext i j
  simp only [ruleG, Xf5, vecMulVec_apply, Pi.star_apply, patVec, star_prod]
  have hsrc : (∏ r, chi (famPat5 f r) a b (repl (fun x => Fin.append (i x) (j x) ∘ P.kp) r)) *
      ∏ r, star (chi (famPat5 f r) a b (repl (fun x => Fin.append (i x) (j x) ∘ P.lp) r)) =
      ∏ u : Fin (4 + 4), chi (srcCode5 f u) a b (posV i j (Fin.append P.kp P.lp u)) := by
    rw [prod_eight]
    refine Finset.prod_congr rfl fun u _ => ?_
    refine Fin.addCases (fun r => ?_) (fun r => ?_) u
    · rw [Fin.append_left, srcCode5, Fin.append_left, Fin.append_left]; rfl
    · rw [Fin.append_right, srcCode5, Fin.append_right, Fin.append_right, chi_conjCode]; rfl
  have htgt : (∏ r, chi (pr r) a b (repl i r)) * ∏ r, star (chi (ps r) a b (repl j r)) =
      ∏ c : Fin (4 + 4), chi (tgtCode pr ps c) a b (posV i j c) := by
    rw [prod_eight]
    refine Finset.prod_congr rfl fun c _ => ?_
    refine Fin.addCases (fun r => ?_) (fun r => ?_) c
    · rw [Fin.append_left, tgtCode, Fin.append_left]
      congr 1
      funext x; simp only [posV, repl, Fin.append_left]
    · rw [Fin.append_right, tgtCode, Fin.append_right, chi_conjCode]
      congr 2
      funext x; simp only [posV, repl, Fin.append_right]
  rw [hsrc, htgt]
  refine Fintype.prod_equiv ⟨Fin.append P.kp P.lp, P.inv, P.h2, P.h1⟩ _ _ fun u => ?_
  simp only [Equiv.coe_fn_mk]
  rw [hc u]

/-- A type whose record rules are valid and consistent with its row patterns has PSD physical blocks. -/
theorem blockR_phys_psd5 {R : ℕ} (t : TypeD) (ri : Fin R → Fin R → RuleRec) (fam : Fin R → Fin R → ℕ)
    (hok : ∀ r s, (ri r s).OK)
    (hcons : ∀ r s, Consistent5 (fam r s) (patOf t r) (patOf t s) (ri r s).kp (ri r s).lp)
    (a b : V1 k d → ℂ) :
    (blockR ri fam (fun f => Xf5 f a b)).PosSemidef := by
  have e : blockR ri fam (fun f => Xf5 f a b) =
      vecMulVec (fun x : Fin R × GI (nf k d) => patVec (patOf t x.1) a b x.2)
        (star fun x : Fin R × GI (nf k d) => patVec (patOf t x.1) a b x.2) := by
    ext x y
    simp only [blockR]
    rw [show (ri x.1 y.1).kp = (hok x.1 y.1).pos.kp from rfl,
      show (ri x.1 y.1).lp = (hok x.1 y.1).pos.lp from rfl,
      phys_rule5 (hok x.1 y.1).pos (hcons x.1 y.1) a b]
    simp [vecMulVec_apply]
  rw [e]
  exact posSemidef_vecMulVec_self_star _

/-- Trace of a pattern projector: `s⁴` when `‖a‖² = ‖b‖² = s`, for every pattern. -/
lemma trace_patProj (pat : Fin 4 → Fin 4) (a b : V1 k d → ℂ) (s : ℝ) (ha : nsq k d a = s)
    (hb : nsq k d b = s) :
    (vecMulVec (patVec pat a b) (star (patVec pat a b))).trace = ((s ^ 4 : ℝ) : ℂ) := by
  have h1 : (vecMulVec (patVec pat a b) (star (patVec pat a b))).trace =
      ∑ i, ∏ r, ((Complex.normSq (chi (pat r) a b (repl i r)) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, vecMulVec_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : patVec pat a b i * star (patVec pat a b i) =
        ((Complex.normSq (patVec pat a b i) : ℝ) : ℂ) := Complex.mul_conj _
    rw [e, patVec, map_prod, Complex.ofReal_prod]
  rw [h1, Obj.sum_GI]
  simp only [Fin.prod_univ_four, Obj.repl_symm]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [nsq_chi _ a b s ha hb, nsq_chi _ a b s ha hb, nsq_chi _ a b s ha hb, nsq_chi _ a b s ha hb]
  push_cast
  ring

lemma trace_Xf5 (f : ℕ) (a b : V1 k d → ℂ) (s : ℝ) (ha : nsq k d a = s) (hb : nsq k d b = s) :
    (Xf5 f a b).trace = ((s ^ 4 : ℝ) : ℂ) := trace_patProj (famPat5 f) a b s ha hb

end NPT.K4

#print axioms NPT.K4.blockR_phys_psd5
#print axioms NPT.K4.VWc_Xf5
#print axioms NPT.K4.trace_Xf5
