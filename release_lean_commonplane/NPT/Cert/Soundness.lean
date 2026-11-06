/-
NPT.Cert.Soundness — **soundness of the moment certificates**: a well-formed certificate (`WF`) whose
identity fact holds (`IdFact`, the class sums of `Λ` vanish) and whose multipliers are PSD proves
`EP (Fin k) d (1/2)`.

Route (no Haar measure, no Schur–Weyl): for a rank-two `C = A Bᴴ` in normal form, the physical moments
`X_f`, symmetrized over site permutations and complex conjugation, are projected (Hilbert–Schmidt) onto the
word algebra; the projections `Y_f` have orbit-constant coefficients (`sym_coeffs`), so the identity fact
gives `Σ_f Σ_w c_f(w) Λ_f(w) = 0`, i.e. objective = Σ blocks + Σ equalities. Blocks are `≥ 0` (Lemma P on the
walled-Brauer algebras), equalities vanish (intertwining), and the objective is `2·k!·‖a‖⁴·2^k·q(C)/N`.
-/
import NPT.Cert.SoundPrep
import NPT.Cert.Sym
import NPT.Cert.PhysSym
import NPT.Cert.EqLink
import NPT.Cert.PhysObj
import NPT.Cert.PhysEq
import NPT.Cert.PhysStiefel
import NPT.Cert.NormalForm

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.Cert

/-- An equality spec built from a traced-slot combination. -/
def specOf (c kind : ℕ) (mk : List ℕ) : EqSpecD := ⟨sget c 0, [sget c 1, sget c 2, sget c 3], kind, mk⟩

/-- Stiefel-shaped equality group (ep3core `stiefel31/22/13`). -/
def StiefelShape (C : CertD) (g : EqGroupD) : Prop :=
  ∃ f c : ℕ, (((f = 0 ∨ f = 1) ∧ c = 0) ∨ (f = 2 ∧ c = 1)) ∧ ∃ P, g.parts = [P] ∧ P.fam = f ∧ P.sign = 1 ∧
    ∀ l : Fin (C.k + 1), P.specs.getD l.val default =
      specOf c (if l.val < C.k then 0 else 1) (P.specs.getD l.val default).mkeys

/-- Marginal-shaped equality group (ep3core `aab`, `abb`). -/
def MargShape (C : CertD) (g : EqGroupD) : Prop :=
  ∃ f1 c1 f2 c2 : ℕ, ((f1 = 0 ∧ c1 = 2 ∧ f2 = 1 ∧ c2 = 2) ∨ (f1 = 1 ∧ c1 = 3 ∧ f2 = 2 ∧ c2 = 4)) ∧
    ∃ P1 P2, g.parts = [P1, P2] ∧ P1.fam = f1 ∧ P1.sign = 1 ∧ P2.fam = f2 ∧ P2.sign = -1 ∧
      ∀ l : Fin (C.k + 1), P1.specs.getD l.val default = specOf c1 0 (P1.specs.getD l.val default).mkeys ∧
        P2.specs.getD l.val default = specOf c2 0 (P1.specs.getD l.val default).mkeys

/-- **Well-formedness** of a certificate: verified entry rules consistent with the row patterns, a common cut
per type, families in range, and the canonical equality groups. -/
structure WF (C : CertD) : Prop where
  hk : 1 ≤ C.k
  hd : 2 ≤ C.d
  types : ∀ t ∈ C.types, ∃ ri : Fin t.nrows → Fin t.nrows → ℕ, ∃ S ∈ cutsUsed,
    (∀ r s, ri r s < nRules) ∧ (∀ r s, rcut (ri r s) = S) ∧
    (∀ r s : Fin t.nrows, posOf (Sem.CertD.ruleOf t r.val s.val).kpos = rkp (ri r s)) ∧
    (∀ r s : Fin t.nrows, posOf (Sem.CertD.ruleOf t r.val s.val).lpos = rlp (ri r s)) ∧
    (∀ r s : Fin t.nrows, (Sem.CertD.ruleOf t r.val s.val).fam < 3) ∧
    (∀ r s : Fin t.nrows, Phys.Consistent (Sem.CertD.ruleOf t r.val s.val).fam (patOf t r.val) (patOf t s.val)
      (rkp (ri r s)) (rlp (ri r s)))
  eqs : ∀ g ∈ C.eqs, StiefelShape C g ∨ MargShape C g

lemma ruleOK_of_lt {i : ℕ} (h : i < nRules) : RuleOK i := ruleTab_ok ⟨i, h⟩

lemma stKer_eq_stF {k d : ℕ} (c : ℕ) :
    stKer (nf := nf k d) (fun l : Fin (k + 1) => ¬ l.val < k) c = Phys.stF (csl c) (cord c) := by
  funext l
  simp only [stKer, Phys.stF]
  by_cases h : l.val < k
  · rw [if_neg (not_not.2 h), if_pos h]
  · rw [if_pos h, if_neg h]

lemma nsq_vecOf {k d : ℕ} (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    Phys.nsq k d (Phys.vecOf A) = ∑ x, ∑ α, Complex.normSq (A x α) := by
  unfold Phys.nsq
  rw [show (∑ v, Complex.normSq (Phys.vecOf A v)) = ∑ p : (Fin k → Fin d) × Fin 2, Complex.normSq (A p.1 p.2)
    from Fintype.sum_equiv (Phys.Obj.siteAuxEquiv k d) _ _ (fun v => rfl), Fintype.sum_prod_type]

theorem soundness (C : CertD) [NeZero C.d] (hwf : WF C) (hid : IdFact C)
    (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef) : NPT.EP (Fin C.k) C.d (1 / 2) := by
  intro Cop hrank
  rcases normal_form hwf.hk hwf.hd Cop hrank with h0 | ⟨A, B, hAB, ⟨cA, hcA, hA⟩, hB⟩
  · rw [h0, q_zero]
  -- transformed matrices and symmetrized physical moments
  let Aε : Bool → Matrix (Fin C.k → Fin C.d) (Fin 2) ℂ := fun ε => if ε then A.map star else A
  let Bε : Bool → Matrix (Fin C.k → Fin C.d) (Fin 2) ℂ := fun ε => if ε then B.map star else B
  let ap : Equiv.Perm (Fin C.k) × Bool → Phys.V1 C.k C.d → ℂ := fun p => Phys.vecOf (permRows p.1 (Aε p.2))
  let bp : Equiv.Perm (Fin C.k) × Bool → Phys.V1 C.k C.d → ℂ := fun p => Phys.vecOf (permRows p.1 (Bε p.2))
  let X : ℕ → Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ := fun f => ∑ p, Phys.Xf f (ap p) (bp p)
  have hgram : ∀ p : Equiv.Perm (Fin C.k) × Bool,
      (permRows p.1 (Aε p.2))ᴴ * permRows p.1 (Aε p.2) = (cA : ℂ) • 1 := by
    rintro ⟨σ, ε⟩
    rw [Phys.permRows_gram]
    cases ε
    · simpa [Aε] using hA
    · simp only [Aε, ↓reduceIte]
      rw [Phys.map_star_gram, hA]
      ext i j
      simp [Matrix.smul_apply, one_apply]
      split_ifs <;> simp [Complex.conj_ofReal]
  have hnsq : ∀ p : Equiv.Perm (Fin C.k) × Bool, Phys.nsq C.k C.d (ap p) = Phys.nsq C.k C.d (bp p) := by
    rintro ⟨σ, ε⟩
    simp only [ap, bp, Phys.nsq_permRows]
    cases ε
    · simp only [Aε, Bε, Bool.false_eq_true, ↓reduceIte]; rw [nsq_vecOf, nsq_vecOf, hB]
    · simp only [Aε, Bε, ↓reduceIte, Phys.nsq_map_star]; rw [nsq_vecOf, nsq_vecOf, hB]
  -- projections
  have hXproj : ∀ f, ∃ Y, IsProj (spanS (nf := nf C.k C.d) 0) (X f) Y := fun f => exists_isProj _ _
  choose Y hY using hXproj
  -- invariances of X
  have hG : ∀ f, f < 3 → ∀ g h : Fin 24, inG f g = true → inG f h = true → VWc g * X f * VWc h = X f := by
    intro f hf g h hg hh
    simp only [X, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun p _ => Phys.VWc_Xf f hf g h hg hh _ _
  have hS : ∀ f (σ : Equiv.Perm (Fin C.k)), siteAct σ (X f) = X f := by
    intro f σ
    simp only [X, siteAct_sum, ap, bp, Phys.siteAct_Xf, permRows_comp]
    exact Fintype.sum_equiv (Equiv.prodCongr (Equiv.mulLeft σ) (Equiv.refl Bool)) _ _ fun p => rfl
  have hT : ∀ f, (X f)ᵀ = X f := by
    intro f
    simp only [X, transpose_sum, Xf_transpose, Phys.conjM_Xf, ap, bp, Phys.vecOf_map_star, permRows_map_star]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_bool, Fintype.sum_bool]
    simp only [Aε, Bε, Bool.false_eq_true, ↓reduceIte]
    first
      | exact add_comm _ _
      | (rw [map_star_map_star, map_star_map_star]; exact add_comm _ _)
  -- orbit-constant coefficients
  have hsym : ∀ f, f < 3 → ∃ c : (Fin (C.k + 1) → Fin 24) → ℂ, Y f = ∑ w, c w • VW (nf C.k C.d) 0 w ∧
      ∀ (g1 g2 : Fin 24) (σ : Fin C.k → Fin C.k) (ε : Bool) (w : Fin (C.k + 1) → Fin 24),
        inG f g1 = true → inG f g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w :=
    fun f hf => sym_coeffs (hY f) (hG f hf) (hS f) (hT f)
  choose! c hcY hcinv using hsym
  -- the identity fact
  have hfam : ∀ t ∈ C.types, ∀ r < t.nrows, ∀ s < t.nrows, (Sem.CertD.ruleOf t r s).fam < 3 := by
    intro t ht r hr s hs
    obtain ⟨ri, S, hS, hlt, hcut, hkp, hlp, hf3, hcons⟩ := hwf.types t ht
    exact hf3 ⟨r, hr⟩ ⟨s, hs⟩
  have hpfam : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, P.fam < 3 := by
    intro g hg P hP
    rcases hwf.eqs g hg with ⟨f, c', hfc, P', hparts, hPf, -, -⟩ | ⟨f1, c1, f2, c2, hfc, P1, P2, hparts, h1, -, h2, -, -⟩
    · rw [hparts, List.mem_singleton] at hP; subst hP; rw [hPf]; omega
    · rw [hparts] at hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rw [h1]; omega
      · rw [h2]; omega
  have hzero : ∑ f ∈ Finset.range 3, ∑ w, c f w * ((C.Λ f w : ℚ) : ℂ) = 0 := by
    refine Finset.sum_eq_zero fun f hf => ?_
    have hf' := Finset.mem_range.1 hf
    exact C.class_sum_zero hid hf' (c f) (class_const C hid hf' (c f) (hcinv f hf'))
  rw [C.Lambda_expand c hfam hpfam] at hzero
  -- equalities vanish
  have heq : (C.eqs.map fun g => (g.parts.map fun P =>
      (P.sign : ℂ) * ∑ w, c P.fam w * ((C.eqVal g P w : ℚ) : ℂ)).sum).sum = 0 := by
    refine List.sum_eq_zero fun z hz => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hz
    rcases hwf.eqs g hg with ⟨f, c', hfc, P, hparts, hPf, hPs, hspec⟩ |
        ⟨f1, c1, f2, c2, hfc, P1, P2, hparts, hP1f, hP1s, hP2f, hP2s, hspec⟩
    · -- Stiefel
      rw [hparts]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hPs, hPf]
      have hc5 : c' < 5 := by omega
      have hf3 : f < 3 := by omega
      have hnat : [sget c' 1, sget c' 2, sget c' 3] = natOrder (sget c' 0) := by
        rcases hfc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
      have hXst : applyG (stKer (nf := nf C.k C.d) (fun l : Fin (C.k + 1) => ¬ l.val < C.k) c') (X f) = 0 := by
        simp only [X, applyG_sum, stKer_eq_stF]
        refine Finset.sum_eq_zero fun p _ => ?_
        rcases hfc with ⟨hf01, rfl⟩ | ⟨rfl, rfl⟩
        · rw [csl_cord_0.1, csl_cord_0.2]
          rcases hf01 with rfl | rfl
          · exact Phys.stiefel31_phys _ cA (hgram p) _
          · exact Phys.stiefel22_phys _ cA (hgram p) _
        · rw [csl_cord_1.1, csl_cord_1.2]
          exact Phys.stiefel13_phys _ cA (hgram p) _
      have hc'lt : c' < 5 := hc5
      have hYst := stiefel_proj (slotTab_ok ⟨c', hc5⟩) (fun p => trTab_ok ⟨c', hc5⟩ p)
        (fun q t => embTab_ok ⟨c', hc5⟩ q t) (fun l : Fin (C.k + 1) => ¬ l.val < C.k) (hY f) hXst
      rw [hcY f hf3] at hYst
      have := eq_stief_link C g P hc5 hnat (fun l => (P.specs.getD l.val default).mkeys)
        (fun l => hspec l) (by have := hwf.hd; omega) (c f) hYst
      rw [this]; simp
    · -- marginal
      rw [hparts]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hP1s, hP2s, hP1f, hP2f]
      have hc1 : c1 < 5 := by omega
      have hc2 : c2 < 5 := by omega
      have hf1 : f1 < 3 := by omega
      have hf2 : f2 < 3 := by omega
      have hXm : applyG (trKer (nf := nf C.k C.d) c1) (X f1) = applyG (trKer (nf := nf C.k C.d) c2) (X f2) := by
        simp only [X, applyG_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rcases hfc with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · show applyG (fun _ => delK (csl 2) (cord 2)) _ = applyG (fun _ => delK (csl 2) (cord 2)) _
          rw [csl_cord_2.1, csl_cord_2.2]
          exact Phys.aab_phys _ _ (hnsq p)
        · show applyG (fun _ => delK (csl 3) (cord 3)) _ = applyG (fun _ => delK (csl 4) (cord 4)) _
          rw [csl_cord_3.1, csl_cord_3.2, csl_cord_4.1, csl_cord_4.2]
          exact Phys.abb_phys _ _ (hnsq p)
      have hYm := marginal_proj (slotTab_ok ⟨c1, hc1⟩) (slotTab_ok ⟨c2, hc2⟩) (fun p => trTab_ok ⟨c1, hc1⟩ p)
        (fun p => trTab_ok ⟨c2, hc2⟩ p) (fun q t => embTab_ok ⟨c1, hc1⟩ q t) (fun q t => embTab_ok ⟨c2, hc2⟩ q t)
        (hY f1) (hY f2) hXm
      rw [hcY f1 hf1, hcY f2 hf2] at hYm
      have := eq_marg_link C g P1 P2 hc1 hc2 (fun l => (P1.specs.getD l.val default).mkeys)
        (fun l => (hspec l).1) (fun l => (hspec l).2) (by have := hwf.hd; omega) (c f1) (c f2) hYm
      rw [this]; push_cast; ring
  -- blocks are nonnegative
  have hblk : 0 ≤ (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
      ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum := by
    refine List.sum_nonneg fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    obtain ⟨ri, S, hSc, hlt, hcut, hkp, hlp, hf3, hcons⟩ := hwf.types t ht
    let fam : Fin t.nrows → Fin t.nrows → ℕ := fun r s => (Sem.CertD.ruleOf t r.val s.val).fam
    have hok : ∀ r s, RuleOK (ri r s) := fun r s => ruleOK_of_lt (hlt r s)
    have hXb : (blockM ri fam X).PosSemidef := by
      simp only [X]
      rw [blockM_sum]
      exact posSemidef_sum _ fun p _ => blockM_phys_psd t ri fam hok hcons _ _
    have hYb := block_psd hSc ri fam hok hcut hY hXb
    have hnn := C.blk_type_nonneg t ri fam hkp hlp Y hYb (hpsd t ht)
    have e : ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
        ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ) =
        ∑ r : Fin t.nrows, ∑ s : Fin t.nrows, C.blkOp t r.val s.val (Y (fam r s)) := by
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [C.sum_blk, hcY _ (hf3 r s)]
    rw [e]; exact hnn
  -- the objective
  have hobj : ∑ w, c 0 w * ((C.obj w : ℚ) : ℂ) =
      (Phys.Oobj C.k C.d * X 0).trace / (2 ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4) := by
    rw [C.sum_obj, ← hcY 0 (by norm_num), trace_Oobj_proj (hY 0)]
  set r0 : ℝ := (Phys.nsq C.k C.d (Phys.vecOf A)) ^ 2 * 2 ^ C.k * NPT.q (1 / 2) (A * Bᴴ) with hr0
  have hTX : (Phys.Oobj C.k C.d * X 0).trace = ((2 * C.k.factorial * r0 : ℝ) : ℂ) := by
    simp only [X, Matrix.mul_sum, Matrix.trace_sum, ap, bp]
    have e1 : ∀ p : Equiv.Perm (Fin C.k) × Bool,
        (Phys.Oobj C.k C.d * Phys.Xf 0 (Phys.vecOf (permRows p.1 (Aε p.2))) (Phys.vecOf (permRows p.1 (Bε p.2)))).trace =
        (Phys.Oobj C.k C.d * Phys.Xf 0 (Phys.vecOf (Aε p.2)) (Phys.vecOf (Bε p.2))).trace := by
      intro p
      rw [← Phys.siteAct_Xf, Phys.trace_Oobj_siteAct]
    simp only [e1]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    rw [Fintype.sum_bool]
    have hT0 : (Phys.Oobj C.k C.d * Phys.Xf 0 (Phys.vecOf A) (Phys.vecOf B)).trace = ((r0 : ℝ) : ℂ) :=
      Phys.obj_phys A B
    have hT1 : (Phys.Oobj C.k C.d * Phys.Xf 0 (Phys.vecOf (A.map star)) (Phys.vecOf (B.map star))).trace =
        ((r0 : ℝ) : ℂ) := by
      rw [← Phys.vecOf_map_star, ← Phys.vecOf_map_star, ← Phys.conjM_Xf, Phys.trace_Oobj_conjM, hT0,
        Complex.star_def, Complex.conj_ofReal]
    simp only [Aε, Bε, if_true, if_false, Bool.false_eq_true, hT0, hT1]
    push_cast
    ring
  -- conclusion
  have hfin : ∑ w, c 0 w * ((C.obj w : ℚ) : ℂ) = (C.types.map fun t => ∑ r ∈ Finset.range t.nrows,
      ∑ s ∈ Finset.range t.nrows, ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum := by
    rw [heq, sub_zero, sub_eq_zero] at hzero
    exact hzero
  rw [hobj, hTX] at hfin
  rw [← hfin] at hblk
  -- positivity of the prefactors
  have hN : (0 : ℝ) < 2 ^ C.k * (2 * (C.d : ℝ) ^ C.k) ^ 4 := by
    have : (0 : ℝ) < C.d := by have := hwf.hd; exact_mod_cast (by omega : 0 < C.d)
    positivity
  have hcast : ((2 * C.k.factorial * r0 : ℝ) : ℂ) / (2 ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4) =
      (((2 * C.k.factorial * r0) / (2 ^ C.k * (2 * (C.d : ℝ) ^ C.k) ^ 4) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast] at hblk
  have hreal : 0 ≤ (2 * C.k.factorial * r0) / (2 ^ C.k * (2 * (C.d : ℝ) ^ C.k) ^ 4) :=
    Complex.zero_le_real.1 hblk
  have h1 : 0 ≤ 2 * C.k.factorial * r0 := by
    have := mul_nonneg hreal hN.le
    rwa [div_mul_cancel₀ _ hN.ne'] at this
  have hfac : (0 : ℝ) < 2 * C.k.factorial := by positivity
  have hr0nn : 0 ≤ r0 := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hnpos : 0 < Phys.nsq C.k C.d (Phys.vecOf A) := by
    rw [nsq_vecOf, gram_trace A cA hA]; linarith
  have h2k : (0 : ℝ) < (Phys.nsq C.k C.d (Phys.vecOf A)) ^ 2 * 2 ^ C.k := by positivity
  rw [hAB]
  by_contra hq
  push Not at hq
  have : r0 < 0 := by rw [hr0]; exact mul_neg_of_pos_of_neg h2k hq
  linarith

end NPT.Cert

#print axioms NPT.Cert.soundness
