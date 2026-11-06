/-
NPT.Cert.PhysSym — the physical invariances behind the symmetrization step (helper task H5): the
family moments `X_f = |w_f⟩⟨w_f|` under site permutations (`siteAct σ X_f(A, B) = X_f(A∘σ, B∘σ)`),
entrywise conjugation and multiplication by constant words `g, h ∈ G_f`; site and conjugation
invariance of `Tr(O ·)`; composition of site actions (a right action:
`siteAct σ ∘ siteAct τ = siteAct (σ * τ)`); and the invariance of the normal-form data (Gram matrix,
`‖a‖²`, `A Bᴴ`) under `permRows σ` and entrywise conjugation.
-/
import NPT.Cert.SymDefs
import NPT.Cert.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert.Phys

variable {k d : ℕ}

namespace SymAux

/-! ### Local word operators -/

/-- Entries of `V_p = VG 0 p`. -/
lemma VG0_apply {n : ℕ} (p : Fin 24) (i j : Dig n 4) :
    VG ℂ n 0 p i j = if i = j ∘ pinvf p then 1 else 0 := by
  have ha : aSel 0 p = pinvf p := by funext s; simp [aSel, inS]
  have hb : bSel 0 p = id := by funext s; simp [bSel, inS]
  unfold VG SelOp
  rw [ha, hb]
  simp only [Matrix.sum_apply, Matrix.single_apply, Function.comp_id]
  rw [Finset.sum_eq_single j]
  · simp [eq_comm]
  · intro x _ hx; simp [hx]
  · simp

lemma star_VG0 {n : ℕ} (p : Fin 24) (i j : Dig n 4) : star (VG ℂ n 0 p i j) = VG ℂ n 0 p i j := by
  rw [VG0_apply]; split_ifs <;> simp

/-- Dimension transport of a word-operator entry. -/
lemma VG_cast {n n' : ℕ} (h : n = n') (S : ℕ) (p : Fin 24) (x y : Dig n 4) :
    VG ℂ n' S p (fun r => Fin.cast h (x r)) (fun r => Fin.cast h (y r)) = VG ℂ n S p x y := by
  subst h; rfl

/-! ### Site permutations of indices -/

lemma sigHat_castSucc (σ : Equiv.Perm (Fin k)) (s : Fin k) : sigHat σ s.castSucc = (σ s).castSucc := by
  simp [sigHat]

lemma sigHat_last (σ : Equiv.Perm (Fin k)) : sigHat σ (Fin.last k) = Fin.last k := by
  simp [sigHat]

lemma sigHat_of_lt (σ : Equiv.Perm (Fin k)) (l : Fin (k + 1)) (h : l.val < k) :
    sigHat σ l = (σ ⟨l.val, h⟩).castSucc := dite_eq_left h

lemma sigHat_of_not_lt (σ : Equiv.Perm (Fin k)) (l : Fin (k + 1)) (h : ¬ l.val < k) :
    sigHat σ l = l := dite_eq_right h

lemma sigHat_mul (σ τ : Equiv.Perm (Fin k)) (l : Fin (k + 1)) :
    sigHat σ (sigHat τ l) = sigHat (σ * τ) l := by
  by_cases h : l.val < k
  · rw [sigHat_of_lt τ l h, sigHat_castSucc, sigHat_of_lt (σ * τ) l h]; rfl
  · rw [sigHat_of_not_lt τ l h, sigHat_of_not_lt σ l h, sigHat_of_not_lt (σ * τ) l h]

lemma sigHat_one (l : Fin (k + 1)) : sigHat (1 : Equiv.Perm (Fin k)) l = l := by
  by_cases h : l.val < k
  · rw [sigHat_of_lt 1 l h]; rfl
  · exact sigHat_of_not_lt 1 l h

lemma val_congr (i : GI (nf k d)) {l l' : Fin (k + 1)} (h : l = l') (r : Fin 4) :
    (i l r).val = (i l' r).val := by
  subst h; rfl

/-- `permIdx` is a right action. -/
lemma permIdx_permIdx (σ τ : Equiv.Perm (Fin k)) (i : GI (nf k d)) :
    permIdx τ (permIdx σ i) = permIdx (σ * τ) i := by
  funext l r
  apply Fin.ext
  simp only [permIdx, Fin.val_cast]
  exact val_congr i (sigHat_mul σ τ l) r

lemma permIdx_one (i : GI (nf k d)) : permIdx (1 : Equiv.Perm (Fin k)) i = i := by
  funext l r
  apply Fin.ext
  simp only [permIdx, Fin.val_cast]
  exact val_congr i (sigHat_one l) r

/-- `permIdx σ` as an equivalence. -/
def permIdxEquiv (σ : Equiv.Perm (Fin k)) : GI (nf k d) ≃ GI (nf k d) where
  toFun := permIdx σ
  invFun := permIdx σ⁻¹
  left_inv i := by rw [permIdx_permIdx, mul_inv_cancel, permIdx_one]
  right_inv i := by rw [permIdx_permIdx, inv_mul_cancel, permIdx_one]

lemma sitePart_repl_permIdx (σ : Equiv.Perm (Fin k)) (i : GI (nf k d)) (r : Fin 4) :
    sitePart (repl (permIdx σ i) r) = sitePart (repl i r) ∘ σ := by
  funext s
  apply Fin.ext
  simp only [sitePart, repl, permIdx, Fin.val_cast, Function.comp_apply]
  exact val_congr i (sigHat_castSucc σ s) r

lemma auxPart_repl_permIdx (σ : Equiv.Perm (Fin k)) (i : GI (nf k d)) (r : Fin 4) :
    auxPart (repl (permIdx σ i) r) = auxPart (repl i r) := by
  apply Fin.ext
  simp only [auxPart, repl, permIdx, Fin.val_cast]
  exact val_congr i (sigHat_last σ) r

lemma vecOf_repl_permIdx (σ : Equiv.Perm (Fin k)) (A : Matrix (Fin k → Fin d) (Fin 2) ℂ)
    (i : GI (nf k d)) (r : Fin 4) :
    vecOf A (repl (permIdx σ i) r) = vecOf (permRows σ A) (repl i r) := by
  simp only [vecOf, permRows, sitePart_repl_permIdx, auxPart_repl_permIdx]

lemma chi_congr (c : Fin 4) {a b a' b' : V1 k d → ℂ} {u u' : V1 k d} (ha : a u = a' u')
    (hb : b u = b' u') : chi c a b u = chi c a' b' u' := by
  fin_cases c <;> simp [chi, ha, hb]

/-! ### Site/auxiliary decomposition of one replica -/

variable (k d) in
/-- Site/auxiliary decomposition `V1 ≃ (Fin k → Fin d) × Fin 2`. -/
def siteAux : V1 k d ≃ (Fin k → Fin d) × Fin 2 :=
  (Fin.snocEquiv fun l => Fin (nf k d l)).symm.trans
    (((finCongr (nf_aux k d)).prodCongr (Equiv.piCongrRight fun s => finCongr (nf_site k d s))).trans
      (Equiv.prodComm _ _))

lemma sitePart_siteAux_symm (x : Fin k → Fin d) (α : Fin 2) :
    sitePart ((siteAux k d).symm (x, α)) = x :=
  congrArg Prod.fst ((siteAux k d).apply_symm_apply (x, α))

lemma auxPart_siteAux_symm (x : Fin k → Fin d) (α : Fin 2) :
    auxPart ((siteAux k d).symm (x, α)) = α :=
  congrArg Prod.snd ((siteAux k d).apply_symm_apply (x, α))

lemma sum_V1 {R : Type*} [AddCommMonoid R] (f : V1 k d → R) :
    ∑ v, f v = ∑ x, ∑ α, f ((siteAux k d).symm (x, α)) := by
  rw [← (siteAux k d).symm.sum_comp, Fintype.sum_prod_type]

/-! ### Constant words -/

lemma VWc_apply (g : Fin 24) (i j : GI (nf k d)) :
    VWc g i j = if j = (fun l => i l ∘ pf g) then 1 else 0 := by
  simp only [VWc, VW, kron, VG0_apply]
  rw [Fintype.prod_boole]
  have hiff : (∀ l, i l = j l ∘ pinvf g) ↔ j = fun l => i l ∘ pf g := by
    constructor
    · intro h; funext l r; simp [h l, pinvf_pf]
    · intro h l; funext r; simp [h, pf_pinvf]
  simp only [hiff]

lemma VWc_mul_apply (g : Fin 24) (M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) (i j : GI (nf k d)) :
    (VWc g * M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) i j = M (fun l => i l ∘ pf g) j := by
  rw [mul_apply, Fintype.sum_eq_single (fun l => i l ∘ pf g)]
  · rw [VWc_apply, ite_eq_left rfl, one_mul]
  · intro x hx; rw [VWc_apply, ite_eq_right hx, zero_mul]

lemma mul_VWc_apply (h : Fin 24) (M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) (i j : GI (nf k d)) :
    (M * VWc h : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) i j = M i (fun l => j l ∘ pinvf h) := by
  have key : ∀ x : GI (nf k d), (j = fun l => x l ∘ pf h) ↔ x = fun l => j l ∘ pinvf h := by
    intro x
    constructor
    · intro hx; funext l r; simp [hx, pf_pinvf]
    · intro hx; funext l r; simp [hx, pinvf_pf]
  rw [mul_apply, Fintype.sum_eq_single (fun l => j l ∘ pinvf h)]
  · rw [VWc_apply, ite_eq_left ((key _).mpr rfl), mul_one]
  · intro x hx; rw [VWc_apply, ite_eq_right (fun h' => hx ((key x).mp h')), mul_zero]

/-- A replica relabelling preserving the letters of the pattern fixes the pattern vector. -/
lemma patVec_relabel (pat : Fin 4 → Fin 4) (a b : V1 k d → ℂ) (π π' : Fin 4 → Fin 4)
    (h1 : ∀ r, π' (π r) = r) (h2 : ∀ r, π (π' r) = r) (hπ : ∀ r, pat (π r) = pat r)
    (i : GI (nf k d)) : patVec pat a b (fun l => i l ∘ π) = patVec pat a b i := by
  let e : Equiv.Perm (Fin 4) := ⟨π, π', h1, h2⟩
  unfold patVec
  rw [← Equiv.prod_comp e (fun r => chi (pat r) a b (repl i r))]
  refine Finset.prod_congr rfl fun r _ => ?_
  show chi (pat r) a b (repl (fun l => i l ∘ π) r) = chi (pat (π r)) a b (repl i (π r))
  rw [hπ]; rfl

lemma famPat_inG : ∀ g : Fin 24, ∀ r : Fin 4,
    (inG 0 g = true → famPat 0 (pf g r) = famPat 0 r) ∧
    (inG 1 g = true → famPat 1 (pf g r) = famPat 1 r) ∧
    (inG 2 g = true → famPat 2 (pf g r) = famPat 2 r) := by decide +kernel

lemma famPat_pf {f : ℕ} (hf : f < 3) {g : Fin 24} (hg : inG f g = true) (r : Fin 4) :
    famPat f (pf g r) = famPat f r := by
  interval_cases f
  · exact (famPat_inG g r).1 hg
  · exact (famPat_inG g r).2.1 hg
  · exact (famPat_inG g r).2.2 hg

lemma famPat_pinvf {f : ℕ} (hf : f < 3) {h : Fin 24} (hh : inG f h = true) (r : Fin 4) :
    famPat f (pinvf h r) = famPat f r := by
  have := famPat_pf hf hh (pinvf h r)
  rw [pf_pinvf] at this
  exact this.symm

/-! ### The objective operator -/

lemma Oloc_cast (l l' : Fin (k + 1)) (h : nf k d l' = nf k d l) (hl : l'.val < k ↔ l.val < k)
    (x y : Dig (nf k d l') 4) :
    (if l.val < k then (2 : ℂ) • VG ℂ (nf k d l) 0 0 - VG ℂ (nf k d l) 0 21 else VG ℂ (nf k d l) 0 21)
        (fun r => Fin.cast h (x r)) (fun r => Fin.cast h (y r)) =
      (if l'.val < k then (2 : ℂ) • VG ℂ (nf k d l') 0 0 - VG ℂ (nf k d l') 0 21
        else VG ℂ (nf k d l') 0 21) x y := by
  by_cases hl' : l'.val < k
  · rw [ite_eq_left (hl.mp hl'), ite_eq_left hl']
    simp only [Matrix.sub_apply, Matrix.smul_apply, VG_cast]
  · rw [ite_eq_right (fun h' => hl' (hl.mpr h')), ite_eq_right hl']
    exact VG_cast h 0 21 x y

lemma star_Oobj (i j : GI (nf k d)) : star (Oobj k d i j) = Oobj k d i j := by
  simp only [Oobj, kron, star_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs
  · simp [star_VG0]
  · exact star_VG0 _ _ _

lemma trace_siteAct_mul (σ : Equiv.Perm (Fin k)) (N M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) :
    (siteAct σ N * siteAct σ M).trace = (N * M).trace := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, siteAct]
  refine Fintype.sum_equiv (permIdxEquiv σ) _ _ fun i => ?_
  exact Fintype.sum_equiv (permIdxEquiv σ) _ _ fun j => rfl

end SymAux

open SymAux

variable (σ τ : Equiv.Perm (Fin k)) (f : ℕ) (A B : Matrix (Fin k → Fin d) (Fin 2) ℂ)
  (M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ)

theorem siteAct_Xf :
    siteAct σ (Xf f (vecOf A) (vecOf B)) = Xf f (vecOf (permRows σ A)) (vecOf (permRows σ B)) := by
  have hw : ∀ i, patVec (famPat f) (vecOf A) (vecOf B) (permIdx σ i) =
      patVec (famPat f) (vecOf (permRows σ A)) (vecOf (permRows σ B)) i := by
    intro i
    unfold patVec
    refine Finset.prod_congr rfl fun r _ => ?_
    exact chi_congr _ (vecOf_repl_permIdx σ A i r) (vecOf_repl_permIdx σ B i r)
  ext i j
  simp only [siteAct, Xf, vecMulVec_apply, Pi.star_apply, hw]

theorem conjM_Xf (a b : V1 k d → ℂ) :
    conjM (Xf f a b) = Xf f (fun v => star (a v)) (fun v => star (b v)) := by
  have hchi : ∀ c u, chi c (fun v => star (a v)) (fun v => star (b v)) u = star (chi c a b u) := by
    intro c u; fin_cases c <;> simp [chi]
  have hw : ∀ i, patVec (famPat f) (fun v => star (a v)) (fun v => star (b v)) i =
      star (patVec (famPat f) a b i) := by
    intro i; simp only [patVec, hchi, star_prod]
  ext i j
  simp only [conjM, Xf, Matrix.map_apply, vecMulVec_apply, Pi.star_apply, hw, star_mul', star_star]

theorem vecOf_map_star : (fun v => star (vecOf A v)) = vecOf (A.map star) := rfl

theorem VWc_Xf (hf : f < 3) (g h : Fin 24) (hg : inG f g = true) (hh : inG f h = true)
    (a b : V1 k d → ℂ) : VWc g * Xf f a b * VWc h = Xf f a b := by
  ext i j
  rw [mul_VWc_apply, VWc_mul_apply]
  simp only [Xf, vecMulVec_apply, Pi.star_apply]
  rw [patVec_relabel (famPat f) a b (pf g) (pinvf g) (pinvf_pf g) (pf_pinvf g) (famPat_pf hf hg) i,
    patVec_relabel (famPat f) a b (pinvf h) (pf h) (pf_pinvf h) (pinvf_pf h) (famPat_pinvf hf hh) j]

theorem siteAct_Oobj : siteAct σ (Oobj k d) = Oobj k d := by
  ext i j
  simp only [siteAct, Oobj, kron]
  exact Fintype.prod_equiv (sigHat σ) _ _ fun l =>
    Oloc_cast l (sigHat σ l) (nf_sigHat σ l) (sigHat_lt σ l) (i (sigHat σ l)) (j (sigHat σ l))

theorem trace_Oobj_siteAct : (Oobj k d * siteAct σ M).trace = (Oobj k d * M).trace := by
  rw [← trace_siteAct_mul σ (Oobj k d) M, siteAct_Oobj]

theorem trace_Oobj_conjM : (Oobj k d * conjM M).trace = star ((Oobj k d * M).trace) := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjM, Matrix.map_apply, star_sum, star_mul',
    star_Oobj]

/-- Site actions compose as a right action: `siteAct σ ∘ siteAct τ = siteAct (σ * τ)`. -/
theorem siteAct_siteAct : siteAct σ (siteAct τ M) = siteAct (σ * τ) M := by
  ext i j
  simp only [siteAct, permIdx_permIdx]

theorem conjM_siteAct : conjM (siteAct σ M) = siteAct σ (conjM M) := rfl

theorem permRows_gram : (permRows σ A)ᴴ * permRows σ A = Aᴴ * A := by
  ext α β
  simp only [mul_apply, conjTranspose_apply, permRows]
  exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl (Fin d))) _ _ fun x => rfl

theorem map_star_gram : (A.map star)ᴴ * A.map star = (Aᴴ * A).map star := by
  ext α β
  simp only [mul_apply, conjTranspose_apply, Matrix.map_apply, star_star, star_sum, star_mul']

theorem nsq_permRows : nsq k d (vecOf (permRows σ A)) = nsq k d (vecOf A) := by
  simp only [nsq, sum_V1, vecOf, sitePart_siteAux_symm, auxPart_siteAux_symm, permRows]
  exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl (Fin d))) _ _ fun x => rfl

theorem nsq_map_star : nsq k d (vecOf (A.map star)) = nsq k d (vecOf A) := by
  simp only [nsq, vecOf, Matrix.map_apply]
  exact Finset.sum_congr rfl fun v _ => Complex.normSq_conj _

theorem permRows_mul : permRows σ A * (permRows σ B)ᴴ = fun x y => (A * Bᴴ) (x ∘ σ) (y ∘ σ) := by
  ext x y
  simp only [mul_apply, conjTranspose_apply, permRows]

end NPT.Cert.Phys
