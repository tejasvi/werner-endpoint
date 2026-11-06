/-
NPT.CP3.Phys — the physical side of the common-plane relaxation.

For a Stiefel `A` (two orthonormal columns in `(ℂ³)^{⊗4}`) let `a = vec A` and `X₄₀ = |aaaa⟩⟨aaaa|` (`NPT.K4.Xf5 3`).
`Xs` is the sum of `X₄₀` over the 48 transforms of `A` (site permutations, optionally complex conjugated), and `Yp` is
its Hilbert–Schmidt projection onto `A'_0` (`NPT.CP3.Alg`). Then:
* `Yp ⪰ 0` and `Yp^{Γ₃} ⪰ 0` (Lemma P; `X₄₀^{Γ₃} = |aaaā⟩⟨aaaā|`);
* `Yp` is site-symmetric, symmetric (`Ypᵀ = Yp`) and bosonic (`V_g Yp = Yp = Yp V_g`);
* the Stiefel contrast at replica 0 annihilates `Yp`;
* `Tr(O_w Yp) = 48 · ‖a‖⁴ · 2⁴ · q(1/2, A diag(w) Aᴴ)` for the objective operator `O_w = D_w O D_w`, where `O` is the
  EP3 objective operator and `D_w` multiplies by `w` of the auxiliary digit of replica 3.
-/
import NPT.CP3.Alg
import NPT.K4.Phys5
import NPT.Cert.Soundness

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Phys NPT.Cert.SymAvg
open scoped ComplexOrder

namespace NPT.CP3

/-- Two-column matrices on four qutrit sites. -/
abbrev MatA := Matrix (Fin 4 → Fin 3) (Fin 2) ℂ

/-! ### Maps preserving `A'_0` -/

lemma map_spanA (T : Matrix GC GC ℂ →ₗ[ℂ] Matrix GC GC ℂ) (hT : ∀ x ∈ genA 0, T x ∈ spanA 0) :
    ∀ Y ∈ spanA 0, T Y ∈ spanA 0 := by
  intro Y hY
  have hle : spanA 0 ≤ (spanA 0).comap T := Submodule.span_le.2 fun x hx => hT x hx
  exact hle hY

lemma proj_invA (T : Matrix GC GC ℂ →ₗ[ℂ] Matrix GC GC ℂ) (hT : ∀ x ∈ genA 0, T x ∈ spanA 0)
    (hadj : ∀ N ∈ spanA 0, ∃ M ∈ spanA 0, ∀ Z, (Nᴴ * T Z).trace = (Mᴴ * Z).trace)
    {X Y : Matrix GC GC ℂ} (hY : IsProj (spanA 0) X Y) (hX : T X = X) : T Y = Y := by
  have h := hY.map T (map_spanA T hT) hadj
  rw [hX] at h
  exact h.unique hY

/-- Kronecker products whose site factors lie in `span {VG 0 p}` (auxiliary factor arbitrary) lie in `A'_0`. -/
lemma kron_mem_spanA_of {F : LocM}
    (hF : ∀ l : Fin 5, l.val < 4 → F l ∈ Submodule.span ℂ (Set.range (VG ℂ (nfC l) 0))) : kron F ∈ spanA 0 := by
  classical
  let V : (l : Fin 5) → Fin 24 → Matrix (Dig (nfC l) 4) (Dig (nfC l) 4) ℂ :=
    fun l p => if l.val < 4 then VG ℂ (nfC l) 0 p else if p = 0 then F l else 0
  have hA : ∀ l, F l ∈ Submodule.span ℂ (Set.range (V l)) := by
    intro l
    by_cases hl : l.val < 4
    · have e : V l = VG ℂ (nfC l) 0 := funext fun p => if_pos hl
      rw [e]; exact hF l hl
    · exact Submodule.subset_span ⟨0, by simp [V, hl]⟩
  refine Submodule.span_le.2 ?_ (kron_mem_span V hA)
  rintro _ ⟨u, rfl⟩
  exact Submodule.subset_span ⟨u, fun l => V l (u l), fun l hl => by simp [V, hl], rfl⟩

/-- Site permutation of the local factors. -/
def siteF (σ : Equiv.Perm (Fin 4)) (F : LocM) : LocM :=
  fun m x y => F (sigHat σ.symm m) (Fin.cast (nf_sigHat σ.symm m).symm ∘ x) (Fin.cast (nf_sigHat σ.symm m).symm ∘ y)

lemma locM_transport (F : LocM) {l l' : Fin 5} (h : l' = l) {n : ℕ} (a b : Dig n 4) (h1 : n = nfC l)
    (h2 : n = nfC l') : F l (Fin.cast h1 ∘ a) (Fin.cast h1 ∘ b) = F l' (Fin.cast h2 ∘ a) (Fin.cast h2 ∘ b) := by
  subst h; rfl

lemma siteAct_kron (σ : Equiv.Perm (Fin 4)) (F : LocM) : siteAct σ (kron F) = kron (siteF σ F) := by
  ext i j
  simp only [siteAct, kron, siteF]
  refine Fintype.prod_equiv (sigHat σ) _ _ fun l => ?_
  exact locM_transport F (sigHat_symm_sigHat σ l) (i (sigHat σ l)) (j (sigHat σ l)) (nf_sigHat σ l)
    (nf_sigHat σ.symm (sigHat σ l)).symm

lemma siteAct_genA (σ : Equiv.Perm (Fin 4)) {x : Matrix GC GC ℂ} (hx : x ∈ genA 0) : siteAct σ x ∈ genA 0 := by
  obtain ⟨w, F, hF, rfl⟩ := hx
  refine ⟨fun m => w (sigHat σ.symm m), siteF σ F, fun m hm => ?_, siteAct_kron σ F⟩
  have hm' : (sigHat σ.symm m).val < 4 := (sigHat_lt σ.symm m).2 hm
  ext x y
  simp only [siteF, hF _ hm']
  exact SymAvg.VG_cast (nf_sigHat σ.symm m).symm (w (sigHat σ.symm m)) x y

lemma siteAct_adjA (σ : Equiv.Perm (Fin 4)) : ∀ N ∈ spanA 0, ∃ M ∈ spanA 0,
    ∀ Z, (Nᴴ * Tsite 4 3 σ Z).trace = (Mᴴ * Z).trace := by
  intro N hN
  refine ⟨siteAct σ.symm N, map_spanA (Tsite 4 3 σ.symm)
    (fun x hx => Submodule.subset_span (siteAct_genA σ.symm hx)) N hN, fun Z => ?_⟩
  let E : GC ≃ GC := ⟨permIdx σ, permIdx σ.symm, permIdx_symm σ, permIdx_symm' σ⟩
  simp only [Tsite, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, siteAct]
  symm
  rw [← E.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← E.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [E, Equiv.coe_fn_mk, permIdx_symm]

lemma transpose_genA {x : Matrix GC GC ℂ} (hx : x ∈ genA 0) : xᵀ ∈ genA 0 := by
  obtain ⟨w, F, hF, rfl⟩ := hx
  refine ⟨fun l => pinvIdx (w l), fun l => (F l)ᵀ, fun l h => ?_, kron_transpose F⟩
  simp only [hF l h]
  exact SymAvg.VG_transpose (w l)

lemma transpose_adjA : ∀ N ∈ spanA 0, ∃ M ∈ spanA 0, ∀ Z, (Nᴴ * Ttr 4 3 Z).trace = (Mᴴ * Z).trace := by
  intro N hN
  refine ⟨Nᵀ, map_spanA (Ttr 4 3) (fun x hx => Submodule.subset_span (transpose_genA hx)) N hN, fun Z => ?_⟩
  simp only [Ttr, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- The Stiefel kernel at replica 0 (`stK` on the auxiliary factor, `etK` on the sites). -/
abbrev stK0 := stKer (nf := nfC) (fun l : Fin 5 => ¬ l.val < 4) 0

lemma stK0_genA {x : Matrix GC GC ℂ} (hx : x ∈ genA 0) : applyG stK0 x ∈ spanA 0 := by
  obtain ⟨w, F, hF, rfl⟩ := hx
  rw [applyG_kron]
  refine kron_mem_spanA_of fun l hl => ?_
  rw [hF l hl]
  exact stKer_local (slotTab_ok ⟨0, by decide⟩) (fun p => trTab_ok ⟨0, by decide⟩ p)
    (fun q t => embTab_ok ⟨0, by decide⟩ q t) _ l (w l)

set_option maxRecDepth 20000 in
/-- The Stiefel kernel as a linear map on `GC`-matrices. -/
noncomputable def stK0L : Matrix GC GC ℂ →ₗ[ℂ] Matrix GC GC ℂ where
  toFun := applyG stK0
  map_add' x y := by
    ext i j
    simp only [applyG, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i j
    simp only [applyG, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

set_option maxRecDepth 20000 in
lemma stK0_mem {Y : Matrix GC GC ℂ} (hY : Y ∈ spanA 0) : stK0L Y ∈ spanA 0 :=
  map_spanA stK0L (fun _ hx => stK0_genA hx) Y hY

set_option maxRecDepth 20000 in
/-- **Stiefel equalities at the projection.** -/
theorem stiefelA_proj {X Y : Matrix GC GC ℂ} (h : IsProj (spanA 0) X Y) (hX : stK0L X = 0) : stK0L Y = 0 :=
  h.map_eq_zero stK0L (fun _ hY => stK0_mem hY)
    (fun N hN => ⟨stK0L N, stK0_mem hN, fun Z => by
      have e := trace_applyG stK0 N Z
      rw [stKer_adj] at e
      exact e⟩) hX

/-! ### The physical moments -/

/-- `X₄₀ = |aaaa⟩⟨aaaa|` for `a = vec A`. -/
noncomputable def X40 (A : MatA) : Matrix GC GC ℂ := K4.Xf5 3 (vecOf A) (vecOf A)

/-- The 48 transforms of `A`: a site permutation, after an optional complex conjugation. -/
def trA (σ : Equiv.Perm (Fin 4)) (e : Bool) (A : MatA) : MatA := permRows σ (if e then A.map star else A)

/-- The symmetrized moment. -/
noncomputable def Xs (A : MatA) : Matrix GC GC ℂ := ∑ σ : Equiv.Perm (Fin 4), ∑ e : Bool, X40 (trA σ e A)

lemma psd_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (M : ι → Matrix GC GC ℂ)
    (h : ∀ i ∈ s, (M i).PosSemidef) : (∑ i ∈ s, M i).PosSemidef := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Matrix.PosSemidef.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma X40_psd (A : MatA) : (X40 A).PosSemidef := by
  unfold X40 K4.Xf5
  exact posSemidef_vecMulVec_self_star _

lemma Xs_psd (A : MatA) : (Xs A).PosSemidef :=
  psd_sum _ _ fun σ _ => psd_sum _ _ fun e _ => X40_psd _

lemma cons_gam3 : K4.Consistent5 3 ![0, 0, 0, 1] ![0, 0, 0, 1] (rkp 1) (rlp 1) := by decide

/-- `X₄₀^{Γ₃} = |aaaā⟩⟨aaaā|`. -/
lemma gam3_X40 (A : MatA) : gam3 (X40 A) =
    vecMulVec (patVec ![0, 0, 0, 1] (vecOf A) (vecOf A)) (star (patVec ![0, 0, 0, 1] (vecOf A) (vecOf A))) :=
  K4.phys_rule5 rule1_ok.pos cons_gam3 (vecOf A) (vecOf A)

lemma gam3_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix GC GC ℂ) : gam3 (∑ i ∈ s, M i) = ∑ i ∈ s, gam3 (M i) :=
  map_sum (ruleGL (nf := nfC) (rkp 1) (rlp 1)) M s

lemma gam3_Xs_psd (A : MatA) : (gam3 (Xs A)).PosSemidef := by
  unfold Xs
  rw [gam3_sum]
  refine psd_sum _ _ fun σ _ => ?_
  rw [gam3_sum]
  refine psd_sum _ _ fun e _ => ?_
  rw [gam3_X40]
  exact posSemidef_vecMulVec_self_star _

lemma Xs_site (τ : Equiv.Perm (Fin 4)) (A : MatA) : siteAct τ (Xs A) = Xs A := by
  unfold Xs X40
  simp only [siteAct_sum, K4.siteAct_Xf5, trA, permRows_comp]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl

lemma X40_transpose (A : MatA) : (X40 A)ᵀ = X40 (A.map star) := by
  unfold X40
  rw [K4.Xf5_transpose, K4.conjM_Xf5, vecOf_map_star]

lemma Xs_transpose (A : MatA) : (Xs A)ᵀ = Xs A := by
  unfold Xs
  simp only [transpose_sum, X40_transpose, trA, permRows_map_star]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [ite_true, Bool.false_eq_true, ite_false, map_star_map_star]
  exact add_comm _ _

lemma VWc_mem (g : Fin 24) : (VWc (k := 4) (d := 3) g) ∈ spanA 0 :=
  kron_mem_spanA (fun _ => g) fun _ _ => rfl

lemma inG5_3 : ∀ g : Fin 24, K4.inG5 3 g = true := by decide

lemma VWc_X40 (g : Fin 24) (A : MatA) : VWc (k := 4) (d := 3) g * X40 A = X40 A := by
  have h := K4.VWc_Xf5 (by norm_num : 3 < 5) g 0 (inG5_3 g) (inG5_3 0) (vecOf A) (vecOf A)
  rwa [show VWc (k := 4) (d := 3) 0 = 1 from VW_zero (by norm_num), Matrix.mul_one] at h

lemma X40_VWc (g : Fin 24) (A : MatA) : X40 A * VWc (k := 4) (d := 3) g = X40 A := by
  have h := K4.VWc_Xf5 (by norm_num : 3 < 5) 0 g (inG5_3 0) (inG5_3 g) (vecOf A) (vecOf A)
  rwa [show VWc (k := 4) (d := 3) 0 = 1 from VW_zero (by norm_num), Matrix.one_mul] at h

lemma VWc_Xs (g : Fin 24) (A : MatA) : VWc (k := 4) (d := 3) g * Xs A = Xs A := by
  unfold Xs
  rw [Matrix.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by rw [Matrix.mul_sum]; exact Finset.sum_congr rfl fun e _ => VWc_X40 g _

lemma Xs_VWc (g : Fin 24) (A : MatA) : Xs A * VWc (k := 4) (d := 3) g = Xs A := by
  unfold Xs
  rw [Matrix.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by rw [Matrix.sum_mul]; exact Finset.sum_congr rfl fun e _ => X40_VWc g _

/-! ### The projected moment -/

/-- The Hilbert–Schmidt projection of `Xs A` onto `A'_0`. -/
noncomputable def Yp (A : MatA) : Matrix GC GC ℂ := Classical.choose (exists_isProj (spanA 0) (Xs A))

lemma Yp_isProj (A : MatA) : IsProj (spanA 0) (Xs A) (Yp A) := Classical.choose_spec (exists_isProj (spanA 0) (Xs A))

lemma Yp_mem (A : MatA) : Yp A ∈ spanA 0 := (Yp_isProj A).1

lemma Yp_psd (A : MatA) : (Yp A).PosSemidef := psd_of_isProj cut0 (Xs_psd A) (Yp_isProj A)

lemma gam3_Yp_psd (A : MatA) : (gam3 (Yp A)).PosSemidef := psd_gam3_of_isProj (Yp_isProj A) (gam3_Xs_psd A)

lemma Yp_site (τ : Equiv.Perm (Fin 4)) (A : MatA) : siteAct τ (Yp A) = Yp A :=
  proj_invA (Tsite 4 3 τ) (fun _ hx => Submodule.subset_span (siteAct_genA τ hx)) (siteAct_adjA τ) (Yp_isProj A)
    (Xs_site τ A)

lemma Yp_transpose (A : MatA) : (Yp A)ᵀ = Yp A :=
  proj_invA (Ttr 4 3) (fun _ hx => Submodule.subset_span (transpose_genA hx)) transpose_adjA (Yp_isProj A)
    (Xs_transpose A)

lemma VWc_Yp (g : Fin 24) (A : MatA) : VWc (k := 4) (d := 3) g * Yp A = Yp A := by
  have h := isProj_mul_left cut0 (Yp_isProj A) (VWc_mem g)
  rw [VWc_Xs] at h
  exact h.unique (Yp_isProj A)

lemma Yp_VWc (g : Fin 24) (A : MatA) : Yp A * VWc (k := 4) (d := 3) g = Yp A := by
  have h := isProj_mul_right cut0 (Yp_isProj A) (VWc_mem g)
  rw [Xs_VWc] at h
  exact h.unique (Yp_isProj A)

/-- `Yp` is real: Hermitian (it is PSD) and symmetric. -/
lemma Yp_real (A : MatA) (i j : GC) : star (Yp A i j) = Yp A i j := by
  have h1 : star (Yp A j i) = Yp A i j := (Yp_psd A).1.apply i j
  have h2 : Yp A j i = Yp A i j := by
    have := congrFun (congrFun (Yp_transpose A) i) j
    simpa [Matrix.transpose_apply] using this
  rw [h2] at h1; exact h1

/-! ### Stiefel -/

lemma trA_gram (σ : Equiv.Perm (Fin 4)) (e : Bool) {A : MatA} (hA : Aᴴ * A = 1) :
    (trA σ e A)ᴴ * trA σ e A = ((1 : ℝ) : ℂ) • 1 := by
  unfold trA
  rw [permRows_gram]
  cases e
  · simp [hA]
  · simp only [ite_true]
    rw [map_star_gram, hA]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

set_option maxRecDepth 20000 in
lemma stK0_X40 {A : MatA} (hA : Aᴴ * A = ((1 : ℝ) : ℂ) • 1) : applyG stK0 (X40 A) = 0 := by
  rw [show stK0 = Phys.stF (csl 0) (cord 0) from stKer_eq_stF 0, csl_cord_0.1, csl_cord_0.2]
  exact Stiefel.applyG_stF_patVec Stiefel.so0 (K4.famPat5 3) rfl A 1 hA (vecOf A)

set_option maxRecDepth 20000 in
lemma stK0_Yp {A : MatA} (hA : Aᴴ * A = 1) : stK0L (Yp A) = 0 := by
  refine stiefelA_proj (Yp_isProj A) ?_
  unfold Xs
  rw [map_sum stK0L]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [map_sum stK0L]
  exact Finset.sum_eq_zero fun e _ => stK0_X40 (trA_gram σ e hA)

/-! ### The objective -/

/-- `D_w`: multiplication by the weight `w` of the auxiliary digit of replica 3. -/
noncomputable def Dw (w : Fin 2 → ℝ) : Matrix GC GC ℂ := diagonal fun i => ((w (auxPart (repl i 3)) : ℝ) : ℂ)

lemma nfC_aux {l : Fin 5} (h : ¬ l.val < 4) : nfC l = 2 := by
  show (if l.val < 4 then 3 else 2) = 2
  rw [if_neg h]

/-- Local factors of `D_w`. -/
noncomputable def DwF (w : Fin 2 → ℝ) : LocM := fun l =>
  if h : l.val < 4 then 1 else diagonal fun x => ((w (Fin.cast (nfC_aux h) (x 3)) : ℝ) : ℂ)

lemma Dw_eq_kron (w : Fin 2 → ℝ) : Dw w = kron (DwF w) := by
  ext i j
  simp only [Dw, kron, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Fin.prod_univ_five]
    simp only [DwF, Fin.isValue]
    simp [auxPart, repl]
  · rw [if_neg hij]
    obtain ⟨l, hl⟩ : ∃ l, i l ≠ j l := by
      by_contra h
      push_neg at h
      exact hij (funext h)
    refine (Finset.prod_eq_zero (Finset.mem_univ l) ?_).symm
    unfold DwF
    split_ifs
    · exact Matrix.one_apply_ne hl
    · exact diagonal_apply_ne _ hl

lemma Dw_mem (w : Fin 2 → ℝ) : Dw w ∈ spanA 0 := by
  rw [Dw_eq_kron]
  refine kron_mem_spanA (fun _ => 0) fun l hl => ?_
  simp only [DwF, dif_pos hl]
  exact (VG_zero (by norm_num)).symm

lemma Dw_conjTranspose (w : Fin 2 → ℝ) : (Dw w)ᴴ = Dw w := by
  unfold Dw
  rw [diagonal_conjTranspose]
  congr 1
  funext i
  simp [Complex.star_def, Complex.conj_ofReal]

/-- The objective operator `O_w = D_w O D_w`. -/
noncomputable def Ow (w : Fin 2 → ℝ) : Matrix GC GC ℂ := Dw w * Oobj 4 3 * Dw w

lemma Oobj_memA : Oobj 4 3 ∈ spanA 0 :=
  kron_mem_spanA_of fun l _ => Oobj_local_mem (k := 4) (d := 3) l

lemma Ow_mem (w : Fin 2 → ℝ) : Ow w ∈ spanA 0 :=
  spanA_mul_mem cut0 (spanA_mul_mem cut0 (Dw_mem w) Oobj_memA) (Dw_mem w)

lemma Ow_conjTranspose (w : Fin 2 → ℝ) : (Ow w)ᴴ = Ow w := by
  unfold Ow
  rw [conjTranspose_mul, conjTranspose_mul, Dw_conjTranspose, Oobj_conjTranspose, Matrix.mul_assoc]

/-- `D_w X₄₀ D_w` is the EP3 family-`31` moment with `b = vec (A diag w)`. -/
lemma Dw_X40_Dw (w : Fin 2 → ℝ) (A : MatA) :
    Dw w * X40 A * Dw w = Xf 0 (vecOf A) (vecOf (A * diagonal fun α => ((w α : ℝ) : ℂ))) := by
  have ha : ∀ (r : Fin 4) (v : V1 4 3), chi (K4.famPat5 3 r) (vecOf A) (vecOf A) v = vecOf A v := by
    intro r v; fin_cases r <;> rfl
  have hb : ∀ (r : Fin 4) (a b : V1 4 3 → ℂ) (v : V1 4 3), chi (famPat 0 r) a b v = if r = 3 then b v else a v := by
    intro r a b v; fin_cases r <;> rfl
  ext i j
  simp only [Dw, diagonal_mul, mul_diagonal, X40, K4.Xf5, Xf, vecMulVec_apply, Pi.star_apply, patVec, ha, hb,
    Fin.prod_univ_four]
  simp [vecOf, mul_diagonal, star_mul', Complex.conj_ofReal]
  ring

lemma permRows_mul_diag (σ : Equiv.Perm (Fin 4)) (M : MatA) (w : Fin 2 → ℝ) :
    permRows σ M * diagonal (fun α => ((w α : ℝ) : ℂ)) = permRows σ (M * diagonal fun α => ((w α : ℝ) : ℂ)) := by
  ext x α
  simp [permRows, mul_diagonal]

lemma map_star_mul_diag (M : MatA) (w : Fin 2 → ℝ) :
    M.map star * diagonal (fun α => ((w α : ℝ) : ℂ)) = (M * diagonal fun α => ((w α : ℝ) : ℂ)).map star := by
  ext x α
  simp [mul_diagonal, Complex.star_def, Complex.conj_ofReal]

lemma trA_mul_diag (σ : Equiv.Perm (Fin 4)) (e : Bool) (A : MatA) (w : Fin 2 → ℝ) :
    trA σ e A * diagonal (fun α => ((w α : ℝ) : ℂ)) = trA σ e (A * diagonal fun α => ((w α : ℝ) : ℂ)) := by
  unfold trA
  rw [permRows_mul_diag]
  cases e
  · rfl
  · simp only [ite_true]; rw [map_star_mul_diag]

/-- **Objective identity** at the symmetrized moment. -/
lemma trace_Ow_Xs (w : Fin 2 → ℝ) (A : MatA) :
    (Ow w * Xs A).trace = ((48 * ((nsq 4 3 (vecOf A)) ^ 2 * 2 ^ 4 *
      NPT.q (1 / 2) (A * (A * diagonal fun α => ((w α : ℝ) : ℂ))ᴴ)) : ℝ) : ℂ) := by
  set B : MatA := A * diagonal fun α => ((w α : ℝ) : ℂ) with hB
  set r0 : ℝ := (nsq 4 3 (vecOf A)) ^ 2 * 2 ^ 4 * NPT.q (1 / 2) (A * Bᴴ) with hr0
  have hT0 : (Oobj 4 3 * Xf 0 (vecOf A) (vecOf B)).trace = ((r0 : ℝ) : ℂ) := obj_phys A B
  have hT1 : (Oobj 4 3 * Xf 0 (vecOf (A.map star)) (vecOf (B.map star))).trace = ((r0 : ℝ) : ℂ) := by
    rw [← vecOf_map_star, ← vecOf_map_star, ← conjM_Xf, trace_Oobj_conjM, hT0, Complex.star_def, Complex.conj_ofReal]
  have e1 : ∀ (σ : Equiv.Perm (Fin 4)) (e : Bool), (Ow w * X40 (trA σ e A)).trace =
      (Oobj 4 3 * Xf 0 (vecOf (if e then A.map star else A)) (vecOf (if e then B.map star else B))).trace := by
    intro σ e
    have h1 : (Ow w * X40 (trA σ e A)).trace = (Oobj 4 3 * (Dw w * X40 (trA σ e A) * Dw w)).trace := by
      simp only [Ow, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [h1, Dw_X40_Dw, trA_mul_diag]
    unfold trA
    rw [← siteAct_Xf, trace_Oobj_siteAct]
  unfold Xs
  simp only [Matrix.mul_sum, Matrix.trace_sum, e1]
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, hT0, hT1, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  norm_num
  ring

lemma trace_Ow_Yp (w : Fin 2 → ℝ) (A : MatA) : (Ow w * Yp A).trace = (Ow w * Xs A).trace := by
  have h := (Yp_isProj A).2 (Ow w) (Ow_mem w)
  rwa [Ow_conjTranspose] at h

lemma nsq_stiefel {A : MatA} (hA : Aᴴ * A = 1) : nsq 4 3 (vecOf A) = 2 := by
  rw [nsq_vecOf, gram_trace A 1 (by simp [hA]), mul_one]

lemma diag_real_conjTranspose (w : Fin 2 → ℝ) :
    (diagonal fun α => ((w α : ℝ) : ℂ))ᴴ = diagonal fun α => ((w α : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose]
  congr 1
  funext α
  simp [Complex.star_def, Complex.conj_ofReal]

lemma mul_diag_conjTranspose (A : MatA) (w : Fin 2 → ℝ) :
    A * (A * diagonal fun α => ((w α : ℝ) : ℂ))ᴴ = A * diagonal (fun α => ((w α : ℝ) : ℂ)) * Aᴴ := by
  rw [conjTranspose_mul, diag_real_conjTranspose, Matrix.mul_assoc]

/-- **The objective at the projected moment**: `Tr(O_w Yp) = 3072 · q(1/2, A diag(w) Aᴴ)` for Stiefel `A`. -/
theorem trace_Ow_Yp_q {A : MatA} (hA : Aᴴ * A = 1) (w : Fin 2 → ℝ) :
    (Ow w * Yp A).trace = ((3072 * NPT.q (1 / 2) (A * diagonal (fun α => ((w α : ℝ) : ℂ)) * Aᴴ) : ℝ) : ℂ) := by
  rw [trace_Ow_Yp, trace_Ow_Xs, nsq_stiefel hA, mul_diag_conjTranspose]
  push_cast
  ring

end NPT.CP3
