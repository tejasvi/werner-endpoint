/-
NPT.Cert.Sym — orbit-constant moment coefficients. The Hilbert–Schmidt projection `Y` onto `span {V_w}`
(cut 0) of an operator `X` invariant under `G_f × G_f` (two-sided multiplication by constant words), the
site permutations and transposition inherits these invariances (uniqueness of projections); its
coefficients in the word basis are then averaged over `G_f × G_f`, the site permutations and inversion,
which makes them constant on the orbits of `Sem.act`. Finite conventions (`ptab0` products, composition
and inversion of permutation indices, closure of `G_f`) are checked by `decide +kernel`.
-/
import NPT.Cert.SymDefs
import NPT.Cert.Proj
import NPT.Cert.Sem

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert

namespace SymAvg

/-! ### Finite conventions (kernel-checked) -/

lemma ptab0_eD : ∀ p q : Fin 24, eD (ptabOf 0) p q = 0 := by decide +kernel
lemma ptab0_rD : ∀ p q : Fin 24, rD (ptabOf 0) p q = mulIdx p q := by decide +kernel
lemma pf_mulIdx : ∀ p q : Fin 24, ∀ s, pf (mulIdx p q) s = pf p (pf q s) := by decide +kernel
lemma pf_pinvIdx : ∀ p : Fin 24, ∀ s, pf (pinvIdx p) s = pinvf p s := by decide +kernel
lemma pf_inj : ∀ p q : Fin 24, (∀ s, pf p s = pf q s) → p = q := by decide +kernel

lemma permE_mul (p q : Fin 24) : permE (mulIdx p q) = permE p * permE q :=
  Equiv.ext fun s => pf_mulIdx p q s

lemma permE_pinv (p : Fin 24) : permE (pinvIdx p) = (permE p)⁻¹ :=
  Equiv.ext fun s => pf_pinvIdx p s

lemma permE_injective : Function.Injective permE :=
  fun p q h => pf_inj p q fun s => Equiv.ext_iff.1 h s

/-! ### Word actions -/

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

lemma VG_cast {n n' : ℕ} (h : n' = n) (p : Fin 24) (a b : Dig n' 4) :
    VG ℂ n 0 p (Fin.cast h ∘ a) (Fin.cast h ∘ b) = VG ℂ n' 0 p a b := by
  subst h; rfl

lemma VG_transpose {n : ℕ} (p : Fin 24) : (VG ℂ n 0 p)ᵀ = VG ℂ n 0 (pinvIdx p) := by
  ext a b
  rw [Matrix.transpose_apply, VG0_apply, VG0_apply]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · rw [h]; funext s; simp [Function.comp, pinvf_pinvIdx, pinvf_pf]
  · rw [h]; funext s; simp [Function.comp, pinvf_pinvIdx, pf_pinvf]

variable {k d : ℕ}

lemma VW_transpose (w : Fin (k + 1) → Fin 24) :
    (VW (nf k d) 0 w)ᵀ = VW (nf k d) 0 (fun l => pinvIdx (w l)) := by
  ext i j
  simp only [VW, kron, Matrix.transpose_apply]
  exact Finset.prod_congr rfl fun l _ => by rw [← VG_transpose]; rfl

lemma VW_mul0 (w u : Fin (k + 1) → Fin 24) :
    VW (nf k d) 0 w * VW (nf k d) 0 u = VW (nf k d) 0 (fun l => mulIdx (w l) (u l)) := by
  rw [VW_mul (by simp [cutsUsed]) w u]
  simp only [ptab0_eD, pow_zero, Finset.prod_const_one, one_smul, ptab0_rD]

lemma VWc_mul (g h : Fin 24) (w : Fin (k + 1) → Fin 24) :
    VWc g * VW (nf k d) 0 w * VWc h = VW (nf k d) 0 (fun l => mulIdx g (mulIdx (w l) h)) := by
  unfold VWc
  rw [Matrix.mul_assoc, VW_mul0, VW_mul0]

lemma sigHat_symm_sigHat (σ : Equiv.Perm (Fin k)) (l : Fin (k + 1)) : sigHat σ.symm (sigHat σ l) = l :=
  (sigHat σ).symm_apply_apply l

lemma sigHat_sigHat_symm (σ : Equiv.Perm (Fin k)) (l : Fin (k + 1)) : sigHat σ (sigHat σ.symm l) = l :=
  (sigHat σ).apply_symm_apply l

lemma siteAct_VW (σ : Equiv.Perm (Fin k)) (w : Fin (k + 1) → Fin 24) :
    siteAct σ (VW (nf k d) 0 w) = VW (nf k d) 0 (w ∘ sigHat σ.symm) := by
  ext i j
  simp only [siteAct, VW, kron]
  refine Fintype.prod_equiv (sigHat σ) _ _ fun l => ?_
  refine (VG_cast (nf_sigHat σ l) (w l) (i (sigHat σ l)) (j (sigHat σ l))).trans ?_
  simp only [Function.comp_apply, sigHat_symm_sigHat]

lemma permIdx_symm (σ : Equiv.Perm (Fin k)) (i : GI (nf k d)) : permIdx σ.symm (permIdx σ i) = i := by
  funext l r
  apply Fin.ext
  simp only [permIdx, Fin.val_cast]
  have key : ∀ m (_ : m = l), ((i m r : Fin (nf k d m)) : ℕ) = (i l r : ℕ) := by rintro m rfl; rfl
  exact key _ (sigHat_sigHat_symm σ l)

lemma permIdx_symm' (σ : Equiv.Perm (Fin k)) (i : GI (nf k d)) : permIdx σ (permIdx σ.symm i) = i := by
  funext l r
  apply Fin.ext
  simp only [permIdx, Fin.val_cast]
  have key : ∀ m (_ : m = l), ((i m r : Fin (nf k d m)) : ℕ) = (i l r : ℕ) := by rintro m rfl; rfl
  exact key _ (sigHat_symm_sigHat σ l)

/-! ### The three maps, their adjoints, and invariance of the projection -/

variable (k d) in
/-- `M ↦ VWc g * M * VWc h`. -/
def Tgh (g h : Fin 24) : Matrix (GI (nf k d)) (GI (nf k d)) ℂ →ₗ[ℂ] Matrix (GI (nf k d)) (GI (nf k d)) ℂ where
  toFun M := VWc g * M * VWc h
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

variable (k d) in
/-- `M ↦ siteAct σ M`. -/
def Tsite (σ : Equiv.Perm (Fin k)) :
    Matrix (GI (nf k d)) (GI (nf k d)) ℂ →ₗ[ℂ] Matrix (GI (nf k d)) (GI (nf k d)) ℂ where
  toFun := siteAct σ
  map_add' A B := by ext i j; rfl
  map_smul' c A := by ext i j; rfl

variable (k d) in
/-- `M ↦ Mᵀ`. -/
def Ttr : Matrix (GI (nf k d)) (GI (nf k d)) ℂ →ₗ[ℂ] Matrix (GI (nf k d)) (GI (nf k d)) ℂ where
  toFun M := Mᵀ
  map_add' := Matrix.transpose_add
  map_smul' c A := Matrix.transpose_smul c A

lemma map_spanS (T : Matrix (GI (nf k d)) (GI (nf k d)) ℂ →ₗ[ℂ] Matrix (GI (nf k d)) (GI (nf k d)) ℂ)
    (hT : ∀ w, T (VW (nf k d) 0 w) ∈ spanS (nf := nf k d) 0) :
    ∀ Y ∈ spanS (nf := nf k d) 0, T Y ∈ spanS (nf := nf k d) 0 := by
  intro Y hY
  have hle : spanS (nf := nf k d) 0 ≤ (spanS (nf := nf k d) 0).comap T :=
    Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact hT w)
  exact hle hY

lemma proj_inv (T : Matrix (GI (nf k d)) (GI (nf k d)) ℂ →ₗ[ℂ] Matrix (GI (nf k d)) (GI (nf k d)) ℂ)
    (hT : ∀ w, T (VW (nf k d) 0 w) ∈ spanS (nf := nf k d) 0)
    (hadj : ∀ N ∈ spanS (nf := nf k d) 0, ∃ M ∈ spanS (nf := nf k d) 0, ∀ Z, (Nᴴ * T Z).trace = (Mᴴ * Z).trace)
    {X Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ} (hY : IsProj (spanS (nf := nf k d) 0) X Y) (hX : T X = X) :
    T Y = Y := by
  have h := hY.map T (map_spanS T hT) hadj
  rw [hX] at h
  exact h.unique hY

lemma Tgh_VW (g h : Fin 24) (w : Fin (k + 1) → Fin 24) :
    Tgh k d g h (VW (nf k d) 0 w) = VW (nf k d) 0 (fun l => mulIdx g (mulIdx (w l) h)) := VWc_mul g h w

lemma Tsite_VW (σ : Equiv.Perm (Fin k)) (w : Fin (k + 1) → Fin 24) :
    Tsite k d σ (VW (nf k d) 0 w) = VW (nf k d) 0 (w ∘ sigHat σ.symm) := siteAct_VW σ w

lemma Ttr_VW (w : Fin (k + 1) → Fin 24) :
    Ttr k d (VW (nf k d) 0 w) = VW (nf k d) 0 (fun l => pinvIdx (w l)) := VW_transpose w

lemma Tgh_adj (g h : Fin 24) : ∀ N ∈ spanS (nf := nf k d) 0, ∃ M ∈ spanS (nf := nf k d) 0,
    ∀ Z, (Nᴴ * Tgh k d g h Z).trace = (Mᴴ * Z).trace := by
  intro N hN
  have hg : (VWc (k := k) (d := d) g)ᴴ ∈ spanS (nf := nf k d) 0 :=
    spanS_star_mem (by norm_num) (VW_mem 0 _)
  have hh : (VWc (k := k) (d := d) h)ᴴ ∈ spanS (nf := nf k d) 0 :=
    spanS_star_mem (by norm_num) (VW_mem 0 _)
  refine ⟨(VWc g)ᴴ * N * (VWc h)ᴴ,
    spanS_mul_mem (by simp [cutsUsed]) (spanS_mul_mem (by simp [cutsUsed]) hg hN) hh, fun Z => ?_⟩
  simp only [Tgh, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

lemma Tsite_adj (σ : Equiv.Perm (Fin k)) : ∀ N ∈ spanS (nf := nf k d) 0, ∃ M ∈ spanS (nf := nf k d) 0,
    ∀ Z, (Nᴴ * Tsite k d σ Z).trace = (Mᴴ * Z).trace := by
  intro N hN
  refine ⟨siteAct σ.symm N, map_spanS (Tsite k d σ.symm)
    (fun w => by rw [Tsite_VW]; exact VW_mem 0 _) N hN, fun Z => ?_⟩
  let E : GI (nf k d) ≃ GI (nf k d) := ⟨permIdx σ, permIdx σ.symm, permIdx_symm σ, permIdx_symm' σ⟩
  simp only [Tsite, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, siteAct]
  symm
  rw [← E.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← E.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [E, Equiv.coe_fn_mk, permIdx_symm]

lemma Ttr_adj : ∀ N ∈ spanS (nf := nf k d) 0, ∃ M ∈ spanS (nf := nf k d) 0,
    ∀ Z, (Nᴴ * Ttr k d Z).trace = (Mᴴ * Z).trace := by
  intro N hN
  refine ⟨Nᵀ, map_spanS (Ttr k d) (fun w => by rw [Ttr_VW]; exact VW_mem 0 _) N hN, fun Z => ?_⟩
  simp only [Ttr, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-! ### Group laws on `Fin 24`, the groups `G_f`, and word maps -/

lemma pinv_pinv (x : Fin 24) : pinvIdx (pinvIdx x) = x := by
  apply permE_injective; simp only [permE_pinv, inv_inv]

lemma inG_cases (f : ℕ) : inG f = inG 0 ∨ inG f = inG 1 ∨ inG f = inG 2 := by
  rcases f with _ | _ | f
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma inG_mul_012 : ∀ f < 3, ∀ g h : Fin 24, inG f g = true → inG f h = true →
    inG f (mulIdx g h) = true := by decide +kernel
lemma inG_pinv_012 : ∀ f < 3, ∀ g : Fin 24, inG f g = true → inG f (pinvIdx g) = true := by
  decide +kernel
lemma inG_one_012 : ∀ f < 3, inG f 0 = true := by decide +kernel

lemma inG_mul {f : ℕ} {g h : Fin 24} (hg : inG f g = true) (hh : inG f h = true) :
    inG f (mulIdx g h) = true := by
  rcases inG_cases f with e | e | e <;> rw [e] at hg hh ⊢
  · exact inG_mul_012 0 (by norm_num) g h hg hh
  · exact inG_mul_012 1 (by norm_num) g h hg hh
  · exact inG_mul_012 2 (by norm_num) g h hg hh

lemma inG_pinv {f : ℕ} {g : Fin 24} (hg : inG f g = true) : inG f (pinvIdx g) = true := by
  rcases inG_cases f with e | e | e <;> rw [e] at hg ⊢
  · exact inG_pinv_012 0 (by norm_num) g hg
  · exact inG_pinv_012 1 (by norm_num) g hg
  · exact inG_pinv_012 2 (by norm_num) g hg

lemma inG_one (f : ℕ) : inG f 0 = true := by
  rcases inG_cases f with e | e | e <;> rw [e]
  · exact inG_one_012 0 (by norm_num)
  · exact inG_one_012 1 (by norm_num)
  · exact inG_one_012 2 (by norm_num)

variable (k) in
/-- `w ↦ g ∘ w ∘ h` on every factor. -/
def tauGH (g h : Fin 24) : (Fin (k + 1) → Fin 24) ≃ (Fin (k + 1) → Fin 24) where
  toFun w l := mulIdx g (mulIdx (w l) h)
  invFun w l := mulIdx (pinvIdx g) (mulIdx (w l) (pinvIdx h))
  left_inv w := by funext l; apply permE_injective; simp only [permE_mul, permE_pinv]; group
  right_inv w := by funext l; apply permE_injective; simp only [permE_mul, permE_pinv]; group

variable (k) in
/-- Site permutation of words (`siteAct σ (VW w) = VW (tauS σ w)`). -/
def tauS (σ : Equiv.Perm (Fin k)) : (Fin (k + 1) → Fin 24) ≃ (Fin (k + 1) → Fin 24) where
  toFun w := w ∘ sigHat σ.symm
  invFun w := w ∘ sigHat σ
  left_inv w := by funext l; simp only [Function.comp_apply, sigHat_symm_sigHat]
  right_inv w := by funext l; simp only [Function.comp_apply, sigHat_sigHat_symm]

variable (k) in
/-- Inversion of words. -/
def tauT : (Fin (k + 1) → Fin 24) ≃ (Fin (k + 1) → Fin 24) where
  toFun w l := pinvIdx (w l)
  invFun w l := pinvIdx (w l)
  left_inv w := by funext l; exact pinv_pinv (w l)
  right_inv w := by funext l; exact pinv_pinv (w l)

lemma sigHat_mul (α β : Equiv.Perm (Fin k)) (l : Fin (k + 1)) :
    sigHat (α * β) l = sigHat α (sigHat β l) := by
  by_cases h : l.val < k
  · simp [sigHat, h, Equiv.Perm.mul_apply]
  · simp [sigHat, h]

/-! ### Representations of `Y` in the word basis -/

lemma rep_transport (T : Matrix (GI (nf k d)) (GI (nf k d)) ℂ →ₗ[ℂ] Matrix (GI (nf k d)) (GI (nf k d)) ℂ)
    (τ : (Fin (k + 1) → Fin 24) ≃ (Fin (k + 1) → Fin 24))
    (hTw : ∀ w, T (VW (nf k d) 0 w) = VW (nf k d) 0 (τ w))
    {Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ} (hTY : T Y = Y) {c : (Fin (k + 1) → Fin 24) → ℂ}
    (hc : Y = ∑ w, c w • VW (nf k d) 0 w) :
    Y = ∑ w, c (τ.symm w) • VW (nf k d) 0 w := by
  have h1 : T Y = ∑ w, c w • VW (nf k d) 0 (τ w) := by
    rw [hc, map_sum]; simp only [map_smul, hTw]
  rw [← hTY, h1, ← τ.sum_comp (fun w => c (τ.symm w) • VW (nf k d) 0 w)]
  simp only [Equiv.symm_apply_apply]

lemma rep_avg {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (c : ι → (Fin (k + 1) → Fin 24) → ℂ)
    {Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ} (hc : ∀ i ∈ s, Y = ∑ w, c i w • VW (nf k d) 0 w) :
    Y = ∑ w, ((s.card : ℂ)⁻¹ * ∑ i ∈ s, c i w) • VW (nf k d) 0 w := by
  have hcard : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
  have h1 : ∑ i ∈ s, Y = ∑ i ∈ s, ∑ w, c i w • VW (nf k d) 0 w := Finset.sum_congr rfl hc
  rw [Finset.sum_const, Finset.sum_comm] at h1
  simp only [mul_smul, Finset.sum_smul]
  rw [← Finset.smul_sum, ← h1, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-! ### Averaging over `G_f × G_f`, the site permutations, and inversion -/

section Avg

variable {f : ℕ} {Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}

/-- The group `G_f` as a finset. -/
def Gf (f : ℕ) : Finset (Fin 24) := univ.filter fun g => inG f g = true

lemma mem_Gf {g : Fin 24} : g ∈ Gf f ↔ inG f g = true := by simp [Gf]

lemma stage1 (YG : ∀ g h : Fin 24, inG f g = true → inG f h = true → VWc g * Y * VWc h = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      ∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c' (tauGH k g h w) = c' w := by
  refine ⟨fun w => ((Gf f ×ˢ Gf f).card : ℂ)⁻¹ * ∑ p ∈ Gf f ×ˢ Gf f, c ((tauGH k p.1 p.2).symm w),
    ?_, ?_⟩
  · refine rep_avg _ ⟨(0, 0), Finset.mem_product.2 ⟨mem_Gf.2 (inG_one f), mem_Gf.2 (inG_one f)⟩⟩
      (fun p w => c ((tauGH k p.1 p.2).symm w)) fun p hp => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact rep_transport (Tgh k d p.1 p.2) (tauGH k p.1 p.2) (Tgh_VW p.1 p.2)
      (YG p.1 p.2 (mem_Gf.1 h1) (mem_Gf.1 h2)) hc
  · intro g h hg hh w
    dsimp only
    congr 1
    refine Finset.sum_nbij' (fun p => (mulIdx (pinvIdx g) p.1, mulIdx p.2 (pinvIdx h)))
      (fun q => (mulIdx g q.1, mulIdx q.2 h)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      exact Finset.mem_product.2 ⟨mem_Gf.2 (inG_mul (inG_pinv hg) (mem_Gf.1 h1)),
        mem_Gf.2 (inG_mul (mem_Gf.1 h2) (inG_pinv hh))⟩
    · intro q hq
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
      exact Finset.mem_product.2 ⟨mem_Gf.2 (inG_mul hg (mem_Gf.1 h1)),
        mem_Gf.2 (inG_mul (mem_Gf.1 h2) hh)⟩
    · intro p _
      refine Prod.ext ?_ ?_ <;>
        (apply permE_injective; simp only [permE_mul, permE_pinv]; group)
    · intro q _
      refine Prod.ext ?_ ?_ <;>
        (apply permE_injective; simp only [permE_mul, permE_pinv]; group)
    · intro p _
      congr 1
      funext l
      simp only [tauGH, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      apply permE_injective
      simp only [permE_mul, permE_pinv]
      group

lemma stage2 (YS : ∀ σ : Equiv.Perm (Fin k), siteAct σ Y = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w)
    (hcG : ∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c (tauGH k g h w) = c w) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧
      ∀ (σ : Equiv.Perm (Fin k)) w, c' (tauS k σ w) = c' w := by
  refine ⟨fun w => ((univ : Finset (Equiv.Perm (Fin k))).card : ℂ)⁻¹ * ∑ σ, c ((tauS k σ).symm w),
    ?_, ?_, ?_⟩
  · exact rep_avg univ univ_nonempty (fun σ w => c ((tauS k σ).symm w)) fun σ _ =>
      rep_transport (Tsite k d σ) (tauS k σ) (Tsite_VW σ) (YS σ) hc
  · intro g h hg hh w
    dsimp only
    congr 1
    exact Finset.sum_congr rfl fun σ _ => hcG g h hg hh ((tauS k σ).symm w)
  · intro τ w
    dsimp only
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft τ⁻¹) _ _ fun σ => ?_
    congr 1
    funext l
    simp only [tauS, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Function.comp_apply, Equiv.coe_mulLeft,
      sigHat_mul, Equiv.Perm.inv_def]

lemma stage3 (YT : Yᵀ = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w)
    (hcG : ∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c (tauGH k g h w) = c w)
    (hcS : ∀ (σ : Equiv.Perm (Fin k)) w, c (tauS k σ w) = c w) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧
      (∀ (σ : Equiv.Perm (Fin k)) w, c' (tauS k σ w) = c' w) ∧ ∀ w, c' (tauT k w) = c' w := by
  refine ⟨fun w => ((univ : Finset Bool).card : ℂ)⁻¹ * ∑ b, cond b (c ((tauT k).symm w)) (c w),
    ?_, ?_, ?_, ?_⟩
  · refine rep_avg univ univ_nonempty (fun b w => cond b (c ((tauT k).symm w)) (c w)) fun b _ => ?_
    cases b
    · exact hc
    · exact rep_transport (Ttr k d) (tauT k) Ttr_VW YT hc
  · intro g h hg hh w
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    cases b
    · exact hcG g h hg hh w
    · have e : (tauT k).symm (tauGH k g h w) = tauGH k (pinvIdx h) (pinvIdx g) ((tauT k).symm w) := by
        funext l
        simp only [tauT, tauGH, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
        apply permE_injective
        simp only [permE_mul, permE_pinv]
        group
      show c ((tauT k).symm (tauGH k g h w)) = c ((tauT k).symm w)
      rw [e]
      exact hcG _ _ (inG_pinv hh) (inG_pinv hg) _
  · intro σ w
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    cases b
    · exact hcS σ w
    · exact hcS σ ((tauT k).symm w)
  · intro w
    dsimp only
    congr 1
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, Equiv.symm_apply_apply]
    rw [add_comm]
    rfl

end Avg

/-! ### The word action `act` -/

lemma find_eq {σ : Fin k → Fin k} (hσ : Function.Bijective σ) (t dflt : Fin k) :
    ((List.finRange k).find? fun i => σ i = t).getD dflt = (Equiv.ofBijective σ hσ).symm t := by
  obtain ⟨i0, hi0⟩ := hσ.2 t
  rcases hf : (List.finRange k).find? (fun i => σ i = t) with _ | i
  · rw [List.find?_eq_none] at hf
    exact absurd (decide_eq_true hi0) (hf i0 (List.mem_finRange i0))
  · have hi : σ i = t := by
      have h' := List.find?_some hf
      simpa using h'
    simp only [Option.getD_some]
    apply hσ.1
    rw [Equiv.ofBijective_apply_symm_apply σ hσ t]
    exact hi

lemma act_eq (g1 g2 : Fin 24) {σ : Fin k → Fin k} (hσ : Function.Bijective σ) (ε : Bool)
    (w : Fin (k + 1) → Fin 24) :
    act g1 g2 σ ε w = cond ε (tauT k (tauGH k g1 g2 (tauS k (Equiv.ofBijective σ hσ) w)))
      (tauGH k g1 g2 (tauS k (Equiv.ofBijective σ hσ) w)) := by
  funext l
  have key : (if h : l.val < k then
      (((List.finRange k).find? fun i => σ i = ⟨l.val, h⟩).getD ⟨0, by omega⟩).castSucc else l) =
      sigHat (Equiv.ofBijective σ hσ).symm l := by
    by_cases h : l.val < k
    · rw [dite_eq_left h, find_eq hσ]; simp [sigHat, h]
    · rw [dite_eq_right h]; simp [sigHat, h]
  simp only [act, key]
  cases ε <;> rfl

end SymAvg

open SymAvg in
/-- **Orbit-constant coefficients.** The Hilbert–Schmidt projection `Y` onto `span {V_w}` of an operator `X`
invariant under `G_f × G_f`, the site permutations and transposition has coefficients `c` in the word basis
that are constant on the orbits of `act`. -/
theorem sym_coeffs {k d : ℕ} {f : ℕ} {X Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}
    (hY : IsProj (spanS (nf := nf k d) 0) X Y)
    (hG : ∀ g h : Fin 24, inG f g = true → inG f h = true → VWc g * X * VWc h = X)
    (hS : ∀ σ : Equiv.Perm (Fin k), siteAct σ X = X)
    (hT : Xᵀ = X) :
    ∃ c : (Fin (k + 1) → Fin 24) → ℂ, Y = ∑ w, c w • VW (nf k d) 0 w ∧
      ∀ (g1 g2 : Fin 24) (σ : Fin k → Fin k) (ε : Bool) (w : Fin (k + 1) → Fin 24),
        inG f g1 = true → inG f g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w := by
  have YG : ∀ g h : Fin 24, inG f g = true → inG f h = true → VWc g * Y * VWc h = Y :=
    fun g h hg hh => proj_inv (Tgh k d g h) (fun w => by rw [Tgh_VW]; exact VW_mem 0 _) (Tgh_adj g h)
      hY (hG g h hg hh)
  have YS : ∀ σ : Equiv.Perm (Fin k), siteAct σ Y = Y :=
    fun σ => proj_inv (Tsite k d σ) (fun w => by rw [Tsite_VW]; exact VW_mem 0 _) (Tsite_adj σ) hY (hS σ)
  have YT : Yᵀ = Y := proj_inv (Ttr k d) (fun w => by rw [Ttr_VW]; exact VW_mem 0 _) Ttr_adj hY hT
  obtain ⟨c₀, hc₀⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hY.1
  obtain ⟨c₁, hc₁, hG₁⟩ := stage1 YG hc₀.symm
  obtain ⟨c₂, hc₂, hG₂, hS₂⟩ := stage2 YS hc₁ hG₁
  obtain ⟨c₃, hc₃, hG₃, hS₃, hT₃⟩ := stage3 YT hc₂ hG₂ hS₂
  refine ⟨c₃, hc₃, fun g1 g2 σ ε w hg1 hg2 hσ => ?_⟩
  rw [act_eq g1 g2 hσ ε w]
  cases ε
  · exact (hG₃ g1 g2 hg1 hg2 _).trans (hS₃ _ w)
  · exact (hT₃ _).trans ((hG₃ g1 g2 hg1 hg2 _).trans (hS₃ _ w))

end NPT.Cert

#print axioms NPT.Cert.sym_coeffs
