/-
NPT.Cert.EqInt — the equality functionals at the projected moments. The global partial traces (marginal
groups) and the Stiefel contrast intertwine the Hilbert–Schmidt projections onto the word algebras, so the
operator identities that hold at physical moments persist at the projected moments.
-/
import NPT.Cert.EqData

open Matrix BigOperators Finset NPT.Brauer

namespace NPT.Cert

variable {n : ℕ}

/-! ### Kernel identities -/

lemma applyK_add_kernel {mo : ℕ} (κ₁ κ₂ : LKer n mo) (c₁ c₂ : ℂ) (M : Matrix (Dig n 4) (Dig n 4) ℂ) :
    applyK (fun i' j' i j => c₁ * κ₁ i' j' i j - c₂ * κ₂ i' j' i j) M =
      c₁ • applyK κ₁ M - c₂ • applyK κ₂ M := by
  ext i' j'
  simp only [applyK, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma applyK_idK (M : Matrix (Dig n 4) (Dig n 4) ℂ) : applyK (idK (n := n)) M = M := by
  ext i' j'
  simp only [applyK, idK]
  rw [Finset.sum_eq_single i']
  · rw [Finset.sum_eq_single j']
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [hi]
  · simp

/-- Composition of a kernel with an adjoint kernel. -/
lemma applyK_comp {mo : ℕ} (κ₁ κ₂ : LKer n mo) (κ₃ : LKer n 4)
    (h : ∀ i j a b, κ₃ i j a b = ∑ i', ∑ j', adjK κ₁ i j i' j' * κ₂ i' j' a b)
    (M : Matrix (Dig n 4) (Dig n 4) ℂ) : applyK κ₃ M = applyA κ₁ (applyK κ₂ M) := by
  ext i j
  simp only [applyK, applyA, h, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  calc ∑ a, ∑ b, ∑ i', ∑ j', adjK κ₁ i j i' j' * (κ₂ i' j' a b * M a b)
      = ∑ a, ∑ i', ∑ b, ∑ j', adjK κ₁ i j i' j' * (κ₂ i' j' a b * M a b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ i', ∑ j', ∑ b, adjK κ₁ i j i' j' * (κ₂ i' j' a b * M a b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i' _ => Finset.sum_comm
    _ = ∑ i', ∑ a, ∑ j', ∑ b, adjK κ₁ i j i' j' * (κ₂ i' j' a b * M a b) := Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ a, ∑ b, adjK κ₁ i j i' j' * (κ₂ i' j' a b * M a b) :=
        Finset.sum_congr rfl fun i' _ => Finset.sum_comm

lemma etK_eq (sl : Fin 4) (ordF : Fin 3 → Fin 4) (i j a b : Dig n 4) :
    etK sl ordF i j a b = ∑ i', ∑ j', adjK (delK sl ordF) i j i' j' * delK sl ordF i' j' a b := by
  simp only [adjK, delK]
  rw [Finset.sum_eq_single (i ∘ ordF)]
  · rw [Finset.sum_eq_single (j ∘ ordF)]
    · simp only [etK, true_and]
      by_cases h1 : i sl = j sl <;> by_cases h2 : a ∘ ordF = i ∘ ordF <;>
        by_cases h3 : b ∘ ordF = j ∘ ordF <;> by_cases h4 : a sl = b sl <;> simp [h1, h2, h3, h4]
    · intro j' _ hj'; simp [Ne.symm hj']
    · simp
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun j' _ => by simp [Ne.symm hi']
  · simp

lemma applyK_etK (sl : Fin 4) (ordF : Fin 3 → Fin 4) (M : Matrix (Dig n 4) (Dig n 4) ℂ) :
    applyK (etK sl ordF) M = applyA (delK sl ordF) (applyK (delK sl ordF) M) :=
  applyK_comp _ _ _ (etK_eq sl ordF) M

lemma applyK_stK (sl : Fin 4) (ordF : Fin 3 → Fin 4) (M : Matrix (Dig n 4) (Dig n 4) ℂ) :
    applyK (stK sl ordF) M = (2 : ℂ) • M - applyK (etK sl ordF) M := by
  have := applyK_add_kernel (idK (n := n)) (etK sl ordF) 2 1 M
  simp only [one_mul, one_smul, applyK_idK] at this
  rw [← this]
  rfl

lemma adjK_etK (sl : Fin 4) (ordF : Fin 3 → Fin 4) : adjK (etK (n := n) sl ordF) = etK sl ordF := by
  funext i j i' j'
  simp only [adjK, etK]
  by_cases h : i' sl = j' sl ∧ i ∘ ordF = i' ∘ ordF ∧ j ∘ ordF = j' ∘ ordF ∧ i sl = j sl
  · have h' : i sl = j sl ∧ i' ∘ ordF = i ∘ ordF ∧ j' ∘ ordF = j ∘ ordF ∧ i' sl = j' sl :=
      ⟨h.2.2.2, h.2.1.symm, h.2.2.1.symm, h.1⟩
    rw [ite_eq_left h, ite_eq_left h', star_one]
  · have h' : ¬ (i sl = j sl ∧ i' ∘ ordF = i ∘ ordF ∧ j' ∘ ordF = j ∘ ordF ∧ i' sl = j' sl) :=
      fun h' => h ⟨h'.2.2.2, h'.2.1.symm, h'.2.2.1.symm, h'.1⟩
    rw [ite_eq_right h, ite_eq_right h', star_zero]

lemma adjK_stK (sl : Fin 4) (ordF : Fin 3 → Fin 4) : adjK (stK (n := n) sl ordF) = stK sl ordF := by
  funext i j i' j'
  have h1 := congrFun (congrFun (congrFun (congrFun (adjK_etK (n := n) sl ordF) i) j) i') j'
  simp only [adjK] at h1
  simp only [adjK, stK, star_sub, star_mul', h1]
  congr 1
  simp only [idK]
  by_cases h : i = i' ∧ j = j'
  · have h' : i' = i ∧ j' = j := ⟨h.1.symm, h.2.symm⟩
    rw [ite_eq_left h', ite_eq_left h]; simp
  · have h' : ¬ (i' = i ∧ j' = j) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    rw [ite_eq_right h', ite_eq_right h]; simp

/-! ### Local closure facts for the five combinations -/

lemma etK_VG {c : ℕ} (hc : SOok c) (ht : ∀ p, TCertOK c p) (hb : ∀ q : Fin 6, ∀ t : Fin 4,
      (if t = csl c then csl c else cord c (p3inv q (cinv c t))) = pinvf (bq c q) t) (p : Fin 24) :
    applyK (etK (n := n) (csl c) (cord c)) (VG ℂ n 0 p) = ((n : ℂ) ^ te c p) • VG ℂ n 0 (bq c (tq c p)) := by
  rw [applyK_etK, delK_VG hc p (ht p)]
  have hlin : applyA (delK (n := n) (csl c) (cord c)) (((n : ℂ) ^ te c p) • V3 n (tq c p)) =
      ((n : ℂ) ^ te c p) • applyA (delK (csl c) (cord c)) (V3 n (tq c p)) := by
    ext i j; simp only [applyA, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring
  rw [hlin, adj_delK_V3 hc _ (hb _)]

section Global

variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ}

/-- Three-replica global word operators. -/
def VW3 (u : L → Fin 6) : Matrix (GO nf (fun _ => 3)) (GO nf (fun _ => 3)) ℂ := kron fun l => V3 (nf l) (u l)

/-- Their span (output space of the marginal maps). -/
def span3 : Submodule ℂ (Matrix (GO nf (fun _ => 3)) (GO nf (fun _ => 3)) ℂ) :=
  Submodule.span ℂ (Set.range (VW3 (nf := nf)))

/-- Global partial trace of combination `c` (the same traced slot on every factor). -/
def trKer (c : ℕ) : (l : L) → LKer (nf l) 3 := fun _ => delK (csl c) (cord c)

lemma applyGA_add (κ : (l : L) → LKer (nf l) 3) (N₁ N₂ : Matrix (GO nf (fun _ => 3)) (GO nf (fun _ => 3)) ℂ) :
    applyGA κ (N₁ + N₂) = applyGA κ N₁ + applyGA κ N₂ := by
  ext i j; simp only [applyGA, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma applyGA_smul (κ : (l : L) → LKer (nf l) 3) (a : ℂ) (N : Matrix (GO nf (fun _ => 3)) (GO nf (fun _ => 3)) ℂ) :
    applyGA κ (a • N) = a • applyGA κ N := by
  ext i j; simp only [applyGA, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring

lemma trKer_mem {c : ℕ} (hc : SOok c) (ht : ∀ p, TCertOK c p) {Y : Matrix (GI nf) (GI nf) ℂ}
    (hY : Y ∈ spanS (nf := nf) 0) : applyG (trKer c) Y ∈ span3 (nf := nf) := by
  induction hY using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, rfl⟩ := ha
    unfold VW
    rw [applyG_kron]
    simp only [trKer]
    rw [show (fun l => applyK (delK (n := nf l) (csl c) (cord c)) (VG ℂ (nf l) 0 (w l))) =
        fun l => ((nf l : ℂ) ^ te c (w l)) • V3 (nf l) (tq c (w l)) from
        funext fun l => delK_VG hc (w l) (ht (w l)), kron_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun l => tq c (w l), rfl⟩)
  | zero => rw [show applyG (trKer c) (0 : Matrix (GI nf) (GI nf) ℂ) = 0 from (applyGL (trKer c)).map_zero]
            exact Submodule.zero_mem _
  | add x z _ _ h1 h2 =>
    rw [show applyG (trKer c) (x + z) = applyG (trKer c) x + applyG (trKer c) z from
      (applyGL (trKer c)).map_add x z]
    exact Submodule.add_mem _ h1 h2
  | smul a x _ h =>
    rw [show applyG (trKer c) (a • x) = a • applyG (trKer c) x from (applyGL (trKer c)).map_smul a x]
    exact Submodule.smul_mem _ a h

lemma trKerA_mem {c : ℕ} (hc : SOok c) (hb : ∀ q : Fin 6, ∀ t : Fin 4,
      (if t = csl c then csl c else cord c (p3inv q (cinv c t))) = pinvf (bq c q) t)
    {N : Matrix (GO nf (fun _ => 3)) (GO nf (fun _ => 3)) ℂ}
    (hN : N ∈ span3 (nf := nf)) : applyGA (trKer c) N ∈ spanS (nf := nf) 0 := by
  induction hN using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, rfl⟩ := ha
    unfold VW3
    rw [applyGA_kron]
    simp only [trKer]
    rw [show (fun l => applyA (delK (n := nf l) (csl c) (cord c)) (V3 (nf l) (u l))) =
        fun l => VG ℂ (nf l) 0 (bq c (u l)) from funext fun l => adj_delK_V3 hc (u l) (hb (u l))]
    exact VW_mem 0 _
  | zero =>
    have : applyGA (trKer (nf := nf) c) 0 = 0 := by ext i j; simp [applyGA]
    rw [this]; exact Submodule.zero_mem _
  | add x z _ _ h1 h2 => rw [applyGA_add]; exact Submodule.add_mem _ h1 h2
  | smul a x _ h => rw [applyGA_smul]; exact Submodule.smul_mem _ a h

/-- **Marginal equalities at the projected moments.** -/
theorem marginal_proj {c₁ c₂ : ℕ} (hc₁ : SOok c₁) (hc₂ : SOok c₂) (ht₁ : ∀ p, TCertOK c₁ p)
    (ht₂ : ∀ p, TCertOK c₂ p)
    (hb₁ : ∀ q : Fin 6, ∀ t : Fin 4, (if t = csl c₁ then csl c₁ else cord c₁ (p3inv q (cinv c₁ t))) = pinvf (bq c₁ q) t)
    (hb₂ : ∀ q : Fin 6, ∀ t : Fin 4, (if t = csl c₂ then csl c₂ else cord c₂ (p3inv q (cinv c₂ t))) = pinvf (bq c₂ q) t)
    {X₁ X₂ Y₁ Y₂ : Matrix (GI nf) (GI nf) ℂ} (h₁ : IsProj (spanS (nf := nf) 0) X₁ Y₁)
    (h₂ : IsProj (spanS (nf := nf) 0) X₂ Y₂) (hX : applyG (trKer c₁) X₁ = applyG (trKer c₂) X₂) :
    applyG (trKer c₁) Y₁ = applyG (trKer c₂) Y₂ := by
  have p₁ := h₁.map (applyGL (trKer c₁)) (fun Y hY => trKer_mem hc₁ ht₁ hY)
    (fun N hN => ⟨applyGA (trKer c₁) N, trKerA_mem hc₁ hb₁ hN, fun Z => trace_applyG _ N Z⟩)
  have p₂ := h₂.map (applyGL (trKer c₂)) (fun Y hY => trKer_mem hc₂ ht₂ hY)
    (fun N hN => ⟨applyGA (trKer c₂) N, trKerA_mem hc₂ hb₂ hN, fun Z => trace_applyG _ N Z⟩)
  change IsProj _ (applyG (trKer c₁) X₁) (applyG (trKer c₁) Y₁) at p₁
  change IsProj _ (applyG (trKer c₂) X₂) (applyG (trKer c₂) Y₂) at p₂
  rw [hX] at p₁
  exact p₁.unique p₂

/-- Stiefel kernel family: `stK` on the auxiliary factor(s), `etK` elsewhere. -/
def stKer (aux : L → Prop) [DecidablePred aux] (c : ℕ) : (l : L) → LKer (nf l) 4 :=
  fun l => if aux l then stK (csl c) (cord c) else etK (csl c) (cord c)

lemma stKer_local {c : ℕ} (hc : SOok c) (ht : ∀ p, TCertOK c p) (hb : ∀ q : Fin 6, ∀ t : Fin 4,
      (if t = csl c then csl c else cord c (p3inv q (cinv c t))) = pinvf (bq c q) t)
    (aux : L → Prop) [DecidablePred aux] (l : L) (p : Fin 24) :
    applyK (stKer (nf := nf) aux c l) (VG ℂ (nf l) 0 p) ∈
      Submodule.span ℂ (Set.range (VG ℂ (nf l) 0)) := by
  have hE : applyK (etK (n := nf l) (csl c) (cord c)) (VG ℂ (nf l) 0 p) ∈
      Submodule.span ℂ (Set.range (VG ℂ (nf l) 0)) := by
    rw [etK_VG hc ht hb p]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  unfold stKer
  split_ifs
  · rw [applyK_stK]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) hE
  · exact hE

lemma stKer_mem {c : ℕ} (hc : SOok c) (ht : ∀ p, TCertOK c p) (hb : ∀ q : Fin 6, ∀ t : Fin 4,
      (if t = csl c then csl c else cord c (p3inv q (cinv c t))) = pinvf (bq c q) t)
    (aux : L → Prop) [DecidablePred aux] {Y : Matrix (GI nf) (GI nf) ℂ}
    (hY : Y ∈ spanS (nf := nf) 0) : applyG (stKer aux c) Y ∈ spanS (nf := nf) 0 := by
  induction hY using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, rfl⟩ := ha
    unfold VW
    rw [applyG_kron]
    exact kron_mem_span (fun l => VG ℂ (nf l) 0) (fun l => stKer_local hc ht hb aux l (w l))
  | zero => rw [show applyG (stKer aux c) (0 : Matrix (GI nf) (GI nf) ℂ) = 0 from
              (applyGL (stKer aux c)).map_zero]
            exact Submodule.zero_mem _
  | add x z _ _ h1 h2 =>
    rw [show applyG (stKer aux c) (x + z) = applyG (stKer aux c) x + applyG (stKer aux c) z from
      (applyGL (stKer aux c)).map_add x z]
    exact Submodule.add_mem _ h1 h2
  | smul a x _ h =>
    rw [show applyG (stKer aux c) (a • x) = a • applyG (stKer aux c) x from
      (applyGL (stKer aux c)).map_smul a x]
    exact Submodule.smul_mem _ a h

lemma stKer_adj (aux : L → Prop) [DecidablePred aux] (c : ℕ) (N : Matrix (GI nf) (GI nf) ℂ) :
    applyGA (stKer aux c) N = applyG (stKer aux c) N := by
  have h : ∀ l, adjK (stKer (nf := nf) aux c l) = stKer aux c l := by
    intro l; unfold stKer; split_ifs
    · exact adjK_stK _ _
    · exact adjK_etK _ _
  ext i j
  simp only [applyGA, applyG, h]

/-- **Stiefel equalities at the projected moments.** -/
theorem stiefel_proj {c : ℕ} (hc : SOok c) (ht : ∀ p, TCertOK c p) (hb : ∀ q : Fin 6, ∀ t : Fin 4,
      (if t = csl c then csl c else cord c (p3inv q (cinv c t))) = pinvf (bq c q) t)
    (aux : L → Prop) [DecidablePred aux]
    {X Y : Matrix (GI nf) (GI nf) ℂ} (h : IsProj (spanS (nf := nf) 0) X Y)
    (hX : applyG (stKer aux c) X = 0) : applyG (stKer aux c) Y = 0 :=
  h.map_eq_zero (applyGL (stKer aux c)) (fun Y hY => stKer_mem hc ht hb aux hY)
    (fun N hN => ⟨applyGA (stKer aux c) N, by rw [stKer_adj]; exact stKer_mem hc ht hb aux hN,
      fun Z => trace_applyG _ N Z⟩) hX

end Global

end NPT.Cert
