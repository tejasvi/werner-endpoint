/-
NPT.Cert.Assembly — combinatorial parts of the soundness theorem: class sums of the identity fact, and the
expansion of `Σ_f Σ_w c_f(w) Λ_f(w)` into objective, block and equality parts.
-/
import NPT.Cert.SemLink

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert

namespace Sem.CertD

variable (C : CertD)

/-- **Class sums.** A coefficient function constant on the classes of the identity fact pairs to zero with `Λ_f`. -/
lemma class_sum_zero (hid : IdFact C) {f : ℕ} (hf : f < 3) (c : (Fin (C.k + 1) → Fin 24) → ℂ)
    (hc : ∀ w, c w = c (hid.rep f (hid.cls f w))) :
    ∑ w, c w * ((C.Λ f w : ℚ) : ℂ) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (hid.cls f))
    (g := hid.cls f) (fun w _ => Finset.mem_image_of_mem _ (Finset.mem_univ w))]
  refine Finset.sum_eq_zero fun v hv => ?_
  obtain ⟨w₀, -, hw₀⟩ := Finset.mem_image.1 hv
  have e : ∀ w ∈ Finset.univ.filter (fun w => hid.cls f w = v),
      c w * ((C.Λ f w : ℚ) : ℂ) = c (hid.rep f v) * ((C.Λ f w : ℚ) : ℂ) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [hc w, hw.2]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have h0 := hid.hsum f hf w₀
  rw [hw₀] at h0
  have h0' : ∑ w ∈ Finset.univ.filter (fun w => hid.cls f w = v), ((C.Λ f w : ℚ) : ℂ) = 0 := by
    rw [← Rat.cast_sum, h0, Rat.cast_zero]
  rw [h0', mul_zero]

lemma sum_list_comm {α β : Type*} (s : Finset β) (L : List α) (G : β → α → ℂ) :
    ∑ f ∈ s, (L.map (G f)).sum = (L.map fun a => ∑ f ∈ s, G f a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

lemma mul_list_sum {α : Type*} (x : ℂ) (L : List α) (G : α → ℂ) :
    x * (L.map G).sum = (L.map fun a => x * G a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

lemma cast_list_sum {α : Type*} (L : List α) (G : α → ℚ) :
    (((L.map G).sum : ℚ) : ℂ) = (L.map fun a => ((G a : ℚ) : ℂ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]

lemma list_sum_congr {α : Type*} (L : List α) (G H : α → ℂ) (h : ∀ a ∈ L, G a = H a) :
    (L.map G).sum = (L.map H).sum := by
  rw [List.map_congr_left h]

/-- Collapse of the family indicator: `Σ_f Σ_w c_f(w) [fam = f] b(w) = Σ_w c_fam(w) b(w)`. -/
lemma fam_collapse {ι : Type*} (S : Finset ι) (fam : ι → ℕ) (hfam : ∀ i ∈ S, fam i < 3)
    (c : ℕ → (Fin (C.k + 1) → Fin 24) → ℂ) (b : ι → (Fin (C.k + 1) → Fin 24) → ℂ) :
    ∑ f ∈ Finset.range 3, ∑ w, c f w * ∑ i ∈ S, (if fam i = f then b i w else 0) =
      ∑ i ∈ S, ∑ w, c (fam i) w * b i w := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, w]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun w _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [hfam i hi]

/-- **Expansion** of the paired identity into objective, blocks and equalities. -/
lemma Lambda_expand (c : ℕ → (Fin (C.k + 1) → Fin 24) → ℂ)
    (hfam : ∀ t ∈ C.types, ∀ r < t.nrows, ∀ s < t.nrows, (ruleOf t r s).fam < 3)
    (hpfam : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, P.fam < 3) :
    ∑ f ∈ Finset.range 3, ∑ w, c f w * ((C.Λ f w : ℚ) : ℂ) =
      ∑ w, c 0 w * ((C.obj w : ℚ) : ℂ)
      - (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
          ∑ w, c (ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum
      - (C.eqs.map fun g => (g.parts.map fun P =>
          (P.sign : ℂ) * ∑ w, c P.fam w * ((C.eqVal g P w : ℚ) : ℂ)).sum).sum := by
  have hΛ : ∀ f w, ((C.Λ f w : ℚ) : ℂ) = (if f = 0 then ((C.obj w : ℚ) : ℂ) else 0)
      - (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
          if ((t.rules.getD r []).getD s default).fam = f then ((C.blk t r s w : ℚ) : ℂ) else 0).sum
      - (C.eqs.map fun g => (g.parts.map fun P =>
          if P.fam = f then (P.sign : ℂ) * ((C.eqVal g P w : ℚ) : ℂ) else 0).sum).sum := by
    intro f w
    simp only [Λ, Rat.cast_sub, cast_list_sum, List.map_map, Function.comp_def]
    congr 1
    · congr 1
      · split_ifs <;> simp
      · refine list_sum_congr _ _ _ fun t _ => ?_
        push_cast
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        split_ifs <;> simp
    · refine list_sum_congr _ _ _ fun g _ => ?_
      try rw [cast_list_sum]
      refine list_sum_congr _ _ _ fun P _ => ?_
      split_ifs <;> simp
  simp only [hΛ, mul_sub, Finset.sum_sub_distrib]
  congr 1
  congr 1
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro f _ hf; simp [hf]
    · simp
  · -- blocks
    simp only [mul_list_sum, sum_list_comm]
    refine list_sum_congr _ _ _ fun t ht => ?_
    have h := fam_collapse C (Finset.range t.nrows ×ˢ Finset.range t.nrows)
      (fun rs => ((t.rules.getD rs.1 []).getD rs.2 default).fam)
      (fun rs hrs => by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hrs
        exact hfam t ht _ hrs.1 _ hrs.2) c (fun rs w => ((C.blk t rs.1 rs.2 w : ℚ) : ℂ))
    simp only [Finset.sum_product] at h
    exact h
  · -- equalities
    simp only [mul_list_sum, sum_list_comm]
    refine list_sum_congr _ _ _ fun g hg => ?_
    refine list_sum_congr _ _ _ fun P hP => ?_
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_range, hpfam g hg P hP, if_true]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring

end Sem.CertD

end NPT.Cert
