import NPT.CP3.Chk.D2Defs
import NPT.CP3.SemD0

/-!
# NPT.CP3.SemD2 — the bosonic range of each tuple (flat level)

`Pflat v` is the average over the 24 replica permutations of the representation of tuple `v` on its true-dims
multi-indices (`flatMI` order): `Pflat v t s = (1/24) Σ_g Π_l π_{l, τ_v l}(g)[t_l][s_l]`, with `t_l = digL dims l t`.
`d2_of_check` derives `(Pflat v)ᵀ = Wq v * (Wl v * (Pflat v)ᵀ)` (every column of `Pflatᵀ` lies in the column space of
`W`) from the list check `d2OK v`. For the tuples with `m = 0` this says `Pflat v = 0`.
-/

open Matrix BigOperators Finset
open NPT.CP3.Data NPT.CP3.Chk

namespace NPT.CP3.Sem

/-- The averaged representation of tuple `v` on its true-dims multi-indices. -/
def Pflat (v : ℕ) : Matrix (Fin (nV v)) (Fin (nV v)) ℚ :=
  fun t s => (∑ g ∈ range 24, ∏ l ∈ range 5,
    (piflI l (tauV v l) g (digL (vb v).dims l t) (digL (vb v).dims l s) : ℚ)) / 24

theorem lprod_map_range : ∀ (n : ℕ) (f : ℕ → Int), lprod ((List.range n).map f) = ∏ l ∈ range n, f l
  | 0, _ => rfl
  | n + 1, f => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, lprod, lprod_map_range n (f ∘ Nat.succ),
      Finset.prod_range_succ']
    simp [mul_comm]

theorem P24_cast (v t s : ℕ) : (P24 v t s : ℚ) = ∑ g ∈ range 24, ∏ l ∈ range 5,
    (piflI l (tauV v l) g (digL (vb v).dims l t) (digL (vb v).dims l s) : ℚ) := by
  rw [P24, P24b, lsum_eq_sum, sum_map_range_eq]
  push_cast
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [lprod_map_range]
  push_cast
  rfl

theorem Pflat_eq (v : ℕ) (t s : Fin (nV v)) : Pflat v t s = (P24 v t s : ℚ) / 24 := by
  rw [P24_cast]
  rfl

theorem d2_of_check {v : ℕ} (hs : wshapeOK v = true) (h : d2OK v = true) :
    (Pflat v)ᵀ = Wq v * (Wl v * (Pflat v)ᵀ) := by
  have hs0 := hs
  simp only [wshapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨-, -⟩, hpl⟩, hpv⟩, hR⟩, hr0⟩ := hs
  obtain ⟨hRl, hRr⟩ := shapeOK_spec hR
  have hrden : ((dv v).rden : ℚ) ≠ 0 := by exact_mod_cast hr0.ne'
  simp only [d2OK, d2OKb, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  ext t s
  -- the integer identity at (s, t)
  have key : ((dv v).rden : ℤ) * P24 v s t = ∑ j ∈ range (mV v), mget (vb v).W t j *
      ∑ k ∈ range (mV v), mget (dv v).rinv j k * P24 v s ((dv v).piv.getD k 0) := by
    have e := h s s.isLt t t.isLt
    change ((dv v).rden : ℤ) * P24 v s t = dot ((vb v).W.getD t [])
      ((dv v).rinv.map fun row => dot row ((dv v).piv.map fun p => P24 v s p)) at e
    rw [dot_eq_sum _ _ (mV v) (wshape_rows hs0 t t.isLt) (by rw [List.length_map]; exact hRl)] at e
    rw [e]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < (dv v).rinv.length := by rw [hRl]; simpa using hj
    rw [getD_map_of_lt _ _ _ _ [] hj', dot_eq_sum _ _ (mV v) (hRr j (by simpa using hj)) (by rw [List.length_map, hpl])]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < (dv v).piv.length := by rw [hpl]; simpa using hk
    rw [getD_map_of_lt _ _ _ _ 0 hk']
    rfl
  -- the inner sum over the rows of W⁺
  have hin : ∀ j : Fin (mV v), ∑ x : Fin (nV v), Wl v j x * (Pflat v)ᵀ x s =
      ∑ k ∈ range (mV v), (mget (dv v).rinv j k : ℚ) / (dv v).rden * ((P24 v s ((dv v).piv.getD k 0) : ℚ) / 24) := by
    intro j
    simp only [Wl, Matrix.transpose_apply, Pflat_eq, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hlt : (dv v).piv.getD k 0 < nV v := by
      have : k < (dv v).piv.length := by rw [hpl]; simpa using hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, Option.getD_some]
      exact hpv _ (List.getElem_mem _)
    simp only [ite_mul, zero_mul]
    rw [sum_fin_ite ((dv v).piv.getD k 0)
      (fun x => (mget (dv v).rinv j k : ℚ) / (dv v).rden * ((P24 v s x : ℚ) / 24)), if_pos hlt]
  rw [Matrix.transpose_apply, Pflat_eq, Matrix.mul_apply]
  simp only [Matrix.mul_apply, hin, Wq]
  rw [Fin.sum_univ_eq_sum_range (fun j => (mget (vb v).W t j : ℚ) * ∑ k ∈ range (mV v),
    (mget (dv v).rinv j k : ℚ) / (dv v).rden * ((P24 v s ((dv v).piv.getD k 0) : ℚ) / 24)) (mV v)]
  have hR' : ∑ j ∈ range (mV v), (mget (vb v).W t j : ℚ) * ∑ k ∈ range (mV v),
      (mget (dv v).rinv j k : ℚ) / (dv v).rden * ((P24 v s ((dv v).piv.getD k 0) : ℚ) / 24) =
      ((∑ j ∈ range (mV v), mget (vb v).W t j * ∑ k ∈ range (mV v),
        mget (dv v).rinv j k * P24 v s ((dv v).piv.getD k 0) : ℤ) : ℚ) / (24 * (dv v).rden) := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [hR', ← key]
  push_cast
  field_simp

end NPT.CP3.Sem
