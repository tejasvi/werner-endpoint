/-
NPT.Cert.PhysObj — the objective identity on physical points:
`Tr(O · X_31) = ‖a‖⁴ · 2^k · q(1/2, A Bᴴ)` for the family-31 moment operator `X_31 = |aaab⟩⟨aaab|`
of a rank-two operator `C = A Bᴴ` (`a = vecOf A`, `b = vecOf B`).

Route: `O = ⊗_sites (2I − F03) ⊗ F03_aux = Σ_J (−1)^|J| 2^(k−|J|) F^{J ∪ aux}`, where `F^T` swaps
replicas 0 and 3 on the factors in `T`; `⟨aaab|F^T|aaab⟩ = ‖a‖⁴ ⟨a⊗b|F^T|a⊗b⟩`, and
`⟨a⊗b|F^{J ∪ aux}|a⊗b⟩ = ‖Tr_J (A Bᴴ)‖² = frobSq (ptrace J (A Bᴴ))`.
-/
import NPT.Cert.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert.Phys

/-! Helper lemmas live in `NPT.Cert.Phys.Obj`. -/
namespace Obj

/-! ### Local operators -/

lemma pinvf21_invol : ∀ s : Fin 4, pinvf 21 (pinvf 21 s) = s := by decide +kernel
lemma pinvf21_0 : pinvf 21 0 = 3 := by decide +kernel
lemma pinvf21_1 : pinvf 21 1 = 1 := by decide +kernel
lemma pinvf21_2 : pinvf 21 2 = 2 := by decide +kernel
lemma pinvf21_3 : pinvf 21 3 = 0 := by decide +kernel

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

lemma comp_swap_iff {n : ℕ} (x y : Fin 4 → Fin n) : x = y ∘ pinvf 21 ↔ y = x ∘ pinvf 21 := by
  constructor <;> rintro rfl <;> funext r <;> simp [Function.comp, pinvf21_invol]

/-- `F03 = V_{21}` swaps replicas `0` and `3`. -/
lemma F03_apply {n : ℕ} (i j : Dig n 4) :
    VG ℂ n 0 21 i j = if j = i ∘ pinvf 21 then 1 else 0 := by
  rw [VG0_apply]
  exact if_congr (comp_swap_iff i j) rfl rfl

variable {k d : ℕ}

lemma Oobj_apply (i j : GI (nf k d)) :
    Oobj k d i j = ∏ l, (if l.val < k then
      2 * (if j l = i l then (1 : ℂ) else 0) - (if j l = i l ∘ pinvf 21 then 1 else 0)
      else (if j l = i l ∘ pinvf 21 then 1 else 0)) := by
  unfold Oobj kron
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : l.val < k
  · simp only [hl, ite_true, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      VG_zero (by norm_num : (0 : ℕ) < 16), Matrix.one_apply, F03_apply, eq_comm]
  · simp only [hl, ite_false, F03_apply]

/-- Factors swapped by `F^{J ∪ aux}`: the sites in `J` and the auxiliary factor. -/
def swapSet (J : Finset (Fin k)) : Finset (Fin (k + 1)) := insert (Fin.last k) (J.map Fin.castSuccEmb)

lemma castSucc_mem_swapSet (J : Finset (Fin k)) (s : Fin k) : s.castSucc ∈ swapSet J ↔ s ∈ J := by
  simp [swapSet, Fin.castSucc_ne_last]

lemma last_mem_swapSet (J : Finset (Fin k)) : Fin.last k ∈ swapSet J := by simp [swapSet]

/-- Swap of replicas `0 ↔ 3` on the factors of `T`. -/
def tau (T : Finset (Fin (k + 1))) (i : GI (nf k d)) : GI (nf k d) :=
  fun l => if l ∈ T then i l ∘ pinvf 21 else i l

lemma prod_ite_mem_univ {α M : Type*} [Fintype α] [DecidableEq α] [CommMonoid M] (J : Finset α)
    (f g : α → M) :
    ∏ s, (if s ∈ J then f s else g s) = (∏ s ∈ J, f s) * ∏ s ∈ univ \ J, g s := by
  rw [← Finset.prod_sdiff (Finset.subset_univ J), mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun s hs => ite_eq_left hs
  · exact Finset.prod_congr rfl fun s hs => ite_eq_right (Finset.mem_sdiff.1 hs).2

/-- `O = Σ_J (-1)^|J| 2^(k-|J|) F^{J ∪ aux}`, entrywise. -/
lemma Oobj_apply_expand (i j : GI (nf k d)) :
    Oobj k d i j = ∑ J : Finset (Fin k), ((-1 : ℂ) ^ J.card * 2 ^ (k - J.card)) *
      (if j = tau (swapSet J) i then 1 else 0) := by
  rw [Oobj_apply, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_irrefl, ite_false]
  set φ : Fin (k + 1) → ℂ := fun l => if j l = i l ∘ pinvf 21 then 1 else 0 with hφ
  set δ : Fin (k + 1) → ℂ := fun l => if j l = i l then 1 else 0 with hδ
  have hexp : ∏ s : Fin k, (2 * δ s.castSucc - φ s.castSucc) =
      ∑ J : Finset (Fin k), (∏ s ∈ J, -φ s.castSucc) * ∏ s ∈ univ \ J, 2 * δ s.castSucc := by
    rw [← Finset.powerset_univ, ← Finset.prod_add]
    exact Finset.prod_congr rfl fun s _ => by ring
  rw [hexp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hind : (if j = tau (swapSet J) i then (1 : ℂ) else 0) =
      (∏ s, (if s ∈ J then φ s.castSucc else δ s.castSucc)) * φ (Fin.last k) := by
    have h1 : (if j = tau (swapSet J) i then (1 : ℂ) else 0) =
        ∏ l, (if j l = tau (swapSet J) i l then (1 : ℂ) else 0) := by
      rw [Fintype.prod_boole]
      by_cases h : j = tau (swapSet J) i
      · rw [ite_eq_left h, ite_eq_left (fun l => congrFun h l)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (funext h'))]
    rw [h1, Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      by_cases hs : s ∈ J
      · simp only [hs, ite_true, hφ, tau, (castSucc_mem_swapSet J s).2 hs]
      · simp only [hs, ite_false, hδ, tau, mt (castSucc_mem_swapSet J s).1 hs]
    · simp only [hφ, tau, last_mem_swapSet, ite_true]
  rw [hind, prod_ite_mem_univ, Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ, Fintype.card_fin]
  simp only [hφ]
  ring

/-! ### The trace as a sum over `J` -/

lemma trace_expand (a b : V1 k d → ℂ) :
    (Oobj k d * Xf 0 a b).trace = ∑ J : Finset (Fin k), ((-1 : ℂ) ^ J.card * 2 ^ (k - J.card)) *
      ∑ i, star (patVec (famPat 0) a b i) * patVec (famPat 0) a b (tau (swapSet J) i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Xf, vecMulVec_apply, Pi.star_apply,
    Oobj_apply_expand, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

/-! ### Replicas -/

lemma patVec31 (a b : V1 k d → ℂ) (i : GI (nf k d)) :
    patVec (famPat 0) a b i = a (repl i 0) * a (repl i 1) * a (repl i 2) * b (repl i 3) := by
  simp only [patVec, Fin.prod_univ_four]
  rfl

/-- Factors of `T` taken from `v`, the others from `u`. -/
def mixV (T : Finset (Fin (k + 1))) (u v : V1 k d) : V1 k d := fun l => if l ∈ T then v l else u l

lemma repl_tau_0 (T : Finset (Fin (k + 1))) (i : GI (nf k d)) :
    repl (tau T i) 0 = mixV T (repl i 0) (repl i 3) := by
  funext l; simp only [repl, tau, mixV]; split_ifs <;> simp [pinvf21_0]

lemma repl_tau_1 (T : Finset (Fin (k + 1))) (i : GI (nf k d)) : repl (tau T i) 1 = repl i 1 := by
  funext l; simp only [repl, tau]; split_ifs <;> simp [pinvf21_1]

lemma repl_tau_2 (T : Finset (Fin (k + 1))) (i : GI (nf k d)) : repl (tau T i) 2 = repl i 2 := by
  funext l; simp only [repl, tau]; split_ifs <;> simp [pinvf21_2]

lemma repl_tau_3 (T : Finset (Fin (k + 1))) (i : GI (nf k d)) :
    repl (tau T i) 3 = mixV T (repl i 3) (repl i 0) := by
  funext l; simp only [repl, tau, mixV]; split_ifs <;> simp [pinvf21_3]

variable (k d) in
/-- Replica decomposition `GI ≃ V1⁴`. -/
def replEquiv : GI (nf k d) ≃ V1 k d × V1 k d × V1 k d × V1 k d :=
  (Equiv.piComm fun (l : Fin (k + 1)) (_ : Fin 4) => Fin (nf k d l)).trans
    { toFun := fun w => (w 0, w 1, w 2, w 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := fun w => by funext r; fin_cases r <;> rfl
      right_inv := fun p => rfl }

lemma sum_GI (f : GI (nf k d) → ℂ) :
    ∑ i, f i = ∑ u0, ∑ u1, ∑ u2, ∑ u3, f ((replEquiv k d).symm (u0, u1, u2, u3)) := by
  rw [← (replEquiv k d).symm.sum_comp]
  simp only [Fintype.sum_prod_type]

lemma repl_symm (u0 u1 u2 u3 : V1 k d) :
    repl ((replEquiv k d).symm (u0, u1, u2, u3)) 0 = u0 ∧
    repl ((replEquiv k d).symm (u0, u1, u2, u3)) 1 = u1 ∧
    repl ((replEquiv k d).symm (u0, u1, u2, u3)) 2 = u2 ∧
    repl ((replEquiv k d).symm (u0, u1, u2, u3)) 3 = u3 := ⟨rfl, rfl, rfl, rfl⟩

/-! ### Sites and auxiliary qubit -/

variable (k d) in
/-- Site/auxiliary decomposition `V1 ≃ (Fin k → Fin d) × Fin 2`. -/
def siteAuxEquiv : V1 k d ≃ (Fin k → Fin d) × Fin 2 :=
  (Fin.snocEquiv fun l => Fin (nf k d l)).symm.trans
    (((finCongr (nf_aux k d)).prodCongr (Equiv.piCongrRight fun s => finCongr (nf_site k d s))).trans
      (Equiv.prodComm _ _))

lemma siteAuxEquiv_apply (v : V1 k d) : siteAuxEquiv k d v = (sitePart v, auxPart v) := rfl

lemma sitePart_symm (x : Fin k → Fin d) (α : Fin 2) : sitePart ((siteAuxEquiv k d).symm (x, α)) = x :=
  congrArg Prod.fst ((siteAuxEquiv k d).apply_symm_apply (x, α))

lemma auxPart_symm (x : Fin k → Fin d) (α : Fin 2) : auxPart ((siteAuxEquiv k d).symm (x, α)) = α :=
  congrArg Prod.snd ((siteAuxEquiv k d).apply_symm_apply (x, α))

lemma sum_V1 (f : V1 k d → ℂ) : ∑ v, f v = ∑ x, ∑ α, f ((siteAuxEquiv k d).symm (x, α)) := by
  rw [← (siteAuxEquiv k d).symm.sum_comp, Fintype.sum_prod_type]

/-- Coordinates of `J` taken from `y`, the others from `x`. -/
def mixS (J : Finset (Fin k)) (x y : Fin k → Fin d) : Fin k → Fin d := fun s => if s ∈ J then y s else x s

lemma sitePart_mixV (J : Finset (Fin k)) (u v : V1 k d) :
    sitePart (mixV (swapSet J) u v) = mixS J (sitePart u) (sitePart v) := by
  funext s
  simp only [sitePart, mixV, mixS, castSucc_mem_swapSet]
  split_ifs <;> rfl

lemma auxPart_mixV (J : Finset (Fin k)) (u v : V1 k d) : auxPart (mixV (swapSet J) u v) = auxPart v := by
  simp only [auxPart, mixV, last_mem_swapSet, ite_true]

lemma sum_mix (J : Finset (Fin k)) (A B : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    ∑ u, ∑ v, star (vecOf A u) * star (vecOf B v) *
      (vecOf A (mixV (swapSet J) u v) * vecOf B (mixV (swapSet J) v u)) =
    ∑ x, ∑ α, ∑ y, ∑ β, star (A x α) * star (B y β) * (A (mixS J x y) β * B (mixS J y x) α) := by
  simp only [sum_V1 (k := k) (d := d), vecOf, sitePart_mixV, auxPart_mixV, sitePart_symm, auxPart_symm]

/-! ### Partial traces -/

lemma ofReal_normSq (z : ℂ) : (Complex.normSq z : ℂ) = star z * z := by
  rw [Complex.normSq_eq_conj_mul_self]; rfl

lemma nsq_complex (a : V1 k d → ℂ) : (nsq k d a : ℂ) = ∑ v, star (a v) * a v := by
  unfold nsq; push_cast; exact Finset.sum_congr rfl fun v _ => ofReal_normSq (a v)

lemma mixS_upd (J : Finset (Fin k)) (x0 y0 : Fin k → Fin d) (z z' : J → Fin d) :
    mixS J (NPT.upd J x0 z') (NPT.upd J y0 z) = NPT.upd J x0 z := by
  funext s
  by_cases hs : s ∈ J <;> simp [mixS, NPT.upd, hs]

section PTrace

variable [NeZero d]

/-- Splitting a multi-index into its part off `J` (padded by `0`) and its part on `J`. -/
lemma sum_split (J : Finset (Fin k)) (f : (Fin k → Fin d) → ℂ) :
    ∑ x, f x = ∑ x0 ∈ univ.filter (NPT.ZeroOn J), ∑ z : J → Fin d, f (NPT.upd J x0 z) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => NPT.upd J p.1 p.2)
    (fun x => (NPT.upd J x (fun _ => 0), fun s => x s.1)) ?_ ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · intro x _
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    intro i hi
    simp [NPT.upd, hi]
  · rintro ⟨x0, z⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
    refine Prod.ext ?_ ?_
    · funext i
      by_cases hi : i ∈ J
      · simp [NPT.upd, hi, hp i hi]
      · simp [NPT.upd, hi]
    · funext s
      simp [NPT.upd, s.2]
  · intro x _
    funext i
    by_cases hi : i ∈ J <;> simp [NPT.upd, hi]
  · intro p _; rfl

lemma frobSq_ptrace (J : Finset (Fin k)) (C : NPT.Op (Fin k) d) :
    (NPT.frobSq (NPT.ptrace J C) : ℂ) =
      ∑ x0 ∈ univ.filter (NPT.ZeroOn J), ∑ y0 ∈ univ.filter (NPT.ZeroOn J),
        star (∑ z : J → Fin d, C (NPT.upd J x0 z) (NPT.upd J y0 z)) *
          ∑ z : J → Fin d, C (NPT.upd J x0 z) (NPT.upd J y0 z) := by
  unfold NPT.frobSq
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : NPT.ZeroOn J x
  · rw [ite_eq_left hx, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : NPT.ZeroOn J y
    · rw [ite_eq_left hy, NPT.ptrace_apply_pos ⟨hx, hy⟩, ofReal_normSq]
    · rw [ite_eq_right hy, NPT.ptrace_apply_neg (fun h => hy h.2)]; simp
  · rw [ite_eq_right hx]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [NPT.ptrace_apply_neg (fun h => hx h.1)]; simp

/-- `Σ_{x,y,α,β} ā(x,α) b̄(y,β) a(x ◁_J y, β) b(y ◁_J x, α) = ‖Tr_J (A Bᴴ)‖²`. -/
lemma core (J : Finset (Fin k)) (A B : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    ∑ x, ∑ α, ∑ y, ∑ β, star (A x α) * star (B y β) * (A (mixS J x y) β * B (mixS J y x) α) =
      (NPT.frobSq (NPT.ptrace J (A * Bᴴ)) : ℂ) := by
  calc ∑ x, ∑ α, ∑ y, ∑ β, star (A x α) * star (B y β) * (A (mixS J x y) β * B (mixS J y x) α)
      = ∑ x, ∑ y, ∑ α, ∑ β, star (A x α) * star (B y β) * (A (mixS J x y) β * B (mixS J y x) α) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x0 ∈ univ.filter (NPT.ZeroOn J), ∑ z' : J → Fin d, ∑ y0 ∈ univ.filter (NPT.ZeroOn J),
          ∑ z : J → Fin d, ∑ α, ∑ β,
          star (A (NPT.upd J x0 z') α) * star (B (NPT.upd J y0 z) β) *
            (A (NPT.upd J x0 z) β * B (NPT.upd J y0 z') α) := by
        rw [sum_split J]
        refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun z' _ => ?_
        rw [sum_split J]
        refine Finset.sum_congr rfl fun y0 _ => Finset.sum_congr rfl fun z _ => ?_
        simp only [mixS_upd]
    _ = ∑ x0 ∈ univ.filter (NPT.ZeroOn J), ∑ y0 ∈ univ.filter (NPT.ZeroOn J),
          ∑ z' : J → Fin d, ∑ α, ∑ z : J → Fin d, ∑ β,
          star (A (NPT.upd J x0 z') α) * star (B (NPT.upd J y0 z) β) *
            (A (NPT.upd J x0 z) β * B (NPT.upd J y0 z') α) := by
        refine Finset.sum_congr rfl fun x0 _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y0 _ => Finset.sum_congr rfl fun z' _ => Finset.sum_comm
    _ = ∑ x0 ∈ univ.filter (NPT.ZeroOn J), ∑ y0 ∈ univ.filter (NPT.ZeroOn J),
          star (∑ z : J → Fin d, (A * Bᴴ) (NPT.upd J x0 z) (NPT.upd J y0 z)) *
            ∑ z : J → Fin d, (A * Bᴴ) (NPT.upd J x0 z) (NPT.upd J y0 z) := by
        refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun y0 _ => ?_
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z' _ => ?_
        rw [Matrix.mul_apply, star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        simp only [Matrix.conjTranspose_apply, star_mul', star_star]
        ring
    _ = _ := (frobSq_ptrace J (A * Bᴴ)).symm

lemma term_J (J : Finset (Fin k)) (A B : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    ∑ i, star (patVec (famPat 0) (vecOf A) (vecOf B) i) *
        patVec (famPat 0) (vecOf A) (vecOf B) (tau (swapSet J) i) =
      (nsq k d (vecOf A) : ℂ) ^ 2 * (NPT.frobSq (NPT.ptrace J (A * Bᴴ)) : ℂ) := by
  rw [← core J A B, ← sum_mix J A B, nsq_complex, sum_GI]
  simp only [patVec31, repl_tau_0, repl_tau_1, repl_tau_2, repl_tau_3, repl_symm, star_mul']
  have h : ∀ u0 u1 u2 u3 : V1 k d,
      star (vecOf A u0) * star (vecOf A u1) * star (vecOf A u2) * star (vecOf B u3) *
        (vecOf A (mixV (swapSet J) u0 u3) * vecOf A u1 * vecOf A u2 * vecOf B (mixV (swapSet J) u3 u0)) =
      (star (vecOf A u1) * vecOf A u1) * ((star (vecOf A u2) * vecOf A u2) *
        (star (vecOf A u0) * star (vecOf B u3) *
          (vecOf A (mixV (swapSet J) u0 u3) * vecOf B (mixV (swapSet J) u3 u0)))) := by
    intros; ring
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end PTrace

end Obj

/-! ### The objective identity -/

open Obj in
/-- **Objective identity.** -/
theorem obj_phys {k d : ℕ} [NeZero d] (A B : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    (Oobj k d * Xf 0 (vecOf A) (vecOf B)).trace =
      (((nsq k d (vecOf A)) ^ 2 * 2 ^ k * NPT.q (1/2) (A * Bᴴ) : ℝ) : ℂ) := by
  rw [trace_expand]
  simp only [term_J]
  unfold NPT.q
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hc : J.card ≤ k := by simpa using Finset.card_le_univ J
  have h2 : (2 : ℂ) ^ k = 2 ^ (k - J.card) * 2 ^ J.card := by rw [← pow_add, Nat.sub_add_cancel hc]
  have h3 : (-(1 / 2 : ℂ)) ^ J.card * 2 ^ J.card = (-1) ^ J.card := by rw [← mul_pow]; norm_num
  rw [h2]
  linear_combination (-(2 : ℂ) ^ (k - J.card) * (nsq k d (vecOf A) : ℂ) ^ 2 *
    (NPT.frobSq (NPT.ptrace J (A * Bᴴ)) : ℂ)) * h3

end NPT.Cert.Phys

#print axioms NPT.Cert.Phys.obj_phys
