/-
NPT.CP3.D3Sem — generic lemmas for the objective and the equality rows.

* `pairF_applyG_trace`: a product functional `⟨⊗F, κ(Y)⟩` of a product kernel is `Tr(kron (Gk κ F) Y)` for every `Y`.
* `ellPad fs fa`: padded local functionals (site entries `fs s la a b`, aux entries `fa la a b`, zero outside the true
  dimensions of cut `()`).
* `pairing_reindex_ellPad`: reading a Gram form through a coset permutation `σ` moves `σ` onto the site entries.
* `pairing_flat`: the pairing with a padded Gram form of tuple `v` is a flat sum over its box (digits `digL`).
-/
import NPT.CP3.Psem
import NPT.CP3.Orbits
import NPT.CP3.D3Def

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-! ### Product functionals pulled back along a product kernel -/

/-- The trace-form matrix of `X ↦ ⟨F, κ(X)⟩`: `Gk κ F a b = Σ_{x,y} F x y · κ x y b a`. -/
noncomputable def Gk {n : ℕ} (κ : LKer n 4) (F : Dig n 4 → Dig n 4 → ℂ) : Matrix (Dig n 4) (Dig n 4) ℂ :=
  fun a b => ∑ x, ∑ y, F x y * κ x y b a

/-- `⟨⊗F, κ(Y)⟩ = Tr(kron (Gk κ F) Y)` for every `Y`. -/
theorem pairF_applyG_trace (κ : (l : Fin 5) → LKer (nfC l) 4)
    (F : (l : Fin 5) → Dig (nfC l) 4 → Dig (nfC l) 4 → ℂ) (Y : Matrix GC GC ℂ) :
    EqLink.pairF (fun i j : GC => ∏ l, F l (i l) (j l)) (applyG κ Y) =
      (kron (fun l => Gk (κ l) (F l)) * Y).trace := by
  have h1 : ∀ i j : GC, ∑ i' : GC, ∑ j' : GC, ∏ l, F l (i' l) (j' l) * κ l (i' l) (j' l) (i l) (j l) =
      ∏ l, Gk (κ l) (F l) (j l) (i l) :=
    fun i j => sum_pair_prod (fun l x y => F l x y * κ l x y (i l) (j l))
  have lhs : EqLink.pairF (fun i j : GC => ∏ l, F l (i l) (j l)) (applyG κ Y) =
      ∑ i' : GC, ∑ j' : GC, ∑ i : GC, ∑ j : GC,
        (∏ l, F l (i' l) (j' l)) * ((∏ l, κ l (i' l) (j' l) (i l) (j l)) * Y i j) := by
    simp only [EqLink.pairF, applyG, Finset.mul_sum]
  have swap : ∀ f : GC → GC → GC → GC → ℂ,
      ∑ i' : GC, ∑ j' : GC, ∑ i : GC, ∑ j : GC, f i' j' i j =
        ∑ i : GC, ∑ j : GC, ∑ i' : GC, ∑ j' : GC, f i' j' i j := by
    intro f
    calc ∑ i' : GC, ∑ j' : GC, ∑ i : GC, ∑ j : GC, f i' j' i j
        = ∑ i' : GC, ∑ i : GC, ∑ j' : GC, ∑ j : GC, f i' j' i j :=
          Finset.sum_congr rfl fun i' _ => Finset.sum_comm
      _ = ∑ i : GC, ∑ i' : GC, ∑ j' : GC, ∑ j : GC, f i' j' i j := Finset.sum_comm
      _ = ∑ i : GC, ∑ i' : GC, ∑ j : GC, ∑ j' : GC, f i' j' i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => Finset.sum_comm
      _ = ∑ i : GC, ∑ j : GC, ∑ i' : GC, ∑ j' : GC, f i' j' i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have e : ∀ i j : GC, ∑ i' : GC, ∑ j' : GC,
      (∏ l, F l (i' l) (j' l)) * ((∏ l, κ l (i' l) (j' l) (i l) (j l)) * Y i j) =
        (∏ l, Gk (κ l) (F l) (j l) (i l)) * Y i j := by
    intro i j
    rw [← h1 i j, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  have rhs : (kron (fun l => Gk (κ l) (F l)) * Y).trace =
      ∑ i : GC, ∑ j : GC, (∏ l, Gk (κ l) (F l) (j l) (i l)) * Y i j := by
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply, kron]
    exact Finset.sum_comm
  rw [lhs, swap, rhs]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j

/-! ### Padded local functionals -/

/-- Padded local functionals from ℕ-indexed entries: site `s` entries `fs s la a b`, aux entries `fa la a b`; zero
outside the true dimensions of cut `()`. -/
noncomputable def ellPad (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ) (l : Fin 5) (la : Fin 5) :
    Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ :=
  fun a b => if l.val < 4 then (if a.val < sdim 0 la ∧ b.val < sdim 0 la then fs l la a b else 0)
    else (if a.val < (ablk 0 la).length ∧ b.val < (ablk 0 la).length then fa la a b else 0)

/-- Site entries read through a site permutation: site `s` takes the entries of site `σ s`. -/
def fsPerm (σ : Equiv.Perm (Fin 4)) (fs : ℕ → ℕ → ℕ → ℕ → ℂ) : ℕ → ℕ → ℕ → ℕ → ℂ :=
  fun s => if h : s < 4 then fs (σ ⟨s, h⟩).val else fs s

lemma sigHat_val_lt (σ : Equiv.Perm (Fin 4)) (m : Fin 5) (h : m.val < 4) :
    (sigHat σ m).val = (σ ⟨m.val, h⟩).val := by
  simp [sigHat, h]

lemma ellPad_sigHat (σ : Equiv.Perm (Fin 4)) (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ) (m la : Fin 5)
    (a b : Fin (dpad (sigHat σ m))) :
    ellPad fs fa (sigHat σ m) la a b =
      ellPad (fsPerm σ fs) fa m la (Fin.cast (dpad_sigHat σ m) a) (Fin.cast (dpad_sigHat σ m) b) := by
  unfold ellPad fsPerm
  by_cases hm : m.val < 4
  · have hs : (sigHat σ m).val < 4 := (sigHat_lt σ m).2 hm
    rw [if_pos hs, if_pos hm, sigHat_val_lt σ m hm, dif_pos hm]
    simp only [Fin.coe_cast]
  · have hs : ¬ (sigHat σ m).val < 4 := fun h => hm ((sigHat_lt σ m).1 h)
    rw [if_neg hs, if_neg hm]
    simp only [Fin.coe_cast]

/-- **Coset permutations move onto the functional.** -/
theorem pairing_reindex_ellPad (σ : Equiv.Perm (Fin 4)) (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ)
    (new τ : Fin 5 → Fin 5) (hnew : (fun l => new (sigHat σ l)) = τ) (G : Matrix MI MI ℂ) :
    pairing (kronR fun l => ellPad fs fa l (new l)) (reindexMI σ G) =
      pairing (kronR fun l => ellPad (fsPerm σ fs) fa l (τ l)) G := by
  unfold pairing
  refine Fintype.sum_equiv (permMIE σ) _ _ fun a => ?_
  refine Fintype.sum_equiv (permMIE σ) _ _ fun b => ?_
  show (∏ l, ellPad fs fa l (new l) (a l) (b l)) * G (permMI σ a) (permMI σ b) =
    (∏ l, ellPad (fsPerm σ fs) fa l (τ l) (permMI σ a l) (permMI σ b l)) * G (permMI σ a) (permMI σ b)
  congr 1
  rw [← Equiv.prod_comp (sigHat σ)]
  refine Finset.prod_congr rfl fun m _ => ?_
  have hn : new (sigHat σ m) = τ m := congrFun hnew m
  rw [hn]
  exact ellPad_sigHat σ fs fa m (τ m) (a (sigHat σ m)) (b (sigHat σ m))

/-! ### Flat form of a pairing with a padded Gram form -/

lemma flatPos_some {dims : Fin 5 → ℕ} {n : ℕ} (h : BoxOK dims n) {μ : MI} {t : Fin n}
    (ht : flatPos dims (n := n) μ = some t) : μ = unflat dims t := by
  unfold flatPos at ht
  by_cases hb : inBox dims μ ∧ flatTrue dims μ < n
  · rw [dif_pos hb] at ht
    cases ht
    exact (h.1 μ hb.1).2.symm
  · rw [dif_neg hb] at ht
    cases ht

lemma pairing_padRC {dims : Fin 5 → ℕ} {n : ℕ} (h : BoxOK dims n) (Z : Matrix MI MI ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ) :
    pairing Z (padRC dims G) = ∑ t : Fin n, ∑ s : Fin n, Z (unflat dims t) (unflat dims s) * G t s := by
  unfold pairing
  have e : ∀ μ : MI, ∑ ν : MI, Z μ ν * padRC dims G μ ν =
      (match flatPos dims (n := n) μ with
        | some t => ∑ s : Fin n, Z (unflat dims t) (unflat dims s) * G t s
        | none => 0) := by
    intro μ
    cases hμ : flatPos dims (n := n) μ with
    | none =>
      refine Finset.sum_eq_zero fun ν _ => ?_
      unfold padRC; rw [hμ]; simp
    | some t =>
      have e2 : ∀ ν : MI, Z μ ν * padRC dims G μ ν =
          (match flatPos dims (n := n) ν with | some s => Z (unflat dims t) (unflat dims s) * G t s | none => 0) := by
        intro ν
        cases hν : flatPos dims (n := n) ν with
        | none => unfold padRC; rw [hμ, hν]; simp
        | some s =>
          unfold padRC; rw [hμ, hν]
          simp only
          rw [← flatPos_some h hμ, ← flatPos_some h hν]
      exact (Finset.sum_congr rfl fun ν _ => e2 ν).trans (sum_MI_flat h _)
  exact (Finset.sum_congr rfl fun μ _ => e μ).trans (sum_MI_flat h _)

lemma unflat_digL (v : ℕ) (hb : BoxOK (dimsF v) (nV v)) (hd : DimsOK v) (t : Fin (nV v)) (l : Fin 5) :
    (unflat (dimsF v) t l).val = digL (vb v).dims l t ∧ (unflat (dimsF v) t l).val < dimsF v l := by
  have h2 := hb.2 t t.isLt
  refine ⟨?_, h2.1 l⟩
  have h3 := digL_flat v hb hd h2.1 l
  rw [h2.2] at h3
  exact h3.symm

lemma ellPad_site (v : ℕ) (hd : DimsOK v) (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ) (l : Fin 5)
    (hl : l.val < 4) (a b : Fin (dpad l)) (ha : a.val < dimsF v l) (hb' : b.val < dimsF v l) :
    ellPad fs fa l (tupF v l) a b = fs l ((vb v).st.getD l 0) a b := by
  have hk : sdim 0 (tupF v l) = dimsF v l := by
    unfold dimsF; rw [hd.2.2.2.1 l hl, tupF_val v hd l]; unfold tauV; rw [if_pos hl]
  have ht : (tupF v l).val = (vb v).st.getD l 0 := by rw [tupF_val v hd l]; unfold tauV; rw [if_pos hl]
  unfold ellPad
  rw [if_pos hl, hk, if_pos ⟨ha, hb'⟩, ht]

lemma ellPad_aux (v : ℕ) (hd : DimsOK v) (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ)
    (a b : Fin (dpad 4)) (ha : a.val < dimsF v 4) (hb' : b.val < dimsF v 4) :
    ellPad fs fa 4 (tupF v 4) a b = fa (vb v).ai a b := by
  have h4 : ¬ ((4 : Fin 5).val < 4) := by decide
  have hk : (ablk 0 (tupF v 4)).length = dimsF v 4 := by
    show (ablk 0 (tupF v 4)).length = (vb v).dims.getD 4 0
    rw [hd.2.2.2.2.1, tupF_val v hd 4]; unfold tauV; rw [if_neg h4]
  have ht : (tupF v 4).val = (vb v).ai := by rw [tupF_val v hd 4]; unfold tauV; rw [if_neg h4]
  unfold ellPad
  rw [if_neg h4, hk, if_pos ⟨ha, hb'⟩, ht]

/-- **The pairing with a padded Gram form of tuple `v` as a flat sum over its box.** -/
theorem pairing_flat (v : ℕ) (hb : BoxOK (dimsF v) (nV v)) (hd : DimsOK v) (fs : ℕ → ℕ → ℕ → ℕ → ℂ)
    (fa : ℕ → ℕ → ℕ → ℂ) (G : Matrix (Fin (nV v)) (Fin (nV v)) ℂ) :
    pairing (kronR fun l => ellPad fs fa l (tupF v l)) (padRC (dimsF v) (n := nV v) G) =
      ∑ a : Fin (nV v), ∑ b : Fin (nV v), G a b *
        ((∏ l ∈ Finset.range 4, fs l ((vb v).st.getD l 0) (digL (vb v).dims l a) (digL (vb v).dims l b)) *
          fa (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b)) := by
  rw [pairing_padRC hb]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]
  congr 1
  simp only [kronR]
  rw [Fin.prod_univ_castSucc, ← Fin.prod_univ_eq_prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    have hl : (Fin.castSucc l).val < 4 := l.isLt
    obtain ⟨ea, la⟩ := unflat_digL v hb hd a (Fin.castSucc l)
    obtain ⟨eb, lb⟩ := unflat_digL v hb hd b (Fin.castSucc l)
    rw [ellPad_site v hd fs fa (Fin.castSucc l) hl _ _ la lb, ea, eb]
    rfl
  · obtain ⟨ea, la⟩ := unflat_digL v hb hd a (Fin.last 4)
    obtain ⟨eb, lb⟩ := unflat_digL v hb hd b (Fin.last 4)
    exact (ellPad_aux v hd fs fa _ _ la lb).trans (by rw [ea, eb]; rfl)

end NPT.CP3.Inst
