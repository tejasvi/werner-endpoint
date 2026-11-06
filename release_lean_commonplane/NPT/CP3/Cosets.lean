/-
NPT.CP3.Cosets — the cosets of the 175 sorted cut-() tuples.

Coset `c` of tuple `v` is the tuple `newT v c` (site labels `cosets[c].1`, the auxiliary label of `v`) with the site
permutation `permT v c` (`cosets[c].2`, as an element of `permL`), and `newT v c ∘ sigHat (permT v c) = tupF v`
(`cos_ok`, decided per coset). The codes of the 1280 cosets, sorted, are exactly the codes of the tuples with site
labels `< 4` (`cos_sorted`, one kernel decision), so `newT` is injective (`newT_inj`) and hits every such tuple
(`newT_cover`). The cut-() site module of label `4` is empty, so a tuple with a site label `4` has Gram form `0`
(`gram_label4`).
-/
import NPT.CP3.Glue
import Mathlib.Data.List.Sort

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-- Coset `c` of tuple `v`: new site labels and the permutation (as lists). -/
def cosE (v c : ℕ) : List ℕ × List ℕ := (vb v).cosets.getD c default

/-- Number of cosets of tuple `v`. -/
def ncos (v : ℕ) : ℕ := (vb v).cosets.length

/-- The coset permutation. -/
def permT (v c : ℕ) : Equiv.Perm (Fin 4) := permE (Fin.ofNat 24 (permL.idxOf (cosE v c).2))

/-- The new tuple of a coset. -/
def newT (v c : ℕ) : Fin 5 → Fin 5 :=
  fun l => Fin.ofNat 5 (if l.val < 4 then (cosE v c).1.getD l.val 0 else (vb v).ai)

/-- The facts of one coset (decided). -/
def CosOK1 (v c : ℕ) : Prop :=
  (∀ l : Fin 5, newT v c (sigHat (permT v c) l) = tupF v l) ∧
  (∀ m : Fin 4, (permT v c m).val = (cosE v c).2.getD m.val m.val)

instance (v c : ℕ) : Decidable (CosOK1 v c) := by unfold CosOK1; infer_instance

theorem cos_ok : ∀ v < 175, ∀ c < ncos v, CosOK1 v c := by decide +kernel

/-- Code of a tuple. -/
def codeT (τ : Fin 5 → Fin 5) : ℕ :=
  (τ 0).val + 5 * (τ 1).val + 25 * (τ 2).val + 125 * (τ 3).val + 625 * (τ 4).val

/-- The codes of all cosets. -/
def cosCodes : List ℕ := (List.range 175).flatMap fun v => (List.range (ncos v)).map fun c => codeT (newT v c)

/-- Codes of the tuples with site labels `< 4`. -/
def ValidP (n : ℕ) : Prop := n < 3125 ∧ n % 5 < 4 ∧ n / 5 % 5 < 4 ∧ n / 25 % 5 < 4 ∧ n / 125 % 5 < 4

instance : DecidablePred ValidP := fun n => by unfold ValidP; infer_instance

def validCodes : List ℕ := (List.range 3125).filter fun n => decide (ValidP n)

theorem cos_sorted : List.insertionSort (· ≤ ·) cosCodes = validCodes := by decide +kernel

lemma codeT_inj {τ τ' : Fin 5 → Fin 5} (h : codeT τ = codeT τ') : τ = τ' := by
  unfold codeT at h
  have b0 := (τ 0).isLt; have b1 := (τ 1).isLt; have b2 := (τ 2).isLt; have b3 := (τ 3).isLt
  have b4 := (τ 4).isLt; have b0' := (τ' 0).isLt; have b1' := (τ' 1).isLt; have b2' := (τ' 2).isLt
  have b3' := (τ' 3).isLt; have b4' := (τ' 4).isLt
  have e0 : (τ 0).val = (τ' 0).val := by omega
  have e1 : (τ 1).val = (τ' 1).val := by omega
  have e2 : (τ 2).val = (τ' 2).val := by omega
  have e3 : (τ 3).val = (τ' 3).val := by omega
  have e4 : (τ 4).val = (τ' 4).val := by omega
  funext l
  apply Fin.ext
  fin_cases l
  exacts [e0, e1, e2, e3, e4]

lemma cosCodes_perm : cosCodes.Perm validCodes := by
  have h := List.perm_insertionSort (· ≤ ·) cosCodes
  rw [cos_sorted] at h
  exact h.symm

lemma cosCodes_nodup : cosCodes.Nodup :=
  cosCodes_perm.nodup_iff.mpr (List.Nodup.filter _ List.nodup_range)

lemma cosCodes_mem {n : ℕ} : n ∈ cosCodes ↔ ValidP n := by
  rw [cosCodes_perm.mem_iff, validCodes, List.mem_filter, List.mem_range, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- **Every tuple with site labels `< 4` is a coset tuple.** -/
theorem newT_cover (τ : Fin 5 → Fin 5) (hτ : ∀ l : Fin 5, l.val < 4 → (τ l).val < 4) :
    ∃ v < 175, ∃ c < ncos v, newT v c = τ := by
  have hval : ValidP (codeT τ) := by
    have h0 := hτ 0 (by decide); have h1 := hτ 1 (by decide); have h2 := hτ 2 (by decide)
    have h3 := hτ 3 (by decide); have h4 := (τ 4).isLt
    have hc : codeT τ = (τ 0).val + 5 * (τ 1).val + 25 * (τ 2).val + 125 * (τ 3).val + 625 * (τ 4).val := rfl
    unfold ValidP
    rw [hc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hmem : codeT τ ∈ cosCodes := cosCodes_mem.mpr hval
  unfold cosCodes at hmem
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hmem
  obtain ⟨v, hv, c, hc, he⟩ := hmem
  exact ⟨v, hv, c, hc, codeT_inj he⟩

/-- **The coset tuples are pairwise distinct.** -/
theorem newT_inj {v v' c c' : ℕ} (hv : v < 175) (hv' : v' < 175) (hc : c < ncos v) (hc' : c' < ncos v')
    (h : newT v c = newT v' c') : v = v' ∧ c = c' := by
  have hcode : codeT (newT v c) = codeT (newT v' c') := by rw [h]
  have hn := cosCodes_nodup
  unfold cosCodes at hn
  rw [List.nodup_flatMap] at hn
  obtain ⟨hin, hpw⟩ := hn
  by_cases hvv : v = v'
  · subst hvv
    exact ⟨rfl, List.inj_on_of_nodup_map (hin v (List.mem_range.mpr hv)) (List.mem_range.mpr hc)
      (List.mem_range.mpr hc') hcode⟩
  · exfalso
    have : Std.Symm (Function.onFun List.Disjoint fun v => (List.range (ncos v)).map fun c => codeT (newT v c)) :=
      ⟨fun _ _ h => List.Disjoint.symm h⟩
    have hd := hpw.forall (List.mem_range.mpr hv) (List.mem_range.mpr hv') hvv
    have m1 : codeT (newT v c) ∈ (List.range (ncos v)).map (fun c => codeT (newT v c)) :=
      List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩
    have m2 : codeT (newT v c) ∈ (List.range (ncos v')).map (fun c => codeT (newT v' c)) := by
      rw [hcode]; exact List.mem_map.mpr ⟨c', List.mem_range.mpr hc', rfl⟩
    exact hd m1 m2

/-! ### Tuples with a site label `4` -/

lemma PD_M_site4 {l : Fin 5} (hl : l.val < 4) : (PD 0).M l 4 = 0 := by
  ext x a
  rw [Matrix.zero_apply]
  have hM : (PD 0).M l 4 x a = MsC 0 4 (Fin.cast (nfC_site hl) ∘ x) (Fin.cast (dpad_site hl) a) := dif_pos hl
  rw [hM]
  have h0 : sdim 0 ((4 : Fin 5) : ℕ) = 0 := sdim4
  exact if_neg (by rw [h0]; exact Nat.not_lt_zero _)

lemma Jt_eq_zero_of {τ : Tup (PD 0).fam} (l : Fin 5) (h : (PD 0).M l (τ l) = 0) : Jt (PD 0).fam τ = 0 := by
  ext i j
  simp only [Jt, kronR, Matrix.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [h, Matrix.zero_apply])

/-- **A tuple with a site label `4` has Gram form `0`.** -/
theorem gram_label4 {τ : Tup (PD 0).fam} {l : Fin 5} (hl : l.val < 4) (h4 : τ l = 4) (Y : Matrix GC GC ℂ) :
    gram (PD 0).fam τ Y = 0 := by
  unfold gram
  rw [Jt_eq_zero_of l (by rw [h4]; exact PD_M_site4 hl), Matrix.mul_zero]

/-- **A tuple that is no coset tuple has Gram form `0`.** -/
theorem gram_out (τ : Tup (PD 0).fam) (h : ∀ v < 175, ∀ c < ncos v, newT v c ≠ τ) (Y : Matrix GC GC ℂ) :
    gram (PD 0).fam τ Y = 0 := by
  by_cases hτ : ∀ l : Fin 5, l.val < 4 → (τ l).val < 4
  · obtain ⟨v, hv, c, hc, he⟩ := newT_cover τ hτ
    exact absurd he (h v hv c hc)
  · push_neg at hτ
    obtain ⟨l, hl, h4⟩ := hτ
    have hlt : (τ l).val < 5 := (τ l).isLt
    exact gram_label4 hl (Fin.ext (show (τ l).val = 4 by omega)) Y

/-- The coset tuples, indexed by the cosets of all tuples, are pairwise distinct. -/
theorem newSig_inj : Function.Injective (fun x : (Σ v : Fin 175, Fin (ncos v)) => newT x.1 x.2) := by
  rintro ⟨v, c⟩ ⟨v', c'⟩ h
  obtain ⟨hv, hc⟩ := newT_inj v.isLt v'.isLt c.isLt c'.isLt h
  have hv' : v = v' := Fin.ext hv
  subst hv'
  have hc' : c = c' := Fin.ext hc
  subst hc'
  rfl

end NPT.CP3.Inst
