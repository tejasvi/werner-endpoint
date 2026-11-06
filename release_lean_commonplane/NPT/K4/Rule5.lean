/-
NPT.K4.Rule5 — entry rules as records (five-family certificate).

`NPT.Cert.RuleOK i` and the lemmas built on it refer to row `i` of the fixed table `ruleTab` (13 rules).  The five-family
certificate uses 12 more position patterns (all with cut 8 or 12, already in `cutsUsed`).  Here a rule is a record
`RuleRec` (positions, inverse, cut, forward/backward tables, the row format of `ruleTab`), `RuleRec.OK` is the
condition of `RuleOK` for a record, and the rule lemmas (`ruleL_V`, `ruleG_VW`, `ruleG_mem`, their inverses) and block
positivity at the projected moments (`block_psdR`, as `NPT.Cert.block_psd`) are restated for records.  The proofs are
those of `RuleData` / `BlockPos` with the table accessors replaced by the record fields.
-/
import NPT.Cert.BlockPos
import NPT.Cert.SoundPrep

open Matrix BigOperators Finset NPT.Brauer NPT.Cert
open scoped ComplexOrder

namespace NPT.K4

/-- An entry rule: positions, inverse of the position map, cut, forward table `p ↦ (q, π)`, backward table
`q ↦ (p, π)`. -/
structure RuleRec where
  kp : Fin 4 → Fin (4 + 4)
  lp : Fin 4 → Fin (4 + 4)
  inv : Fin (4 + 4) → Fin (4 + 4)
  cut : ℕ
  fq : Fin 24 → Fin 24
  fπ : Fin 24 → Fin 24
  bq : Fin 24 → Fin 24
  bπ : Fin 24 → Fin 24

/-- The record of a table row in the format of `NPT.Cert.ruleTab`. -/
def recOf (row : List (List ℕ)) : RuleRec where
  kp s := Fin.ofNat (4 + 4) ((row.getD 0 []).getD s.val 0)
  lp s := Fin.ofNat (4 + 4) ((row.getD 1 []).getD s.val 0)
  inv c := Fin.ofNat (4 + 4) ((row.getD 2 []).getD c.val 0)
  cut := (row.getD 3 []).getD 0 0
  fq p := Fin.ofNat 24 ((row.getD 4 []).getD (2 * p.val) 0)
  fπ p := Fin.ofNat 24 ((row.getD 4 []).getD (2 * p.val + 1) 0)
  bq q := Fin.ofNat 24 ((row.getD 5 []).getD (2 * q.val) 0)
  bπ q := Fin.ofNat 24 ((row.getD 5 []).getD (2 * q.val + 1) 0)

/-- Validity of a rule record (the condition of `NPT.Cert.RuleOK`). -/
def RuleRec.OK (R : RuleRec) : Prop :=
  (∀ c, Fin.append R.kp R.lp (R.inv c) = c) ∧ (∀ u, R.inv (Fin.append R.kp R.lp u) = u) ∧
  (∀ p : Fin 24, ∀ s : Fin 4,
     Fin.append (aSel 0 p) (bSel 0 p) (R.inv (Fin.castAdd 4 s)) = pf (R.fπ p) (aSel R.cut (R.fq p) s) ∧
     Fin.append (aSel 0 p) (bSel 0 p) (R.inv (Fin.natAdd 4 s)) = pf (R.fπ p) (bSel R.cut (R.fq p) s)) ∧
  (∀ q : Fin 24, ∀ s : Fin 4,
     Fin.append (aSel R.cut q) (bSel R.cut q) (R.kp s) = pf (R.bπ q) (aSel 0 (R.bq q) s) ∧
     Fin.append (aSel R.cut q) (bSel R.cut q) (R.lp s) = pf (R.bπ q) (bSel 0 (R.bq q) s))

instance (R : RuleRec) : Decidable R.OK := by unfold RuleRec.OK; infer_instance

/-- The 13 verified rules, as records. -/
theorem recOf_ruleTab_ok : ∀ i : Fin 13, (recOf (ruleTab.getD i.val [])).OK := by decide +kernel

/-- Position data of a valid record. -/
def RuleRec.OK.pos {R : RuleRec} (h : R.OK) : RulePos := ⟨R.kp, R.lp, R.inv, h.1, h.2.1⟩

section Local

variable {n : ℕ}

lemma RuleRec.OK.ruleL_V {R : RuleRec} (h : R.OK) (p : Fin 24) :
    ruleL R.kp R.lp (VG ℂ n 0 p) = VG ℂ n R.cut (R.fq p) := by
  unfold VG
  rw [show ruleL R.kp R.lp = ruleL h.pos.kp h.pos.lp from rfl, h.pos.ruleL_SelOp,
    ← SelOp_reindex (permE (R.fπ p)) (aSel R.cut (R.fq p)) (bSel R.cut (R.fq p))]
  congr 1
  · funext s; exact (h.2.2.1 p s).1
  · funext s; exact (h.2.2.1 p s).2

lemma RuleRec.OK.ruleL_inv_V {R : RuleRec} (h : R.OK) (q : Fin 24) :
    ruleL h.pos.ikp h.pos.ilp (VG ℂ n R.cut q) = VG ℂ n 0 (R.bq q) := by
  unfold VG
  rw [show ruleL h.pos.ikp h.pos.ilp = ruleL h.pos.symm.kp h.pos.symm.lp from rfl,
    h.pos.symm.ruleL_SelOp, h.pos.symm_ikp, h.pos.symm_ilp,
    ← SelOp_reindex (permE (R.bπ q)) (aSel 0 (R.bq q)) (bSel 0 (R.bq q))]
  congr 1
  · funext s; exact (h.2.2.2 q s).1
  · funext s; exact (h.2.2.2 q s).2

end Local

section Global

variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ}

lemma RuleRec.OK.ruleG_VW {R : RuleRec} (h : R.OK) (w : L → Fin 24) :
    ruleG R.kp R.lp (VW nf 0 w) = VW nf R.cut (fun l => R.fq (w l)) := by
  unfold VW
  rw [ruleG_kron]
  congr 1
  funext l
  exact h.ruleL_V (w l)

lemma RuleRec.OK.ruleG_inv_VW {R : RuleRec} (h : R.OK) (w : L → Fin 24) :
    ruleG h.pos.ikp h.pos.ilp (VW nf R.cut w) = VW nf 0 (fun l => R.bq (w l)) := by
  unfold VW
  rw [ruleG_kron]
  congr 1
  funext l
  exact h.ruleL_inv_V (w l)

lemma RuleRec.OK.ruleG_mem {R : RuleRec} (h : R.OK) {Y : Matrix (GI nf) (GI nf) ℂ}
    (hY : Y ∈ spanS (nf := nf) 0) : ruleG R.kp R.lp Y ∈ spanS (nf := nf) R.cut := by
  induction hY using Submodule.span_induction with
  | mem a ha => obtain ⟨w, rfl⟩ := ha; rw [h.ruleG_VW]; exact VW_mem _ _
  | zero => exact Submodule.zero_mem _
  | add x z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c x _ h' => exact Submodule.smul_mem _ c h'

lemma RuleRec.OK.ruleG_inv_mem {R : RuleRec} (h : R.OK) {N : Matrix (GI nf) (GI nf) ℂ}
    (hN : N ∈ spanS (nf := nf) R.cut) : ruleG h.pos.ikp h.pos.ilp N ∈ spanS (nf := nf) 0 := by
  induction hN using Submodule.span_induction with
  | mem a ha => obtain ⟨w, rfl⟩ := ha; rw [h.ruleG_inv_VW]; exact VW_mem _ _
  | zero => exact Submodule.zero_mem _
  | add x z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c x _ h' => exact Submodule.smul_mem _ c h'

/-- Block operator of a multiplier type with record rules: block `(r, s)` is `ruleG_{rs}(Y_{fam r s})`. -/
def blockR {R : ℕ} (ri : Fin R → Fin R → RuleRec) (fam : Fin R → Fin R → ℕ)
    (Y : ℕ → Matrix (GI nf) (GI nf) ℂ) : Matrix (Fin R × GI nf) (Fin R × GI nf) ℂ :=
  fun a b => ruleG (ri a.1 b.1).kp (ri a.1 b.1).lp (Y (fam a.1 b.1)) a.2 b.2

lemma blockOf_blockR {R : ℕ} (ri : Fin R → Fin R → RuleRec) (fam : Fin R → Fin R → ℕ)
    (Y : ℕ → Matrix (GI nf) (GI nf) ℂ) (r s : Fin R) :
    blockOf (blockR ri fam Y) r s = ruleG (ri r s).kp (ri r s).lp (Y (fam r s)) := rfl

lemma blockR_sum {R : ℕ} (ri : Fin R → Fin R → RuleRec) (fam : Fin R → Fin R → ℕ) {ι : Type*} (s : Finset ι)
    (X : ι → ℕ → Matrix (GI nf) (GI nf) ℂ) :
    blockR ri fam (fun f => ∑ i ∈ s, X i f) = ∑ i ∈ s, blockR ri fam (X i) := by
  ext a b
  simp only [blockR, ruleG, Matrix.sum_apply]

/-- **Block positivity at the projected moments**, record rules (as `NPT.Cert.block_psd`). -/
theorem block_psdR {R : ℕ} {S : ℕ} (hS : S ∈ cutsUsed) (ri : Fin R → Fin R → RuleRec) (fam : Fin R → Fin R → ℕ)
    (hok : ∀ r s, (ri r s).OK) (hcut : ∀ r s, (ri r s).cut = S)
    {X Y : ℕ → Matrix (GI nf) (GI nf) ℂ} (hY : ∀ f, IsProj (spanS (nf := nf) 0) (X f) (Y f))
    (hX : (blockR ri fam X).PosSemidef) : (blockR ri fam Y).PosSemidef := by
  refine condexp_posSemidef (blockAlg (AS (nf := nf) S hS) R) hX ?_ ?_
  · intro r s
    rw [blockOf_blockR, mem_AS, ← hcut r s]
    exact (hok r s).ruleG_mem (hY _).1
  · intro W hW
    rw [trace_block, trace_block]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have hWrs : blockOf W r s ∈ spanS (nf := nf) (ri r s).cut := by
      rw [hcut r s]; exact (mem_AS hS).1 (hW r s)
    rw [blockOf_blockR, blockOf_blockR]
    have e := (hok r s).pos.trace_ruleG (blockOf W r s)
    rw [show (ri r s).kp = (hok r s).pos.kp from rfl, show (ri r s).lp = (hok r s).pos.lp from rfl,
      e, e, (hY _).2 _ ((hok r s).ruleG_inv_mem hWrs)]

end Global

end NPT.K4

#print axioms NPT.K4.block_psdR
#print axioms NPT.K4.recOf_ruleTab_ok
