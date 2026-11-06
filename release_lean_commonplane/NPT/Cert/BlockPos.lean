/-
NPT.Cert.BlockPos — positivity of the multiplier blocks at the projected moments.

For a multiplier type with rows `r < R`, entry rules `ri r s` (all with the same cut `S`) and entry
families `fam r s`, the block operator `M(Y)` has blocks `ruleG_{rs}(Y_{fam r s})`. If `Y_f` is the
Hilbert–Schmidt projection of `X_f` onto the word algebra `span {V_w}` and `M(X)` is PSD, then `M(Y)` is
PSD (Lemma P on the block algebra over the walled-Brauer algebra `A_S`, with the rule maps as
Hilbert–Schmidt unitaries). At physical moments `M(X)` is a Gram matrix whenever the rules are consistent
with the row patterns (`phys_rule`).
-/
import NPT.Cert.RuleData
import NPT.Cert.Phys

open Matrix BigOperators Finset NPT.Brauer
open scoped ComplexOrder

namespace NPT.Cert

section Gen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_block {R : ℕ} (M N : Matrix (Fin R × ι) (Fin R × ι) ℂ) :
    (Mᴴ * N).trace = ∑ r, ∑ s, ((blockOf M r s)ᴴ * blockOf N r s).trace := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, blockOf, Fintype.sum_prod_type]
  conv_lhs => enter [2, s]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Gen

section Block

variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ}

/-- Block operator of a multiplier type: block `(r, s)` is `ruleG_{rs}(Y_{fam r s})`. -/
def blockM {R : ℕ} (ri : Fin R → Fin R → ℕ) (fam : Fin R → Fin R → ℕ)
    (Y : ℕ → Matrix (GI nf) (GI nf) ℂ) : Matrix (Fin R × GI nf) (Fin R × GI nf) ℂ :=
  fun a b => ruleG (rkp (ri a.1 b.1)) (rlp (ri a.1 b.1)) (Y (fam a.1 b.1)) a.2 b.2

lemma blockOf_blockM {R : ℕ} (ri : Fin R → Fin R → ℕ) (fam : Fin R → Fin R → ℕ)
    (Y : ℕ → Matrix (GI nf) (GI nf) ℂ) (r s : Fin R) :
    blockOf (blockM ri fam Y) r s = ruleG (rkp (ri r s)) (rlp (ri r s)) (Y (fam r s)) := rfl

/-- **Block positivity at the projected moments.** -/
theorem block_psd {R : ℕ} {S : ℕ} (hS : S ∈ cutsUsed) (ri : Fin R → Fin R → ℕ) (fam : Fin R → Fin R → ℕ)
    (hok : ∀ r s, RuleOK (ri r s)) (hcut : ∀ r s, rcut (ri r s) = S)
    {X Y : ℕ → Matrix (GI nf) (GI nf) ℂ} (hY : ∀ f, IsProj (spanS (nf := nf) 0) (X f) (Y f))
    (hX : (blockM ri fam X).PosSemidef) : (blockM ri fam Y).PosSemidef := by
  refine condexp_posSemidef (blockAlg (AS (nf := nf) S hS) R) hX ?_ ?_
  · intro r s
    rw [blockOf_blockM, mem_AS, ← hcut r s]
    exact (hok r s).ruleG_mem (hY _).1
  · intro W hW
    rw [trace_block, trace_block]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have hWrs : blockOf W r s ∈ spanS (nf := nf) (rcut (ri r s)) := by
      rw [hcut r s]; exact (mem_AS hS).1 (hW r s)
    rw [blockOf_blockM, blockOf_blockM]
    have e := (hok r s).pos.trace_ruleG (blockOf W r s)
    rw [show rkp (ri r s) = (hok r s).pos.kp from rfl, show rlp (ri r s) = (hok r s).pos.lp from rfl,
      e, e, (hY _).2 _ ((hok r s).ruleG_inv_mem hWrs)]

end Block

/-! ### Physical blocks are Gram matrices -/

namespace Phys

open NPT.Cert.Sem

variable {k d : ℕ}

/-- The one-replica vector at position `c` of an index pair `(i, j)`. -/
def posV (i j : GI (nf k d)) (c : Fin (4 + 4)) : V1 k d := fun x => Fin.append (i x) (j x) c

/-- Conjugate code: `a ↔ ā`, `b ↔ b̄`. -/
def conjCode (c : Fin 4) : Fin 4 := ![1, 0, 3, 2] c

lemma chi_conjCode (c : Fin 4) (a b : V1 k d → ℂ) (v : V1 k d) :
    chi (conjCode c) a b v = star (chi c a b v) := by
  fin_cases c <;> simp [conjCode, chi]

/-- Source codes of a family entry: positions `u < 4` read `X_f`'s row (letter `f_u`), positions `4 + u`
its column (conjugated letter). -/
def srcCode (f : ℕ) (u : Fin (4 + 4)) : Fin 4 :=
  Fin.append (famPat f) (fun r => conjCode (famPat f r)) u

/-- Target codes of an entry `(r, s)`: row pattern on the i-slots, conjugated column pattern on the j-slots. -/
def tgtCode (pr ps : Fin 4 → Fin 4) (c : Fin (4 + 4)) : Fin 4 :=
  Fin.append pr (fun t => conjCode (ps t)) c

/-- Consistency of an entry rule with the family and the row patterns (decidable). -/
def Consistent (f : ℕ) (pr ps : Fin 4 → Fin 4) (kp lp : Fin 4 → Fin (4 + 4)) : Prop :=
  ∀ u, srcCode f u = tgtCode pr ps (Fin.append kp lp u)

instance (f : ℕ) (pr ps : Fin 4 → Fin 4) (kp lp : Fin 4 → Fin (4 + 4)) :
    Decidable (Consistent f pr ps kp lp) := by unfold Consistent; infer_instance

lemma prod_eight {f g : Fin 4 → ℂ} :
    (∏ r, f r) * ∏ r, g r = ∏ u : Fin (4 + 4), Fin.append f g u := by
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Physical entry.** A consistent rule maps the family moment `X_f` to `|ψ_r⟩⟨ψ_s|`. -/
theorem phys_rule (P : RulePos) {f : ℕ} {pr ps : Fin 4 → Fin 4}
    (hc : Consistent f pr ps P.kp P.lp) (a b : V1 k d → ℂ) :
    ruleG P.kp P.lp (Xf f a b) = vecMulVec (patVec pr a b) (star (patVec ps a b)) := by
  ext i j
  simp only [ruleG, Xf, vecMulVec_apply, Pi.star_apply, patVec, star_prod]
  -- source side: an eight-fold product over the source positions
  have hsrc : (∏ r, chi (famPat f r) a b (repl (fun x => Fin.append (i x) (j x) ∘ P.kp) r)) *
      ∏ r, star (chi (famPat f r) a b (repl (fun x => Fin.append (i x) (j x) ∘ P.lp) r)) =
      ∏ u : Fin (4 + 4), chi (srcCode f u) a b (posV i j (Fin.append P.kp P.lp u)) := by
    rw [prod_eight]
    refine Finset.prod_congr rfl fun u _ => ?_
    refine Fin.addCases (fun r => ?_) (fun r => ?_) u
    · rw [Fin.append_left, srcCode, Fin.append_left, Fin.append_left]; rfl
    · rw [Fin.append_right, srcCode, Fin.append_right, Fin.append_right, chi_conjCode]; rfl
  have htgt : (∏ r, chi (pr r) a b (repl i r)) * ∏ r, star (chi (ps r) a b (repl j r)) =
      ∏ c : Fin (4 + 4), chi (tgtCode pr ps c) a b (posV i j c) := by
    rw [prod_eight]
    refine Finset.prod_congr rfl fun c _ => ?_
    refine Fin.addCases (fun r => ?_) (fun r => ?_) c
    · rw [Fin.append_left, tgtCode, Fin.append_left]
      congr 1
      funext x; simp only [posV, repl, Fin.append_left]
    · rw [Fin.append_right, tgtCode, Fin.append_right, chi_conjCode]
      congr 2
      funext x; simp only [posV, repl, Fin.append_right]
  rw [hsrc, htgt]
  -- reindex by the position bijection
  refine Fintype.prod_equiv ⟨Fin.append P.kp P.lp, P.inv, P.h2, P.h1⟩ _ _ fun u => ?_
  simp only [Equiv.coe_fn_mk]
  rw [hc u]

end Phys

end NPT.Cert
