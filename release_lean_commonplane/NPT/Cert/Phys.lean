/-
NPT.Cert.Phys — the physical side of the moment relaxation: one-replica vectors `a, b` of a rank-two
operator `C = A Bᴴ`, the four-replica pattern vectors (ep3core row patterns) and the family moment
operators `X_f = |w_f⟩⟨w_f|`, on the global index of `NPT.Cert.Glob` with factors `Fin (k+1)`
(sites `l < k` of dimension `d`, auxiliary qubit `l = k`).
-/
import NPT.Cert.Glob
import NPT.Cert.Sem
import NPT.Basic

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert.Phys

variable (k d : ℕ)

/-- One-replica index: one digit per factor. -/
abbrev V1 := (l : Fin (k + 1)) → Fin (nf k d l)

lemma nf_site (s : Fin k) : nf k d s.castSucc = d := by simp [nf]
lemma nf_aux : nf k d (Fin.last k) = 2 := by simp [nf]

variable {k d}

/-- Site digits of a one-replica index. -/
def sitePart (v : V1 k d) : Fin k → Fin d := fun s => Fin.cast (nf_site k d s) (v s.castSucc)
/-- Auxiliary digit of a one-replica index. -/
def auxPart (v : V1 k d) : Fin 2 := Fin.cast (nf_aux k d) (v (Fin.last k))

/-- The one-replica vector of a two-column matrix: `a(v) = A(sites, aux) = Σ_r |r⟩_aux ⊗ A_{·r}`. -/
def vecOf (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) : V1 k d → ℂ := fun v => A (sitePart v) (auxPart v)

/-- Replica `r` of a global index. -/
def repl (i : GI (nf k d)) (r : Fin 4) : V1 k d := fun l => i l r

/-- Letter of a pattern code: 0 = a, 1 = ā, 2 = b, 3 = b̄. -/
def chi (c : Fin 4) (a b : V1 k d → ℂ) (v : V1 k d) : ℂ :=
  match c with
  | 0 => a v
  | 1 => star (a v)
  | 2 => b v
  | 3 => star (b v)

/-- Product vector of a row pattern: `ψ(i) = Π_r χ_{pat r}(i_r)`. -/
def patVec (pat : Fin 4 → Fin 4) (a b : V1 k d → ℂ) (i : GI (nf k d)) : ℂ :=
  ∏ r, chi (pat r) a b (repl i r)

/-- Family patterns (ep3core FAMILY_LETTERS): '31' = aaab, '22' = aabb, '13' = bbba. -/
def famPat (f : ℕ) : Fin 4 → Fin 4 :=
  match f with
  | 0 => ![0, 0, 0, 2]
  | 1 => ![0, 0, 2, 2]
  | _ => ![2, 2, 2, 0]

/-- Family moment operator `X_f = |w_f⟩⟨w_f|`. -/
def Xf (f : ℕ) (a b : V1 k d → ℂ) : Matrix (GI (nf k d)) (GI (nf k d)) ℂ :=
  vecMulVec (patVec (famPat f) a b) (star (patVec (famPat f) a b))

variable (k d)

/-- Objective operator `O = ⊗_{sites} (2 I − F03) ⊗ F03^{aux}` (`F03 = V_{(3,1,2,0)}` = PERMS index 21). -/
def Oobj : Matrix (GI (nf k d)) (GI (nf k d)) ℂ :=
  kron fun l => if l.val < k then (2 : ℂ) • VG ℂ (nf k d l) 0 0 - VG ℂ (nf k d l) 0 21
    else VG ℂ (nf k d l) 0 21

/-- `‖a‖²`. -/
def nsq (a : V1 k d → ℂ) : ℝ := ∑ v, Complex.normSq (a v)

end NPT.Cert.Phys
