/-
NPT.Cert.BrauerTab — the 24 permutations of four replicas (ep3core `PERMS`, itertools order), their
partially transposed operators `VG S p` for a cut `S ⊆ Fin 4` (bit mask), and the closure of
`span {VG S p}` under products, generic in the local dimension `n`:
`VG S p * VG S q = n ^ e • VG S r`, with `(r, e)` computed and certified (`GCert`) by `decide +kernel`.
-/
import NPT.Cert.Brauer

open Matrix BigOperators Finset

namespace NPT.Brauer

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- ep3core `PERMS = itertools.permutations(range(4))`; entry `j` of permutation `i` is its image `p[j]`. -/
def permL : List (List ℕ) :=
  [[0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],
   [1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],
   [2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],
   [3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0]]

/-- Permutation number `i` as a function. -/
def pf (i : Fin 24) (j : Fin 4) : Fin 4 := Fin.ofNat 4 ((permL.getD i.val []).getD j.val 0)

/-- Its inverse as a function. -/
def pinvf (i : Fin 24) (j : Fin 4) : Fin 4 := Fin.ofNat 4 ((permL.getD i.val []).idxOf j.val)

/-- Index of the inverse permutation. -/
def pinvIdx (i : Fin 24) : Fin 24 :=
  Fin.ofNat 24 (permL.idxOf ((List.range 4).map fun j => (permL.getD i.val []).idxOf j))

lemma pf_pinvf : ∀ i : Fin 24, ∀ j, pf i (pinvf i j) = j := by decide +kernel
lemma pinvf_pf : ∀ i : Fin 24, ∀ j, pinvf i (pf i j) = j := by decide +kernel
lemma pinvf_pinvIdx : ∀ i : Fin 24, ∀ j, pinvf (pinvIdx i) j = pf i j := by decide +kernel

/-- Permutation number `i` as an `Equiv.Perm`. -/
def permE (i : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := pf i
  invFun := pinvf i
  left_inv j := pinvf_pf i j
  right_inv j := pf_pinvf i j

/-- Membership in the cut `S` (bit mask). -/
def inS (S : ℕ) (s : Fin 4) : Bool := S.testBit s.val

/-- Row selector of `V_p^{Γ_S}`: `s ↦ s` on the cut, `p⁻¹ s` off the cut. -/
def aSel (S : ℕ) (p : Fin 24) (s : Fin 4) : Fin 4 := if inS S s then s else pinvf p s
/-- Column selector of `V_p^{Γ_S}`. -/
def bSel (S : ℕ) (p : Fin 24) (s : Fin 4) : Fin 4 := if inS S s then pinvf p s else s

/-- The partially transposed permutation operator `V_p^{Γ_S}` (for `S = 0`: `V_p`, ep3core `perm_op`). -/
def VG (R : Type*) [CommSemiring R] (n : ℕ) (S : ℕ) (p : Fin 24) :
    Matrix (Dig n 4) (Dig n 4) R :=
  SelOp R n (aSel S p) (bSel S p)

/-! ### Product certificates from data

The certificate of the product `VG S p * VG S q` is stored as 32 natural numbers
`[r, e, σ_0..σ_7, τ_0..τ_5, par_0..par_7, dep_0..dep_7]` (variables `0..3`: left factor, `4..7`: right
factor; `σ` codes `t < 4` for result digit `t`, `4 + j` for loop `j`; `τ` padded to 6 entries).
The data are untrusted: every condition is checked by the kernel. -/

/-- Data table type: `D p q` is the 32-entry row of the pair `(p, q)`. -/
abbrev PTab := List (List (List ℕ))

def pget (D : PTab) (p q : Fin 24) (j : ℕ) : ℕ := ((D.getD p.val []).getD q.val []).getD j 0

section Fields

variable (S : ℕ) (D : PTab) (p q : Fin 24)

/-- Result word of the product. -/
def rD : Fin 24 := Fin.ofNat 24 (pget D p q 0)
/-- Number of free loops of the product. -/
def eD : ℕ := pget D p q 1

def Eg : Fin 4 → Fin (4 + 4) × Fin (4 + 4) :=
  fun s => (Fin.castAdd 4 (bSel S p s), Fin.natAdd 4 (aSel S q s))

def σd (v : Fin (4 + 4)) : Fin 4 ⊕ Fin (eD D p q) :=
  let c := pget D p q (2 + v.val)
  if h : c < 4 then Sum.inl ⟨c, h⟩ else
    if h' : c - 4 < eD D p q then Sum.inr ⟨c - 4, h'⟩ else Sum.inl 0

def τd : Fin 4 ⊕ Fin (eD D p q) → Fin (4 + 4) :=
  Sum.elim (fun t => Fin.ofNat (4 + 4) (pget D p q (10 + t.val)))
    (fun j => Fin.ofNat (4 + 4) (pget D p q (14 + j.val)))

def pard (v : Fin (4 + 4)) : Fin (4 + 4) := Fin.ofNat (4 + 4) (pget D p q (16 + v.val))

def depd (v : Fin (4 + 4)) : ℕ := pget D p q (24 + v.val)

/-- All certificate conditions, as a decidable proposition over small `Fin` types. -/
def PCertOK : Prop :=
  (∀ i : Fin 4, σd D p q (Eg S p q i).1 = σd D p q (Eg S p q i).2) ∧
  (∀ t : Fin 4, σd D p q (τd D p q (Sum.inl t)) = Sum.inl t) ∧
  (∀ j : Fin (eD D p q), σd D p q (τd D p q (Sum.inr j)) = Sum.inr j) ∧
  (∀ s : Fin 4, σd D p q (Fin.castAdd 4 (aSel S p s)) = Sum.inl (aSel S (rD D p q) s)) ∧
  (∀ s : Fin 4, σd D p q (Fin.natAdd 4 (bSel S q s)) = Sum.inl (bSel S (rD D p q) s)) ∧
  (∀ v : Fin (4 + 4), v = τd D p q (σd D p q v) ∨
    (depd D p q (pard D p q v) < depd D p q v ∧ σd D p q (pard D p q v) = σd D p q v ∧
      ∃ i : Fin 4, (v = (Eg S p q i).1 ∧ pard D p q v = (Eg S p q i).2) ∨
        (v = (Eg S p q i).2 ∧ pard D p q v = (Eg S p q i).1)))

instance : Decidable (PCertOK S D p q) := by unfold PCertOK; infer_instance

/-- The certificate built from a successful check. -/
def pcert (h : PCertOK S D p q) :
    GCert (Eg S p q) (Fin.castAdd 4 ∘ aSel S p) (Fin.natAdd 4 ∘ bSel S q)
      (aSel S (rD D p q)) (bSel S (rD D p q)) (eD D p q) where
  σ := σd D p q
  τ := τd D p q
  par := pard D p q
  dep := depd D p q
  hA := h.1
  hB := by
    rintro (t | j)
    · exact h.2.1 t
    · exact h.2.2.1 j
  hC1 := h.2.2.2.1
  hC2 := h.2.2.2.2.1
  hD := h.2.2.2.2.2

end Fields

/-- Product rule for a certified pair. -/
theorem VG_mul_of_ok {S : ℕ} {D : PTab} {p q : Fin 24} (h : PCertOK S D p q) :
    VG R n S p * VG R n S q = ((n : R) ^ eD D p q) • VG R n S (rD D p q) :=
  SelOp_mul_of_gcert (pcert S D p q h)

end NPT.Brauer
