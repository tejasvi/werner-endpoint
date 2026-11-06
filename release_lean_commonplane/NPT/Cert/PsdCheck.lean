/-
NPT.Cert.PsdCheck — kernel-checkable positive semidefiniteness of exact certificate multipliers.

A multiplier block is `Z = Zint / 2^E + U`, where `Zint` is an integer symmetric matrix (the dyadic part of the
certificate) and `U` is the exact correction: sparse entries `num / Lden` (common denominator `Lden`), placed
symmetrically. The hint is a fixed-point `L D Lᵀ` factorization: `L` unit lower triangular scaled by `2^F` (rows
`lrows`, strictly lower part; the diagonal `2^F` is implicit) and `D ≥ 0` scaled by `2^E`. With
`R = 2^(2F) Zint - L D Lᵀ` (exact integers), the checker verifies, for every row `i`,
`R_ii - Σ_{j≠i} |R_ij| ≥ n · 2^(2F+E-UB)` and `|num| · 2^UB ≤ Lden` for every correction entry.
Then `Z = L' D' L'ᴴ + (R / 2^(2F+E) + U)` with `D' ≥ 0` and the second summand diagonally dominant, so `Z ⪰ 0`.
The checker uses lists and structural recursion only (for `decide +kernel`).
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset


open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.Cert

/-- One multiplier block with its PSD hint. -/
structure PBlock where
  n : Nat
  E : Nat
  F : Nat
  zrows : List (List Int)
  lrows : List (List Int)
  dvals : List Nat
  uent : List (Nat × Nat × Int)
  deriving Inhabited

/-- `2^k` as an integer, through `Nat.pow` (GMP in the kernel). -/
def pow2I (k : Nat) : Int := Int.ofNat (2 ^ k)

/-- `Σ_k a_k c_k b_k` over the common length. -/
def dot3 : List Int → List Int → List Int → Int
  | a :: as, c :: cs, b :: bs => a * c * b + dot3 as cs bs
  | _, _, _ => 0

namespace PBlock

variable (b : PBlock)

/-- Entry `(i, j)` of `Zint`. -/
def zget (i j : Nat) : Int := (b.zrows.getD i []).getD j 0

/-- Row `i` of `L` (scaled by `2^F`) up to the diagonal: `[L_i0, …, L_i(i-1), 2^F]`. -/
def lrow (i : Nat) : List Int := b.lrows.getD i [] ++ [pow2I b.F]

/-- Entry `(i, k)` of `L` (scaled). -/
def lget (i k : Nat) : Int := (b.lrow i).getD k 0

/-- The diagonal of `D` as integers. -/
def dlist : List Int := b.dvals.map Int.ofNat

/-- Entry `(i, j)` of `R = 2^(2F) Zint - L D Lᵀ`. -/
def rval (i j : Nat) : Int := pow2I (2 * b.F) * b.zget i j - dot3 (b.lrow i) b.dlist (b.lrow j)

/-- The dominance condition of row `i`. -/
def rowOK (UB : Nat) (i : Nat) : Bool :=
  let off : Int := ((List.range b.n).map fun j => if j = i then (0 : Int) else ((b.rval i j).natAbs : Int)).sum
  decide (off + Int.ofNat b.n * pow2I (2 * b.F + b.E - UB) ≤ b.rval i i)

/-- Correction entries: in range and bounded by `2^-UB`. -/
def uOK (Lden UB : Nat) : Bool :=
  b.uent.all fun e => decide (e.1 < b.n) && decide (e.2.1 < b.n) && decide (e.2.2.natAbs * 2 ^ UB ≤ Lden)

/-- `Zint` is symmetric. -/
def symOK : Bool :=
  (List.range b.n).all fun i => (List.range b.n).all fun j => decide (b.zget i j = b.zget j i)

/-- The rows of `L` have the right lengths. -/
def lenOK : Bool := (List.range b.n).all fun i => decide ((b.lrows.getD i []).length = i)

/-- The complete check of one block. -/
def check (Lden UB : Nat) : Bool :=
  decide (UB ≤ 2 * b.F + b.E) && b.symOK && b.lenOK && b.uOK Lden UB && (List.range b.n).all (b.rowOK UB)

/-- The correction entry at `(i, j)` (first matching entry, either orientation). -/
def ufind (i j : Nat) : Option (Nat × Nat × Int) :=
  b.uent.find? fun e => (e.1 == i && e.2.1 == j) || (e.1 == j && e.2.1 == i)

/-- The correction value at `(i, j)`. -/
def uval (Lden : Nat) (i j : Nat) : ℚ :=
  match b.ufind i j with
  | some e => (e.2.2 : ℚ) / Lden
  | none => 0

/-- The exact multiplier `Z = Zint / 2^E + U`, as a complex matrix. -/
def Zmat (Lden : Nat) : Matrix (Fin b.n) (Fin b.n) ℂ :=
  fun i j => (((b.zget i j : ℚ) / 2 ^ b.E + b.uval Lden i j : ℚ) : ℂ)

end PBlock

end NPT.Cert
