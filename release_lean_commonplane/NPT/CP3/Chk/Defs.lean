import NPT.CP3.Data.Cert
import NPT.CP3.Data.CertG
import NPT.CP3.Data.Outs
import NPT.CP3.Data.F
import NPT.CP3.Data.E
import NPT.CP3.Data.Obj
import NPT.CP3.Data.Psd
import NPT.CP3.Data.ZW
import NPT.Cert.PsdCheck

/-!
# NPT.CP3.Chk.Defs — list-level checkers of the common-plane certificate (kernel-evaluated)

With `q_k = D / 2^s_k`, `D·Y_k = q_k Yi_k + dYn_k`, so `D·Z_k = q_k (N Yi Nᵀ) + N dYn Nᵀ`. The data `zw` hold, per
active block, the weighted upper triangles of the three parts (`Z11`, `Z22`, `Z12 + Z21ᵀ`) of `N Yi Nᵀ` and of
`N dYn Nᵀ`; `zdOK k` recomputes them from the certificate. The identity at coordinate `i` (`identAt i`) then needs only
dot products with the rows of `Fc[i]`, the E column and `λ`:
`Σ_e E[e,i] lamN[c][e] + Σ_rows g_k (q_k ⟨f, wS_k,c⟩ + ⟨f, wB_k,c⟩) = (D / cDen) · tN c i`, with `g_k = fScale[cut k]`.
`psdOK k` is the `NPT.Cert.PBlock` check of the integer matrix `D·Y_k`. `structOK` collects the shapes used by the
semantic lemmas. All functions use lists and structural recursion only (for `decide +kernel`).
-/

namespace NPT.CP3.Chk

open NPT.CP3.Data NPT.Cert

/-- `Σ a_t b_t` over the common length. -/
def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- Sum of a list of integers. -/
def lsum : List Int → Int
  | [] => 0
  | a :: as => a + lsum as

/-- Entry `(u, v)` of a list matrix (0 outside). -/
def mget (A : List (List Int)) (u v : Nat) : Int := (A.getD u []).getD v 0

/-- `N X Nᵀ`, entry `(u, v) = dot(N_u, X N_v)` with `(X N_v)_t = dot(X_t, N_v)`. -/
def nxnt (N X : List (List Int)) : List (List Int) :=
  let W := N.map fun nv => X.map fun row => dot row nv
  N.map fun nu => W.map fun wv => dot nu wv

/-- Entry `(u, v)` of part `c` of a `2m × 2m` matrix: `Z11`, `Z22`, `Z12 + Z21ᵀ`. -/
def pentry (Z : List (List Int)) (m c u v : Nat) : Int :=
  match c with
  | 0 => mget Z u v
  | 1 => mget Z (m + u) (m + v)
  | _ => mget Z u (m + v) + mget Z (m + v) u

/-- The upper-triangle positions `(u, v)`, `u ≤ v < m`, in the order `(0,0), (0,1), …, (0,m−1), (1,1), …`. -/
def ups (m : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap fun u => (List.range (m - u)).map fun t => (u, u + t)

/-- Weighted entry of part `c` at an upper position: `P u u` on the diagonal, `P u v + P v u` above it. -/
def wentry (Z : List (List Int)) (m c : Nat) (q : Nat × Nat) : Int :=
  if q.1 = q.2 then pentry Z m c q.1 q.1 else pentry Z m c q.1 q.2 + pentry Z m c q.2 q.1

/-- The weighted upper triangle of part `c`, in the order of `ups m`. -/
def wup (Z : List (List Int)) (m c : Nat) : List Int := (ups m).map (wentry Z m c)

/-- The three weighted parts. -/
def wparts (Z : List (List Int)) (m : Nat) : List (List Int) := [wup Z m 0, wup Z m 1, wup Z m 2]

/-- Stored weighted parts of block `k`: `(of N Yi Nᵀ, of N dYn Nᵀ)`. -/
def zwOf (k : Nat) : List (List Int) × List (List Int) := zw.getD k ([], [])

/-- The stored weighted parts of block `k` agree with the certificate. -/
def zdOK (k : Nat) : Bool :=
  let b := certs.getD k default
  (zwOf k).1 == wparts (nxnt b.N b.Yi) b.m && (zwOf k).2 == wparts (nxnt b.N b.dYn) b.m

/-- `g_k = fScale[cut k]`. -/
def gk (k : Nat) : Int := Int.ofNat (fScale.getD (outs.getD k default).cut 1)

/-- `q_k = D / 2^s_k`. -/
def qk (k : Nat) : Int := Int.ofNat (D / 2 ^ (certs.getD k default).s)

/-- Contribution of one row `[k, f…]` of `Fc[i]` to component `c`. -/
def rowTerm (c : Nat) (row : List Int) : Int :=
  gk (row.headD 0).toNat * (qk (row.headD 0).toNat * dot row.tail ((zwOf (row.headD 0).toNat).1.getD c []) +
    dot row.tail ((zwOf (row.headD 0).toNat).2.getD c []))

/-- Integer targets: `cDen · (ca, cb, 2 cab)`. -/
def tN (c i : Nat) : Int :=
  match c with
  | 0 => caN.getD i 0
  | 1 => cbN.getD i 0
  | _ => 2 * cabN.getD i 0

/-- Left-hand side of component `c` at coordinate `i` (times `D`). -/
def lhsAt (c i : Nat) : Int := dot (Ecol.getD i []) (lamN.getD c []) + lsum ((Fc.getD i []).map (rowTerm c))

/-- The three identities at coordinate `i`. -/
def identAt (i : Nat) : Bool := (List.range 3).all fun c => decide (lhsAt c i = Int.ofNat (D / cDen) * tN c i)

/-- `D · Y = Yi · (D / 2^s) + dYn`. -/
def DYm (b : CertB) : List (List Int) :=
  List.zipWith (List.zipWith fun y e => y * Int.ofNat (D / 2 ^ b.s) + e) b.Yi b.dYn

/-- PSD hint of block `k`. -/
def hintOf (k : Nat) : Nat × List (List Int) × List Nat := psdHint.getD k default

/-- The `PBlock` of `D·Y` for block `k` (no corrections). -/
def pblockOf (k : Nat) : PBlock :=
  { n := (certs.getD k default).r, E := 0, F := (hintOf k).1, zrows := DYm (certs.getD k default),
    lrows := (hintOf k).2.1, dvals := (hintOf k).2.2, uent := [] }

/-- The PSD check of block `k` (`Lden = 1`, `UB = 2F`). -/
def psdOK (k : Nat) : Bool := (pblockOf k).check 1 (2 * (hintOf k).1)

/-- A list matrix has `r` rows of length `c`. -/
def shapeOK (A : List (List Int)) (r c : Nat) : Bool := A.length == r && A.all fun row => row.length == c

/-- Shape facts of one block `k`. -/
def blockOK (k : Nat) : Bool :=
  let b := certs.getD k default
  let o := outs.getD k default
  b.idx == o.idx && b.m == o.m && o.cut < 2 && shapeOK b.N (2 * b.m) b.r && shapeOK b.Yi b.r b.r &&
    shapeOK b.dYn b.r b.r && D % 2 ^ b.s == 0

/-- The block indices (row heads) of a coordinate are `≥ lo`, strictly increasing and `< 302`. -/
def headsOK : Nat → List (List Int) → Bool
  | _, [] => true
  | lo, row :: rows => decide (0 ≤ row.headD (-1)) && decide (lo ≤ (row.headD (-1)).toNat) &&
      decide ((row.headD (-1)).toNat < 302) && headsOK ((row.headD (-1)).toNat + 1) rows

/-- Shapes of the global lists. -/
def globOK : Bool :=
  certs.length == 302 && outs.length == 302 && psdHint.length == 302 && zw.length == 302 && Fc.length == 1331 &&
    shapeOK Ecol 1331 146 && shapeOK lamN 3 146 && erows.length == 146 && caN.length == 1331 &&
    cbN.length == 1331 && cabN.length == 1331 && D % cDen == 0 && fScale.length == 2 && 0 < D && 0 < cDen

end NPT.CP3.Chk
