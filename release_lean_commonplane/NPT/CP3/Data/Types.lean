/-!
# NPT.CP3.Data.Types — record types of the common-plane (d = 3) certificate data

The data are untrusted lists; every property used downstream is a proposition checked in `NPT.CP3.Chk*`.

Conventions:
* cut `c = 0` is cut `()`, `c = 1` is cut `(3,)` (operator `NPT.Brauer.VG R n S p` with mask `S = 0`, resp. `8`);
  permutations are indices into `NPT.Brauer.permL`;
* site digit strings are flat base-3 indices (`Sem.flat`, replica 0 most significant); aux strings are
  `z = Σ z_i 2^(3−i)`;
* module multi-indices are flat mixed-radix indices over `dims = [d_st0, d_st1, d_st2, d_st3, auxdim]` (`Sem.flatMI`,
  factor 0 most significant); this is the row order of every `W` and `V`;
* matrices are lists of rows; the upper triangle of a symmetric `m × m` matrix lists `(u, v)`, `u ≤ v`, in the order
  `(0,0), (0,1), …, (0,m−1), (1,1), …`;
* site Gram coordinates of cut `c`: label `l`, entry `(a, b)` at `siteOff[c][l] + a·d_l + b`; aux Gram coordinates:
  block `li`, entry `(i, j)` at `auxOff[li] + i·auxDims[li] + j`;
* coordinates `y_i`, `i < 1331`: `i = off_v + j` belongs to the basis matrix `S_j` of variable `v`; active blocks
  `k < 302` are in increasing producer output index.
-/

namespace NPT.CP3.Data

/-- A variable block: a sorted cut-`()` tuple `τ = (st, ai)` with its bosonic basis `W` (`n × m`, rows in `flatMI`
order over `dims`), the basis `S_j` of the stabilizer-invariant symmetric `m × m` matrices (coordinate `off + j`) and
the coset representatives `(new, s)`: site `q` of `st` moves to position `s[q]`, so `new[s[q]] = st[q]`. -/
structure VarB where
  st : List Nat
  ai : Nat
  dims : List Nat
  off : Nat
  W : List (List Int)
  S : List (List (List Int))
  cosets : List (List Nat × List Nat)
  deriving Inhabited

/-- Hints for the data-structure checks of a variable block: a left inverse `W⁺ = rinv / rden` supported on the rows
`piv`, the stabilizer `stab` (indices into `NPT.Brauer.permL`), `B_σ = bsig / bden` with `Π_σ W = W B_σ`, and the
coefficients `coef / cden` of the averaged symmetric units in the basis `S_j` (rows in upper-triangle order). -/
structure VarD0 where
  piv : List Nat
  rinv : List (List Int)
  rden : Nat
  stab : List Nat
  bsig : List (List (List Int))
  bden : Nat
  coef : List (List Int)
  cden : Nat
  deriving Inhabited

/-- An active output block: cut `c`, sorted cut-`c` tuple `(st, ai)`, and the `n × m` matrix `V` (rows in `flatMI`
order over `dims`). -/
structure OutB where
  idx : Nat
  cut : Nat
  st : List Nat
  ai : Nat
  dims : List Nat
  m : Nat
  V : List (List Int)
  deriving Inhabited

/-- The certificate of an active block: `Z = N Y Nᵀ` (`2m × 2m`) with `Y = Yi / 2^s + dYn / D` (`r × r`). -/
structure CertB where
  idx : Nat
  m : Nat
  r : Nat
  N : List (List Int)
  Yi : List (List Int)
  s : Nat
  dYn : List (List Int)
  deriving Inhabited

end NPT.CP3.Data
