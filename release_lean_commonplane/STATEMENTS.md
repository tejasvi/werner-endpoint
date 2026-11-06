# Lean formalization of the common-plane theorem at d = 3: what is proved

All modules build with Lean 4.35.0 and the Mathlib pinned in `lake-manifest.json`. There is no `sorry`. The main
theorems depend on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on 68 `native_decide`
axioms of data checks (`AXIOMS.txt`, and the section *Axioms* below).

## Main theorems (module `NPT.CP3.Final`)

    theorem NPT.CP3.q4_commonPlane_d3 (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
        (c : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ NPT.q (1 / 2) (U * c * Uᴴ)

    theorem NPT.CP3.q4_commonPlane_proj (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
        (C : NPT.Op (Fin 4) 3) (hC : U * Uᴴ * C * (U * Uᴴ) = C) : 0 ≤ NPT.q (1 / 2) C

## Correspondence with the paper

Theorem 8.1 of the accompanying paper reads: *let `d ≥ 2`; every common-plane operator `C` on `(ℂ^d)^{⊗4}` satisfies
`q_4(1/2, C) ≥ 0`*, where `C` is a common-plane operator if `ran C + ran C*` lies in a plane and
`q_k(t, C) = Σ_{J ⊆ {1,…,k}} (−t)^{|J|} ‖Tr_J C‖²_F`. This package proves the case `d = 3`. The definitions are those
of the three-copy package (module `NPT.Basic`), unchanged:

| paper | Lean (`NPT.Basic`) |
|---|---|
| the four copies `{1,…,4}`, a subset `J` | `Fin 4`, `J : Finset (Fin 4)` (all 16 subsets) |
| `H = (ℂ³)^{⊗4}` and its product basis | `NPT.Idx (Fin 4) 3 = Fin 4 → Fin 3` (a basis vector is a choice of digit per copy) |
| an operator `C` on `H` | `C : NPT.Op (Fin 4) 3 = Matrix (NPT.Idx (Fin 4) 3) (NPT.Idx (Fin 4) 3) ℂ` |
| the partial trace `Tr_J C` over the copies in `J` | `NPT.ptrace J C`: row and column digits on `J` replaced by the same summation index, padded by `\|0⟩⟨0\|` on `J`, so its entries are those of `Tr_J C` and zeros |
| `‖A‖²_F` | `NPT.frobSq A = Σ_{x,y} \|A x y\|²` (so `frobSq (ptrace J C) = ‖Tr_J C‖²_F`) |
| `q_4(t, C)` | `NPT.q t C = Σ_{J : Finset (Fin 4)} (−t)^{\|J\|} * frobSq (ptrace J C)` |
| `t = 1/2` | `(1 / 2 : ℝ)` |
| `C` common-plane: `ran C + ran C* ⊆ V`, `V` a plane | an isometry `U : ℂ² → H` (`Uᴴ * U = 1`) whose columns span `V`, and `C = U * c * Uᴴ` (`q4_commonPlane_d3`) or `U * Uᴴ * C * (U * Uᴴ) = C` (`q4_commonPlane_proj`) |

The two forms say exactly that `C` is a common-plane operator. If `ran C + ran C*` lies in a plane `V` (or in a smaller
subspace, extended to a plane), let the columns of `U` be an orthonormal basis of `V`; then `P = U Uᴴ` is the
orthogonal projector onto `V`, `P C = C` (range in `V`) and `C P = C` (co-range in `V`), so `P C P = C`, and
`C = U (Uᴴ C U) Uᴴ` (`NPT.CP3.eq_of_plane`). Conversely `C = U c Uᴴ` has range and co-range in `ran U`. The hypotheses
are satisfiable (for instance `U` with two standard basis vectors as columns).

## The chain

| statements | module | content |
|---|---|---|
| `q_add_I`, `herm_plane_normal`, `q_nonneg_of_stiefel`, `eq_of_plane` | `NPT.CP3.Basic` | `q(H + iK) = q(H) + q(K)` for Hermitian `H, K`; it suffices to treat `C = A diag(w) Aᴴ` with `Aᴴ A = 1` and real `w` |
| `Yp_psd`, `gam3_Yp_psd`, `stK0_Yp`, `trace_Ow_Yp_q` | `NPT.CP3.Phys` | the projected moment `Y(A)` (the site- and conjugation-averaged moment projected onto the cut-`()` algebra) is PSD, PSD after the partial transpose on replica 3, annihilated by the Stiefel map, and `Tr(O_w Y(A)) = 3072 · q(1/2, A diag(w) Aᴴ)` |
| `sound_real` | `NPT.CP3.SoundR` | the certificate inequality: the identity, symmetric PSD multipliers, PSD active blocks and vanishing equality rows give a nonnegative objective at every coordinate vector |
| `q4_commonPlane_of_linksR` | `NPT.CP3.MainR` | the theorem from the certificate facts and three link facts (`hF`, `hE`, `hobj`) at the coordinate vector `yvec T A` of `Y(A)` |
| `hcoord`, `T`, `offDisj_T`, `hcoordT` | `NPT.CP3.Assemble`, `NPT.CP3.Glue` | coordinates: the Gram form of every sorted tuple at `Y(A)` is `Σ_j y_(off+j) W S_j Wᵀ`, `y = yvec T A` (1331 coordinates) |
| `cert_ident`, `cert_zsym`, `cert_zpsd` | `NPT.CP3.Cert` | the certificate identity (1331 coordinates, 3 components) and the PSD multipliers (302 blocks), kernel checks |
| `hF_cert` | `NPT.CP3.HFCert` | `hF`: every active block `Σ_i y_i F_k[i]` is PSD (Fourier lift of the partial transpose, orbits of the tuples, and the D1 check `F_k[i] = scale_k · Fsem_k[i]`) |
| `hobj_of`, `hE_of` | `NPT.CP3.D3Link` | `hobj` with `κ = 1/(8 · 162⁴)` and `hE`, from the two D3 identities (trace lifts of the objective and of the Stiefel equality functionals) |
| `d3_obj`, `d3_E` | `NPT.CP3.ChecksD3` | the D3 identities: the objective coefficients and the 146 equality rows are the coordinate functionals |
| `q4_commonPlane_of_D1D3`, `q4_commonPlane_of_hF` | `NPT.CP3.FinalPre`, `NPT.CP3.FinalD3` | the theorem from `hF` and the two D3 identities, resp. from `hF` alone |

### `q4_commonPlane_of_linksR` (exact statement)

    theorem NPT.CP3.q4_commonPlane_of_linksR {P : PadData}
        {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
        {nV : ℕ} (T : Fin nV → TupleData P πp)
        (nC nK nE : ℕ) (mOf : ℕ → ℕ) (Fmat : (k i : ℕ) → Matrix (Fin (mOf k)) (Fin (mOf k)) ℝ)
        (Erow lam cvec : ℕ → ℕ → ℝ) (Zmat : (k : ℕ) → Matrix (Fin (2 * mOf k)) (Fin (2 * mOf k)) ℝ)
        (hident : ∀ c < 3, ∀ i < nC, cvec c i = (∑ e ∈ range nE, Erow e i * lam c e) +
          ∑ k ∈ range nK, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fmat k i u v * partH c (Zmat k) u v)
        (hFsym : ∀ k i u v, Fmat k i u v = Fmat k i v u)
        (hZt : ∀ k < nK, (Zmat k)ᵀ = Zmat k) (hZ : ∀ k < nK, (crm (Zmat k)).PosSemidef)
        (hF : ∀ A : MatA, Aᴴ * A = 1 → ∀ k < nK, (∑ i ∈ range nC, yvec T A i • crm (Fmat k i)).PosSemidef)
        (hE : ∀ A : MatA, Aᴴ * A = 1 → ∀ e < nE, ∑ i ∈ range nC, yvec T A i * (Erow e i : ℂ) = 0)
        (κ : ℝ) (hκ : 0 < κ)
        (hobj : ∀ A : MatA, Aᴴ * A = 1 → ∀ x₁ x₂ : ℝ,
          ∑ i ∈ range nC, yvec T A i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) +
            (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) = (κ : ℂ) * (Ow ![x₁, x₂] * Yp A).trace)
        (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (c : Matrix (Fin 2) (Fin 2) ℂ) :
        0 ≤ NPT.q (1 / 2) (U * c * Uᴴ)

`NPT.CP3.Inst.q4_commonPlane_of_D1D3` instantiates it with the certificate data (`nC = 1331`, `nK = 302`,
`nE = 146`, the 175 sorted tuples `T`) and discharges everything except `hF` and the two D3 identities; `hF_cert`,
`d3_obj` and `d3_E` then give `q4_commonPlane_d3`.

## Data checks

| checks | modules | mode |
|---|---|---|
| identity, PSD multipliers, data structure (`ident_ok`, `psd_ok`, `struct`, `zd`) | `NPT.CP3.Checks`, `NPT.CP3.Chk.Ident*`, `Psd*`, `Zd*`, `Struct` | kernel |
| bases, stabilizers, spans, cosets of the 150 variable blocks (`d0_ok`) | `NPT.CP3.ChecksD0`, `NPT.CP3.Chk.D*` | kernel |
| bosonic range `Σ_g ⊗ π(g) = W K` (`d2_ok`) | `NPT.CP3.ChecksD2`, `NPT.CP3.Chk.D2N*` | 3 `native_decide` |
| padding bridges, dimensions, cosets as a transversal of the 1280 tuples with site labels below 4 | `NPT.CP3.Bridge.*`, `NPT.CP3.Cosets` | kernel |
| site and auxiliary Gram forms, Fourier coefficients, objective and equality functionals on one factor | `NPT.CP3.FourierSite`, `FourierAux`, `D3Site`, `D3Aux` | kernel |
| active blocks `F_k[i]` against the semantics (D1, 1331 coordinates in 64 ranges) | `NPT.CP3.D1All`, `NPT.CP3.D1Nat.N*` | 64 `native_decide` |
| objective coefficients and equality rows (D3) | `NPT.CP3.ChecksD3`, `NPT.CP3.Chk.D3N` | 1 `native_decide` |

## Axioms

`#print axioms` of both main theorems (`AXIOMS.txt`): `propext`, `Classical.choice`, `Quot.sound` and the 68 axioms
`NPT.CP3.Chk.d2n00_ok`, `d2n01_ok`, `d2n02_ok` (D2), `NPT.CP3.D1.nat_00`, …, `nat_63` (D1) and
`NPT.CP3.D3F.d3_native` (D3), each with the suffix `._native.native_decide.ax_1`.
