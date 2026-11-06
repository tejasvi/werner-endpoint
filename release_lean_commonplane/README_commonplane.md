# Lean 4 formalization: the four-copy endpoint property on the common-plane sector at d = 3

This package is a Lean 4 / Mathlib formalization of the common-plane theorem (Theorem 8.1) of the accompanying paper in
local dimension 3: `q_4(1/2, C) ≥ 0` for every operator `C` on `(ℂ³)^{⊗4}` whose range and co-range lie in one
plane, where `q_4(t, C) = Σ_{J ⊆ {1,2,3,4}} (−t)^{|J|} ‖Tr_J C‖²_F`.

The numerical certificate (a degree-4 moment certificate restricted to the common-plane sector, with one certificate
for all directions in the plane) enters as Lean data modules, and every check on it is a proposition that Lean
verifies. Three groups of data checks, 68 theorems in all, are evaluated with `native_decide`, two of the groups by
compiled code built from this package's sources; every other check is evaluated by Lean's kernel (`decide +kernel`).
There is no `sorry`.

## What is proved

| Theorem | Statement |
|---|---|
| `NPT.CP3.q4_commonPlane_d3` | `0 ≤ NPT.q (1/2) (U * c * Uᴴ)` for every isometry `U : ℂ² → (ℂ³)^{⊗4}` (`Uᴴ * U = 1`) and every `2 × 2` matrix `c` |
| `NPT.CP3.q4_commonPlane_proj` | `0 ≤ NPT.q (1/2) C` for every operator `C` with `P C P = C`, `P = U Uᴴ` the projector onto a plane |

`STATEMENTS.md` gives the exact statements and the chain of theorems with their modules. `NPT.q`, `NPT.Idx` and
`NPT.Op` are the definitions of the three-copy package (module `NPT.Basic`), unchanged.

**Not formalized.** The theorem in other dimensions (the paper proves it for every `d`), the general rank-two case, and
the consequences for Werner states.

## Axioms

| Theorem | Axioms |
|---|---|
| `NPT.CP3.q4_commonPlane_d3`, `NPT.CP3.q4_commonPlane_proj` | `propext`, `Classical.choice`, `Quot.sound` and 68 `native_decide` axioms: `NPT.CP3.Chk.d2n00_ok`, `d2n01_ok`, `d2n02_ok`; `NPT.CP3.D1.nat_00`, …, `nat_63`; `NPT.CP3.D3F.d3_native` (each `._native.native_decide.ax_1`) |

The labels D0–D3 of the check groups, which also appear in the module names, are unrelated to the rows D1–D4 of Table 2
of the paper, where this package is row D4.

`AXIOMS.txt` holds the complete `#print axioms` output. Each `native_decide` axiom records that one Boolean data check
evaluated to `true` by compiled code. For the 64 D1 checks and the D3 check that code is a shared library compiled from
this package's Lean sources (`NPT.CP3.D1Core`, `NPT.CP3.D3Fast`, `NPT.CP3.Data.Types`) by Lean's compiler to C and by
`leanc -O3` to machine code, and loaded with `--load-dynlib`; for the 3 D2 checks it is Lean's own evaluator. For these
checks the trusted base therefore also includes the Lean compiler, `leanc` (the toolchain's bundled C compiler), the
shared-library loader, Lean's runtime (including GMP big-integer arithmetic) and every `@[implemented_by]`/`@[extern]`
implementation that the evaluated code uses. The final audit (`AUDIT.md`) rebuilt every module of this package and both
libraries from the sources and checked the axioms of every theorem of every module. Every build of the libraries from
these sources so far, all on the audit machine, has given byte-identical files; `AUDIT.md` gives their SHA-256. To
print the axioms of the main theorems yourself after a full build:

    lean NPT/CP3/Axioms.lean        # with LEAN_PATH as set by build_sequential.sh

## How it is proved

1. **Reduction** (`NPT/CP3/Basic.lean`). `q(H + iK) = q(H) + q(K)` for Hermitian `H, K`, so it suffices to treat
   Hermitian `C = A diag(w) Aᴴ` with `Aᴴ A = 1` and real `w`.
2. **Moment** (`NPT/CP3/Alg.lean`, `NPT/CP3/Phys.lean`). The moment of `A` averaged over site permutations and complex
   conjugation is projected (Hilbert–Schmidt) onto the algebra spanned by the site permutation operators tensored with
   all operators of the auxiliary register. The projection `Y(A)` is positive semidefinite, stays so after the partial
   transpose on replica 3, is annihilated by the Stiefel map, and the objective operator `O_w` satisfies
   `Tr(O_w Y(A)) = 3072 · q(1/2, A diag(w) Aᴴ)`.
3. **Coordinates** (`NPT/CP3/Coord.lean` … `NPT/CP3/Glue.lean`). Gram forms of `Y(A)` against integer module bases of
   the cut-`()` irreducible blocks: the bosonic range (D2) and the site stabilizers (D0) give, for each of the 175
   sorted tuples, `H_τ = Σ_j y_j W_τ S_j W_τᵀ`; this defines `y(A) ∈ ℂ^1331`.
4. **Certificate** (`NPT/CP3/SoundR.lean`, `NPT/CP3/Cert.lean`, `NPT/CP3/MainR.lean`). The identity
   `c(x) = Eᵀλ(x) + Σ_k F_k*(Z_k(x))` in the 1331 coordinates and the PSD multipliers `Z_k` (302 blocks, `L·D·Lᵀ`
   hints) are kernel checks; with PSD active blocks `Σ_i y_i F_k[i]` and vanishing equality rows `E y = 0` they give
   `q ≥ 0`.
5. **Links** (`NPT/CP3/Fsem.lean`, `NPT/CP3/HF.lean`, `NPT/CP3/D3*.lean`). The active blocks are compressions of Gram
   forms of `Y(A)` (cut `()`) and of `Y(A)^{Γ₃}` (cut `(3,)`, by a Fourier lift on each site), assembled over the orbits
   of the sorted tuples (the cosets form a transversal of the 1280 tuples with site labels below 4); D1 checks the
   certificate's `F_k[i]` against these formulas. The objective and the 146 equality rows are trace functionals of
   `Y(A)` lifted to the coordinates the same way; D3 checks the certificate's coefficients against them, and the
   equality functionals vanish because the Stiefel map annihilates `Y(A)`.

The certificate data are untrusted: they enter only through propositions that Lean checks.

## Relation to earlier packages

Every file under `NPT/` outside `NPT/CP3/` and `NPT/K4/` is byte-identical to the file of the same path in the
three-copy Lean package, `release_lean.tar.gz` in the Zenodo record of *Undistillability of Werner states from three,
four and five copies* (10.5281/zenodo.23604343).
`NPT/K4/Phys5.lean`, `Rule5.lean` and `Traces.lean` are byte-identical to the files of the same path in the four-copy
Lean package, `release_lean_k4.tar.gz` in the same record. The new material is under `NPT/CP3/`.

## Building

You need `elan` (or the toolchain itself), `git`, `python3` and a Linux x86-64 machine (the native libraries are built
with the toolchain's `leanc`; `prlimit` and `nm` are used). The toolchain `leanprover/lean4:v4.35.0` is pinned in
`lean-toolchain`, and Mathlib with its dependencies in `lake-manifest.json`. Use the sequential script:

    ./build_sequential.sh                  # every module, one at a time, then the axioms of the main theorems
    ./build_sequential.sh NPT.CP3.Final    # only the given modules and their imports

`build_sequential.sh` fetches the prebuilt Mathlib with `lake exe cache get` (network access needed), then compiles one
module at a time with `lean`, in topological import order, into `.build/lib`, building the two native libraries
(`native1/libcp3d1.so`, `native/libcp3d3.so`) when their source modules are reached. Plain `lake build` does not
build the native libraries; it would evaluate the 65 compiled checks with Lean's interpreter instead, which takes days.

**Memory and time.** Most modules build in seconds with a few GB. The heaviest are the padding bridges
`NPT/CP3/Bridge/B3.lean` and `B5.lean` (up to 55 GiB of memory and 67 GiB of address space, about 8 minutes each); the
64 D1 checks take 4–15 minutes each with about 3 GiB, the 3 D2 checks 13–15 minutes, the D3 check 8 minutes.
`build_sequential.sh` therefore needs about 60 GB of free memory (a machine with 64 GB of RAM or more) and, one module at
a time, on the order of 15 hours; the final audit built all 388 modules in 59 minutes with up to 28 modules at a time
on a 64-core machine (14.5 CPU-hours in all). See `AUDIT.md`.

## Contents

| Path | Content |
|---|---|
| `NPT/` | Lean sources: the import closure of the main theorems (`NPT/CP3/` new, the rest from earlier packages) |
| `NPT/CP3/Axioms.lean` | `#print axioms` for the main theorems |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake setup (Mathlib) |
| `build_sequential.sh`, `build_order.txt`, `scripts/` | sequential build; the modules in import order; the import-order tool and the two native-library scripts |
| `STATEMENTS.md` | the theorems of the chain with their hypotheses |
| `AXIOMS.txt` | `#print axioms` of the main theorems |
| `AUDIT.md` | summary of the final audit |
| `LICENSE` | license |
| `SHA256SUMS` | SHA-256 of every file in the package |
