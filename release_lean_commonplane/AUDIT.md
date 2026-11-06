# Final audit

The final audit rebuilt this package from an empty build directory, rebuilt both native libraries from the package's
sources, and checked the axioms of every theorem. It used Lean 4.35.0 (commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (build hash
`359c60f733ecd8b8`), as pinned in `lean-toolchain` and `lake-manifest.json`.

- **Sources.** The audit worked on a fresh copy of the source tree with no links to any other build tree, and it hashed
  every source file before the build. Every Lean file of this package has the audited SHA-256.
- **Build.** All 388 modules were built in topological import order (`build_order.txt`), up to 28 at a time, on a
  64-core x86-64 machine with 512 GB of RAM. Each Lean process ran in its own memory-limited control group and under an
  address-space limit, with `maxHeartbeats 400000` and `Elab.async false`; the address-space limits of the running
  modules summed to at most 420 GiB. The build took 59 minutes of wall time and 14.5 CPU-hours. Every module got a
  fresh `.olean`, and no module build exited with an error.
- **Resources.** The largest modules were `NPT.CP3.Bridge.B5` (55.2 GiB RSS, 66.6 GiB address space, 463 s),
  `NPT.CP3.Bridge.B3` (50.6 GiB RSS, 58.6 GiB address space, 421 s) and `NPT.CP3.Chk.Zd00` (27.5 GiB RSS, 38.2 GiB
  address space, 185 s). Each of the 64 D1 checks took 4–15 minutes with at most 3.1 GiB RSS and 9.7 GiB of address
  space, each of the 3 D2 checks 13–15 minutes with 3.1 GiB RSS and 11.2 GiB of address space, and the D3 check
  8 minutes with 1.6 GiB RSS and 7.5 GiB of address space.
- **Native libraries.** In the audit tree, `scripts/d1lib.sh` and `scripts/d3lib.sh` built `native1/libcp3d1.so` (SHA-256
  `63dc851f57ce7820f01e96f1e44b87202215d8eb50452a0c836adf43575914af`) and `native/libcp3d3.so` (SHA-256
  `a0f325b0cedfc955472c4a8efa922ffffb053f448959e52211cfc07957357417`) from the package's sources, as
  `build_sequential.sh` does. The 64 D1 check modules and the D3 check module were compiled with `--load-dynlib` of
  these libraries.
- **Axioms.** The audit printed the axioms of the main theorems, with output identical to `AXIOMS.txt`, and of every
  theorem of `NPT.CP3.Final`, `NPT.CP3.FinalD3` and `NPT.CP3.FinalPre`, and it checked the axioms of every theorem of
  every `NPT.*` module of the package, 1900 theorems in all. Of these, 154 use an axiom
  besides `propext`, `Classical.choice` and `Quot.sound`, and each such axiom is one of the 68 `native_decide` axioms of
  the data checks: `NPT.CP3.Chk.d2n00_ok`, `d2n01_ok`, `d2n02_ok`, `NPT.CP3.D1.nat_00`, …, `nat_63` and
  `NPT.CP3.D3F.d3_native`, each with the suffix `._native.native_decide.ax_1`. The main theorems
  `NPT.CP3.q4_commonPlane_d3` and `NPT.CP3.q4_commonPlane_proj` depend on the three standard axioms and on all 68 of
  these axioms.
- **Text scan.** The 388 source files of the import order contain no `sorry`, no `admit`, no axiom declaration, no
  `unsafe`, no `implemented_by` and no `extern`. `native_decide` is used as a tactic in exactly the 68 check modules
  `NPT/CP3/D1Nat/N00.lean`, …, `N63.lean`, `NPT/CP3/Chk/D2N00.lean`, …, `D2N02.lean` and `NPT/CP3/Chk/D3N.lean`;
  elsewhere the word occurs only in one comment, in `NPT/CP3/D3Core.lean`.
