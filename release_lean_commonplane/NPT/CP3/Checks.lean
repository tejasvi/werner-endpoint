import NPT.CP3.Chk.All
import NPT.CP3.Sem

/-!
# NPT.CP3.Checks — the certificate facts used by the soundness proof

* `psd_ok`: every `Y_k = Yi_k / 2^s_k + dYn_k / D` (`k < 302`) is positive semidefinite;
* `ident_ok`: for `c < 3` and every coordinate `i < 1331`,
  `cvec c i = Σ_{e<146} Erow e i · lam c e + Σ_{k<302} Σ_{u,v} Fmat k i u v · part c (Zmat k) u v`
  with `Zmat k = N_k Y_k N_kᵀ` and `cvec = (ca, cb, 2 cab)`.

Both follow from the kernel checks in `NPT.CP3.Chk.*` (no native code) through `NPT.CP3.Sem`.
-/

namespace NPT.CP3

open NPT.CP3.Sem NPT.CP3.Chk Finset

theorem psd_ok : ∀ k < 302, (Ymat k).PosSemidef := psd_of_checks blocks_all psd_all

theorem ident_ok : ∀ c < 3, ∀ i < 1331, cvec c i = (∑ e ∈ range 146, Erow e i * lam c e) +
    ∑ k ∈ range 302, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fmat k i u v * part c (Zmat k) u v :=
  ident_of_checks glob_ok blocks_all heads_all zd_all ident_all

end NPT.CP3
