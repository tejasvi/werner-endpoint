/-
NPT.CP3.FinalPre — the common-plane theorem at `d = 3` from the remaining data links, stated as hypotheses:
the active blocks (`hF`, from D1 and the Fourier facts) and the D3 identities of the objective and the equality rows.
Everything else (the certificate checks, the coordinates of the projected moment, the orbits, the objective and
equality semantics) is proved.
-/
import NPT.CP3.D3Link
import NPT.CP3.Cert
import NPT.CP3.MainR

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-- **The common-plane theorem from the block and D3 links.** -/
theorem q4_commonPlane_of_D1D3
    (hF : ∀ A : MatA, ∀ k < 302, (∑ i ∈ Finset.range 1331, yvec T A i • crm (Sem.Fmat k i)).PosSemidef)
    (hd3o : ∀ k < 3, ∀ v < 175, ∀ j < (vb v).S.length,
      cobjFlat k v j = 16 * 162 ^ 4 * (tN k ((vb v).off + j) : ℚ) / cDen)
    (hd3e : ∀ e < 146, ∀ v < 175, ∀ j < (vb v).S.length,
      (((Ecol.getD ((vb v).off + j) []).getD e 0 : ℤ) : ℚ) = 192 ^ 4 * cEFlat e v j)
    (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (c : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ NPT.q (1 / 2) (U * c * Uᴴ) :=
  q4_commonPlane_of_linksR T 1331 302 146 Sem.mOf Sem.Fmat Sem.Erow Sem.lam Sem.cvec Sem.Zmat
    cert_ident Sem.Fmat_symm cert_zsym cert_zpsd
    (fun A _ k hk => hF A k hk) (fun A hA e he => hE_of hd3e A hA e he)
    (1 / (8 * 162 ^ 4)) (by norm_num) (fun A _ x₁ x₂ => hobj_of hd3o A x₁ x₂) U hU c

end NPT.CP3.Inst
