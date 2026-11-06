/-
NPT.CP3.HF — the hypothesis `hF` of `q4_commonPlane_of_linksR` for the certificate: at the physical coordinate
vector `y = yvec T A`, every active block `Σ_i y_i F_k[i]` is positive semidefinite.

D1 (`d1_block`) writes `F_k[i] = scaleK k · Dcp.coordSum (Xk k) i`. By `sum_coord` and `fsem_sound0`/`fsem_sound3`,
`Σ_i y_i Dcp.coordSum (Xk k) i = V_kᵀ H V_k`, where `H` is the Gram form of `Yp A` (cut `()`), resp. of `(Yp A)^{Γ₃}`
(cut `(3,)`; Fourier facts of `FourierD`), which is PSD by `psd_cut0`/`psd_cut3`.
-/
import NPT.CP3.D1Inst
import NPT.CP3.PsdSide

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.D1 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

lemma Vo_conjTranspose (k : ℕ) : (Vo k)ᴴ = (Vo k)ᵀ :=
  padR_conjTranspose (Vqk k) fun p u => by simp [Vqk]

/-- **`hF` for the certificate**, given the native D1 check. -/
theorem hF_of (hnat : checkRange raw 0 1331 = true) :
    ∀ A : MatA, ∀ k < 302, (∑ i ∈ range 1331, yvec T A i • crm (Sem.Fmat k i)).PosSemidef := by
  intro A k hk
  have e1 : ∑ i ∈ range 1331, yvec T A i • crm (Fmat k i) =
      scaleK k • ∑ i ∈ range 1331, yvec T A i • Dcp.coordSum (Xk k) i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [d1_block hnat hk (Finset.mem_range.1 hi), smul_comm]
  have hsym : ∀ σ : Equiv.Perm (Fin 4), ∀ i j, Yp A (permIdx σ i) (permIdx σ j) = Yp A i j :=
    fun σ i j => congrFun (congrFun (Yp_site σ A) i) j
  rw [e1, sum_coord Dcp 1331 Dcp_le (yvec T A) (Xk k)]
  by_cases hc : (ob k).cut = 0
  · have e2 := fsem_sound0 (PD 0) Dcp Dcp_cos Dcp_inj hsym (Dcp_out (Yp A)) (yvec T A) (Dcp_coord A) (oTup k)
      (Vo k)
    have e3 : ∀ v j, Xk k v j = (Vo k)ᵀ * (∑ c : Fin (Dcp.nc v),
        if Dcp.new v c = oTup k then reindexMI (Dcp.perm v c) (Dcp.WSW v j) else 0) * Vo k := by
      intro v j
      unfold Xk Hk
      rw [if_pos hc]
    simp only [e3]
    rw [← e2]
    unfold scaleK
    rw [if_pos hc, one_smul]
    exact psd_cut0 (PD_real 0) A (oTup k) (Vo k) (Vo_conjTranspose k)
  · have e2 := fsem_sound3 (phiPad Pφ) (phiPad_uniform Pφ) fourier_site fourier_aux Dcp Dcp_cos Dcp_inj (Yp_mem A)
      hsym (Dcp_out (Yp A)) (yvec T A) (Dcp_coord A) (oTup k) (Vo k)
    have e3 : ∀ v j, Xk k v j = (Vo k)ᵀ * (∑ c : Fin (Dcp.nc v), reindexMI (Dcp.perm v c)
        (phiMap (F := (PD 0).fam) (F' := (PD 1).fam) (phiPad Pφ) (fun l => oTup k (sigHat (Dcp.perm v c) l))
          (Dcp.tup v) (Dcp.WSW v j))) * Vo k := by
      intro v j
      unfold Xk Hk
      rw [if_neg hc]
    simp only [e3]
    rw [← e2]
    unfold scaleK
    rw [if_neg hc]
    have h0 : (0 : ℂ) ≤ (192 : ℂ) ^ 4 := by positivity
    exact (psd_cut3 (PD_real 1) A (oTup k) (Vo k) (Vo_conjTranspose k)).smul h0

end NPT.CP3.Inst
