/-
NPT.CP3.Final — **EP_4(1/2) on the common-plane sector at d = 3.**

`q_4(1/2, C) ≥ 0` for every operator `C` on `(ℂ³)^{⊗4}` whose range and corange lie in a plane: `C = U c Uᴴ` for an
isometry `U : ℂ² → (ℂ³)^{⊗4}` and any `2 × 2` matrix `c` (`q4_commonPlane_d3`), equivalently `P C P = C` for the
projector `P = U Uᴴ` onto the plane (`q4_commonPlane_proj`).
-/
import NPT.CP3.FinalD3
import NPT.CP3.HFCert

open Matrix

namespace NPT.CP3

/-- **The common-plane theorem** (`d = 3`, four copies, `t = 1/2`), isometry form. -/
theorem q4_commonPlane_d3 (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (c : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ NPT.q (1 / 2) (U * c * Uᴴ) :=
  Inst.q4_commonPlane_of_hF Inst.hF_cert U hU c

/-- **The common-plane theorem**, projector form: `P C P = C` for the projector `P = U Uᴴ` onto a plane. -/
theorem q4_commonPlane_proj (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (C : NPT.Op (Fin 4) 3)
    (hC : U * Uᴴ * C * (U * Uᴴ) = C) : 0 ≤ NPT.q (1 / 2) C := by
  rw [eq_of_plane U C hC]
  exact q4_commonPlane_d3 U hU (Uᴴ * C * U)

end NPT.CP3
