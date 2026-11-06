import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D088 — B_σ relations 17..23 of variable 148

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b148_01_ok : (List.range' 17 7).all (bsigOK1 148) = true := by decide +kernel

end NPT.CP3.Chk
