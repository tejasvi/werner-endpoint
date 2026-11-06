import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D008 — B_σ relations 5..9 of variable 81

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b081_01_ok : (List.range' 5 5).all (bsigOK1 81) = true := by decide +kernel

end NPT.CP3.Chk
