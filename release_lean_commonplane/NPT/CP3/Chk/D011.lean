import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D011 — B_σ relations 20..23 of variable 81

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b081_04_ok : (List.range' 20 4).all (bsigOK1 81) = true := by decide +kernel

end NPT.CP3.Chk
