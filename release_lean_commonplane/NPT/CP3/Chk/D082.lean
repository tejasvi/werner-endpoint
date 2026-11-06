import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D082 — span positions 99..131 of variable 147

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s147_03_ok : (List.range' 99 33).all (spanOK1 147) = true := by decide +kernel

end NPT.CP3.Chk
