import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Struct — shapes of the data

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem glob_ok : globOK = true := by decide +kernel
theorem blocks_ok : (List.range 302).all blockOK = true := by decide +kernel
theorem heads_ok : Fc.all (headsOK 0) = true := by decide +kernel

end NPT.CP3.Chk
