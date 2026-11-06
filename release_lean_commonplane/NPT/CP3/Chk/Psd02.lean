import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Psd02 — positive semidefiniteness of blocks 275..301

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem psd02_ok : (List.range' 275 27).all psdOK = true := by decide +kernel

end NPT.CP3.Chk
