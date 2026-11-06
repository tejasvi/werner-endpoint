import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Psd01 — positive semidefiniteness of blocks 257..274

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem psd01_ok : (List.range' 257 18).all psdOK = true := by decide +kernel

end NPT.CP3.Chk
