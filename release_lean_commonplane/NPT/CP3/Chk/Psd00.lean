import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Psd00 — positive semidefiniteness of blocks 0..256

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem psd00_ok : (List.range' 0 257).all psdOK = true := by decide +kernel

end NPT.CP3.Chk
