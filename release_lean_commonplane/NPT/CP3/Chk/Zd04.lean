import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Zd04 — stored weighted parts of blocks 276..301

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem zd04_ok : (List.range' 276 26).all zdOK = true := by decide +kernel

end NPT.CP3.Chk
