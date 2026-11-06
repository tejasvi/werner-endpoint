import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Ident18 — the identities at coordinates 508..534

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem ident18_ok : (List.range' 508 27).all identAt = true := by decide +kernel

end NPT.CP3.Chk
