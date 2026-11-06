import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Ident11 — the identities at coordinates 341..361

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem ident11_ok : (List.range' 341 21).all identAt = true := by decide +kernel

end NPT.CP3.Chk
