import NPT.CP3.Chk.Defs

/-!
# NPT.CP3.Chk.Ident50 — the identities at coordinates 1308..1330

Kernel check (`decide +kernel`) over the generated data; see `NPT.CP3.Chk.Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem ident50_ok : (List.range' 1308 23).all identAt = true := by decide +kernel

end NPT.CP3.Chk
