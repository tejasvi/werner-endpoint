import NPT.CP3.Chk.D2Defs

/-!
# NPT.CP3.Chk.D2N00 — bosonic range of tuples 0..91

Native check (`native_decide`) of `d2OK` over generated data; see `NPT.CP3.Chk.D2Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d2n00_ok : (List.range' 0 92).all d2OK = true := by native_decide

end NPT.CP3.Chk
