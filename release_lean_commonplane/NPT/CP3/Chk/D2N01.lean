import NPT.CP3.Chk.D2Defs

/-!
# NPT.CP3.Chk.D2N01 — bosonic range of tuples 92..123

Native check (`native_decide`) of `d2OK` over generated data; see `NPT.CP3.Chk.D2Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d2n01_ok : (List.range' 92 32).all d2OK = true := by native_decide

end NPT.CP3.Chk
