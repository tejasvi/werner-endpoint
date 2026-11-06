import NPT.CP3.Inst

/-! Bridge facts of the tuples 25..49 (decided by the kernel). -/

namespace NPT.CP3.Inst

theorem bridge_chunk_1 : ∀ v < 25, BridgeB (25 + v) := by decide +kernel

end NPT.CP3.Inst
