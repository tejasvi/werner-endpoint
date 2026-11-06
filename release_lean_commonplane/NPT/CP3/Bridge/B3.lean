import NPT.CP3.Inst

/-! Bridge facts of the tuples 75..99 (decided by the kernel). -/

namespace NPT.CP3.Inst

theorem bridge_chunk_3 : ∀ v < 25, BridgeB (75 + v) := by decide +kernel

end NPT.CP3.Inst
