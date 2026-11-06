import NPT.CP3.Inst

/-! Bridge facts of the tuples 150..174 (decided by the kernel). -/

namespace NPT.CP3.Inst

theorem bridge_chunk_6 : ∀ v < 25, BridgeB (150 + v) := by decide +kernel

end NPT.CP3.Inst
