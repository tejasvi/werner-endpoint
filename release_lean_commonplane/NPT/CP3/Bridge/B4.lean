import NPT.CP3.Inst

/-! Bridge facts of the tuples 100..124 (decided by the kernel). -/

namespace NPT.CP3.Inst

theorem bridge_chunk_4 : ∀ v < 25, BridgeB (100 + v) := by decide +kernel

end NPT.CP3.Inst
