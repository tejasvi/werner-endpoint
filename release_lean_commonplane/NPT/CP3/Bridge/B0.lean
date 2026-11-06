import NPT.CP3.Inst

/-! Bridge facts of the tuples 0..24 (decided by the kernel). -/

namespace NPT.CP3.Inst

theorem bridge_chunk_0 : ∀ v < 25, BridgeB (0 + v) := by decide +kernel

end NPT.CP3.Inst
