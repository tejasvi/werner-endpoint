import NPT.CP3.Inst

/-! Bridge facts of the tuples 50..74 (decided by the kernel). -/

namespace NPT.CP3.Inst

theorem bridge_chunk_2 : ∀ v < 25, BridgeB (50 + v) := by decide +kernel

end NPT.CP3.Inst
