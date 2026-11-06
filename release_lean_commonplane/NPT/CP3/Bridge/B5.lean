import NPT.CP3.Inst

/-! Bridge facts of the tuples 125..149 (decided by the kernel). -/

namespace NPT.CP3.Inst

theorem bridge_chunk_5 : ∀ v < 25, BridgeB (125 + v) := by decide +kernel

end NPT.CP3.Inst
