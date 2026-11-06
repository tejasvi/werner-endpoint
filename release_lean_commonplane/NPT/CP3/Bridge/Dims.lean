import NPT.CP3.D2B

/-! The dimension facts `DimsOK` of all 175 tuples (one kernel decision). -/

namespace NPT.CP3.Inst

theorem dims_ok : ∀ v < 175, DimsOK v := by decide +kernel

end NPT.CP3.Inst
