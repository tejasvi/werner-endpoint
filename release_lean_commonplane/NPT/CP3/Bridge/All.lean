import NPT.CP3.Bridge.B0
import NPT.CP3.Bridge.B1
import NPT.CP3.Bridge.B2
import NPT.CP3.Bridge.B3
import NPT.CP3.Bridge.B4
import NPT.CP3.Bridge.B5
import NPT.CP3.Bridge.B6

/-! The bridge facts of all 175 tuples. -/

namespace NPT.CP3.Inst

lemma bridge_of_chunk {lo : ℕ} (h : ∀ v < 25, BridgeB (lo + v)) {v : ℕ} (h1 : lo ≤ v) (h2 : v < lo + 25) :
    BridgeB v := by
  have := h (v - lo) (by omega)
  rwa [show lo + (v - lo) = v by omega] at this

theorem bridge_all : ∀ v < 175, BridgeOK v := by
  intro v hv
  apply bridgeOK_of
  by_cases h0 : v < 25
  · exact bridge_of_chunk bridge_chunk_0 (by omega) (by omega)
  by_cases h1 : v < 50
  · exact bridge_of_chunk bridge_chunk_1 (by omega) (by omega)
  by_cases h2 : v < 75
  · exact bridge_of_chunk bridge_chunk_2 (by omega) (by omega)
  by_cases h3 : v < 100
  · exact bridge_of_chunk bridge_chunk_3 (by omega) (by omega)
  by_cases h4 : v < 125
  · exact bridge_of_chunk bridge_chunk_4 (by omega) (by omega)
  by_cases h5 : v < 150
  · exact bridge_of_chunk bridge_chunk_5 (by omega) (by omega)
  · exact bridge_of_chunk bridge_chunk_6 (by omega) (by omega)

end NPT.CP3.Inst
