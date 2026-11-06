import NPT.CP3.D3Core
import NPT.CP3.D3Fast

/-!
# NPT.CP3.D3Equiv — the module data as one record, and the record check is the check of `NPT.CP3.D3Core` (`rfl`)
-/

namespace NPT.CP3.D3F

open NPT.CP3.Data

/-- The module data read by `NPT.CP3.D3Core`. -/
def rawD : D3Raw :=
  { vars := vars, Ecol := Ecol, zsObj2 := zsObj2, ifgNum := ifgNum, siteOff := siteOff, eqNum := eqNum,
    auxBlocks := auxBlocks, words := words, zaA := zaA, zaB := zaB, zaAB := zaAB, caN := caN, cbN := cbN,
    cabN := cabN, sortedQ := sortedQ, erows := erows, auxMst := auxMst, cDen := cDen }

theorem d3OK_eq (v : Nat) : d3OK rawD (zrA rawD) v = NPT.CP3.D3.d3OK v := rfl

theorem d3Range_eq (a b : Nat) : d3Range rawD a b = (List.range' a (b - a)).all NPT.CP3.D3.d3OK := rfl

end NPT.CP3.D3F
