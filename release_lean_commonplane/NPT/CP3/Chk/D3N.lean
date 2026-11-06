import NPT.CP3.D3Equiv

/-!
# NPT.CP3.Chk.D3N — the D3 check over all 175 tuples, by one native evaluation

Built with `--load-dynlib` of the library compiled from `NPT.CP3.D3Fast`, `NPT.CP3.D1Core` and `NPT.CP3.Data.Types`
(the record `rawD` is evaluated by the interpreter, `d3Range` runs as native code).
-/

namespace NPT.CP3.D3F

theorem d3_native : d3Range rawD 0 175 = true := by native_decide

end NPT.CP3.D3F
