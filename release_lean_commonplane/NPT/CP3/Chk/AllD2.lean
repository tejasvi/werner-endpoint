import NPT.CP3.Chk.All
import NPT.CP3.Chk.D2N00
import NPT.CP3.Chk.D2N01
import NPT.CP3.Chk.D2N02

/-!
# NPT.CP3.Chk.AllD2 — the bosonic-range checks over all 175 tuples
-/

namespace NPT.CP3.Chk

theorem d2_range : (List.range' 0 175).all d2OK = true :=
  all_range'_append (s := 0) (m := 124) (n := 51) (all_range'_append (s := 0) (m := 92) (n := 32) (d2n00_ok) d2n01_ok) d2n02_ok
theorem d2_all : ∀ v < 175, d2OK v = true := forall_of_range' d2_range

end NPT.CP3.Chk
