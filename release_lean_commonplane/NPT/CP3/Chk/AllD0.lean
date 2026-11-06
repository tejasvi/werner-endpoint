import NPT.CP3.Chk.All
import NPT.CP3.Chk.D000
import NPT.CP3.Chk.D001
import NPT.CP3.Chk.D002
import NPT.CP3.Chk.D003
import NPT.CP3.Chk.D004
import NPT.CP3.Chk.D005
import NPT.CP3.Chk.D006
import NPT.CP3.Chk.D007
import NPT.CP3.Chk.D008
import NPT.CP3.Chk.D009
import NPT.CP3.Chk.D010
import NPT.CP3.Chk.D011
import NPT.CP3.Chk.D012
import NPT.CP3.Chk.D013
import NPT.CP3.Chk.D014
import NPT.CP3.Chk.D015
import NPT.CP3.Chk.D016
import NPT.CP3.Chk.D017
import NPT.CP3.Chk.D018
import NPT.CP3.Chk.D019
import NPT.CP3.Chk.D020
import NPT.CP3.Chk.D021
import NPT.CP3.Chk.D022
import NPT.CP3.Chk.D023
import NPT.CP3.Chk.D024
import NPT.CP3.Chk.D025
import NPT.CP3.Chk.D026
import NPT.CP3.Chk.D027
import NPT.CP3.Chk.D028
import NPT.CP3.Chk.D029
import NPT.CP3.Chk.D030
import NPT.CP3.Chk.D031
import NPT.CP3.Chk.D032
import NPT.CP3.Chk.D033
import NPT.CP3.Chk.D034
import NPT.CP3.Chk.D035
import NPT.CP3.Chk.D036
import NPT.CP3.Chk.D037
import NPT.CP3.Chk.D038
import NPT.CP3.Chk.D039
import NPT.CP3.Chk.D040
import NPT.CP3.Chk.D041
import NPT.CP3.Chk.D042
import NPT.CP3.Chk.D043
import NPT.CP3.Chk.D044
import NPT.CP3.Chk.D045
import NPT.CP3.Chk.D046
import NPT.CP3.Chk.D047
import NPT.CP3.Chk.D048
import NPT.CP3.Chk.D049
import NPT.CP3.Chk.D050
import NPT.CP3.Chk.D051
import NPT.CP3.Chk.D052
import NPT.CP3.Chk.D053
import NPT.CP3.Chk.D054
import NPT.CP3.Chk.D055
import NPT.CP3.Chk.D056
import NPT.CP3.Chk.D057
import NPT.CP3.Chk.D058
import NPT.CP3.Chk.D059
import NPT.CP3.Chk.D060
import NPT.CP3.Chk.D061
import NPT.CP3.Chk.D062
import NPT.CP3.Chk.D063
import NPT.CP3.Chk.D064
import NPT.CP3.Chk.D065
import NPT.CP3.Chk.D066
import NPT.CP3.Chk.D067
import NPT.CP3.Chk.D068
import NPT.CP3.Chk.D069
import NPT.CP3.Chk.D070
import NPT.CP3.Chk.D071
import NPT.CP3.Chk.D072
import NPT.CP3.Chk.D073
import NPT.CP3.Chk.D074
import NPT.CP3.Chk.D075
import NPT.CP3.Chk.D076
import NPT.CP3.Chk.D077
import NPT.CP3.Chk.D078
import NPT.CP3.Chk.D079
import NPT.CP3.Chk.D080
import NPT.CP3.Chk.D081
import NPT.CP3.Chk.D082
import NPT.CP3.Chk.D083
import NPT.CP3.Chk.D084
import NPT.CP3.Chk.D085
import NPT.CP3.Chk.D086
import NPT.CP3.Chk.D087
import NPT.CP3.Chk.D088
import NPT.CP3.Chk.D089
import NPT.CP3.Chk.D090
import NPT.CP3.Chk.D091

/-!
# NPT.CP3.Chk.AllD0 — the D0 kernel checks over all variable blocks
-/

set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0OK_of {v L P : Nat} (h0 : d0LightOK v = true) (hL : (dv v).stab.length = L)
    (hP : (ups (mv v)).length = P) (hb : (List.range' 0 L).all (bsigOK1 v) = true)
    (hs : (List.range' 0 P).all (spanOK1 v) = true) : d0OK v = true := by
  simp only [d0OK, h0, hL, hP, List.range_eq_range', hb, hs, Bool.and_self]

theorem single_range' {p : Nat → Bool} {v : Nat} (h : p v = true) : (List.range' v 1).all p = true := by
  simp [List.range'_succ, h]

theorem d0v080_ok : d0OK 80 = true :=
  d0OK_of d0l080_ok (by decide +kernel : (dv 80).stab.length = 24) (by decide +kernel : (ups (mv 80)).length = 105)
    (all_range'_append (s := 0) (m := 17) (n := 7) (d0b080_00_ok) d0b080_01_ok)
    (all_range'_append (s := 0) (m := 95) (n := 10) (d0s080_00_ok) d0s080_01_ok)
theorem d0v080_r : (List.range' 80 1).all d0OK = true := single_range' d0v080_ok

theorem d0v081_ok : d0OK 81 = true :=
  d0OK_of d0l081_ok (by decide +kernel : (dv 81).stab.length = 24) (by decide +kernel : (ups (mv 81)).length = 231)
    (all_range'_append (s := 0) (m := 20) (n := 4) (all_range'_append (s := 0) (m := 15) (n := 5) (all_range'_append (s := 0) (m := 10) (n := 5) (all_range'_append (s := 0) (m := 5) (n := 5) (d0b081_00_ok) d0b081_01_ok) d0b081_02_ok) d0b081_03_ok) d0b081_04_ok)
    (all_range'_append (s := 0) (m := 198) (n := 33) (all_range'_append (s := 0) (m := 165) (n := 33) (all_range'_append (s := 0) (m := 132) (n := 33) (all_range'_append (s := 0) (m := 99) (n := 33) (all_range'_append (s := 0) (m := 66) (n := 33) (all_range'_append (s := 0) (m := 33) (n := 33) (d0s081_00_ok) d0s081_01_ok) d0s081_02_ok) d0s081_03_ok) d0s081_04_ok) d0s081_05_ok) d0s081_06_ok)
theorem d0v081_r : (List.range' 81 1).all d0OK = true := single_range' d0v081_ok

theorem d0v082_ok : d0OK 82 = true :=
  d0OK_of d0l082_ok (by decide +kernel : (dv 82).stab.length = 24) (by decide +kernel : (ups (mv 82)).length = 105)
    (all_range'_append (s := 0) (m := 17) (n := 7) (d0b082_00_ok) d0b082_01_ok)
    (all_range'_append (s := 0) (m := 95) (n := 10) (d0s082_00_ok) d0s082_01_ok)
theorem d0v082_r : (List.range' 82 1).all d0OK = true := single_range' d0v082_ok

theorem d0v091_ok : d0OK 91 = true :=
  d0OK_of d0l091_ok (by decide +kernel : (dv 91).stab.length = 6) (by decide +kernel : (ups (mv 91)).length = 210)
    (all_range'_append (s := 0) (m := 5) (n := 1) (d0b091_00_ok) d0b091_01_ok)
    (all_range'_append (s := 0) (m := 192) (n := 18) (all_range'_append (s := 0) (m := 144) (n := 48) (all_range'_append (s := 0) (m := 96) (n := 48) (all_range'_append (s := 0) (m := 48) (n := 48) (d0s091_00_ok) d0s091_01_ok) d0s091_02_ok) d0s091_03_ok) d0s091_04_ok)
theorem d0v091_r : (List.range' 91 1).all d0OK = true := single_range' d0v091_ok

theorem d0v105_ok : d0OK 105 = true :=
  d0OK_of d0l105_ok (by decide +kernel : (dv 105).stab.length = 4) (by decide +kernel : (ups (mv 105)).length = 105)
    (d0b105_00_ok)
    (d0s105_00_ok)
theorem d0v105_r : (List.range' 105 1).all d0OK = true := single_range' d0v105_ok

theorem d0v106_ok : d0OK 106 = true :=
  d0OK_of d0l106_ok (by decide +kernel : (dv 106).stab.length = 4) (by decide +kernel : (ups (mv 106)).length = 231)
    (d0b106_00_ok)
    (all_range'_append (s := 0) (m := 208) (n := 23) (all_range'_append (s := 0) (m := 182) (n := 26) (all_range'_append (s := 0) (m := 156) (n := 26) (all_range'_append (s := 0) (m := 130) (n := 26) (all_range'_append (s := 0) (m := 104) (n := 26) (all_range'_append (s := 0) (m := 78) (n := 26) (all_range'_append (s := 0) (m := 52) (n := 26) (all_range'_append (s := 0) (m := 26) (n := 26) (d0s106_00_ok) d0s106_01_ok) d0s106_02_ok) d0s106_03_ok) d0s106_04_ok) d0s106_05_ok) d0s106_06_ok) d0s106_07_ok) d0s106_08_ok)
theorem d0v106_r : (List.range' 106 1).all d0OK = true := single_range' d0v106_ok

theorem d0v107_ok : d0OK 107 = true :=
  d0OK_of d0l107_ok (by decide +kernel : (dv 107).stab.length = 4) (by decide +kernel : (ups (mv 107)).length = 105)
    (d0b107_00_ok)
    (d0s107_00_ok)
theorem d0v107_r : (List.range' 107 1).all d0OK = true := single_range' d0v107_ok

theorem d0v124_ok : d0OK 124 = true :=
  d0OK_of d0l124_ok (by decide +kernel : (dv 124).stab.length = 6) (by decide +kernel : (ups (mv 124)).length = 210)
    (all_range'_append (s := 0) (m := 5) (n := 1) (d0b124_00_ok) d0b124_01_ok)
    (all_range'_append (s := 0) (m := 192) (n := 18) (all_range'_append (s := 0) (m := 144) (n := 48) (all_range'_append (s := 0) (m := 96) (n := 48) (all_range'_append (s := 0) (m := 48) (n := 48) (d0s124_00_ok) d0s124_01_ok) d0s124_02_ok) d0s124_03_ok) d0s124_04_ok)
theorem d0v124_r : (List.range' 124 1).all d0OK = true := single_range' d0v124_ok

theorem d0v146_ok : d0OK 146 = true :=
  d0OK_of d0l146_ok (by decide +kernel : (dv 146).stab.length = 24) (by decide +kernel : (ups (mv 146)).length = 105)
    (all_range'_append (s := 0) (m := 17) (n := 7) (d0b146_00_ok) d0b146_01_ok)
    (all_range'_append (s := 0) (m := 95) (n := 10) (d0s146_00_ok) d0s146_01_ok)
theorem d0v146_r : (List.range' 146 1).all d0OK = true := single_range' d0v146_ok

theorem d0v147_ok : d0OK 147 = true :=
  d0OK_of d0l147_ok (by decide +kernel : (dv 147).stab.length = 24) (by decide +kernel : (ups (mv 147)).length = 231)
    (all_range'_append (s := 0) (m := 20) (n := 4) (all_range'_append (s := 0) (m := 15) (n := 5) (all_range'_append (s := 0) (m := 10) (n := 5) (all_range'_append (s := 0) (m := 5) (n := 5) (d0b147_00_ok) d0b147_01_ok) d0b147_02_ok) d0b147_03_ok) d0b147_04_ok)
    (all_range'_append (s := 0) (m := 198) (n := 33) (all_range'_append (s := 0) (m := 165) (n := 33) (all_range'_append (s := 0) (m := 132) (n := 33) (all_range'_append (s := 0) (m := 99) (n := 33) (all_range'_append (s := 0) (m := 66) (n := 33) (all_range'_append (s := 0) (m := 33) (n := 33) (d0s147_00_ok) d0s147_01_ok) d0s147_02_ok) d0s147_03_ok) d0s147_04_ok) d0s147_05_ok) d0s147_06_ok)
theorem d0v147_r : (List.range' 147 1).all d0OK = true := single_range' d0v147_ok

theorem d0v148_ok : d0OK 148 = true :=
  d0OK_of d0l148_ok (by decide +kernel : (dv 148).stab.length = 24) (by decide +kernel : (ups (mv 148)).length = 105)
    (all_range'_append (s := 0) (m := 17) (n := 7) (d0b148_00_ok) d0b148_01_ok)
    (all_range'_append (s := 0) (m := 95) (n := 10) (d0s148_00_ok) d0s148_01_ok)
theorem d0v148_r : (List.range' 148 1).all d0OK = true := single_range' d0v148_ok

theorem d0_range : (List.range' 0 175).all d0OK = true :=
  all_range'_append (s := 0) (m := 149) (n := 26) (all_range'_append (s := 0) (m := 148) (n := 1) (all_range'_append (s := 0) (m := 147) (n := 1) (all_range'_append (s := 0) (m := 146) (n := 1) (all_range'_append (s := 0) (m := 142) (n := 4) (all_range'_append (s := 0) (m := 129) (n := 13) (all_range'_append (s := 0) (m := 125) (n := 4) (all_range'_append (s := 0) (m := 124) (n := 1) (all_range'_append (s := 0) (m := 123) (n := 1) (all_range'_append (s := 0) (m := 119) (n := 4) (all_range'_append (s := 0) (m := 108) (n := 11) (all_range'_append (s := 0) (m := 107) (n := 1) (all_range'_append (s := 0) (m := 106) (n := 1) (all_range'_append (s := 0) (m := 105) (n := 1) (all_range'_append (s := 0) (m := 101) (n := 4) (all_range'_append (s := 0) (m := 96) (n := 5) (all_range'_append (s := 0) (m := 92) (n := 4) (all_range'_append (s := 0) (m := 91) (n := 1) (all_range'_append (s := 0) (m := 87) (n := 4) (all_range'_append (s := 0) (m := 83) (n := 4) (all_range'_append (s := 0) (m := 82) (n := 1) (all_range'_append (s := 0) (m := 81) (n := 1) (all_range'_append (s := 0) (m := 80) (n := 1) (d0r00_ok) d0v080_r) d0v081_r) d0v082_r) d0r24_ok) d0r25_ok) d0v091_r) d0r34_ok) d0r35_ok) d0r36_ok) d0v105_r) d0v106_r) d0v107_r) d0r54_ok) d0r55_ok) d0r56_ok) d0v124_r) d0r65_ok) d0r66_ok) d0r67_ok) d0v146_r) d0v147_r) d0v148_r) d0r91_ok
theorem d0_all : ∀ v < 175, d0OK v = true := forall_of_range' d0_range

end NPT.CP3.Chk
