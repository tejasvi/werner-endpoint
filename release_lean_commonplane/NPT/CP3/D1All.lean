/-
NPT.CP3.D1All — the native D1 check over all 1331 coordinates, from the chunk theorems NPT.CP3.D1Nat.N*.
-/
import NPT.CP3.D1Box
import NPT.CP3.D1Nat.N00
import NPT.CP3.D1Nat.N01
import NPT.CP3.D1Nat.N02
import NPT.CP3.D1Nat.N03
import NPT.CP3.D1Nat.N04
import NPT.CP3.D1Nat.N05
import NPT.CP3.D1Nat.N06
import NPT.CP3.D1Nat.N07
import NPT.CP3.D1Nat.N08
import NPT.CP3.D1Nat.N09
import NPT.CP3.D1Nat.N10
import NPT.CP3.D1Nat.N11
import NPT.CP3.D1Nat.N12
import NPT.CP3.D1Nat.N13
import NPT.CP3.D1Nat.N14
import NPT.CP3.D1Nat.N15
import NPT.CP3.D1Nat.N16
import NPT.CP3.D1Nat.N17
import NPT.CP3.D1Nat.N18
import NPT.CP3.D1Nat.N19
import NPT.CP3.D1Nat.N20
import NPT.CP3.D1Nat.N21
import NPT.CP3.D1Nat.N22
import NPT.CP3.D1Nat.N23
import NPT.CP3.D1Nat.N24
import NPT.CP3.D1Nat.N25
import NPT.CP3.D1Nat.N26
import NPT.CP3.D1Nat.N27
import NPT.CP3.D1Nat.N28
import NPT.CP3.D1Nat.N29
import NPT.CP3.D1Nat.N30
import NPT.CP3.D1Nat.N31
import NPT.CP3.D1Nat.N32
import NPT.CP3.D1Nat.N33
import NPT.CP3.D1Nat.N34
import NPT.CP3.D1Nat.N35
import NPT.CP3.D1Nat.N36
import NPT.CP3.D1Nat.N37
import NPT.CP3.D1Nat.N38
import NPT.CP3.D1Nat.N39
import NPT.CP3.D1Nat.N40
import NPT.CP3.D1Nat.N41
import NPT.CP3.D1Nat.N42
import NPT.CP3.D1Nat.N43
import NPT.CP3.D1Nat.N44
import NPT.CP3.D1Nat.N45
import NPT.CP3.D1Nat.N46
import NPT.CP3.D1Nat.N47
import NPT.CP3.D1Nat.N48
import NPT.CP3.D1Nat.N49
import NPT.CP3.D1Nat.N50
import NPT.CP3.D1Nat.N51
import NPT.CP3.D1Nat.N52
import NPT.CP3.D1Nat.N53
import NPT.CP3.D1Nat.N54
import NPT.CP3.D1Nat.N55
import NPT.CP3.D1Nat.N56
import NPT.CP3.D1Nat.N57
import NPT.CP3.D1Nat.N58
import NPT.CP3.D1Nat.N59
import NPT.CP3.D1Nat.N60
import NPT.CP3.D1Nat.N61
import NPT.CP3.D1Nat.N62
import NPT.CP3.D1Nat.N63

namespace NPT.CP3.D1

theorem upto_00 : checkRange raw 0 21 = true := nat_00
theorem upto_01 : checkRange raw 0 42 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_00 nat_01
theorem upto_02 : checkRange raw 0 63 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_01 nat_02
theorem upto_03 : checkRange raw 0 84 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_02 nat_03
theorem upto_04 : checkRange raw 0 105 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_03 nat_04
theorem upto_05 : checkRange raw 0 126 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_04 nat_05
theorem upto_06 : checkRange raw 0 147 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_05 nat_06
theorem upto_07 : checkRange raw 0 168 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_06 nat_07
theorem upto_08 : checkRange raw 0 189 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_07 nat_08
theorem upto_09 : checkRange raw 0 210 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_08 nat_09
theorem upto_10 : checkRange raw 0 231 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_09 nat_10
theorem upto_11 : checkRange raw 0 252 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_10 nat_11
theorem upto_12 : checkRange raw 0 273 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_11 nat_12
theorem upto_13 : checkRange raw 0 294 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_12 nat_13
theorem upto_14 : checkRange raw 0 315 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_13 nat_14
theorem upto_15 : checkRange raw 0 336 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_14 nat_15
theorem upto_16 : checkRange raw 0 357 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_15 nat_16
theorem upto_17 : checkRange raw 0 378 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_16 nat_17
theorem upto_18 : checkRange raw 0 399 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_17 nat_18
theorem upto_19 : checkRange raw 0 420 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_18 nat_19
theorem upto_20 : checkRange raw 0 441 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_19 nat_20
theorem upto_21 : checkRange raw 0 462 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_20 nat_21
theorem upto_22 : checkRange raw 0 483 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_21 nat_22
theorem upto_23 : checkRange raw 0 504 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_22 nat_23
theorem upto_24 : checkRange raw 0 525 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_23 nat_24
theorem upto_25 : checkRange raw 0 546 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_24 nat_25
theorem upto_26 : checkRange raw 0 567 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_25 nat_26
theorem upto_27 : checkRange raw 0 588 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_26 nat_27
theorem upto_28 : checkRange raw 0 609 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_27 nat_28
theorem upto_29 : checkRange raw 0 630 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_28 nat_29
theorem upto_30 : checkRange raw 0 651 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_29 nat_30
theorem upto_31 : checkRange raw 0 672 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_30 nat_31
theorem upto_32 : checkRange raw 0 693 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_31 nat_32
theorem upto_33 : checkRange raw 0 714 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_32 nat_33
theorem upto_34 : checkRange raw 0 735 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_33 nat_34
theorem upto_35 : checkRange raw 0 756 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_34 nat_35
theorem upto_36 : checkRange raw 0 777 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_35 nat_36
theorem upto_37 : checkRange raw 0 798 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_36 nat_37
theorem upto_38 : checkRange raw 0 819 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_37 nat_38
theorem upto_39 : checkRange raw 0 840 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_38 nat_39
theorem upto_40 : checkRange raw 0 861 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_39 nat_40
theorem upto_41 : checkRange raw 0 882 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_40 nat_41
theorem upto_42 : checkRange raw 0 903 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_41 nat_42
theorem upto_43 : checkRange raw 0 924 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_42 nat_43
theorem upto_44 : checkRange raw 0 945 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_43 nat_44
theorem upto_45 : checkRange raw 0 966 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_44 nat_45
theorem upto_46 : checkRange raw 0 987 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_45 nat_46
theorem upto_47 : checkRange raw 0 1008 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_46 nat_47
theorem upto_48 : checkRange raw 0 1029 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_47 nat_48
theorem upto_49 : checkRange raw 0 1050 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_48 nat_49
theorem upto_50 : checkRange raw 0 1071 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_49 nat_50
theorem upto_51 : checkRange raw 0 1092 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_50 nat_51
theorem upto_52 : checkRange raw 0 1113 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_51 nat_52
theorem upto_53 : checkRange raw 0 1134 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_52 nat_53
theorem upto_54 : checkRange raw 0 1155 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_53 nat_54
theorem upto_55 : checkRange raw 0 1176 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_54 nat_55
theorem upto_56 : checkRange raw 0 1197 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_55 nat_56
theorem upto_57 : checkRange raw 0 1218 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_56 nat_57
theorem upto_58 : checkRange raw 0 1239 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_57 nat_58
theorem upto_59 : checkRange raw 0 1260 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_58 nat_59
theorem upto_60 : checkRange raw 0 1281 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_59 nat_60
theorem upto_61 : checkRange raw 0 1302 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_60 nat_61
theorem upto_62 : checkRange raw 0 1323 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_61 nat_62
theorem upto_63 : checkRange raw 0 1331 = true :=
  checkRange_append raw (by norm_num) (by norm_num) upto_62 nat_63

/-- **The native D1 check over all coordinates.** -/
theorem nat_all : checkRange raw 0 1331 = true := upto_63

end NPT.CP3.D1
