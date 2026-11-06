import NPT.CP3.Chk.Struct
import NPT.CP3.Chk.Ident00
import NPT.CP3.Chk.Ident01
import NPT.CP3.Chk.Ident02
import NPT.CP3.Chk.Ident03
import NPT.CP3.Chk.Ident04
import NPT.CP3.Chk.Ident05
import NPT.CP3.Chk.Ident06
import NPT.CP3.Chk.Ident07
import NPT.CP3.Chk.Ident08
import NPT.CP3.Chk.Ident09
import NPT.CP3.Chk.Ident10
import NPT.CP3.Chk.Ident11
import NPT.CP3.Chk.Ident12
import NPT.CP3.Chk.Ident13
import NPT.CP3.Chk.Ident14
import NPT.CP3.Chk.Ident15
import NPT.CP3.Chk.Ident16
import NPT.CP3.Chk.Ident17
import NPT.CP3.Chk.Ident18
import NPT.CP3.Chk.Ident19
import NPT.CP3.Chk.Ident20
import NPT.CP3.Chk.Ident21
import NPT.CP3.Chk.Ident22
import NPT.CP3.Chk.Ident23
import NPT.CP3.Chk.Ident24
import NPT.CP3.Chk.Ident25
import NPT.CP3.Chk.Ident26
import NPT.CP3.Chk.Ident27
import NPT.CP3.Chk.Ident28
import NPT.CP3.Chk.Ident29
import NPT.CP3.Chk.Ident30
import NPT.CP3.Chk.Ident31
import NPT.CP3.Chk.Ident32
import NPT.CP3.Chk.Ident33
import NPT.CP3.Chk.Ident34
import NPT.CP3.Chk.Ident35
import NPT.CP3.Chk.Ident36
import NPT.CP3.Chk.Ident37
import NPT.CP3.Chk.Ident38
import NPT.CP3.Chk.Ident39
import NPT.CP3.Chk.Ident40
import NPT.CP3.Chk.Ident41
import NPT.CP3.Chk.Ident42
import NPT.CP3.Chk.Ident43
import NPT.CP3.Chk.Ident44
import NPT.CP3.Chk.Ident45
import NPT.CP3.Chk.Ident46
import NPT.CP3.Chk.Ident47
import NPT.CP3.Chk.Ident48
import NPT.CP3.Chk.Ident49
import NPT.CP3.Chk.Ident50
import NPT.CP3.Chk.Zd00
import NPT.CP3.Chk.Zd01
import NPT.CP3.Chk.Zd02
import NPT.CP3.Chk.Zd03
import NPT.CP3.Chk.Zd04
import NPT.CP3.Chk.Psd00
import NPT.CP3.Chk.Psd01
import NPT.CP3.Chk.Psd02

/-!
# NPT.CP3.Chk.All — the kernel checks over their whole ranges
-/

namespace NPT.CP3.Chk

open NPT.CP3.Data

theorem all_range'_append {p : Nat → Bool} {s m n : Nat} (h₁ : (List.range' s m).all p = true)
    (h₂ : (List.range' (s + m) n).all p = true) : (List.range' s (m + n)).all p = true := by
  rw [← List.range'_append, Nat.one_mul, List.all_append, h₁, h₂, Bool.and_self]

theorem forall_of_range' {p : Nat → Bool} {n : Nat} (h : (List.range' 0 n).all p = true) : ∀ i < n, p i = true := by
  intro i hi
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)

theorem ident_range : (List.range' 0 1331).all identAt = true :=
  all_range'_append (s := 0) (m := 1308) (n := 23) (all_range'_append (s := 0) (m := 1282) (n := 26) (all_range'_append (s := 0) (m := 1248) (n := 34) (all_range'_append (s := 0) (m := 1225) (n := 23) (all_range'_append (s := 0) (m := 1194) (n := 31) (all_range'_append (s := 0) (m := 1172) (n := 22) (all_range'_append (s := 0) (m := 1144) (n := 28) (all_range'_append (s := 0) (m := 1111) (n := 33) (all_range'_append (s := 0) (m := 1086) (n := 25) (all_range'_append (s := 0) (m := 1065) (n := 21) (all_range'_append (s := 0) (m := 1040) (n := 25) (all_range'_append (s := 0) (m := 1011) (n := 29) (all_range'_append (s := 0) (m := 987) (n := 24) (all_range'_append (s := 0) (m := 965) (n := 22) (all_range'_append (s := 0) (m := 944) (n := 21) (all_range'_append (s := 0) (m := 915) (n := 29) (all_range'_append (s := 0) (m := 891) (n := 24) (all_range'_append (s := 0) (m := 871) (n := 20) (all_range'_append (s := 0) (m := 844) (n := 27) (all_range'_append (s := 0) (m := 813) (n := 31) (all_range'_append (s := 0) (m := 788) (n := 25) (all_range'_append (s := 0) (m := 768) (n := 20) (all_range'_append (s := 0) (m := 747) (n := 21) (all_range'_append (s := 0) (m := 725) (n := 22) (all_range'_append (s := 0) (m := 705) (n := 20) (all_range'_append (s := 0) (m := 681) (n := 24) (all_range'_append (s := 0) (m := 655) (n := 26) (all_range'_append (s := 0) (m := 624) (n := 31) (all_range'_append (s := 0) (m := 601) (n := 23) (all_range'_append (s := 0) (m := 581) (n := 20) (all_range'_append (s := 0) (m := 560) (n := 21) (all_range'_append (s := 0) (m := 535) (n := 25) (all_range'_append (s := 0) (m := 508) (n := 27) (all_range'_append (s := 0) (m := 486) (n := 22) (all_range'_append (s := 0) (m := 456) (n := 30) (all_range'_append (s := 0) (m := 434) (n := 22) (all_range'_append (s := 0) (m := 413) (n := 21) (all_range'_append (s := 0) (m := 391) (n := 22) (all_range'_append (s := 0) (m := 362) (n := 29) (all_range'_append (s := 0) (m := 341) (n := 21) (all_range'_append (s := 0) (m := 310) (n := 31) (all_range'_append (s := 0) (m := 286) (n := 24) (all_range'_append (s := 0) (m := 259) (n := 27) (all_range'_append (s := 0) (m := 228) (n := 31) (all_range'_append (s := 0) (m := 196) (n := 32) (all_range'_append (s := 0) (m := 172) (n := 24) (all_range'_append (s := 0) (m := 145) (n := 27) (all_range'_append (s := 0) (m := 116) (n := 29) (all_range'_append (s := 0) (m := 88) (n := 28) (all_range'_append (s := 0) (m := 54) (n := 34) (ident00_ok) ident01_ok) ident02_ok) ident03_ok) ident04_ok) ident05_ok) ident06_ok) ident07_ok) ident08_ok) ident09_ok) ident10_ok) ident11_ok) ident12_ok) ident13_ok) ident14_ok) ident15_ok) ident16_ok) ident17_ok) ident18_ok) ident19_ok) ident20_ok) ident21_ok) ident22_ok) ident23_ok) ident24_ok) ident25_ok) ident26_ok) ident27_ok) ident28_ok) ident29_ok) ident30_ok) ident31_ok) ident32_ok) ident33_ok) ident34_ok) ident35_ok) ident36_ok) ident37_ok) ident38_ok) ident39_ok) ident40_ok) ident41_ok) ident42_ok) ident43_ok) ident44_ok) ident45_ok) ident46_ok) ident47_ok) ident48_ok) ident49_ok) ident50_ok
theorem ident_all : ∀ i < 1331, identAt i = true := forall_of_range' ident_range

theorem zd_range : (List.range' 0 302).all zdOK = true :=
  all_range'_append (s := 0) (m := 276) (n := 26) (all_range'_append (s := 0) (m := 261) (n := 15) (all_range'_append (s := 0) (m := 257) (n := 4) (all_range'_append (s := 0) (m := 253) (n := 4) (zd00_ok) zd01_ok) zd02_ok) zd03_ok) zd04_ok
theorem zd_all : ∀ i < 302, zdOK i = true := forall_of_range' zd_range

theorem psd_range : (List.range' 0 302).all psdOK = true :=
  all_range'_append (s := 0) (m := 275) (n := 27) (all_range'_append (s := 0) (m := 257) (n := 18) (psd00_ok) psd01_ok) psd02_ok
theorem psd_all : ∀ i < 302, psdOK i = true := forall_of_range' psd_range

theorem blocks_all : ∀ k < 302, blockOK k = true := by
  intro k hk
  have := blocks_ok
  rw [List.all_eq_true] at this
  exact this k (List.mem_range.2 hk)

theorem heads_all : ∀ i < 1331, headsOK 0 (Fc.getD i []) = true := by
  intro i _
  have h := heads_ok
  rw [List.all_eq_true] at h
  by_cases hl : i < Fc.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

end NPT.CP3.Chk
