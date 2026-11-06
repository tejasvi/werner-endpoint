import NPT.CP3.Chk.AllD0
import NPT.CP3.Chk.AllD2
import NPT.CP3.Chk.Inter
import NPT.CP3.SemD2

/-!
# NPT.CP3.ChecksD2 — the bosonic range of every tuple, and the cut-() intertwiners

* `d2_ok`: for every sorted cut-`()` tuple `v < 175`, `(Pflat v)ᵀ = Wq v * (Wl v * (Pflat v)ᵀ)`: every column of
  `Pflatᵀ` lies in the column space of `W_v`. For the 25 tuples with `m = 0` this is `Pflat v = 0`.
  From the native checks `NPT.CP3.Chk.D2N*` (`d2OK`) through `NPT.CP3.SemD2`.
* `interSite_sum`: for every cut-`()` site label `k < 4`, `g < 24`, row `y < 81` (flat base-3 string, digit 0 most
  significant) and column `a < d_k`: `J_k[y ∘ pf g][a] = Σ_{b<d_k} J_k[y][b] · piSite[k][g][b][a]`, where
  `flatPerm 3 g y` is the flat index of `r ↦ y_{pf g r}` (`pf` = `NPT.Brauer.permL`).
* `interAux_sum`: the same for the selection matrix of every cut-`()` aux block `li < 5` (16 strings) against
  `auxM[0][li][g]`. Both from the kernel checks in `NPT.CP3.Chk.Inter`.
-/

namespace NPT.CP3

open Matrix NPT.CP3.Sem NPT.CP3.Chk NPT.CP3.Data

theorem d2_ok : ∀ v < 175, (Pflat v)ᵀ = Wq v * (Wl v * (Pflat v)ᵀ) := fun v hv =>
  d2_of_check (d0OK_spec (d0_all v hv)).2.2.1 (d2_all v hv)

theorem interSite_ok : ∀ l < 4, ∀ g < 24, interSiteOK l g = true := by
  have h := inter_ok
  simp only [interOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.1

theorem interAux_ok : ∀ li < 5, ∀ g < 24, interAuxOK li g = true := by
  have h := inter_ok
  simp only [interOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2

theorem interSite_sum : ∀ k < 4, ∀ g < 24, ∀ y < 81, ∀ a < (siteDims.getD 0 []).getD k 0,
    mget ((siteJ.getD 0 []).getD k []) (flatPerm 3 g y) a =
      ∑ b ∈ Finset.range ((siteDims.getD 0 []).getD k 0),
        mget ((siteJ.getD 0 []).getD k []) y b * mget ((piSite.getD k []).getD g []) b a := by
  intro k hk g hg y hy a ha
  have h := interSite_ok k hk g hg
  have hs := interShape_ok
  simp only [interSiteOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  simp only [interShapeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hs
  obtain ⟨hP, hJ⟩ := hs.1 k hk
  rw [h y hy a ha]
  obtain ⟨hPl, -⟩ := shapeOK_spec (hP g hg)
  rcases hJ y hy with h0 | hd
  · have e0 := List.eq_nil_of_length_eq_zero h0
    rw [e0, dot_nil_left]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    unfold mget
    rw [e0]
    simp
  · rw [dot_eq_sum _ _ _ hd (by rw [List.length_map]; exact hPl)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [getD_map_of_lt _ _ _ _ [] (by rw [hPl]; simpa using hb)]
    rfl

theorem interAux_sum : ∀ li < 5, ∀ g < 24, ∀ y < 16, ∀ j < ((auxBlocks.getD 0 []).getD li []).length,
    (if ((auxBlocks.getD 0 []).getD li []).getD j 0 = flatPerm 2 g y then (1 : Int) else 0) =
      ∑ j' ∈ Finset.range ((auxBlocks.getD 0 []).getD li []).length,
        (if ((auxBlocks.getD 0 []).getD li []).getD j' 0 = y then (1 : Int) else 0) *
          mget (((auxM.getD 0 []).getD li []).getD g []) j' j := by
  intro li hli g hg y hy j hj
  have h := interAux_ok li hli g hg
  have hs := interShape_ok
  simp only [interAuxOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  simp only [interShapeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨hSl, -⟩ := shapeOK_spec (hs.2 li hli g hg)
  have hsel : (selRow ((auxBlocks.getD 0 []).getD li []) y).length = ((auxBlocks.getD 0 []).getD li []).length := by
    rw [selRow, List.length_map]
  rw [h y hy j hj, dot_eq_sum _ _ ((auxBlocks.getD 0 []).getD li []).length hsel (by rw [List.length_map]; exact hSl)]
  refine Finset.sum_congr rfl fun j' hj' => ?_
  have hj'' : j' < ((auxBlocks.getD 0 []).getD li []).length := Finset.mem_range.1 hj'
  rw [selRow, getD_map_of_lt _ _ _ _ 0 hj'', getD_map_of_lt _ _ _ _ [] (by rw [hSl]; exact hj'')]
  rfl

end NPT.CP3
