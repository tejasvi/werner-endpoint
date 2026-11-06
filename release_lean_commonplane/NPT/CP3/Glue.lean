/-
NPT.CP3.Glue — the 175 sorted cut-() tuples of the certificate as `TupleData (PD 0) πp`.

`T v` carries the padded data of tuple `v` with its bridge facts (`bridge_all`), the D0 facts (`d0_ok`) and the
bosonic-range fact from `d2_ok` (`hK_tuple`). The coordinate ranges are disjoint (`off_disjoint`), so the Gram form of
every tuple at the projected moment is `Σ_j y_(off_v + j) W_v S_j W_vᵀ` with `y = yvec T A` (`hcoordT`).
-/
import NPT.CP3.PD
import NPT.CP3.ChecksD2
import NPT.CP3.Bridge.All
import NPT.CP3.Bridge.Dims
import NPT.CP3.Chk.Off

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-- The bosonic-range fact of tuple `v`: `Pavᵀ = W (W⁺ Pavᵀ)`, padded from `d2_ok`. -/
lemma hK_tuple (v : ℕ) (hv : v < 175) (hb : BridgeOK v) (hd : DimsOK v) :
    (Pav πp (tupF v))ᵀ = Wc v * (Wpc v * (Pav πp (tupF v))ᵀ) := by
  rw [Pav_eq_padRC v hb.box hd]
  unfold Wc Wpc
  refine hK_of_flat hb.box (cq' (Wq v)) (cq' (Wl v)) (cq' (Pflat v)) ?_
  have h := congrArg cq' (d2_ok v hv)
  rwa [cq'_mul, cq'_mul, cq'_transpose] at h

/-- **The 175 sorted cut-() tuples.** -/
noncomputable def T : Fin 175 → TupleData (PD 0) πp := fun v =>
  mkTuple (PD 0) πp v (bridge_all v v.isLt) (d0_ok v v.isLt)
    (hK_tuple v v.isLt (bridge_all v v.isLt) (dims_ok v v.isLt))

/-- The coordinate ranges of the tuples are disjoint. -/
theorem offDisj_T : OffDisj T := by
  intro v v' j j' h
  have hj : j.val < (vb v).S.length := j.isLt
  have hj' : j'.val < (vb v').S.length := j'.isLt
  have h' : (vb v).off + j.val = (vb v').off + j'.val := h
  by_cases hvv : v = v'
  · subst hvv
    exact ⟨rfl, by omega⟩
  · exfalso
    have hd := off_disjoint v v.isLt v' v'.isLt (fun e => hvv (Fin.ext e))
    have m1 : (vb v).off + j.val ∈ Finset.Ico (vb v).off ((vb v).off + (vb v).S.length) :=
      Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have m2 : (vb v).off + j.val ∈ Finset.Ico (vb v').off ((vb v').off + (vb v').S.length) :=
      Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    exact Finset.disjoint_left.mp hd m1 m2

/-- **The coordinate representation** of the Gram form of every tuple at the projected moment. -/
theorem hcoordT (A : MatA) (v : Fin 175) :
    gram (PD 0).fam (tupF v) (Yp A) =
      ∑ j : Fin (vb v).S.length, yvec T A ((vb v).off + j.val) • (Wc v * cq' (Sq v j) * (Wc v)ᵀ) :=
  hcoord T offDisj_T PD_intertw A v

end NPT.CP3.Inst
