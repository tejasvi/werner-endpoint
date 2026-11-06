/-
NPT.CP3.Assemble — the global coordinate vector of the projected moment.

Each sorted cut-() tuple carries its data and checks (`TupleData`, the hypotheses of `tuple_coords`) and an offset; the
coordinate ranges are disjoint. The coordinates of all tuples assemble into one vector `yvec A : ℕ → ℂ` with
`gram τ_v (Yp A) = Σ_j yvec A (off_v + j) • W_v S_j W_vᵀ` for every tuple (`hcoord`).
-/
import NPT.CP3.Coords

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem

namespace NPT.CP3

/-- Data and checks of one sorted cut-() tuple. -/
structure TupleData (P : PadData) (πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ) where
  τ : Fin 5 → Fin 5
  m : ℕ
  W : Matrix MI (Fin m) ℂ
  Wp : Matrix (Fin m) MI ℂ
  K : Matrix (Fin m) MI ℂ
  hWp : Wp * W = 1
  hK : (Pav πp τ)ᵀ = W * K
  n : ℕ
  σs : Fin n → Equiv.Perm (Fin 4)
  hσ : ∀ i, (fun l => τ (sigHat (σs i) l)) = τ
  B : Fin n → Matrix (Fin m) (Fin m) ℂ
  hB : ∀ i, Qperm (σs i) * W = W * B i
  nb : ℕ
  S : Fin nb → Matrix (Fin m) (Fin m) ℂ
  c : Fin m → Fin m → Fin nb → ℂ
  hc : ∀ a b, ∑ i, B i * symU a b * (B i)ᵀ = ∑ j, c a b j • S j
  hn : n ≠ 0
  off : ℕ

variable {P : PadData} {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}

/-- The coordinates of one tuple at the Stiefel matrix `A`. -/
noncomputable def TupleData.yc (T : TupleData P πp) (A : MatA) (j : Fin T.nb) : ℂ :=
  ycoord (n := T.n) (T.Wp * gram P.fam T.τ (Yp A) * T.Wpᵀ) T.c j

theorem TupleData.coords (T : TupleData P πp) (h : Intertw P πp) (A : MatA) :
    gram P.fam T.τ (Yp A) = ∑ j, T.yc A j • (T.W * T.S j * T.Wᵀ) :=
  tuple_coords P h T.τ A T.W T.Wp T.K T.hWp T.hK T.σs T.hσ T.B T.hB T.S T.c T.hc T.hn

/-- The global coordinate vector. -/
noncomputable def yvec {nV : ℕ} (T : Fin nV → TupleData P πp) (A : MatA) (i : ℕ) : ℂ :=
  ∑ v, ∑ j : Fin (T v).nb, if (T v).off + j.val = i then (T v).yc A j else 0

/-- Disjoint coordinate ranges. -/
def OffDisj {nV : ℕ} (T : Fin nV → TupleData P πp) : Prop :=
  ∀ v v' (j : Fin (T v).nb) (j' : Fin (T v').nb), (T v).off + j.val = (T v').off + j'.val → v = v' ∧ j.val = j'.val

lemma yvec_apply {nV : ℕ} (T : Fin nV → TupleData P πp) (hT : OffDisj T) (A : MatA) (v : Fin nV) (j : Fin (T v).nb) :
    yvec T A ((T v).off + j.val) = (T v).yc A j := by
  unfold yvec
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      rw [if_neg]
      intro h
      exact hj' (Fin.ext (hT v v j' j h).2)
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro v' _ hv'
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [if_neg]
    intro h
    exact hv' (hT v' v j' j h).1
  · intro h; exact absurd (Finset.mem_univ v) h

/-- **The coordinate representation** of every tuple's Gram form (`hcoord`). -/
theorem hcoord {nV : ℕ} (T : Fin nV → TupleData P πp) (hT : OffDisj T) (h : Intertw P πp) (A : MatA) (v : Fin nV) :
    gram P.fam (T v).τ (Yp A) = ∑ j, yvec T A ((T v).off + j.val) • ((T v).W * (T v).S j * (T v).Wᵀ) := by
  rw [(T v).coords h A]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [yvec_apply T hT A v j]

end NPT.CP3
