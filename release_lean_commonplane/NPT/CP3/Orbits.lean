/-
NPT.CP3.Orbits — the orbit data of the certificate (`NPT.CP3.OrbitData` of `Fsem.lean`) and the facts that
`fsem_sound0`, `fsem_sound3` and `sum_coord` need at the projected moment `Yp A` with `y = yvec T A`.
-/
import NPT.CP3.Fsem
import NPT.CP3.Cosets

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-- **The orbit data of the certificate**: the 175 sorted tuples, their coordinates and their cosets. -/
@[reducible] noncomputable def Dcp : OrbitData where
  nv := 175
  tup := fun v => tupF v
  m := fun v => (vb v).S.length
  off := fun v => (vb v).off
  WSW := fun v j => Wc v * cq' (Sq v j) * (Wc v)ᵀ
  nc := fun v => ncos v
  new := fun v c => newT v c
  perm := fun v c => permT v c

theorem Dcp_cos : Dcp.CosOK := fun v c => funext fun l => (cos_ok v v.isLt c c.isLt).1 l

theorem Dcp_inj : Function.Injective Dcp.newOf := newSig_inj

theorem Dcp_out (Y : Matrix GC GC ℂ) :
    ∀ τ : Tup (PD 0).fam, (∀ x, Dcp.newOf x ≠ τ) → gram (PD 0).fam τ Y = 0 :=
  fun τ h => gram_out τ (fun v hv c hc he => h ⟨⟨v, hv⟩, ⟨c, hc⟩⟩ he) Y

theorem Dcp_coord (A : MatA) :
    ∀ v, gram (PD 0).fam (Dcp.tup v) (Yp A) = ∑ j : Fin (Dcp.m v), yvec T A (Dcp.off v + j.val) • Dcp.WSW v j :=
  fun v => hcoordT A v

theorem Dcp_le : ∀ v, Dcp.off v + Dcp.m v ≤ 1331 := fun v => off_le v v.isLt

/-- The coset permutations are the lists of the data (`sOf` of the D1 check). -/
theorem Dcp_perm (v : Fin Dcp.nv) (c : Fin (Dcp.nc v)) (m : Fin 4) :
    (Dcp.perm v c m).val = (cosE v c).2.getD m.val m.val := (cos_ok v v.isLt c c.isLt).2 m

end NPT.CP3.Inst
