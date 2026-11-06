import NPT.CP3.Chk.AllD0
import NPT.CP3.SemD0

/-!
# NPT.CP3.ChecksD0 — the variable-block facts used by the coordinate semantics

`d0_ok`: for every sorted cut-`()` tuple `v < 175` (the 150 variable blocks, then the 25 tuples whose `W` has no
columns), `NPT.CP3.Sem.D0Facts v`: left inverse `Wl v * Wq v = 1`; `Π_σ W = W B_σ` for the listed stabilizer; the list
`stab` is the whole stabilizer of `st`; `Σ_σ B_σ E_ab B_σᵀ = |stab| Σ_j c_j S_j`; the cosets form a transversal. From the
kernel checks in `NPT.CP3.Chk.D0*` through `NPT.CP3.SemD0`.
-/

namespace NPT.CP3

open NPT.CP3.Sem NPT.CP3.Chk

theorem d0_ok : ∀ v < 175, D0Facts v := d0_of_checks d0_all

end NPT.CP3
