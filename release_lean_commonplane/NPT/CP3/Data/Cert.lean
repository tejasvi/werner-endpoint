import NPT.CP3.Data.Cert00
import NPT.CP3.Data.Cert01
import NPT.CP3.Data.Cert02
import NPT.CP3.Data.Cert03
import NPT.CP3.Data.Cert04

/-!
# NPT.CP3.Data.Cert — The certificate of the 302 active blocks, same order as `outs`.

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- The certificate of the 302 active blocks, same order as `outs`. -/
def certs : List CertB := cert00 ++ cert01 ++ cert02 ++ cert03 ++ cert04

end NPT.CP3.Data
