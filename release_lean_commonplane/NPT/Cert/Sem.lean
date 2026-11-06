/-
NPT.Cert.Sem — the semantic target of the EP_k certificate check (ep3core semantics, generic in `k`).

This file fixes, in Lean, the functional `Λ_f(w)` whose orbit sums the identity check must show to vanish
. Data are list-based (exported); the definitions read them through
`getD` accessors. Conventions are ep3core's:
* factors `l : Fin (k+1)`: sites `l < k` (local dimension `d`), auxiliary qubit `l = k` (local dimension 2);
* words `w : Fin (k+1) → Fin 24` (PERMS in itertools order, `NPT.Brauer.permL`), `V_p = VG 0 p` (perm_op);
* digit strings are flattened base `n`, digit 0 most significant (ep3core `undigits`);
* module multi-indices are flattened mixed radix over `l = 0..k`, `l = 0` most significant.
-/
import NPT.Cert.BrauerTab
import NPT.Cert.PsdCheck

open Matrix BigOperators Finset NPT.Brauer

namespace NPT.Cert.Sem

/-! ### Indices -/

/-- Local dimension of factor `l`: `d` for the sites `l < k`, `2` for the auxiliary qubit `l = k`. -/
def nf (k d : ℕ) (l : Fin (k + 1)) : ℕ := if l.val < k then d else 2

/-- Flat index of a digit string (base `n`, digit 0 most significant). -/
def flat {n m : ℕ} (x : Fin m → Fin n) : ℕ := ∑ s : Fin m, (x s).val * n ^ (m - 1 - s.val)

/-- Flat mixed-radix index of a module multi-index (`l = 0` most significant). -/
def flatMI {k : ℕ} (dims : Fin (k + 1) → ℕ) (μ : (l : Fin (k + 1)) → Fin (dims l)) : ℕ :=
  ∑ l : Fin (k + 1), (μ l).val * ∏ l' : Fin (k + 1), (if l.val < l'.val then dims l' else 1)

/-- Module matrix from list data: rows = flat digit index (`m` replicas, base `n`), columns = coordinates. -/
def Jm (n m : ℕ) (J : List (List Int)) (dim : ℕ) : Matrix (Fin m → Fin n) (Fin dim) ℚ :=
  fun x μ => (((J.getD (flat x) []).getD μ.val 0 : ℤ) : ℚ)

/-! ### Local operators -/

/-- Entry-rule operator (ep3core `entry_op`): `ruleOp M [i; j] = M[k; l]`, where `k_s` is the digit at
position `kpos s` of `(i, j)` (codes `t < 4`: i-slot `t`; `4 + t`: j-slot `t`), `l` likewise. -/
def ruleOp {n : ℕ} (kpos lpos : Fin 4 → Fin (4 + 4))
    (M : Matrix (Fin 4 → Fin n) (Fin 4 → Fin n) ℚ) : Matrix (Fin 4 → Fin n) (Fin 4 → Fin n) ℚ :=
  fun i j => M (Fin.append i j ∘ kpos) (Fin.append i j ∘ lpos)

/-- Position code from data (`('i', t) ↦ t`, `('j', t) ↦ 4 + t`). -/
def posOf (xs : List ℕ) (s : Fin 4) : Fin (4 + 4) := Fin.ofNat (4 + 4) (xs.getD s.val 0)

/-- Local block map `Jᵀ · ruleOp(V_p) · J` (ep3core `local_rows`, row `p`). -/
def Kmat (n : ℕ) (J : List (List Int)) (dim : ℕ) (kpos lpos : List ℕ) (p : Fin 24) :
    Matrix (Fin dim) (Fin dim) ℚ :=
  (Jm n 4 J dim)ᵀ * ruleOp (posOf kpos) (posOf lpos) (VG ℚ n 0 p) * Jm n 4 J dim

/-- Survivor relabelling: old replica `t ≠ slot` sits at new position `order⁻¹ t`. -/
def insAt {n : ℕ} (slot : ℕ) (order : List ℕ) (i : Fin 3 → Fin n) (z : Fin n) : Fin 4 → Fin n :=
  fun t => if t.val = slot then z else i (Fin.ofNat 3 (order.idxOf t.val))

/-- Partial trace over replica `slot`, survivors relabelled by `order` (ep3core `tr_replica`). -/
def trSlot {n : ℕ} [NeZero n] (slot : ℕ) (order : List ℕ) (M : Matrix (Fin 4 → Fin n) (Fin 4 → Fin n) ℚ) :
    Matrix (Fin 3 → Fin n) (Fin 3 → Fin n) ℚ :=
  fun i j => ∑ z : Fin n, M (insAt slot order i z) (insAt slot order j z)

/-- Survivors of `slot` in natural order. -/
def natOrder (slot : ℕ) : List ℕ := (List.range 4).filter (· ≠ slot)

/-- Restriction of a 4-replica digit string to the survivors of `slot` (natural order). -/
def restr {n : ℕ} (slot : ℕ) (i : Fin 4 → Fin n) : Fin 3 → Fin n :=
  fun u => i (Fin.ofNat 4 ((natOrder slot).getD u.val 0))

/-- Stiefel contrast on the auxiliary qubit: `2 M − I_slot ⊗ Tr_slot M` (ep3core `stiefel_aux`). -/
def stief (slot : ℕ) (M : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℚ) :
    Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℚ :=
  fun i j => 2 * M i j -
    (if i (Fin.ofNat 4 slot) = j (Fin.ofNat 4 slot) then
      trSlot slot (natOrder slot) M (restr slot i) (restr slot j) else 0)

/-! ### Certificate data (list form; exported) -/

/-- A module: local dimension `n`, number of replicas `m` (4, or 3 for `eq3` modules), dimension, matrix. -/
structure ModD where
  n : ℕ
  m : ℕ
  dim : ℕ
  J : List (List Int)
  deriving Inhabited

/-- One entry `(r, s)` of a multiplier type: family (0 = '31', 1 = '22', 2 = '13') and the entry rule. -/
structure RuleD where
  fam : ℕ
  kpos : List ℕ
  lpos : List ℕ
  deriving Inhabited

/-- A multiplier type (ep3core `types[t]`). Row patterns `pat[r][slot]`: 0 = a, 1 = a*, 2 = b, 3 = b*. -/
structure TypeD where
  nrows : ℕ
  pat : List (List ℕ)
  cut : ℕ
  mods : List ℕ
  W : List (List Int)
  rules : List (List RuleD)
  zi : ℕ
  deriving Inhabited

/-- One factor of an equality part: traced slot, survivor order, kind (0 = del, 1 = stiefel_aux), modules. -/
structure EqSpecD where
  slot : ℕ
  order : List ℕ
  kind : ℕ
  mkeys : List ℕ
  deriving Inhabited

structure EqPartD where
  fam : ℕ
  sign : ℤ
  specs : List EqSpecD
  deriving Inhabited

/-- An equality group: parts and multipliers `λ[o] = num / lamDen` (`o` = one stacked-row index per
factor; `lamDen` is global, in `CertD`). -/
structure EqGroupD where
  parts : List EqPartD
  lam : List (List ℕ × ℤ)
  deriving Inhabited

/-- A complete certificate at `(k, d)`. `Z` is the PSD block list (same objects as the PSD fact). -/
structure CertD where
  k : ℕ
  d : ℕ
  types : List TypeD
  mods : List ModD
  eqs : List EqGroupD
  Z : List NPT.Cert.PBlock
  Lden : ℕ
  lamDen : ℕ

/-! ### The functional -/

namespace CertD

variable (C : CertD)

/-- Exact multiplier entry `Z_t[a, b]` (rational form of `PBlock.Zmat`). -/
def zq (b : NPT.Cert.PBlock) (Lden : ℕ) (i j : ℕ) : ℚ := (b.zget i j : ℚ) / 2 ^ b.E + b.uval Lden i j

/-- Dimension of the module of type `t` at factor `l`. -/
def tdim (t : TypeD) (l : Fin (C.k + 1)) : ℕ := (C.mods.getD (t.mods.getD l.val 0) default).dim

/-- `B^t_{rs}[μ, ν] = (W_r Z_t W_sᵀ)[μ, ν]` at flat indices. -/
def Bq (t : TypeD) (r s μ ν : ℕ) : ℚ :=
  let nn := ∏ l, C.tdim t l
  let b := C.Z.getD t.zi default
  ∑ a ∈ range b.n, ∑ c ∈ range b.n,
    ((t.W.getD (r * nn + μ) []).getD a 0 : ℚ) * zq b C.Lden a c * ((t.W.getD (s * nn + ν) []).getD c 0 : ℚ)

/-- Block entry `blk(t, r, s, w) = Σ_{μν} B^t_rs[μ,ν] Π_l K_{t,l}(w l)[μ_l, ν_l]`. -/
def blk (t : TypeD) (r s : ℕ) (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  let R := (t.rules.getD r []).getD s default
  ∑ μ : (l : Fin (C.k + 1)) → Fin (C.tdim t l), ∑ ν : (l : Fin (C.k + 1)) → Fin (C.tdim t l),
    C.Bq t r s (flatMI (C.tdim t) μ) (flatMI (C.tdim t) ν) *
      ∏ l, Kmat (nf C.k C.d l) (C.mods.getD (t.mods.getD l.val 0) default).J (C.tdim t l)
        R.kpos R.lpos (w l) (μ l) (ν l)

/-- Objective (ep3core `objective_tensor`): sites `2 tr V_p − tr F03 V_p` at `n = d`, aux `tr F03 V_p` at
`n = 2`, divided by `2^k (2 d^k)^4`. `F03 = V_swap`, `swap = (3,1,2,0)` = PERMS index 21. -/
def obj (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  (∏ l : Fin C.k, (2 * trace (VG ℚ C.d 0 (w l.castSucc)) -
      trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 (w l.castSucc)))) *
    trace (VG ℚ 2 0 21 * VG ℚ 2 0 (w (Fin.last C.k))) / (2 ^ C.k * (2 * C.d ^ C.k) ^ 4)

/-- Stacked-row decoding of an equality row index `o` over the modules `mkeys`:
`(module position, μ, ν)` with blocks of `dim²` rows, row-major `μ·dim + ν`. -/
def eqDecode (mkeys : List ℕ) (o : ℕ) : ℕ × ℕ × ℕ :=
  let rec go (ms : List ℕ) (pos o : ℕ) : ℕ × ℕ × ℕ :=
    match ms with
    | [] => (pos, 0, 0)
    | m0 :: rest =>
      let dm := (C.mods.getD m0 default).dim
      if o < dm * dm then (pos, o / dm, o % dm) else go rest (pos + 1) (o - dm * dm)
  go mkeys 0 o

/-- Equality local map entry `E_{P,l}(p)[o]` (ep3core `eq_local`). -/
def eqLoc (sp : EqSpecD) (n : ℕ) (p : Fin 24) (o : ℕ) : ℚ :=
  let dec := C.eqDecode sp.mkeys o
  let md := C.mods.getD (sp.mkeys.getD dec.1 0) default
  if hμ : dec.2.1 < md.dim then if hν : dec.2.2 < md.dim then
    if sp.kind = 0 then
      if hn : n = 0 then 0 else
      haveI : NeZero n := ⟨hn⟩
      ((Jm n 3 md.J md.dim)ᵀ * trSlot sp.slot sp.order (VG ℚ n 0 p) * Jm n 3 md.J md.dim)
        ⟨dec.2.1, hμ⟩ ⟨dec.2.2, hν⟩
    else
      ((Jm 2 4 md.J md.dim)ᵀ * stief sp.slot (VG ℚ 2 0 p) * Jm 2 4 md.J md.dim) ⟨dec.2.1, hμ⟩ ⟨dec.2.2, hν⟩
  else 0 else 0

/-- Equality part value `Σ_o λ[o] Π_l E_{P,l}(w l)[o_l]`. -/
def eqVal (g : EqGroupD) (P : EqPartD) (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  (g.lam.map fun ol => ((ol.2 : ℚ) / C.lamDen) * ∏ l : Fin (C.k + 1),
    C.eqLoc (P.specs.getD l.val default) (nf C.k C.d l) (w l) (ol.1.getD l.val 0)).sum

/-- **The functional** `Λ_f(w) = [f=31]·obj(w) − Σ blk − Σ sign·eq` (family codes 0/1/2 = '31'/'22'/'13'). -/
def Λ (f : ℕ) (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  (if f = 0 then C.obj w else 0)
  - (C.types.map fun t => ∑ r ∈ range t.nrows, ∑ s ∈ range t.nrows,
        if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0).sum
  - (C.eqs.map fun g => (g.parts.map fun P =>
        if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum).sum

end CertD

/-! ### Orbits of words (ep3core `word_orbits`) and the identity fact -/

/-- Letters of the families (true = a): '31' = aaab, '22' = aabb, '13' = bbba. -/
def famLet (f : ℕ) : List Bool :=
  match f with
  | 0 => [true, true, true, false]
  | 1 => [true, true, false, false]
  | _ => [false, false, false, true]

/-- `g ∈ G_f` (ep3core `family_group`: `L[g[i]] = L[i]`). -/
def inG (f : ℕ) (g : Fin 24) : Bool :=
  (List.finRange 4).all fun i => (famLet f).getD (pf g i).val false == (famLet f).getD i.val false

/-- Index of the composition `compose(p, q) = p ∘ q`. -/
def mulIdx (p q : Fin 24) : Fin 24 :=
  Fin.ofNat 24 (permL.idxOf ((List.range 4).map fun i => (permL.getD p.val []).getD
    ((permL.getD q.val []).getD i 0) 0))

/-- Group element acting on words: site permutation `σ` (component `i` moves to `σ i`), then
`w_l ↦ g1 ∘ w_l ∘ g2` on every factor, then inversion if `ε`. -/
def act {k : ℕ} (g1 g2 : Fin 24) (σ : Fin k → Fin k) (ε : Bool) (w : Fin (k + 1) → Fin 24) :
    Fin (k + 1) → Fin 24 :=
  fun l =>
    let src : Fin (k + 1) := if h : l.val < k then
      (((List.finRange k).find? fun i => σ i = ⟨l.val, h⟩).getD ⟨0, by omega⟩).castSucc else l
    let x := mulIdx g1 (mulIdx (w src) g2)
    if ε then pinvIdx x else x

/-- **The identity fact** for a certificate: a class function per family whose classes have vanishing
`Λ`-sums, with, for every word, a group element (`g1, g2 ∈ G_f`, `σ` a permutation of the sites, `ε`)
moving it to the representative of its class. -/
structure IdFact (C : CertD) where
  cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ
  rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24)
  wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool
  hG : ∀ f < 3, ∀ w, inG f (wit f w).1 = true ∧ inG f (wit f w).2.1 = true
  hσ : ∀ f < 3, ∀ w, Function.Bijective (wit f w).2.2.1
  hrep : ∀ f < 3, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w)
  hsum : ∀ f < 3, ∀ w₀, ∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), C.Λ f w = 0

end NPT.Cert.Sem
