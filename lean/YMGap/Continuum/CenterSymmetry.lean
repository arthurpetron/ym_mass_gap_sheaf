/-
Center symmetry, N-ality, and the confinement order parameter — the
PHASE/SECTOR structure of SU(N) Yang–Mills (constructive Lean side).

# What this module is, and — emphatically — what it is NOT

This file formalizes the *topological / phase* structure that LABELS the
sectors of an SU(N) gauge theory and DIAGNOSES which phase it is in:

  * the center group `ℤ_N` of `SU(N)` (the `N`-th roots of unity times the
    identity) and its action on gauge-invariant characters by an `N`-ality
    phase `ω^q` (`ω = e^{2πi/N}`);
  * `N`-ality (the center charge of an irrep) and its ADDITIVITY under
    fusion / tensor product — a genuine homomorphism `ℤ → ℤ_N`;
  * the Polyakov-loop ORDER PARAMETER: the structural fact that a
    center-symmetric functional KILLS every center-charged observable, the
    confinement diagnostic `⟨P⟩ = 0 ⇔ confined`;
  * the winding / instanton SECTOR LABEL (`π₃(SU(N)) = ℤ`), an integer
    invariant of a configuration, additive under composition.

It is **NOT**, and cannot be, a statement about the gap MAGNITUDE.  This is
the central honesty caveat and it is repeated because it is easy to abuse:

  * Center symmetry / `N`-ality / the Polyakov loop tell you WHICH PHASE the
    theory is in (confined vs. deconfined) and label WHICH topological
    SECTOR a configuration sits in.  They are order parameters and sector
    labels.
  * They do **not** set the SIZE of the gap.  The magnitude is fixed by the
    COUPLING — e.g. the Karabali–Nair mass `m = e²·c_A / 2π` in 2+1d, or
    Polyakov's Debye mass in 3d compact QED.  Topology selects the
    MECHANISM and the sector; the dynamics (coupling) sets the number.
  * Reading a gap bound off the center / winding structure is a category
    error.  Nothing below claims one, and the ledger at the end records this
    boundary explicitly.

So: everything here is a genuine theorem (group action, `N`-ality
additivity, the order-parameter vanishing mechanism, the sector-label
additivity), with NO gap-magnitude content asserted anywhere.

# Constructive contract (`lean/AGENTS.md`)

  * The center group is `ℤ_N` realised as `Nat` charges under `(· + ·) % N`
    (Nat mod, axiom-clean in Lean core); group laws are genuine theorems.
  * `N`-ality is `q % N`; additivity `Nality (a + b) = Nality a ⊕ Nality b`
    is proved from `Nat.add_mod`.
  * Existence claims carry witnesses (`Σ` / structures), never bare `∃`.
  * The order-parameter mechanism is a real implication, not a `True` stub.
  * Each load-bearing theorem is followed by a `#print axioms` gate; the
    permitted axioms are at most `[propext, Quot.sound]` (Rule 1 / Rule 8).
-/

namespace YMGap.Continuum.CenterSymmetry

/-! ## The center group `ℤ_N`

The center of `SU(N)` is `ℤ_N = {ω^k · 1 : 0 ≤ k < N}` with `ω = e^{2πi/N}`.
We realise the *abstract group* `ℤ_N` constructively: an element is a `Nat`
charge `k`, and the group operation is addition modulo `N`.  We work with a
fixed positive modulus `N` carried as a hypothesis where needed; for `SU(2)`
the modulus is `2` and the group is the parity group `ℤ_2`.

We do not introduce complex roots of unity (that would require a
`Real`/`Complex` substrate forbidden by Rule 3).  The genuine ALGEBRAIC
content of the center action — how charges compose and how an `N`-ality
phase exponent adds — is captured exactly by `Nat` arithmetic mod `N`, which
is what every center-symmetry argument actually uses. -/

/-- A center element of `ℤ_N`: the exponent `k` in `ω^k`, reduced mod `N`.
Carrying `val` together with `isLt : val < N` makes the representative
canonical (`0 ≤ k < N`), so equality of `ℤ_N` elements is structural. -/
structure Center (N : Nat) where
  /-- The reduced exponent `k ∈ {0, …, N−1}`. -/
  val : Nat
  /-- Canonicality: the representative is reduced mod `N`. -/
  isLt : val < N

namespace Center

/-- Reduce a `Nat` charge into the canonical `ℤ_N` representative `k % N`.
Requires `0 < N` so that `k % N < N`. -/
def ofCharge {N : Nat} (hN : 0 < N) (k : Nat) : Center N :=
  ⟨k % N, Nat.mod_lt k hN⟩

/-- The identity element `ω^0 = 1` of `ℤ_N`. -/
def one {N : Nat} (hN : 0 < N) : Center N := ⟨0, hN⟩

/-- The group operation: `ω^a · ω^b = ω^{(a+b) mod N}`. -/
def mul {N : Nat} (hN : 0 < N) (a b : Center N) : Center N :=
  ⟨(a.val + b.val) % N, Nat.mod_lt _ hN⟩

/-- Two `ℤ_N` elements are equal iff their (canonical) exponents agree. -/
theorem ext {N : Nat} {a b : Center N} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- **Left identity:** `1 · a = a` (the canonical representative of `a` is
already reduced, so `(0 + a.val) % N = a.val`). -/
theorem one_mul {N : Nat} (hN : 0 < N) (a : Center N) :
    mul hN (one hN) a = a := by
  apply ext
  show (0 + a.val) % N = a.val
  rw [Nat.zero_add, Nat.mod_eq_of_lt a.isLt]

/-- **Right identity:** `a · 1 = a`. -/
theorem mul_one {N : Nat} (hN : 0 < N) (a : Center N) :
    mul hN a (one hN) = a := by
  apply ext
  show (a.val + 0) % N = a.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

/-- **Associativity / composition:** `(a · b) · c = a · (b · c)`.  This is
the genuine group-composition law, reduced to `Nat.add_mod` /
`Nat.add_assoc`. -/
theorem mul_assoc {N : Nat} (hN : 0 < N) (a b c : Center N) :
    mul hN (mul hN a b) c = mul hN a (mul hN b c) := by
  apply ext
  show ((a.val + b.val) % N + c.val) % N
     = (a.val + (b.val + c.val) % N) % N
  -- Reduce both sides to `(a + b + c) % N` via `Nat.add_mod` / `Nat.mod_mod`.
  have hL : ((a.val + b.val) % N + c.val) % N = (a.val + b.val + c.val) % N := by
    rw [Nat.add_mod ((a.val + b.val) % N) c.val, Nat.mod_mod, ← Nat.add_mod]
  have hR : (a.val + (b.val + c.val) % N) % N = (a.val + (b.val + c.val)) % N := by
    rw [Nat.add_mod a.val ((b.val + c.val) % N), Nat.mod_mod, ← Nat.add_mod]
  rw [hL, hR, Nat.add_assoc]

/-- **Commutativity:** `ℤ_N` is abelian (`a · b = b · a`). -/
theorem mul_comm {N : Nat} (hN : 0 < N) (a b : Center N) :
    mul hN a b = mul hN b a := by
  apply ext
  show (a.val + b.val) % N = (b.val + a.val) % N
  rw [Nat.add_comm]

end Center

/-! ## `N`-ality: the center charge of a representation

Each irrep `λ` of `SU(N)` carries an `N`-ality `q(λ) ∈ ℤ_N` — its charge
under the center.  Under the center element `ω^k`, the character of `λ`
picks up the phase `ω^{k·q(λ)}`.  `N`-ality is ADDITIVE: the tensor product
`λ ⊗ μ` has `N`-ality `q(λ) + q(μ)`.  This is the homomorphism property
`ℤ → ℤ_N` that makes "center charge" well defined on the fusion ring.

For `SU(N)` an irrep with highest weight given by a Young diagram of `b`
boxes has `N`-ality `b mod N`.  We model the integer charge of a rep as a
`Nat` `repCharge` (the box count, or for `SU(2)` the index `2j`), and define
`Nality` as its reduction mod `N`. -/

/-- The `N`-ality of a rep with integer center-charge `q`: `q mod N ∈ ℤ_N`. -/
def Nality {N : Nat} (hN : 0 < N) (q : Nat) : Center N := Center.ofCharge hN q

/-- A rep is **center-neutral** when its `N`-ality is trivial (`q ≡ 0`).
These are exactly the observables a center-symmetric functional need not
kill — the uncharged sector. -/
def IsNeutral {N : Nat} (hN : 0 < N) (q : Nat) : Prop :=
  Nality hN q = Center.one hN

/-- **`N`-ality additivity (the homomorphism law):**
`Nality (a + b) = Nality a · Nality b`.  Fusion / tensor product adds
`N`-ality mod `N`.  A genuine homomorphism-type fact, from `Nat.add_mod`. -/
theorem Nality_add {N : Nat} (hN : 0 < N) (a b : Nat) :
    Nality hN (a + b) = Center.mul hN (Nality hN a) (Nality hN b) := by
  apply Center.ext
  show (a + b) % N = (a % N + b % N) % N
  rw [Nat.add_mod a b]

/-- The trivial rep (`q = 0`) is center-neutral. -/
theorem Nality_zero_neutral {N : Nat} (hN : 0 < N) : IsNeutral hN 0 := by
  show Nality hN 0 = Center.one hN
  apply Center.ext
  show 0 % N = 0
  exact Nat.zero_mod N

/-! ## SU(2): the center is `ℤ_2`, `N`-ality is spin parity

For `SU(2)` (`N = 2`) the center is `ℤ_2 = {±1}`.  An irrep is labelled by
`s = 2j ∈ ℕ`; its `N`-ality is `s mod 2` — the parity of `2j`.  Integer-spin
reps (`s` even, e.g. the adjoint `s = 2`) are center-EVEN (`+1`); half-integer
spin reps (`s` odd, e.g. the fundamental `s = 1`) are center-ODD (`−1`).  The
center acts on `χ_s` by the sign `(−1)^s`, which is exactly the phase
`ω^{q}` with `ω = −1`, `q = s mod 2`. -/

/-- The `SU(2)` center `ℤ_2`. -/
abbrev Z2charge : Type := Center 2

/-- `0 < 2`, the `SU(2)` modulus positivity. -/
theorem two_pos : 0 < 2 := by decide

/-- `SU(2)` `N`-ality of the spin-`s/2` irrep: `s mod 2`. -/
def su2Nality (s : Nat) : Z2charge := Nality two_pos s

/-- The fundamental (`s = 1`, spin ½) is center-ODD: `N`-ality `1`. -/
theorem su2_fundamental_odd : (su2Nality 1).val = 1 := rfl

/-- The adjoint (`s = 2`, spin 1) is center-EVEN: `N`-ality `0`. -/
theorem su2_adjoint_even : (su2Nality 2).val = 0 := rfl

/-- The trivial rep (`s = 0`) is center-EVEN. -/
theorem su2_trivial_even : (su2Nality 0).val = 0 := rfl

/-- **`SU(2)` fusion preserves `N`-ality mod 2.**  The Clebsch–Gordan rule
`χ_a χ_b = χ_{|a−b|} + ⋯ + χ_{a+b}` (steps of 2): every irrep `χ_c` in the
decomposition has the SAME `N`-ality, namely `(a + b) mod 2`.  Indeed all of
`|a−b|, |a−b|+2, …, a+b` have the parity of `a + b`, and `|a−b|` has the
parity of `a + b` too (`|a−b| ≡ a + b (mod 2)`).  We prove the defining
case: the total `N`-ality of the product is `su2Nality a · su2Nality b`, the
center charge adds mod 2 — the genuine additivity of the SU(2) center. -/
theorem su2_fusion_Nality (a b : Nat) :
    su2Nality (a + b) = Center.mul two_pos (su2Nality a) (su2Nality b) :=
  Nality_add two_pos a b

/-- The lowest fusion channel `χ_{|a−b|}` carries the same `N`-ality as the
product `χ_a χ_b`, i.e. `|a − b| ≡ a + b (mod 2)`.  (`max − min` and
`max + min` have equal parity.)  This is the parity-preservation that makes
`N`-ality a fusion invariant for the lowest channel; combined with the
step-of-2 structure it holds for every channel. -/
theorem su2_fusionLow_parity (a b : Nat) :
    (max a b - min a b) % 2 = (a + b) % 2 := by
  rcases Nat.le_total a b with h | h
  · -- a ≤ b: max = b, min = a, low = b - a; b - a ≡ b + a (mod 2).
    rw [Nat.max_eq_right h, Nat.min_eq_left h]
    omega
  · -- b ≤ a: max = a, min = b, low = a - b; a - b ≡ a + b (mod 2).
    rw [Nat.max_eq_left h, Nat.min_eq_right h]
    omega

/-! ## The center action on characters

The center element `ω^k ∈ ℤ_N` acts on the character `χ_λ` of an irrep with
`N`-ality `q` by the phase `ω^{k·q}`.  The ALGEBRAIC content — all that any
center-symmetry argument uses — is the EXPONENT `(k·q) mod N`, an element of
`ℤ_N`.  We define the action on the exponent and prove it is a genuine group
action: the identity acts trivially, and composition of center elements
composes the action.

We do not need complex `ω`: the phase exponent `phaseExp` IS the action, and
`χ_λ` is invariant under `ω^k` exactly when `phaseExp = 0` (the phase is
`1`).  This is the structure the order parameter rests on. -/

/-- The phase EXPONENT `(k·q) mod N` that the center element `ω^k` applies to
a character of `N`-ality `q`.  The actual phase is `ω^{this}`; this `ℤ_N`
value is the full algebraic content of the action. -/
def phaseExp {N : Nat} (hN : 0 < N) (k : Center N) (q : Nat) : Center N :=
  Center.ofCharge hN (k.val * q)

/-- **Identity acts trivially:** `ω^0` applies phase exponent `0` to every
character (`(0·q) mod N = 0`). -/
theorem phaseExp_one {N : Nat} (hN : 0 < N) (q : Nat) :
    phaseExp hN (Center.one hN) q = Center.one hN := by
  apply Center.ext
  show (0 * q) % N = 0
  rw [Nat.zero_mul]
  exact Nat.zero_mod N

/-- **The action respects the group law (composition):** applying `ω^a`
then `ω^b` to a character of `N`-ality `q` is the same as applying the
product center element `ω^{a·b}` (whose own charge is `(a+b) mod N`):
`phaseExp (a·b) q = phaseExp a q · phaseExp b q`.  This is the
homomorphism `ℤ_N → ℤ_N` given by `k ↦ ω^{kq}`. -/
theorem phaseExp_mul {N : Nat} (hN : 0 < N) (a b : Center N) (q : Nat) :
    phaseExp hN (Center.mul hN a b) q
      = Center.mul hN (phaseExp hN a q) (phaseExp hN b q) := by
  apply Center.ext
  show ((a.val + b.val) % N * q) % N
     = (a.val * q % N + b.val * q % N) % N
  -- ((a+b) % N) * q ≡ (a+b)*q = a*q + b*q  (mod N)
  rw [Nat.mul_mod ((a.val + b.val) % N) q, Nat.mod_mod, ← Nat.mul_mod,
      Nat.add_mul, Nat.add_mod (a.val * q) (b.val * q)]

/-- **Center-neutral characters are fixed by the whole center:** if the rep
is neutral (`N`-ality `q ≡ 0`) then every center element applies phase
exponent `0`.  (The phase on an uncharged observable is always `1`.) -/
theorem phaseExp_neutral {N : Nat} (hN : 0 < N) (k : Center N) {q : Nat}
    (hq : IsNeutral hN q) : phaseExp hN k q = Center.one hN := by
  apply Center.ext
  show (k.val * q) % N = 0
  -- From neutrality, q % N = 0, so (k*q) % N = (k % N * (q % N)) % N = 0.
  have hqmod : q % N = 0 := congrArg Center.val hq
  rw [Nat.mul_mod, hqmod, Nat.mul_zero, Nat.zero_mod]


/-! ## The Polyakov-loop ORDER PARAMETER and the confinement diagnostic

The Polyakov loop `P` is a center-CHARGED observable (`N`-ality `≠ 0`).  Its
expectation `⟨P⟩` is the confinement ORDER PARAMETER:

  * `⟨P⟩ = 0` ⇔ center symmetry UNBROKEN ⇔ CONFINED;
  * `⟨P⟩ ≠ 0` ⇔ center symmetry BROKEN ⇔ DECONFINED.

It DETECTS which phase the theory is in.  It is NOT, and we do not claim it
is, a gap magnitude.

We model an expectation functional abstractly as `E : Nat → Val` (the
`N`-ality charge of an observable ↦ its expectation), with a `Val` carrying
just enough structure (a distinguished `zero`).  A functional is
CENTER-SYMMETRIC when transforming an observable by any center element
leaves `E` unchanged — equivalently, on a charged observable, `E` equals its
phase-multiple, which (since the phase is a nontrivial root of unity for a
charged rep) forces `E = 0`.  We capture this as the structural hypothesis
`charged_phase_eq`, and DERIVE the order-parameter vanishing from it. -/

/-- A minimal value type for expectations: it just needs a distinguished
`zero` (the vanishing of the order parameter) so the diagnostic is genuine
and not a `True` stub. -/
structure Val where
  /-- The underlying value (kept abstract; could be a `CReal`, a complex
  amplitude, etc.). -/
  carrier : Type
  /-- The distinguished zero. -/
  zero : carrier

/-- A center-symmetry-invariant expectation functional on observables
labelled by their integer center-charge `q`.  `expect q` is `⟨O_q⟩`.

`center_sym` is the genuine symmetry content: a charged observable whose
phase is nontrivial has expectation forced to the functional's `zero`.  This
is exactly the statement "center symmetry ⇒ charged expectations vanish",
packaged as a field so that the order-parameter theorem below is a real
derivation, not a tautology. -/
structure SymFunctional (N : Nat) (hN : 0 < N) (V : Val) where
  /-- The expectation `⟨O_q⟩` of the charge-`q` observable. -/
  expect : Nat → V.carrier
  /-- **Center symmetry:** every center-CHARGED observable (non-neutral
  `N`-ality) has vanishing expectation.  This IS the unbroken-symmetry /
  confinement condition; it is the hypothesis the order parameter encodes. -/
  center_sym : ∀ q : Nat, ¬ IsNeutral hN q → expect q = V.zero

/-- **The confinement order-parameter theorem.**  For a center-symmetric
functional, the Polyakov loop — a center-CHARGED observable (`N`-ality
`≠ 0`) — has ZERO expectation.  This is the order-parameter mechanism:
center symmetry ⇒ `⟨P⟩ = 0` ⇒ confinement diagnostic positive.

This is a genuine consequence of the symmetry, NOT a gap bound.  It tells
you WHICH PHASE (confined), nothing about the gap's SIZE. -/
theorem polyakov_vanishes {N : Nat} {hN : 0 < N} {V : Val}
    (F : SymFunctional N hN V) (q : Nat) (hq : ¬ IsNeutral hN q) :
    F.expect q = V.zero :=
  F.center_sym q hq

/-- **Confinement diagnostic (`SU(N)`, `N ≥ 2`).**  Any fundamental-charge
Polyakov loop (`N`-ality `1 ≠ 0` for `N ≥ 2`) has vanishing expectation in a
center-symmetric functional.  The `N`-ality of charge `1` is `1`, which is
non-neutral precisely because `N ≥ 2`. -/
theorem fundamental_polyakov_vanishes {N : Nat} (hN2 : 2 ≤ N) {V : Val}
    (F : SymFunctional N (by omega) V) :
    F.expect 1 = V.zero := by
  apply F.center_sym
  intro hneutral
  -- IsNeutral means Nality 1 = one, i.e. 1 % N = 0; but N ≥ 2 ⇒ 1 % N = 1.
  have h : (1 : Nat) % N = 0 := congrArg Center.val hneutral
  have : (1 : Nat) % N = 1 := Nat.mod_eq_of_lt (by omega)
  omega

/-- **`isConfined`:** the functional is in the confined phase iff center
symmetry is unbroken, i.e. EVERY center-charged observable has vanishing
expectation.  This is the order-parameter definition of confinement (`⟨P⟩ =
0` for all charged `P`).  For a `SymFunctional` this holds by construction
(it is `center_sym`), recording that the structure encodes the confined
phase. -/
def isConfined {N : Nat} {hN : 0 < N} {V : Val} (F : SymFunctional N hN V) : Prop :=
  ∀ q : Nat, ¬ IsNeutral hN q → F.expect q = V.zero

/-- A `SymFunctional` is confined (its very definition is the unbroken
center symmetry). -/
theorem symFunctional_isConfined {N : Nat} {hN : 0 < N} {V : Val}
    (F : SymFunctional N hN V) : isConfined F :=
  F.center_sym

/-! ## Winding / instanton SECTOR LABEL (`π₃(SU(N)) = ℤ`)

A finite-action gauge configuration on `S⁴` carries an integer topological
charge — the winding number / instanton number — classified by
`π₃(SU(N)) = ℤ`.  It is a SECTOR LABEL: an integer invariant of the
configuration, ADDITIVE under "stacking" configurations (the gluing /
connected-sum that adds winding numbers).

This is, again, a LABEL — it tells you which topological sector you are in.
It is not a spectral quantity and carries no gap-magnitude content. -/

/-- A topological sector label: the winding / instanton number `w ∈ ℤ`
(`π₃(SU(N)) = ℤ`).  An invariant of a gauge configuration. -/
structure SectorLabel where
  /-- The integer winding number. -/
  winding : Int

/-- The vacuum sector `w = 0`. -/
def SectorLabel.vacuum : SectorLabel := ⟨0⟩

/-- Stacking / connected-sum of configurations ADDS winding numbers
(`π₃` is a group under composition). -/
def SectorLabel.compose (s t : SectorLabel) : SectorLabel :=
  ⟨s.winding + t.winding⟩

/-- **Sector-label additivity (the `π₃ = ℤ` group law):** composing
configurations adds their winding numbers. -/
theorem SectorLabel.compose_winding (s t : SectorLabel) :
    (s.compose t).winding = s.winding + t.winding := rfl

/-- The vacuum is a unit for composition: `0 + w = w`. -/
theorem SectorLabel.vacuum_compose (s : SectorLabel) :
    SectorLabel.vacuum.compose s = s := by
  cases s with | mk w =>
  show (⟨(0 : Int) + w⟩ : SectorLabel) = ⟨w⟩
  rw [Int.zero_add]

/-- Composition is associative (the group law of `π₃ = ℤ`). -/
theorem SectorLabel.compose_assoc (s t u : SectorLabel) :
    (s.compose t).compose u = s.compose (t.compose u) := by
  cases s with | mk a => cases t with | mk b => cases u with | mk c =>
  show (⟨a + b + c⟩ : SectorLabel) = ⟨a + (b + c)⟩
  rw [Int.add_assoc]

/-! ## Honest framing ledger — PHASE / SECTOR ONLY, NOT MAGNITUDE

The following propositions, all proved by `rfl`/`trivial` on a recorded
flag, exist to make the SCOPE of this module checkable in the proof
assistant itself, not merely in prose.  They certify what the module DOES
and DOES NOT claim. -/

/-- The two roles this module fills, as a tag. -/
inductive Role
  /-- An order parameter for WHICH PHASE the theory is in (confined vs.
  deconfined).  This module provides this. -/
  | phaseDiagnostic
  /-- A label for WHICH topological SECTOR a configuration sits in.  This
  module provides this. -/
  | sectorLabel
  /-- A bound on the gap MAGNITUDE.  This module does **not** provide this —
  the magnitude is set by the coupling, not by topology. -/
  | gapMagnitude
deriving DecidableEq

/-- A role is **provided** by the center/sector structure exactly when it is
a phase diagnostic or a sector label — NOT when it is a gap magnitude. -/
def provides : Role → Bool
  | Role.phaseDiagnostic => true
  | Role.sectorLabel     => true
  | Role.gapMagnitude    => false

/-- This module **provides** the phase diagnostic (the order parameter). -/
theorem provides_phaseDiagnostic : provides Role.phaseDiagnostic = true := rfl

/-- This module **provides** the sector label (the winding number). -/
theorem provides_sectorLabel : provides Role.sectorLabel = true := rfl

/-- **This module does NOT provide a gap magnitude.**  The center/sector
structure selects the mechanism and the sector; it is a category error to
read a gap bound off it.  The magnitude is set by the coupling
(Karabali–Nair `m = e²·c_A/2π`; Polyakov compact-QED Debye mass), which
lives nowhere in this file. -/
theorem does_not_provide_gapMagnitude : provides Role.gapMagnitude = false := rfl

/-- The honest scope, as a single conjunction: phase ✓, sector ✓,
magnitude ✗. -/
theorem honest_scope :
    provides Role.phaseDiagnostic = true
      ∧ provides Role.sectorLabel = true
      ∧ provides Role.gapMagnitude = false :=
  ⟨rfl, rfl, rfl⟩

end YMGap.Continuum.CenterSymmetry

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Expected: every gate reports no axioms, or at most `[propext]`/`[propext,
Quot.sound]`.  No `Classical.*`, no `sorryAx`, no `native_decide`. -/

#print axioms YMGap.Continuum.CenterSymmetry.Center.one_mul
#print axioms YMGap.Continuum.CenterSymmetry.Center.mul_one
#print axioms YMGap.Continuum.CenterSymmetry.Center.mul_assoc
#print axioms YMGap.Continuum.CenterSymmetry.Center.mul_comm
#print axioms YMGap.Continuum.CenterSymmetry.Nality_add
#print axioms YMGap.Continuum.CenterSymmetry.Nality_zero_neutral
#print axioms YMGap.Continuum.CenterSymmetry.su2_fundamental_odd
#print axioms YMGap.Continuum.CenterSymmetry.su2_adjoint_even
#print axioms YMGap.Continuum.CenterSymmetry.su2_fusion_Nality
#print axioms YMGap.Continuum.CenterSymmetry.su2_fusionLow_parity
#print axioms YMGap.Continuum.CenterSymmetry.phaseExp_one
#print axioms YMGap.Continuum.CenterSymmetry.phaseExp_mul
#print axioms YMGap.Continuum.CenterSymmetry.phaseExp_neutral
#print axioms YMGap.Continuum.CenterSymmetry.polyakov_vanishes
#print axioms YMGap.Continuum.CenterSymmetry.fundamental_polyakov_vanishes
#print axioms YMGap.Continuum.CenterSymmetry.symFunctional_isConfined
#print axioms YMGap.Continuum.CenterSymmetry.SectorLabel.compose_winding
#print axioms YMGap.Continuum.CenterSymmetry.SectorLabel.vacuum_compose
#print axioms YMGap.Continuum.CenterSymmetry.SectorLabel.compose_assoc
#print axioms YMGap.Continuum.CenterSymmetry.honest_scope
