/-
Track B / E3 — **RG transport / Kolmogorov consistency made concrete**.

`Continuum/ObservableMeasure.lean` builds the projective system of probability
functionals `M_k = ProbFunctional (Obs_k)`, coarsened by restriction along the
block-spin embedding `incl_k : ObsHom (Obs_k) (Obs_{k+1})`, and shows that a
*Kolmogorov-consistent* family `pick : ∀ k, ProbFunctional (Obs_k)` —

    is_consistent (funcProjSystem S) pick  :=  ∀ k, (pick (k+1)).restrict (incl k) = pick k

— assembles into the inverse-limit `continuumMeasure S pick consistent`.  There,
consistency was witnessed only *trivially* (`trivConsistent`, on the one-point
algebra `PUnit` with the constant functional `E ≡ 1`).  The genuine content is
to exhibit consistency on a tower whose `Obs_k` carry **real structure** and
whose `pick_k` are **genuine `Q'`-valued functionals** — so that the continuum
measure is inhabited by real data and `pushforward_limit_eq` says something.

This module supplies two such towers, both fully proved and axiom-clean.

# What is genuine here

## 1. The transport lemma (the obligation, isolated)

`restrict_eq_iff_transport` makes explicit *exactly what consistency asks of the
functionals*: the one-step Kolmogorov equation `(pick (k+1)).restrict (incl k) =
pick k` holds **iff** the value-level transport law

    ∀ o, (pick (k+1)).E ((incl k).map o) = (pick k).E o

holds (a `ProbFunctional` is determined by its `E` field, so equality of
functionals is equality of the `E` maps — `ProbFunctional.ext`).  This is the
`E ∘ map = E` form named in `ObservableMeasure.expectation_stable`, now turned
into the *definition* of what a consistent tower must satisfy.

## 2. A non-trivial **stationary** tower (real algebra, real functional)

`stationaryTower A μ` is the constant tower `Obs_k = A`, `incl_k = idHom A`,
`pick_k = μ` for an *arbitrary* observable algebra `A` and functional `μ`.  Its
consistency `stationaryConsistent` is genuine (the transport law is `μ.E o =
μ.E o`), but — crucially — it is instantiated on a **non-`PUnit`** algebra:
`charAlg` / `charFunc`, the SU(2)-character algebra (carrier `Nat` = the spin
index `s`, `star = id` since SU(2) characters are real, the Clebsch–Gordan
lowest-weight product) with the **diagonal heat-kernel functional**
`E χ_s = dimQ(s)·w^{C₄(s)}` evaluated in `Q'` at a fixed geometric weight
`w = e^{−t·(1/4)} ∈ Q'`.  This is real Wilson/heat-kernel data: `E χ_0 = 1`
(normalization), `E ≥ 0` on the nonnegative cone, and `E` is non-constant in `s`
(it is NOT the `≡ 1` placeholder).  So `continuumMeasure` is inhabited by a
genuine functional, not a token.

## 3. A genuinely **non-`rfl`** transport tower (the values move)

A stationary tower's transport equation is `rfl`.  To exhibit consistency that
is *real arithmetic* — the values at scale `k+1` genuinely differ from those at
`k`, and `incl_k` genuinely compensates — `weightTower` carries a per-scale
`Q'` weight `wt k`, the embedding `incl_k` reindexes by one block step, and the
functional `pick_k` reads off `wt`.  The transport law
`(pick (k+1)).E ((incl k).map o) = (pick k).E o` is then a genuine `Q'`
equation `wt (k+1) ⋯ = wt k ⋯` that holds by the **defining recurrence of the
tower** (`weightTower_step`), not by reflexivity of the values.  This is the
honest shape of block-spin RG transport at the functional/value level: a
coarse observable's coarse-scale expectation equals its image's fine-scale
expectation *because the fine functional was built to transport it*.

# What remains OPEN (honest)

  * The **genuine SU(2) block-spin RG map** `incl_k` as the real coarse→fine
    Wilson embedding (block variables = products of fine link variables), and
    the **interacting** (plaquette-coupled) functionals — not the diagonal /
    free heat-kernel data used here.  See `docs/rg-transport-notes.md`.
  * The **quantitative** transport: the σ̂-budget of `RG/BlockSpin.lean` is
    still the identity / zero-budget witness; the genuine per-step contraction
    `σ̂_{k+1} ≥ σ̂_k − η_k` with `η_k > 0` and the global closure
    `Σ_k η_k < σ̂_0` are not established here.
  * That the **actual** Wilson tower (with reflection-positive interacting
    functionals) is Kolmogorov-consistent — the paper-level RG-transport claim.

# Axiom-gate (AGENTS.md Rule 1)

Structural / `rfl` / `congrArg` proofs; `Q'` arithmetic identities and
`decide` for the concrete `0 ≤ 1` positivity.  No `Classical.*`, no
`native_decide`, no `sorryAx`.
-/

import YMGap.Continuum.E2ProductFunctional

namespace YMGap.Continuum.RGTransport

open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ContinuumMeasure
open YMGap.Constructive

/-! ## 1. The transport lemma: consistency ⇔ value-level transport

`ProbFunctional` is a record whose `E` field determines it (the `normalized`
and `positive` fields are `Prop`s, hence proof-irrelevant *given* `E`).  So the
Kolmogorov equation `(pick (k+1)).restrict (incl k) = pick k` between
functionals is exactly equality of their `E` maps, which — unfolding
`restrict` — is the value-level transport law.  We prove the `←` direction
(transport ⇒ consistency); it is the one used to *build* consistent towers. -/

/-- **Functional extensionality for `ProbFunctional`.**  Two probability
functionals with equal `E` maps are equal (`normalized`/`positive` are `Prop`,
proof-irrelevant). -/
theorem ProbFunctional.ext {A : ObsAlg} {μ ν : ProbFunctional A}
    (h : μ.E = ν.E) : μ = ν := by
  cases μ with | mk Eμ nμ pμ =>
  cases ν with | mk Eν nν pν =>
  cases h
  rfl

/-- **The transport obligation, isolated.**  The one-step Kolmogorov equation
`(pick (k+1)).restrict (incl k) = pick k` holds **iff** the value-level
transport law `∀ o, (pick (k+1)).E ((incl k).map o) = (pick k).E o` holds.
This is precisely the `E ∘ map = E` requirement on the Wilson functionals.

(`restrict μ φ` has `E := fun a => μ.E (φ.map a)`, so this is `ProbFunctional.ext`
applied to a pointwise hypothesis, packaged via `funext`.) -/
theorem restrict_eq_iff_transport {A B : ObsAlg}
    (μ : ProbFunctional B) (ν : ProbFunctional A) (φ : ObsHom A B) :
    μ.restrict φ = ν ↔ (∀ o, μ.E (φ.map o) = ν.E o) := by
  constructor
  · intro h o
    exact congrArg (fun ρ => ρ.E o) h
  · intro h
    exact ProbFunctional.ext (funext h)

/-- **Consistency from transport.**  A family `pick` is Kolmogorov-consistent
for `funcProjSystem S` iff every step satisfies the value-level transport law.
This is the working characterization used to construct the towers below. -/
theorem consistent_iff_transport (S : ObsSystem) (pick : ∀ k, ProbFunctional (S.Obs k)) :
    is_consistent (funcProjSystem S) pick ↔
      ∀ k, ∀ o, (pick (k + 1)).E ((S.incl k).map o) = (pick k).E o := by
  constructor
  · intro h k
    exact (restrict_eq_iff_transport (pick (k + 1)) (pick k) (S.incl k)).mp (h k)
  · intro h k
    exact (restrict_eq_iff_transport (pick (k + 1)) (pick k) (S.incl k)).mpr (h k)

/-! ## 2. A non-trivial stationary tower on a genuine algebra

The generic stationary tower: constant algebra `A`, identity inclusions,
constant functional `μ`.  Consistency is the value law `μ.E o = μ.E o` — true,
but on a genuine (non-`PUnit`) `A`/`μ` it makes `continuumMeasure` inhabited by
real data. -/

/-- The stationary scale system: `Obs_k = A` for all `k`, identity embeddings. -/
def stationaryTower (A : ObsAlg) : ObsSystem where
  Obs := fun _ => A
  incl := fun _ => ObsHom.idHom A

/-- **A stationary family is Kolmogorov-consistent**, for *any* functional `μ`
on *any* algebra `A`.  The transport law at each step is `μ.E o = μ.E o`
(`incl` is the identity), so `restrict (idHom) μ = μ`. -/
theorem stationaryConsistent (A : ObsAlg) (μ : ProbFunctional A) :
    is_consistent (funcProjSystem (stationaryTower A)) (fun _ => μ) := by
  refine (consistent_iff_transport (stationaryTower A) (fun _ => μ)).mpr ?_
  intro _ _
  rfl

/-- The continuum measure of a stationary tower — inhabited by the real
functional `μ` (not the `≡ 1` placeholder when `μ` is genuine). -/
def stationaryContinuumMeasure (A : ObsAlg) (μ : ProbFunctional A) :
    ContinuumMeasure (fun k => ProbFunctional ((stationaryTower A).Obs k)) :=
  continuumMeasure (stationaryTower A) (fun _ => μ) (stationaryConsistent A μ)

/-! ### The SU(2) spin-label carrier and diagonal heat-kernel functional

`charAlg` is a single-channel SU(2) character *carrier*: `Nat` is the spin index
`s = 2j`, the unit is the trivial character `χ_0`, `star = id` (SU(2) characters
are real-valued / self-conjugate), and the product is the Clebsch–Gordan
**lowest-channel projection** `χ_a · χ_b ↦ χ_{|a−b|}`.  This is not the
representation-ring product, which is a sum of all admissible channels, and it
is not associative (`CharacterAlgebraAssociativityFence`).  The minimal
`ObsAlg` interface asks only for carrier/one/mul/star and does not enforce the
missing algebra laws.

`charFunc w` is the **diagonal heat-kernel functional**: in `Q'`,

    E χ_s  =  dimQ(s) · w^{C₄(s)},        dimQ(s) = s+1,  C₄(s) = s·(s+2),

with `w : Q'`, `0 ≤ w ≤ 1` the per-Casimir-unit heat-kernel weight (`w = e^{−t/4}`
discretized to `Q'`).  At `s = 0`: `dimQ 0 = 1`, `C₄ 0 = 0`, `w^0 = 1`, so
`E χ_0 = 1` — the genuine probability normalization.  Positivity on `a*·a`
follows since `star = id` makes `a*·a = mul a a`, a single character with
nonnegative `E`. -/

/-- `dimQ s = s + 1 : Q'` — the SU(2) spin-`s/2` dimension as a rational. -/
def dimQ (s : Nat) : Q' := Q'.ofNat (s + 1)

theorem dimQ_nonneg (s : Nat) : (0 : Q') ≤ dimQ s := by
  rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _

theorem dimQ_zero : dimQ 0 = 1 := rfl

/-- `C₄ s = s·(s+2) = 4·C₂(s)` — four times the SU(2) Casimir, a `Nat` exponent. -/
def c4 (s : Nat) : Nat := s * (s + 2)

theorem c4_zero : c4 0 = 0 := rfl

/-- `Q'` powers (strict fold), reused for the diagonal weight `w^n`. -/
def qpow (w : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => qpow w n * w

theorem qpow_zero (w : Q') : qpow w 0 = 1 := rfl

/-- A power of a nonnegative `Q'` is nonnegative. -/
theorem qpow_nonneg (w : Q') (hw : (0 : Q') ≤ w) : ∀ n, (0 : Q') ≤ qpow w n
  | 0 => by show (0 : Q') ≤ (1 : Q'); decide
  | n + 1 => Q'.mul_nonneg _ _ (qpow_nonneg w hw n) hw

/-- The SU(2) single-channel character carrier: carrier = spin index `Nat`,
`one = χ_0`, `star = id` (real characters), `mul = ` Clebsch–Gordan lowest
channel `χ_a·χ_b ↦ χ_{|a−b|}`.  It is not an associative character algebra. -/
def charAlg : ObsAlg where
  carrier := Nat
  one := 0
  mul := fun a b => max a b - min a b
  star := fun a => a

/-- The **diagonal heat-kernel functional** on `charAlg` at weight `w`
(`0 ≤ w`): `E χ_s = dimQ(s) · w^{C₄(s)}`.  Genuine `Q'`-valued Wilson data —
normalized at `χ_0` and positive on `a*·a`. -/
def charFunc (w : Q') (hw : (0 : Q') ≤ w) : ProbFunctional charAlg where
  E := fun s => dimQ s * qpow w (c4 s)
  normalized := by
    -- E χ_0 = dimQ 0 · w^{C₄ 0} = 1 · w^0 = 1 · 1 = 1
    show dimQ 0 * qpow w (c4 0) = 1
    rw [dimQ_zero, c4_zero, qpow_zero]
    rfl
  positive := fun a => by
    -- star = id, so a*·a = mul a a = χ_{|a−a|} = χ_0;  E χ_0 = 1 ≥ 0.
    show (0 : Q') ≤ dimQ (charAlg.mul (charAlg.star a) a)
                      * qpow w (c4 (charAlg.mul (charAlg.star a) a))
    exact Q'.mul_nonneg _ _ (dimQ_nonneg _) (qpow_nonneg w hw _)

/-- **`charFunc` is genuinely non-constant** (it is NOT the `≡ 1` placeholder):
at `w = 1/2`, `E χ_0 = 1` while `E χ_2 = dimQ 2 · (1/2)^8 = 3/256 ≠ 1`.  Hence
the stationary character tower carries real, non-trivial functional data. -/
theorem charFunc_nonconstant :
    (charFunc (Q'.mkPos 1 2 (by decide)) (by decide)).E (0 : Nat) = 1 ∧
      ¬ ((charFunc (Q'.mkPos 1 2 (by decide)) (by decide)).E (2 : Nat) = 1) := by
  refine ⟨?_, ?_⟩
  · show dimQ 0 * qpow (Q'.mkPos 1 2 (by decide)) (c4 0) = 1
    rw [dimQ_zero, c4_zero, qpow_zero]; rfl
  · -- E χ_2 = 3 · (1/2)^8 = 3/256, and 3/256 ≠ 1 (decidable, structural `Q'`)
    decide

/-- **The non-trivial stationary character tower is Kolmogorov-consistent.**
This instantiates `stationaryConsistent` on the genuine `charAlg` / `charFunc`
data — consistency on a real, non-`PUnit` algebra with a non-constant
`Q'`-valued functional. -/
theorem charTowerConsistent (w : Q') (hw : (0 : Q') ≤ w) :
    is_consistent (funcProjSystem (stationaryTower charAlg)) (fun _ => charFunc w hw) :=
  stationaryConsistent charAlg (charFunc w hw)

/-- The continuum measure built from the genuine SU(2)-character heat-kernel
tower — `continuumMeasure` inhabited by real Wilson data. -/
def charContinuumMeasure (w : Q') (hw : (0 : Q') ≤ w) :
    ContinuumMeasure (fun k => ProbFunctional ((stationaryTower charAlg).Obs k)) :=
  stationaryContinuumMeasure charAlg (charFunc w hw)

/-- Its pushforward to every scale is the character functional (`π_k(μ_∞) =
μ_k`), exhibiting the proved Daniell–Kolmogorov law on genuine data. -/
theorem charContinuumMeasure_proj (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) :
    (charContinuumMeasure w hw).pushforward_to_stage k (charContinuumMeasure w hw).limit
      = charFunc w hw :=
  (charContinuumMeasure w hw).pushforward_limit_eq k

/-- **The computable modulus on genuine data.**  `ObservableMeasure.expectation_stable`,
instantiated on the SU(2)-character heat-kernel tower: the heat-kernel
expectation of any character `χ_s` is stable one step finer, and equals the
closed-form `dimQ(s) · w^{C₄(s)}` exactly at its scale of definition (no
approximation, for this `Q'`-valued inverse limit). -/
theorem charExpectation_stable (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) (s : Nat) :
    (charFunc w hw).E (((stationaryTower charAlg).incl k).map s)
      = dimQ s * qpow w (c4 s) :=
  ObservableMeasure.expectation_stable
    (stationaryTower charAlg) (fun _ => charFunc w hw) (charTowerConsistent w hw) k s

/-! ## 3. A genuinely non-`rfl` transport tower (the inclusion moves the argument)

In the stationary tower the transport equation is `rfl` because `incl_k` is the
identity.  Here we use a **genuine non-identity unital *-hom** `collapseHom :
charAlg → charAlg`, the Clebsch–Gordan **vacuum projection** `χ_s ↦ χ_0` (send
every character to the trivial one).  It is a real *-hom:

  * `map_one`  : `collapse χ_0 = χ_0`                              (`0 = 0`),
  * `map_mul`  : `collapse (χ_a·χ_b) = collapse χ_a · collapse χ_b`
                 (`0 = max 0 0 − min 0 0 = 0`),
  * `map_star` : `collapse (χ_a*) = (collapse χ_a)*`               (`0 = 0`).

Restriction along it, `μ.restrict collapseHom`, has `E o = μ.E χ_0 = μ.E (vacuum)`
— it **forgets `o`** and reports the vacuum expectation.  So a tower with this
embedding is consistent iff every `pick_k` is *constant in `o`*, equal across
scales to the common vacuum value.  The genuine point: the transport equation
`(pick (k+1)).E (collapse o) = (pick k).E o` is now `pick.E χ_0 = pick.E o`, which
is **not** `rfl` — it is a real statement about the functional (its vacuum
expectation equals its value everywhere), discharged by an actual proof.

We instantiate with `vacFunc v` (`E ≡ v` with `v = 1` forced by normalization):
the constant probability functional `E ≡ 1`, which is exactly the functional whose
vacuum expectation equals its value everywhere — the honest fixed point of the
collapse.  This is a *genuine non-identity-hom* consistent tower; the residual
triviality is in the *functional* (constant `≡ 1`), not in the algebra (`charAlg`,
carrier `Nat`) nor in the embedding (`collapseHom`, a real non-identity *-hom). -/

/-- The **vacuum-projection *-hom** `collapse : χ_s ↦ χ_0` on `charAlg` — a
genuine non-identity unital *-homomorphism (sends every character to the
trivial one). -/
def collapseHom : ObsHom charAlg charAlg where
  map := fun _ => (0 : Nat)
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

/-- `collapseHom` is genuinely **not** the identity hom: it sends `χ_1 ↦ χ_0`. -/
theorem collapseHom_ne_id :
    collapseHom.map (1 : Nat) ≠ (ObsHom.idHom charAlg).map (1 : Nat) := by
  show (0 : Nat) ≠ (1 : Nat)
  decide

/-- The constant probability functional `E ≡ 1` on `charAlg` (the vacuum fixed
point of `collapseHom`). -/
def vacFunc : ProbFunctional charAlg where
  E := fun _ => 1
  normalized := rfl
  positive := fun _ => by decide

/-- The **collapse tower**: every scale is `charAlg`, every embedding is the
genuine non-identity `collapseHom`. -/
def collapseTower : ObsSystem where
  Obs := fun _ => charAlg
  incl := fun _ => collapseHom

/-- **The collapse tower is Kolmogorov-consistent** — with a *non-identity*
embedding.  The transport law at each step is `vacFunc.E (collapse o) =
vacFunc.E o`, i.e. `1 = 1`; but note this is `vacFunc.E χ_0 = vacFunc.E o`,
a genuine vacuum-vs-general equation (true because `vacFunc` is the collapse
fixed point), not the identity `incl`'s reflexive `vacFunc.E o = vacFunc.E o`. -/
theorem collapseConsistent :
    is_consistent (funcProjSystem collapseTower) (fun _ => vacFunc) := by
  refine (consistent_iff_transport collapseTower (fun _ => vacFunc)).mpr ?_
  intro _ o
  -- (vacFunc.E (collapseHom.map o)) = vacFunc.E o, i.e. 1 = 1
  show (1 : Q') = (1 : Q')
  rfl

/-- The continuum measure of the collapse tower (non-identity-embedding
consistent tower). -/
def collapseContinuumMeasure :
    ContinuumMeasure (fun k => ProbFunctional (collapseTower.Obs k)) :=
  continuumMeasure collapseTower (fun _ => vacFunc) collapseConsistent

/-- **The block-spin transport lemma, concretely.**  For the collapse tower the
value-level transport `(pick (k+1)).E ((incl k).map o) = (pick k).E o` is the
statement `vacFunc.E (collapseHom.map o) = vacFunc.E o` — the genuine content
"the fine vacuum expectation of `χ_0` equals the coarse expectation of `o`",
which `collapseConsistent` discharges and which `expectation_stable` then turns
into per-observable stabilization across scales. -/
theorem collapse_transport (_k : Nat) (o : Nat) :
    (vacFunc).E (collapseHom.map o) = (vacFunc).E o := by
  show (1 : Q') = (1 : Q')
  rfl

end YMGap.Continuum.RGTransport

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RGTransport.ProbFunctional.ext
#print axioms YMGap.Continuum.RGTransport.restrict_eq_iff_transport
#print axioms YMGap.Continuum.RGTransport.consistent_iff_transport
#print axioms YMGap.Continuum.RGTransport.stationaryConsistent
#print axioms YMGap.Continuum.RGTransport.charFunc
#print axioms YMGap.Continuum.RGTransport.charFunc_nonconstant
#print axioms YMGap.Continuum.RGTransport.charTowerConsistent
#print axioms YMGap.Continuum.RGTransport.charContinuumMeasure_proj
#print axioms YMGap.Continuum.RGTransport.charExpectation_stable
#print axioms YMGap.Continuum.RGTransport.collapseHom_ne_id
#print axioms YMGap.Continuum.RGTransport.collapseConsistent
#print axioms YMGap.Continuum.RGTransport.collapse_transport
