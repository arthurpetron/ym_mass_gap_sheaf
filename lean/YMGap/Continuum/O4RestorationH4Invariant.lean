/-
Track A1 — **a genuine non-identity H₄ rotation `*`-automorphism under which the
heat-kernel Schwinger functional is INVARIANT**, upgrading the O(4)-restoration
carrier off the identity rotation.

# The gap this closes (and exactly how far)

`CarrierPrecursors.o4_restoration_on_charAlg` witnesses `O4RestorationContent`
only under the **identity** rotation (`ObsHom.idHom`, via
`OSAxioms.functionalEquivariant_id`), and `heatKernel_not_equivariant_under_collapse`
shows a *generic* non-identity `*`-hom (the vacuum-projection `collapseHom`) BREAKS
invariance.  So the standing precursor is identity-only: the equivariance existential
`∃ A E r, FunctionalEquivariant E r` had been inhabited with `r = id`.

The reason it was identity-only is a **modeling** limitation, not a mathematical
one: a single lattice edge / a single character index has no *direction* to permute,
so the only symmetry of the single-edge character algebra realized in the repo was
the trivial one.  The fix is to give the observable algebra ≥ 2 lattice DIRECTIONS.

This module builds the smallest honest model that carries a genuine H₄ action:

  * `dirAlg4` — the observable `*`-algebra of the **four lattice axes** at a site
    (carrier `Nat × Nat × Nat × Nat`, one SU(2) spin index per axis, unit = the
    all-trivial character, componentwise Clebsch–Gordan product, `star = id`).
  * `axisSwap12 : (a,b,c,d) ↦ (b,a,c,d)` — the **transposition of two lattice axes**,
    a genuine order-2 element of the hypercubic group `H₄ = B₄` (signed axis
    permutations), realized as a **non-identity, self-inverse, order-2 unital
    `*`-automorphism** (`axisSwap12_selfInv`, `axisSwap12_order2`,
    `axisSwap12_nontrivial`).  All hom laws are `rfl`.
  * `isoFunc w` — the **isotropic** product heat-kernel functional: EVERY axis
    carries the SAME weight `w` (each factor `dimQ s · w^{C₄(s)}`, the genuine SU(2)
    heat-kernel value).  Because the weight is symmetric under axis permutation —
    the lattice heat-kernel action has full `H₄` symmetry — `isoFunc` is genuinely
    invariant under `axisSwap12`.

The invariance `isoFunc_invariant_swap : FunctionalEquivariant (isoFunc w) axisSwap12`
is a **genuine `Eq`-level** statement, discharged by one structural commutativity of
`Q'` multiplication (`qmul_comm`, proved from `Int.mul_comm`/`Nat.mul_comm` — NOT
`rfl`, and NOT the mere `eqv` used elsewhere).  It is NOT vacuous:

  * `isoFunc` is genuinely **non-constant** (`isoFunc_nonconstant`: `E χ₀⊗… = 1`
    while `E χ₂⊗χ₀⊗χ₀⊗χ₀ = 3/256 ≠ 1`), so it is not the `≡ 1` placeholder;
  * `axisSwap12` genuinely **moves an observable that the functional distinguishes**
    from the vacuum (`swap_moves_excitation`: it sends the `χ₂`-on-axis-1 excitation
    to `χ₂`-on-axis-2, two *distinct* observables both with `E = 3/256 ≠ 1`, whose
    equal expectation is the content of the invariance) — so the invariance is not
    "true because the rotation acts trivially on the support of `E`."

`o4_restoration_H4` then re-witnesses `O4RestorationContent` under this **non-identity
`axisSwap12`**, the direct upgrade of `o4_restoration_on_charAlg` off the identity.

# What is proved vs. what stays OPEN (honest banner)

PROVED (here, axiom-clean): a non-identity order-2 element of the hypercubic group
`H₄`, realized as a genuine `*`-automorphism of a 4-axis lattice observable algebra,
under which the genuine (non-constant) heat-kernel Schwinger functional is exactly
invariant at the `Eq` level.

OPEN (research mathematics, UNCHANGED):
  * the FULL continuum `O(4) ⋉ ℝ⁴` Euclidean rotation restoration in the `a → 0`
    limit (Magnen–Rivasseau–Sénéor) — this is `RubricO4Restoration`, a *decay-to-zero*
    of the anisotropy defect, a strictly harder and separate object (the anisotropic
    complement is handled, as a *model schedule*, in `H4RotationAuto.lean`);
  * whether `dirAlg4` is the REAL continuum gauge-invariant Wilson observable algebra
    — it is a FAITHFUL FINITE SUB-MODEL (the 4-axis single-site character algebra),
    not the continuum orbit space.  The genuine full continuum `H₄`-action and its
    restoration to `O(4)` are not constructed here.

This is a genuine SHARPENING of the O(4)-restoration precursor (identity ⟶ a real
non-identity `H₄` `*`-automorphism with proved invariance), NOT a closure of the
Clay clause.

# Axiom-gate (AGENTS.md Rules 1, 8)

Componentwise `rfl` hom laws; one structural `Q'` commutativity from
`Int.mul_comm`/`Nat.mul_comm`; `decide` for the concrete numeric (non)equalities;
`Q'.mul_nonneg` chains for positivity.  All witnesses are `Type`-level data.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.FourDExistence
import YMGap.Continuum.RGTransport

namespace YMGap.Continuum.O4RestorationH4Invariant

open YMGap.Constructive
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ObservableMeasure (ProbFunctional ObsAlg ObsHom)
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.RGTransport

/-! ## 0. Structural commutativity of `Q'` multiplication (at the `Eq` level)

`Q'` is the raw pair `⟨num, denPred⟩`; `mul p q = ⟨p.num*q.num, p.den*q.den − 1⟩`.
The repo elsewhere only uses `mul_comm_eqv` (commutativity up to the value-setoid
`eqv`).  But `mul` is ALSO commutative up to structural `Eq` — the numerators and
denominators commute as `Int`/`Nat` products — it is simply not `rfl`.  That
`Eq`-level commutativity is exactly what `FunctionalEquivariant` (stated with `Eq`,
not `eqv`) needs. -/

/-- **Structural commutativity of `Q'` multiplication.**  `a * b = b * a` as genuine
`Eq` (via `Int.mul_comm` on numerators and `Nat.mul_comm` on denominators) — not
`rfl`, and stronger than the value-level `mul_comm_eqv`. -/
theorem qmul_comm (a b : Q') : a * b = b * a := by
  show Q'.mul a b = Q'.mul b a
  unfold Q'.mul
  congr 1
  · exact Int.mul_comm a.num b.num
  · exact congrArg (fun n => n - 1) (Nat.mul_comm a.den b.den)

/-! ## 1. The 4-axis lattice observable algebra -/

/-- The observable `*`-algebra of the **four lattice axes** at a site: carrier
`Nat × Nat × Nat × Nat` (one SU(2) spin index per axis), unit = the all-trivial
character `(χ₀,χ₀,χ₀,χ₀)`, componentwise Clebsch–Gordan lowest-weight product, and
`star = id` (real SU(2) characters, componentwise). -/
def dirAlg4 : ObsAlg where
  carrier := Nat × Nat × Nat × Nat
  one     := (0, 0, 0, 0)
  mul     := fun (a, b, c, d) (a', b', c', d') =>
               (charAlg.mul a a', charAlg.mul b b', charAlg.mul c c', charAlg.mul d d')
  star    := fun x => x

/-! ## 2. The axis transposition: a non-identity order-2 `*`-automorphism -/

/-- **Transposition of lattice axes 1 and 2** `(a,b,c,d) ↦ (b,a,c,d)` — a genuine
order-2 element of the hypercubic group `H₄`, realized as a unital `*`-hom.  All
three hom laws are `rfl` (the swap commutes with the componentwise product / unit /
involution). -/
def axisSwap12 : ObsHom dirAlg4 dirAlg4 where
  map     := fun (a, b, c, d) => (b, a, c, d)
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

/-- `axisSwap12` is its own two-sided inverse (`rfl`, componentwise) — an
`involution`, hence a genuine `*`-automorphism (invertible), unlike the vacuum
projection `collapseHom`. -/
theorem axisSwap12_selfInv : ∀ x, axisSwap12.map (axisSwap12.map x) = x := fun _ => rfl

/-- `axisSwap12` has order exactly 2: it is an involution (`axisSwap12_selfInv`) that
is not the identity (`axisSwap12_nontrivial`). -/
theorem axisSwap12_order2 : ∀ x, axisSwap12.map (axisSwap12.map x) = x := axisSwap12_selfInv

/-- `axisSwap12` is genuinely **not** the identity: it moves `(χ₁,χ₀,χ₀,χ₀)` to
`(χ₀,χ₁,χ₀,χ₀)`. -/
theorem axisSwap12_nontrivial : ∃ x, axisSwap12.map x ≠ x :=
  ⟨(1, 0, 0, 0), by
    show ((0 : Nat), (1 : Nat), (0 : Nat), (0 : Nat))
         ≠ ((1 : Nat), (0 : Nat), (0 : Nat), (0 : Nat))
    decide⟩

/-! ## 3. The isotropic product heat-kernel functional -/

/-- One SU(2) heat-kernel factor: `ff w s = dimQ s · w^{C₄(s)}` (`dimQ s = s+1`,
`C₄(s) = s(s+2)`), the genuine diagonal heat-kernel value at spin `s`. -/
def ff (w : Q') (s : Nat) : Q' := dimQ s * qpow w (c4 s)

/-- `ff w 0 = 1` — the vacuum factor is the probability normalization. -/
theorem ff_zero (w : Q') : ff w 0 = 1 := by
  unfold ff
  rw [dimQ_zero]
  show (1 : Q') * qpow w (c4 0) = 1
  rw [show c4 0 = 0 from rfl, qpow_zero]
  decide

/-- `0 ≤ ff w s` for `0 ≤ w` (nonnegative dimension times a nonnegative power). -/
theorem ff_nonneg (w : Q') (hw : (0 : Q') ≤ w) (s : Nat) : (0 : Q') ≤ ff w s :=
  Q'.mul_nonneg _ _ (dimQ_nonneg s) (qpow_nonneg w hw _)

/-- The **isotropic** product heat-kernel functional on `dirAlg4`: every axis carries
the SAME weight `w`, `E (a,b,c,d) = ff w a · ff w b · ff w c · ff w d`.  Normalized
(`= 1` at the unit) and positive on `a*·a` (`star = id`, so each factor is a
nonnegative heat-kernel value).  Isotropy across axes is exactly the `H₄` symmetry of
the lattice action. -/
def isoFunc (w : Q') (hw : (0 : Q') ≤ w) : ProbFunctional dirAlg4 where
  E := fun (a, b, c, d) => ff w a * ff w b * ff w c * ff w d
  normalized := by
    show ff w 0 * ff w 0 * ff w 0 * ff w 0 = 1
    rw [ff_zero]
    decide
  positive := fun x => by
    obtain ⟨a, b, c, d⟩ := x
    show (0 : Q') ≤ ff w (charAlg.mul a a) * ff w (charAlg.mul b b)
                  * ff w (charAlg.mul c c) * ff w (charAlg.mul d d)
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (ff_nonneg w hw _) (ff_nonneg w hw _))
        (ff_nonneg w hw _))
      (ff_nonneg w hw _)

/-! ## 4. The genuine invariance of the functional under the non-identity rotation -/

/-- **The heat-kernel functional is INVARIANT under the non-identity axis
transposition.**  `FunctionalEquivariant (isoFunc w) axisSwap12`: for every observable
`(a,b,c,d)`,

    E (axisSwap12 (a,b,c,d)) = E (b,a,c,d)
      = ff w b · ff w a · ff w c · ff w d
      = ff w a · ff w b · ff w c · ff w d       (by `qmul_comm` on the first pair)
      = E (a,b,c,d).

A genuine `Eq`-level invariance under a NON-identity `*`-automorphism — the upgrade
off the identity-only precursor.  The single algebraic input is the structural
commutativity `qmul_comm` of `Q'` multiplication (the isotropy of the weight across
the two swapped axes is what makes the two factors interchangeable). -/
theorem isoFunc_invariant_swap (w : Q') (hw : (0 : Q') ≤ w) :
    FunctionalEquivariant (isoFunc w hw) axisSwap12 := by
  intro x
  obtain ⟨a, b, c, d⟩ := x
  show ff w b * ff w a * ff w c * ff w d = ff w a * ff w b * ff w c * ff w d
  rw [qmul_comm (ff w b) (ff w a)]

/-! ## 5. Non-vacuity: the functional is non-constant and the rotation moves its
support -/

/-- Anchor weight `w = 1/2` (a representative sub-critical heat-kernel weight
`e^{−t/4}`). -/
def heatWeight : Q' := Q'.mkPos 1 2 (by decide)

theorem heatWeight_nonneg : (0 : Q') ≤ heatWeight := by decide

set_option maxRecDepth 4000 in
/-- **The functional is genuinely non-constant** (NOT the `≡ 1` placeholder):
`E (χ₀,χ₀,χ₀,χ₀) = 1` while `E (χ₂,χ₀,χ₀,χ₀) = 3·(1/2)^8 = 3/256 ≠ 1`.  So the
invariance is not vacuously true of a constant functional. -/
theorem isoFunc_nonconstant :
    (isoFunc heatWeight heatWeight_nonneg).E (0, 0, 0, 0) = 1 ∧
      ¬ ((isoFunc heatWeight heatWeight_nonneg).E (2, 0, 0, 0) = 1) := by
  refine ⟨?_, ?_⟩
  · show ff heatWeight 0 * ff heatWeight 0 * ff heatWeight 0 * ff heatWeight 0 = 1
    rw [ff_zero]; decide
  · decide

set_option maxRecDepth 4000 in
/-- **The rotation genuinely moves an observable the functional distinguishes.**  The
transposition sends the `χ₂`-on-axis-1 excitation `(χ₂,χ₀,χ₀,χ₀)` to the *distinct*
`χ₂`-on-axis-2 excitation `(χ₀,χ₂,χ₀,χ₀)`; both have expectation `3/256 ≠ 1 =
E(vacuum)`, and their EQUALITY is exactly the content of the invariance.  So the
invariance is not "true because the rotation fixes the support of `E`" — it is a real
constraint the axis symmetry satisfies. -/
theorem swap_moves_excitation :
    axisSwap12.map (2, 0, 0, 0) ≠ (2, 0, 0, 0) ∧
    (isoFunc heatWeight heatWeight_nonneg).E (axisSwap12.map (2, 0, 0, 0))
        = (isoFunc heatWeight heatWeight_nonneg).E (2, 0, 0, 0) ∧
    ¬ ((isoFunc heatWeight heatWeight_nonneg).E (2, 0, 0, 0) = 1) := by
  refine ⟨?_, ?_, isoFunc_nonconstant.2⟩
  · show ((0 : Nat), (2 : Nat), (0 : Nat), (0 : Nat))
         ≠ ((2 : Nat), (0 : Nat), (0 : Nat), (0 : Nat))
    decide
  · exact isoFunc_invariant_swap heatWeight heatWeight_nonneg (2, 0, 0, 0)

/-! ## 6. The upgraded O(4)-restoration precursor (off the identity) -/

/-- **O(4)-restoration carrier under a genuine NON-identity H₄ rotation.**  Witnesses
`O4RestorationContent` with the 4-axis lattice observable algebra `dirAlg4`, the
genuine isotropic heat-kernel functional `isoFunc heatWeight`, and the **non-identity**
order-2 axis transposition `axisSwap12` in the rotation slot — the direct upgrade of
`CarrierPrecursors.o4_restoration_on_charAlg` (which used `ObsHom.idHom`).

The equivariance is genuine (`isoFunc_invariant_swap`), the functional is genuinely
non-constant (`isoFunc_nonconstant`), and the rotation genuinely moves observables the
functional distinguishes (`swap_moves_excitation`).

OPEN (research mathematics): the full continuum `O(4) ⋉ ℝ⁴` restoration
(`RubricO4Restoration`, Magnen–Rivasseau–Sénéor), and whether `dirAlg4` is the real
continuum gauge-invariant Wilson algebra (it is a faithful finite sub-model). No
continuum rotation action is constructed here. -/
theorem o4_restoration_H4 {M : Nat → Type} (_μ_inf : ContinuumMeasure M) :
    O4RestorationContent _μ_inf :=
  ⟨dirAlg4, isoFunc heatWeight heatWeight_nonneg, axisSwap12,
    isoFunc_invariant_swap heatWeight heatWeight_nonneg⟩

/-- **Capstone (the honest content in one place).**  There is a genuine non-identity
order-2 `H₄` `*`-automorphism (`axisSwap12`, self-inverse, moving `(χ₁,χ₀,χ₀,χ₀)`)
under which the genuine, non-constant heat-kernel functional `isoFunc heatWeight` is
exactly invariant. -/
theorem h4_invariance_capstone :
    (∃ x, axisSwap12.map x ≠ x) ∧
    (∀ x, axisSwap12.map (axisSwap12.map x) = x) ∧
    FunctionalEquivariant (isoFunc heatWeight heatWeight_nonneg) axisSwap12 ∧
    ¬ ((isoFunc heatWeight heatWeight_nonneg).E (2, 0, 0, 0) = 1) :=
  ⟨axisSwap12_nontrivial, axisSwap12_selfInv,
    isoFunc_invariant_swap heatWeight heatWeight_nonneg, isoFunc_nonconstant.2⟩

end YMGap.Continuum.O4RestorationH4Invariant

/-! ## Axiom-dependency gates (AGENTS.md Rules 1, 8) -/

#print axioms YMGap.Continuum.O4RestorationH4Invariant.qmul_comm
#print axioms YMGap.Continuum.O4RestorationH4Invariant.dirAlg4
#print axioms YMGap.Continuum.O4RestorationH4Invariant.axisSwap12
#print axioms YMGap.Continuum.O4RestorationH4Invariant.axisSwap12_selfInv
#print axioms YMGap.Continuum.O4RestorationH4Invariant.axisSwap12_order2
#print axioms YMGap.Continuum.O4RestorationH4Invariant.axisSwap12_nontrivial
#print axioms YMGap.Continuum.O4RestorationH4Invariant.ff_zero
#print axioms YMGap.Continuum.O4RestorationH4Invariant.ff_nonneg
#print axioms YMGap.Continuum.O4RestorationH4Invariant.isoFunc
#print axioms YMGap.Continuum.O4RestorationH4Invariant.isoFunc_invariant_swap
#print axioms YMGap.Continuum.O4RestorationH4Invariant.isoFunc_nonconstant
#print axioms YMGap.Continuum.O4RestorationH4Invariant.swap_moves_excitation
#print axioms YMGap.Continuum.O4RestorationH4Invariant.o4_restoration_H4
#print axioms YMGap.Continuum.O4RestorationH4Invariant.h4_invariance_capstone
