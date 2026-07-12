/-
Adversarial statement-audit fences for two legacy fields of `FrontierDAG`.

# What is machine-refuted here

The canonical DAG currently carries

  * `boundedH : BoundedFunctionalCalculusResidual G L`, and
  * `trueMargin : UniformCouplingFromAF.TrueMarginRecursion`.

Their docstrings advertise substantially stronger physics than their Lean field
types enforce.

1. `BoundedFunctionalCalculusResidual G L` has no boundedness field and no law
   tying its `op` to `G.op`, `L`, or `exp (-H) = T`.  Its `gapWitness` is already
   the theorem `G.hamiltonianGapReal_pos`.  Therefore `L.T` supplies a generic
   inhabitant (`boundedFunctionalCalculusResidual_generic`).

2. The legacy `TrueMarginRecursion` does not carry a lattice mass, a spacing, or
   the equation `trueMargin = massLat / spacing`.  It only asks for a freely
   named function equal to `D.physGap`.  Hence every `DefectGapRecursion` supplies
   one (`legacyTrueMargin_of_defectRecursion`), and the already-built dominant-mode
   survival PRODUCT supplies an unconditional inhabitant
   (`legacyTrueMargin_surrogate_unconditional`).

These are statement-bug fences, NOT Clay progress.  They intentionally expose
that the two legacy atom types are too weak; they do not construct a
`FrontierDAG`, do not modify any guarded statement, and do not claim that either
physical obligation is solved.  The stricter existing carrier
`TrueMarginRecursionPhysical` does contain the missing mass/spacing pin; its
equation is re-exported as `physicalMargin_is_massLat_div_spacing` to make the
distinction kernel-visible.

# Required repair (not performed in this audit module)

The canonical DAG must eventually use a genuinely pinned physical-margin type
(at least `TrueMarginRecursionPhysical`) and a Hamiltonian/transfer carrier whose
fields actually state boundedness/domain information and the functional relation
to `T`.  Because those are pinned frontier-statement changes, this module records
the defect without silently rewriting the targets.

# Axiom gate

No `sorry`, custom axiom, `Classical.*`, `native_decide`, or `Real`.  The generic
legacy-margin constructor is axiom-free; the other fences inherit only the
permitted `propext` / `Quot.sound` footprint of the constructive GNS substrate.
-/

import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.UniformCouplingFromAF
import YMGap.Continuum.TrueMarginRecursionPhysical

namespace YMGap.Continuum.FrontierStatementBugFence

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ContinuumClosureProgram

/-! ## 1. The legacy bounded-H atom is generically inhabitable -/

/-- **STATEMENT-BUG FENCE (bounded-H atom).**  The current
`BoundedFunctionalCalculusResidual G L` is supplied by the already-bounded transfer
map `L.T` for arbitrary `G` and `L`: additivity and self-adjointness are fields of
`L`, while the alleged Hamiltonian gap witness is already a theorem of `G`.

This constructor would be impossible if the residual actually required the
advertised functional identity `exp (-H) = T` (plus the appropriate domain or
boundedness data).  Its genericity is the machine-checked refutation of the
current statement's intended strength. -/
def boundedFunctionalCalculusResidual_generic {D : GNSData}
    (G : SpectralGapData D.gnsComplete) (L : AdditiveTransferOperator D) :
    BoundedFunctionalCalculusResidual G L where
  op := L.T
  op_add := L.T_add
  selfAdjoint := L.selfAdjoint
  gapWitness := fun hwin => G.hamiltonianGapReal_pos hwin

/-- The diagnostic residual's alleged Hamiltonian operator is definitionally just
the supplied transfer operator.  No logarithm or functional calculus occurred. -/
theorem boundedFunctionalCalculusResidual_generic_op {D : GNSData}
    (G : SpectralGapData D.gnsComplete) (L : AdditiveTransferOperator D) :
    (boundedFunctionalCalculusResidual_generic G L).op = L.T :=
  rfl

/-! ## 2. The legacy true-margin atom is only an alias pin -/

/-- **STATEMENT-BUG FENCE (legacy true-margin atom).**  Every defect recursion
inhabits the current `UniformCouplingFromAF.TrueMarginRecursion`: name its existing
`physGap` function `trueMargin` and discharge the only pin by reflexivity.

There is no `massLat`, no `spacing`, and no ratio equation in this legacy type, so
this constructor contains no physical-margin identification. -/
def legacyTrueMargin_of_defectRecursion (D : DefectGapRecursion) :
    UniformCouplingFromAF.TrueMarginRecursion where
  D := D
  trueMargin := D.physGap
  physGap_is_trueMargin := fun _ => rfl

/-- The legacy constructor's `trueMargin` is definitionally the input recursion's
uninterpreted `physGap`; this is the full content of its current pin. -/
theorem legacyTrueMargin_is_physGap (D : DefectGapRecursion) (k : Nat) :
    (legacyTrueMargin_of_defectRecursion D).trueMargin k = D.physGap k :=
  rfl

/-- **Unconditional surrogate inhabitant.**  Applying the generic constructor to
the already-proved dominant-mode recursion inhabits the legacy atom with the
dominant-mode survival PRODUCT.  This is an audit-only, non-load-bearing wrapper
around the existing constructive extraction; it is marked `noncomputable` only
because `DominantModeRecursion.dominantModeRecursion` already is.

It is deliberately NOT exported as a `FrontierDAG`: it refutes the legacy atom's
statement strength rather than closing the physical margin. -/
noncomputable def legacyTrueMargin_surrogate_unconditional :
    UniformCouplingFromAF.TrueMarginRecursion :=
  legacyTrueMargin_of_defectRecursion
    DominantModeRecursion.dominantModeRecursion

/-- The unconditional legacy inhabitant is exactly the dominant-mode survival
product's gap schedule, not a mass-over-spacing quantity. -/
theorem legacyTrueMargin_surrogate_is_survivalProduct (k : Nat) :
    legacyTrueMargin_surrogate_unconditional.trueMargin k =
      DominantModeRecursion.dominantModeRecursion.physGap k :=
  rfl

/-! ## 3. Kernel-visible distinction from the stricter physical carrier -/

/-- **The missing pin exists in the stricter carrier.**  Unlike the legacy atom,
`TrueMarginRecursionPhysical` requires, at every scale,

`margin k = massLat k / spacing k`

with a proof that the spacing is strictly positive.  This theorem re-exports that
field beside the fences above, making the statement-strength distinction explicit
without changing either type. -/
theorem physicalMargin_is_massLat_div_spacing
    (T : TrueMarginRecursionPhysical) (k : Nat) :
    T.margin k = Q'.divPos (T.massLat k) (T.spacing k) (T.spacing_pos k) :=
  T.margin_def k

end YMGap.Continuum.FrontierStatementBugFence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FrontierStatementBugFence.boundedFunctionalCalculusResidual_generic
#print axioms YMGap.Continuum.FrontierStatementBugFence.boundedFunctionalCalculusResidual_generic_op
#print axioms YMGap.Continuum.FrontierStatementBugFence.legacyTrueMargin_of_defectRecursion
#print axioms YMGap.Continuum.FrontierStatementBugFence.legacyTrueMargin_is_physGap
#print axioms YMGap.Continuum.FrontierStatementBugFence.legacyTrueMargin_surrogate_unconditional
#print axioms YMGap.Continuum.FrontierStatementBugFence.legacyTrueMargin_surrogate_is_survivalProduct
#print axioms YMGap.Continuum.FrontierStatementBugFence.physicalMargin_is_massLat_div_spacing
