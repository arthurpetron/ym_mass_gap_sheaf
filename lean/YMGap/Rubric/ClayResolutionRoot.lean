/-
The object-identity root for the corrected Clay resolution target.

This is Phase A infrastructure, not the completed `ClayResolutionTarget` and
not a closure claim.  It makes three choices that every later Clay-facing
carrier must share definitionally:

  * one compact-simple Cartan type and its pinned representation data;
  * one continuum OS bundle and probability/Schwinger functional;
  * one Wilson GNS datum whose expectation is exactly that functional.

The completed constructive GNS Hilbert space is then DEFINED from the Wilson
datum.  It is not a separately selected field.  Likewise, the time-translation
interface below pins its transfer operator on the dense image of observables and
pins the vacuum to the image of the unit.  This prevents the independent-object
hole in the legacy target.

This module deliberately supplies no constructor for a Yang--Mills root and no
constructor for time translations.  In particular it does not use the identity
transfer or trivial spectral model.  Full Euclidean covariance, unbounded
semigroup generation, the physical spectral gap, and local/OPE content remain
separate faithful interfaces to be added before assembling the canonical target.
-/

import YMGap.MassGap.AllSimpleTypes
import YMGap.Continuum.OSAxioms
import YMGap.Continuum.WilsonGNS
import YMGap.Continuum.GNSDynamics

namespace YMGap.Rubric.ClayResolutionRoot

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RG
open YMGap.MassGap.AllSimpleTypes
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.WilsonGNS

/-! ## 1. Compact-simple group pin -/

/-- A compact-simple Cartan type together with the exact representation datum
used by the existing all-simple-types reduction.

The equality `repPinned` forbids replacing the selected Cartan type by an
unrelated convenient `RepData`.  This is classification-facing information;
the physical group-specific heat-kernel tail remains a later target field. -/
structure PinnedSimpleGroup (T : CartanType) : Type where
  simpleRank : IsSimpleRank T
  rep : RepData
  repPinned : rep = repDataOf T
  admissible : AdmissibleSimpleGroup rep

/-- The classification data already proved in `AllSimpleTypes` gives the
canonical pin for every genuine-simple Cartan type. -/
def pinnedSimpleGroup (T : CartanType) (hT : IsSimpleRank T) :
    PinnedSimpleGroup T where
  simpleRank := hT
  rep := repDataOf T
  repPinned := rfl
  admissible := admissible_of_cartanType T hT

/-! ## 2. One functional, one Wilson GNS space -/

/-- The shared functional/GNS root of the corrected target.

`bundle` fixes the observable algebra and Schwinger functional.  `wilson` adds
the constructive vector-space and reflection-positive form needed for the GNS
quotient.  `expectationPinned` says these are the same functional, not merely
two objects with similar comments. -/
structure CanonicalWilsonRoot
    {M : Nat → Type} (μ_inf : ContinuumMeasure M) (T : CartanType) : Type 2 where
  group : PinnedSimpleGroup T
  bundle : OSAxiomBundle μ_inf
  wilson : WilsonGNSData bundle.A
  expectationPinned : wilson.E = bundle.E.E

namespace CanonicalWilsonRoot

variable {M : Nat → Type} {μ_inf : ContinuumMeasure M} {T : CartanType}

/-- The physical GNS datum is definitionally the datum built from the pinned
Wilson functional. -/
def gnsData (R : CanonicalWilsonRoot μ_inf T) : GNSData :=
  R.wilson.toGNSData

/-- The physical Hilbert space is definitionally the constructive completion of
the pinned Wilson GNS datum.  There is no independently selectable Hilbert-space
field. -/
def gnsHilbert (R : CanonicalWilsonRoot μ_inf T) : CompleteGNSHilbert R.gnsData :=
  R.gnsData.gnsComplete

/-- The dense GNS image of the unit observable, provisionally the vacuum vector
that every later reconstruction field must use. -/
def vacuum (R : CanonicalWilsonRoot μ_inf T) : R.gnsHilbert.hilbert.carrier :=
  embedV R.gnsData R.bundle.A.one

end CanonicalWilsonRoot

/-! ## 3. Time translations pinned on the dense observable image -/

/-- A discrete nonnegative-time action on the canonical observable algebra,
together with its descended transfer operator on the exact completed GNS space.

This is the finite/dense precursor of the eventual strongly continuous
contraction semigroup and unbounded positive generator.  The two pins are
load-bearing:

* `transfer_dense` identifies the transfer action on every embedded observable;
* `vacuumPinned` identifies its vacuum with the embedded algebra unit.

Consequently a later spectral model cannot float free of the physical time
translation.  A continuum semigroup package must extend this action rather than
replace it with an unrelated operator. -/
structure CanonicalTimeTranslations
    {M : Nat → Type} {μ_inf : ContinuumMeasure M} {T : CartanType}
    (R : CanonicalWilsonRoot μ_inf T) : Type 1 where
  shift : Nat → ObsHom R.bundle.A R.bundle.A
  shift_zero : ∀ a, (shift 0).map a = a
  shift_add : ∀ n m a,
    (shift (n + m)).map a = (shift n).map ((shift m).map a)
  expectationInvariant : ∀ n a,
    R.bundle.E.E ((shift n).map a) = R.bundle.E.E a
  transfer : TransferOperator R.gnsHilbert
  transfer_dense : ∀ a,
    transfer.T (embedV R.gnsData a) =
      embedV R.gnsData ((shift 1).map a)
  vacuumPinned : transfer.vacuum = R.vacuum

end YMGap.Rubric.ClayResolutionRoot

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Rubric.ClayResolutionRoot.pinnedSimpleGroup
#print axioms YMGap.Rubric.ClayResolutionRoot.CanonicalWilsonRoot.gnsData
#print axioms YMGap.Rubric.ClayResolutionRoot.CanonicalWilsonRoot.gnsHilbert
#print axioms YMGap.Rubric.ClayResolutionRoot.CanonicalWilsonRoot.vacuum
