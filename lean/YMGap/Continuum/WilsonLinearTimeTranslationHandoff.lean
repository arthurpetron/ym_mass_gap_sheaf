/-
M4k -- expose the exact linear-operator data needed to feed the constructive
functional-calculus stack from the selected Wilson time translation.

`WilsonTimeTranslationPin` deliberately carries only a completed positive,
self-adjoint contraction and its dense intertwining equation.  Those fields do
not state additivity, scalar homogeneity, or a representative-level lift.  The
existing `LinearTransferOperator` requires all three.

This module therefore introduces one honest strengthening of a fixed time pin.
It also proves that the spectral datum formed from the strengthened operator is
the *same record* as the datum already selected by `WilsonLinkedOSGNSData`.
Unlike the earlier character/OS4 comparison, both sides here use definitionally
the same model and located-gap proof, so transporting the record is sound.

No linear transfer is constructed for a continuum Yang--Mills measure here,
and no bounded or unbounded Hamiltonian functional calculus is asserted.
-/

import YMGap.Continuum.ContinuousFCCarrierLimit
import YMGap.Continuum.LinearTransferOperator
import YMGap.Continuum.WilsonLinkedOSReconstruction

namespace YMGap.Continuum.WilsonLinearTimeTranslationHandoff

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.WilsonGNS
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonLinkedOSReconstruction

/-! ## The Wilson carrier with the two missing scalar-module laws -/

/-- Promote the fixed Wilson carrier to the exact scalar module used by the
continuous functional-calculus stack.  Both laws are explicit inputs because
the minimal `WilsonGNSData` interface does not contain them. -/
def wilsonLinearSmulGNSData
    {A : ObservableMeasure.ObsAlg}
    (W : WilsonGNSData A)
    (smul_sub : forall (s : Q') (a b : W.toGNSData.V),
      W.toGNSData.veq (W.toGNSData.smul s (W.toGNSData.sub a b))
        (W.toGNSData.sub (W.toGNSData.smul s a)
          (W.toGNSData.smul s b)))
    (smul_add_scalar : forall (s t : Q') (a : W.toGNSData.V),
      W.toGNSData.veq (W.toGNSData.smul (s + t) a)
        (W.toGNSData.add (W.toGNSData.smul s a)
          (W.toGNSData.smul t a))) : LinearSmulGNSData where
  toSmulGNSData := W.toSmulGNSData smul_sub
  smul_add_scalar := smul_add_scalar

/-! ## A linear strengthening of one already-selected time translation -/

/-- The selected Wilson transfer, strengthened by precisely the linear and
representative-level data required by the constructive functional calculus.

`operatorPinned` prevents replacing the physical time translation by an
unrelated linear operator on the same carrier. -/
structure WilsonLinearTimeTranslationPin
    {A : ObservableMeasure.ObsAlg}
    {W : WilsonGNSData A}
    (P : WilsonTimeTranslationPin W) : Type where
  /-- Scalar multiplication distributes over subtraction on the Wilson
  carrier. -/
  smul_sub : forall (s : Q') (a b : W.toGNSData.V),
    W.toGNSData.veq (W.toGNSData.smul s (W.toGNSData.sub a b))
      (W.toGNSData.sub (W.toGNSData.smul s a)
        (W.toGNSData.smul s b))
  /-- Scalar addition distributes through the Wilson carrier action. -/
  smul_add_scalar : forall (s t : Q') (a : W.toGNSData.V),
    W.toGNSData.veq (W.toGNSData.smul (s + t) a)
      (W.toGNSData.add (W.toGNSData.smul s a)
        (W.toGNSData.smul t a))
  /-- The additive, scalar-linear, representative-lifted completed operator. -/
  linearOperator : LinearTransferOperator
    (wilsonLinearSmulGNSData W smul_sub smul_add_scalar).toSmulGNSData
  /-- The linear operator is exactly the already-selected time translation. -/
  operatorPinned : linearOperator.toTransferOperator = P.op

namespace WilsonLinearTimeTranslationPin

/-- The scalar-module datum selected by the linear time pin. -/
def linearSmulData
    {A : ObservableMeasure.ObsAlg}
    {W : WilsonGNSData A}
    {P : WilsonTimeTranslationPin W}
    (L : WilsonLinearTimeTranslationPin P) : LinearSmulGNSData :=
  wilsonLinearSmulGNSData W L.smul_sub L.smul_add_scalar

/-- The formed spectral datum uses the selected OS4 model and located gap, and
the linear operator pinned to the Wilson time translation. -/
def selectedLinearSpectralGapData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (L : WilsonLinearTimeTranslationPin D.timeTranslation) :
    SpectralGapData D.wilson.toGNSData.gnsComplete :=
  ContinuousFunctionalCalculusForm.spectralGapDataOfL
    L.linearSmulData.toSmulGNSData
    L.linearOperator.toAdditiveTransferOperator
    H.os_axioms.S (bundleLocatedGap D.measureLinked)

/-- The functional-calculus spectral datum is exactly the already-selected
Wilson/OS4 datum.  This equality is safe because the model and the dependent
located-gap proof are definitionally identical; only the operator pin is
rewritten. -/
theorem selectedLinearSpectralGapData_eq
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (L : WilsonLinearTimeTranslationPin D.timeTranslation) :
    L.selectedLinearSpectralGapData D =
      selectedSpectralGapData D.measureLinked D.timeTranslation := by
  unfold selectedLinearSpectralGapData
  unfold ContinuousFunctionalCalculusForm.spectralGapDataOfL
  unfold selectedSpectralGapData
  rw [L.operatorPinned]
  rfl

/-- Transport the already-proved canonical operator-form gap onto the exact
spectral record consumed by the linear functional-calculus stack. -/
def selectedCanonicalFormGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (L : WilsonLinearTimeTranslationPin D.timeTranslation) :
    CanonicalTransferFormGap.CanonicalTransferFormGap
      (L.selectedLinearSpectralGapData D) := by
  rw [L.selectedLinearSpectralGapData_eq D]
  exact D.reconstructionCanonicalFormGap

end WilsonLinearTimeTranslationPin

end YMGap.Continuum.WilsonLinearTimeTranslationHandoff

#print axioms YMGap.Continuum.WilsonLinearTimeTranslationHandoff.wilsonLinearSmulGNSData
#print axioms YMGap.Continuum.WilsonLinearTimeTranslationHandoff.WilsonLinearTimeTranslationPin.linearSmulData
#print axioms YMGap.Continuum.WilsonLinearTimeTranslationHandoff.WilsonLinearTimeTranslationPin.selectedLinearSpectralGapData
#print axioms YMGap.Continuum.WilsonLinearTimeTranslationHandoff.WilsonLinearTimeTranslationPin.selectedLinearSpectralGapData_eq
#print axioms YMGap.Continuum.WilsonLinearTimeTranslationHandoff.WilsonLinearTimeTranslationPin.selectedCanonicalFormGap
