/-
# Asymptotic fixed-nome physical BF4 connected cutoff gap

An exact sixteenth at every representation cutoff is stronger than the limit
needs.  The transitive Bishop-real order `CReal.leEv` only requires that for
every rational tolerance `epsilon > 0`, all sufficiently large cutoffs obey

  centeredForm_K <= (1/16) * centeredNorm_K + epsilon.

This module packages the threshold as Type-level data, proves that additive
mean-zero form errors survive exact stationary centering, and contracts the
result into the strict eventual-order gap between the actual connected cutoff
limits.  The exact certificate and the genuine local-gluing certificate from
the preceding module both map into this weaker interface.

No asymptotic certificate is constructed here.  In particular, convergence
of ordinary bounded slab expectations does not automatically control the
cutoff-dependent centered observable.

Axiom gate: constructive exact rational estimates and Bishop-real eventual
order only.  No `Classical`, `sorry`, `native_decide`, choice, functional
extensionality, noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4PhysicalCutoffConnectedGap
import YMGap.Constructive.CRealComplete

namespace YMGap.Continuum.BF4PhysicalCutoffAsymptoticConnectedGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Additive-error stationary centering -/

/-- Any additive-error absolute mean-zero form bound becomes the corresponding
additive-error corrected form bound for an arbitrary observable. -/
theorem centralPhysical_centeredCorrection_form_le_of_abs_gap_add
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (rate error : Q')
    (hgap : ∀ observable : EdgeLabelling → Q',
      CentralPhysicalMeanZero w hw cutoff half observable →
        Q'.abs
            (centralPhysicalJointQuadratic
              w hw cutoff half observable) ≤
          rate *
              centralPhysicalWeightedInner
                w hw cutoff half observable observable +
            error)
    (observable : EdgeLabelling → Q') :
    let D := (centralPhysicalSmulGNS w hw cutoff half).toGNSData
    let E := (centralPhysicalMarkovFormGNS w hw cutoff half).toGNSData
    let mean :=
      centralPhysicalStationaryMean w hw cutoff half observable
    E.B observable observable + -(mean * mean) ≤
      rate * (D.B observable observable + -(mean * mean)) + error := by
  let D := (centralPhysicalSmulGNS w hw cutoff half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw cutoff half).toGNSData
  let mean := centralPhysicalStationaryMean w hw cutoff half observable
  let centered :=
    centralPhysicalCenteredObservable w hw cutoff half observable
  have hmeanZero :
      CentralPhysicalMeanZero w hw cutoff half centered :=
    centralPhysicalCenteredObservable_meanZero
      w hw cutoff half observable
  have hEJoint : E.B centered centered ≈
      centralPhysicalJointQuadratic w hw cutoff half centered := by
    refine Q'.eqv_trans _
      (centralPhysicalWeightedInner w hw cutoff half
        (centralPhysicalMarkovApply w hw cutoff half centered) centered) _
        ?_ ?_
    · exact Q'.eqv_of_eq
        (centralPhysicalMarkovFormGNS_B_eq
          w hw cutoff half centered centered)
    refine Q'.eqv_trans _
      (centralPhysicalWeightedInner w hw cutoff half centered
        (centralPhysicalMarkovApply w hw cutoff half centered)) _ ?_ ?_
    · exact Q'.eqv_symm
        (centralPhysicalMarkovApply_self_adjoint
          w hw cutoff half centered centered)
    exact centralPhysicalWeightedMarkovQuadratic_eq_joint
      w hw cutoff half centered
  have hcenteredFinite :
      E.B centered centered ≤ rate * D.B centered centered + error := by
    refine Q'.le_trans' _
      (centralPhysicalJointQuadratic w hw cutoff half centered) _
      (Q'.le_of_eqv hEJoint) ?_
    refine Q'.le_trans' _
      (Q'.abs
        (centralPhysicalJointQuadratic w hw cutoff half centered)) _
      (Q'.le_abs_self _) ?_
    refine le_of_le_eqv (hgap centered hmeanZero) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left rate _ _
        (Q'.eqv_symm
          (Q'.eqv_of_eq
            (centralPhysicalSmulGNS_B_eq
              w hw cutoff half centered centered))))
      (Q'.eqv_refl error)
  have hleft : E.B centered centered ≈
      E.B observable observable + -(mean * mean) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalMarkovFormGNS_B_eq
          w hw cutoff half centered centered))
      (centralPhysicalCenteredObservable_markovForm_identity
        w hw cutoff half observable)
  have hright : D.B centered centered ≈
      D.B observable observable + -(mean * mean) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalSmulGNS_B_eq
          w hw cutoff half centered centered))
      (centralPhysicalCenteredObservable_norm_identity
        w hw cutoff half observable)
  exact le_of_eqv_le (Q'.eqv_symm hleft)
    (le_of_le_eqv hcenteredFinite
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left rate _ _ hright)
        (Q'.eqv_refl error)))

/-! ## 2. A Type-level asymptotic sixteenth modulus -/

/-- A cutoff modulus for the physical mean-zero sixteenth with arbitrarily
small additive error. -/
structure FixedNomeCutoffCenteredSixteenthModulus
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  cutoff : Q' → Nat
  meanZeroGap :
    ∀ epsilon : Q', (0 : Q') < epsilon →
      ∀ K : Nat, cutoff epsilon ≤ K →
        ∀ observable : EdgeLabelling → Q',
          CentralPhysicalMeanZero w hw K half observable →
            Q'.abs
                (centralPhysicalJointQuadratic
                  w hw K half observable) ≤
              physicalCutoffSixteenth *
                  centralPhysicalWeightedInner
                    w hw K half observable observable +
                epsilon

namespace FixedNomeCutoffCenteredSixteenthModulus

/-- An exact cutoff-uniform sixteenth supplies the asymptotic modulus with
threshold zero. -/
def ofExact
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCutoffCenteredSixteenth w hw half) :
    FixedNomeCutoffCenteredSixteenthModulus w hw half where
  cutoff := fun _ => 0
  meanZeroGap := by
    intro epsilon hepsilon K _ observable hmean
    exact Q'.le_trans' _ _ _
      (certificate.meanZeroGap K observable hmean)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

end FixedNomeCutoffCenteredSixteenthModulus

/-! ## 3. Contraction into the strict eventual-order limit gap -/

/-- An asymptotic sixteenth with an explicit cutoff modulus proves the strict
connected cutoff-limit gap in the transitive Bishop-real eventual order. -/
theorem centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate :
      FixedNomeCutoffCenteredSixteenthModulus
        w (Q'.le_of_lt hw0) half)
    (observable : CentralPhysicalUnitObservable) :
    CReal.leEv
      (centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable)
      (CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalConnectedNormCutoffLimit
          hw0 hw1 half observable)) := by
  intro epsilon hepsilon
  refine ⟨certificate.cutoff epsilon, ?_⟩
  intro K hK
  let hw := Q'.le_of_lt hw0
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let transferred :=
    centralPhysicalMarkovApply w hw K half observable.value
  let mean :=
    centralPhysicalStationaryMean w hw K half observable.value
  have hfinite :=
    centralPhysical_centeredCorrection_form_le_of_abs_gap_add
      w hw K half physicalCutoffSixteenth epsilon
      (certificate.meanZeroGap epsilon hepsilon K hK)
      observable.value
  have hleft :
      (centralPhysicalConnectedAutocorrelationCutoffLimit
          hw0 hw1 half observable).approx K ≈
        E.B observable.value observable.value + -(mean * mean) := by
    exact Q'.add_eqv_congr'
      (D.B_symm observable.value transferred) (Q'.eqv_refl _)
  have hright :
      physicalCutoffSixteenth *
            (D.B observable.value observable.value + -(mean * mean)) +
          epsilon ≈
        (CReal.mul
            (CReal.ofQ' physicalCutoffSixteenth)
            (centralPhysicalConnectedNormCutoffLimit
              hw0 hw1 half observable)).approx K + epsilon := by
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left physicalCutoffSixteenth _ _
        (Q'.eqv_refl _))
      (Q'.eqv_refl epsilon)
  exact le_of_eqv_le hleft (le_of_le_eqv hfinite hright)

/-- The exact cutoff-uniform certificate recovers the eventual-order theorem
through its zero-threshold modulus. -/
theorem centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth_of_exact
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate :
      FixedNomeCutoffCenteredSixteenth w (Q'.le_of_lt hw0) half)
    (observable : CentralPhysicalUnitObservable) :
    CReal.leEv
      (centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable)
      (CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalConnectedNormCutoffLimit
          hw0 hw1 half observable)) :=
  centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth
    hw0 hw1 half
    (FixedNomeCutoffCenteredSixteenthModulus.ofExact certificate)
    observable

/-! ## Axiom audit -/

#print axioms
  centralPhysical_centeredCorrection_form_le_of_abs_gap_add
#print axioms FixedNomeCutoffCenteredSixteenthModulus.ofExact
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth_of_exact

end YMGap.Continuum.BF4PhysicalCutoffAsymptoticConnectedGap
