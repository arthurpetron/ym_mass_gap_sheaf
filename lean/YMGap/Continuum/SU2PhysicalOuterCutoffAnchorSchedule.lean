/-
# Executable fixed-anchor schedule for the physical SU(2) outer tail

At the strong-coupling anchor `w = 1/400`, the degree-thirteen Casimir tail
already has successive-term ratio at most `1/2` from spin one onward.  Hence
the retained cutoff can be chosen constructively as

  M(precision) = precision,

while the one-coordinate mass ceiling uses the fixed base cutoff `S = 1`.
This file discharges both rational hypotheses required by
`anchorCutoffIncrement_le_tensorEnvelope` and exposes the resulting theorem
with no arithmetic premises beyond `M(precision) <= K`.

This is a fixed-coupling result.  It is uniform in the later Peter--Weyl
cutoff `K`, but it asserts no spacing-uniform estimate along a running
continuum trajectory.

## Axiom gate

Constructive `Nat`/`Q'` recursion only.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail

namespace YMGap.Continuum.SU2PhysicalOuterCutoffAnchorSchedule

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- Fixed one-coordinate prefix used in every precision envelope. -/
def anchorPhysicalBaseCutoff : Nat := 1

/-- Executable retained-spin schedule at the fixed anchor. -/
def anchorPhysicalRetainedCutoff (precision : Nat) : Nat :=
  precision

/-- At `w=1/400`, the crude degree-thirteen ratio is already below one half
from every spin `S >= 1` onward. -/
theorem anchorDegreeThirteenCutoffCondition
    (S : Nat) (hS : 1 ≤ S) :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow anchorCoupling (2 * S + 3) ≤
      HalfPow.half := by
  have hpow :
      qpow anchorCoupling (2 * S + 3) ≤
        qpow anchorCoupling 5 :=
    qpow_antitone (by decide) (by decide)
      5 (2 * S + 3) (by omega)
  have hmul :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow anchorCoupling (2 * S + 3) ≤
        Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow anchorCoupling 5 :=
    Q'.mul_le_mul_of_nonneg_left
      _ _ _ hpow (zero_le_ofNat _)
  refine Q'.le_trans' _ _ _ hmul ?_
  unfold physicalFacePolynomialDegree anchorCoupling
  dsimp [qpow]
  decide

/-- The spin-one degree-thirteen term fits the first dyadic head budget. -/
theorem anchorDegreeThirteenHeadAtBase :
    tailTerm anchorCoupling
        physicalFacePolynomialDegree
        anchorPhysicalBaseCutoff ≤
      dyad 1 := by
  unfold anchorPhysicalBaseCutoff physicalFacePolynomialDegree
    tailTerm anchorCoupling dyad
  dsimp [c4, qpow, Q'.pow]
  decide

private theorem anchorDegreeThirteenHeadFromOne :
    ∀ precision : Nat,
      tailTerm anchorCoupling
          physicalFacePolynomialDegree
          (1 + precision) ≤
        dyad (precision + 1)
  | 0 => by
      simpa using anchorDegreeThirteenHeadAtBase
  | precision + 1 => by
      have ih :=
        anchorDegreeThirteenHeadFromOne precision
      have hratio :=
        tailTerm_ratio
          (w := anchorCoupling)
          (by decide) (by decide)
          physicalFacePolynomialDegree
          1 precision
      have hterm0 :
          (0 : Q') ≤
            tailTerm anchorCoupling
              physicalFacePolynomialDegree
              (1 + precision) :=
        tailTerm_nonneg
          (by decide)
          physicalFacePolynomialDegree
          (1 + precision)
      have hratioHalf :
          Q'.ofNat
                (2 ^ physicalFacePolynomialDegree) *
              qpow anchorCoupling (2 * 1 + 3) ≤
            HalfPow.half :=
        anchorDegreeThirteenCutoffCondition 1
          (Nat.le_refl 1)
      have hfirst :
          (Q'.ofNat
                (2 ^ physicalFacePolynomialDegree) *
              qpow anchorCoupling (2 * 1 + 3)) *
                tailTerm anchorCoupling
                  physicalFacePolynomialDegree
                  (1 + precision) ≤
            HalfPow.half *
                tailTerm anchorCoupling
                  physicalFacePolynomialDegree
                  (1 + precision) :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ hratioHalf hterm0
      have hsecond :
          HalfPow.half *
                tailTerm anchorCoupling
                  physicalFacePolynomialDegree
                  (1 + precision) ≤
            HalfPow.half * dyad (precision + 1) :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ ih HalfPow.half_nonneg
      have hcombined :
          tailTerm anchorCoupling
              physicalFacePolynomialDegree
              (1 + (precision + 1)) ≤
            HalfPow.half * dyad (precision + 1) :=
        Q'.le_trans' _ _ _ hratio
          (Q'.le_trans' _ _ _ hfirst hsecond)
      simpa only [dyad, Q'.pow_succ] using hcombined

/-- Every additional retained spin buys at least one further dyadic power. -/
theorem anchorDegreeThirteenHeadSchedule
    (precision : Nat) :
    tailTerm anchorCoupling
        physicalFacePolynomialDegree
        (anchorPhysicalRetainedCutoff precision + 1) ≤
      dyad (precision + 1) := by
  have hhead :=
    anchorDegreeThirteenHeadFromOne precision
  simpa [anchorPhysicalRetainedCutoff,
    Nat.add_comm] using hhead

theorem anchorPhysicalBaseCutoffCondition :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow anchorCoupling
          (2 * anchorPhysicalBaseCutoff + 3) ≤
      HalfPow.half := by
  exact anchorDegreeThirteenCutoffCondition
    anchorPhysicalBaseCutoff (by decide)

theorem anchorPhysicalRetainedCutoffCondition
    (precision : Nat) :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow anchorCoupling
          (2 *
            (anchorPhysicalRetainedCutoff precision + 1) +
              3) ≤
      HalfPow.half := by
  exact anchorDegreeThirteenCutoffCondition
    (anchorPhysicalRetainedCutoff precision + 1)
    (by omega)

/-- The scheduled one-face shell is dyadically small for every later outer
cutoff.  No relation between `precision` and `K` is needed for this scalar
window estimate. -/
theorem anchorScheduledOuterShell_le_dyad
    (precision K : Nat) :
    su2PhysicalOuterShellMass
        anchorCoupling
        (anchorPhysicalRetainedCutoff precision)
        K ≤
      dyad precision := by
  exact su2PhysicalOuterShellMass_le_dyad
    (w := anchorCoupling) (by decide) (by decide)
    precision
    (M := anchorPhysicalRetainedCutoff precision)
    (K := K)
    (anchorPhysicalRetainedCutoffCondition precision)
    (anchorDegreeThirteenHeadSchedule precision)

/-- Unconditional fixed-anchor increment estimate, apart from the necessary
statement that the later cutoff contains the retained window. -/
theorem anchorScheduledCutoffIncrement_le_tensorEnvelope
    (precision : Nat) {K n : Nat}
    (hretained :
      anchorPhysicalRetainedCutoff precision ≤ K) :
    parametricKCutoffIncrement anchorCoupling
        (anchorPhysicalRetainedCutoff precision)
        K n ≤
      su2PhysicalTensorTailEnvelope
        anchorCoupling
        anchorPhysicalBaseCutoff
        (anchorPhysicalRetainedCutoff precision)
        precision
        (plaquetteEdgeCount n) := by
  exact anchorCutoffIncrement_le_tensorEnvelope
    anchorPhysicalBaseCutoff precision
    hretained
    anchorPhysicalBaseCutoffCondition
    anchorDegreeThirteenHeadAtBase
    (anchorPhysicalRetainedCutoffCondition precision)
    (anchorDegreeThirteenHeadSchedule precision)

#print axioms anchorDegreeThirteenCutoffCondition
#print axioms anchorDegreeThirteenHeadAtBase
#print axioms anchorDegreeThirteenHeadSchedule
#print axioms anchorPhysicalRetainedCutoffCondition
#print axioms anchorScheduledOuterShell_le_dyad
#print axioms anchorScheduledCutoffIncrement_le_tensorEnvelope

end YMGap.Continuum.SU2PhysicalOuterCutoffAnchorSchedule
