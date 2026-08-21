/-
# The fixed-nome physical BF4 connected cutoff gap

The representation-cutoff limits of the connected norm and one-step
autocorrelation are already actual Bishop reals.  A strict limiting gap now
requires one estimate at every representation cutoff in that same sequence.
This module isolates that estimate in two layers:

* `FixedNomeCutoffCenteredSixteenth` is the exact form-level input;
* `FixedNomeCutoffLocalGluing` expands it into one genuine local-slice gluing
  witness at every cutoff.

The local-gluing layer contracts through the arbitrary-extent physical
sixteenth theorem, and the resulting pointwise centered estimate contracts
again into

  connectedAutocorrelationLimit <= (1/16) * connectedNormLimit.

No inhabitant of either cutoff-uniform certificate is constructed here.  In
particular, the existing matched-AF producer cannot be reused: it controls its
own coupled nome/cutoff trajectory, whereas this limit holds the nome and
finite extent fixed while the representation cutoff tends to infinity.

Axiom gate: constructive finite sums, exact rational estimates, and
Bishop-real order only.  No `Classical`, `sorry`, `native_decide`, choice,
functional extensionality, noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
import YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate

namespace YMGap.Continuum.BF4PhysicalCutoffConnectedGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact cutoff-uniform form input -/

/-- The fixed strict rate inherited from a quarter-rate local slice with two
endpoint buffers. -/
def physicalCutoffSixteenth : Q' := Q'.mkPos 1 16 (by decide)

theorem physicalCutoffSixteenth_nonnegative :
    (0 : Q') ≤ physicalCutoffSixteenth := by
  decide

theorem physicalCutoffSixteenth_lt_one :
    physicalCutoffSixteenth < (1 : Q') := by
  decide

/-- The precise form-level datum needed to retain the physical sixteenth while
removing the representation cutoff at fixed nome and finite extent. -/
structure FixedNomeCutoffCenteredSixteenth
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  meanZeroGap :
    ∀ cutoff (observable : EdgeLabelling → Q'),
      CentralPhysicalMeanZero w hw cutoff half observable →
        Q'.abs
            (centralPhysicalJointQuadratic
              w hw cutoff half observable) ≤
          physicalCutoffSixteenth *
            centralPhysicalWeightedInner
              w hw cutoff half observable observable

namespace FixedNomeCutoffCenteredSixteenth

/-- Exact stationary centering turns the supplied mean-zero estimate into the
corrected form estimate for any finite-cutoff observable. -/
theorem centeredCorrection_form_le
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCutoffCenteredSixteenth w hw half)
    (cutoff : Nat) (observable : EdgeLabelling → Q') :
    let D := (centralPhysicalSmulGNS w hw cutoff half).toGNSData
    let E := (centralPhysicalMarkovFormGNS w hw cutoff half).toGNSData
    let mean :=
      centralPhysicalStationaryMean w hw cutoff half observable
    E.B observable observable + -(mean * mean) ≤
      physicalCutoffSixteenth *
        (D.B observable observable + -(mean * mean)) := by
  exact centralPhysical_centeredCorrection_form_le_of_abs_gap
    w hw cutoff half physicalCutoffSixteenth
    (certificate.meanZeroGap cutoff) observable

end FixedNomeCutoffCenteredSixteenth

/-! ## 2. Expansion into genuine local-slice witnesses -/

/-- One local BF4 slice, shared by all positive source rows, at every
representation cutoff of the fixed-nome and fixed-extent family. -/
structure FixedNomeCutoffLocalGluing
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  depth : Nat → Nat
  localRate : Nat → Q'
  localRate_le_quarter :
    ∀ cutoff, localRate cutoff ≤ quarter
  oneStep : Nat → EdgeLabelling → EdgeLabelling → Q'
  localSlice :
    ∀ cutoff,
      PhysicalBF4LocalSliceGluing
        hw cutoff half (depth cutoff) (oneStep cutoff) (localRate cutoff)

namespace FixedNomeCutoffLocalGluing

/-- Genuine cutoff-uniform local gluing constructs the exact centered
sixteenth needed by the limiting form theorem. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCutoffLocalGluing w hw half) :
    FixedNomeCutoffCenteredSixteenth w hw half where
  meanZeroGap := by
    intro cutoff observable hmean
    exact physical_joint_quadratic_abs_le_sixteenth_of_local_gluing
      (certificate.localRate_le_quarter cutoff)
      (fun source hsource =>
        ⟨⟨certificate.oneStep cutoff,
          (certificate.localSlice cutoff).toRow source hsource⟩⟩)
      observable hmean

end FixedNomeCutoffLocalGluing

/-! ## 3. Contraction into the connected Bishop-real gap -/

/-- A sixteenth at every representation cutoff survives as the same strict
factor between the actual connected cutoff-limit forms. -/
theorem centralPhysicalConnectedAutocorrelationCutoffLimit_le_sixteenth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate :
      FixedNomeCutoffCenteredSixteenth w (Q'.le_of_lt hw0) half)
    (observable : CentralPhysicalUnitObservable) :
    centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable ≤
      CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalConnectedNormCutoffLimit
          hw0 hw1 half observable) := by
  intro cutoff
  let hw := Q'.le_of_lt hw0
  let D := (centralPhysicalSmulGNS w hw cutoff half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw cutoff half).toGNSData
  let transferred :=
    centralPhysicalMarkovApply w hw cutoff half observable.value
  let mean :=
    centralPhysicalStationaryMean w hw cutoff half observable.value
  have hfinite := certificate.centeredCorrection_form_le
    cutoff observable.value
  have hleft :
      (centralPhysicalConnectedAutocorrelationCutoffLimit
          hw0 hw1 half observable).approx cutoff ≈
        E.B observable.value observable.value + -(mean * mean) := by
    exact Q'.add_eqv_congr'
      (D.B_symm observable.value transferred) (Q'.eqv_refl _)
  have hright :
      physicalCutoffSixteenth *
          (D.B observable.value observable.value + -(mean * mean)) ≈
        (CReal.mul
            (CReal.ofQ' physicalCutoffSixteenth)
            (centralPhysicalConnectedNormCutoffLimit
              hw0 hw1 half observable)).approx cutoff := by
    exact Q'.mul_eqv_congr_left physicalCutoffSixteenth _ _
      (Q'.eqv_refl _)
  have hcore :
      (centralPhysicalConnectedAutocorrelationCutoffLimit
          hw0 hw1 half observable).approx cutoff ≤
        (CReal.mul
            (CReal.ofQ' physicalCutoffSixteenth)
            (centralPhysicalConnectedNormCutoffLimit
              hw0 hw1 half observable)).approx cutoff :=
    le_of_eqv_le hleft (le_of_le_eqv hfinite hright)
  exact Q'.le_trans' _ _ _ hcore
    (Q'.add_le_self_of_nonneg _ (Q'.invSucc cutoff)
      (Q'.invSucc_nonneg cutoff))

/-- The fully expanded local-gluing certificate gives the same connected
cutoff-limit sixteenth as a direct corollary. -/
theorem
    centralPhysicalConnectedAutocorrelationCutoffLimit_le_sixteenth_of_localGluing
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate :
      FixedNomeCutoffLocalGluing w (Q'.le_of_lt hw0) half)
    (observable : CentralPhysicalUnitObservable) :
    centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable ≤
      CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalConnectedNormCutoffLimit
          hw0 hw1 half observable) :=
  centralPhysicalConnectedAutocorrelationCutoffLimit_le_sixteenth
    hw0 hw1 half certificate.toCenteredSixteenth observable

/-! ## Axiom audit -/

#print axioms physicalCutoffSixteenth_lt_one
#print axioms FixedNomeCutoffLocalGluing.toCenteredSixteenth
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_le_sixteenth
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_le_sixteenth_of_localGluing

end YMGap.Continuum.BF4PhysicalCutoffConnectedGap
