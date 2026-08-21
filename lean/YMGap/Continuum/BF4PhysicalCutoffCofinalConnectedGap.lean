/-
# Cofinal fixed-nome physical BF4 connected cutoff gap

The strict representation-cutoff limit does not require a finite sixteenth at
every cutoff.  Because the connected norm and autocorrelation streams are
already Cauchy, it is enough to have exact finite strictness on a constructively
chosen cofinal subsequence.  This module packages such an anchor function,
optionally expands each anchor into a genuine local-slice gluing witness, and
uses the two Cauchy estimates to prove the same strict `CReal.leEv` limit gap.

This is weaker than both cutoff-uniform local gluing and an all-later-cutoff
error modulus.  It is the natural interface for a sparse family of certified
representation cutoffs.  No such cofinal family is constructed here, and the
existing matched-AF scale family still changes the nome along with the cutoff.

Axiom gate: constructive finite estimates and Bishop-real Cauchy reasoning
only.  No `Classical`, `sorry`, `native_decide`, choice, functional
extensionality, noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4PhysicalCutoffAsymptoticConnectedGap

namespace YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffAsymptoticConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
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

/-! ## 1. Exact strictness on a cofinal cutoff subsequence -/

/-- A constructively selected unbounded subsequence of representation cutoffs
carrying the exact physical mean-zero sixteenth. -/
structure FixedNomeCofinalCenteredSixteenth
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  meanZeroGap :
    ∀ base (observable : EdgeLabelling → Q'),
      CentralPhysicalMeanZero
          w hw (anchor base) half observable →
        Q'.abs
            (centralPhysicalJointQuadratic
              w hw (anchor base) half observable) ≤
          physicalCutoffSixteenth *
            centralPhysicalWeightedInner
              w hw (anchor base) half observable observable

namespace FixedNomeCofinalCenteredSixteenth

/-- At every selected anchor, exact centering turns the mean-zero sixteenth
into the corresponding connected approximation inequality. -/
theorem connectedApprox_le_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half)
    (base : Nat) (observable : CentralPhysicalUnitObservable) :
    let K := certificate.anchor base
    let D := (centralPhysicalSmulGNS w hw K half).toGNSData
    let mean :=
      centralPhysicalStationaryMean w hw K half observable.value
    centralPhysicalWeightedInner w hw K half observable.value
          (centralPhysicalMarkovApply
            w hw K half observable.value) +
        -(mean * mean) ≤
      physicalCutoffSixteenth *
        (D.B observable.value observable.value + -(mean * mean)) := by
  let K := certificate.anchor base
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let transferred :=
    centralPhysicalMarkovApply w hw K half observable.value
  let mean :=
    centralPhysicalStationaryMean w hw K half observable.value
  have hfinite := centralPhysical_centeredCorrection_form_le_of_abs_gap
    w hw K half physicalCutoffSixteenth
    (certificate.meanZeroGap base) observable.value
  have hleft :
      centralPhysicalWeightedInner w hw K half observable.value
            transferred + -(mean * mean) ≈
        (centralPhysicalMarkovFormGNS
            w hw K half).toGNSData.B
              observable.value observable.value + -(mean * mean) := by
    exact Q'.add_eqv_congr'
      (D.B_symm observable.value transferred) (Q'.eqv_refl _)
  exact le_of_eqv_le hleft hfinite

end FixedNomeCofinalCenteredSixteenth

/-! ## 2. Expansion into cofinal genuine local slices -/

/-- Genuine local-slice gluing only at the selected unbounded representation
cutoffs. -/
structure FixedNomeCofinalLocalGluing
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  depth : Nat → Nat
  localRate : Nat → Q'
  localRate_le_quarter :
    ∀ base, localRate base ≤ quarter
  oneStep : Nat → EdgeLabelling → EdgeLabelling → Q'
  localSlice :
    ∀ base,
      PhysicalBF4LocalSliceGluing
        hw (anchor base) half (depth base)
        (oneStep base) (localRate base)

namespace FixedNomeCofinalLocalGluing

/-- Cofinal local slices construct the cofinal centered sixteenth. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalLocalGluing w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half where
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hmean
    exact physical_joint_quadratic_abs_le_sixteenth_of_local_gluing
      (certificate.localRate_le_quarter base)
      (fun source hsource =>
        ⟨⟨certificate.oneStep base,
          (certificate.localSlice base).toRow source hsource⟩⟩)
      observable hmean

end FixedNomeCofinalLocalGluing

/-! ## 3. Cauchy contraction from the cofinal anchors -/

/-- Exact strictness on any constructively cofinal cutoff subsequence survives
as the same strict connected gap in the transitive eventual order. -/
theorem centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth_of_cofinal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate :
      FixedNomeCofinalCenteredSixteenth
        w (Q'.le_of_lt hw0) half)
    (observable : CentralPhysicalUnitObservable) :
    CReal.leEv
      (centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable)
      (CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalConnectedNormCutoffLimit
          hw0 hw1 half observable)) := by
  let autocorrelation :=
    centralPhysicalConnectedAutocorrelationCutoffLimit
      hw0 hw1 half observable
  let norm :=
    centralPhysicalConnectedNormCutoffLimit
      hw0 hw1 half observable
  intro epsilon hepsilon
  let delta := HalfPow.half * epsilon
  have hdelta : (0 : Q') < delta :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨autocorrelationCutoff, hauto⟩ :=
    autocorrelation.cauchy delta hdelta
  obtain ⟨normCutoff, hnorm⟩ := norm.cauchy delta hdelta
  let base := max autocorrelationCutoff normCutoff
  let anchor := certificate.anchor base
  have hbaseAnchor : base ≤ anchor := certificate.anchor_ge base
  have hautoAnchor : autocorrelationCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_left _ _) hbaseAnchor
  have hnormAnchor : normCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_right _ _) hbaseAnchor
  refine ⟨base, ?_⟩
  intro cutoff hcutoff
  have hautoCutoff : autocorrelationCutoff ≤ cutoff :=
    Nat.le_trans (Nat.le_max_left _ _) hcutoff
  have hnormCutoff : normCutoff ≤ cutoff :=
    Nat.le_trans (Nat.le_max_right _ _) hcutoff
  have hautoToAnchor :
      autocorrelation.approx cutoff ≤
        autocorrelation.approx anchor + delta :=
    (hauto cutoff anchor hautoCutoff hautoAnchor).1
  have hnormFromAnchor :
      norm.approx anchor ≤ norm.approx cutoff + delta :=
    (hnorm anchor cutoff hnormAnchor hnormCutoff).1
  have hanchorGap :
      autocorrelation.approx anchor ≤
        physicalCutoffSixteenth * norm.approx anchor := by
    simpa only [autocorrelation, norm, anchor, base,
      centralPhysicalConnectedAutocorrelationCutoffLimit_approx,
      centralPhysicalConnectedNormCutoffLimit_approx] using
        certificate.connectedApprox_le_sixteenth base observable
  have hscaledNorm :
      physicalCutoffSixteenth * norm.approx anchor ≤
        physicalCutoffSixteenth * (norm.approx cutoff + delta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hnormFromAnchor
      physicalCutoffSixteenth_nonnegative
  have hscaleDelta : physicalCutoffSixteenth * delta ≤ delta := by
    exact Q'.le_trans' _ ((1 : Q') * delta) _
      (Q'.mul_le_mul_of_nonneg_right _ _ delta
        (Q'.le_of_lt physicalCutoffSixteenth_lt_one)
        (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  have herror : physicalCutoffSixteenth * delta + delta ≤ epsilon := by
    exact Q'.le_trans' _ (delta + delta) _
      (Q'.add_le_add_right _ _ delta hscaleDelta)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  refine Q'.le_trans' _ _ _ hautoToAnchor ?_
  refine Q'.le_trans' _
    (physicalCutoffSixteenth * norm.approx anchor + delta) _
    (Q'.add_le_add_right _ _ delta hanchorGap) ?_
  refine Q'.le_trans' _
    (physicalCutoffSixteenth * (norm.approx cutoff + delta) + delta) _
    (Q'.add_le_add_right _ _ delta hscaledNorm) ?_
  refine Q'.le_trans' _
    (physicalCutoffSixteenth * norm.approx cutoff +
      (physicalCutoffSixteenth * delta + delta)) _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((physicalCutoffSixteenth * norm.approx cutoff +
            physicalCutoffSixteenth * delta) + delta) _
        (Q'.add_eqv_congr_right _ _ delta
          (Q'.mul_add_eqv physicalCutoffSixteenth
            (norm.approx cutoff) delta))
        (Q'.add_assoc_eqv
          (physicalCutoffSixteenth * norm.approx cutoff)
          (physicalCutoffSixteenth * delta) delta))) ?_
  exact Q'.add_le_add_left
    (physicalCutoffSixteenth * norm.approx cutoff)
    (physicalCutoffSixteenth * delta + delta) epsilon herror

/-- Cofinal genuine local gluing gives the strict connected cutoff-limit gap. -/
theorem
    centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth_of_cofinalLocalGluing
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate :
      FixedNomeCofinalLocalGluing w (Q'.le_of_lt hw0) half)
    (observable : CentralPhysicalUnitObservable) :
    CReal.leEv
      (centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable)
      (CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalConnectedNormCutoffLimit
          hw0 hw1 half observable)) :=
  centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth_of_cofinal
    hw0 hw1 half certificate.toCenteredSixteenth observable

/-! ## Axiom audit -/

#print axioms
  FixedNomeCofinalCenteredSixteenth.connectedApprox_le_sixteenth
#print axioms FixedNomeCofinalLocalGluing.toCenteredSixteenth
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth_of_cofinal
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_leEv_sixteenth_of_cofinalLocalGluing

end YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
