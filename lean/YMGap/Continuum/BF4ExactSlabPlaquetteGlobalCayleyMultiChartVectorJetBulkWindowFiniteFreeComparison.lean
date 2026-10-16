/-
# Finite FREE comparison for the actual selected-window centered deficit

The actual finite selected-window centered ORIGINAL deficit pair is placed on
the squared `2^66` normalization.  Its exact SAME-ORIGINAL non-jet remainder,
the selected-window/full-slab law-and-centering defect, and the complete
full-slab multi-chart-to-FREE residual are retained as three separately named
terms.  Their sum has an explicit finite constructive-real absolute bound.

This is a finite comparison.  It does not prove that the total residual is
small enough to pay a strict margin, remove a cutoff, construct a continuum
Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
  (centeredPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
  (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarCharacterInterval
  (heatRatio heatRemainderBound)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The actual finite selected-window centered ORIGINAL deficit pair consumed
by milestone 384. -/
def originalBulkDeficitOwnCenteredWindowPair
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  centeredPair hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L
    (sourcePolynomial (originalBulkDeficitExpression s hs))
    (originalBulkDeficitOwnMean hw0 hw1 s hs stage n)

/-- The actual centered deficit pair on the common pair normalization
`(2^66)^2`. -/
def originalBulkDeficitOwnScaledCenteredWindowPair
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  let scale := globalCayleyVectorJetNorthWeightScale
  (scale * scale) *
    originalBulkDeficitOwnCenteredWindowPair hw0 hw1 s hs stage n L

/-- The scaled SAME-ORIGINAL non-jet remainder isolated in milestone 384. -/
def originalBulkDeficitOwnScaledCenteredNonJetRemainder
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  let scale := globalCayleyVectorJetNorthWeightScale
  (scale * scale) *
    (originalBulkDeficitOwnCenteredWindowPair hw0 hw1 s hs stage n L +
      -originalBulkVectorQuadraticJetWindowPair
        hw0 hw1 s hs stage n L)

/-- Exact finite selected-window split after the common pair scaling. -/
theorem originalBulkDeficitOwnScaledCenteredWindowPair_jet_remainder_split
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    originalBulkDeficitOwnScaledCenteredWindowPair
        hw0 hw1 s hs stage n L ≈
      originalBulkVectorQuadraticJetScaledWindowPair
          hw0 hw1 s hs stage n L +
        originalBulkDeficitOwnScaledCenteredNonJetRemainder
          hw0 hw1 s hs stage n L := by
  let scaleSquare := globalCayleyVectorJetNorthWeightScale *
    globalCayleyVectorJetNorthWeightScale
  let total := originalBulkDeficitOwnCenteredWindowPair
    hw0 hw1 s hs stage n L
  let jet := originalBulkVectorQuadraticJetWindowPair
    hw0 hw1 s hs stage n L
  change scaleSquare * total ≈
    scaleSquare * jet + scaleSquare * (total + -jet)
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.var 1))
    (.add (.mul (.var 0) (.var 2))
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))))
    (by decide)
    (fun
      | 0 => scaleSquare
      | 1 => total
      | _ => jet)

/-- Constructive-real lift of the exact scaled selected-window split. -/
theorem originalBulkDeficitOwnScaledCenteredWindowPair_creal_jet_remainder_split
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    CReal.Equiv
      (CReal.ofQ'
        (originalBulkDeficitOwnScaledCenteredWindowPair
          hw0 hw1 s hs stage n L))
      (CReal.add
        (CReal.ofQ'
          (originalBulkVectorQuadraticJetScaledWindowPair
            hw0 hw1 s hs stage n L))
        (CReal.ofQ'
          (originalBulkDeficitOwnScaledCenteredNonJetRemainder
            hw0 hw1 s hs stage n L))) := by
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    originalBulkDeficitOwnScaledCenteredWindowPair_jet_remainder_split
      hw0 hw1 s hs stage n L)

/-- Explicit scaled form of the milestone-384 SAME-ORIGINAL non-jet budget. -/
def originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  let scale := globalCayleyVectorJetNorthWeightScale
  (scale * scale) *
    originalBulkCenteredRemainderGeometricBudget
      hw0 hw1 hd hsRate s hs n

theorem originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) :
    (0 : Q') ≤
      originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound
        hw0 hw1 hd hsRate s hs n := by
  unfold originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound
  exact Q'.mul_nonneg _ _ (by decide)
    (originalBulkCenteredRemainderGeometricBudget_nonnegative
      hw0 hw1 hd hsRate s hs n)

/-- The scaled SAME-ORIGINAL non-jet remainder obeys its explicit geometric
budget. -/
theorem originalBulkDeficitOwnScaledCenteredNonJetRemainder_abs_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    Q'.abs
        (originalBulkDeficitOwnScaledCenteredNonJetRemainder
          hw0 hw1 s hs stage n L) ≤
      originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound
        hw0 hw1 hd hsRate s hs n := by
  let scaleSquare := globalCayleyVectorJetNorthWeightScale *
    globalCayleyVectorJetNorthWeightScale
  let total := originalBulkDeficitOwnCenteredWindowPair
    hw0 hw1 s hs stage n L
  let jet := originalBulkVectorQuadraticJetWindowPair
    hw0 hw1 s hs stage n L
  let budget := originalBulkCenteredRemainderGeometricBudget
    hw0 hw1 hd hsRate s hs n
  have hremainder :=
    originalBulkDeficitOwn_centeredPair_sub_jet_absolute_geometric_le
      hw0 hw1 hsmall hd hsRate s hs stage n L
  change Q'.abs (total + -jet) ≤ budget at hremainder
  have hscale : (0 : Q') ≤ scaleSquare := by
    unfold scaleSquare globalCayleyVectorJetNorthWeightScale
    decide
  change Q'.abs (scaleSquare * (total + -jet)) ≤ scaleSquare * budget
  exact Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le scaleSquare (total + -jet)) (by
      rw [ExpNeg.abs_of_nonneg hscale]
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ hremainder hscale)

/-- The three macro-residuals in the finite selected-window-to-FREE
comparison: SAME-ORIGINAL non-jet, window/full-slab law, and complete
full-slab multi-chart comparison. -/
def originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (half s : Nat) (hs : 0 < s) (stage n L : Nat) : CReal :=
  CReal.add
    (CReal.ofQ'
      (originalBulkDeficitOwnScaledCenteredNonJetRemainder
        hw0 hw1 s hs stage n L))
    (CReal.add
      (globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
        hw0 hw1 half s hs stage n L n (n + L))
      (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
        w hw0 hw1 half s hs stage n (n + L)))

private theorem cadd_three_reorder (first second third : CReal) :
    CReal.Equiv
      (CReal.add (CReal.add first second) third)
      (CReal.add first (CReal.add third second)) := by
  exact SumOfSquares.Equiv_of_approx_eqv (fun index =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.var 0) (.add (.var 2) (.var 1)))
      (by decide)
      (fun
        | 0 => first.approx index
        | 1 => second.approx index
        | _ => third.approx index))

private theorem cadd_four_reorder
    (first second third fourth : CReal) :
    CReal.Equiv
      (CReal.add (CReal.add first (CReal.add second third)) fourth)
      (CReal.add first (CReal.add fourth (CReal.add second third))) := by
  exact SumOfSquares.Equiv_of_approx_eqv (fun index =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 1) (.var 2))) (.var 3))
      (.add (.var 0) (.add (.var 3) (.add (.var 1) (.var 2))))
      (by decide)
      (fun
        | 0 => first.approx index
        | 1 => second.approx index
        | 2 => third.approx index
        | _ => fourth.approx index))

/-- Exact finite comparison of the actual scaled selected-window centered
deficit pair with the finite FREE identity-quadratic covariance. -/
theorem originalBulkDeficitOwnScaledCenteredWindow_finiteFree_total_split
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (half s : Nat) (hs : 0 < s) (stage n L : Nat)
    (hwidth : s * s ≤ centralExtent half)
    (htime : n + L ≤ centralExtent half) :
    CReal.Equiv
      (CReal.ofQ'
        (originalBulkDeficitOwnScaledCenteredWindowPair
          hw0 hw1 s hs stage n L))
      (CReal.add
        (globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
          half s hs stage n (n + L))
        (originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual
          hw0 hw1 half s hs stage n L)) := by
  let selected := CReal.ofQ'
    (originalBulkDeficitOwnScaledCenteredWindowPair
      hw0 hw1 s hs stage n L)
  let jet := CReal.ofQ'
    (originalBulkVectorQuadraticJetScaledWindowPair
      hw0 hw1 s hs stage n L)
  let sameOriginal := CReal.ofQ'
    (originalBulkDeficitOwnScaledCenteredNonJetRemainder
      hw0 hw1 s hs stage n L)
  let pure := globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
    w hw0 hw1 half s hs n (n + L)
  let law := globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
    hw0 hw1 half s hs stage n L n (n + L)
  let multi := globalCayleyVectorJetBulkCenteredMultiChartReassemblyResponse
    w hw0 hw1 half s hs n (n + L)
  let free := globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
    half s hs stage n (n + L)
  let fullResidual := globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
    w hw0 hw1 half s hs stage n (n + L)
  have hselected :=
    originalBulkDeficitOwnScaledCenteredWindowPair_creal_jet_remainder_split
      hw0 hw1 s hs stage n L
  change CReal.Equiv selected (CReal.add jet sameOriginal) at hselected
  have hlaw :=
    originalBulkVectorQuadraticJetScaledWindowPair_fullSlab_split
      hw0 hw1 half s hs stage n L n (n + L)
  change CReal.Equiv jet (CReal.add pure law) at hlaw
  have hpure := globalCayleyVectorJetBulkCenteredMultiChartReassembly_pure
    w hw0 hw1 half s hs n (n + L)
  change CReal.Equiv multi pure at hpure
  have hfree :=
    globalCayleyVectorJetBulkCenteredMultiChart_freeComparison_total_split
      w hw0 hw1 half s hs stage n (n + L)
        (by omega) (by omega) htime
  change CReal.Equiv multi (CReal.add free fullResidual) at hfree
  have hpureFree : CReal.Equiv pure (CReal.add free fullResidual) :=
    hpure.symm.trans hfree
  have hjetFree : CReal.Equiv jet
      (CReal.add free (CReal.add law fullResidual)) :=
    hlaw.trans
      ((Pivot2.add_congr hpureFree (CReal.Equiv.refl law)).trans
        (cadd_three_reorder free fullResidual law))
  exact hselected.trans
    ((Pivot2.add_congr hjetFree (CReal.Equiv.refl sameOriginal)).trans
      (cadd_four_reorder free law fullResidual sameOriginal))

/-- The same capstone with the leading finite FREE term written explicitly as
the existing scaled physical-link `A2` covariance. -/
theorem originalBulkDeficitOwnScaledCenteredWindow_freeA2_total_split
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (half s : Nat) (hs : 0 < s) (stage n L : Nat)
    (hwidth : s * s ≤ centralExtent half)
    (htime : n + L ≤ centralExtent half) :
    CReal.Equiv
      (CReal.ofQ'
        (originalBulkDeficitOwnScaledCenteredWindowPair
          hw0 hw1 s hs stage n L))
      (CReal.add
        (CReal.ofQ'
          ((identityCayleyVectorJetFreeA2Scale *
            identityCayleyVectorJetFreeA2Scale) *
            finiteGaussianCovariance
              (bulkSourceNoiseCount (centralExtent half) s)
              (openCubeBulkCayleyTraceA2
                (centralExtent half) s hs stage n)
              (openCubeBulkCayleyTraceA2
                (centralExtent half) s hs stage (n + L))))
        (originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual
          hw0 hw1 half s hs stage n L)) := by
  have hsplit :=
    originalBulkDeficitOwnScaledCenteredWindow_finiteFree_total_split
      hw0 hw1 half s hs stage n L hwidth htime
  have hA2 :=
    globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance_eq_A2
      half s hs stage n (n + L)
  exact hsplit.trans
    (Pivot2.add_congr hA2
      (CReal.Equiv.refl
        (originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual
          hw0 hw1 half s hs stage n L)))

/-- Explicit finite bound for the three-macro-family selected-window-to-FREE
residual. -/
def originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidualAbsBound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound
      hw0 hw1 hd hsRate s hs n +
    (globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound
        hw0 hw1 hd hsRate half s hs n n (n + L) +
      globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound
        w hw0 hw1 half s hs stage n (n + L))

theorem originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidualAbsBound_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s) (stage n L : Nat) :
    (0 : Q') ≤
      originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidualAbsBound
        hw0 hw1 hd hsRate half s hs stage n L := by
  exact Q'.zero_le_add _ _
    (originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound_nonnegative
      hw0 hw1 hd hsRate s hs n)
    (Q'.zero_le_add _ _
      (globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound_nonnegative
        hw0 hw1 hd hsRate half s hs n n (n + L))
      (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound_nonnegative
        w hw0 hw1 half s hs stage n (n + L)))

/-- Every approximant of the three-family total residual obeys the summed
finite bound. -/
theorem originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual_approx_abs_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s) (stage n L index : Nat) :
    Q'.abs
        ((originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual
          hw0 hw1 half s hs stage n L).approx index) ≤
      originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidualAbsBound
        hw0 hw1 hd hsRate half s hs stage n L := by
  let sameOriginal := originalBulkDeficitOwnScaledCenteredNonJetRemainder
    hw0 hw1 s hs stage n L
  let law := globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect
    hw0 hw1 half s hs stage n L n (n + L)
  let fullResidual := globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
    w hw0 hw1 half s hs stage n (n + L)
  let sameBound := originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound
    hw0 hw1 hd hsRate s hs n
  let lawBound :=
    globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefectAbsBound
      hw0 hw1 hd hsRate half s hs n n (n + L)
  let fullBound :=
    globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound
      w hw0 hw1 half s hs stage n (n + L)
  have hsame := originalBulkDeficitOwnScaledCenteredNonJetRemainder_abs_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change Q'.abs sameOriginal ≤ sameBound at hsame
  have hlaw :=
    globalCayleyVectorJetBulkCenteredWindowToFullSlabLawDefect_approx_abs_le
      hw0 hw1 hsmall hd hsRate half s hs stage n L n (n + L) index
  change Q'.abs (law.approx index) ≤ lawBound at hlaw
  have hfull :=
    globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual_approx_abs_le
      w hw0 hw1 half s hs stage n (n + L) index
  change Q'.abs (fullResidual.approx index) ≤ fullBound at hfull
  change Q'.abs
      (sameOriginal + (law.approx index + fullResidual.approx index)) ≤
    sameBound + (lawBound + fullBound)
  have hinner : Q'.abs (law.approx index + fullResidual.approx index) ≤
      lawBound + fullBound :=
    Q'.le_trans' _ _ _
      (Q'.abs_add_le' (law.approx index) (fullResidual.approx index))
      (Q'.add_le_add hlaw hfull)
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le' sameOriginal
      (law.approx index + fullResidual.approx index))
    (Q'.add_le_add hsame hinner)

private theorem creal_abs_le_of_approx_abs_le
    (value : CReal) (bound : Q')
    (h : ∀ index, Q'.abs (value.approx index) ≤ bound) :
    CReal.leEv (CReal.abs value) (CReal.ofQ' bound) :=
  CReal.leEv_le_ofQ'_of_approx_le h

/-- Constructive-real absolute bound for the complete finite
selected-window-to-FREE comparison residual. -/
theorem originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual_abs_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (half s : Nat) (hs : 0 < s) (stage n L : Nat) :
    CReal.leEv
      (CReal.abs
        (originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual
          hw0 hw1 half s hs stage n L))
      (CReal.ofQ'
        (originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidualAbsBound
          hw0 hw1 hd hsRate half s hs stage n L)) := by
  let residual := originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual
    hw0 hw1 half s hs stage n L
  let bound :=
    originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidualAbsBound
      hw0 hw1 hd hsRate half s hs stage n L
  change CReal.leEv (CReal.abs residual) (CReal.ofQ' bound)
  apply creal_abs_le_of_approx_abs_le residual bound
  intro index
  have h :=
    originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual_approx_abs_le
      hw0 hw1 hsmall hd hsRate half s hs stage n L index
  change Q'.abs (residual.approx index) ≤ bound at h
  exact h

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnScaledCenteredWindowPair_jet_remainder_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnScaledCenteredWindowPair_creal_jet_remainder_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnScaledCenteredNonJetRemainderAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnScaledCenteredNonJetRemainder_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnScaledCenteredWindow_finiteFree_total_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnScaledCenteredWindow_freeA2_total_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidualAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowFiniteFreeComparison.originalBulkDeficitOwnCenteredWindowFiniteFreeTotalResidual_abs_le
