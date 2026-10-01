/-
# Joint signed correction for the original spatial family

The actual first-order projected source, its full angular weight defect, and
the complete-weight Ward residual add to twelve times the SAME original
unnormalized odd variance. Combining this cancellation with the separately
proved actual-source first-order cap leaves the retained negative square,
curvature, and Taylor error as explicit signed debt. The coefficient here is
width-dependent and is not a continuum or mass-gap estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRetainedSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointCorrection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal
  (angularWeightDefect angular_weight_identity)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance wardResidual family_ward)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
  (firstOrderVarianceConstant family_firstOrder_variance_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRetainedSquare
  (projectedObservableSquare retainedVarianceCeiling padded_family_energy_le_retained)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCurvature (curvatureMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
  (sourceFirstOrder_eq_weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceErrorBudget)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  angularWeightDefect wardResidual oddMass oddVariance sourceFirstOrder
  sourceErrorBudget curvatureMoment projectedObservableSquare firstOrderVarianceConstant

private def minus (a b : PolyExpr) : PolyExpr := .add a (.neg b)

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

/-- The computed first-order source and BOTH signed complete-weight
corrections cancel into the original odd-marginal variance. -/
theorem family_firstOrder_defect_ward {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
    (sourceFirstOrder (N width-1) q f +
      angularWeightDefect w K width (n+1) f) +
      wardResidual hw0 hw1 K width hK (n+1) f ≈
      12*(oddMass w K width (n+1) *
        oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width) q := by
    unfold q projectedEndpointSource
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width (n+1)))
  have hf : SupportedQuaternionBlocks (N width) f := spatialSpan_supported width c qs
  have hind := spatialSpan_fringe_independent_after_padding hwidth c qs hqs
  have hfirst := sourceFirstOrder_eq_weightedAngularEnergy
    (N width-1) q f (by simpa only [hN] using hq)
    (by simpa only [hN] using hf)
  have hweight := angular_weight_identity w K width (n+1) f hf
    (baseLinks_positive width) hind
  have hward := family_ward hw0 hw1 K width hK (n+1) qs c
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hfirst (Q'.eqv_refl _)) (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hweight (Q'.eqv_refl _)) hward)

/-- The leading coefficients retain their literal half-time normalization. -/
def jointStep (w : Q') : Q' := (1 : Q')-w

def jointHalfSquare (w : Q') : Q' :=
  HalfPow.half*(jointStep w*jointStep w)

def jointTotalStep (w : Q') : Q' := jointStep w + jointHalfSquare w

/-- The three source-dependent signed terms that must be combined before
bounding any one of them. -/
def jointRaw {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  jointHalfSquare w * sourceFirstOrder (N width-1) q f -
    jointStep w * angularWeightDefect w K width n f -
    jointStep w * wardResidual hw0 hw1 K width hK n f

/-- Remaining signed debt, not estimated relative to the SAME variance:
curvature, the retained source square, and the full finite-cutoff Taylor error. -/
def jointDebt (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  jointHalfSquare w *
    (-curvatureMoment w K width n f - 48*projectedObservableSquare w K width n f) +
    sourceErrorBudget (N width-1) w K q f

private theorem jointTotalStep_nonnegative {w : Q'} (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ jointTotalStep w := by
  have hh : (0 : Q') ≤ jointStep w := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have ha : (0 : Q') ≤ jointHalfSquare w :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg (Q'.mul_nonneg _ _ hh hh)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : (0 : Q') ≈ 0+0))
    (Q'.add_le_add hh ha)

/-- The source cap is applied ONLY after exact joint Ward cancellation.
The full original unnormalized variance stays on the right. -/
theorem jointRaw_le_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width c qs
    jointRaw hw0 hw1 K width hK (n+1) f ≤
      (jointTotalStep w * firstOrderVarianceConstant hw0 hw1 width -
        12*jointStep w) *
        (oddMass w K width (n+1) *
          oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let f := spatialSpan width c qs
  let A := sourceFirstOrder (N width-1)
    (projectedEndpointSource w K width (terminalMessage w K width (n+1))) f
  let D := angularWeightDefect w K width (n+1) f
  let W := wardResidual hw0 hw1 K width hK (n+1) f
  let S := oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f
  let U := firstOrderVarianceConstant hw0 hw1 width
  let h := jointStep w
  let a := jointHalfSquare w
  let t := jointTotalStep w
  have hj : (A+D)+W ≈ 12*S :=
    family_firstOrder_defect_ward hw0 hw1 K hwidth hK n qs c hqs
  have hb : A ≤ U*S :=
    family_firstOrder_variance_bound hw0 hw1 K width hK n c qs
      (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hraw : jointRaw hw0 hw1 K width hK (n+1) f ≈
      t*A - h*((A+D)+W) :=
    poly_identity_of_normal_eq
      (minus (minus (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.var 2) (.var 4)))
      (minus (.mul (.add (.var 2) (.var 0)) (.var 1))
        (.mul (.var 2) (.add (.add (.var 1) (.var 3)) (.var 4))))
      (by decide) (fun | 0 => a | 1 => A | 2 => h | 3 => D | _ => W)
  have hpin : t*A - h*((A+D)+W) ≈ t*A - h*(12*S) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left h _ _ hj))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ t hb
    (jointTotalStep_nonnegative hw1)
  have hmove := Q'.add_le_add_right _ _ (-(h*(12*S))) hscaled
  have hright : t*(U*S) - h*(12*S) ≈ (t*U-12*h)*S :=
    poly_identity_of_normal_eq
      (minus (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 3) (.mul (.const 12) (.var 2))))
      (.mul (minus (.mul (.var 0) (.var 1)) (.mul (.const 12) (.var 3)))
        (.var 2))
      (by decide) (fun | 0 => t | 1 => U | 2 => S | _ => h)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hraw)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ hmove (Q'.le_of_eqv hright)))

/-- The original retained ceiling is exactly joint signed correction plus
the remaining debt, normalized by its ORIGINAL odd partition. -/
theorem retainedVarianceCeiling_eq_joint {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    retainedVarianceCeiling hw0 hw1 K width hK n f ≈
      (jointRaw hw0 hw1 K width hK n f + jointDebt w K width n f) *
        Q'.recipPos (oddMass w K width n)
          (oddMass_positive hw0 hw1 K width hK n) := by
  unfold retainedVarianceCeiling jointRaw jointDebt jointHalfSquare jointStep
  exact poly_identity_of_normal_eq
    (.mul
      (minus
        (minus
          (.add (.mul (.var 0)
            (.add (minus (.neg (.var 1)) (.mul (.const 48) (.var 2)))
              (.var 3))) (.var 4))
          (.mul (.var 5) (.var 6)))
        (.mul (.var 5) (.var 7)))
      (.var 8))
    (.mul
      (.add
        (minus (minus (.mul (.var 0) (.var 3)) (.mul (.var 5) (.var 6)))
          (.mul (.var 5) (.var 7)))
        (.add (.mul (.var 0)
          (minus (.neg (.var 1)) (.mul (.const 48) (.var 2)))) (.var 4)))
      (.var 8))
    (by decide) (fun
      | 0 => HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
      | 1 => curvatureMoment w K width n f
      | 2 => projectedObservableSquare w K width n f
      | 3 => sourceFirstOrder (N width-1)
          (projectedEndpointSource w K width (terminalMessage w K width n)) f
      | 4 => sourceErrorBudget (N width-1) w K
          (projectedEndpointSource w K width (terminalMessage w K width n)) f
      | 5 => (1 : Q')-w
      | 6 => angularWeightDefect w K width n f
      | 7 => wardResidual hw0 hw1 K width hK n f
      | _ => Q'.recipPos (oddMass w K width n)
          (oddMass_positive hw0 hw1 K width hK n))

/-- The retained ceiling has a SAME-variance upper bound with the precise
signed curvature/source-square/Taylor debt still visible. -/
theorem retainedCeiling_le_jointVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width c qs
    retainedVarianceCeiling hw0 hw1 K width hK (n+1) f ≤
      (jointTotalStep w * firstOrderVarianceConstant hw0 hw1 width -
        12*jointStep w) *
        oddVariance hw0 hw1 K width hK (n+1) f +
      jointDebt w K width (n+1) f *
        Q'.recipPos (oddMass w K width (n+1))
          (oddMass_positive hw0 hw1 K width hK (n+1)) := by
  dsimp only
  let f := spatialSpan width c qs
  let z := oddMass w K width (n+1)
  let v := oddVariance hw0 hw1 K width hK (n+1) f
  let r := Q'.recipPos z (oddMass_positive hw0 hw1 K width hK (n+1))
  let b := jointDebt w K width (n+1) f
  let d := jointTotalStep w * firstOrderVarianceConstant hw0 hw1 width -
    12*jointStep w
  have hraw := jointRaw_le_variance hw0 hw1 K hwidth hK n qs c hqs
  have hshift := Q'.add_le_add_right _ _ b hraw
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ r hshift
    (Q'.le_of_lt (Q'.recipPos_pos z (oddMass_positive hw0 hw1 K width hK (n+1))))
  have hcore : (d*(z*v))*r ≈ d*v := by
    have hperm : (d*(z*v))*r ≈ d*(v*(z*r)) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
        (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3))))
        (by decide) (fun | 0 => d | 1 => z | 2 => v | _ => r)
    exact Q'.eqv_trans _ _ _ hperm
      (Q'.mul_eqv_congr_left d _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left v _ _
            (Q'.mul_recipPos_eqv z (oddMass_positive hw0 hw1 K width hK (n+1))))
          (Q'.mul_one_eqv v)))
  have hright : (d*(z*v)+b)*r ≈ d*v+b*r :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr' hcore (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (retainedVarianceCeiling_eq_joint
      hw0 hw1 K width hK (n+1) f))
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hright))

/-- Original normalized temporal energy, bounded against its SAME odd
variance. The displayed debt remains signed and is not asserted small. -/
theorem padded_family_energy_le_jointVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width c qs
    normalizedEnergy hw0 hw1 K width hK (n+1) f ≤
      (jointTotalStep w * firstOrderVarianceConstant hw0 hw1 width) *
        oddVariance hw0 hw1 K width hK (n+1) f +
      jointDebt w K width (n+1) f *
        Q'.recipPos (oddMass w K width (n+1))
          (oddMass_positive hw0 hw1 K width hK (n+1)) := by
  dsimp only
  let f := spatialSpan width c qs
  let v := oddVariance hw0 hw1 K width hK (n+1) f
  let b := jointDebt w K width (n+1) f *
    Q'.recipPos (oddMass w K width (n+1))
      (oddMass_positive hw0 hw1 K width hK (n+1))
  let h := jointStep w
  let t := jointTotalStep w
  let U := firstOrderVarianceConstant hw0 hw1 width
  have henergy := padded_family_energy_le_retained hw0 hw1 K hwidth hK
    (n+1) qs c hqs
  have hceiling := retainedCeiling_le_jointVariance hw0 hw1 K
    hwidth hK n qs c hqs
  have hstep := Q'.add_le_add_left (12*(((1 : Q')-w)*v)) _ _ hceiling
  have hscalar : 12*(h*v)+((t*U-12*h)*v+b) ≈ (t*U)*v+b :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 12) (.mul (.var 0) (.var 1)))
        (.add (.mul (minus (.mul (.var 2) (.var 3))
          (.mul (.const 12) (.var 0))) (.var 1)) (.var 4)))
      (.add (.mul (.mul (.var 2) (.var 3)) (.var 1)) (.var 4))
      (by decide) (fun | 0 => h | 1 => v | 2 => t | 3 => U | _ => b)
  exact Q'.le_trans' _ _ _ henergy
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hscalar))

#print axioms family_firstOrder_defect_ward
#print axioms jointStep
#print axioms jointHalfSquare
#print axioms jointTotalStep
#print axioms jointRaw
#print axioms jointDebt
#print axioms jointRaw_le_variance
#print axioms retainedVarianceCeiling_eq_joint
#print axioms retainedCeiling_le_jointVariance
#print axioms padded_family_energy_le_jointVariance

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointCorrection
