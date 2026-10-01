/-
# Centered square completion on the original signed-family energy

The retained negative commutator square absorbs the raw angular cost without
an eigenpin or score coefficient. Apply this to the ACTUAL odd-centered
observable. Its q^2 square is exactly SAME Z*Var minus the SIGNED original
sourceCorrection. Nothing identifies q^2 with q*Pq or drops that correction.

The concrete family consumer has leading coefficient 12*h+h^2/8, h=1-w.
It retains the original source correction, COMPLETE-weight Ward residual,
cubic/omitted-mode budgets and angular pair debt. Their joint scaling
calibration is still open; this is not a continuum survival or mass theorem.
-/

import YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialRemainderCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
  (sourceMoment sourceCorrection)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceErrorBudget)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairBudget)
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
  (angularSquare)
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted normalizedMoment)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive normalizedWardResidual family_normalized_ward)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported oddCentered_independent centered_source_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialRemainderCancellation (signedRemainder_generic)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (energy_shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

private theorem blockDerivative_shifted (b i j : Nat) (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (blockAngularDerivative b i j (shifted f c))
      (blockAngularDerivative b i j f) := by
  unfold blockAngularDerivative shifted
  have hz := (angularDerivative_smul (4*b+i) (4*b+j) (-c) polyOne).trans
    (((angularDerivative_one (4*b+i) (4*b+j)).smul (-c)).trans
      (RatPolyCoeffEqv.smul_zero (-c)))
  have hf := (angularDerivative_smul (4*b+i) (4*b+j) 1 f).trans
    (RatPolyCoeffEqv.one_smul _)
  exact (angularDerivative_add _ _ _ _).trans
    ((hf.add hz).trans (RatPolyCoeffEqv.add_zero _))

/-- Every literal angular square is invariant under a rational shift.
The equality is coefficientwise; no source independence is asserted. -/
theorem blockSquare_shifted (b : Nat) (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (blockAngularSquare b (shifted f c)) (blockAngularSquare b f) := by
  have h (i j : Nat) := (blockDerivative_shifted b i j f c).mul
    (blockDerivative_shifted b i j f c)
  exact (h 0 1).add ((h 0 2).add ((h 0 3).add
    ((h 1 2).add ((h 1 3).add (h 2 3)))))

theorem marginalAngular_shifted (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') :
    marginalAngular w K width n (shifted f c) ≈ marginalAngular w K width n f := by
  unfold marginalAngular
  exact finSum_eqv_congr_lt _ _ (N width) (fun i _ =>
    haar_of_coeff ((blockSquare_shifted i f c).mul_left _))

/-- Center the observable with its own ORIGINAL mean, not the raw q^2 law.
Only the remainder's observable changes; original energy and angular cost do not. -/
theorem normalizedEnergy_centered_taylor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    normalizedEnergy hw0 hw1 K width hK n f ≈
      ((1 : Q')-w)*normalizedAngular hw0 hw1 K width hK n f +
        normalizedRemainder hw0 hw1 K width hK n (oddCentered hw0 hw1 K width hK n f) := by
  let c := normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hK n)
  have hshift := energy_shifted w K width (terminalMessage_supported w K width n) hf c
  have henergy : normalizedEnergy hw0 hw1 K width hK n f ≈
      normalizedEnergy hw0 hw1 K width hK n (oddCentered hw0 hw1 K width hK n f) :=
    Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hshift)
  have ha : normalizedAngular hw0 hw1 K width hK n
      (oddCentered hw0 hw1 K width hK n f) ≈
        normalizedAngular hw0 hw1 K width hK n f :=
    Q'.mul_eqv_congr_right _ _ _ (marginalAngular_shifted w K width n f c)
  exact Q'.eqv_trans _ _ _ henergy (Q'.eqv_trans _ _ _
    (normalizedEnergy_taylor hw0 hw1 K width hK n _
      (oddCentered_supported hw0 hw1 K width hK n hf) (baseLinks_positive width)
      (fun i hi => oddCentered_independent hw0 hw1 K width hK n i (hind i hi)))
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ ha) (Q'.eqv_refl _)))

/-- The original signed difference between interacting and raw-source
centered square mass. Its sign and scaling size are NOT assumed. -/
def centeredCorrection {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  sourceCorrection (N width) w K (List.range (N width))
    (projectedEndpointSource w K width (terminalMessage w K width n))
    (oddCentered hw0 hw1 K width hK n f)

/-- Exact SAME-variance pin; the q^2 to q*Pq mismatch stays SIGNED. -/
theorem centered_sourceSquare_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    sourceSquareMass (N width-1)
        (projectedEndpointSource w K width (terminalMessage w K width n))
        (oddCentered hw0 hw1 K width hK n f) ≈
      oddMass w K width n * oddVariance hw0 hw1 K width hK n f -
        centeredCorrection hw0 hw1 K width hK n f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let psi := oddCentered hw0 hw1 K width hK n f
  let Q := H (N width) (polyMul (polyMul q psi) (polyMul q psi))
  let M := sourceMoment (N width) w K (List.range (N width)) q (polyMul psi psi)
  let C := centeredCorrection hw0 hw1 K width hK n f
  have hc : C ≈ M-Q := by
    refine Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.add (.var 2) (.neg (.var 0))))
      (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))
      (by decide) (fun
        | 0 => q
        | 1 => psi
        | _ => productMap (N width) w K (List.range (N width)) q))) ?_
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (haar_of_coeff (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul _))
          (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (-1) _)
            (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
              (by decide) (fun _ => Q)))))
  have hraw : Q ≈ M-C :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1)
      (by decide) (fun | 0 => M | _ => Q)))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hc)))
  have hm := centered_source_square hw0 hw1 K width hK n hf hind
  unfold sourceSquareMass observableSquare
  rw [hN]
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.add_eqv_congr' hm (Q'.eqv_refl _))

/-- Explicit coefficient h^2/8, independent of width/depth/cutoff/family. -/
def quadraticRate (w : Q') : Q' :=
  (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*squareQuarter

/-- The existing changing-source budgets and SIGNED correction are kept.
This is data, not an assumption that the debt is small or positive. -/
def centeredError {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let psi := oddCentered hw0 hw1 K width hK n f
  let h := (1 : Q')-w
  sourceErrorBudget (N width-1) w K q psi +
    h*((h*h)*pairBudget (N width-1) q (polyMul q (angularSquare (N width-1) psi))) -
      quadraticRate w * centeredCorrection hw0 hw1 K width hK n f

def normalizedCenteredError {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  centeredError hw0 hw1 K width hK n f *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

private theorem partition_cancel (B Z V : Q') (hZ : (0 : Q') < Z) :
    (B*(Z*V))*Q'.recipPos Z hZ ≈ B*V :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => B | 1 => Z | 2 => V | _ => Q'.recipPos Z hZ))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv _))

attribute [local irreducible] oddMass oddVariance sourceErrorBudget pairBudget

theorem normalizedRemainder_centered_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (hquad : sufficientCutoff w ≤ K)
    (n : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    normalizedRemainder hw0 hw1 K width hK n (oddCentered hw0 hw1 K width hK n f) ≤
      quadraticRate w * oddVariance hw0 hw1 K width hK n f +
        normalizedCenteredError hw0 hw1 K width hK n f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let psi := oddCentered hw0 hw1 K width hK n f
  let h := (1 : Q')-w
  let alpha := HalfPow.half*(h*h)
  let Z := oddMass w K width n
  let V := oddVariance hw0 hw1 K width hK n f
  let C := centeredCorrection hw0 hw1 K width hK n f
  let E := sourceErrorBudget (N width-1) w K q psi
  let T := h*((h*h)*pairBudget (N width-1) q (polyMul q (angularSquare (N width-1) psi)))
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n)
  have hceiling := completeRemainder_le_squareCeiling (N width-1)
    (Q'.le_of_lt hw0) hw1 K hquad q psi
    (by simpa only [hN] using source_supported w K width n)
    (by simpa only [hN] using oddCentered_supported hw0 hw1 K width hK n hf)
  have hp : squareCeiling (N width-1) w K q psi ≈
      quadraticRate w*(Z*V)+centeredError hw0 hw1 K width hK n f :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (centered_sourceSquare_pin hw0 hw1 K width hK n hf hind)))
        (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.mul (.var 1)
          (.add (.mul (.var 2) (.var 3)) (.neg (.var 4))))) (.var 5)) (.var 6))
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.add (.add (.var 5) (.var 6)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 4)))))
        (by decide) (fun
          | 0 => alpha
          | 1 => squareQuarter
          | 2 => Z
          | 3 => V
          | 4 => C
          | 5 => E
          | _ => T))
  have hraw := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (signedRemainder_generic w K width n psi))
    (Q'.le_trans' _ _ _ hceiling (Q'.le_of_eqv hp))
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ r hraw
    (Q'.le_of_lt (Q'.recipPos_pos Z _))
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr' (partition_cancel _ Z V _) (Q'.eqv_refl _))))

/-- The original complete-weight Ward residual is SUBTRACTED, never assigned
a favorable sign. Every remaining same-object debt is visible. -/
def completeCenteredError {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  normalizedCenteredError hw0 hw1 K width hK n f -
    ((1 : Q')-w)*normalizedWardResidual hw0 hw1 K width hK n f

/-- A concrete SAME-variance upper bound with leading rate 12*h+h^2/8.
The complete centered error is NOT asserted small along a scaling family. -/
theorem padded_family_energy_centered_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (hquad : sufficientCutoff w ≤ K)
    (n : Nat) (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width coeff qs) ≤
      (12*((1 : Q')-w)+quadraticRate w) *
        oddVariance hw0 hw1 K width hK n (spatialSpan width coeff qs) +
      completeCenteredError hw0 hw1 K width hK n (spatialSpan width coeff qs) := by
  let f := spatialSpan width coeff qs
  let A := normalizedAngular hw0 hw1 K width hK n f
  let W := normalizedWardResidual hw0 hw1 K width hK n f
  let V := oddVariance hw0 hw1 K width hK n f
  let D := normalizedCenteredError hw0 hw1 K width hK n f
  let h := (1 : Q')-w
  let beta := quadraticRate w
  have hf := spatialSpan_supported width coeff qs
  have hind := spatialSpan_fringe_independent_after_padding hwidth coeff qs hqs
  have hward := family_normalized_ward hw0 hw1 K width hK n qs coeff
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hupper := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedEnergy_centered_taylor hw0 hw1 K width hK n hf hind))
    (Q'.add_le_add_left (h*A) _ _
      (normalizedRemainder_centered_square_bound hw0 hw1 K width hK hquad n hf hind))
  have hjoin : h*A+(beta*V+D) ≈ h*(A+W)+beta*V+(D-h*W) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 4) (.var 3)) (.var 5)))
      (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 4) (.var 3))) (.add (.var 5) (.neg (.mul (.var 0) (.var 2)))))
      (by decide) (fun | 0 => h | 1 => A | 2 => W | 3 => V | 4 => beta | _ => D)
  exact Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hjoin
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hward) (Q'.eqv_refl _))
      (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.mul (.const 12) (.var 1)))
          (.mul (.var 2) (.var 1))) (.var 3))
        (.add (.mul (.add (.mul (.const 12) (.var 0)) (.var 2)) (.var 1)) (.var 3))
        (by decide) (fun | 0 => h | 1 => V | 2 => beta | _ => D-h*W)))))

#print axioms blockSquare_shifted
#print axioms marginalAngular_shifted
#print axioms normalizedEnergy_centered_taylor
#print axioms centeredCorrection
#print axioms centered_sourceSquare_pin
#print axioms quadraticRate
#print axioms centeredError
#print axioms normalizedCenteredError
#print axioms normalizedRemainder_centered_square_bound
#print axioms completeCenteredError
#print axioms padded_family_energy_centered_square

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare
