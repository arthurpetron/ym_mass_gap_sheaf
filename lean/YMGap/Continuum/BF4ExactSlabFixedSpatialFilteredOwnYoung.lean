/-
# The full original filtered ceiling meets its OWN odd variance

Young's EXACT radial identity retains the radial centered square U, the
Young square Y and the actual drift square D. The center in every term is
the SAME computed odd-window mean. A certified cap16 compares the mixed
upper centered-square window (n,1,n+1) with the matched window (n,1,n),
paying the explicit original-transfer error 32*mixRate^n. The mixed even
partition is retained, never equated with an odd partition.

The resulting full signed-source ceiling may also pay its actual quartic
term using the constructed original cutoff/depth producer. The remaining
first chord moment and all favorable squares stay literal. This is not a
useful changing-family relative budget or a continuum survival theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredQuarticCeiling
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement
  (upperOriented upper_character_lift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
  (upper_supported upper_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement (wordChordal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
  (mean mean_square_le_four centered_edge_square_pin edgeMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredQuarticCeiling
open YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion (mixedQuarticDepthCutoff)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
  (lift_add lift_smul lift_product lift_one lift_supported)
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step_pairing)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (reindexQuaternionPolynomial_neg)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarWordDifference (word_supported word_unit difference difference_supported)
open YMGap.Continuum.QuaternionHaarRadialMeanYoung
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff (quarticCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.PositiveContractionResidual (geometric_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage spatialWeight kineticWeight oddMass

/-- Literal upper-word fundamental trace, on the original two-slice carrier. -/
def upperTrace (width : Nat) (loop : SourceLoop width) : RatPoly :=
  characterPolynomial (wordWith (upperOriented width) loop.edges).scalar 1

/-- The existing actual odd mean; no mixed-window mean replaces it. -/
def ownMean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) : Q' :=
  mean hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)

def mixedChordMoment (w : Q') (K width n : Nat) (loop : SourceLoop width) : Q' :=
  H (N width+N width) (polyMul (mixedDensity w K width n) (wordChordal width loop))

def mixedCenteredMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) : Q' :=
  let psi := displacement (ownMean hw0 hw1 K width hK n loop) (upperTrace width loop)
  H (N width+N width) (polyMul (mixedDensity w K width n) (polyMul psi psi))

def mixedRadialCenteredMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) : Q' :=
  let psi := displacement (ownMean hw0 hw1 K width hK n loop) (upperTrace width loop)
  H (N width+N width) (polyMul (mixedDensity w K width n)
    (polyMul (wordChordal width loop) (polyMul psi psi)))

def mixedYoungSquareMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) (t : Q') : Q' :=
  let y := youngSquareRoot (ownMean hw0 hw1 K width hK n loop) t
    (upperTrace width loop) (wordChordal width loop)
  H (N width+N width) (polyMul (mixedDensity w K width n) (polyMul y y))

private def upperBound (width : Nat) (loop : SourceLoop width) :
    SquareBound (N width+N width) (upperTrace width loop) 4 :=
  SquareBound.changeCap (by decide : characterBound 1 ≈ (4 : Q'))
    (character_squareBound (SquareBound.scalar
      (word_supported (upperOriented width) loop.edges
        (fun e he => upper_supported (loop.physical e he)))
      (word_unit (upperOriented width) loop.edges
        (fun e he => upper_unit (loop.physical e he)))) 1)

/-- A cap of sixteen on the CENTERED SQUARE, not cap16 on the trace. -/
def upperCenteredSquare_interval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    let psi := displacement (ownMean hw0 hw1 K width hK n loop) (upperTrace width loop)
    Interval (N width+N width) (polyMul psi psi) 16 := by
  let c := ownMean hw0 hw1 K width hK n loop
  have hc : c*c ≤ (4 : Q') := mean_square_le_four hw0 hw1 K width hK n loop
  have he : c*c+(4-c*c) ≈ (4 : Q') :=
    poly_identity_of_normal_eq (.add (.var 0) (.add (.const 4) (.neg (.var 0))))
      (.const 4) (by decide) (fun _ => c*c)
  let C : SquareBound (N width+N width) (cap c) 4 :=
    SquareBound.changeCap he ((SquareBound.constant _ c).raise (4-c*c)
      (Q'.sub_nonneg_of_le hc))
  let P : SquareBound (N width+N width) (displacement c (upperTrace width loop)) 16 :=
    SquareBound.changeCap (by decide : sumBound (4 : Q') 4 ≈ 16)
      (C.add (upperBound width loop).neg)
  exact ⟨supported_polyMul P.support P.support, by decide, P.certificate,
    (Certificate.constant _ 16 (by decide)).add (Certificate.square _ P.support)⟩

private theorem padded_neg {n : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv n p q) :
    PaddedPolynomialCoeffEqv n (polyNeg p) (polyNeg q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

private theorem upper_displacement (width : Nat) (loop : SourceLoop width) (c : Q') :
    PaddedPolynomialCoeffEqv (N width+N width)
      (liftBoundary (N width) (displacement c (sourceCharacter width loop.edges 1)))
      (displacement c (upperTrace width loop)) := by
  simp only [displacement, cap, lift_add, lift_smul, lift_neg, upperTrace]
  exact ((lift_one (N width+N width) (N width)).smul c).add
    (padded_neg (upper_character_lift width loop))

private theorem matched_upper_lower (w : Q') (K width n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    H (N width+N width) (polyMul (edgeDensity w K width (terminalMessage w K width n))
      (liftBoundary (N width) p)) ≈
      H (N width+N width) (polyMul (edgeDensity w K width (terminalMessage w K width n)) p) := by
  let g := terminalMessage w K width n
  have hpoly : RatPolyCoeffEqv
      (polyMul (edgeDensity w K width g) (liftBoundary (N width) p))
      (polyMul (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) g))
        (liftBoundary (N width) (polyMul (spatialWeight w K width) (polyMul g p)))) := by
    simp only [edgeDensity, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (by decide) (fun
        | 0 => polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) g)
        | 1 => liftBoundary (N width) (spatialWeight w K width)
        | 2 => liftBoundary (N width) g
        | _ => liftBoundary (N width) p)
  have hupper : H (N width+N width) (polyMul (edgeDensity w K width g)
      (liftBoundary (N width) p)) ≈ weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
      (Q'.eqv_trans _ _ _ (step_pairing (N width) (N width) _ _ _ _)
        (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
          (.mul (.var 1) (.mul (.mul (.var 2) (.var 0)) (.var 3)))
          (by decide) (fun
            | 0 => transferStep w K width g | 1 => spatialWeight w K width
            | 2 => g | _ => p))))
  exact Q'.eqv_trans _ _ _ hupper
    (Q'.eqv_symm (edge_marginal_pairing w K width (terminalMessage_supported w K width n) hp))

private theorem matched_centered_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    let c := ownMean hw0 hw1 K width hK n loop
    let psi := displacement c (upperTrace width loop)
    windowRatio hw0 hw1 K width hK n 1 n (polyMul psi psi) ≈
      oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1) := by
  let c := ownMean hw0 hw1 K width hK n loop
  let psi := displacement c (upperTrace width loop)
  let phi := displacement c (sourceCharacter width loop.edges 1)
  have hphi := displacement_supported (sourceCharacter_supported width loop.edges 1) c
  have hpsi := displacement_supported (upperBound width loop).support c
  have hh := upper_displacement width loop c
  have hlift : SupportedQuaternionBlocks (N width+N width)
      (polyMul (liftBoundary (N width) phi) (liftBoundary (N width) phi)) :=
    supported_polyMul (lift_supported hphi (N width)) (lift_supported hphi (N width))
  have hp := (hh.mul hh).haar_insert hlift (supported_polyMul hpsi hpsi)
    (edgeDensity w K width (terminalMessage w K width n))
    (edgeDensity_supported w K width (terminalMessage_supported w K width n))
  have hraw : H (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width n)) (polyMul psi psi)) ≈
      H (N width+N width)
        (polyMul (edgeDensity w K width (terminalMessage w K width n)) (polyMul phi phi)) := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hp)
      (by rw [← lift_product]; exact matched_upper_lower w K width n (supported_polyMul hphi hphi))
  have hpair := terminalEdge_probe_pairing w K width n n (supported_polyMul hpsi hpsi)
  have hwindow : windowRatio hw0 hw1 K width hK n 1 n (polyMul psi psi) ≈
      H (N width+N width) (polyMul (edgeDensity w K width (terminalMessage w K width n))
        (polyMul psi psi)) * Q'.recipPos (oddMass w K width n)
          (oddMass_positive hw0 hw1 K width hK n) := by
    unfold windowRatio massRatio oddMass
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hpair)
  exact Q'.eqv_trans _ _ _ hwindow (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hraw)
    (centered_edge_square_pin hw0 hw1 K width hK n (sourceCharacter_supported width loop.edges 1)))

private theorem clear_bound (M Z b : Q') (hz : (0 : Q') < Z)
    (h : M*Q'.recipPos Z hz ≤ b) : M ≤ b*Z := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _ Z h (Q'.le_of_lt hz)
  have he : (M*Q'.recipPos Z hz)*Z ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hz)))
        (Q'.mul_one_eqv M))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hb

/-- Finite OWN join: one fixed odd center across both actual windows. -/
theorem mixedCenteredMoment_le_ownVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    mixedCenteredMoment hw0 hw1 K width hK n loop ≤
      (oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1) +
        mixRate hw0 hw1 width^n*32)*evenPartition w K width n := by
  let c := ownMean hw0 hw1 K width hK n loop
  let psi := displacement c (upperTrace width loop)
  let p := polyMul psi psi
  let I := upperCenteredSquare_interval hw0 hw1 K width hK n loop
  have hb := (windowRatio_right_commonTail hw0 hw1 K width hK n 1 n (n+1) n
    (by simpa only [Nat.one_add, Nat.two_mul] using I) (by omega) (Nat.le_refl n)).1
  have hmatched := matched_centered_pin hw0 hw1 K width hK n loop
  have hc : windowRatio hw0 hw1 K width hK n 1 (n+1) p ≤
      oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)+
        mixRate hw0 hw1 width^n*32 :=
    Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.add_eqv_congr' hmatched
      (Q'.mul_eqv_congr_left _ _ _ (by decide : (16 : Q')+16 ≈ 32))))
  let Z := weightedMass w K width (polyMul (terminalMessage w K width (n+1))
    (terminalMessage w K width (n+1)))
  let M := weightedMass w K width
    (polyMul (observedMessage w K width n 1 p) (terminalMessage w K width (n+1)))
  let hz := terminalPair_positive hw0 hw1 K width hK (n+1) (n+1)
  have hh : M*Q'.recipPos Z hz ≤
      oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)+
        mixRate hw0 hw1 width^n*32 := by
    simpa only [windowRatio, massRatio] using hc
  have hZ : Z ≈ evenPartition w K width n := by
    have h := evenPartition_middle_pin w K width n
    rw [terminalMessage_next w K width n] at h
    exact Q'.eqv_symm h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (mixedDensity_window_pairing w K width n I.support))
    (Q'.le_trans' _ _ _ (clear_bound M Z _ hz hh)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hZ)))

/-- Exact retained identity; positivity and the temporal comparison play no role. -/
theorem mixed_own_young_identity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) (t : Q') :
    (t*(mixedRadialMoment w K width n loop+mixedQuarticMoment w K width n loop)+
      t*mixedRadialCenteredMoment hw0 hw1 K width hK n loop)+
      mixedYoungSquareMoment hw0 hw1 K width hK n loop t ≈
    (t*t)*mixedCenteredMoment hw0 hw1 K width hK n loop+
      (t+ownMean hw0 hw1 K width hK n loop*ownMean hw0 hw1 K width hK n loop)*
        mixedQuarticMoment w K width n loop+
      (t*(4-ownMean hw0 hw1 K width hK n loop*ownMean hw0 hw1 K width hK n loop))*
        mixedChordMoment w K width n loop :=
  weighted_young_moments_identity (N width+N width) (mixedDensity w K width n)
    (upperTrace width loop) (wordChordal width loop) (ownMean hw0 hw1 K width hK n loop) t

private theorem collect_filtered (s r q d u y v l c t : Q')
    (ht : (0 : Q') ≤ t) (hs : s ≤ (2*r+2*q)+ -(2*d))
    (hy : (t*(r+q)+t*u)+y ≈ (t*t)*v+(t+c*c)*q+(t*(4-c*c))*l) :
    ((t*s+2*(t*u))+2*y)+2*(t*d) ≤
      2*((t*t)*v)+2*((t+c*c)*q)+2*((t*(4-c*c))*l) := by
  have hb := Q'.mul_le_mul_of_nonneg_left _ _ t hs ht
  have ha := Q'.add_le_add_right _ _ (2*(t*u)+2*y+2*(t*d)) hb
  have hl : ((t*s+2*(t*u))+2*y)+2*(t*d) ≈
      t*s+(2*(t*u)+2*y+2*(t*d)) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 0) (.var 1)) (.mul (.const 2) (.mul (.var 0) (.var 2))))
        (.mul (.const 2) (.var 3))) (.mul (.const 2) (.mul (.var 0) (.var 4))))
      (.add (.mul (.var 0) (.var 1)) (.add (.add (.mul (.const 2) (.mul (.var 0) (.var 2)))
        (.mul (.const 2) (.var 3))) (.mul (.const 2) (.mul (.var 0) (.var 4)))))
      (by decide) (fun | 0 => t | 1 => s | 2 => u | 3 => y | _ => d)
  have hr : t*((2*r+2*q)+ -(2*d))+(2*(t*u)+2*y+2*(t*d)) ≈
      2*((t*(r+q)+t*u)+y) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.add (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 2)))
        (.neg (.mul (.const 2) (.var 3)))))
        (.add (.add (.mul (.const 2) (.mul (.var 0) (.var 4))) (.mul (.const 2) (.var 5)))
          (.mul (.const 2) (.mul (.var 0) (.var 3)))))
      (.mul (.const 2) (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 0) (.var 4))) (.var 5)))
      (by decide) (fun | 0 => t | 1 => r | 2 => q | 3 => d | 4 => u | _ => y)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl) (Q'.le_trans' _ _ _ ha
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hy)
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv _ _ _)))))))

/-- Complete literal source, SAME finite OWN variance and three retained gains. -/
theorem filtered_loop_own_young_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width)
    (t : Q') (ht : (0 : Q') ≤ t) :
    ((t*numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1)))+
      2*(t*mixedRadialCenteredMoment hw0 hw1 K width hK n loop))+
      2*mixedYoungSquareMoment hw0 hw1 K width hK n loop t)+
      2*(t*driftSquare w K width n (sourceCharacter width loop.edges 1)) ≤
    2*((t*t)*((oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)+
      mixRate hw0 hw1 width^n*32)*evenPartition w K width n))+
    2*((t+ownMean hw0 hw1 K width hK n loop*ownMean hw0 hw1 K width hK n loop)*
      mixedQuarticMoment w K width n loop)+
    2*((t*(4-ownMean hw0 hw1 K width hK n loop*ownMean hw0 hw1 K width hK n loop))*
      mixedChordMoment w K width n loop) := by
  have h := collect_filtered _ _ _ _ _ _ _ _ _ t ht
    (filtered_loop_radial_drift_bound hw0 hw1 K width hK n loop)
    (mixed_own_young_identity hw0 hw1 K width hK n loop t)
  have hv := Q'.mul_le_mul_of_nonneg_left _ _ (t*t)
    (mixedCenteredMoment_le_ownVariance hw0 hw1 K width hK n loop)
    (SumOfSquares.q_mul_self_nonneg t)
  exact Q'.le_trans' _ _ _ h (Q'.add_le_add_right _ _ _
    (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 hv (by decide))))

/-- The SAME computed depth onset also pays the finite variance-alignment
error. The quartic term is paid by its actual whole-word producer. -/
theorem filtered_loop_own_young_paid {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide) ≤ w) (he : (0 : Q') < epsilon)
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width)
    (hcut : quarticCutoff w epsilon ≤ K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon ≤ n)
    (t : Q') (ht : (0 : Q') ≤ t) :
    ((t*numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1)))+
      2*(t*mixedRadialCenteredMoment hw0 hw1 K width hK n loop))+
      2*mixedYoungSquareMoment hw0 hw1 K width hK n loop t)+
      2*(t*driftSquare w K width n (sourceCharacter width loop.edges 1)) ≤
    2*(evenPartition w K width n *
      ((t*t)*(oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)+epsilon)+
        (t+ownMean hw0 hw1 K width hK n loop*ownMean hw0 hw1 K width hK n loop)*
          mixedWordQuarticRate w epsilon loop)+
      (t*(4-ownMean hw0 hw1 K width hK n loop*ownMean hw0 hw1 K width hK n loop))*
        mixedChordMoment w K width n loop) := by
  let c := ownMean hw0 hw1 K width hK n loop
  let v := oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)
  let z := evenPartition w K width n
  let b := mixedWordQuarticRate w epsilon loop
  let l := mixedChordMoment w K width n loop
  have hsmall := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (by decide : (0 : Q') ≤ 32) he n hn
  have hv : (t*t)*((v+mixRate hw0 hw1 width^n*32)*z) ≤ (t*t)*((v+epsilon)*z) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (t*t)
    (Q'.mul_le_mul_of_nonneg_right _ _ z (Q'.add_le_add_left v _ _ hsmall)
      (Q'.le_of_lt (evenPartition_positive hw0 hw1 K width hK n)))
    (SumOfSquares.q_mul_self_nonneg t)
  have hq := Q'.mul_le_mul_of_nonneg_left _ _ (t+c*c)
    (mixed_word_quartic_tolerance_bound hw0 hw1 hw he K width hK n loop hactive hcut hn)
    (Q'.zero_le_add _ _ ht (SumOfSquares.q_mul_self_nonneg c))
  have hb := Q'.add_le_add_right _ _ (2*((t*(4-c*c))*l))
    (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ 2 hv (by decide))
      (Q'.mul_le_mul_of_nonneg_left _ _ 2 hq (by decide)))
  have hc : 2*((t*t)*((v+epsilon)*z))+2*((t+c*c)*(b*z))+2*((t*(4-c*c))*l) ≈
      2*(z*((t*t)*(v+epsilon)+(t+c*c)*b)+(t*(4-c*c))*l) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 2) (.mul (.mul (.var 0) (.var 0))
        (.mul (.add (.var 1) (.var 2)) (.var 3))))
        (.mul (.const 2) (.mul (.add (.var 0) (.mul (.var 4) (.var 4)))
          (.mul (.var 5) (.var 3)))))
        (.mul (.const 2) (.mul (.mul (.var 0) (.add (.const 4)
          (.neg (.mul (.var 4) (.var 4))))) (.var 6))))
      (.mul (.const 2) (.add (.mul (.var 3)
        (.add (.mul (.mul (.var 0) (.var 0)) (.add (.var 1) (.var 2)))
          (.mul (.add (.var 0) (.mul (.var 4) (.var 4))) (.var 5))))
        (.mul (.mul (.var 0) (.add (.const 4) (.neg (.mul (.var 4) (.var 4))))) (.var 6))))
      (by decide) (fun | 0 => t | 1 => v | 2 => epsilon | 3 => z | 4 => c | 5 => b | _ => l)
  exact Q'.le_trans' _ _ _ (filtered_loop_own_young_bound hw0 hw1 K width hK n loop t ht)
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hc))

#print axioms upperTrace
#print axioms ownMean
#print axioms mixedChordMoment
#print axioms mixedCenteredMoment
#print axioms mixedRadialCenteredMoment
#print axioms mixedYoungSquareMoment
#print axioms upperCenteredSquare_interval
#print axioms mixedCenteredMoment_le_ownVariance
#print axioms mixed_own_young_identity
#print axioms filtered_loop_own_young_bound
#print axioms filtered_loop_own_young_paid

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung
