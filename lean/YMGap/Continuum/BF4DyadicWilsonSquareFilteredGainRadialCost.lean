/-
# Original word-local gain cost with its trace-gap cancellation retained

The gap is the literal H[V*b^2*(4-f^2)] at the actual growing square,
original centered message b=T(g_n*(f-c)), and unchanged spatial action V.
Its nonnegativity is constructed from the original cap-four certificate.
The retained local covariance cost separates into a second-order scalar
coefficient and a first-order coefficient multiplying this exact gap.

No trace concentration, source-loss/OWN-variance comparison, favorable gain,
relative response budget, or changing-family continuum assertion is supplied.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainLocalCovariance
import YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry

namespace YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainRadialCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
  (centeredMessage commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair (centeredMeanPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry (paddedSquareSquareBound)
open YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainCovariance
  (centeredMessageSquare centeredMessageCharacterSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainLocalCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap gap)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted_supported)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter

/-- Actual trace gap; the same finite mean is retained inside b. -/
def centeredMessageTraceGap (w : Q') (K width n scale : Nat)
    (hwidth : side scale < width) (c : Q') : Q' :=
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let b := centeredMessage w K width n f c
  weightedMass w K width (polyMul (polyMul b b) (gap 4 f))

private theorem weighted_gap_pin (blocks : Nat) (V B F : RatPoly) :
    quaternionHaar blocks (polyMul V (polyMul B (gap 4 F))) ≈
      4*quaternionHaar blocks (polyMul V B) -
        quaternionHaar blocks (polyMul V (polyMul B (polyMul F F))) := by
  have ha : quaternionHaar blocks (polyMul V (polyMul B (gap 4 F))) ≈
      quaternionHaar blocks (polyMul (polyMul V B) (gap 4 F)) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_assoc V B (gap 4 F)).symm)
  have hc : quaternionHaar blocks (polyMul (polyMul V B) (cap 4)) ≈
      4*quaternionHaar blocks (polyMul V B) :=
    Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_smul_right blocks 4 (polyMul V B) polyOne)
      (Q'.mul_eqv_congr_left 4 _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
  have hn : quaternionHaar blocks (polyMul (polyMul V B) (polyNeg (polyMul F F))) ≈
      -quaternionHaar blocks (polyMul V (polyMul B (polyMul F F))) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl (polyMul V B)).mul (neg_smul _)))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_smul_right blocks (-1) (polyMul V B) (polyMul F F))
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
            (by decide) (fun _ => quaternionHaar blocks (polyMul (polyMul V B) (polyMul F F))))
          (Q'.neg_eqv_congr _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc V B (polyMul F F))))))
  exact Q'.eqv_trans _ _ _ ha
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right blocks (polyMul V B) (cap 4) (polyNeg (polyMul F F)))
      (Q'.add_eqv_congr' hc hn))

/-- Complete exact gap moment, not a substituted variance. -/
theorem centeredMessageTraceGap_pin (w : Q') (K width n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    centeredMessageTraceGap w K width n scale hwidth c ≈
      4*centeredMessageSquare w K width n f c -
        centeredMessageCharacterSquare w K width n f c := by
  exact weighted_gap_pin (N width) (spatialWeight w K width)
    (polyMul (centeredMessage w K width n
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) c)
      (centeredMessage w K width n
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) c))
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)

/-- The original cap-four certificate is multiplied by the actual V and b^2. -/
theorem centeredMessageTraceGap_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width) (c : Q') :
    (0 : Q') ≤ centeredMessageTraceGap w K width n scale hwidth c := by
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let b := centeredMessage w K width n f c
  have hb : SupportedQuaternionBlocks (N width) b := transferStep_supported w K width
    (supported_polyMul (terminalMessage_supported w K width n)
      (shifted_supported (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1) c))
  exact ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hhead).mul
    ((Certificate.square b hb).mul (paddedSquareSquareBound scale width hwidth).certificate)).haar_nonnegative

/-- Second order in the exact word-scale heat loss 1-x. -/
def radialSecondRate (x : Q') : Q' := (1-x)*(1-x)*(1+2*x+3*(x*x))

/-- First order in the exact word-scale heat loss 1-x. -/
def radialFirstRate (x : Q') : Q' := ((x*x)*x)*(1-x)

theorem radial_rates_nonnegative (x : Q') (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    (0 : Q') ≤ radialSecondRate x ∧ (0 : Q') ≤ radialFirstRate x := by
  have ht := Q'.sub_nonneg_of_le hx1
  have hxx := Q'.mul_nonneg x x hx0 hx0
  have hpoly : (0 : Q') ≤ 1+2*x+3*(x*x) :=
    Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (by decide) (Q'.mul_nonneg _ _ (by decide) hx0))
      (Q'.mul_nonneg _ _ (by decide) hxx)
  exact ⟨Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ht ht) hpoly,
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hxx hx0) ht⟩

/-- Explicit quadratic/linear coefficient ceilings, including x=0 and x=1. -/
theorem radial_rates_upper (x : Q') (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    radialSecondRate x ≤ 6*((1-x)*(1-x)) ∧ radialFirstRate x ≤ 1-x := by
  have ht := Q'.sub_nonneg_of_le hx1
  have hxx0 := Q'.mul_nonneg x x hx0 hx0
  have hxx1 : x*x ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ x hx1 hx0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv x)) hx1)
  have hxxx1 : (x*x)*x ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ x hxx1 hx0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv x)) hx1)
  have hp : 1+2*x+3*(x*x) ≤ (6 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add
      (Q'.add_le_add_left 1 _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 hx1 (by decide)))
      (Q'.mul_le_mul_of_nonneg_left _ _ 3 hxx1 (by decide)))
    (Q'.le_of_eqv (by decide : (1 : Q')+2*1+3*1 ≈ 6))
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ ((1-x)*(1-x)) hp (Q'.mul_nonneg _ _ ht ht))
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  · exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ (1-x) hxxx1 ht)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))

private theorem qpow_rg (w : Q') : ∀ k : Nat, qpow w k = RGTransport.qpow w k
  | 0 => rfl
  | k+1 => congrArg (fun z : Q' => z*w) (qpow_rg w k)

/-- The coefficient bounds hold on every actual strict nome and square scale. -/
theorem paddedSquare_radial_rates_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    let x := qpow w (8*side scale)
    ((0 : Q') ≤ radialSecondRate x ∧ (0 : Q') ≤ radialFirstRate x) ∧
      (radialSecondRate x ≤ 6*((1-x)*(1-x)) ∧ radialFirstRate x ≤ 1-x) := by
  dsimp only
  have hx0 : (0 : Q') ≤ qpow w (8*side scale) := by
    rw [qpow_rg]
    exact RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hx1 : qpow w (8*side scale) ≤ (1 : Q') := by
    rw [qpow_rg]
    exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _
  exact ⟨radial_rates_nonnegative _ hx0 hx1, radial_rates_upper _ hx0 hx1⟩

private theorem power_multiple (w : Q') (m : Nat) : ∀ k : Nat,
    qpow w (m*k) ≈ qpow (qpow w m) k
  | 0 => by simp only [Nat.mul_zero, qpow_zero]; exact Q'.eqv_refl _
  | k+1 => by
    rw [Nat.mul_succ]
    exact Q'.eqv_trans _ _ _ (qpow_add w (m*k) m)
      (Q'.mul_eqv_congr_right _ _ _ (power_multiple w m k))

private theorem rates_power_pin (w : Q') (scale : Nat) :
    let x := qpow w (8*side scale)
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    a*a ≈ (x*x)*x ∧ d ≈ ((x*x)*x)*x := by
  dsimp only
  have h3 := power_multiple w (8*side scale) 3
  have h4 := power_multiple w (8*side scale) 4
  have h33 := qpow_add w (12*side scale) (12*side scale)
  rw [show 8*side scale*3 = 12*side scale+12*side scale by omega] at h3
  rw [show 8*side scale*4 = 32*side scale by omega] at h4
  constructor
  · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm h33) (Q'.eqv_trans _ _ _ h3
      (by simpa only [qpow] using (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.const 1) (.var 0)) (.var 0)) (.var 0))
        (.mul (.mul (.var 0) (.var 0)) (.var 0)) (by decide)
        (fun _ => qpow w (8*side scale)))))
  · exact Q'.eqv_trans _ _ _ h4
      (by simpa only [qpow] using (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.mul (.const 1) (.var 0)) (.var 0)) (.var 0)) (.var 0))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 0)) (by decide)
        (fun _ => qpow w (8*side scale))))

private theorem retained_ring (x U F : Q') :
    (1-((x*x)*x)*x)*U-((x*x)*x-((x*x)*x)*x)*F ≈
      radialSecondRate x*U+radialFirstRate x*(4*U-F) :=
  poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1)
      (.neg (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 0)))) (.var 1))
      (.neg (.mul (.add (.mul (.mul (.var 0) (.var 0)) (.var 0))
        (.neg (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 0)))) (.var 2))))
    (.add
      (.mul (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
        (.add (.add (.const 1) (.mul (.const 2) (.var 0)))
          (.mul (.const 3) (.mul (.var 0) (.var 0))))) (.var 1))
      (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.add (.const 1) (.neg (.var 0))))
        (.add (.mul (.const 4) (.var 1)) (.neg (.var 2)))))
    (by decide) (fun | 0 => x | 1 => U | _ => F)

/-- Exact cancellation in the actual retained square cost, at any finite center. -/
theorem retained_cost_decomposition (w : Q') (K width n scale : Nat)
    (hwidth : side scale < width) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let d := qpow w (32*side scale)
    let x := qpow w (8*side scale)
    (1-d)*centeredMessageSquare w K width n f c -
        (a*a-d)*centeredMessageCharacterSquare w K width n f c ≈
      radialSecondRate x*centeredMessageSquare w K width n f c +
        radialFirstRate x*centeredMessageTraceGap w K width n scale hwidth c := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let U := centeredMessageSquare w K width n f c
  let F := centeredMessageCharacterSquare w K width n f c
  let x := qpow w (8*side scale)
  have hp := rates_power_pin w scale
  have hcoeff :
      (1-qpow w (32*side scale))*U -
          (qpow w (12*side scale)*qpow w (12*side scale)-qpow w (32*side scale))*F ≈
        (1-((x*x)*x)*x)*U-((x*x)*x-((x*x)*x)*x)*F := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl 1) (Q'.neg_eqv_congr _ _ hp.2)))
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.add_eqv_congr' hp.1 (Q'.neg_eqv_congr _ _ hp.2))))
  exact Q'.eqv_trans _ _ _ hcoeff (Q'.eqv_trans _ _ _ (retained_ring x U F)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (centeredMessageTraceGap_pin w K width n scale hwidth c)))))

attribute [local irreducible] ownMean originalLocalSourceHeatLoss centeredMessageTraceGap

/-- The checked OWN-centered local covariance now pays its exact radial cost.
All original source, mean residue, action and word-only sweep are unchanged. -/
theorem paddedSquare_own_commutatorGain_local_radial_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K) (n scale : Nat) (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let f := sourceCharacter width loop.edges 1
    let c := ownMean hw0 hw1 K width hhead n loop
    let a := qpow w (12*side scale)
    let x := qpow w (8*side scale)
    let residue := (a-1)*c*centeredMeanPair w K width n f c
    (commutatorGain w K width n f c a-residue)*(commutatorGain w K width n f c a-residue) ≤
      originalLocalSourceHeatLoss w K width n scale hwidth *
        (radialSecondRate x*centeredMessageSquare w K width n f c +
          radialFirstRate x*centeredMessageTraceGap w K width n scale hwidth c) := by
  dsimp only
  let loop := paddedSquare scale width hwidth
  let c := ownMean hw0 hw1 K width hhead n loop
  have h := paddedSquare_own_commutatorGain_local_retained_bound hw0 hw1 K width hhead htwo n scale hwidth
  have he := retained_cost_decomposition w K width n scale hwidth c
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (Q'.mul_eqv_congr_left (originalLocalSourceHeatLoss w K width n scale hwidth) _ _ he))

#print axioms centeredMessageTraceGap
#print axioms centeredMessageTraceGap_pin
#print axioms centeredMessageTraceGap_nonnegative
#print axioms radialSecondRate
#print axioms radialFirstRate
#print axioms radial_rates_nonnegative
#print axioms radial_rates_upper
#print axioms paddedSquare_radial_rates_bounds
#print axioms retained_cost_decomposition
#print axioms paddedSquare_own_commutatorGain_local_radial_bound

end YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainRadialCost
