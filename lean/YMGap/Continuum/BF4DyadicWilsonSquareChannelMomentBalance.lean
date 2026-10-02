/-
# Exact signed channel moments in the original centered Wilson energy

The literal full-Casimir curvature and square are evaluated against EVERY
actual passive channel. Their combination is P^2*(5*F2-8*M), with the SAME
channel mass and raw uncentered fundamental square moment. OWN centering is
retained in the cubic budget and angular defect. No favorable sign, channel
factorization, global gain identity or changing-family bound is assumed.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareCasimirCurvature
import YMGap.Continuum.BF4DyadicWilsonSquareActiveChannelSobolev
import YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelMomentBalance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy)
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss (familyChannelQuadratic)
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add)
open YMGap.Continuum.SU2QuaternionPassiveChannelRetainedCasimirSobolev
  (channelCurvature channelCasimirSquare
    sourceEnergy_le_exactChannelAngular_activeSobolev_retainedCasimir)
open YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir (oneThird)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted normalizedMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource energy_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance normalizedWardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered_supported oddCentered_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (angularWeightDefect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (energy_shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar (weighted_gamma_finSum)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareWardMoments (paddedSquare_gamma)
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels (squareChannelSource)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
open YMGap.Continuum.BF4DyadicWilsonSquareCasimirCurvature
open YMGap.Continuum.BF4DyadicWilsonSquareActiveChannelSobolev

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

private theorem haar_neg_right (n : Nat) (a p : RatPoly) :
    H n (polyMul a (polyNeg p)) ≈ -(H n (polyMul a p)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((neg_smul p).mul_left a))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (-1) a p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n (polyMul a p))))

private theorem sum_difference (cs : List GramChannel) (a : Q')
    (M F : RatPoly → Q') :
    channelSum cs (fun z => a*(M z-F z)) ≈
      a*(channelSum cs M-channelSum cs F) := by
  have hn : channelSum cs (fun z => -F z) ≈ -(channelSum cs F) :=
    Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => (-1)*F z) cs (fun z _ =>
      poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
        (by decide) (fun _ => F z.2)))
      (Q'.eqv_trans _ _ _ (channelSum_smul F (-1) cs)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => channelSum cs F)))
  exact Q'.eqv_trans _ _ _ (channelSum_smul _ a cs)
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _ (channelSum_add M (fun z => -F z) cs)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hn)))

/-- Full centered curvature evaluated against the SAME actual channel mass
and uncentered fundamental square moment. No sign or support premise is needed. -/
theorem paddedSquare_channelCurvature_moments (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    channelCurvature (N width-1) w K (spectatorBlocks scale width hwidth)
      (projectedEndpointSource w K width g) (shifted f c) ≈
      (8*(perimeter scale*perimeter scale)) *
        (squareChannelMass w K scale width hwidth g-
          squareChannelMoment w K scale width hwidth g) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth g
  let M := fun z => H (N width) (polyMul (b z) (b z))
  let F := fun z => H (N width) (polyMul (polyMul (b z) (b z)) (polyMul f f))
  let a := 8*(perimeter scale*perimeter scale)
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hpoint (z : RatPoly) : H (N width) (polyMul (polyMul (b z) (b z))
      (activeCasimirPolynomial (List.range (N width))
        (activeGamma (List.range (N width)) (shifted f c) (shifted f c)))) ≈
      a*(M z-F z) := by
    have hc := paddedSquare_shifted_gamma_casimir scale width hwidth c
      (polyMul (b z) (b z))
    exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_smul_right (N width) a (polyMul (b z) (b z)) _)
      (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_add_right (N width) _ polyOne (polyNeg (polyMul f f)))
        (Q'.add_eqv_congr' (haar_of_coeff (RatPolyCoeffEqv.mul_one _))
          (haar_neg_right (N width) _ _)))))
  unfold channelCurvature
  rw [hN]
  exact Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => a*(M z-F z)) cs (fun z _ => by
    simpa only [f, b, squareChannelSource] using hpoint z.2))
    (sum_difference cs a M F)

/-- The centered literal Casimir square is a raw UNcentered loop square moment,
not lambda squared times the centered square or OWN variance. -/
theorem paddedSquare_channelCasimirSquare_moments (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    channelCasimirSquare (N width-1) w K (spectatorBlocks scale width hwidth)
      (projectedEndpointSource w K width g) (shifted f c) ≈
      (9*(perimeter scale*perimeter scale))*
        squareChannelMoment w K scale width hwidth g := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth g
  let Cf := activeCasimirPolynomial (List.range (N width)) (shifted f c)
  let l := 3*perimeter scale
  let a := 9*(perimeter scale*perimeter scale)
  let F := fun z => H (N width) (polyMul (polyMul (b z) (b z)) (polyMul f f))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hC := paddedSquare_shifted_casimir scale width hwidth c
  have hpoint (z : RatPoly) : H (N width) (polyMul (polyMul (b z) Cf)
      (polyMul (b z) Cf)) ≈ a*F z := by
    have he : RatPolyCoeffEqv (polyMul (polyMul (b z) Cf) (polyMul (b z) Cf))
        (polyMul (polyMul (b z) (b z)) (polyMul Cf Cf)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => b z | _ => Cf)
    have hs : RatPolyCoeffEqv (polyMul (polySmul l f) (polySmul l f))
        (polySmul a (polyMul f f)) :=
      (RatPolyCoeffEqv.polyMul_smul_left l f (polySmul l f)).trans
        (((RatPolyCoeffEqv.polyMul_smul_right l f f).smul l).trans
          ((RatPolyCoeffEqv.smul_assoc l l _).trans
            (RatPolyCoeffEqv.smul_coefficient
              (poly_identity_of_normal_eq
                (.mul (.mul (.const 3) (.var 0)) (.mul (.const 3) (.var 0)))
                (.mul (.const 9) (.mul (.var 0) (.var 0))) (by decide)
                (fun _ => perimeter scale)) _)))
    exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (Q'.eqv_trans _ _ _ ((HaarCarrierEqv.mul hC hC) (polyMul (b z) (b z)))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (hs.mul_left _))
          (quaternionHaar_polyMul_smul_right (N width) a _ _)))
  unfold channelCasimirSquare
  rw [hN]
  exact Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => a*F z) cs (fun z _ => by
    simpa only [f, b, Cf, squareChannelSource] using hpoint z.2))
    (channelSum_smul F a cs)

/-- The signed quadratic contribution with all differentiated insertions removed.
The mass and square moment still belong to the SAME actual passive channels. -/
def signedChannelMomentBalance (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) : Q' :=
  (perimeter scale*perimeter scale) *
    (5*squareChannelMoment w K scale width hwidth g-
      8*squareChannelMass w K scale width hwidth g)

theorem paddedSquare_channel_secondOrder_balance (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1;
    -channelCurvature (N width-1) w K (spectatorBlocks scale width hwidth)
      (projectedEndpointSource w K width g) (shifted f c)-
      oneThird*channelCasimirSquare (N width-1) w K (spectatorBlocks scale width hwidth)
        (projectedEndpointSource w K width g) (shifted f c) ≈
      signedChannelMomentBalance w K scale width hwidth g := by
  dsimp only
  let P := perimeter scale
  let F := squareChannelMoment w K scale width hwidth g
  let M := squareChannelMass w K scale width hwidth g
  have he := Q'.add_eqv_congr'
    (Q'.neg_eqv_congr _ _ (paddedSquare_channelCurvature_moments w K scale width hwidth g c))
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left oneThird _ _
      (paddedSquare_channelCasimirSquare_moments w K scale width hwidth g c)))
  have hthird : oneThird*(9*(P*P)*F) ≈ 3*(P*P)*F :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 9) (.mul (.var 1) (.var 1))) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.const 9)) (.mul (.var 1) (.var 1))) (.var 2))
      (by decide) (fun | 0 => oneThird | 1 => P | _ => F))
      (Q'.mul_eqv_congr_right _ _ F (Q'.mul_eqv_congr_right _ _ (P*P)
        (by decide : oneThird*(9 : Q') ≈ (3 : Q'))))
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hthird))
    (poly_identity_of_normal_eq
      (.add (.neg (.mul (.mul (.const 8) (.mul (.var 0) (.var 0)))
        (.add (.var 2) (.neg (.var 1)))))
        (.neg (.mul (.mul (.const 3) (.mul (.var 0) (.var 0))) (.var 1))))
      (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.const 5) (.var 1)) (.neg (.mul (.const 8) (.var 2)))))
      (by decide) (fun | 0 => P | 1 => F | _ => M)))

/-- The existing cap four gives an upper mass ceiling, NOT a favorable sign. -/
theorem signedChannelMomentBalance_le_twelve_mass {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K scale width : Nat) (hwidth : side scale < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    signedChannelMomentBalance w K scale width hwidth g ≤
      (12*(perimeter scale*perimeter scale))*squareChannelMass w K scale width hwidth g := by
  let P := perimeter scale
  let M := squareChannelMass w K scale width hwidth g
  let F := squareChannelMoment w K scale width hwidth g
  have hF := squareChannelMoment_le_four_mass hw0 K scale width hwidth g hg
  have h5 := Q'.add_le_add_right _ _ (-(8*M))
    (Q'.mul_le_mul_of_nonneg_left _ _ 5 hF (by decide))
  have hcoef := Q'.mul_le_mul_of_nonneg_left _ _ (P*P) h5 (SumOfSquares.q_mul_self_nonneg P)
  exact Q'.le_trans' _ _ _ hcoef (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.const 5) (.mul (.const 4) (.var 1)))
          (.neg (.mul (.const 8) (.var 1)))))
      (.mul (.mul (.const 12) (.mul (.var 0) (.var 0))) (.var 1))
      (by decide) (fun | 0 => P | _ => M)))

/-- Exact angular channel sum; no Bessel enlargement to the raw source is paid. -/
theorem paddedSquare_channelAngular_moments (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly) (c : Q') :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
      (fun z => weightedAngularEnergy (N width-1)
        (squareChannelSource w K scale width hwidth g z) (shifted f c)) ≈
      perimeter scale*(4*squareChannelMass w K scale width hwidth g-
        squareChannelMoment w K scale width hwidth g) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth g
  let M := fun z => H (N width) (polyMul (b z) (b z))
  let F := fun z => H (N width) (polyMul (polyMul (b z) (b z)) (polyMul f f))
  let P := perimeter scale
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hpoint (z : RatPoly) : weightedAngularEnergy (N width-1) (b z) (shifted f c) ≈
      P*(4*M z-F z) := by
    have hgamma := (paddedSquare_shifted_gamma scale width hwidth c).trans
      (paddedSquare_gamma scale width hwidth)
    unfold weightedAngularEnergy
    rw [hN]
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (weighted_gamma_finSum (N width) (polyMul (b z) (b z)) (shifted f c)))
      (Q'.eqv_trans _ _ _ (hgamma (polyMul (b z) (b z)))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (N width) P _ _)
          (Q'.mul_eqv_congr_left P _ _ (Q'.eqv_trans _ _ _
            (quaternionHaar_polyMul_add_right (N width) _ _ _)
            (Q'.add_eqv_congr'
              (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (N width) 4 _ polyOne)
                (Q'.mul_eqv_congr_left 4 _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _))))
              (haar_neg_right (N width) _ _))))))
  exact Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => P*(4*M z-F z)) cs
    (fun z _ => hpoint z.2))
    (Q'.eqv_trans _ _ _ (sum_difference cs P (fun z => 4*M z) F)
      (Q'.mul_eqv_congr_left P _ _ (Q'.add_eqv_congr'
        (channelSum_smul M 4 cs) (Q'.eqv_refl _))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "psi" => oddCentered hw0 hw1 K width hK n f
local notation "g" => terminalMessage w K width n
local notation "Z" => oddMass w K width n
local notation "V" => oddVariance hw0 hw1 K width hK n f

/-- Exact original centered debt, with the raw signed moment combination
substituted for curvature and Casimir square. All other signed costs remain. -/
theorem activeChannelCenteredDebt_moments :
    activeChannelCenteredDebt hw0 hw1 K width hK n scale hwidth ≈
      let h := (1 : Q')-w
      let t := HalfPow.half*(h*h)
      activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth-
        (h+t)*angularWeightDefect w K width n psi+
        t*signedChannelMomentBalance w K scale width hwidth g := by
  dsimp only
  unfold activeChannelCenteredDebt activeChannelCurvature activeChannelCasimirSquare
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left _ _ _ (paddedSquare_channel_secondOrder_balance
      w K scale width hwidth g _))

/-- Actual original energy ceiling with the combined second-order correction
written as SAME-channel moments. This does not identify them with OWN variance. -/
theorem paddedSquare_energy_channel_moment_bound :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    normalizedEnergy hw0 hw1 K width hK n f ≤
      (h+t)*((12*Q'.ofNat (side scale))*V)-
        (h+t)*normalizedWardResidual hw0 hw1 K width hK n f+
        (activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth-
          (h+t)*angularWeightDefect w K width n psi+
          t*signedChannelMomentBalance w K scale width hwidth g)*
          Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n) := by
  dsimp only
  have he := paddedSquare_energy_activeChannel_sobolev_bound hw0 hw1 K width hK n scale hwidth
  exact Q'.le_trans' _ _ _ he (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _ _ (activeChannelCenteredDebt_moments
      hw0 hw1 K width hK n scale hwidth))))

/-- Original energy with exact angular and quadratic channel moments. The
observable keeps its OWN mean in the active cubic error. No angular Bessel
loss, factorization, favorable sign or OWN-variance comparison is supplied. -/
theorem paddedSquare_energy_exact_channel_moment_bound :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    normalizedEnergy hw0 hw1 K width hK n f ≤
      ((h+t)*perimeter scale*
          (4*squareChannelMass w K scale width hwidth g-
            squareChannelMoment w K scale width hwidth g)+
        t*signedChannelMomentBalance w K scale width hwidth g+
        activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth)*
        Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n) := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let q := projectedEndpointSource w K width g
  let mean := normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hK n)
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hp := oddCentered_supported hw0 hw1 K width hK n hf
  have hfringe := fun i hi => oddCentered_independent hw0 hw1 K width hK n i
    (paddedSquare_fringe_independent scale width hwidth i hi)
  have hpass := fun i hi => oddCentered_independent hw0 hw1 K width hK n i
    (sourceCharacter_spectator_independent scale width hwidth i hi)
  have hsource := energy_projected_source w K width g psi
    (terminalMessage_supported w K width n) hp hfringe
  have hcenter := energy_shifted w K width (terminalMessage_supported w K width n) hf mean
  have hbound := sourceEnergy_le_exactChannelAngular_activeSobolev_retainedCasimir (N width-1)
    (Q'.le_of_lt hw0) hw1 K (spectatorBlocks scale width hwidth)
    (observableBlocks scale width hwidth) (spectatorBlocks_nodup scale width hwidth)
    (by simpa only [hN] using spectatorBlocks_lt scale width hwidth)
    (by simpa only [hN] using observableBlocks_lt scale width hwidth)
    (spectator_not_observable scale width hwidth)
    (by simpa only [hN] using spectator_observable_cover scale width hwidth)
    q psi (by simpa only [hN] using source_supported w K width n)
    (by simpa only [hN] using hp) hpass
  have hangular := paddedSquare_channelAngular_moments w K scale width hwidth g mean
  have hquadratic := paddedSquare_channel_secondOrder_balance w K scale width hwidth g mean
  have hrewrite :
      let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
      (h+t)*channelSum cs (fun z => weightedAngularEnergy (N width-1)
          (channelSource (spectatorBlocks scale width hwidth) q z) psi)+
        (t*(-channelCurvature (N width-1) w K (spectatorBlocks scale width hwidth) q psi-
          oneThird*channelCasimirSquare (N width-1) w K (spectatorBlocks scale width hwidth) q psi)+
          activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth) ≈
      (h+t)*perimeter scale*(4*squareChannelMass w K scale width hwidth g-
          squareChannelMoment w K scale width hwidth g)+
        t*signedChannelMomentBalance w K scale width hwidth g+
        activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth := by
    dsimp only
    have hang := Q'.mul_eqv_congr_left (h+t) _ _ hangular
    have hquad := Q'.mul_eqv_congr_left t _ _ hquadratic
    have hjoin := Q'.add_eqv_congr' hang (Q'.add_eqv_congr' hquad (Q'.eqv_refl
      (activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth)))
    have hgroup := Q'.eqv_trans _ _ _ hjoin
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.eqv_refl _))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))
    simpa only [hN, q, oddCentered, mean, squareChannelSource] using hgroup
  have hraw := Q'.le_trans' _ _ _ (Q'.le_of_eqv hcenter.symm)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource)
      (Q'.le_trans' _ _ _ (by simpa only [hN] using hbound) (Q'.le_of_eqv hrewrite)))
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hraw
    (Q'.le_of_lt (Q'.recipPos_pos Z (oddMass_positive hw0 hw1 K width hK n)))

#print axioms paddedSquare_channelCurvature_moments
#print axioms paddedSquare_channelCasimirSquare_moments
#print axioms signedChannelMomentBalance
#print axioms paddedSquare_channel_secondOrder_balance
#print axioms signedChannelMomentBalance_le_twelve_mass
#print axioms paddedSquare_channelAngular_moments
#print axioms activeChannelCenteredDebt_moments
#print axioms paddedSquare_energy_channel_moment_bound
#print axioms paddedSquare_energy_exact_channel_moment_bound

end YMGap.Continuum.BF4DyadicWilsonSquareChannelMomentBalance
