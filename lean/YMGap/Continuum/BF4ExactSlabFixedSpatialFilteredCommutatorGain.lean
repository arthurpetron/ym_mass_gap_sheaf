/-
# Original filtered source, centered transfer commutator and endpoint mismatch

All terminal messages and spatial weights are retained. For g=g_n, A=Tg,
psi=f-c and b=T(g psi), the literal radius-two source is
  Delta + 2(1-a) ell(A psi b) - 2 ell(b(b-a A psi)).
The identity holds for every rational a: it does NOT assert a centered
eigenpin. At the SAME finite odd mean, the original endpoint mismatch has
absolute value at most 32 mixRate^n times the EVEN window partition.
The matched centered transfer comparison below uses the SAME moving center.
Neither the sign of the commutator gain, a reserve, nor a useful relative
changing-family budget is established here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferCovariance
import YMGap.Continuum.SU2QuaternionReplicaPairBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (mean_pin mean_square_le_four)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMoment_pin marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step_pairing partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (lift_cap_carrier)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarWordDifference
  (word_supported word_unit weighted_difference weighted_scale)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported normalizedMoment)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage spatialWeight kineticWeight oddMass

/-- Literal centered original terminal insertion, before any normalization. -/
def centeredMessage (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') : RatPoly :=
  transferStep w K width (polyMul (terminalMessage w K width n) (shifted f c))

def centeredTransferCross (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') : Q' :=
  weightedMass w K width (polyMul
    (polyMul (transferStep w K width (terminalMessage w K width n)) (shifted f c))
    (centeredMessage w K width n f c))

/-- Signed gain; no positivity of this quadratic is asserted. -/
def commutatorGain (w : Q') (K width n : Nat) (f : RatPoly) (c a : Q') : Q' :=
  let b := centeredMessage w K width n f c
  let u := polyMul (transferStep w K width (terminalMessage w K width n)) (shifted f c)
  weightedMass w K width (polyMul b (polyAdd b (polySmul (-a) u)))

/-- Difference of the two actual centered endpoint moments in the mixed edge. -/
def endpointMismatch (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') : Q' :=
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let psi := shifted f c
  weightedMass w K width (polyMul A (transferStep w K width (polyMul g (polyMul psi psi)))) -
    weightedMass w K width (polyMul (polyMul A psi) (polyMul A psi))

def endpointSquareDifference (width : Nat) (f : RatPoly) (c : Q') : RatPoly :=
  let psi := shifted f c
  polyAdd (polyMul psi psi) (polyNeg (liftBoundary (N width) (polyMul psi psi)))

private theorem support_pair {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks (blocks+blocks) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem step_coeff (w : Q') (K width : Nat) {p r : RatPoly}
    (h : RatPolyCoeffEqv p r) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width r) :=
  partialHaarHeads_congr (N width)
    ((RatPolyCoeffEqv.refl (kineticWeight w K width)).mul
      ((RatPolyCoeffEqv.refl (spatialWeight w K width)).mul h))

/-- b=B-cA, not a times the centered observable. -/
theorem centeredMessage_pin (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (centeredMessage w K width n f c)
      (polyAdd (transferStep w K width (polyMul (terminalMessage w K width n) f))
        (polySmul (-c) (transferStep w K width (terminalMessage w K width n)))) := by
  have hm : RatPolyCoeffEqv (polyMul (terminalMessage w K width n) (shifted f c))
      (polyAdd (polyMul (terminalMessage w K width n) f)
        (polySmul (-c) (terminalMessage w K width n))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right 1 _ f).trans (RatPolyCoeffEqv.one_smul _)).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-c) _ polyOne).trans
          ((RatPolyCoeffEqv.mul_one _).smul (-c))))
  exact (step_coeff w K width hm).trans
    ((transferStep_add w K width _ _).trans
      ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width (-c) _)))

private theorem lower_fold (w : Q') (K width n : Nat) (p : RatPoly) :
    H (N width+N width) (polyMul (mixedDensity w K width n) p) ≈
      weightedMass w K width (polyMul (terminalMessage w K width (n+1))
        (transferStep w K width (polyMul (terminalMessage w K width n) p))) := by
  have hr : RatPolyCoeffEqv (polyMul (mixedDensity w K width n) p)
      (polyMul (polyMul (kineticWeight w K width)
        (polyMul (spatialWeight w K width) (polyMul (terminalMessage w K width n) p)))
        (liftBoundary (N width) (polyMul (spatialWeight w K width)
          (terminalMessage w K width (n+1))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 4)) (.var 3))
      (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.var 4))
      (by decide) (fun
        | 0 => kineticWeight w K width | 1 => spatialWeight w K width
        | 2 => terminalMessage w K width n | 3 => p
        | _ => liftBoundary (N width) (polyMul (spatialWeight w K width)
            (terminalMessage w K width (n+1))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _ (step_pairing (N width) (N width) _ _ _ _)
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _))))

/-- The complete mismatch is an ORIGINAL mixed-window insertion. -/
theorem endpointMismatch_mixed_pin (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') :
    H (N width+N width) (polyMul (mixedDensity w K width n)
      (endpointSquareDifference width f c)) ≈ endpointMismatch w K width n f c := by
  let psi := shifted f c
  have hl := lower_fold w K width n (polyMul psi psi)
  rw [← terminalMessage_next w K width n] at hl
  have hu := mixedDensity_upper_marginal w K width n (polyMul psi psi)
  rw [← terminalMessage_next w K width n] at hu
  have hu' := Q'.eqv_trans _ _ _ hu (weightedMass_congr w K width
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => transferStep w K width (terminalMessage w K width n) | _ => psi)))
  exact Q'.eqv_trans _ _ _ (weighted_difference _ _ _ _)
    (Q'.add_eqv_congr' hl (Q'.neg_eqv_congr _ _ hu'))

private theorem square_expansion (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd p (polySmul (-1) q)) (polyAdd p (polySmul (-1) q)))
      (polyAdd (polyMul p p) (polyAdd (polySmul (-2) (polyMul p q)) (polyMul q q))) := by
  have he := (RatPolyCoeffEqv.refl p).add (cap_mul_left (-1) q).symm
  exact (he.mul he).trans ((coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.mul (.const (-1)) (.var 1)))
      (.add (.var 0) (.mul (.const (-1)) (.var 1))))
    (.add (.mul (.var 0) (.var 0))
      (.add (.mul (.const (-2)) (.mul (.var 0) (.var 1))) (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => p | _ => q)).trans
      ((RatPolyCoeffEqv.refl _).add ((cap_mul_left (-2) _).add (RatPolyCoeffEqv.refl _))))

/-- Exact ORIGINAL quadratic source identity for arbitrary reference a and
center c. In particular a=w^(3*length) does not require a source eigenpin. -/
theorem filtered_loop_commutator_identity (w : Q') (K width n : Nat)
    (loop : SourceLoop width) (c a : Q') :
    numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≈
      endpointMismatch w K width n (sourceCharacter width loop.edges 1) c +
        2*(1-a)*centeredTransferCross w K width n (sourceCharacter width loop.edges 1) c -
        2*commutatorGain w K width n (sourceCharacter width loop.edges 1) c a := by
  let f := sourceCharacter width loop.edges 1
  let psi := shifted f c
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let b := centeredMessage w K width n f c
  let u := polyMul A psi
  let ac := weightedMass w K width (polyMul A (transferStep w K width (polyMul g (polyMul psi psi))))
  let bb := weightedMass w K width (polyMul b b)
  let j := centeredTransferCross w K width n f c
  let uu := weightedMass w K width (polyMul u u)
  have hf := sourceCharacter_supported width loop.edges 1
  have hs := shifted_supported hf c
  have hj := SU2QuaternionProductHeatSourceCentering.jump_shifted (N width) f c
  have hjump : mixedJumpSquare w K width n psi ≈ mixedJumpSquare w K width n f :=
    (hj.mul hj).haar_insert (supported_polyMul (jump_supported width hs) (jump_supported width hs))
      (supported_polyMul (jump_supported width hf) (jump_supported width hf))
      (mixedDensity w K width n) (mixedDensity_supported w K width n)
  have hdshift : driftSquare w K width n psi ≈ driftSquare w K width n f :=
    weightedMass_congr w K width ((driftPolynomial_shifted w K width n f c).mul
      (driftPolynomial_shifted w K width n f c))
  have hsource : numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≈
      noise w K width n psi - driftSquare w K width n psi :=
    Q'.eqv_trans _ _ _ (filtered_loop_jump_drift w K width n loop)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_symm hjump)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hdshift))))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (mixedJumpSquare_noise_drift w K width n psi))
          (poly_identity_of_normal_eq
            (.add (.add (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 1))))
            (.add (.var 0) (.neg (.var 1))) (by decide)
            (fun | 0 => noise w K width n psi | _ => driftSquare w K width n psi))))
  have hn : noise w K width n psi ≈ ac+(-1)*bb :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (weightedMass_smul w K width (-1) _))
  have hd : driftSquare w K width n psi ≈ bb+((-2)*j+uu) :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width (square_expansion b u))
      (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
          (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-2) _)
            (Q'.mul_eqv_congr_left _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm b u))))
            (Q'.eqv_refl _)))))
  have hg : commutatorGain w K width n f c a ≈ bb+(-a)*j :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right _ _ _))
      (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
          (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right (-a) b u))
          (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-a) _)
            (Q'.mul_eqv_congr_left _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm b u)))))))
  exact Q'.eqv_trans _ _ _ hsource (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hn (Q'.neg_eqv_congr _ _ hd))
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.const (-1)) (.var 1)))
        (.neg (.add (.var 1) (.add (.mul (.const (-2)) (.var 2)) (.var 3)))))
      (.add (.add (.add (.var 0) (.neg (.var 3)))
        (.mul (.mul (.const 2) (.add (.const 1) (.neg (.var 4)))) (.var 2)))
        (.neg (.mul (.const 2) (.add (.var 1) (.mul (.neg (.var 4)) (.var 2))))))
      (by decide) (fun | 0 => ac | 1 => bb | 2 => j | 3 => uu | _ => a))
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hg))))))

private def fundamentalBound (width : Nat) (loop : SourceLoop width) :
    SquareBound (N width) (sourceCharacter width loop.edges 1) 4 := by
  have hu (e : OrientedBF4Link) (he : e ∈ loop.edges) :
      HaarCarrierEqv (N width) (polyQuaternionNorm (orientedLink width e)) polyOne := by
    have hmem := loop.physical e he
    have hi := List.idxOf_lt_length_of_mem hmem
    have h := haarNorm_coordinate hi
    unfold orientedLink link
    rw [if_pos hmem]
    split
    · exact (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans h
    · exact h
  exact SquareBound.changeCap (by decide : characterBound 1 ≈ (4 : Q'))
    (character_squareBound (SquareBound.scalar
      (let hp := sourceWord_supported width loop.edges
       show Supported (N width) (sourceWord width loop.edges) from
         ⟨hp.scalar, hp.iPart, hp.jPart, hp.kPart⟩)
      (word_unit (orientedLink width) loop.edges hu)) 1)

attribute [local irreducible] sourceCharacter
  YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial.mean

/-- Computed cap16 for the actual centered fundamental square. -/
def ownCenteredBound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    SquareBound (N width) (shifted (sourceCharacter width loop.edges 1)
      (ownMean hw0 hw1 K width hK n loop)) 16 := by
  let c := ownMean hw0 hw1 K width hK n loop
  have hc : c*c ≤ (4 : Q') := mean_square_le_four hw0 hw1 K width hK n loop
  have he : c*c+(4-c*c) ≈ (4 : Q') :=
    poly_identity_of_normal_eq (.add (.var 0) (.add (.const 4) (.neg (.var 0))))
      (.const 4) (by decide) (fun _ => c*c)
  let C : SquareBound (N width) (cap c) 4 :=
    SquareBound.changeCap he ((SquareBound.constant _ c).raise (4-c*c) (Q'.sub_nonneg_of_le hc))
  let P := (fundamentalBound width loop).add C.neg
  refine SquareBound.ofCoeff (shifted_supported (sourceCharacter_supported width loop.edges 1) c) ?_
    (SquareBound.changeCap (by decide : sumBound (4 : Q') 4 ≈ 16) P)
  exact (RatPolyCoeffEqv.one_smul _).add
    ((RatPolyCoeffEqv.smul_coefficient (poly_identity_of_normal_eq
      (.neg (.var 0)) (.mul (.const (-1)) (.var 0)) (by decide) (fun _ => c)) polyOne).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) c polyOne).symm.trans
        ((cap_mul_left (-1) (cap c)).symm.trans
          (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0))
            (.neg (.var 0)) (by decide) (fun _ => cap c)))))

private theorem gap_support {blocks : Nat} {p : RatPoly} {C : Q'}
    (P : SquareBound blocks p C) : SupportedQuaternionBlocks blocks (gap C p) :=
  supported_add (polySmul_supported (supported_one blocks) C)
    (support_neg (supported_polyMul P.support P.support))

private def lowerBound {blocks : Nat} {p : RatPoly} {C : Q'} (P : SquareBound blocks p C) :
    SquareBound (blocks+blocks) p C :=
  ⟨support_pair P.support, P.nonnegative, certificate_extend blocks (gap_support P) P.certificate⟩

private def liftedBound {blocks : Nat} {p : RatPoly} {C : Q'} (P : SquareBound blocks p C) :
    SquareBound (blocks+blocks) (liftBoundary blocks p) C where
  support := lift_supported P.support blocks
  nonnegative := P.nonnegative
  certificate := by
    have hc : HaarCarrierEqv (blocks+blocks) (liftBoundary blocks (gap C p))
        (gap C (liftBoundary blocks p)) := by
      unfold gap
      rw [lift_add, lift_neg, lift_product]
      exact HaarCarrierEqv.add (lift_cap_carrier blocks C) (HaarCarrierEqv.refl _ _)
    exact .transport hc.symm (lift_certificate blocks P.certificate)

/-- Cap16 on the actual centered PRODUCT at the two endpoints. -/
def centeredProduct_interval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    let psi := shifted (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop)
    Interval (N width+N width) (polyMul psi (liftBoundary (N width) psi)) 16 := by
  let psi := shifted (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop)
  let P := ownCenteredBound hw0 hw1 K width hK n loop
  let L := lowerBound P
  let U := liftedBound P
  refine ⟨supported_polyMul L.support U.support, by decide, L.cross U, ?_⟩
  exact Certificate.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.mul (.var 1) (.var 2)))
    (.add (.var 0) (.neg (.mul (.neg (.var 1)) (.var 2)))) (by decide)
    (fun | 0 => cap 16 | 1 => psi | _ => liftBoundary (N width) psi)) (L.neg.cross U)

/-- Difference of two nonnegative cap16 squares has cap16, not cap32. -/
def endpointSquareDifference_interval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    Interval (N width+N width) (endpointSquareDifference width
      (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop)) 16 := by
  let P := ownCenteredBound hw0 hw1 K width hK n loop
  let psi := shifted (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop)
  let lo := polyMul psi psi
  let up := liftBoundary (N width) lo
  have hlo := support_pair (supported_polyMul P.support P.support)
  have hup := lift_supported (supported_polyMul P.support P.support) (N width)
  let Cl : Certificate (N width+N width) (polyAdd (cap 16) (polyNeg lo)) :=
    certificate_extend (N width) (gap_support P) P.certificate
  let Cu : Certificate (N width+N width) (polyAdd (cap 16) (polyNeg up)) := by
    have h : HaarCarrierEqv (N width+N width) (liftBoundary (N width) (gap 16 psi))
        (polyAdd (cap 16) (polyNeg up)) := by
      unfold gap
      rw [lift_add, lift_neg]
      exact HaarCarrierEqv.add (lift_cap_carrier (N width) 16) (HaarCarrierEqv.refl _ _)
    exact .transport h.symm (lift_certificate (N width) P.certificate)
  refine ⟨supported_add hlo (support_neg hup), by decide, ?_, ?_⟩
  · exact Certificate.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.add (.var 0) (.neg (.var 1))) (.var 2)) (by decide)
      (fun | 0 => cap 16 | 1 => lo | _ => up))
      (Cl.add (by
        change Certificate (N width+N width) (liftBoundary (N width) (polyMul psi psi))
        rw [lift_product]
        exact Certificate.square _ (lift_supported P.support (N width))))
  · exact Certificate.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.add (.var 0) (.neg (.var 2))) (.var 1)) (by decide)
      (fun | 0 => cap 16 | 1 => lo | _ => up))
      (Cu.add (Certificate.square psi (support_pair P.support)))

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
        | 2 => liftBoundary (N width) g | _ => liftBoundary (N width) p)
  have hupper : H (N width+N width) (polyMul (edgeDensity w K width g)
      (liftBoundary (N width) p)) ≈ weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
      (Q'.eqv_trans _ _ _ (step_pairing (N width) (N width) _ _ _ _)
        (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
          (.mul (.var 1) (.mul (.mul (.var 2) (.var 0)) (.var 3))) (by decide) (fun
            | 0 => transferStep w K width g | 1 => spatialWeight w K width | 2 => g | _ => p))))
  exact Q'.eqv_trans _ _ _ hupper
    (Q'.eqv_symm (edge_marginal_pairing w K width (terminalMessage_supported w K width n) hp))

private theorem matched_difference_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    windowRatio hw0 hw1 K width hK n 1 n (endpointSquareDifference width
      (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop)) ≈ 0 := by
  let psi := shifted (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop)
  have hs := shifted_supported (sourceCharacter_supported width loop.edges 1)
    (ownMean hw0 hw1 K width hK n loop)
  let I := endpointSquareDifference_interval hw0 hw1 K width hK n loop
  have hp : H (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width n))
        (endpointSquareDifference width (sourceCharacter width loop.edges 1)
          (ownMean hw0 hw1 K width hK n loop))) ≈ 0 :=
    Q'.eqv_trans _ _ _ (weighted_difference (N width+N width)
      (edgeDensity w K width (terminalMessage w K width n)) (polyMul psi psi)
      (liftBoundary (N width) (polyMul psi psi)))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (matched_upper_lower w K width n (supported_polyMul hs hs))))
      (Q'.add_neg_self_eqv _))
  have hn := terminalEdge_probe_pairing w K width n n I.support
  have hnum := Q'.eqv_trans _ _ _ (Q'.eqv_symm hn) hp
  unfold windowRatio massRatio
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hnum) (Q'.zero_mul_eqv _)

private theorem clear_bound (M Z b : Q') (hz : (0 : Q') < Z)
    (h : M*Q'.recipPos Z hz ≤ b) : M ≤ b*Z := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _ Z h (Q'.le_of_lt hz)
  have he : (M*Q'.recipPos Z hz)*Z ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hz))) (Q'.mul_one_eqv M))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hb

/-- Actual endpoint mismatch, with no partition substitution or sign premise. -/
theorem endpointMismatch_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    Q'.abs (endpointMismatch w K width n (sourceCharacter width loop.edges 1)
      (ownMean hw0 hw1 K width hK n loop)) ≤
        (mixRate hw0 hw1 width^n*32)*evenPartition w K width n := by
  let p := endpointSquareDifference width (sourceCharacter width loop.edges 1)
    (ownMean hw0 hw1 K width hK n loop)
  let I := endpointSquareDifference_interval hw0 hw1 K width hK n loop
  let r := mixRate hw0 hw1 width^n*32
  have hb := windowRatio_right_commonTail hw0 hw1 K width hK n 1 n (n+1) n
    (by simpa only [Nat.one_add, Nat.two_mul] using I) (by omega) (Nat.le_refl n)
  have hzero := matched_difference_zero hw0 hw1 K width hK n loop
  have hup : windowRatio hw0 hw1 K width hK n 1 (n+1) p ≤ r :=
    Q'.le_trans' _ _ _ hb.1 (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hzero (Q'.mul_eqv_congr_left _ _ _ (by decide : (16 : Q')+16 ≈ 32)))
      (Q'.eqv_of_eq (Q'.zero_add' _))))
  have hlo : -r ≤ windowRatio hw0 hw1 K width hK n 1 (n+1) p := by
    have h := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hzero) hb.2
    have h' : (0 : Q') ≤ windowRatio hw0 hw1 K width hK n 1 (n+1) p+r :=
      Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : (16 : Q')+16 ≈ 32))))
    have h'' := Q'.add_le_add_right _ _ (-r) h'
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
      (Q'.le_trans' _ _ _ h'' (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0) (by decide)
        (fun | 0 => windowRatio hw0 hw1 K width hK n 1 (n+1) p | _ => r))))
  let Z := weightedMass w K width (polyMul (terminalMessage w K width (n+1))
    (terminalMessage w K width (n+1)))
  let hz := terminalPair_positive hw0 hw1 K width hK (n+1) (n+1)
  let M := weightedMass w K width (polyMul (observedMessage w K width n 1 p)
    (terminalMessage w K width (n+1)))
  have hpin : M ≈ endpointMismatch w K width n (sourceCharacter width loop.edges 1)
      (ownMean hw0 hw1 K width hK n loop) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (mixedDensity_window_pairing w K width n I.support))
      (endpointMismatch_mixed_pin w K width n _ _)
  have hZ : Z ≈ evenPartition w K width n := by
    have h := evenPartition_middle_pin w K width n
    rw [terminalMessage_next w K width n] at h
    exact Q'.eqv_symm h
  have hupper : M ≤ r*Z := clear_bound M Z r hz (by simpa only [windowRatio, massRatio] using hup)
  have hnegative : -M ≤ r*Z := clear_bound (-M) Z r hz (by
    have h := Q'.neg_le_neg hlo
    have he : -(M*Q'.recipPos Z hz) ≈ (-M)*Q'.recipPos Z hz :=
      Q'.eqv_symm (Q'.neg_mul_eqv _ _)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
      (Q'.le_trans' _ _ _ (by simpa only [windowRatio, massRatio] using h)
        (Q'.le_of_eqv (Q'.neg_neg_eqv r))))
  apply Q'.abs_le
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hZ)))
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg hnegative)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv M) hpin)))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin)
      (Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hZ)))

private theorem cross_fold (w : Q') (K width n : Nat) (p r : RatPoly) :
    H (N width+N width) (polyMul (mixedDensity w K width n) (polyMul p (liftBoundary (N width) r))) ≈
      weightedMass w K width (polyMul (polyMul (terminalMessage w K width (n+1)) r)
        (transferStep w K width (polyMul (terminalMessage w K width n) p))) := by
  have hr : RatPolyCoeffEqv
      (polyMul (mixedDensity w K width n) (polyMul p (liftBoundary (N width) r)))
      (polyMul (polyMul (kineticWeight w K width)
        (polyMul (spatialWeight w K width) (polyMul (terminalMessage w K width n) p)))
        (liftBoundary (N width) (polyMul (spatialWeight w K width)
          (polyMul (terminalMessage w K width (n+1)) r)))) := by
    unfold mixedDensity
    simp only [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 4) (.var 5))) (.mul (.var 3) (.var 6)))
      (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.var 4) (.mul (.var 5) (.var 6)))) (by decide) (fun
          | 0 => kineticWeight w K width | 1 => spatialWeight w K width
          | 2 => terminalMessage w K width n | 3 => p
          | 4 => liftBoundary (N width) (spatialWeight w K width)
          | 5 => liftBoundary (N width) (terminalMessage w K width (n+1))
          | _ => liftBoundary (N width) r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _ (step_pairing (N width) (N width) _ _ _ _)
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (RatPolyCoeffEqv.mul_assoc _ _ _))))

/-- The J1 numerator is the actual mixed centered endpoint product. -/
theorem centeredTransferCross_mixed_pin (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') :
    H (N width+N width) (polyMul (mixedDensity w K width n)
      (polyMul (shifted f c) (liftBoundary (N width) (shifted f c)))) ≈
        centeredTransferCross w K width n f c := by
  have h := cross_fold w K width n (shifted f c) (shifted f c)
  rw [← terminalMessage_next w K width n] at h
  exact h

/-- Only the SAME EVEN partition is inverted in the mixed J1 window pin. -/
theorem centeredTransferCross_window_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (c : Q') :
    centeredTransferCross w K width n f c * Q'.recipPos (evenPartition w K width n)
      (evenPartition_positive hw0 hw1 K width hK n) ≈
        windowRatio hw0 hw1 K width hK n 1 (n+1)
          (polyMul (shifted f c) (liftBoundary (N width) (shifted f c))) := by
  have hs := shifted_supported hf c
  have hp := supported_polyMul (support_pair hs) (lift_supported hs (N width))
  have hn := Q'.eqv_trans _ _ _ (Q'.eqv_symm (centeredTransferCross_mixed_pin w K width n f c))
    (mixedDensity_window_pairing w K width n hp)
  have hZ := evenPartition_middle_pin w K width n
  rw [terminalMessage_next w K width n] at hZ
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hn)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _
      (evenPartition_positive hw0 hw1 K width hK n)
      (terminalPair_positive hw0 hw1 K width hK (n+1) (n+1)) hZ))

private theorem matched_product_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    let f := sourceCharacter width loop.edges 1
    let psi := shifted f (ownMean hw0 hw1 K width hK n loop)
    windowRatio hw0 hw1 K width hK n 1 n (polyMul psi (liftBoundary (N width) psi)) ≈
      normalizedCenteredTransferQuadratic hw0 hw1 K width hK n f := by
  let f := sourceCharacter width loop.edges 1
  let ce := ownMean hw0 hw1 K width hK n loop
  let cm := normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hK n)
  have hc : ce ≈ cm := Q'.eqv_trans _ _ _
    (mean_pin hw0 hw1 K width hK n (sourceCharacter_supported width loop.edges 1))
    (Q'.eqv_symm (marginalMoment_pin hw0 hw1 K width hK n f))
  have hpsi : RatPolyCoeffEqv (shifted f ce) (oddCentered hw0 hw1 K width hK n f) :=
    (RatPolyCoeffEqv.refl (polySmul 1 f)).add
      (RatPolyCoeffEqv.smul_coefficient (Q'.neg_eqv_congr _ _ hc) polyOne)
  exact Q'.eqv_trans _ _ _ (windowRatio_congr hw0 hw1 K width hK n 1 n
    (hpsi.mul (lift_coeff (N width) hpsi)))
    (Q'.eqv_symm (normalizedCenteredTransferQuadratic_window hw0 hw1 K width hK n
      (sourceCharacter_supported width loop.edges 1)))

/-- Both-order comparison to the existing matched transfer quadratic, with
the SAME odd center. This supplies no reserve or sign for the gain. -/
theorem centeredTransferCross_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    let f := sourceCharacter width loop.edges 1
    let J := centeredTransferCross w K width n f (ownMean hw0 hw1 K width hK n loop) *
      Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n)
    let C := normalizedCenteredTransferQuadratic hw0 hw1 K width hK n f
    J ≤ C+mixRate hw0 hw1 width^n*32 ∧ C ≤ J+mixRate hw0 hw1 width^n*32 := by
  let I := centeredProduct_interval hw0 hw1 K width hK n loop
  have hb := windowRatio_right_commonTail hw0 hw1 K width hK n 1 n (n+1) n
    (by simpa only [Nat.one_add, Nat.two_mul] using I) (by omega) (Nat.le_refl n)
  have hmixed := centeredTransferCross_window_pin hw0 hw1 K width hK n
    (sourceCharacter_supported width loop.edges 1) (ownMean hw0 hw1 K width hK n loop)
  have hmatched := matched_product_pin hw0 hw1 K width hK n loop
  have ht := Q'.mul_eqv_congr_left (mixRate hw0 hw1 width^n) _ _
    (by decide : (16 : Q')+16 ≈ 32)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hmixed)
      (Q'.le_trans' _ _ _ hb.1 (Q'.le_of_eqv (Q'.add_eqv_congr' hmatched ht))),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hmatched)
      (Q'.le_trans' _ _ _ hb.2 (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_symm hmixed) ht)))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.centeredMessage_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.centeredMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.centeredTransferCross
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.commutatorGain
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.endpointMismatch
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.endpointSquareDifference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.endpointMismatch_mixed_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.filtered_loop_commutator_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.ownCenteredBound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.endpointSquareDifference_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.endpointMismatch_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.centeredProduct_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.centeredTransferCross_mixed_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.centeredTransferCross_window_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain.centeredTransferCross_commonTail
