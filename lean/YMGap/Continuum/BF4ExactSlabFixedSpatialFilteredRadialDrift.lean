/-
# The original filtered source has a mixed radial/drift ceiling

The literal (n,2,n) filtered numerator is J-2D. Here J is the fundamental
one-edge jump square in the ORIGINAL mixed window (n,1,n+1), with g_n
on the lower/input slice and g_(n+1) on the upper/output slice. The weight
retains both spatial factors, the complete kinetic kernel and both actual
terminal messages. Its total mass is the SAME EVEN radius-two partition.

The original quaternion square certificate bounds J by twice the mixed
radial moment plus twice the word-chord quartic moment. The negative drift
square is retained. Neither mixed moment is estimated or identified with
OWN interacting variance; no finite odd/even partition equality, stationarity,
quartic-kernel identification or changing-family survival is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (link orientedLink spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder (kineticCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump jump_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (observedMessage windowRatio)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement
  (upperOriented upper_character_lift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement (wilsonRadialBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement (wordChordal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_supported)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step_pairing)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (chain)
open YMGap.Continuum.SU2QuaternionHeadWindowContraction (windowMessage windowMessage_pairing)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarRadialChordalIncrement

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage spatialWeight kineticWeight

/-- The ORIGINAL mixed window (n,1,n+1), not a matched-terminal edge. -/
def mixedDensity (w : Q') (K width n : Nat) : RatPoly :=
  polyMul (polyMul (kineticWeight w K width)
    (polyMul (spatialWeight w K width) (terminalMessage w K width n)))
    (liftBoundary (N width)
      (polyMul (spatialWeight w K width) (terminalMessage w K width (n+1))))

private theorem support_pair {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks (blocks+blocks) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

theorem mixedDensity_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width+N width) (mixedDensity w K width n) :=
  supported_polyMul
    (supported_polyMul (kineticWeight_supported w K width)
      (support_pair (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width n))))
    (lift_supported (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1))) (N width))

/-- Constructed from the two actual terminal certificates and original K/V. -/
def mixedDensity_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width+N width) (mixedDensity w K width n) :=
  let VG := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)
  let VA := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK (n+1))
  ((kineticCertificate hw0 hw1 K width hK).mul
    (certificate_extend (N width) (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n)) VG)).mul
    (lift_certificate (N width) VA)

def mixedJumpSquare (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  quaternionHaar (N width+N width)
    (polyMul (mixedDensity w K width n) (polyMul (jump width f) (jump width f)))

/-- Both mixed moments use the SAME lower word, upper word and full weight. -/
def mixedRadialMoment (w : Q') (K width n : Nat) (loop : SourceLoop width) : Q' :=
  let f := characterPolynomial (wordWith (upperOriented width) loop.edges).scalar 1
  quaternionHaar (N width+N width) (polyMul (mixedDensity w K width n)
    (polyMul (wordChordal width loop) (polyAdd (cap 4) (polyNeg (polyMul f f)))))

def mixedQuarticMoment (w : Q') (K width n : Nat) (loop : SourceLoop width) : Q' :=
  quaternionHaar (N width+N width) (polyMul (mixedDensity w K width n)
    (polyMul (wordChordal width loop) (wordChordal width loop)))

private theorem lower_fold (w : Q') (K width n : Nat) (p : RatPoly) :
    quaternionHaar (N width+N width) (polyMul (mixedDensity w K width n) p) ≈
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
        | 0 => kineticWeight w K width
        | 1 => spatialWeight w K width
        | 2 => terminalMessage w K width n
        | 3 => p
        | _ => liftBoundary (N width) (polyMul (spatialWeight w K width)
            (terminalMessage w K width (n+1))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _ (step_pairing (N width) (N width) _ _ _ _)
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _))))

private theorem cross_fold (w : Q') (K width n : Nat) (p r : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (mixedDensity w K width n) (polyMul p (liftBoundary (N width) r))) ≈
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
          | 0 => kineticWeight w K width
          | 1 => spatialWeight w K width
          | 2 => terminalMessage w K width n
          | 3 => p
          | 4 => liftBoundary (N width) (spatialWeight w K width)
          | 5 => liftBoundary (N width) (terminalMessage w K width (n+1))
          | _ => liftBoundary (N width) r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _ (step_pairing (N width) (N width) _ _ _ _)
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _))))

private theorem upper_fold (w : Q') (K width n : Nat) (p : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (mixedDensity w K width n) (liftBoundary (N width) p)) ≈
      weightedMass w K width (polyMul (polyMul (terminalMessage w K width (n+1)) p)
        (transferStep w K width (terminalMessage w K width n))) := by
  have hr : RatPolyCoeffEqv
      (polyMul (mixedDensity w K width n) (liftBoundary (N width) p))
      (polyMul (polyMul (kineticWeight w K width)
        (polyMul (spatialWeight w K width) (terminalMessage w K width n)))
        (liftBoundary (N width) (polyMul (polyMul (spatialWeight w K width)
          (terminalMessage w K width (n+1))) p))) := by
    unfold mixedDensity
    simp only [lift_product]
    exact RatPolyCoeffEqv.mul_assoc _ _ _
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _ (step_pairing (N width) (N width) _ _ _ _)
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.mul (.var 1) (.mul (.mul (.var 2) (.var 3)) (.var 0)))
        (by decide) (fun
          | 0 => transferStep w K width (terminalMessage w K width n)
          | 1 => spatialWeight w K width
          | 2 => terminalMessage w K width (n+1)
          | _ => p))))

/-- The upper marginal is literally the middle A² marginal, not an odd law. -/
theorem mixedDensity_upper_marginal (w : Q') (K width n : Nat) (p : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (mixedDensity w K width n) (liftBoundary (N width) p)) ≈
      weightedMass w K width (polyMul
        (polyMul (terminalMessage w K width (n+1)) (terminalMessage w K width (n+1))) p) := by
  have h := upper_fold w K width n p
  rw [terminalMessage_next w K width n] at h
  exact Q'.eqv_trans _ _ _ h (weightedMass_congr w K width
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 0))
      (.mul (.mul (.var 0) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => terminalMessage w K width (n+1) | _ => p)))

/-- Exact original one-edge Fubini pin, with arbitrary endpoint depths. -/
theorem terminalEdge_probe_pairing (w : Q') (K width m n : Nat) {p : RatPoly}
    (_hp : SupportedQuaternionBlocks (N width+N width) p) :
    quaternionHaar (N width+N width)
      (polyMul (polyMul (polyMul (kineticWeight w K width)
        (polyMul (spatialWeight w K width) (terminalMessage w K width m)))
        (liftBoundary (N width) (polyMul (spatialWeight w K width)
          (terminalMessage w K width n)))) p) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width m 1 p) (terminalMessage w K width n)) := by
  let g := terminalMessage w K width m
  let a := terminalMessage w K width n
  let V := spatialWeight w K width
  let W := kineticWeight w K width
  let G := liftBoundary (N width) (polyMul V a)
  have h := windowMessage_pairing (N width) W V 1 g p a
  have hcount : (1+1)*(N width) = N width+N width := by omega
  rw [hcount] at h
  have hin : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul W (polyMul V g)) G) p)
      (polyMul (polyMul g p) (chain (N width) W V 1 a)) := by
    change RatPolyCoeffEqv
      (polyMul (polyMul (polyMul W (polyMul V g)) G) p)
      (polyMul (polyMul g p) (polyMul W (polyMul V G)))
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.var 4))
      (.mul (.mul (.var 2) (.var 4)) (.mul (.var 0) (.mul (.var 1) (.var 3))))
      (by decide) (fun | 0 => W | 1 => V | 2 => g | 3 => G | _ => p)
  have hout : RatPolyCoeffEqv
      (polyMul (windowMessage (N width) W V 1 g p) (polyMul V a))
      (polyMul V (polyMul (observedMessage w K width m 1 p) a)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => observedMessage w K width m 1 p | 1 => V | _ => a)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hin)
    (Q'.eqv_trans _ _ _ h (haar_of_coeff hout))

theorem mixedDensity_window_pairing (w : Q') (K width n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width+N width) p) :
    quaternionHaar (N width+N width) (polyMul (mixedDensity w K width n) p) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width n 1 p) (terminalMessage w K width (n+1))) :=
  terminalEdge_probe_pairing w K width n (n+1) hp

/-- The mixed edge has the SAME EVEN partition as the radius-two source. -/
theorem mixedDensity_mass (w : Q') (K width n : Nat) :
    quaternionHaar (N width+N width) (mixedDensity w K width n) ≈
      evenPartition w K width n := by
  have h := lower_fold w K width n polyOne
  have hc : RatPolyCoeffEqv
      (transferStep w K width (polyMul (terminalMessage w K width n) polyOne))
      (transferStep w K width (terminalMessage w K width n)) :=
    SU2QuaternionHeadChainComposition.partialHaarHeads_congr (N width)
      ((RatPolyCoeffEqv.refl _).mul ((RatPolyCoeffEqv.refl _).mul (RatPolyCoeffEqv.mul_one _)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
    (Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
      (weightedMass_congr w K width (hc.mul_left _))
      (by
        rw [terminalMessage_next w K width n]
        have hm := evenPartition_middle_pin w K width n
        rw [terminalMessage_next w K width n] at hm
        exact Q'.eqv_symm hm)))

private theorem neg_coefficient (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg p) (polySmul (-1) p) :=
  (coeffEvalExpr_eqv_of_normalize_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
    (by decide) (fun _ => p)).trans (cap_mul_left (-1) p)

private theorem square_expansion (a b : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd a (polySmul (-1) b))
      (polyAdd a (polySmul (-1) b)))
      (polyAdd (polyMul a a) (polyAdd (polySmul (-2) (polyMul a b)) (polyMul b b))) := by
  have h := (RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b).symm
  refine (h.mul h).trans ?_
  refine (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.mul (.const (-1)) (.var 1)))
      (.add (.var 0) (.mul (.const (-1)) (.var 1))))
    (.add (.mul (.var 0) (.var 0))
      (.add (.mul (.const (-2)) (.mul (.var 0) (.var 1))) (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => a | _ => b)).trans ?_
  exact (RatPolyCoeffEqv.refl _).add ((cap_mul_left (-2) _).add (RatPolyCoeffEqv.refl _))

/-- Exact mixed jump identity: the noise is NOT itself the jump square. -/
theorem mixedJumpSquare_noise_drift (w : Q') (K width n : Nat) (f : RatPoly) :
    mixedJumpSquare w K width n f ≈ noise w K width n f + driftSquare w K width n f := by
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let B := transferStep w K width (polyMul g f)
  let C := transferStep w K width (polyMul g (polyMul f f))
  let ac := weightedMass w K width (polyMul A C)
  let bb := weightedMass w K width (polyMul B B)
  let abf := weightedMass w K width (polyMul (polyMul A f) B)
  let aaff := weightedMass w K width (polyMul (polyMul A f) (polyMul A f))
  have hl : quaternionHaar (N width+N width)
      (polyMul (mixedDensity w K width n) (polyMul f f)) ≈ ac := by
    have h := lower_fold w K width n (polyMul f f)
    rw [← terminalMessage_next w K width n] at h
    exact h
  have hc : quaternionHaar (N width+N width)
      (polyMul (mixedDensity w K width n) (polyMul f (liftBoundary (N width) f))) ≈ abf := by
    have h := cross_fold w K width n f f
    rw [← terminalMessage_next w K width n] at h
    exact h
  have hu : quaternionHaar (N width+N width) (polyMul (mixedDensity w K width n)
      (polyMul (liftBoundary (N width) f) (liftBoundary (N width) f))) ≈ aaff := by
    rw [← lift_product]
    have h := upper_fold w K width n (polyMul f f)
    rw [← terminalMessage_next w K width n] at h
    exact Q'.eqv_trans _ _ _ h (weightedMass_congr w K width
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => A | _ => f)))
  have hj : mixedJumpSquare w K width n f ≈ ac+((-2)*abf+aaff) := by
    have hp : RatPolyCoeffEqv (jump width f)
        (polyAdd f (polySmul (-1) (liftBoundary (N width) f))) :=
      (RatPolyCoeffEqv.refl _).add (neg_coefficient _)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff
      (((hp.mul hp).trans (square_expansion f (liftBoundary (N width) f))).mul_left _))
      (Q'.eqv_trans _ _ _ (haar_weighted_add _ _ _ _)
        (Q'.add_eqv_congr' hl (Q'.eqv_trans _ _ _ (haar_weighted_add _ _ _ _)
          (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (weighted_scale _ _ _ (-2))
            (Q'.mul_eqv_congr_left _ _ _ hc)) hu))))
  have hn : noise w K width n f ≈ ac+(-1)*bb :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (weightedMass_smul w K width (-1) _))
  have hd : driftSquare w K width n f ≈ bb+((-2)*abf+aaff) :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width (square_expansion B (polyMul A f)))
      (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
          (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-2) _)
            (Q'.mul_eqv_congr_left _ _ _ (weightedMass_congr w K width
              (RatPolyCoeffEqv.mul_comm B (polyMul A f))))) (Q'.eqv_refl _)))))
  exact Q'.eqv_trans _ _ _ hj (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.var 0) (.add (.mul (.const (-2)) (.var 2)) (.var 3)))
      (.add (.add (.var 0) (.mul (.const (-1)) (.var 1)))
        (.add (.var 1) (.add (.mul (.const (-2)) (.var 2)) (.var 3))))
      (by decide) (fun | 0 => ac | 1 => bb | 2 => abf | _ => aaff))
    (Q'.eqv_symm (Q'.add_eqv_congr' hn hd)))

/-- The literal ORIGINAL source equals jump minus TWICE the actual drift. -/
theorem filtered_loop_jump_drift (w : Q') (K width n : Nat) (loop : SourceLoop width) :
    numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≈
      mixedJumpSquare w K width n (sourceCharacter width loop.edges 1) +
        -(2*driftSquare w K width n (sourceCharacter width loop.edges 1)) :=
  Q'.eqv_trans _ _ _ (filtered_loop_numerator w K width n loop 1)
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.add (.add (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 1))))
      (by decide) (fun
        | 0 => noise w K width n (sourceCharacter width loop.edges 1)
        | _ => driftSquare w K width n (sourceCharacter width loop.edges 1)))
      (Q'.add_eqv_congr' (Q'.eqv_symm (mixedJumpSquare_noise_drift w K width n _))
        (Q'.eqv_refl _)))

private theorem lower_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) : Supported (N width+N width) (orientedLink width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width)
      (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf e.link)) :=
    Supported.coordinate (by omega)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact hs.conj
  · exact hs

private theorem upper_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) : Supported (N width+N width) (upperOriented width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width)
      (PolyQuaternion.coordinateVariable (N width+(baseLinks width).idxOf e.link)) :=
    Supported.coordinate (by omega)
  unfold upperOriented
  split
  · exact hs.conj
  · exact hs

private theorem lower_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (orientedLink width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : (baseLinks width).idxOf e.link < N width+N width)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

private theorem upper_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (upperOriented width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : N width+(baseLinks width).idxOf e.link < N width+N width)
  unfold upperOriented
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem padded_neg {n : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv n p q) :
    PaddedPolynomialCoeffEqv n (polyNeg p) (polyNeg q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

private theorem norm_difference_swap (p q : PolyQuaternion) :
    RatPolyCoeffEqv (polyQuaternionNorm (difference q p))
      (polyQuaternionNorm (difference p q)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.norm
      ⟨.add (.var 4) (.neg (.var 0)), .add (.var 5) (.neg (.var 1)),
        .add (.var 6) (.neg (.var 2)), .add (.var 7) (.neg (.var 3))⟩)
    (PolyQuaternionExpr.norm
      ⟨.add (.var 0) (.neg (.var 4)), .add (.var 1) (.neg (.var 5)),
        .add (.var 2) (.neg (.var 6)), .add (.var 3) (.neg (.var 7))⟩)
    (by decide) (fun
      | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
      | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart)

private theorem trace_square_swap (p q : PolyQuaternion) :
    RatPolyCoeffEqv (polyMul (traceDifference p q) (traceDifference p q))
      (polyMul (traceDifference q p) (traceDifference q p)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
    (.mul (.add (.var 1) (.neg (.var 0))) (.add (.var 1) (.neg (.var 0))))
    (by decide) (fun | 0 => characterPolynomial p.scalar 1 | _ => characterPolynomial q.scalar 1)

/-- The upper-word radial gap is the literal lifted original observable gap.
The transport is padded coefficient equality under the ORIGINAL Haar. -/
theorem mixedRadialMoment_upper_pin (w : Q') (K width n : Nat) (loop : SourceLoop width) :
    mixedRadialMoment w K width n loop ≈
      quaternionHaar (N width+N width) (polyMul (mixedDensity w K width n)
        (polyMul (wordChordal width loop) (polyAdd (cap 4) (polyNeg
          (polyMul (liftBoundary (N width) (sourceCharacter width loop.edges 1))
            (liftBoundary (N width) (sourceCharacter width loop.edges 1))))))) := by
  have hp := word_supported (orientedLink width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
  have hq := word_supported (upperOriented width) loop.edges
    (fun e he => upper_supported (loop.physical e he))
  have hd := difference_supported hp hq
  have hr : SupportedQuaternionBlocks (N width+N width) (wordChordal width loop) :=
    supported_add (supported_polyMul hd.scalar hd.scalar)
      (supported_add (supported_polyMul hd.iPart hd.iPart)
        (supported_add (supported_polyMul hd.jPart hd.jPart)
          (supported_polyMul hd.kPart hd.kPart)))
  have hu := character_supported hq.scalar 1
  have hl := lift_supported (sourceCharacter_supported width loop.edges 1) (N width)
  have hcap : SupportedQuaternionBlocks (N width+N width) (cap 4) := by
    intro t ht
    obtain ⟨r,hr',rfl⟩ := List.mem_map.mp ht
    exact supported_one _ r hr'
  have h := upper_character_lift width loop
  have hgap := (PaddedPolynomialCoeffEqv.refl (N width+N width) (cap 4)).add
    (padded_neg (h.mul h))
  have he := hgap.haar_insert
    (supported_add hcap (neg_supported (supported_polyMul hl hl)))
    (supported_add hcap (neg_supported (supported_polyMul hu hu)))
    (polyMul (mixedDensity w K width n) (wordChordal width loop))
    (supported_polyMul (mixedDensity_supported w K width n) hr)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)))

theorem mixed_radial_split (w : Q') (K width n : Nat) (loop : SourceLoop width) :
    quaternionHaar (N width+N width)
      (polyMul (mixedDensity w K width n)
        (radialBudget (wordWith (upperOriented width) loop.edges) (sourceWord width loop.edges))) ≈
      2*mixedRadialMoment w K width n loop + 2*mixedQuarticMoment w K width n loop := by
  let p := sourceWord width loop.edges
  let q := wordWith (upperOriented width) loop.edges
  have hr := norm_difference_swap p q
  have hbudget := (radialBudget_pin q p).trans
    (((hr.mul (RatPolyCoeffEqv.refl _)).smul 2).add ((hr.mul hr).smul 2))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hbudget.mul_left _))
    (Q'.eqv_trans _ _ _ (haar_weighted_add _ _ _ _)
      (Q'.add_eqv_congr' (weighted_scale _ _ _ 2) (weighted_scale _ _ _ 2)))

theorem mixedJumpSquare_radial_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    mixedJumpSquare w K width n (sourceCharacter width loop.edges 1) ≤
      2*mixedRadialMoment w K width n loop + 2*mixedQuarticMoment w K width n loop := by
  let p := sourceWord width loop.edges
  let q := wordWith (upperOriented width) loop.edges
  let W := mixedDensity w K width n
  have hp := word_supported (orientedLink width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
  have hq := word_supported (upperOriented width) loop.edges
    (fun e he => upper_supported (loop.physical e he))
  have hup := word_unit (orientedLink width) loop.edges
    (fun e he => lower_unit (loop.physical e he))
  have huq := word_unit (upperOriented width) loop.edges
    (fun e he => upper_unit (loop.physical e he))
  have hw := mixedDensity_supported w K width n
  have hj := jump_supported width (sourceCharacter_supported width loop.edges 1)
  have hd : SupportedQuaternionBlocks (N width+N width) (traceDifference p q) :=
    supported_add (character_supported hp.scalar 1)
      (neg_supported (character_supported hq.scalar 1))
  have hpin : PaddedPolynomialCoeffEqv (N width+N width)
      (jump width (sourceCharacter width loop.edges 1)) (traceDifference p q) :=
    (PaddedPolynomialCoeffEqv.refl _ _).add (padded_neg (upper_character_lift width loop))
  have he := (hpin.mul hpin).haar_insert
    (supported_polyMul hj hj) (supported_polyMul hd hd) W hw
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff ((trace_square_swap p q).mul_left W)))
      (Q'.le_trans' _ _ _ (weighted_radial_bound
        (mixedDensity_certificate hw0 hw1 K width hK n) hq hp huq hup)
        (Q'.le_of_eqv (mixed_radial_split w K width n loop))))

/-- Genuine signed-source ceiling retaining both mixed moments and -2D. -/
theorem filtered_loop_radial_drift_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≤
      (2*mixedRadialMoment w K width n loop + 2*mixedQuarticMoment w K width n loop) +
        -(2*driftSquare w K width n (sourceCharacter width loop.edges 1)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (filtered_loop_jump_drift w K width n loop))
    (Q'.add_le_add (mixedJumpSquare_radial_bound hw0 hw1 K width hK n loop)
      (Q'.le_refl' _))

/-- SAME original symmetric window normalization, by its positive EVEN Z. -/
theorem filtered_loop_radial_drift_normalized {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    windowRatio hw0 hw1 K width hK n 2 n
      (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≤
      ((2*mixedRadialMoment w K width n loop + 2*mixedQuarticMoment w K width n loop) +
        -(2*driftSquare w K width n (sourceCharacter width loop.edges 1))) *
      Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n) := by
  have hz := evenPartition_positive hw0 hw1 K width hK n
  have hpin : windowRatio hw0 hw1 K width hK n 2 n
      (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≈
      numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) *
        Q'.recipPos (evenPartition w K width n) hz :=
    Q'.eqv_trans _ _ _ (filtered_loop_windowRatio hw0 hw1 K width hK n loop 1)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (filtered_loop_numerator w K width n loop 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (filtered_loop_radial_drift_bound hw0 hw1 K width hK n loop)
      (Q'.le_of_lt (Q'.recipPos_pos _ hz)))

#print axioms mixedDensity
#print axioms mixedDensity_supported
#print axioms mixedDensity_certificate
#print axioms mixedDensity_mass
#print axioms terminalEdge_probe_pairing
#print axioms mixedDensity_window_pairing
#print axioms mixedDensity_upper_marginal
#print axioms mixedJumpSquare_noise_drift
#print axioms filtered_loop_jump_drift
#print axioms mixedRadialMoment_upper_pin
#print axioms mixed_radial_split
#print axioms mixedJumpSquare_radial_bound
#print axioms filtered_loop_radial_drift_bound
#print axioms filtered_loop_radial_drift_normalized

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift
