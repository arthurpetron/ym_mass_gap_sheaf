/-
# Continuity of the ORIGINAL transfer in its SAME spatially weighted form

The positive original edge energy at g=1 bounds the transfer quadratic by
H[V*(T1)*f^2]. The existing kinetic cap certificate then bounds this by
C*H[V*f^2], where C=kineticCap*H[V]. Product-heat Cauchy--Schwarz gives the
mixed bound with the same V at both ends. No spatial floor, comparison to an
unweighted norm, stationary state or changed action is used.

These are finite late-cutoff continuity bounds. C retains its nome, width
and cutoff dependence; this is NOT a coercive estimate or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy energy_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight weightedMass

/-- The original rank-one cap times the SAME spatial mass. -/
def transferWeightedCap (w : Q') (K width : Nat) : Q' :=
  kineticCap w width * weightedMass w K width polyOne

theorem transferWeightedCap_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) : (0 : Q') ≤ transferWeightedCap w K width :=
  Q'.mul_nonneg _ _ (kineticCap_nonnegative hw0 width)
    (weightedMass_nonnegative hw0 hw1 K width hK (Certificate.one _))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem kinetic_pin (w : Q') (K width : Nat) (f g : RatPoly) :
    weightedMass w K width (polyMul f (transferStep w K width g)) ≈
      kineticPair (N width) w K (activeBlocks width)
        (polyMul (spatialWeight w K width) f) (polyMul (spatialWeight w K width) g) := by
  rw [transferStep_eq_productMap]
  unfold weightedMass kineticPair
  exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm

/-- Cauchy--Schwarz for the literal interacting transfer quadratic. -/
theorem transferStep_weighted_cauchySchwarz (w : Q') (hw : (0 : Q') ≤ w)
    (K width : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    let B := fun p q => weightedMass w K width (polyMul p (transferStep w K width q))
    B f g * B f g ≤ B f f * B g g := by
  dsimp only
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (qmul (kinetic_pin w K width f g) (kinetic_pin w K width f g)))
    (Q'.le_trans' _ _ _
      (kineticPair_cauchySchwarz (N width) w hw K (activeBlocks width) (activeBlocks_lt width)
        _ _ (supported_polyMul (spatialWeight_supported w K width) hf)
        (supported_polyMul (spatialWeight_supported w K width) hg))
      (Q'.ge_of_eqv (qmul (kinetic_pin w K width f f) (kinetic_pin w K width g g))))

private theorem diagonal_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    weightedMass w K width
        (polyMul (transferStep w K width polyOne) (polyMul f f)) ≤
      transferWeightedCap w K width * weightedMass w K width (polyMul f f) := by
  let c := transferWeightedCap w K width
  let t := transferStep w K width polyOne
  let sq := polyMul f f
  have C := transferStepUpperCertificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  have hn := weightedMass_nonnegative hw0 hw1 K width hK
    (C.mul (Certificate.square f hf))
  have he : weightedMass w K width (polyMul (polyAdd (cap c) (polyNeg t)) sq) ≈
      c * weightedMass w K width sq + -(weightedMass w K width (polyMul t sq)) :=
    Q'.eqv_trans _ _ _
      (weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => cap c | 1 => t | _ => sq)))
      (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (weightedMass_congr w K width (cap_mul_left c sq))
            (weightedMass_smul w K width c sq))
          (Q'.eqv_trans _ _ _
            (weightedMass_congr w K width
              (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul _))
            (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) _)
              (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
                (by decide) (fun _ => weightedMass w K width (polyMul t sq)))))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- The SAME V-weighted quadratic ceiling follows from the original edge square. -/
theorem transferStep_weighted_quadratic_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    weightedMass w K width (polyMul f (transferStep w K width f)) ≤
      transferWeightedCap w K width * weightedMass w K width (polyMul f f) := by
  have hn := energy_nonnegative hw0 hw1 K width hK (supported_one (N width)) hf
    (Certificate.one (N width))
  have hdiag := (RatPolyCoeffEqv.one_mul (transferStep w K width polyOne)).mul_right (polyMul f f)
  have hmix := (RatPolyCoeffEqv.one_mul f).mul
    (transfer_congr w K width (RatPolyCoeffEqv.one_mul f))
  have he : energy w K width polyOne f ≈
      weightedMass w K width (polyMul (transferStep w K width polyOne) (polyMul f f)) +
        -(weightedMass w K width (polyMul f (transferStep w K width f))) :=
    Q'.add_eqv_congr' (weightedMass_congr w K width hdiag)
      (Q'.neg_eqv_congr _ _ (weightedMass_congr w K width hmix))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he)))
    (diagonal_cap hw0 hw1 K width hK hf)

/-- Finite mixed continuity with all original spatial factors retained. -/
theorem transferStep_weighted_mixed_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    {f g : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    let x := weightedMass w K width (polyMul f (transferStep w K width g))
    x*x ≤ (transferWeightedCap w K width * transferWeightedCap w K width) *
      (weightedMass w K width (polyMul f f) * weightedMass w K width (polyMul g g)) := by
  dsimp only
  have hff := transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width f hf
  have hgg := transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width g hg
  have hfc := transferStep_weighted_quadratic_le hw0 hw1 K width hK hf
  have hgc := transferStep_weighted_quadratic_le hw0 hw1 K width hK hg
  have hfn := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square f hf)
  have hcn := transferWeightedCap_nonnegative hw0 hw1 K width hK
  exact Q'.le_trans' _ _ _
    (transferStep_weighted_cauchySchwarz w (Q'.le_of_lt hw0) K width hf hg)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hfc hgg)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hgc (Q'.mul_nonneg _ _ hcn hfn))
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (by decide)
          (fun
            | 0 => transferWeightedCap w K width
            | 1 => weightedMass w K width (polyMul f f)
            | _ => weightedMass w K width (polyMul g g))))))

/-- Sharp Cauchy--Schwarz for the same spatially weighted norm. -/
theorem weightedMass_pair_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    {f g : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    let B := fun p q => weightedMass w K width (polyMul p q)
    B f g * B f g ≤ B f f * B g g := by
  dsimp only
  have pin (p q : RatPoly) : weightedPair (N width) (spatialWeight w K width) p q ≈
      weightedMass w K width (polyMul p q) := by
    unfold weightedPair weightedMass
    exact haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul (pin f g) (pin f g)))
    (Q'.le_trans' _ _ _ (weighted_cauchySchwarz (N width) (spatialWeight w K width) f g
      (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK) hf hg)
      (Q'.le_of_eqv (qmul (pin f f) (pin g g))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound.transferWeightedCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound.transferWeightedCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound.transferStep_weighted_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound.transferStep_weighted_quadratic_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound.transferStep_weighted_mixed_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound.weightedMass_pair_square_le
