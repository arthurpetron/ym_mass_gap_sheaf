/-
# Upper and triangle bounds for the ORIGINAL finite temporal energy

The constructed original transfer quadratic gives the sharper bound
E_{g_n}(f) <= H[nu*f^2] at every nonnegative nome and cutoff. The positive
full edge square of f+f' and the exact two-endpoint marginal
identity give E_{g_n}(f) <= 2*H[nu*f^2]. The same positive edge form gives
E_{g_n}(f+q) <= 2*E_{g_n}(f)+2*E_{g_n}(q).

These bounds retain g_n=T^n1, both spatial endpoint factors, and the
unnormalized odd marginal nu. They control finite approximation errors;
the weaker edge proofs do not use transfer positive semidefiniteness, while
the sharper norm bound consumes its existing proof. None assumes a stationary
vacuum or supplies a coercive lower bound or continuum gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEnergyNormBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
  (edgeDensity jump jump_supported energy energy_identity edge_diagonal_identity edgeCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add lift_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle (weighted_square_add_le)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight weightedMass

private theorem norm_pin (w : Q') (K width n : Nat) (f : RatPoly) :
    weightedMass w K width
      (polyMul (polyMul (terminalMessage w K width n)
        (transferStep w K width (terminalMessage w K width n))) (polyMul f f)) ≈
      marginalPair w K width n f f := by
  rw [terminalMessage_next]
  unfold weightedMass marginalPair marginalWeight
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 3))))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 3)))
    (by decide) (fun
      | 0 => spatialWeight w K width | 1 => terminalMessage w K width n
      | 2 => terminalMessage w K width (n+1) | _ => f))

private theorem parallelogram (p q : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (polyAdd p (polyNeg q)) (polyAdd p (polyNeg q)))
        (polyMul (polyAdd p q) (polyAdd p q)))
      (polyAdd (polyAdd (polyMul p p) (polyMul q q))
        (polyAdd (polyMul p p) (polyMul q q))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))))
    (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => p | _ => q)

/-- Positivity of the ORIGINAL transfer quadratic removes the factor two.
The nome need only be nonnegative; there is no late-cutoff or stationary-source
premise in this upper bound. -/
theorem energy_le_norm (w : Q') (hw : (0 : Q') ≤ w) (K width n : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    energy w K width (terminalMessage w K width n) f ≤
      marginalPair w K width n f f := by
  let g := terminalMessage w K width n
  have hn := BF4ExactSlabFixedSpatialTransferPositive.transferStep_quadratic_nonnegative
    w hw K width (polyMul g f) (supported_polyMul (terminalMessage_supported w K width n) hf)
  unfold energy
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hn)) ?_
  exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0)
      (by decide) (fun _ => weightedMass w K width
        (polyMul (polyMul g (transferStep w K width g)) (polyMul f f))))
    (norm_pin w K width n f))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

include hw0 hw1 hK in
/-- Every supported error has energy at most twice its SAME marginal norm. -/
theorem energy_le_two_norm {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    energy w K width (terminalMessage w K width n) f ≤
      (2 : Q')*marginalPair w K width n f f := by
  let g := terminalMessage w K width n
  let e := edgeDensity w K width g
  let q := liftBoundary (N width) f
  let s := polyAdd f q
  let d := polyAdd (polyMul f f) (polyMul q q)
  have hg := terminalMessage_supported w K width n
  have C := edgeCertificate hw0 hw1 K width hK hg (terminalMessage_certificate hw0 hw1 K width hK n)
  have hsf : SupportedQuaternionBlocks (N width+N width) f :=
    fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))
  have hs := supported_add hsf (lift_supported hf (N width))
  have hpos := (C.mul (Certificate.square s hs)).haar_nonnegative
  have hdiag : quaternionHaar (N width+N width) (polyMul e d) ≈
      (2 : Q')*marginalPair w K width n f f :=
    Q'.eqv_trans _ _ _ (edge_diagonal_identity w K width hg hf)
      (Q'.mul_eqv_congr_left 2 _ _ (norm_pin w K width n f))
  have hpar :
      quaternionHaar (N width+N width) (polyMul e (polyMul (jump width f) (jump width f))) +
        quaternionHaar (N width+N width) (polyMul e (polyMul s s)) ≈
      quaternionHaar (N width+N width) (polyMul e d) +
        quaternionHaar (N width+N width) (polyMul e d) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_weighted_add (N width+N width) e _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff ((parallelogram f q).mul_left e))
        (haar_weighted_add (N width+N width) e d d))
  have he : (2 : Q')*energy w K width g f +
      quaternionHaar (N width+N width) (polyMul e (polyMul s s)) ≈
      (2 : Q')*((2 : Q')*marginalPair w K width n f f) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (energy_identity w K width hg hf) (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ hpar
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hdiag hdiag)
          (poly_identity_of_normal_eq
            (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
            (.mul (.const 2) (.mul (.const 2) (.var 0))) (by decide)
            (fun _ => marginalPair w K width n f f))))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hpos) (Q'.le_of_eqv he))
    (by decide : (0 : Q') < (2 : Q'))

private theorem jump_add (width : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (jump width (polyAdd p q)) (polyAdd (jump width p) (jump width q)) := by
  unfold jump
  rw [lift_add]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
    (by decide) (fun | 0 => p | 1 => q | 2 => liftBoundary (N width) p | _ => liftBoundary (N width) q)

include hw0 hw1 hK in
/-- Triangle bound on the same actual finite energy, with no new norm object. -/
theorem energy_add_le {f q : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hq : SupportedQuaternionBlocks (N width) q) :
    energy w K width (terminalMessage w K width n) (polyAdd f q) ≤
      (2 : Q')*energy w K width (terminalMessage w K width n) f +
        (2 : Q')*energy w K width (terminalMessage w K width n) q := by
  let g := terminalMessage w K width n
  let e := edgeDensity w K width g
  have hg := terminalMessage_supported w K width n
  have C := edgeCertificate hw0 hw1 K width hK hg (terminalMessage_certificate hw0 hw1 K width hK n)
  have hbound := weighted_square_add_le C (jump_supported width hf) (jump_supported width hq)
  have hsum := jump_add width f q
  have hleft := Q'.eqv_trans _ _ _ (energy_identity w K width hg (supported_add hf hq))
    (haar_of_coeff ((hsum.mul hsum).mul_left e))
  have hfp := Q'.eqv_symm (energy_identity w K width hg hf)
  have hqp := Q'.eqv_symm (energy_identity w K width hg hq)
  have hright := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hfp hfp) (Q'.add_eqv_congr' hqp hqp))
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
        (.add (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1))))
      (.mul (.const 2) (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1))))
      (by decide) (fun | 0 => energy w K width g f | _ => energy w K width g q))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hright)))
    (by decide : (0 : Q') < (2 : Q'))

end YMGap.Continuum.BF4ExactSlabFixedSpatialEnergyNormBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEnergyNormBound.energy_le_two_norm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEnergyNormBound.energy_le_norm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEnergyNormBound.energy_add_le
