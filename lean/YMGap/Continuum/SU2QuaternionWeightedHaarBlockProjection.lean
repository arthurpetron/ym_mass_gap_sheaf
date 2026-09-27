/-
# Coordinate Haar projection under an independent certified background

The background retains all spectator variables. Independence is required only
of the selected block, and no interacting conditional projection is replaced.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.SU2QuaternionWeightedHaarBlockProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

local infix:50 " ≈ " => Q'.eqv

/-- The raw coordinate projection is self-adjoint for any background omitting
that coordinate, even when the background couples all other coordinates. -/
theorem weighted_project_selfAdjoint (blocks block : Nat) (hb : block < blocks)
    (W p q : RatPoly) (hW : QuaternionBlockIndependent block W) :
    weightedPair blocks W (project block p) q ≈
      weightedPair blocks W p (project block q) := by
  unfold weightedPair
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
    (Q'.eqv_trans _ _ _
      (project_selfAdjoint blocks block hb p (polyMul q W))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff ((project_mul_right_of_independent block q W hW).mul_left p))
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)))

/-- A coordinate fluctuation is orthogonal to every projected test under
the SAME certified spectator weight. -/
theorem weighted_project_fluctuation_orthogonal (blocks block : Nat)
    (hb : block < blocks) (W p q : RatPoly)
    (hW : QuaternionBlockIndependent block W) :
    weightedPair blocks W (project block p) (fluctuation block q) ≈ 0 := by
  have htest : QuaternionBlockIndependent block (polyMul (project block p) W) :=
    quaternionBlockIndependent_polyMul (project_independent block p) hW
  have hswap : RatPolyCoeffEqv
      (polyMul (polyMul (project block p) (fluctuation block q)) W)
      (polyMul (polyMul (project block p) W) (fluctuation block q)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => project block p | 1 => fluctuation block q | _ => W)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hswap)
    (fluctuation_orthogonal blocks block hb q _ htest)

private theorem weightedMoment_add (blocks : Nat) (W a b : RatPoly) :
    quaternionHaar blocks (polyMul (polyAdd a b) W) ≈
      quaternionHaar blocks (polyMul a W) + quaternionHaar blocks (polyMul b W) := by
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

/-- Exact weighted Pythagoras for an independent positive background. -/
theorem weighted_square_decomposition (blocks block : Nat) (hb : block < blocks)
    (W p : RatPoly) (hW : QuaternionBlockIndependent block W) :
    weightedPair blocks W p p ≈
      weightedPair blocks W (project block p) (project block p) +
        weightedPair blocks W (fluctuation block p) (fluctuation block p) := by
  let q := project block p
  let r := fluctuation block p
  have hc : weightedPair blocks W q r ≈ 0 :=
    weighted_project_fluctuation_orthogonal blocks block hb W p p hW
  have halg : RatPolyCoeffEqv (polyMul p p)
      (polyAdd (polyMul q q) (polyAdd (polyMul r r)
        (polyAdd (polyMul q r) (polyMul q r)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
          (.add
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1)))))))
      (by decide) (fun | 0 => p | _ => q)
  have hz : quaternionHaar blocks (polyMul (polyAdd (polyMul q r) (polyMul q r)) W) ≈ 0 :=
    Q'.eqv_trans _ _ _ (weightedMoment_add blocks W _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc hc)
        (by decide : (0 : Q') + 0 ≈ 0))
  unfold weightedPair
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (halg.mul_right W))
    (Q'.eqv_trans _ _ _ (weightedMoment_add blocks W _ _)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (weightedMoment_add blocks W _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))))))

/-- A Haar-coordinate projection contracts the quadratic form with the SAME
independent certified background; no all-volume floor enters. -/
theorem weighted_project_square_contraction (blocks block : Nat)
    (hb : block < blocks) (W p : RatPoly) (H : Certificate blocks W)
    (hW : QuaternionBlockIndependent block W)
    (hp : SupportedQuaternionBlocks blocks p) :
    weightedPair blocks W (project block p) (project block p) ≤
      weightedPair blocks W p p :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (H.square_insertion_nonnegative (fluctuation block p)
        (fluctuation_supported block hp)))
    (Q'.ge_of_eqv (weighted_square_decomposition blocks block hb W p hW))

#print axioms weighted_project_selfAdjoint
#print axioms weighted_project_fluctuation_orthogonal
#print axioms weighted_square_decomposition
#print axioms weighted_project_square_contraction

end YMGap.Continuum.SU2QuaternionWeightedHaarBlockProjection
