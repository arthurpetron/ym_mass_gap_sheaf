/-
# Integrated signed score paid by the original conditional variance

Average the variance determinants of the actual positive laws C*W+d and
C*W-d. If the head marginal of d is zero, the result is exactly
C^2*det(W,f)-I(d*f)^2. No density, conditional mass, source norm or C is
inverted. The angular specialization produces the zero marginal by actual
head-Haar integration by parts. This is finite algebra, not a useful
changing-family cost, surviving-variance or physical mass-gap estimate.
-/

import YMGap.Continuum.SU2QuaternionConditionalGrussSquare
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.QuaternionHaarRelativeAngularBound

namespace YMGap.Continuum.SU2QuaternionIntegratedScoreVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant determinant_certificate)
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul cap_mul_left SquareBound)
open YMGap.Continuum.QuaternionHaarRelativeAngularBound (RelativeBound)

local notation "I" heads:arg p:arg => partialHaarHeads heads p

private theorem integral_cap (heads : Nat) (C : Q') (p : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (cap C) p)) (polyMul (cap C) (I heads p)) :=
  (partialHaarHeads_congr heads (cap_mul_left C p)).trans
    ((partialHaarHeads_smul heads C p).trans (cap_mul_left C _).symm)

private theorem plus_moment (heads : Nat) (C : Q') (W d r : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (polyAdd (polyMul (cap C) W) d) r))
      (polyAdd (polyMul (cap C) (I heads (polyMul W r))) (I heads (polyMul d r))) := by
  have he : RatPolyCoeffEqv
      (polyMul (polyAdd (polyMul (cap C) W) d) r)
      (polyAdd (polyMul (cap C) (polyMul W r)) (polyMul d r)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => cap C | 1 => W | 2 => d | _ => r)
  refine (partialHaarHeads_congr heads he).trans ?_
  rw [partialHaarHeads_add]
  exact (integral_cap heads C (polyMul W r)).add (RatPolyCoeffEqv.refl _)

private theorem minus_moment (heads : Nat) (C : Q') (W d r : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (polyAdd (polyMul (cap C) W) (polyNeg d)) r))
      (polyAdd (polyMul (cap C) (I heads (polyMul W r)))
        (polyNeg (I heads (polyMul d r)))) :=
  (plus_moment heads C W (polyNeg d) r).trans
    ((RatPolyCoeffEqv.refl _).add
      ((partialHaarHeads_congr heads
        (coeffEvalExpr_eqv_of_normalize_eq (.mul (.neg (.var 0)) (.var 1))
          (.neg (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => d | _ => r))).trans
        (partialHaarHeads_neg heads (polyMul d r))))

private theorem half_twice (p : RatPoly) :
    RatPolyCoeffEqv (polySmul HalfPow.half (polySmul 2 p)) p :=
  (RatPolyCoeffEqv.smul_assoc HalfPow.half 2 p).trans
    ((RatPolyCoeffEqv.smul_coefficient
      (by decide : Q'.eqv (HalfPow.half*2) 1) p).trans (RatPolyCoeffEqv.one_smul p))

/-- The centered signed moment is paid by the SAME conditional determinant.
The two positive tilted laws are data; C need not be positive or nonzero. -/
def centeredSignedSquare_certificate (tail heads : Nat) (W d f : RatPoly) (C : Q')
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hd : SupportedQuaternionBlocks (tail+heads) d)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (Pplus : Certificate (tail+heads) (polyAdd (polyMul (cap C) W) d))
    (Pminus : Certificate (tail+heads) (polyAdd (polyMul (cap C) W) (polyNeg d)))
    (hz : RatPolyCoeffEqv (I heads d) polyZero) :
    Certificate tail (polyAdd
      (polyMul (cap (C*C)) (determinant heads W f))
      (polyNeg (polyMul (I heads (polyMul d f)) (I heads (polyMul d f))))) := by
  let U := polyAdd (polyMul (cap C) W) d
  let V := polyAdd (polyMul (cap C) W) (polyNeg d)
  have hbase := supported_polyMul (SquareBound.constant (tail+heads) C).support hW
  have hneg : SupportedQuaternionBlocks (tail+heads) (polyNeg d) := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    exact hd r hr
  have hU := supported_add hbase hd
  have hV := supported_add hbase hneg
  let Du := determinant heads U f
  let Dv := determinant heads V f
  let PD := (determinant_certificate tail heads U f hU hf Pplus).add
    (determinant_certificate tail heads V f hV hf Pminus)
  let A := I heads W
  let b := I heads (polyMul W f)
  let e := I heads (polyMul d f)
  let H := I heads (polyMul W (polyMul f f))
  let J := I heads (polyMul d (polyMul f f))
  let p := polyAdd (polyMul (cap (C*C)) (determinant heads W f))
    (polyNeg (polyMul e e))
  have hu : RatPolyCoeffEqv (I heads U) (polyMul (cap C) A) := by
    change RatPolyCoeffEqv (I heads (polyAdd _ _)) _
    rw [partialHaarHeads_add]
    exact ((integral_cap heads C W).add hz).trans (RatPolyCoeffEqv.add_zero _)
  have hv : RatPolyCoeffEqv (I heads V) (polyMul (cap C) A) := by
    change RatPolyCoeffEqv (I heads (polyAdd _ _)) _
    rw [partialHaarHeads_add]
    exact ((integral_cap heads C W).add
      ((partialHaarHeads_neg heads d).trans (RatPolyCoeffEqv.neg hz))).trans
      (RatPolyCoeffEqv.add_zero _)
  have hDu := (hu.mul (plus_moment heads C W d (polyMul f f))).add
    (RatPolyCoeffEqv.neg ((plus_moment heads C W d f).mul (plus_moment heads C W d f)))
  have hDv := (hv.mul (minus_moment heads C W d (polyMul f f))).add
    (RatPolyCoeffEqv.neg ((minus_moment heads C W d f).mul (minus_moment heads C W d f)))
  let ca : PolyExpr := .mul (.var 0) (.var 1)
  let cb : PolyExpr := .mul (.var 0) (.var 2)
  let ch : PolyExpr := .mul (.var 0) (.var 4)
  let du : PolyExpr := .add (.mul ca (.add ch (.var 5)))
    (.neg (.mul (.add cb (.var 3)) (.add cb (.var 3))))
  let dv : PolyExpr := .add (.mul ca (.add ch (.neg (.var 5))))
    (.neg (.mul (.add cb (.neg (.var 3))) (.add cb (.neg (.var 3)))))
  let variance : PolyExpr := .add (.mul (.var 1) (.var 4))
    (.neg (.mul (.var 2) (.var 2)))
  have hring := coeffEvalExpr_eqv_of_normalize_eq (.add du dv)
    (.mul (.const 2) (.add (.mul (.mul (.var 0) (.var 0)) variance)
      (.neg (.mul (.var 3) (.var 3)))))
    (by decide) (fun | 0 => cap C | 1 => A | 2 => b | 3 => e | 4 => H | _ => J)
  have htarget := ((cap_mul C C).mul_right (determinant heads W f)).add
    (RatPolyCoeffEqv.refl (polyNeg (polyMul e e)))
  have hfinal : RatPolyCoeffEqv (polyAdd Du Dv) (polySmul 2 p) :=
    (hDu.add hDv).trans (hring.trans
      ((htarget.mul_left (cap 2)).trans (cap_mul_left 2 p)))
  exact .ofCoeff (half_twice p).symm
    (.smul HalfPow.half (by decide) (.ofCoeff hfinal.symm PD))

/-- Actual angular score in an integrated head block. The full W and f are
retained. Head integration produces the zero marginal, rather than assuming
a normalized conditional score or annihilation of f. -/
def integratedAngularScore_certificate (tail heads block i j : Nat)
    (hblock : block < heads) (hi : i < 4) (hj : j < 4)
    (W f : RatPoly) (C : Q')
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (P : RelativeBound (tail+heads) (4*block+i) (4*block+j) W C) :
    Certificate tail (polyAdd
      (polyMul (cap (C*C)) (determinant heads W f))
      (polyNeg (polyMul
        (I heads (polyMul (angularDerivative (4*block+i) (4*block+j) W) f))
        (I heads (polyMul (angularDerivative (4*block+i) (4*block+j) W) f))))) :=
  centeredSignedSquare_certificate tail heads W
    (angularDerivative (4*block+i) (4*block+j) W) f C hW
    (angularDerivative_supported_at (by omega) (by omega) hW) hf P.lower P.upper
    (partialHaarHeads_angularDerivative_at_zero hblock hi hj W)

end YMGap.Continuum.SU2QuaternionIntegratedScoreVariance

#print axioms YMGap.Continuum.SU2QuaternionIntegratedScoreVariance.centeredSignedSquare_certificate
#print axioms YMGap.Continuum.SU2QuaternionIntegratedScoreVariance.integratedAngularScore_certificate
