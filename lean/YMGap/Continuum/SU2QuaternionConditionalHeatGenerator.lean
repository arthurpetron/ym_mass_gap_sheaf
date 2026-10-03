/-
# Formal nome generator at the ORIGINAL retained conditional boundary

Actual packet coefficients are finite QPoly rows. Their literal pderiv,
integrated against the original input, generates its INPUT angular Laplacian.
The output y and every shared spectator remain in the coefficients of p(x,y,z).
No output-Laplacian identity, saturation, positivity or source independence is
assumed. This is the outer-generator algebra for finite Laurent interpolation;
it asserts no conditional variance or changing-family estimate.
-/

import YMGap.Continuum.SU2QuaternionConditionalHeatComposition
import YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
import YMGap.Continuum.SU2QuaternionHeadHeatGenerator

namespace YMGap.Continuum.SU2QuaternionConditionalHeatGenerator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower coordinate)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow dimQ c4)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.SU2CharacterVacuumHaar (coeffAt)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (HasQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini (partialHaarHead)
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (head_pairing)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator (nome_power_generator)
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv

/-- The actual dimension times the monomial nome coefficient of label spin. -/
def nomeCoefficient (spin : Nat) : Poly :=
  pscale (dimQ spin) (polynomialPower coordinate (c4 spin))

/-- All original packet rows, including zero and the inclusive cutoff. -/
def conditionalHeatNomePolynomial (K : Nat) : List (Poly × RatPoly) :=
  (List.range (K+1)).map fun spin => (nomeCoefficient spin, relativeCharacter spin)

def finiteConditionalKernel (w : Q') (K : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (QPoly.eval (nomeCoefficient spin) w)
    (relativeCharacter spin)) (List.range (K+1))

/-- Literal formal differentiation of the original finite kernel coefficients. -/
def formalConditionalKernelDerivative (w : Q') (K : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (QPoly.eval (pderiv (nomeCoefficient spin)) w)
    (relativeCharacter spin)) (List.range (K+1))

def finiteConditionalHeat (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  partialHaarHead (polyMul (finiteConditionalKernel w K) p)

/-- Only the integrated head is removed, not the already-existing output. -/
def formalConditionalNomeDerivative (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  partialHaarHead (polyMul (formalConditionalKernelDerivative w K) p)

private theorem coordinate_eval (w : Q') : QPoly.eval coordinate w ≈ w :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => w)

private theorem power_eval (w : Q') : ∀ n : Nat,
    QPoly.eval (polynomialPower coordinate n) w ≈ qpow w n
  | 0 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ 0 (Q'.mul_zero_eqv w)) (q_add_zero_eqv 1)
  | n+1 => Q'.eqv_trans _ _ _ (eval_pmul coordinate (polynomialPower coordinate n) w)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ w _ (coordinate_eval w))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ (power_eval w n))
          (Q'.mul_comm_eqv w (qpow w n))))

private theorem coefficient_eval_pin (w : Q') (spin : Nat) :
    QPoly.eval (nomeCoefficient spin) w ≈ coeffW w spin :=
  Q'.eqv_trans _ _ _ (eval_pscale (dimQ spin) _ w)
    (Q'.mul_eqv_congr_left (dimQ spin) _ _ (power_eval w (c4 spin)))

/-- Exact original packet identification, before any Haar quotient. -/
theorem finiteConditionalKernel_original_pin (w : Q') (K : Nat) :
    RatPolyCoeffEqv (finiteConditionalKernel w K) (relativeHeat w K) := by
  have hsum : ∀ ids : List Nat, (∀ spin, spin ∈ ids → spin < K+1) →
      RatPolyCoeffEqv
        (finitePolySum (fun spin => polySmul (QPoly.eval (nomeCoefficient spin) w)
          (relativeCharacter spin)) ids)
        (finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
          (relativeCharacter spin)) ids) := by
    intro ids
    induction ids with
    | nil => intro _; exact .refl _
    | cons spin ids ih =>
        intro hids
        have hs := coeffAt_heatKernelPacket (w := w) (hids spin List.mem_cons_self)
        exact (RatPolyCoeffEqv.smul_coefficient
          (Q'.eqv_trans _ _ _ (coefficient_eval_pin w spin) (Q'.eqv_of_eq hs.symm)) _).add
          (ih (fun j hj => hids j (List.mem_cons_of_mem spin hj)))
  exact hsum (List.range (K+1)) (fun _ h => List.mem_range.mp h)

theorem finiteConditionalHeat_original_pin (w : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (finiteConditionalHeat w K p) (conditionalHeat w K p) :=
  partialHaarHead_congr ((finiteConditionalKernel_original_pin w K).mul_right p)

private theorem coefficient_euler (w : Q') (spin : Nat) :
    w * QPoly.eval (pderiv (nomeCoefficient spin)) w ≈
      Q'.ofNat (c4 spin) * QPoly.eval (nomeCoefficient spin) w := by
  have hd := Q'.eqv_trans _ _ _
    (coefficient_eval (pderiv_pscale (dimQ spin) (polynomialPower coordinate (c4 spin))) w)
    (eval_pscale (dimQ spin) _ w)
  have hs : w * (dimQ spin * QPoly.eval (pderiv (polynomialPower coordinate (c4 spin))) w) ≈
      dimQ spin * (w * QPoly.eval (pderiv (polynomialPower coordinate (c4 spin))) w) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => w | 1 => dimQ spin | _ => QPoly.eval (pderiv (polynomialPower coordinate (c4 spin))) w)
  have hr : dimQ spin * (Q'.ofNat (c4 spin) * qpow w (c4 spin)) ≈
      Q'.ofNat (c4 spin) * coeffW w spin :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => dimQ spin | 1 => Q'.ofNat (c4 spin) | _ => qpow w (c4 spin))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ hd)
    (Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (nome_power_generator w (c4 spin)))
      (Q'.eqv_trans _ _ _ hr
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (coefficient_eval_pin w spin))))))

private theorem casimir_nat (spin : Nat) :
    Q'.ofNat (c4 spin) ≈ Q'.ofNat spin * (Q'.ofNat spin+2) :=
  Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv spin (spin+2))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv spin 2)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))))

private theorem term_generator (blocks : Nat) (hb : 1 < blocks) (w : Q') (spin : Nat) :
    HaarCarrierEqv blocks
      (polySmul w (polySmul (QPoly.eval (pderiv (nomeCoefficient spin)) w) (relativeCharacter spin)))
      (polySmul (-1) (angularLaplacian
        (polySmul (QPoly.eval (nomeCoefficient spin) w) (relativeCharacter spin)))) := by
  let a := QPoly.eval (nomeCoefficient spin) w
  let e := Q'.ofNat spin * (Q'.ofNat spin+2)
  have hl : RatPolyCoeffEqv
      (polySmul w (polySmul (QPoly.eval (pderiv (nomeCoefficient spin)) w) (relativeCharacter spin)))
      (polySmul (Q'.ofNat (c4 spin)*a) (relativeCharacter spin)) :=
    (RatPolyCoeffEqv.smul_assoc _ _ _).trans
      (RatPolyCoeffEqv.smul_coefficient (coefficient_euler w spin) _)
  have hr := (RatPolyCoeffEqv.haarCarrier (angularLaplacian_smul a (relativeCharacter spin))).trans
    (HaarCarrierEqv.smul a (relativeCharacter_angularCasimir blocks spin hb))
  have hscalar : (-1)*(a*(-e)) ≈ Q'.ofNat (c4 spin)*a :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.mul (.var 0) (.neg (.var 1))))
        (.mul (.var 1) (.var 0)) (by decide) (fun | 0 => a | _ => e))
      (Q'.mul_eqv_congr_right _ _ a (Q'.eqv_symm (casimir_nat spin)))
  have hr' : HaarCarrierEqv blocks
      (polySmul (-1) (angularLaplacian (polySmul a (relativeCharacter spin))))
      (polySmul (Q'.ofNat (c4 spin)*a) (relativeCharacter spin)) :=
    (HaarCarrierEqv.smul (-1) hr).trans
      (RatPolyCoeffEqv.haarCarrier
        (((RatPolyCoeffEqv.smul_assoc a (-e) _).smul (-1)).trans
          ((RatPolyCoeffEqv.smul_assoc (-1) (a*(-e)) _).trans
            (RatPolyCoeffEqv.smul_coefficient hscalar _))))
  exact (RatPolyCoeffEqv.haarCarrier hl).trans hr'.symm

/-- The literal derivative of every finite packet, including omitted modes.
No nome or cutoff premise is needed; the carrier contains both kernel blocks. -/
theorem conditionalKernel_formal_nome_generator (blocks : Nat) (hb : 1 < blocks)
    (w : Q') (K : Nat) :
    HaarCarrierEqv blocks (polySmul w (formalConditionalKernelDerivative w K))
      (polySmul (-1) (angularLaplacian (finiteConditionalKernel w K))) := by
  have hsum : ∀ ids : List Nat, HaarCarrierEqv blocks
      (polySmul w (finitePolySum (fun spin =>
        polySmul (QPoly.eval (pderiv (nomeCoefficient spin)) w) (relativeCharacter spin)) ids))
      (polySmul (-1) (angularLaplacian (finitePolySum (fun spin =>
        polySmul (QPoly.eval (nomeCoefficient spin) w) (relativeCharacter spin)) ids))) := by
    intro ids
    induction ids with
    | nil =>
        change HaarCarrierEqv blocks (polySmul w polyZero) (polySmul (-1) polyZero)
        exact RatPolyCoeffEqv.haarCarrier
          ((RatPolyCoeffEqv.smul_zero w).trans (RatPolyCoeffEqv.smul_zero (-1)).symm)
    | cons spin ids ih =>
        exact (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_add w _ _)).trans
          ((HaarCarrierEqv.add (term_generator blocks hb w spin) ih).trans
            (RatPolyCoeffEqv.haarCarrier
              (((angularLaplacian_add _ _).smul (-1)).trans
                (RatPolyCoeffEqv.smul_add (-1) _ _))).symm)
  exact hsum (List.range (K+1))

private theorem partial_pairing (tail : Nat) (p boundary : RatPoly) :
    quaternionHaar tail (polyMul boundary (partialHaarHead p)) ≈
      quaternionHaar (tail+1) (polyMul p (liftHead boundary)) := by
  have h := head_pairing tail 1 p boundary
  simpa only [partialHaarHeads, liftBoundary, Nat.add_zero] using
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm boundary (partialHaarHead p)))
      (Q'.eqv_symm h)

private theorem derivative_mul_lift (i j : Nat) (hi : i < 4) (hj : j < 4)
    (p boundary : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (polyMul p (liftHead boundary)))
      (polyMul (angularDerivative i j p) (liftHead boundary)) := by
  have hboundary : HasQuaternionBlockDegree 0 0 (liftHead boundary) := by
    intro term hterm
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hterm
    rfl
  exact (angularDerivative_mul i j p (liftHead boundary)).trans
    (((RatPolyCoeffEqv.refl _).add
      (((angularDerivative_independent_zero hi hj _ hboundary).mul_left p).trans
        (RatPolyCoeffEqv.mul_zero_right p))).trans (RatPolyCoeffEqv.add_zero _))

private theorem second_mul_lift (i j : Nat) (hi : i < 4) (hj : j < 4)
    (p boundary : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polyMul p (liftHead boundary))))
      (polyMul (angularDerivative i j (angularDerivative i j p)) (liftHead boundary)) :=
  (angularDerivative_congr i j (derivative_mul_lift i j hi hj p boundary)).trans
    (derivative_mul_lift i j hi hj (angularDerivative i j p) boundary)

private theorem second_pair (tail i j : Nat) (hi : i < 4) (hj : j < 4)
    (p q : RatPoly) :
    quaternionHaar (tail+1) (polyMul p (angularDerivative i j (angularDerivative i j q))) ≈
      quaternionHaar (tail+1) (polyMul q (angularDerivative i j (angularDerivative i j p))) := by
  have hp := angular_pair tail hi hj p (angularDerivative i j q)
  have hq := angular_pair tail hi hj (angularDerivative i j p) q
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hq)
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.neg (.neg (.var 0))) (.var 0) (by decide)
          (fun _ => quaternionHaar (tail+1)
            (polyMul (angularDerivative i j (angularDerivative i j p)) q)))
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

private theorem laplacian_input_swap (tail : Nat) (kernel p : RatPoly) :
    HaarCarrierEqv tail
      (partialHaarHead (polyMul (angularLaplacian kernel) p))
      (partialHaarHead (polyMul kernel (angularLaplacian p))) := by
  intro boundary
  have hleft : RatPolyCoeffEqv
      (polyMul (polyMul (angularLaplacian kernel) p) (liftHead boundary))
      (polyMul (polyMul p (liftHead boundary)) (angularLaplacian kernel)) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).trans (RatPolyCoeffEqv.mul_comm _ _)
  have hplane (i j : Nat) (hi : i < 4) (hj : j < 4) :
      quaternionHaar (tail+1) (polyMul (polyMul p (liftHead boundary))
        (angularDerivative i j (angularDerivative i j kernel))) ≈
      quaternionHaar (tail+1) (polyMul (polyMul kernel
        (angularDerivative i j (angularDerivative i j p))) (liftHead boundary)) :=
    Q'.eqv_trans _ _ _ (second_pair tail i j hi hj (polyMul p (liftHead boundary)) kernel)
      (Q'.eqv_trans _ _ _
        (haar_of_coeff ((second_mul_lift i j hi hj p boundary).mul_left kernel))
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm))
  have hright : RatPolyCoeffEqv
      (polyMul (polyMul kernel (angularLaplacian p)) (liftHead boundary))
      (polyMul (polyMul (liftHead boundary) kernel) (angularLaplacian p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => kernel | 1 => angularLaplacian p | _ => liftHead boundary)
  have hs : quaternionHaar (tail+1) (polyMul (polyMul p (liftHead boundary))
        (angularLaplacian kernel)) ≈
      quaternionHaar (tail+1) (polyMul (polyMul (liftHead boundary) kernel)
        (angularLaplacian p)) :=
    Q'.eqv_trans _ _ _ (haar_six (tail+1) (polyMul p (liftHead boundary)) _)
      (Q'.eqv_trans _ _ _
        (sixValue_congr _ _ (fun i j hi hj => Q'.eqv_trans _ _ _ (hplane i j hi hj)
          (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 1)) (.var 2))
            (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
            (fun | 0 => kernel | 1 => angularDerivative i j (angularDerivative i j p)
                 | _ => liftHead boundary)))))
        (Q'.eqv_symm (haar_six (tail+1) (polyMul (liftHead boundary) kernel) _)))
  exact Q'.eqv_trans _ _ _ (partial_pairing tail _ boundary)
    (Q'.eqv_trans _ _ _ (haar_of_coeff hleft)
      (Q'.eqv_trans _ _ _ hs
        (Q'.eqv_trans _ _ _ (haar_of_coeff hright.symm)
          (Q'.eqv_symm (partial_pairing tail _ boundary)))))

/-- Literal conditional formal nome differentiation acts on the integrated
INPUT. Arbitrary output-dependent coefficients and insertions are retained. -/
theorem conditionalHeat_formal_nome_generator (tail : Nat) (ht : 0 < tail)
    (w : Q') (K : Nat) (p : RatPoly) :
    HaarCarrierEqv tail (polySmul w (formalConditionalNomeDerivative w K p))
      (conditionalHeat w K (polyNeg (angularLaplacian p))) := by
  have hscale : RatPolyCoeffEqv
      (polySmul w (formalConditionalNomeDerivative w K p))
      (partialHaarHead (polyMul (polySmul w (formalConditionalKernelDerivative w K)) p)) :=
    (partialHaarHead_smul w (polyMul (formalConditionalKernelDerivative w K) p)).symm.trans
      (partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_left _ _ _).symm)
  have hk := partialHaarHead_carrier
    (HaarCarrierEqv.mul_right p
      (conditionalKernel_formal_nome_generator (tail+1) (by omega) w K))
  have hs : RatPolyCoeffEqv
      (partialHaarHead (polyMul (polySmul (-1) (angularLaplacian (finiteConditionalKernel w K))) p))
      (polySmul (-1) (partialHaarHead (polyMul (angularLaplacian (finiteConditionalKernel w K)) p))) :=
    (partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_left _ _ _)).trans
      (partialHaarHead_smul (-1) _)
  have hswap := HaarCarrierEqv.smul (-1) (laplacian_input_swap tail (finiteConditionalKernel w K) p)
  have hfinish : RatPolyCoeffEqv
      (polySmul (-1) (partialHaarHead (polyMul (finiteConditionalKernel w K) (angularLaplacian p))))
      (conditionalHeat w K (polyNeg (angularLaplacian p))) :=
    (partialHaarHead_smul (-1) _).symm.trans
      ((partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_right _ _ _).symm).trans
        ((partialHaarHead_congr ((neg_smul _).symm.mul_left _)).trans
          (partialHaarHead_congr ((finiteConditionalKernel_original_pin w K).mul_right _))))
  exact (RatPolyCoeffEqv.haarCarrier hscale).trans
    (hk.trans ((RatPolyCoeffEqv.haarCarrier hs).trans
      (hswap.trans (RatPolyCoeffEqv.haarCarrier hfinish))))

#print axioms nomeCoefficient
#print axioms conditionalHeatNomePolynomial
#print axioms finiteConditionalKernel
#print axioms formalConditionalKernelDerivative
#print axioms finiteConditionalHeat
#print axioms formalConditionalNomeDerivative
#print axioms finiteConditionalKernel_original_pin
#print axioms finiteConditionalHeat_original_pin
#print axioms conditionalKernel_formal_nome_generator
#print axioms conditionalHeat_formal_nome_generator

end YMGap.Continuum.SU2QuaternionConditionalHeatGenerator
