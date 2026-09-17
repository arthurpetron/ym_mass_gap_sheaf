/-
# Polynomial dual tests in the original temporal marginal

For a=V*T^n1, t=T^(n+1)1, nu=a*t, and the actual erased message d,
the independent polynomial reciprocal G_k gives r_k=t*q*G_k.
Exact conditional centering P_i(nu*q)=0 supplies P_i(a*r_k)=0.
The norm budget follows from the single positive polynomial identity
  U*a*t*q^2-a*d*(t*q*G_k)^2
    = a*d*t*(q*G_k)^2*(U*d-t)
      + U*a*t*q^2*(1-(d*G_k)^2).
No positivity of q or G_k, nor independence of V or t, is assumed.
The pairing error has an explicit geometric bound. Rational order closure
then proves h*H[nu*f*q]^2 <= U*energy(T^n1,f)*H[nu*q^2]. The reference
weight is nu, not the erased marginal a*d. A collective spatial budget and the
continuum/physical-mass/every-group joins remain separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse
import YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Constructive.CRealExp
import YMGap.Constructive.RegularCReal

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse
open YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy energy_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_sub (blocks : Nat) (p q : RatPoly) :
    quaternionHaar blocks (polyAdd p (polyNeg q)) ≈ quaternionHaar blocks p + -(quaternionHaar blocks q) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append blocks p (polyNeg q))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks q))

/-- The literal original odd-edge marginal, not an auxiliary measure. -/
def marginalWeight (w : Q') (K width n : Nat) : RatPoly :=
  polyMul (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (terminalMessage w K width (n+1))

def marginalPair (w : Q') (K width n : Nat) (f q : RatPoly) : Q' :=
  quaternionHaar (N width) (polyMul (marginalWeight w K width n) (polyMul f q))

theorem marginalWeight_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width) (marginalWeight w K width n) :=
  supported_polyMul (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
    (terminalMessage_supported w K width (n+1))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n i : Nat) (hi : i ∈ activeBlocks width)

def marginalCertificate : Certificate (N width) (marginalWeight w K width n) :=
  ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)).mul
    (terminalMessage_certificate hw0 hw1 K width hK (n+1))

private def erasedCertificate : Certificate (N width) (conditionalMessage w K width n i) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => conditionalMessage w K width n i | _ => cap (lower hw0 hw1 K width n)))
    ((lowerCertificate hw0 hw1 K width hK n i hi).add
      (Certificate.constant (N width) _ (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n))))

/-- Bounded polynomial dual test, not a claimed exact inverse state. -/
def dualTest (q : RatPoly) (k : Nat) : RatPoly :=
  polyMul (polyMul (terminalMessage w K width (n+1)) q) (reciprocal hw0 hw1 K width hK n i k)

theorem dualTest_supported {q : RatPoly} (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    SupportedQuaternionBlocks (N width) (dualTest hw0 hw1 K width hK n i q k) :=
  supported_polyMul (supported_polyMul (terminalMessage_supported w K width (n+1)) hq)
    (reciprocal_supported hw0 hw1 K width hK n i k)

include hi in
theorem dualTest_centered {q : RatPoly}
    (hc : RatPolyCoeffEqv (project i (polyMul (marginalWeight w K width n) q)) polyZero) (k : Nat) :
    RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n))
      (dualTest hw0 hw1 K width hK n i q k))) polyZero := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let t := terminalMessage w K width (n+1)
  let G := reciprocal hw0 hw1 K width hK n i k
  exact (project_congr i (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (by decide)
    (fun | 0 => a | 1 => t | 2 => q | _ => G))).trans
    ((project_mul_right_of_independent i _ G (reciprocal_independent hw0 hw1 K width hK n i hi k)).trans
      ((hc.mul_right G).trans (RatPolyCoeffEqv.mul_zero_left G)))

/-- A single sum of positive products controls the norm in the SAME marginal. -/
def dualTestNormCertificate {q : RatPoly} (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    Certificate (N width) (polyAdd
      (polySmul (prefixCap w) (polyMul (marginalWeight w K width n) (polyMul q q)))
      (polyNeg (polyMul
        (polyMul (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (conditionalMessage w K width n i))
        (polyMul (dualTest hw0 hw1 K width hK n i q k) (dualTest hw0 hw1 K width hK n i q k))))) := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let d := conditionalMessage w K width n i
  let t := terminalMessage w K width (n+1)
  let G := reciprocal hw0 hw1 K width hK n i k
  let U := prefixCap w
  have A : Certificate (N width) a :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK n)
  have T := terminalMessage_certificate hw0 hw1 K width hK (n+1)
  have D := erasedCertificate hw0 hw1 K width hK n i hi
  have Q := Certificate.square q hq
  have qG := Certificate.square (polyMul q G) (supported_polyMul hq (reciprocal_supported hw0 hw1 K width hK n i k))
  have B : Certificate (N width) (polyAdd (polyMul (cap U) d) (polyNeg t)) :=
    .ofCoeff ((cap_mul_left U d).add (.refl _)) (conditionalMessage_capCertificate hw0 hw1 K width hK n i hi)
  have C := multiplierSquareCertificate hw0 hw1 K width hK n i hi k
  have S := ((((A.mul D).mul T).mul qG).mul B).add
    (((Certificate.constant (N width) U (prefixCap_nonnegative hw0)).mul ((A.mul T).mul Q)).mul C)
  exact .ofCoeff (((cap_mul_left U _).symm.add (.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 5) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 3))))
        (.neg (.mul (.mul (.var 0) (.var 1))
          (.mul (.mul (.mul (.var 2) (.var 3)) (.var 4)) (.mul (.mul (.var 2) (.var 3)) (.var 4))))))
      (.add
        (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))
          (.add (.mul (.var 5) (.var 1)) (.neg (.var 2))))
        (.mul (.mul (.var 5) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 3))))
          (.add (.const 1) (.neg (.mul (.mul (.var 1) (.var 4)) (.mul (.var 1) (.var 4)))))))
      (by decide) (fun | 0 => a | 1 => d | 2 => t | 3 => q | 4 => G | _ => cap U))) S

include hi in
theorem dualTest_norm_bound {q : RatPoly} (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    erasedPair w K width n i (dualTest hw0 hw1 K width hK n i q k) (dualTest hw0 hw1 K width hK n i q k) ≤
      prefixCap w * marginalPair w K width n q q := by
  have H := (dualTestNormCertificate hw0 hw1 K width hK n i hi hq k).haar_nonnegative
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ H (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (haar_sub (N width) _ _)
      (Q'.add_eqv_congr' (quaternionHaar_polySmul _ _ _) (Q'.eqv_refl _)))))

include hi in
/-- The original energy of f controls every approximating dual test with
only one upper heat constant. No inverse cap survives in this coefficient. -/
theorem approximate_dual_energy {f q : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hq : SupportedQuaternionBlocks (N width) q)
    (hc : RatPolyCoeffEqv (project i (polyMul (marginalWeight w K width n) q)) polyZero) (k : Nat) :
    let L := erasedPair w K width n i f (dualTest hw0 hw1 K width hK n i q k)
    headFloor w * (L*L) ≤ prefixCap w * energy w K width (terminalMessage w K width n) f * marginalPair w K width n q q := by
  have H := terminal_dual_energy hw0 hw1 K width hK n i hi hf
    (dualTest_supported hw0 hw1 K width hK n i hq k) (dualTest_centered hw0 hw1 K width hK n i hi hc k)
  have hE := energy_nonnegative hw0 hw1 K width hK (terminalMessage_supported w K width n) hf
    (terminalMessage_certificate hw0 hw1 K width hK n)
  exact Q'.le_trans' _ _ _ H
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (dualTest_norm_bound hw0 hw1 K width hK n i hi hq k) hE)
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
        (fun | 0 => energy w K width (terminalMessage w K width n) f | 1 => prefixCap w | _ => marginalPair w K width n q q))))

/-- Explicit amplitude for the scalar pairing error; it need not be uniform. -/
def pairingErrorCap (w : Q') (K width n : Nat) (f q : RatPoly) : Q' :=
  polynomialCap (polyMul f q) * quaternionHaar (N width) (marginalWeight w K width n)

include hw0 hw1 hK in
theorem pairingErrorCap_nonnegative (f q : RatPoly) : (0 : Q') ≤ pairingErrorCap w K width n f q :=
  Q'.mul_nonneg _ _ (polynomialCap_nonnegative _) (marginalCertificate hw0 hw1 K width hK n).haar_nonnegative

include hi in
theorem dualTest_pairing_error {f q : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    Q'.abs (erasedPair w K width n i f (dualTest hw0 hw1 K width hK n i q k) + -(marginalPair w K width n f q)) ≤
      (radius hw0 hw1 K width hK n)^k * pairingErrorCap w K width n f q := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let d := conditionalMessage w K width n i
  let t := terminalMessage w K width (n+1)
  let G := reciprocal hw0 hw1 K width hK n i k
  have he : erasedPair w K width n i f (dualTest hw0 hw1 K width hK n i q k) + -(marginalPair w K width n f q) ≈
      quaternionHaar (N width) (polyMul (marginalWeight w K width n)
        (polyMul (polyMul f q) (polyAdd (polyMul d G) (polyNeg polyOne)))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_sub (N width) _ _))
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.mul (.mul (.var 2) (.var 4)) (.var 5))))
          (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 4)))))
        (.mul (.mul (.var 0) (.var 2))
          (.mul (.mul (.var 3) (.var 4)) (.add (.mul (.var 1) (.var 5)) (.neg (.const 1)))))
        (by decide) (fun | 0 => a | 1 => d | 2 => t | 3 => f | 4 => q | _ => G)))
  have H := ((polynomialInterval (N width) (polyMul f q) (supported_polyMul hf hq)).mul
    (multiplierErrorInterval hw0 hw1 K width hK n i hi k)).weighted_haar_bound (marginalCertificate hw0 hw1 K width hK n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ H (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun
        | 0 => polynomialCap (polyMul f q)
        | 1 => (radius hw0 hw1 K width hK n)^k
        | _ => quaternionHaar (N width) (marginalWeight w K width n)))))

private theorem geometric_square_closed (h L D B r : Q') (x : Nat → Q')
    (hh : (0 : Q') ≤ h) (hB : (0 : Q') ≤ B) (hr : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (hx : ∀ k, Q'.abs (x k + -L) ≤ r^k*B) (hD : ∀ k, h*(x k*x k) ≤ D) :
    h*(L*L) ≤ D := by
  let S := (Q'.abs L+B)+Q'.abs L
  let C := (h*B)*S
  have hS : (0 : Q') ≤ S := Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (Q'.abs_nonneg L) hB) (Q'.abs_nonneg L)
  have hC : (0 : Q') ≤ C := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hh hB) hS
  have happrox : ∀ k : Nat, h*(L*L) ≤ D+r^k*C := by
    intro k
    have hpow := HKPos.pow_le_one hr (Q'.le_of_lt hr1) k
    have hsmall : Q'.abs (x k + -L) ≤ B := Q'.le_trans' _ _ _ (hx k)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hB) (Q'.le_of_eqv (Q'.one_mul_eqv B)))
    have hxx : Q'.abs (x k) ≤ Q'.abs L+B :=
      Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub (x k) L) (Q'.add_le_add_left _ _ _ hsmall)
    have hsum : Q'.abs (x k+L) ≤ S :=
      Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add_right _ _ _ hxx)
    have he : x k*x k + -(L*L) ≈ (x k + -L)*(x k+L) :=
      poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1))) (by decide)
        (fun | 0 => x k | _ => L)
    have hsq : Q'.abs (x k*x k + -(L*L)) ≤ (r^k*B)*S :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.mul_le_mul_of_nonneg (hx k) hsum
            (Q'.mul_nonneg _ _ (Q'.pow_nonneg r hr k) hB) (Q'.abs_nonneg _)))
    have hs := ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ExpNeg.abs_sub_comm _ _)) hsq)
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ h hs hh
    have heq : h*(x k*x k+(r^k*B)*S) ≈ h*(x k*x k)+r^k*C :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.var 1) (.mul (.mul (.var 2) (.var 3)) (.var 4))))
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.mul (.var 0) (.var 3)) (.var 4))))
        (by decide) (fun | 0 => h | 1 => x k*x k | 2 => r^k | 3 => B | _ => S)
    exact Q'.le_trans' _ _ _ hm
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.add_le_add_right _ _ _ (hD k)))
  refine Q'.le_of_le_add_mul_invSucc _ _ 1 ?_
  intro precision
  let k := PositiveContractionResidual.geometricCutoff r C (Q'.invSucc precision)
  have he := PositiveContractionResidual.geometric_bound hr hr1 hC (Q'.invSucc_pos precision) k (Nat.le_refl k)
  exact Q'.le_trans' _ _ _ (happrox k)
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ he (Q'.ge_of_eqv (Q'.one_mul_eqv _))))

include hw0 hw1 hK hi in
/-- The local dual estimate on the SAME original odd marginal. Its coefficient
depends on nome but has no cutoff/width/depth power. Conditional centering is
essential; global mean zero alone is not the hypothesis proved here. -/
theorem actual_marginal_dual_energy {f q : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hq : SupportedQuaternionBlocks (N width) q)
    (hc : RatPolyCoeffEqv (project i (polyMul (marginalWeight w K width n) q)) polyZero) :
    headFloor w * (marginalPair w K width n f q * marginalPair w K width n f q) ≤
      prefixCap w * energy w K width (terminalMessage w K width n) f * marginalPair w K width n q q :=
  geometric_square_closed _ _ _ (pairingErrorCap w K width n f q) (radius hw0 hw1 K width hK n)
    (fun k => erasedPair w K width n i f (dualTest hw0 hw1 K width hK n i q k))
    (Q'.le_of_lt (headFloor_positive hw0 hw1)) (pairingErrorCap_nonnegative hw0 hw1 K width hK n f q)
    (radius_nonnegative hw0 hw1 K width hK n) (radius_lt_one hw0 hw1 K width hK n)
    (dualTest_pairing_error hw0 hw1 K width hK n i hi hf hq)
    (approximate_dual_energy hw0 hw1 K width hK n i hi hf hq hc)

include hw0 hw1 hK hi in
/-- Concrete division-free residuals in the ACTUAL marginal supply the
conditional test, without requiring a new centering hypothesis. -/
theorem actualResidual_dual_energy {f s : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hs : SupportedQuaternionBlocks (N width) s) :
    let q := weightedResidual i (marginalWeight w K width n) s
    headFloor w * (marginalPair w K width n f q * marginalPair w K width n f q) ≤
      prefixCap w * energy w K width (terminalMessage w K width n) f * marginalPair w K width n q q :=
  actual_marginal_dual_energy hw0 hw1 K width hK n i hi hf
    (weightedResidual_supported i (marginalWeight_supported w K width n) hs)
    (project_weightedResidual_zero i _ s)

end YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.marginalCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.dualTest_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.dualTest_centered
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.dualTestNormCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.dualTest_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.approximate_dual_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.pairingErrorCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.dualTest_pairing_error
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.actual_marginal_dual_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual.actualResidual_dual_energy
