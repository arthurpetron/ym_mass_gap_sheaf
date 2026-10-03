/-
# Computed head Casimir inverse with every spectator retained

Compute the existing finite Fischer modes, discard only their degree-zero
head part, and divide each remaining harmonic by its positive integer
Casimir d(d+2). The resulting polynomial solves the original head Poisson
equation modulo its CONDITIONAL Haar mean, under every original insertion.
Angular integration by parts therefore represents a centered source pairing
by derivatives of the actual source, not by an assigned score or new source.

This is an exact finite construction. No positivity of a signed defect,
uniform interacting estimate, or continuum spectral gap is asserted.
-/

import YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionRelativeHeatInsertion

namespace YMGap.Continuum.SU2QuaternionHeadCasimirInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHarmonicDegreeSelection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul angular_pair)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Zero-degree modes retain arbitrary polynomials in ALL other blocks. -/
def zeroPart {blocks : Nat} : List (Mode blocks) → RatPoly
  | [] => polyZero
  | m::ms => if m.degree = 0 then polyAdd (harmonicPart m) (zeroPart ms)
      else zeroPart ms

def positivePart {blocks : Nat} : List (Mode blocks) → RatPoly
  | [] => polyZero
  | m::ms => if m.degree = 0 then positivePart ms
      else polyAdd (harmonicPart m) (positivePart ms)

/-- The reciprocal is concrete rational data; division at degree zero is
never attempted. -/
def inverseModes {blocks : Nat} : List (Mode blocks) → RatPoly
  | [] => polyZero
  | m::ms => if m.degree = 0 then inverseModes ms
      else polyAdd
        (polySmul (Q'.invSucc (m.degree*(m.degree+2)-1)) (harmonicPart m))
        (inverseModes ms)

theorem split_reassembly {blocks : Nat} : ∀ ms : List (Mode blocks),
    RatPolyCoeffEqv (sumHarmonics ms) (polyAdd (zeroPart ms) (positivePart ms))
  | [] => .refl _
  | m::ms => by
      by_cases hd : m.degree = 0
      · simp only [sumHarmonics, zeroPart, positivePart, if_pos hd]
        exact ((RatPolyCoeffEqv.refl _).add (split_reassembly ms)).trans
          (RatPolyCoeffEqv.add_assoc _ _ _).symm
      · simp only [sumHarmonics, zeroPart, positivePart, if_neg hd]
        exact ((RatPolyCoeffEqv.refl _).add (split_reassembly ms)).trans
          (coeffEvalExpr_eqv_of_normalize_eq
            (.add (.var 0) (.add (.var 1) (.var 2)))
            (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
            (fun | 0 => harmonicPart m | 1 => zeroPart ms | _ => positivePart ms))

theorem zeroPart_degree {blocks : Nat} : ∀ ms : List (Mode blocks),
    HasQuaternionBlockDegree 0 0 (zeroPart ms)
  | [] => hasQuaternionBlockDegree_zero _ _
  | m::ms => by
      by_cases hd : m.degree = 0
      · simp only [zeroPart, if_pos hd]
        exact ((harmonicPart_degree m).relabel hd).add (zeroPart_degree ms)
      · simpa only [zeroPart, if_neg hd] using zeroPart_degree ms

theorem inverseModes_supported {blocks : Nat} : ∀ ms : List (Mode blocks),
    SupportedQuaternionBlocks blocks (inverseModes ms)
  | [] => by intro t ht; contradiction
  | m::ms => by
      by_cases hd : m.degree = 0
      · simpa only [inverseModes, if_pos hd] using inverseModes_supported ms
      · simp only [inverseModes, if_neg hd]
        exact polyAdd_supported (polySmul_supported (harmonicPart_supported m) _)
          (inverseModes_supported ms)

theorem positivePart_partial_zero {blocks : Nat} : ∀ ms : List (Mode blocks),
    RatPolyCoeffEqv (partialHaarHead (positivePart ms)) polyZero
  | [] => .refl _
  | m::ms => by
      by_cases hd : m.degree = 0
      · simpa only [positivePart, if_pos hd] using positivePart_partial_zero ms
      · simp only [positivePart, if_neg hd, partialHaarHead_add]
        have hz : RatPolyCoeffEqv (partialHaarHead (harmonicPart m)) polyZero :=
          (partialHaarHead_congr (RatPolyCoeffEqv.mul_one (harmonicPart m))).symm.trans
            (partialHaarHead_harmonic_lower_degree (harmonicPart_degree m)
              (harmonicPart_harmonic m) (hasQuaternionBlockDegree_one 0) (by omega))
        exact hz.add (positivePart_partial_zero ms)

private theorem reciprocal_casimir {d : Nat} (hd : d ≠ 0) :
    Q'.invSucc (d*(d+2)-1) * (-(Q'.ofNat d*(Q'.ofNat d+2))) ≈ (-1 : Q') := by
  have hn : d*(d+2)-1+1 = d*(d+2) := by
    have hp : 0 < d*(d+2) := Nat.mul_pos (by omega) (by omega)
    omega
  have hc : Q'.ofNat d*(Q'.ofNat d+2) ≈ Q'.ofNat (d*(d+2)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))
          (Q'.ofNat_add_eqv d 2).symm))
      (HeatKernelRGStep.ofNat_mul_eqv d (d+2)).symm
  have hi : Q'.invSucc (d*(d+2)-1)*Q'.ofNat (d*(d+2)) ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_of_eq (congrArg Q'.ofNat hn.symm)))
        (Q'.ofNat_succ_mul_invSucc (d*(d+2)-1)))
  exact Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv _ _)
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hc) hi))

/-- Exact inverse on every computed positive-degree mode. Signs and all
within-degree cancellations stay inside the supplied polynomial. -/
theorem inverseModes_casimir {blocks : Nat} (hb : 0 < blocks) :
    ∀ ms : List (Mode blocks), HaarCarrierEqv blocks
      (angularLaplacian (inverseModes ms)) (polySmul (-1) (positivePart ms))
  | [] => .refl _ _
  | m::ms => by
      by_cases hd : m.degree = 0
      · simpa only [inverseModes, positivePart, if_pos hd] using inverseModes_casimir hb ms
      · simp only [inverseModes, positivePart, if_neg hd]
        have hm : HaarCarrierEqv blocks
            (angularLaplacian
              (polySmul (Q'.invSucc (m.degree*(m.degree+2)-1)) (harmonicPart m)))
            (polySmul (-1) (harmonicPart m)) :=
          (RatPolyCoeffEqv.haarCarrier (angularLaplacian_smul _ _)).trans
            ((HaarCarrierEqv.smul _
              (harmonic_angularLaplacian hb _ (harmonicPart_degree m)
                (harmonicPart_harmonic m))).trans
              (RatPolyCoeffEqv.haarCarrier
                ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
                  (RatPolyCoeffEqv.smul_coefficient (reciprocal_casimir hd) _))))
        exact (RatPolyCoeffEqv.haarCarrier (angularLaplacian_add _ _)).trans
          ((HaarCarrierEqv.add hm (inverseModes_casimir hb ms)).trans
            (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_add _ _ _).symm))

private theorem degree_zero_partial {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 0 p) :
    RatPolyCoeffEqv (partialHaarHead p) (dropHeadPolynomial p) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead p) (dropHeadPolynomial p) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih =>
        have hd := hp t List.mem_cons_self
        have hz : exponentAt t.1 0 = 0 ∧ exponentAt t.1 1 = 0 ∧
            exponentAt t.1 2 = 0 ∧ exponentAt t.1 3 = 0 := by
          change exponentAt t.1 0 + exponentAt t.1 1 + exponentAt t.1 2 +
            exponentAt t.1 3 = 0 at hd
          have h012_3 := Nat.eq_zero_of_add_eq_zero hd
          have h01_2 := Nat.eq_zero_of_add_eq_zero h012_3.1
          have h0_1 := Nat.eq_zero_of_add_eq_zero h01_2.1
          exact ⟨h0_1.1, h0_1.2, h01_2.2, h012_3.2⟩
        have hm : headQuaternionMoment t.1 ≈ (1 : Q') := by
          unfold headQuaternionMoment
          rw [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
          decide +kernel
        exact ⟨rfl, Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm)
          (Q'.mul_one_eqv _), ih (fun s hs => hp s (List.mem_cons_of_mem t hs))⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem degree_zero_projection (tail : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 0 p) :
    HaarCarrierEqv (tail+1) p (liftBoundary 1 (partialHaarHead p)) := by
  intro insertion
  have hi : HeadQuaternionIndependent p := hp
  exact Q'.eqv_trans _ _ _ (independent_to_lift tail insertion p hi)
    (haar_of_coeff ((lift_coeff 1 (degree_zero_partial hp)).symm.mul_left insertion))

/-- Actual polynomial data, computed from the input rather than an inverse
existence certificate or an assumed Poisson solver. -/
def potential (tail : Nat) (p : RatPoly) : RatPoly :=
  inverseModes (modes (tail+1) (by omega) p)

theorem potential_supported (tail : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks (tail+1) (potential tail p) := inverseModes_supported _

/-- The retained constant sector is exactly the conditional Haar projection,
not the global mean. -/
theorem zeroPart_projection (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1)
      (zeroPart (modes (tail+1) (by omega) p))
      (liftBoundary 1 (partialHaarHead p)) := by
  let ms := modes (tail+1) (by omega) p
  have hs : HaarCarrierEqv (tail+1) p (polyAdd (zeroPart ms) (positivePart ms)) :=
    (polynomial_harmonic_carrier (by omega) p hp).trans
      (RatPolyCoeffEqv.haarCarrier (split_reassembly ms))
  have hpartial : HaarCarrierEqv tail (partialHaarHead p) (partialHaarHead (zeroPart ms)) := by
    have h := partialHaarHead_carrier hs
    rw [partialHaarHead_add] at h
    exact h.trans (RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl _).add (positivePart_partial_zero ms)).trans
        (RatPolyCoeffEqv.add_zero _)))
  exact (degree_zero_projection tail _ (zeroPart_degree ms)).trans
    (lift_carrier 1 hpartial.symm)

/-- Solves the positive head-Casimir equation for the input minus its
conditional projection. Every insertion is on the SAME original carrier. -/
theorem potential_poisson (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (polyNeg (angularLaplacian (potential tail p)))
      (polyAdd p (polyNeg (liftBoundary 1 (partialHaarHead p)))) := by
  let ms := modes (tail+1) (by omega) p
  have hi : HaarCarrierEqv (tail+1)
      (polyNeg (angularLaplacian (potential tail p))) (positivePart ms) :=
    (HaarCarrierEqv.neg (inverseModes_casimir (by omega) ms)).trans
      (RatPolyCoeffEqv.haarCarrier (by
        exact (neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
          ((RatPolyCoeffEqv.smul_coefficient
            (by decide : (-1 : Q')*(-1) ≈ (1 : Q')) _).trans
            (RatPolyCoeffEqv.one_smul _)))))
  have hs : HaarCarrierEqv (tail+1) p (polyAdd (zeroPart ms) (positivePart ms)) :=
    (polynomial_harmonic_carrier (by omega) p hp).trans
      (RatPolyCoeffEqv.haarCarrier (split_reassembly ms))
  have hz := zeroPart_projection tail p hp
  have hr := HaarCarrierEqv.add hs (HaarCarrierEqv.neg hz.symm)
  have hc : RatPolyCoeffEqv
      (polyAdd (polyAdd (zeroPart ms) (positivePart ms)) (polyNeg (zeroPart ms)))
      (positivePart ms) := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
    (by decide) (fun | 0 => zeroPart ms | _ => positivePart ms)
  exact hi.trans (hr.trans (RatPolyCoeffEqv.haarCarrier hc)).symm

private theorem sixValue_neg (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) :=
  poly_identity_of_normal_eq
    (.add (.neg (.var 0)) (.add (.neg (.var 1)) (.add (.neg (.var 2))
      (.add (.neg (.var 3)) (.add (.neg (.var 4)) (.neg (.var 5)))))))
    (.neg (.add (.var 0) (.add (.var 1) (.add (.var 2)
      (.add (.var 3) (.add (.var 4) (.var 5))))))) (by decide)
    (fun | 0 => f 0 1 | 1 => f 0 2 | 2 => f 0 3
         | 3 => f 1 2 | 4 => f 1 3 | _ => f 2 3)

/-- Source derivatives paired with the CONSTRUCTED inverse polynomial. -/
def sourceGradientPair (tail : Nat) (q p : RatPoly) : Q' :=
  sixValue (fun i j => H (tail+1)
    (polyMul (angularDerivative i j q) (angularDerivative i j (potential tail p))))

private theorem gradient_ibp (tail : Nat) (q u : RatPoly) :
    sixValue (fun i j => H (tail+1)
      (polyMul (angularDerivative i j q) (angularDerivative i j u))) ≈
      H (tail+1) (polyMul q (polyNeg (angularLaplacian u))) := by
  let second := fun i j => H (tail+1)
    (polyMul q (angularDerivative i j (angularDerivative i j u)))
  have hp := sixValue_congr _ (fun i j => -(second i j)) (fun i j hi hj =>
    Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (angular_pair tail hi hj
        q (angularDerivative i j u)))
      (poly_identity_of_normal_eq (.neg (.neg (.var 0))) (.var 0) (by decide)
        (fun _ => H (tail+1)
          (polyMul (angularDerivative i j q) (angularDerivative i j u))))))
  have hs := (haar_six (tail+1) q (fun i j =>
    angularDerivative i j (angularDerivative i j u))).symm
  have hn : -(H (tail+1) (polyMul q (angularLaplacian u))) ≈
      H (tail+1) (polyMul q (polyNeg (angularLaplacian u))) := by
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (haar_of_coeff ((neg_smul _).mul_left q))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ (-1) q _)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
          (.neg (.var 0)) (by decide)
          (fun _ => H (tail+1) (polyMul q (angularLaplacian u))))))
  exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ (sixValue_neg second)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hs) hn))

/-- Finite Stein identity: the source is arbitrary and is differentiated
literally. It is not assumed independent of the selected block. -/
theorem source_gradient_identity (tail : Nat) (q p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    H (tail+1) (polyMul q
      (polyAdd p (polyNeg (liftBoundary 1 (partialHaarHead p))))) ≈
      sourceGradientPair tail q p :=
  Q'.eqv_trans _ _ _ (potential_poisson tail p hp q).symm
    (gradient_ibp tail q (potential tail p)).symm

end YMGap.Continuum.SU2QuaternionHeadCasimirInverse

#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.split_reassembly
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.zeroPart_degree
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.inverseModes_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.positivePart_partial_zero
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.inverseModes_casimir
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.potential_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.zeroPart_projection
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.potential_poisson
#print axioms YMGap.Continuum.SU2QuaternionHeadCasimirInverse.source_gradient_identity
