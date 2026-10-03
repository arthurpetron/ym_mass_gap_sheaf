/-
# Direct positive certificates for the original cutoff-one product heat

The sharp fundamental trace interval constructs the actual relative heat
factor 1+alpha*chi_1 when 0<=alpha and 2*alpha<=1. All selected original
kernel factors are multiplied on their shared carrier, then the actual
head-Haar integration constructs a positive output certificate.

This finite producer does not invoke or weaken the late-cutoff guard.
No interacting variance, strict transfer bound, gain or scaling estimate
is inferred from positivity preservation.
-/

import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Continuum.SU2QuaternionProductHeatLocalBand

namespace YMGap.Continuum.SU2QuaternionFundamentalProductHeatCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

private theorem sum_congr (f g : Nat → RatPoly) : ∀ xs : List Nat,
    (∀ i, i ∈ xs → f i = g i) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | i::xs, h => by
    simp only [finitePolySum, h i List.mem_cons_self,
      sum_congr f g xs (fun j hj => h j (List.mem_cons_of_mem i hj))]

private theorem heatAt_eq_prefix (a b : Nat) (w : Q') (K : Nat) :
    heatAt a b w K = heatPrefix w K (scalarAt a b) := by
  unfold heatAt heatPrefix
  apply sum_congr
  intro spin hspin
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]

private theorem fundamental_prefix (w : Q') (p : RatPoly) :
    RatPolyCoeffEqv (heatPrefix w 1 p)
      (polyAdd polyOne (polySmul (coeffW w 1) (characterPolynomial p 1))) := by
  have hr : RatPolyCoeffEqv (heatRemainder w 1 p)
      (polySmul (coeffW w 1) (characterPolynomial p 1)) := by
    unfold heatRemainder
    change RatPolyCoeffEqv
      (polyAdd (polySmul (coeffW w 1) (characterPolynomial p 1)) polyZero)
      (polySmul (coeffW w 1) (characterPolynomial p 1))
    exact RatPolyCoeffEqv.add_zero _
  exact (heatPrefix_split w 1 p).trans ((RatPolyCoeffEqv.refl polyOne).add hr)

/-- A direct certificate of the actual fundamental heat factor. The two
original coordinate blocks may coincide; no independence is assumed. -/
def heatAt_certificate {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    (w : Q') (h0 : (0 : Q') ≤ coeffW w 1) (hcap : coeffW w 1 * 2 ≤ 1) :
    Certificate blocks (heatAt a b w 1) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  have hp : Supported blocks word :=
    (Supported.coordinate ha).mul (Supported.coordinate hb).conj
  have hu : HaarCarrierEqv blocks (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb))
  let R := (sharpCharacterInterval (SquareBound.scalar hp hu) 1).smul (coeffW w 1) h0
  have he : Q'.eqv ((1 + -(coeffW w 1 * 2)) + coeffW w 1 * 2) 1 :=
    poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.var 0))) (.var 0)) (.const 1)
      (by decide) (fun _ => coeffW w 1 * 2)
  have hc : RatPolyCoeffEqv
      (polyAdd (cap (1 + -(coeffW w 1 * 2)))
        (polyAdd (cap (coeffW w 1 * 2))
          (polySmul (coeffW w 1) (characterPolynomial word.scalar 1))))
      (polyAdd polyOne (polySmul (coeffW w 1) (characterPolynomial word.scalar 1))) :=
    (RatPolyCoeffEqv.add_assoc _ _ _).symm.trans
      (((cap_add _ _).trans ((RatPolyCoeffEqv.smul_coefficient he polyOne).trans
        (RatPolyCoeffEqv.one_smul polyOne))).add (RatPolyCoeffEqv.refl _))
  rw [heatAt_eq_prefix]
  exact .ofCoeff ((fundamental_prefix w (scalarAt a b)).trans hc.symm)
    ((Certificate.constant blocks (1 + -(coeffW w 1 * 2))
      (Q'.sub_nonneg_of_le hcap)).add R.lower)

/-- Every literal selected kernel factor remains in the positivity witness. -/
def productHeat_certificate (n : Nat) (w : Q')
    (h0 : (0 : Q') ≤ coeffW w 1) (hcap : coeffW w 1 * 2 ≤ 1) :
    (ids : List Nat) → (∀ i, i ∈ ids → i < n) →
      Certificate (n+n) (productHeat n w 1 ids)
  | [], _ => .one _
  | i::ids, hi =>
    (heatAt_certificate (by have := hi i List.mem_cons_self; omega)
      (by have := hi i List.mem_cons_self; omega) w h0 hcap).mul
      (productHeat_certificate n w h0 hcap ids
        (fun j hj => hi j (List.mem_cons_of_mem i hj)))

/-- The actual cutoff-one kinetic map preserves the constructed positive cone,
using direct kernel positivity and ordered head integration, not a late guard. -/
def productMap_certificate (n : Nat) (w : Q')
    (h0 : (0 : Q') ≤ coeffW w 1) (hcap : coeffW w 1 * 2 ≤ 1)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    {f : RatPoly} (hf : SupportedQuaternionBlocks n f) (F : Certificate n f) :
    Certificate n (productMap n w 1 ids f) :=
  partialHaarHeads_certificate n n
    ((productHeat_certificate n w h0 hcap ids hids).mul (certificate_extend n hf F))

end YMGap.Continuum.SU2QuaternionFundamentalProductHeatCertificate

#print axioms YMGap.Continuum.SU2QuaternionFundamentalProductHeatCertificate.heatAt_certificate
#print axioms YMGap.Continuum.SU2QuaternionFundamentalProductHeatCertificate.productHeat_certificate
#print axioms YMGap.Continuum.SU2QuaternionFundamentalProductHeatCertificate.productMap_certificate
