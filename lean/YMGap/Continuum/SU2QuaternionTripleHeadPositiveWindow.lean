/-
# Literal positive windows for three heads over one shared tail

The original supported weight has one certified lower and upper window.
Copying or lifting the whole residual transports those certificates to each
literal replica slot. Two uses of the certified product compiler then give
the window for the actual three-copy kernel product. All three slots retain
the same tail variables; no independence of the tail is used.
-/

import YMGap.Continuum.SU2QuaternionTripleHeadReplica
import YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct

namespace YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
  (lift_add lift_supported lift_smul lift_one)
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
  (copy copy_add copy_neg copySupported copyCertificate copy_cap_carrier)
open YMGap.Continuum.SU2QuaternionTripleHeadReplica
  (tripleCopy tripleCopy_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct

private theorem cap_supported (blocks : Nat) (c : Q') :
    SupportedQuaternionBlocks blocks (cap c) :=
  polySmul_supported (supported_one blocks) c

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem residual_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polyAdd p (polyNeg (cap c))) :=
  supported_add hp (neg_supported (cap_supported blocks c))

private theorem complement_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polyAdd (cap c) (polyNeg p)) :=
  supported_add (cap_supported blocks c) (neg_supported hp)

/-- Copy the entire lower residual before identifying its padded scalar cap. -/
def copyLowerCertificate (tail heads : Nat) {p : RatPoly} {ell : Q'}
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (L : Certificate (tail+heads) (polyAdd p (polyNeg (cap ell)))) :
    Certificate (tail+(heads+heads))
      (polyAdd (copy heads p) (polyNeg (cap ell))) := by
  let C := copyCertificate tail heads _ (residual_supported hp ell) L
  have h : HaarCarrierEqv (tail+(heads+heads))
      (copy heads (polyAdd p (polyNeg (cap ell))))
      (polyAdd (copy heads p) (polyNeg (cap ell))) := by
    rw [copy_add, copy_neg]
    exact HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.neg (copy_cap_carrier tail heads ell))
  exact .transport h.symm C

/-- Copy the entire upper residual before identifying its padded scalar cap. -/
def copyUpperCertificate (tail heads : Nat) {p : RatPoly} {upper : Q'}
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (U : Certificate (tail+heads) (polyAdd (cap upper) (polyNeg p))) :
    Certificate (tail+(heads+heads))
      (polyAdd (cap upper) (polyNeg (copy heads p))) := by
  let C := copyCertificate tail heads _ (complement_supported hp upper) U
  have h : HaarCarrierEqv (tail+(heads+heads))
      (copy heads (polyAdd (cap upper) (polyNeg p)))
      (polyAdd (cap upper) (polyNeg (copy heads p))) := by
    rw [copy_add, copy_neg]
    exact HaarCarrierEqv.add (copy_cap_carrier tail heads upper)
      (HaarCarrierEqv.refl _ _)
  exact .transport h.symm C

/-- A lifted cap is the same scalar on any enlarged supported carrier. -/
theorem lift_cap_carrier (blocks shift : Nat) (c : Q') :
    HaarCarrierEqv (blocks+shift) (liftBoundary shift (cap c)) (cap c) := by
  have hp := lift_supported (cap_supported blocks c) shift
  have hq := cap_supported (blocks+shift) c
  apply carrier_of_supported hp hq
  intro r hr
  apply PaddedPolynomialCoeffEqv.haar_insert ?_ hp hq r hr
  unfold cap
  rw [lift_smul]
  exact (lift_one (blocks+shift) shift).smul c

/-- Lift the whole lower residual, preserving its literal scalar endpoint. -/
def liftLowerCertificate (blocks shift : Nat) {p : RatPoly} {ell : Q'}
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell)))) :
    Certificate (blocks+shift)
      (polyAdd (liftBoundary shift p) (polyNeg (cap ell))) := by
  let C := lift_certificate shift L
  have h : HaarCarrierEqv (blocks+shift)
      (liftBoundary shift (polyAdd p (polyNeg (cap ell))))
      (polyAdd (liftBoundary shift p) (polyNeg (cap ell))) := by
    rw [lift_add, lift_neg]
    exact HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.neg (lift_cap_carrier blocks shift ell))
  exact .transport h.symm C

/-- Lift the whole upper residual, preserving its literal scalar endpoint. -/
def liftUpperCertificate (blocks shift : Nat) {p : RatPoly} {upper : Q'}
    (U : Certificate blocks (polyAdd (cap upper) (polyNeg p))) :
    Certificate (blocks+shift)
      (polyAdd (cap upper) (polyNeg (liftBoundary shift p))) := by
  let C := lift_certificate shift U
  have h : HaarCarrierEqv (blocks+shift)
      (liftBoundary shift (polyAdd (cap upper) (polyNeg p)))
      (polyAdd (cap upper) (polyNeg (liftBoundary shift p))) := by
    rw [lift_add, lift_neg]
    exact HaarCarrierEqv.add (lift_cap_carrier blocks shift upper)
      (HaarCarrierEqv.refl _ _)
  exact .transport h.symm C

private def slotLower (tail heads : Nat) {p : RatPoly} {ell : Q'}
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (L : Certificate (tail+heads) (polyAdd p (polyNeg (cap ell))))
    (i : Fin 3) : Certificate (tail+(heads+(heads+heads)))
      (polyAdd (tripleCopy heads i p) (polyNeg (cap ell))) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    have hmid : SupportedQuaternionBlocks ((tail+heads)+heads) (copy heads p) := by
      simpa only [Nat.add_assoc] using copySupported tail heads hp
    have Lmid : Certificate ((tail+heads)+heads)
        (polyAdd (copy heads p) (polyNeg (cap ell))) := by
      simpa only [Nat.add_assoc] using copyLowerCertificate tail heads hp L
    simpa only [tripleCopy, Nat.add_assoc] using
      copyLowerCertificate (tail+heads) heads hmid Lmid
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        liftLowerCertificate (tail+(heads+heads)) heads
          (copyLowerCertificate tail heads hp L)
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        liftLowerCertificate ((tail+heads)+heads) heads
          (liftLowerCertificate (tail+heads) heads L)

private def slotUpper (tail heads : Nat) {p : RatPoly} {upper : Q'}
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (U : Certificate (tail+heads) (polyAdd (cap upper) (polyNeg p)))
    (i : Fin 3) : Certificate (tail+(heads+(heads+heads)))
      (polyAdd (cap upper) (polyNeg (tripleCopy heads i p))) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    have hmid : SupportedQuaternionBlocks ((tail+heads)+heads) (copy heads p) := by
      simpa only [Nat.add_assoc] using copySupported tail heads hp
    have Umid : Certificate ((tail+heads)+heads)
        (polyAdd (cap upper) (polyNeg (copy heads p))) := by
      simpa only [Nat.add_assoc] using copyUpperCertificate tail heads hp U
    simpa only [tripleCopy, Nat.add_assoc] using
      copyUpperCertificate (tail+heads) heads hmid Umid
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        liftUpperCertificate (tail+(heads+heads)) heads
          (copyUpperCertificate tail heads hp U)
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        liftUpperCertificate ((tail+heads)+heads) heads
          (liftUpperCertificate (tail+heads) heads U)

/-- The actual three-copy kernel has cubic literal lower and upper windows
on three head slices with a single shared tail. -/
def tripleKernelWindow (tail heads : Nat) (p : RatPoly) {ell upper : Q'}
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (hell : (0 : Q') < ell) (hupper : (0 : Q') < upper)
    (horder : ell ≤ upper)
    (L : Certificate (tail+heads) (polyAdd p (polyNeg (cap ell))))
    (U : Certificate (tail+heads) (polyAdd (cap upper) (polyNeg p))) :
    PositiveWindowProduct (tail+(heads+(heads+heads)))
      (polyMul (tripleCopy heads 0 p) (tripleCopy heads 1 p))
      (tripleCopy heads 2 p) (ell*ell) (upper*upper) ell upper := by
  let h0 := tripleCopy_supported tail heads hp 0
  let h1 := tripleCopy_supported tail heads hp 1
  let h2 := tripleCopy_supported tail heads hp 2
  let W01 := multiplyPositiveWindows h0 h1 hell hupper hell hupper
    horder horder (slotLower tail heads hp L 0) (slotUpper tail heads hp U 0)
    (slotLower tail heads hp L 1) (slotUpper tail heads hp U 1)
  exact multiplyPositiveWindows W01.support h2 W01.lowerPositive W01.upperPositive
    hell hupper W01.endpointsOrdered horder W01.lowerCertificate
    W01.upperCertificate (slotLower tail heads hp L 2) (slotUpper tail heads hp U 2)

end YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow

#print axioms YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow.copyLowerCertificate
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow.copyUpperCertificate
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow.lift_cap_carrier
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow.liftLowerCertificate
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow.liftUpperCertificate
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow.tripleKernelWindow
