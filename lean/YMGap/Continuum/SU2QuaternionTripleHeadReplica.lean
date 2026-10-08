/-
# Three original head replicas with ONE shared surviving tail

Each placement is a composition of the existing copy and lift maps.
The actual supported square certificates are transported through these
maps. The product pin reuses the existing exact three-copy Fubini theorem;
it is not an independence assumption about the common tail. Zero heads
and zero surviving blocks are included. No density inverse, window or
normalized conditional bound is asserted here.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadThreeGram

namespace YMGap.Continuum.SU2QuaternionTripleHeadReplica

set_option autoImplicit false

open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_supported lift_add)
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
  (copy copy_mul copy_add copy_neg copySupported copyCertificate)

/-- Three placements on heads0, heads1, heads2, followed by the SAME tail. -/
def tripleCopy (heads : Nat) (i : Fin 3) (p : RatPoly) : RatPoly :=
  match i.val with
  | 0 => copy heads (copy heads p)
  | 1 => liftBoundary heads (copy heads p)
  | _ => liftBoundary heads (liftBoundary heads p)

/-- Every actual replica placement preserves polynomial multiplication. -/
theorem tripleCopy_mul (heads : Nat) (i : Fin 3) (p q : RatPoly) :
    tripleCopy heads i (polyMul p q) =
      polyMul (tripleCopy heads i p) (tripleCopy heads i q) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    simp only [tripleCopy, copy_mul]
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      simp only [tripleCopy, copy_mul, lift_product]
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      simp only [tripleCopy, lift_product]

/-- Signed moment algebra is preserved by each actual placement. -/
theorem tripleCopy_add (heads : Nat) (i : Fin 3) (p q : RatPoly) :
    tripleCopy heads i (polyAdd p q) =
      polyAdd (tripleCopy heads i p) (tripleCopy heads i q) := by
  unfold tripleCopy
  split <;> simp only [copy_add, lift_add]

theorem tripleCopy_neg (heads : Nat) (i : Fin 3) (p : RatPoly) :
    tripleCopy heads i (polyNeg p) = polyNeg (tripleCopy heads i p) := by
  unfold tripleCopy
  split <;> simp only [copy_neg, lift_neg]

/-- Support remains explicit through all THREE heads and the shared tail. -/
theorem tripleCopy_supported (tail heads : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+heads) p) (i : Fin 3) :
    SupportedQuaternionBlocks (tail+(heads+(heads+heads))) (tripleCopy heads i p) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    have hmid : SupportedQuaternionBlocks ((tail+heads)+heads) (copy heads p) := by
      simpa only [Nat.add_assoc] using copySupported tail heads hp
    simpa only [tripleCopy, Nat.add_assoc] using copySupported (tail+heads) heads hmid
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        lift_supported (copySupported tail heads hp) heads
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        lift_supported (lift_supported hp heads) heads

/-- Type-valued positivity is carried by the EXISTING copy/lift witnesses. -/
def tripleCopy_certificate (tail heads : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+heads) p) (P : Certificate (tail+heads) p)
    (i : Fin 3) : Certificate (tail+(heads+(heads+heads))) (tripleCopy heads i p) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    have hmid : SupportedQuaternionBlocks ((tail+heads)+heads) (copy heads p) := by
      simpa only [Nat.add_assoc] using copySupported tail heads hp
    let Q : Certificate ((tail+heads)+heads) (copy heads p) := by
      simpa only [Nat.add_assoc] using copyCertificate tail heads p hp P
    simpa only [tripleCopy, Nat.add_assoc] using
      copyCertificate (tail+heads) heads (copy heads p) hmid Q
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        lift_certificate heads (copyCertificate tail heads p hp P)
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      simpa only [tripleCopy, Nat.add_assoc] using
        lift_certificate heads (lift_certificate heads P)

/-- Exact THREE-moment factorization, with arbitrary jointly occurring
tail coordinates and no support premise on the factors. -/
theorem replica_product_three (heads : Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (heads+(heads+heads))
        (polyMul (polyMul (tripleCopy heads 0 p) (tripleCopy heads 1 q))
          (tripleCopy heads 2 r)))
      (polyMul (polyMul (partialHaarHeads heads p) (partialHaarHeads heads q))
        (partialHaarHeads heads r)) := by
  have hcount : 3*heads=heads+(heads+heads) := by omega
  simpa only [hcount, tripleCopy, SU2QuaternionMultiHeadThreeGram.tripleTensor] using
    SU2QuaternionMultiHeadThreeGram.triple_product_pin heads p q r

end YMGap.Continuum.SU2QuaternionTripleHeadReplica

#print axioms YMGap.Continuum.SU2QuaternionTripleHeadReplica.tripleCopy
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadReplica.tripleCopy_mul
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadReplica.tripleCopy_add
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadReplica.tripleCopy_neg
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadReplica.tripleCopy_supported
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadReplica.tripleCopy_certificate
#print axioms YMGap.Continuum.SU2QuaternionTripleHeadReplica.replica_product_three
