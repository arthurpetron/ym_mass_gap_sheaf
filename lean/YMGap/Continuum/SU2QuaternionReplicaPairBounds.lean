/-
# Two-copy order certificates for one positive finite Haar weight

The two independent copies of a supported certified polynomial inherit
its scalar floor and cap with squared constants.  All certificates live
on the actual doubled quaternion carrier, including after an explicit
block involution.  This is algebraic order data for a replica comparison;
no conditional normalization or coercivity is asserted here.
-/

import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionCoordinateColumnLift
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.SU2QuaternionReplicaPairBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier (carrierOfPrefix)

private theorem support_smul {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_first {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) p := by
  intro t ht
  exact Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))

private theorem support_cap (n : Nat) (c : Q') :
    SupportedQuaternionBlocks n (cap c) :=
  support_smul (supported_one n) c

private theorem support_lower {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polyAdd p (polyNeg (cap c))) :=
  supported_add hp (support_neg (support_cap n c))

private theorem support_upper {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polyAdd (cap c) (polyNeg p)) :=
  supported_add (support_cap n c) (support_neg hp)

/-- A scalar polynomial shifted to the second copy remains the SAME
constant under every Haar insertion on the doubled carrier. -/
theorem lift_cap_carrier (n : Nat) (c : Q') :
    HaarCarrierEqv (n+n) (liftBoundary n (cap c)) (cap c) := by
  have hp := lift_supported (support_cap n c) n
  have hq := support_cap (n+n) c
  apply carrier_of_supported hp hq
  intro r hr
  apply PaddedPolynomialCoeffEqv.haar_insert ?_ hp hq r hr
  unfold cap
  rw [lift_smul]
  exact (lift_one (n+n) n).smul c

/-- Reindexing a scalar cap changes only harmless zero padding. -/
theorem reindex_cap_carrier {n : Nat}
    (s : QuaternionBlockInvolution n) (c : Q') :
    HaarCarrierEqv n (reindexQuaternionPolynomial s (cap c)) (cap c) := by
  have hp := reindex_supported s (cap c)
  have hq := support_cap n c
  apply carrierOfPrefix hp hq
  unfold cap
  rw [reindexQuaternionPolynomial_smul]
  exact (reindexQuaternionPolynomial_character_prefix s polyZero 0).smul c

private theorem lift_lower_carrier (n : Nat) (p : RatPoly) (c : Q') :
    HaarCarrierEqv (n+n)
      (liftBoundary n (polyAdd p (polyNeg (cap c))))
      (polyAdd (liftBoundary n p) (polyNeg (cap c))) := by
  rw [lift_add, lift_neg]
  exact HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
    (HaarCarrierEqv.neg (lift_cap_carrier n c))

private theorem lift_upper_carrier (n : Nat) (p : RatPoly) (c : Q') :
    HaarCarrierEqv (n+n)
      (liftBoundary n (polyAdd (cap c) (polyNeg p)))
      (polyAdd (cap c) (polyNeg (liftBoundary n p))) := by
  rw [lift_add, lift_neg]
  exact HaarCarrierEqv.add (lift_cap_carrier n c)
    (HaarCarrierEqv.refl _ _)

/-- The actual two-copy weight is positive on the doubled carrier. -/
def pairCertificate (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (P : Certificate n p) :
    Certificate (n+n) (polyMul p (liftBoundary n p)) :=
  (certificate_extend n hp P).mul (lift_certificate n P)

theorem pair_supported (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) (polyMul p (liftBoundary n p)) :=
  supported_polyMul (support_first hp) (lift_supported hp n)

/-- A one-copy lower certificate yields the literal squared scalar floor
for the two-copy weight; only harmless constant padding uses Haar carrier
transport. -/
def pairFloorCertificate (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (P : Certificate n p)
    (ell : Q') (hell : (0 : Q') ≤ ell)
    (L : Certificate n (polyAdd p (polyNeg (cap ell)))) :
    Certificate (n+n)
      (polyAdd (polyMul p (liftBoundary n p)) (polyNeg (cap (ell*ell)))) := by
  let q := liftBoundary n p
  let c := cap ell
  let lower := polyAdd p (polyNeg c)
  have hraw : Certificate (n+n)
      (polyAdd (polyMul lower q)
        (polyMul c (liftBoundary n lower))) :=
    .add ((certificate_extend n (support_lower hp ell) L).mul (lift_certificate n P))
      ((Certificate.constant (n+n) ell hell).mul (lift_certificate n L))
  have hring : RatPolyCoeffEqv
      (polyAdd (polyMul p q) (polyNeg (cap (ell*ell))))
      (polyAdd (polyMul lower q)
        (polyMul c (polyAdd q (polyNeg c)))) :=
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul ell ell).symm)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
        (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
          (.mul (.var 2) (.add (.var 1) (.neg (.var 2)))))
        (by decide) (fun | 0 => p | 1 => q | _ => c))
  exact .transport ((RatPolyCoeffEqv.haarCarrier hring).trans
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
        (lift_lower_carrier n p ell).symm))) hraw

/-- The corresponding squared scalar cap retains the exact two-copy
weight rather than replacing either copy by a scalar measure. -/
def pairCapCertificate (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (P : Certificate n p)
    (U : Q') (hU : (0 : Q') ≤ U)
    (C : Certificate n (polyAdd (cap U) (polyNeg p))) :
    Certificate (n+n)
      (polyAdd (cap (U*U)) (polyNeg (polyMul p (liftBoundary n p)))) := by
  let q := liftBoundary n p
  let c := cap U
  let upper := polyAdd c (polyNeg p)
  have hraw : Certificate (n+n)
      (polyAdd (polyMul upper q)
        (polyMul c (liftBoundary n upper))) :=
    .add ((certificate_extend n (support_upper hp U) C).mul (lift_certificate n P))
      ((Certificate.constant (n+n) U hU).mul (lift_certificate n C))
  have hring : RatPolyCoeffEqv
      (polyAdd (cap (U*U)) (polyNeg (polyMul p q)))
      (polyAdd (polyMul upper q)
        (polyMul c (polyAdd c (polyNeg q)))) :=
    (((cap_mul U U).symm).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1))))
        (.add (.mul (.add (.var 2) (.neg (.var 0))) (.var 1))
          (.mul (.var 2) (.add (.var 2) (.neg (.var 1)))))
        (by decide) (fun | 0 => p | 1 => q | _ => c))
  exact .transport ((RatPolyCoeffEqv.haarCarrier hring).trans
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
        (lift_upper_carrier n p U).symm))) hraw

/-- The pair certificate survives any explicit two-copy block involution. -/
def reindexedPairCertificate (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (P : Certificate n p)
    (s : QuaternionBlockInvolution (n+n)) :
    Certificate (n+n)
      (reindexQuaternionPolynomial s (polyMul p (liftBoundary n p))) :=
  reindex_certificate s (pair_supported n hp) (pairCertificate n hp P)

/-- Reindexed lower gap with the literal squared scalar floor. -/
def reindexedPairFloorCertificate (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (P : Certificate n p)
    (ell : Q') (hell : (0 : Q') ≤ ell)
    (L : Certificate n (polyAdd p (polyNeg (cap ell))))
    (s : QuaternionBlockInvolution (n+n)) :
    Certificate (n+n)
      (polyAdd (reindexQuaternionPolynomial s (polyMul p (liftBoundary n p)))
        (polyNeg (cap (ell*ell)))) := by
  have hraw := reindex_certificate s
    (supported_add (pair_supported n hp) (support_neg (support_cap (n+n) (ell*ell))))
    (pairFloorCertificate n hp P ell hell L)
  have hcarrier : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial s
        (polyAdd (polyMul p (liftBoundary n p)) (polyNeg (cap (ell*ell)))))
      (polyAdd (reindexQuaternionPolynomial s (polyMul p (liftBoundary n p)))
        (polyNeg (cap (ell*ell)))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
    exact HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.neg (reindex_cap_carrier s (ell*ell)))
  exact Certificate.transport hcarrier.symm hraw

/-- Reindexed upper gap on the SAME doubled carrier. -/
def reindexedPairCapCertificate (n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (P : Certificate n p)
    (U : Q') (hU : (0 : Q') ≤ U)
    (C : Certificate n (polyAdd (cap U) (polyNeg p)))
    (s : QuaternionBlockInvolution (n+n)) :
    Certificate (n+n)
      (polyAdd (cap (U*U))
        (polyNeg (reindexQuaternionPolynomial s (polyMul p (liftBoundary n p))))) := by
  have hraw := reindex_certificate s
    (supported_add (support_cap (n+n) (U*U)) (support_neg (pair_supported n hp)))
    (pairCapCertificate n hp P U hU C)
  have hcarrier : HaarCarrierEqv (n+n)
      (reindexQuaternionPolynomial s
        (polyAdd (cap (U*U)) (polyNeg (polyMul p (liftBoundary n p)))))
      (polyAdd (cap (U*U))
        (polyNeg (reindexQuaternionPolynomial s (polyMul p (liftBoundary n p))))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
    exact HaarCarrierEqv.add (reindex_cap_carrier s (U*U))
      (HaarCarrierEqv.refl _ _)
  exact Certificate.transport hcarrier.symm hraw

#print axioms lift_cap_carrier
#print axioms reindex_cap_carrier
#print axioms pairCertificate
#print axioms pair_supported
#print axioms pairFloorCertificate
#print axioms pairCapCertificate
#print axioms reindexedPairCertificate
#print axioms reindexedPairFloorCertificate
#print axioms reindexedPairCapCertificate

end YMGap.Continuum.SU2QuaternionReplicaPairBounds
