/-
# Explicit finite-Haar SU(2) GNS carrier

The product-heat and plaquette modules already prove finite positive forms, but
their carriers are packaged separately.  This module exposes the ordinary
finite normalized Haar form on supported quaternion polynomials as one
constructive `GNSData` object and names its quotient carrier.

The resulting quotient is a finite-cutoff GNS/pre-Hilbert stage.  It supplies
an exact same-object pairing, a normalized unit class, positive definiteness
after radical quotienting, and sharp Cauchy--Schwarz.  It is not the general
Hilbert completion, does not identify the selected-link relative pairing, and
does not assert a uniform transfer gap or a continuum limit.
-/

import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.BF4CompactActionCPOrder
import YMGap.Continuum.QPolyHaarPositiveSubstitution
import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv

/-! ## The finite ordinary-Haar form -/

/-- The normalized finite Haar pairing on supported quaternion polynomials. -/
def finiteHaarPair (blocks : Nat) (p q : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul p q)

theorem finiteHaarPair_symm (blocks : Nat) (p q : RatPoly) :
    finiteHaarPair blocks p q ≈ finiteHaarPair blocks q p := by
  unfold finiteHaarPair
  exact haar_of_coeff (RatPolyCoeffEqv.mul_comm p q)

theorem finiteHaarPair_add_left (blocks : Nat) (p q r : RatPoly) :
    finiteHaarPair blocks (polyAdd p q) r ≈
      finiteHaarPair blocks p r + finiteHaarPair blocks q r := by
  unfold finiteHaarPair
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

theorem finiteHaarPair_smul_left (blocks : Nat) (c : Q') (p q : RatPoly) :
    finiteHaarPair blocks (polySmul c p) q ≈
      c * finiteHaarPair blocks p q := by
  unfold finiteHaarPair
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p q))
    (quaternionHaar_polySmul blocks c (polyMul p q))

theorem finiteHaarPair_nonnegative (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    (0 : Q') ≤ finiteHaarPair blocks p p :=
  by
    unfold finiteHaarPair
    exact quaternionHaar_square_nonnegative blocks p hp

theorem finiteHaarUnit_pairing (blocks : Nat) :
    finiteHaarPair blocks polyOne polyOne ≈ (1 : Q') := by
  unfold finiteHaarPair
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.one_mul polyOne))
    (haar_one blocks)

private theorem finiteHaar_support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem finiteHaar_zero_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 0 polyOne) p) p :=
  ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl p)).trans
    (RatPolyCoeffEqv.zero_add p)

private theorem finiteHaar_neg_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul (-1) p) p) (polySmul 0 polyOne) :=
  (RatPolyCoeffEqv.add_comm _ _).trans
    ((RatPolyCoeffEqv.add_neg_smul p).trans
      (RatPolyCoeffEqv.zero_smul polyOne).symm)

/-! ## Packaging as one genuine finite GNS datum -/

/-- The supported finite polynomial carrier with its ordinary Haar form. -/
def finiteHaarGNSData (blocks : Nat) : GNSData where
  V := {p : RatPoly // SupportedQuaternionBlocks blocks p}
  veq := fun p q => RatPolyCoeffEqv p.val q.val
  veq_refl := fun p => RatPolyCoeffEqv.refl p.val
  veq_symm := fun h => h.symm
  veq_trans := fun h h' => h.trans h'
  zero := ⟨polySmul 0 polyOne, finiteHaar_support_smul (supported_one blocks) 0⟩
  add := fun p q => ⟨polyAdd p.val q.val, supported_add p.property q.property⟩
  neg := fun p => ⟨polySmul (-1) p.val, finiteHaar_support_smul p.property (-1)⟩
  smul := fun c p => ⟨polySmul c p.val, finiteHaar_support_smul p.property c⟩
  add_congr := fun h h' => h.add h'
  neg_congr := fun h => h.smul (-1)
  smul_congr := fun c {_ _} h => h.smul c
  add_assoc := fun p q r => RatPolyCoeffEqv.add_assoc p.val q.val r.val
  add_comm := fun p q => RatPolyCoeffEqv.add_comm p.val q.val
  zero_add := fun p => finiteHaar_zero_add p.val
  neg_add := fun p => finiteHaar_neg_add p.val
  B := fun p q => finiteHaarPair blocks p.val q.val
  B_congr_left := fun q h => by
    unfold finiteHaarPair
    exact haar_of_coeff (h.mul_right q.val)
  B_add_left := fun p q r => finiteHaarPair_add_left blocks p.val q.val r.val
  B_smul_left := fun c p q => finiteHaarPair_smul_left blocks c p.val q.val
  B_symm := fun p q => finiteHaarPair_symm blocks p.val q.val
  self_nonneg := fun p => finiteHaarPair_nonnegative blocks p.val p.property

/-- The finite ordinary-Haar GNS quotient carrier. -/
abbrev finiteHaarQuotient (blocks : Nat) : Type :=
  (finiteHaarGNSData blocks).QuotSpace

/-- The class of a supported polynomial in the finite Haar quotient. -/
def finiteHaarClass (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) : finiteHaarQuotient blocks :=
  (finiteHaarGNSData blocks).qmk ⟨p, hp⟩

/-- The normalized finite constant class, retained as the vacuum seed. -/
def finiteHaarUnitClass (blocks : Nat) : finiteHaarQuotient blocks :=
  finiteHaarClass blocks polyOne (supported_one blocks)

theorem finiteHaar_qInner_mk (blocks : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    (finiteHaarGNSData blocks).qInner
        (finiteHaarClass blocks p hp) (finiteHaarClass blocks q hq) =
      Quotient.mk qSetoid (finiteHaarPair blocks p q) := by
  rfl

theorem finiteHaar_qInner_posdef (blocks : Nat)
    (q : finiteHaarQuotient blocks) :
    (finiteHaarGNSData blocks).qInner q q = QR.zero ↔
      q = (finiteHaarGNSData blocks).qZero := by
  exact (finiteHaarGNSData blocks).qInner_posdef q

theorem finiteHaar_cauchySchwarz (blocks : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    finiteHaarPair blocks p q * finiteHaarPair blocks p q ≤
      finiteHaarPair blocks p p * finiteHaarPair blocks q q :=
  (finiteHaarGNSData blocks).cauchy_schwarz ⟨p, hp⟩ ⟨q, hq⟩

end YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier

#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier.finiteHaarPair
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier.finiteHaarPair_symm
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier.finiteHaarPair_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier.finiteHaarGNSData
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier.finiteHaar_qInner_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier.finiteHaar_qInner_posdef
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier.finiteHaar_cauchySchwarz
