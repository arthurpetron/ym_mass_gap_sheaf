/-
# Sharp Cauchy--Schwarz with a constructed quaternion Haar weight

An existing square certificate for the weight constructs the positive
bilinear form on supported polynomials. The old GNS Cauchy--Schwarz theorem
therefore applies to the SAME weighted Haar integral, including shared
variables and signed polynomials. No pointwise positivity oracle is used.
-/

import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

namespace YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

def weightedPair (blocks : Nat) (W p q : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul (polyMul p q) W)

theorem weighted_symm (blocks : Nat) (W p q : RatPoly) :
    weightedPair blocks W p q ≈ weightedPair blocks W q p :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_comm p q).mul_right W)

theorem weighted_add_left (blocks : Nat) (W a b c : RatPoly) :
    weightedPair blocks W (polyAdd a b) c ≈ weightedPair blocks W a c + weightedPair blocks W b c := by
  unfold weightedPair
  rw [polyMul_add_left_exact, polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

theorem weighted_smul_left (blocks : Nat) (W : RatPoly) (c : Q') (p q : RatPoly) :
    weightedPair blocks W (polySmul c p) q ≈ c*weightedPair blocks W p q :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    (((RatPolyCoeffEqv.polyMul_smul_left c p q).mul_right W).trans (RatPolyCoeffEqv.polyMul_smul_left _ _ _)))
    (quaternionHaar_polySmul _ _ _)

private theorem support_smul {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem zero_add (p : RatPoly) : RatPolyCoeffEqv (polyAdd (polySmul 0 polyOne) p) p :=
  ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl p)).trans (RatPolyCoeffEqv.zero_add p)

private theorem neg_add (p : RatPoly) : RatPolyCoeffEqv (polyAdd (polySmul (-1) p) p) (polySmul 0 polyOne) :=
  (RatPolyCoeffEqv.add_comm _ _).trans
    ((RatPolyCoeffEqv.add_neg_smul p).trans (RatPolyCoeffEqv.zero_smul polyOne).symm)

/-- The analytic positive-form fields are proved from the supplied algebraic certificate. -/
def weightedGNSData (blocks : Nat) (W : RatPoly) (H : Certificate blocks W) : GNSData where
  V := {p : RatPoly // SupportedQuaternionBlocks blocks p}
  veq := fun p q => RatPolyCoeffEqv p.val q.val
  veq_refl := fun _ => RatPolyCoeffEqv.refl _
  veq_symm := fun h => h.symm
  veq_trans := fun h h' => h.trans h'
  zero := ⟨polySmul 0 polyOne, support_smul (supported_one blocks) 0⟩
  add := fun p q => ⟨polyAdd p.val q.val, supported_add p.property q.property⟩
  neg := fun p => ⟨polySmul (-1) p.val, support_smul p.property (-1)⟩
  smul := fun c p => ⟨polySmul c p.val, support_smul p.property c⟩
  add_congr := fun h h' => h.add h'
  neg_congr := fun h => h.smul (-1)
  smul_congr := fun c {_ _} h => h.smul c
  add_assoc := fun _ _ _ => RatPolyCoeffEqv.add_assoc _ _ _
  add_comm := fun _ _ => RatPolyCoeffEqv.add_comm _ _
  zero_add := fun p => zero_add p.val
  neg_add := fun p => neg_add p.val
  B := fun p q => weightedPair blocks W p.val q.val
  B_congr_left := fun q h => haar_of_coeff ((h.mul_right q.val).mul_right W)
  B_add_left := fun p q r => weighted_add_left blocks W p.val q.val r.val
  B_smul_left := fun c p q => weighted_smul_left blocks W c p.val q.val
  B_symm := fun p q => weighted_symm blocks W p.val q.val
  self_nonneg := fun p => H.square_insertion_nonnegative p.val p.property

theorem weighted_cauchySchwarz (blocks : Nat) (W p q : RatPoly) (H : Certificate blocks W)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    weightedPair blocks W p q * weightedPair blocks W p q ≤
      weightedPair blocks W p p * weightedPair blocks W q q :=
  (weightedGNSData blocks W H).cauchy_schwarz ⟨p,hp⟩ ⟨q,hq⟩

end YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

#print axioms YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz.weightedPair
#print axioms YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz.weighted_symm
#print axioms YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz.weighted_add_left
#print axioms YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz.weighted_smul_left
#print axioms YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz.weightedGNSData
#print axioms YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz.weighted_cauchySchwarz
