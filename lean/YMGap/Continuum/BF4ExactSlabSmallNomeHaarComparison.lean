/-
# Local small-nome comparisons for the ORIGINAL shared-link action

At every physical face, cutoff and slab extent, the original heat remainder
has a constructed two-sided Haar certificate with cap delta(w). Multiplying
by any positive-certificate background retains all shared link variables.
Thus inserting one original face changes the background integral by factors
between 1-delta(w) and 1+delta(w), independently of the background's size.

When delta(w) <= 1, certificates for all finite products of original heat
factors are constructed here, so the background premise is discharged for
the original action. The small-nome guard is explicit; there is no claim of
uniformity in the coupling, decay in separation, or a physical spectral gap.
-/

import YMGap.Continuum.QuaternionHaarCharacterInterval
import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

namespace YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BondMovingStep

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half)

/-- Same original face, at every cutoff; no syntactic coefficient radius. -/
def faceRemainderInterval (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) :
    Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 K) (heatRemainderBound w) :=
  (Interval.finiteRange (fun i => faceHeatTerm w extent id (1+i)) (fun i => heatTermBound w (1+i))
    (fun i => Interval.smul (coeffW w (1+i)) (coeffW_nonneg hw0 _)
      (characterInterval (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi))) (1+i))) K).weaken
    (heatPositiveLabels_bound hw0 hw1 hsmall K)

/-- Positivity of the actual character prefix, not of an auxiliary law. -/
def faceCertificate (hdelta : heatRemainderBound w ≤ 1)
    (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) :
    Certificate (boundaryCompleteSlabLinks extent).length (faceHeatPolynomial w K extent id) :=
  .ofCoeff ((faceHeat_eq_one_add w extent id K).trans
    ((RatPolyCoeffEqv.one_smul polyOne).symm.add (RatPolyCoeffEqv.refl _)))
    ((faceRemainderInterval hw0 hw1 hsmall extent id hi K).weaken hdelta).lower

/-- Every original finite face background gets an actual certificate. -/
def faceProductCertificate (hdelta : heatRemainderBound w ≤ 1) (K extent : Nat) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    Certificate (boundaryCompleteSlabLinks extent).length (polynomialProduct (faceHeatPolynomial w K extent) ids)
  | [], _ => .one _
  | id :: ids, hi => (faceCertificate hw0 hw1 hsmall hdelta extent id (hi id List.mem_cons_self) K).mul
      (faceProductCertificate hdelta K extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def fullActionCertificate (hdelta : heatRemainderBound w ≤ 1) (K half : Nat) :
    Certificate (boundaryCompleteSlabLinks (centralExtent half)).length (fullHeatProduct w K half) :=
  faceProductCertificate hw0 hw1 hsmall hdelta K _ _ (fun _ hi => hi)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_add (blocks : Nat) (p q : RatPoly) :
    quaternionHaar blocks (polyAdd p q) ≈ quaternionHaar blocks p + quaternionHaar blocks q :=
  quaternionHaar_append blocks p q

private theorem haar_cap_product (blocks : Nat) (c : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul p (cap c)) ≈ c*quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm p (cap c)).trans (cap_mul_left c p)))
    (quaternionHaar_polySmul blocks c p)

private def env3 (p c r : RatPoly) : Nat → RatPoly
  | 0 => p | 1 => c | _ => r

private theorem interval_integral_upper {blocks : Nat} {p r : RatPoly} {d : Q'}
    (P : Certificate blocks p) (R : Interval blocks r d) :
    quaternionHaar blocks (polyMul p r) ≤ d*quaternionHaar blocks p := by
  have h := (P.mul R.upper).haar_nonnegative
  have he : quaternionHaar blocks (polyMul p (polyAdd (cap d) (polyNeg r))) ≈
      d*quaternionHaar blocks p + -(quaternionHaar blocks (polyMul p r)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (by decide) (env3 p (cap d) r)))
      (Q'.eqv_trans _ _ _ (haar_add _ _ _) (Q'.add_eqv_congr' (haar_cap_product _ _ _) (haar_neg _ _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))

private theorem interval_integral_lower {blocks : Nat} {p r : RatPoly} {d : Q'}
    (P : Certificate blocks p) (R : Interval blocks r d) :
    -(d*quaternionHaar blocks p) ≤ quaternionHaar blocks (polyMul p r) := by
  have h := (P.mul R.lower).haar_nonnegative
  have he : quaternionHaar blocks (polyMul p (polyAdd (cap d) r)) ≈
      quaternionHaar blocks (polyMul p r) + d*quaternionHaar blocks p :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.var 2)))
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 1))) (by decide) (env3 p (cap d) r)))
      (Q'.eqv_trans _ _ _ (haar_add _ _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_cap_product _ _ _)))
  exact Q'.neg_le_of_zero_le_add (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))

private theorem face_product_split (extent id K : Nat) (p : RatPoly) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (faceHeatPolynomial w K extent id)) ≈
      quaternionHaar (boundaryCompleteSlabLinks extent).length p +
      quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (faceHeatTail w extent id 1 K)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (((RatPolyCoeffEqv.refl p).mul (faceHeat_eq_one_add w extent id K)).trans
    ((RatPolyCoeffEqv.mul_add_right _ _ _).trans ((RatPolyCoeffEqv.mul_one p).add (RatPolyCoeffEqv.refl _)))))
    (haar_add _ _ _)

include hw0 hw1 hsmall

/-- One-face upper comparison on the original carrier, for any positive background. -/
theorem insertFace_upper (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat)
    {p : RatPoly} (P : Certificate (boundaryCompleteSlabLinks extent).length p) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (faceHeatPolynomial w K extent id)) ≤
      (1+heatRemainderBound w)*quaternionHaar (boundaryCompleteSlabLinks extent).length p := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (face_product_split extent id K p))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _
      (interval_integral_upper P (faceRemainderInterval hw0 hw1 hsmall extent id hi K)))
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.add (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.add (.const 1) (.var 1)) (.var 0)) (by decide)
        (fun i => if i = 0 then quaternionHaar (boundaryCompleteSlabLinks extent).length p else heatRemainderBound w))))

/-- One-face lower comparison with the SAME background integral. -/
theorem insertFace_lower (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat)
    {p : RatPoly} (P : Certificate (boundaryCompleteSlabLinks extent).length p) :
    (1 + -heatRemainderBound w)*quaternionHaar (boundaryCompleteSlabLinks extent).length p ≤
      quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (faceHeatPolynomial w K extent id)) := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)) (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
    (by decide) (fun i => if i = 0 then quaternionHaar (boundaryCompleteSlabLinks extent).length p else heatRemainderBound w)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _
      (interval_integral_lower P (faceRemainderInterval hw0 hw1 hsmall extent id hi K)))
      (Q'.ge_of_eqv (face_product_split extent id K p)))

/-- Fully discharged background: any finite collection of actual original faces.
The comparison factors depend on w, not on K, extent, or the number of faces. -/
theorem originalBackground_comparison (hdelta : heatRemainderBound w ≤ 1) (extent K id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges extent) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent) :
    let p := polynomialProduct (faceHeatPolynomial w K extent) ids
    (1 + -heatRemainderBound w)*quaternionHaar (boundaryCompleteSlabLinks extent).length p ≤
      quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (faceHeatPolynomial w K extent id)) ∧
    quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (faceHeatPolynomial w K extent id)) ≤
      (1+heatRemainderBound w)*quaternionHaar (boundaryCompleteSlabLinks extent).length p :=
  ⟨insertFace_lower hw0 hw1 hsmall extent id hi K (faceProductCertificate hw0 hw1 hsmall hdelta K extent ids hids),
   insertFace_upper hw0 hw1 hsmall extent id hi K (faceProductCertificate hw0 hw1 hsmall hdelta K extent ids hids)⟩

/-- Explicit finite-product floor. Unlike the ONE-face comparison factor,
this floor depends on the number of faces and is not volume-uniform. -/
theorem faceProduct_floor (hdelta : heatRemainderBound w ≤ 1) (K extent : Nat) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    (1 + -heatRemainderBound w)^ids.length ≤
      quaternionHaar (boundaryCompleteSlabLinks extent).length (polynomialProduct (faceHeatPolynomial w K extent) ids)
  | [], _ => Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
      (Q'.eqv_of_eq (Q'.add_zero' 1)))
  | id :: ids, hi => by
      have hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent := fun j hj => hi j (List.mem_cons_of_mem id hj)
      have h := insertFace_lower hw0 hw1 hsmall extent id (hi id List.mem_cons_self) K
        (faceProductCertificate hw0 hw1 hsmall hdelta K extent ids hids)
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (faceProduct_floor hdelta K extent ids hids) (Q'.sub_nonneg_of_le hdelta))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

theorem fullAction_floor (hdelta : heatRemainderBound w ≤ 1) (K half : Nat) :
    (1 + -heatRemainderBound w)^(slabPhysicalFaceEdges (centralExtent half)).length ≤
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (fullHeatProduct w K half) :=
  faceProduct_floor hw0 hw1 hsmall hdelta K _ _ (fun _ hi => hi)

omit hw0 hw1 hsmall in
/-- The already-used exact-rational pilot lies strictly inside both guards. -/
theorem existingNome_guards :
    heatRatio BF4ExactSlabPlaquetteSmallNomeCertificate.nome ≤ HalfPow.half ∧
      heatRemainderBound BF4ExactSlabPlaquetteSmallNomeCertificate.nome < (1 : Q') := by decide

end YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison

#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.faceRemainderInterval
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.faceCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.faceProductCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.fullActionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.insertFace_upper
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.insertFace_lower
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.originalBackground_comparison
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.faceProduct_floor
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.fullAction_floor
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison.existingNome_guards
