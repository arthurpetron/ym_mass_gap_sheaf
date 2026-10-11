/-
# Direct finite-prefix Haar floor for the original shared-link slab action

The literal corrected slab link is either its assigned rational unit
quaternion or the identity. Coefficientwise quaternion norm identities give
pointwise unit norm for the ORIGINAL ordered plaquette word. Consequently its
scalar lies in [-1,1] on every explicit unit-quaternion assignment.

The original finite-prefix pointwise floor and finite-product Haar order then
give `finiteFloor(w)^ids.length` below the actual shared-link heat-product
integral. No factor independence or pointwise consequence of HaarCarrierEqv
is used. Lists may overlap and repeat faces. This is a direct finite-prefix
proof, not the first original-action positivity result: the existing
comparison-based floor and cutoff remain unchanged. No algebraic positivity
Certificate, H1 estimate, gap, or continuum claim is made.
-/

import YMGap.Continuum.QuaternionHaarFiniteProductOrder
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
import YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.BF4ExactSlabAllExtentActionLimit

namespace YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionNormRepair (coordinate coordinate_square_le)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq evalMono)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_var evalRatPoly_one)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics (polyQuaternionNorm)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment environment_coordinate)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail (faceScalar)
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit (heatProductHaar)
open YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor (productFloor productFloor_pos)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*evalMono rho t.1+z) (weighted_eval rho p)

private theorem eval_congr (rho : Nat → Q') {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    evalRatPoly rho p ≈ evalRatPoly rho q := by
  simpa only [weighted_eval] using h (evalMono rho)

private def value (rho : Nat → Q') (p : PolyQuaternion) : RationalQuaternion :=
  ⟨evalRatPoly rho p.scalar, evalRatPoly rho p.iPart,
    evalRatPoly rho p.jPart, evalRatPoly rho p.kPart⟩

private theorem norm_eval (rho : Nat → Q') (p : PolyQuaternion) :
    evalRatPoly rho (polyQuaternionNorm p) ≈ normSq (value rho p) := by
  have h := Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
    (Q'.add_eqv_congr' (evalRatPoly_mul rho p.scalar p.scalar)
      (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
        (Q'.add_eqv_congr' (evalRatPoly_mul rho p.iPart p.iPart)
          (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
            (Q'.add_eqv_congr' (evalRatPoly_mul rho p.jPart p.jPart)
              (evalRatPoly_mul rho p.kPart p.kPart))))))
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem coordinate_norm_one (qs : Nat → UnitNorm) (block : Nat) :
    evalRatPoly (environment qs) (polyQuaternionNorm (PolyQuaternion.coordinateVariable block)) ≈ 1 := by
  have hc (a : Fin 4) : evalRatPoly (environment qs) (polyVar (4*block+a.val)) ≈
      coordinate (qs block).val a :=
    Q'.eqv_trans _ _ _ (evalRatPoly_var _ _) (Q'.eqv_of_eq (environment_coordinate qs block a))
  have hv : (value (environment qs) (PolyQuaternion.coordinateVariable block)).Equivalent (qs block).val := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [value, PolyQuaternion.coordinateVariable, coordinate, Nat.add_zero]
        using hc ⟨0,by decide⟩
    · simpa only [value, PolyQuaternion.coordinateVariable, coordinate]
        using hc ⟨1,by decide⟩
    · simpa only [value, PolyQuaternion.coordinateVariable, coordinate]
        using hc ⟨2,by decide⟩
    · simpa only [value, PolyQuaternion.coordinateVariable, coordinate]
        using hc ⟨3,by decide⟩
  exact Q'.eqv_trans _ _ _ (norm_eval _ _)
    (Q'.eqv_trans _ _ _ (normSq_congr hv) (qs block).unitNorm)

private theorem one_norm (rho : Nat → Q') :
    evalRatPoly rho (polyQuaternionNorm PolyQuaternion.one) ≈ 1 :=
  Q'.eqv_trans _ _ _ (eval_congr rho polyQuaternionNorm_one) (evalRatPoly_one rho)

private theorem mul_norm {rho : Nat → Q'} {p q : PolyQuaternion}
    (hp : evalRatPoly rho (polyQuaternionNorm p) ≈ 1)
    (hq : evalRatPoly rho (polyQuaternionNorm q) ≈ 1) :
    evalRatPoly rho (polyQuaternionNorm (PolyQuaternion.mul p q)) ≈ 1 :=
  Q'.eqv_trans _ _ _ (eval_congr rho (polyQuaternionNorm_mul p q))
    (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (Q'.eqv_trans _ _ _ (mc hp hq) (Q'.one_mul_eqv 1)))

private theorem conj_norm {rho : Nat → Q'} {p : PolyQuaternion}
    (hp : evalRatPoly rho (polyQuaternionNorm p) ≈ 1) :
    evalRatPoly rho (polyQuaternionNorm (PolyQuaternion.conj p)) ≈ 1 :=
  Q'.eqv_trans _ _ _ (eval_congr rho (polyQuaternionNorm_conj p)) hp

private theorem link_norm_one (extent : Nat) (qs : Nat → UnitNorm) (link : Z4Link) :
    evalRatPoly (environment qs) (polyQuaternionNorm (correctedSlabLinkPolynomial extent link)) ≈ 1 := by
  cases (inferInstance : Decidable (link ∈ boundaryCompleteSlabLinks extent)) with
  | isTrue h =>
      rw [correctedSlabLinkPolynomial_of_mem h]
      exact coordinate_norm_one qs _
  | isFalse h =>
      rw [correctedSlabLinkPolynomial_of_not_mem h]
      exact one_norm _

private theorem oriented_norm_one (extent : Nat) (qs : Nat → UnitNorm) (entry : OrientedBF4Link) :
    evalRatPoly (environment qs)
      (polyQuaternionNorm (orientedCorrectedSlabLinkPolynomial extent entry)) ≈ 1 := by
  unfold orientedCorrectedSlabLinkPolynomial
  cases entry.reverse
  · exact link_norm_one extent qs entry.link
  · exact conj_norm (link_norm_one extent qs entry.link)

private theorem fold_norm {A : Type} (rho : Nat → Q') (factor : A → PolyQuaternion)
    (hf : ∀ a, evalRatPoly rho (polyQuaternionNorm (factor a)) ≈ 1) :
    ∀ (xs : List A) (initial : PolyQuaternion),
      evalRatPoly rho (polyQuaternionNorm initial) ≈ 1 →
      evalRatPoly rho
        (polyQuaternionNorm (xs.foldl (fun total a => PolyQuaternion.mul total (factor a)) initial)) ≈ 1
  | [], _, hi => hi
  | a::xs, _, hi => fold_norm rho factor hf xs _ (mul_norm hi (hf a))

/-- Pointwise unit norm of the literal corrected plaquette, proved from
coefficient identities. This does not specialize a Haar-only equivalence. -/
theorem plaquette_norm_one (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    evalRatPoly (environment qs) (polyQuaternionNorm (correctedSlabPlaquettePolynomial extent face)) ≈ 1 :=
  fold_norm (environment qs) (orientedCorrectedSlabLinkPolynomial extent)
    (oriented_norm_one extent qs) (orientedPlaquetteBoundary face) PolyQuaternion.one (one_norm _)

private theorem abs_square (a : Q') : Q'.abs a*Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => a)

private theorem scalar_square_box (s : Q') (hs : s*s ≤ (1 : Q')) :
    (-1 : Q') ≤ s ∧ s ≤ (1 : Q') := by
  have has : Q'.abs s*Q'.abs s ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square s)) hs
  have has' : Q'.abs s*Q'.abs s ≤ (1 : Q')*1 :=
    Q'.le_trans' _ _ _ has (Q'.le_of_eqv (by decide : (1 : Q') ≈ 1*1))
  have ha : Q'.abs s ≤ (1 : Q') := CReal.le_of_sq_le_sq (by decide) (Q'.abs_nonneg s)
    has'
  exact ⟨Q'.le_trans' _ _ _ (Q'.neg_le_neg ha) (ExpNeg.neg_abs_le s),
    Q'.le_trans' _ _ _ (Q'.le_abs_self s) ha⟩

private theorem quaternion_scalar_box (q : RationalQuaternion) (hq : normSq q ≈ 1) :
    (-1 : Q') ≤ q.r ∧ q.r ≤ (1 : Q') := by
  have hc := coordinate_square_le q ⟨0,by decide⟩
  simp only [coordinate] at hc
  exact scalar_square_box q.r (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv hq))

private theorem scalar_box {rho : Nat → Q'} {p : PolyQuaternion}
    (hp : evalRatPoly rho (polyQuaternionNorm p) ≈ 1) :
    (-1 : Q') ≤ evalRatPoly rho p.scalar ∧ evalRatPoly rho p.scalar ≤ (1 : Q') :=
  quaternion_scalar_box (value rho p)
    (Q'.eqv_trans (normSq (value rho p)) (evalRatPoly rho (polyQuaternionNorm p)) 1
      (Q'.eqv_symm (norm_eval rho p)) hp)

/-- Every original face scalar is in its genuine unit-quaternion box,
for every explicit assignment on the shared slab links. -/
theorem faceScalar_box (extent id : Nat) (qs : Nat → UnitNorm) :
    (-1 : Q') ≤ evalRatPoly (environment qs) (faceScalar extent id) ∧
      evalRatPoly (environment qs) (faceScalar extent id) ≤ (1 : Q') :=
  scalar_box (plaquette_norm_one extent qs (Z4HalfTimeReflectionFaceReindex.slabPlaquetteAt extent id))

/-- Direct lower bound for the ORIGINAL shared-link finite heat product.
The cutoff is the original one-factor `finiteCutoff`; all selected factors
remain in the same polynomial and the same finite Haar functional. -/
theorem productFloor_le_heatProductHaar {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (ids : List Nat)
    (hK : SU2PointwiseHeatStrictFloor.finiteCutoff w ≤ K+1) :
    productFloor w ids ≤ heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K :=
  QuaternionHaarFiniteProductOrder.haar_lower_bound _ _
    (BF4ExactSlabFaceLinkLocality.heatProduct_supported w K extent ids) _
    (fun qs => BF4ExactSlabHeatPointwiseFloor.productFloor_le_eval_heatProduct
      hw0 hw1 K extent (environment qs) hK ids (fun id _ => faceScalar_box extent id qs))

/-- Strict positivity at this direct original-prefix cutoff, with the
face-count-dependent rational floor retained explicitly above. -/
theorem heatProductHaar_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (ids : List Nat)
    (hK : SU2PointwiseHeatStrictFloor.finiteCutoff w ≤ K+1) :
    (0 : Q') < heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K :=
  Q'.pos_of_lt_of_le (productFloor_pos hw0 hw1 ids)
    (productFloor_le_heatProductHaar hw0 hw1 K extent ids hK)

end YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder

#print axioms YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder.plaquette_norm_one
#print axioms YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder.faceScalar_box
#print axioms YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder.productFloor_le_heatProductHaar
#print axioms YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder.heatProductHaar_positive
