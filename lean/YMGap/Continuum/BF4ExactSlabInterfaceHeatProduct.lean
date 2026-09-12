/-
# The exact BF4 interface insertion is the product of its face heat kernels

Finite distributivity over the ORIGINAL bounded labelling enumeration turns
the fixed-interface sum into 24 independent local character sums. The proof
is symbolic at every spin cutoff: no global label carrier is enumerated.

The resulting face factors retain their actual noncommutative plaquette
holonomies and heat coefficients. Coefficient-probe equality carries this
product into the same signed bilinear and quadratic Haar forms. This is not
pointwise or reflection positivity; the positive reflected-channel expansion
and its physical geometry pins remain to be proved.
-/

import YMGap.Continuum.BF4ExactSlabObservableHaarForm

namespace YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs ++ ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by simp only [List.cons_append, finitePolySum, sum_append f xs ys, polyAdd, List.append_assoc]

private theorem sum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, finitePolySum, sum_map f g xs]

private theorem sum_flatMap {A B : Type} (f : B → RatPoly) (g : A → List B) : ∀ xs : List A,
    finitePolySum f (xs.flatMap g) = finitePolySum (fun a => finitePolySum f (g a)) xs
  | [] => rfl
  | _ :: xs => by simp only [List.flatMap_cons, sum_append, sum_flatMap f g xs, finitePolySum]

private theorem sum_congr_on {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → RatPolyCoeffEqv (f a) (g a)) →
      RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => RatPolyCoeffEqv.refl _
  | a :: xs, h => (h a List.mem_cons_self).add
      (sum_congr_on f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem sum_mul_right {A : Type} (f : A → RatPoly) (p : RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul (finitePolySum f xs) p)
      (finitePolySum (fun a => polyMul (f a) p) xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => by
    change RatPolyCoeffEqv (polyMul (polyAdd (f a) (finitePolySum f xs)) p) _
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add (sum_mul_right f p xs)

private theorem mul_sum_right {A : Type} (p : RatPoly) (f : A → RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul p (finitePolySum f xs))
      (finitePolySum (fun a => polyMul p (f a)) xs)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | _ :: xs => (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (mul_sum_right p f xs))

/-- Product of local polynomial factors evaluated on one labelling. -/
def labelProduct (factor : Nat → Nat → RatPoly) (state : EdgeLabelling) : List Nat → RatPoly
  | [] => polyOne
  | id :: rest => polyMul (factor id (state id)) (labelProduct factor state rest)

/-- Product of independent local sums over the same spin range `0,...,K`. -/
def facewiseProduct (K : Nat) (factor : Nat → Nat → RatPoly) : List Nat → RatPoly
  | [] => polyOne
  | id :: rest => polyMul (finitePolySum (factor id) (List.range (K + 1)))
      (facewiseProduct K factor rest)

private theorem labelProduct_congr (factor : Nat → Nat → RatPoly)
    (left right : EdgeLabelling) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id = right id) →
      labelProduct factor left ids = labelProduct factor right ids
  | [], _ => rfl
  | id :: rest, h => by
    simp only [labelProduct, h id List.mem_cons_self,
      labelProduct_congr factor left right rest (fun j hj => h j (List.mem_cons_of_mem id hj))]

/-- Exact Cartesian distributivity over the library's actual bounded label
enumerator. Distinct face IDs are the only combinatorial hypothesis. -/
theorem bounded_label_sum_product (K : Nat) (factor : Nat → Nat → RatPoly) :
    ∀ ids : List Nat, ids.Nodup →
      RatPolyCoeffEqv
        (finitePolySum (fun state => labelProduct factor state ids) (boundedEdgeLabellings K ids))
        (facewiseProduct K factor ids)
  | [], _ => RatPolyCoeffEqv.add_zero polyOne
  | id :: rest, hnodup => by
    have hn := List.nodup_cons.mp hnodup
    have hcell (spin : Nat) (state : EdgeLabelling) :
        labelProduct factor (setEdgeLabel state id spin) (id :: rest) =
          polyMul (factor id spin) (labelProduct factor state rest) := by
      change polyMul (factor id (if id = id then spin else state id))
        (labelProduct factor (setEdgeLabel state id spin) rest) = _
      rw [if_pos rfl, labelProduct_congr factor (setEdgeLabel state id spin) state rest]
      intro j hj
      apply if_neg
      intro heq
      subst j
      exact hn.1 hj
    simp only [boundedEdgeLabellings, sum_flatMap, sum_map, hcell]
    refine (sum_congr_on _ (fun spin => polyMul (factor id spin) (facewiseProduct K factor rest))
      (List.range (K + 1)) (fun spin _ => ?_)).trans ?_
    · exact (mul_sum_right (factor id spin) (fun state => labelProduct factor state rest)
        (boundedEdgeLabellings K rest)).symm.trans
        ((bounded_label_sum_product K factor rest hn.2).mul_left _)
    · exact (sum_mul_right (factor id) (facewiseProduct K factor rest) (List.range (K + 1))).symm

private def localFaceTerm (w : Q') (K id spin : Nat) : RatPoly :=
  polySmul (coeffAt (heatKernelPacket K w) spin)
    (characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar spin)

/-- The finite heat character polynomial of the literal named plaquette. -/
def faceHeatPolynomial (w : Q') (K id : Nat) : RatPoly :=
  finitePolySum (localFaceTerm w K id) (List.range (K + 1))

/-- Local packet coefficients are exactly the original dimension/Casimir
heat coefficients on every retained spin. -/
theorem faceHeatPolynomial_eq_heat_sum (w : Q') (K id : Nat) :
    RatPolyCoeffEqv (faceHeatPolynomial w K id)
      (finitePolySum (fun spin => polySmul (coeffW w spin)
        (characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar spin))
        (List.range (K + 1))) := by
  apply sum_congr_on
  intro spin hspin
  unfold localFaceTerm
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]
  exact RatPolyCoeffEqv.refl _

/-- The actual 24-face interface heat product, on the original link carrier. -/
def interfaceHeatProduct (w : Q') (K : Nat) : RatPoly :=
  (centralFixedFaceIds 0).foldr (fun id p => polyMul (faceHeatPolynomial w K id) p) polyOne

private theorem labelProduct_eq_fold (factor : Nat → Nat → RatPoly) (state : EdgeLabelling)
    (ids : List Nat) : labelProduct factor state ids =
      ids.foldr (fun id p => polyMul (factor id (state id)) p) polyOne := by
  induction ids with
  | nil => rfl
  | cons _ _ ih => simp only [labelProduct, List.foldr, ih]

private theorem facewiseProduct_eq_fold (K : Nat) (factor : Nat → Nat → RatPoly)
    (ids : List Nat) : facewiseProduct K factor ids =
      ids.foldr (fun id p => polyMul (finitePolySum (factor id) (List.range (K + 1))) p) polyOne := by
  induction ids with
  | nil => rfl
  | cons _ _ ih => simp only [facewiseProduct, List.foldr, ih]

/-- No global boundary-channel enumeration remains: the ORIGINAL interface
insertion is coefficient-equivalent to the product of its 24 heat factors. -/
theorem interfaceHeatInsertion_eq_product (w : Q') (K : Nat) :
    RatPolyCoeffEqv (interfaceHeatInsertion w K) (interfaceHeatProduct w K) := by
  have hlabel (state : EdgeLabelling) : interfacePolynomial w K state =
      labelProduct (localFaceTerm w K) state (centralFixedFaceIds 0) := by
    rw [interfacePolynomial_eq_fold, labelProduct_eq_fold]
    rfl
  unfold interfaceHeatInsertion centralBoundaryChannels
  rw [funext hlabel]
  have h := bounded_label_sum_product K (localFaceTerm w K) (centralFixedFaceIds 0) (by decide)
  rw [facewiseProduct_eq_fold] at h
  exact h

/-- The product insertion can replace the sum before integration, with
arbitrary signed lower and upper observable coefficients. -/
theorem observableIntegrand_eq_product (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    RatPolyCoeffEqv (observableIntegrand w K left right)
      (polyMul (lowerObservable w K left)
        (polyMul (interfaceHeatProduct w K) (upperObservable w K right))) :=
  ((interfaceHeatInsertion_eq_product w K).mul_right _).mul_left _

private theorem haar_eq_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: rest => by unfold quaternionHaar ratWeightedSum; rw [haar_eq_weighted blocks rest]

/-- Exact same-law bilinear formula with the literal local heat product. -/
theorem exact_bilinear_eq_productHaar (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K 0) left right (exactCorrectedSlabReflectedKernel w K 0) ≈
      quaternionHaar 116 (polyMul (lowerObservable w K left)
        (polyMul (interfaceHeatProduct w K) (upperObservable w K right))) := by
  refine Q'.eqv_trans _ _ _ (exact_bilinear_eq_haar w K left right) ?_
  rw [haar_eq_weighted, haar_eq_weighted]
  exact observableIntegrand_eq_product w K left right (quaternionHaarMono 116)

theorem exact_quadratic_eq_productHaar (w : Q') (K : Nat) (coefficient : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K coefficient ≈
      quaternionHaar 116 (polyMul (lowerObservable w K coefficient)
        (polyMul (interfaceHeatProduct w K) (upperObservable w K coefficient))) :=
  exact_bilinear_eq_productHaar w K coefficient coefficient

end YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct

#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.labelProduct
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.facewiseProduct
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.bounded_label_sum_product
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.faceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.faceHeatPolynomial_eq_heat_sum
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.interfaceHeatProduct
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.interfaceHeatInsertion_eq_product
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.observableIntegrand_eq_product
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.exact_bilinear_eq_productHaar
#print axioms YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct.exact_quadratic_eq_productHaar
