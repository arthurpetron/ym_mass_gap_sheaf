/-
# Computed reflection-compatible heat profiles in the ORIGINAL action

Specify lower-half nome/cutoff profiles and independent crossing profiles.
Upper faces use the actual reflected lower-face data. Every original heat
factor remains in the complete physical face list. The lower bulk product
is an explicit expression in the EXISTING plaquette algebra, not a new
observable or a supplied reflection hypothesis.

The original full reflected numerator equals the previous crossing-profile
form of that computed dressed expression. Positivity and per-face comparison
therefore concern this SAME full action. These finite identities supply no
cutoff/volume limit, OS-norm range estimate or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabProfileOriginalInterface
import YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression
import YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity

namespace YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression (faceExpression faceExpression_lower faceExpression_upper)
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity (reflectedInsertion)
open YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison
open YMGap.Continuum.BF4ExactSlabProfileOriginalInterface
open YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabLocalBulkSelection (profileHeat profileHeat_supported)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

/-- Upper data are computed from the actual reflected lower face. -/
def reflectedProfile {A : Type} (bulk crossing : Nat → A) (half id : Nat) : A :=
  match plaquetteHalfSide half (slabPlaquetteAt (centralExtent half) id) with
  | .lower => bulk id
  | .fixed => crossing id
  | .upper => bulk (slabFaceReflectId (centralExtent half) id)

theorem reflectedProfile_lower {A : Type} (bulk crossing : Nat → A) {half id : Nat}
    (hi : id ∈ centralLowerFaceIds half) : reflectedProfile bulk crossing half id = bulk id := by
  simp only [reflectedProfile,(mem_centralLowerFaceIds.mp hi).2]

theorem reflectedProfile_fixed {A : Type} (bulk crossing : Nat → A) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) : reflectedProfile bulk crossing half id = crossing id := by
  simp only [reflectedProfile,(mem_centralFixedFaceIds.mp hi).2]

theorem reflectedProfile_upper {A : Type} (bulk crossing : Nat → A) {half id : Nat}
    (hi : id ∈ centralUpperFaceIds half) :
    reflectedProfile bulk crossing half id = bulk (slabFaceReflectId (centralExtent half) id) := by
  simp only [reflectedProfile,(mem_centralUpperFaceIds.mp hi).2]

theorem reflectedProfile_constant {A : Type} (a : A) (half id : Nat) :
    reflectedProfile (fun _ => a) (fun _ => a) half id = a := by
  unfold reflectedProfile
  split <;> rfl

def profileExpression (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    (ids : List Nat) → (∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) → PlaquetteExpression half
  | [], _ => .unit
  | id::ids, hi => .mul (faceExpression (w id) (cutoff id) (hi id List.mem_cons_self))
      (profileExpression w cutoff half ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

theorem profileExpression_lower (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    (ids : List Nat) → (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) →
      RatPolyCoeffEqv (lower (profileExpression w cutoff half ids hi)) (profileHeat w cutoff (centralExtent half) ids)
  | [], _ => RatPolyCoeffEqv.refl _
  | id::ids, hi => (faceExpression_lower (w id) (cutoff id) (hi id List.mem_cons_self)).mul
      (profileExpression_lower w cutoff half ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

private theorem expression_upper (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    (ids : List Nat) → (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) →
      RatPolyCoeffEqv (upper (profileExpression w cutoff half ids hi))
        (polynomialProduct (fun id => faceHeatPolynomial (w id) (cutoff id) (centralExtent half)
          (slabFaceReflectId (centralExtent half) id)) ids)
  | [], _ => RatPolyCoeffEqv.refl _
  | id::ids, hi => (faceExpression_upper (w id) (cutoff id) (hi id List.mem_cons_self)).mul
      (expression_upper w cutoff half ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def lowerHeat (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) : RatPoly :=
  profileHeat w cutoff (centralExtent half) (centralLowerFaceIds half)

def upperHeat (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) : RatPoly :=
  profileHeat (fun id => w (slabFaceReflectId (centralExtent half) id))
    (fun id => cutoff (slabFaceReflectId (centralExtent half) id)) (centralExtent half) (centralUpperFaceIds half)

theorem profileExpression_upper (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    RatPolyCoeffEqv (upper (profileExpression w cutoff half (centralLowerFaceIds half) (fun _ h => h)))
      (upperHeat w cutoff half) := by
  let f := fun id => faceHeatPolynomial (w (slabFaceReflectId (centralExtent half) id))
    (cutoff (slabFaceReflectId (centralExtent half) id)) (centralExtent half) id
  have hperm := polynomialProduct_perm f (reflected_lower_ids half)
  simp only [polynomialProduct,List.foldr_map] at hperm
  have he : polynomialProduct (fun id => faceHeatPolynomial (w id) (cutoff id) (centralExtent half)
      (slabFaceReflectId (centralExtent half) id)) (centralLowerFaceIds half) =
      polynomialProduct (fun id => f (slabFaceReflectId (centralExtent half) id)) (centralLowerFaceIds half) := by
    apply polynomialProduct_congr
    intro id hi
    simp only [f,slabFaceReflectId_involutive (mem_centralLowerFaceIds.mp hi).1]
  have h := expression_upper w cutoff half (centralLowerFaceIds half) (fun _ hi => hi)
  rw [he] at h
  exact h.trans hperm

def fullHeat (bulk : Nat → Q') (bulkCutoff : Nat → Nat) (crossing : Nat → Q')
    (crossingCutoff : Nat → Nat) (half : Nat) : RatPoly :=
  profileHeat (reflectedProfile bulk crossing half) (reflectedProfile bulkCutoff crossingCutoff half)
    (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))

theorem fullHeat_split (bulk : Nat → Q') (bulkCutoff : Nat → Nat) (crossing : Nat → Q')
    (crossingCutoff : Nat → Nat) (half : Nat) :
    RatPolyCoeffEqv (fullHeat bulk bulkCutoff crossing crossingCutoff half)
      (polyMul (lowerHeat bulk bulkCutoff half)
        (polyMul (profileHeat crossing crossingCutoff (centralExtent half) (centralFixedFaceIds half))
          (upperHeat bulk bulkCutoff half))) := by
  let f := fun id => faceHeatPolynomial (reflectedProfile bulk crossing half id)
    (reflectedProfile bulkCutoff crossingCutoff half id) (centralExtent half) id
  have hl : polynomialProduct f (centralLowerFaceIds half) = lowerHeat bulk bulkCutoff half := by
    apply polynomialProduct_congr
    intro id hi
    simp only [f,reflectedProfile_lower _ _ hi]
  have hi : polynomialProduct f (centralFixedFaceIds half) =
      profileHeat crossing crossingCutoff (centralExtent half) (centralFixedFaceIds half) := by
    apply polynomialProduct_congr
    intro id hi
    simp only [f,reflectedProfile_fixed _ _ hi]
  have hu : polynomialProduct f (centralUpperFaceIds half) = upperHeat bulk bulkCutoff half := by
    apply polynomialProduct_congr
    intro id hi
    simp only [f,reflectedProfile_upper _ _ hi]
  have h := central_product_factorization half f
  rw [hl,hi,hu] at h
  exact h

def dressedExpression (bulk : Nat → Q') (bulkCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) :
    PlaquetteExpression half := .mul e (profileExpression bulk bulkCutoff half (centralLowerFaceIds half) (fun _ hi => hi))

def fullQuadratic (bulk : Nat → Q') (bulkCutoff : Nat → Nat) (crossing : Nat → Q')
    (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  quaternionHaar (blocks half) (polyMul (reflectedInsertion e) (fullHeat bulk bulkCutoff crossing crossingCutoff half))

/-- The COMPLETE original reflected action becomes an expression in the old algebra. -/
theorem fullQuadratic_expression (bulk : Nat → Q') (bulkCutoff : Nat → Nat) (crossing : Nat → Q')
    (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) :
    fullQuadratic bulk bulkCutoff crossing crossingCutoff e ≈
      originalForm crossing crossingCutoff (dressedExpression bulk bulkCutoff e) := by
  let E := dressedExpression bulk bulkCutoff e
  let H := fullHeat bulk bulkCutoff crossing crossingCutoff half
  let I := profileHeat crossing crossingCutoff (centralExtent half) (centralFixedFaceIds half)
  have hH := profileHeat_supported (reflectedProfile bulk crossing half)
    (reflectedProfile bulkCutoff crossingCutoff half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
  have hI := profileHeat_supported crossing crossingCutoff (centralExtent half) (centralFixedFaceIds half)
  have he := (PaddedPolynomialCoeffEqv.mul (lower_reflection e) (PaddedPolynomialCoeffEqv.refl (blocks half) (lower e))).mul
    (PaddedPolynomialCoeffEqv.refl _ H)
  have hE := (PaddedPolynomialCoeffEqv.mul (lower_reflection E) (PaddedPolynomialCoeffEqv.refl (blocks half) (lower E))).mul
    (PaddedPolynomialCoeffEqv.refl _ I)
  have hleft := he.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (lower_supported e)) hH)
    (supported_polyMul (supported_polyMul (upper_supported e) (lower_supported e)) hH)
  have hright := hE.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (lower_supported E)) hI)
    (supported_polyMul (supported_polyMul (upper_supported E) (lower_supported E)) hI)
  have hL : RatPolyCoeffEqv (lower E) (polyMul (lower e) (lowerHeat bulk bulkCutoff half)) :=
    (RatPolyCoeffEqv.refl _).mul (profileExpression_lower bulk bulkCutoff half _ _)
  have hU : RatPolyCoeffEqv (upper E) (polyMul (upper e) (upperHeat bulk bulkCutoff half)) :=
    (RatPolyCoeffEqv.refl _).mul (profileExpression_upper bulk bulkCutoff half)
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul (upper e) (upperHeat bulk bulkCutoff half))
        (polyMul (lower e) (lowerHeat bulk bulkCutoff half))) I)
      (polyMul (polyMul (upper e) (lower e))
        (polyMul (lowerHeat bulk bulkCutoff half) (polyMul I (upperHeat bulk bulkCutoff half)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4))))
      (by decide) (fun | 0 => upper e | 1 => lower e | 2 => lowerHeat bulk bulkCutoff half | 3 => I | _ => upperHeat bulk bulkCutoff half)
  have hcoeff := ((hU.mul hL).mul_right I).trans
    (hr.trans ((fullHeat_split bulk bulkCutoff crossing crossingCutoff half).symm.mul_left _))
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff_eqv _ hcoeff)) (Q'.eqv_symm hright))

theorem fullQuadratic_gram (bulk : Nat → Q') (bulkCutoff : Nat → Nat) (crossing : Nat → Q')
    (hc : ∀ id,(0 : Q') ≤ crossing id) (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) :
    fullQuadratic bulk bulkCutoff crossing crossingCutoff e ≈
      profileForm crossing crossingCutoff half (lower (dressedExpression bulk bulkCutoff e)) :=
  Q'.eqv_trans _ _ _ (fullQuadratic_expression bulk bulkCutoff crossing crossingCutoff e)
    (originalForm_pin crossing hc crossingCutoff _)

theorem fullQuadratic_nonnegative (bulk : Nat → Q') (bulkCutoff : Nat → Nat) (crossing : Nat → Q')
    (hc : ∀ id,(0 : Q') ≤ crossing id) (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) :
    (0 : Q') ≤ fullQuadratic bulk bulkCutoff crossing crossingCutoff e :=
  Q'.le_trans' _ _ _ (originalForm_nonnegative crossing hc crossingCutoff _)
    (Q'.ge_of_eqv (fullQuadratic_expression bulk bulkCutoff crossing crossingCutoff e))

/-- Same full bulk action, with only the crossing coefficients compared. -/
theorem fullQuadratic_comparison (bulk : Nat → Q') (bulkCutoff : Nat → Nat)
    (a b c : Nat → Q') (ha : ∀ id,(0 : Q') ≤ a id) (hb : ∀ id,(0 : Q') ≤ b id)
    (hc : ∀ id,(0 : Q') ≤ c id) (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half)
    (hcoeff : ∀ id,id ∈ centralFixedFaceIds half → ∀ s,s ≤ crossingCutoff id → c id * coeffW (a id) s ≤ coeffW (b id) s) :
    factorProduct c (centralFixedFaceIds half) * fullQuadratic bulk bulkCutoff a crossingCutoff e ≤
      fullQuadratic bulk bulkCutoff b crossingCutoff e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (fullQuadratic_expression bulk bulkCutoff a crossingCutoff e)))
    (Q'.le_trans' _ _ _ (originalForm_comparison a b c ha hb hc crossingCutoff _ hcoeff)
      (Q'.ge_of_eqv (fullQuadratic_expression bulk bulkCutoff b crossingCutoff e)))

/-- The explicit local floor now bounds the FULL reflection-compatible action.
Only selected crossing cutoffs are bounded; every bulk cutoff is arbitrary. -/
theorem fullQuadratic_local_lower (bulk : Nat → Q') (bulkCutoff : Nat → Nat)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (selected : Nat → Bool)
    (N : Nat) (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half)
    (hN : ∀ id,id ∈ centralFixedFaceIds half → selected id=true → crossingCutoff id ≤ N) :
    YMGap.Continuum.RGTransport.qpow w (N*(N+2)*changedFaceCount selected half) *
      fullQuadratic bulk bulkCutoff (referenceNome w selected) crossingCutoff e ≤
      fullQuadratic bulk bulkCutoff (fun _ => w) crossingCutoff e := by
  let E := dressedExpression bulk bulkCutoff e
  have h := local_lower_bounded w hw0 hw1 selected N half crossingCutoff hN (lower E)
    (lower_supported E) (lower_local E)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
    (fullQuadratic_gram bulk bulkCutoff (referenceNome w selected) (referenceNome_nonnegative w hw0 selected) crossingCutoff e)))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (fullQuadratic_gram bulk bulkCutoff (fun _ => w) (fun _ => hw0) crossingCutoff e)))

theorem fullQuadratic_local_upper (bulk : Nat → Q') (bulkCutoff : Nat → Nat)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (selected : Nat → Bool)
    (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) :
    fullQuadratic bulk bulkCutoff (fun _ => w) crossingCutoff e ≤
      fullQuadratic bulk bulkCutoff (referenceNome w selected) crossingCutoff e := by
  let E := dressedExpression bulk bulkCutoff e
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (fullQuadratic_gram bulk bulkCutoff (fun _ => w) (fun _ => hw0) crossingCutoff e))
    (Q'.le_trans' _ _ _ (local_upper w hw0 hw1 selected crossingCutoff half (lower E) (lower_supported E) (lower_local E))
      (Q'.ge_of_eqv (fullQuadratic_gram bulk bulkCutoff (referenceNome w selected) (referenceNome_nonnegative w hw0 selected) crossingCutoff e)))

theorem fullQuadratic_diagonal (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    fullQuadratic (fun _ => w) (fun _ => K) (fun _ => w) (fun _ => K) e =
      numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e) K := by
  have h : fullHeat (fun _ => w) (fun _ => K) (fun _ => w) (fun _ => K) half =
      polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (slabPhysicalFaceEdges (centralExtent half)) := by
    apply polynomialProduct_congr
    intro id _
    rw [reflectedProfile_constant,reflectedProfile_constant]
  unfold fullQuadratic numerator
  rw [h]

end YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles

#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.reflectedProfile
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.reflectedProfile_lower
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.reflectedProfile_fixed
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.reflectedProfile_upper
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.reflectedProfile_constant
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.profileExpression
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.profileExpression_lower
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.lowerHeat
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.upperHeat
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.profileExpression_upper
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullHeat
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullHeat_split
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.dressedExpression
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic_expression
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic_gram
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic_comparison
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic_local_lower
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic_local_upper
#print axioms YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles.fullQuadratic_diagonal
