/-
# Relative partition control for actual face-dependent heat factors

Each face has its own nome and representation cutoff. A common displayed
small-nome ceiling W supplies the remainder cap delta(W). Inserting a list
of faces costs only (1-delta(W))^length, relative to the SAME arbitrary
positive shared-link background. Actual varying heat products get positive
certificates, and the exact background partition square is retained.

This is an analytic input to heterogeneous connected resummation, not that
resummation or a spatial-mixing theorem. No continuum assertion is made.
-/
import YMGap.Continuum.BF4ExactSlabRelativePartitionBound
import YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity

namespace YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabRelativePartitionBound (removalFloor removalFloor_nonnegative)
open YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity (heatRatio_mono heatRemainderBound_mono)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

variable (w : Nat → Q') (K : Nat → Nat) (extent : Nat)

/-- The original ordered plaquette heat polynomial, with facewise parameters. -/
def factor (id : Nat) : RatPoly := faceHeatPolynomial (w id) (K id) extent id

def partition (ids : List Nat) : Q' :=
  quaternionHaar (blocks extent) (polynomialProduct (factor w K extent) ids)

variable {W : Q'}
  (hw0 : ∀ id, id ∈ slabPhysicalFaceEdges extent → (0 : Q') ≤ w id)
  (hwW : ∀ id, id ∈ slabPhysicalFaceEdges extent → w id ≤ W)
  (hW1 : W ≤ (1 : Q')) (hsmall : heatRatio W ≤ HalfPow.half)

/-- A common cap for the actual remainder at every face's own cutoff. -/
def remainderInterval (id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) :
    Interval (blocks extent) (faceHeatTail (w id) extent id 1 (K id)) (heatRemainderBound W) :=
  (faceRemainderInterval (hw0 id hi) (Q'.le_trans' _ _ _ (hwW id hi) hW1)
    (Q'.le_trans' _ _ _ (heatRatio_mono (hw0 id hi) (hwW id hi)) hsmall)
    extent id hi (K id)).weaken (heatRemainderBound_mono (hw0 id hi) (hwW id hi))

def remainderProductInterval (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Interval (blocks extent)
      (polynomialProduct (fun id => faceHeatTail (w id) extent id 1 (K id)) ids)
      ((heatRemainderBound W)^ids.length) :=
  Interval.productUniform _ _ ids
    (fun id hid => remainderInterval w K extent hw0 hwW hW1 hsmall id (hi id hid))

include hw0 hwW hW1 hsmall in
/-- Every selected face still pays a small factor, against the exact background. -/
theorem weighted_remainder_bound (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    {B : RatPoly} (HB : Certificate (blocks extent) B) :
    Q'.abs (quaternionHaar (blocks extent) (polyMul B
      (polynomialProduct (fun id => faceHeatTail (w id) extent id 1 (K id)) ids))) ≤
      (heatRemainderBound W)^ids.length * quaternionHaar (blocks extent) B :=
  (remainderProductInterval w K extent hw0 hwW hW1 hsmall ids hi).weighted_haar_bound HB

variable (hdelta : heatRemainderBound W ≤ 1)

/-- Constructed positivity, including every shared link in the varying product. -/
def productCertificate : (ids : List Nat) →
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    Certificate (blocks extent) (polynomialProduct (factor w K extent) ids)
  | [], _ => .one _
  | id::ids, hi =>
      let hid := hi id List.mem_cons_self
      (faceCertificate (hw0 id hid) (Q'.le_trans' _ _ _ (hwW id hid) hW1)
        (Q'.le_trans' _ _ _ (heatRatio_mono (hw0 id hid) (hwW id hid)) hsmall)
        (Q'.le_trans' _ _ _ (heatRemainderBound_mono (hw0 id hid) (hwW id hid)) hdelta)
        extent id hid (K id)).mul
        (productCertificate ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

include hw0 hwW hW1 hsmall in
theorem insert_lower (id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
    {B : RatPoly} (HB : Certificate (blocks extent) B) :
    (1 + -heatRemainderBound W)*quaternionHaar (blocks extent) B ≤
      quaternionHaar (blocks extent) (polyMul B (factor w K extent id)) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_add (Q'.le_refl' 1) (Q'.neg_le_neg (heatRemainderBound_mono (hw0 id hi) (hwW id hi))))
      HB.haar_nonnegative)
    (insertFace_lower (hw0 id hi) (Q'.le_trans' _ _ _ (hwW id hi) hW1)
      (Q'.le_trans' _ _ _ (heatRatio_mono (hw0 id hi) (hwW id hi)) hsmall) extent id hi (K id) HB)

include hw0 hwW hW1 hsmall hdelta in
/-- Only inserted faces enter the cost. The background is not replaced or bounded below. -/
theorem weighted_floor (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    {B : RatPoly} (HB : Certificate (blocks extent) B) :
    removalFloor W ids.length * quaternionHaar (blocks extent) B ≤
      quaternionHaar (blocks extent) (polyMul B (polynomialProduct (factor w K extent) ids)) := by
  induction ids with
  | nil =>
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one B))))
  | cons id ids ih =>
      have ht : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent := fun j hj => hi j (List.mem_cons_of_mem id hj)
      have h := insert_lower w K extent hw0 hwW hW1 hsmall id (hi id List.mem_cons_self)
        (HB.mul (productCertificate w K extent hw0 hwW hW1 hsmall hdelta ids ht))
      have he : RatPolyCoeffEqv
          (polyMul (polyMul B (polynomialProduct (factor w K extent) ids)) (factor w K extent id))
          (polyMul B (polyMul (factor w K extent id) (polynomialProduct (factor w K extent) ids))) :=
        (RatPolyCoeffEqv.mul_assoc _ _ _).trans ((RatPolyCoeffEqv.mul_comm _ _).mul_left B)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (ih ht) (Q'.sub_nonneg_of_le hdelta))
          (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff he))))

include hw0 hwW hW1 hsmall hdelta in
theorem relative_floor (removed background : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    removalFloor W removed.length * partition w K extent background ≤
      partition w K extent (removed++background) :=
  Q'.le_trans' _ _ _
    (weighted_floor w K extent hw0 hwW hW1 hsmall hdelta removed hr
      (productCertificate w K extent hw0 hwW hW1 hsmall hdelta background hb))
    (Q'.le_of_eqv (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans
      (polynomialProduct_append (factor w K extent) removed background).symm)))

include hw0 hwW hW1 hsmall hdelta in
/-- SAME-background partition square, without a whole-volume reciprocal loss. -/
theorem relative_square_floor (removed background : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    (removalFloor W removed.length * removalFloor W removed.length) *
      (partition w K extent background * partition w K extent background) ≤
        partition w K extent (removed++background) * partition w K extent (removed++background) := by
  let f := removalFloor W removed.length
  let z := partition w K extent background
  let Z := partition w K extent (removed++background)
  have hz : (0 : Q') ≤ z := (productCertificate w K extent hw0 hwW hW1 hsmall hdelta background hb).haar_nonnegative
  have hfz : (0 : Q') ≤ f*z := Q'.mul_nonneg _ _ (removalFloor_nonnegative hdelta _) hz
  have h := relative_floor w K extent hw0 hwW hW1 hsmall hdelta removed background hr hb
  have hZ : (0 : Q') ≤ Z := Q'.le_trans' _ _ _ hfz h
  have hs := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h hfz)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ h hZ)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide)
    (fun i => if i = 0 then f else z))) hs

include hw0 hwW hW1 hsmall in
/-- Strict positivity of every finite heterogeneous physical partition. -/
theorem partition_positive (hd : heatRemainderBound W < 1) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    (0 : Q') < partition w K extent ids := by
  have h := relative_floor w K extent hw0 hwW hW1 hsmall (Q'.le_of_lt hd)
    ids [] hi (fun _ h => False.elim (List.not_mem_nil h))
  have hOne : partition w K extent [] ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
      (Q'.eqv_of_eq (Q'.add_zero' 1))
  have hf : (0 : Q') < removalFloor W ids.length := HKPos.pow_pos (HKPos.one_sub_pos hd) _
  have he : removalFloor W ids.length * partition w K extent [] ≈ removalFloor W ids.length :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hOne) (Q'.mul_one_eqv _)
  simpa only [List.append_nil] using Q'.pos_of_lt_of_le hf (Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h)

end YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison

#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.factor
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.partition
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.remainderInterval
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.remainderProductInterval
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.weighted_remainder_bound
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.productCertificate
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.insert_lower
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.weighted_floor
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.relative_floor
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.relative_square_floor
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison.partition_positive
