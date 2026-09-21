/-
# Bounded-overlap cost for actual original-action Ward score families

Each index witnesses an actual physical link. Tests may depend on that
link's whole plaquette star. Its score has the same star support; off-star
Gram entries vanish under the full interacting action. A duplicate-free
family has at most 25 near entries per row, so its actual sum-square costs
at most 25 times the sum of actual diagonal costs, not a family-size factor.
The centered response retains the whole signed observable. No response
lower bound, nome-scaling estimate, OS gap or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabOriginalWardLocality
import YMGap.Continuum.BF4ExactSlabWardStarGeometry
import YMGap.Continuum.QuaternionHaarSparseFamilyCost

namespace YMGap.Continuum.BF4ExactSlabWardFamilyCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabOriginalWardLocality
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarCenteredResponse
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarSparseFamilyCost
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- Physical membership is retained, not an invalid-index fallback. -/
abbrev PhysicalLink (extent : Nat) := { link : Z4Link // link ∈ boundaryCompleteSlabLinks extent }

def score (w : Q') (K extent i j : Nat) (tests : PhysicalLink extent → RatPoly)
    (link : PhysicalLink extent) : RatPoly :=
  originalScore w K extent link.val link.property i j (tests link)

def totalScore (w : Q') (K extent i j : Nat) (tests : PhysicalLink extent → RatPoly)
    (xs : List (PhysicalLink extent)) : RatPoly := finitePolySum (score w K extent i j tests) xs

variable (w : Q') (K extent : Nat)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- Positivity of the actual full partition, including empty score families. -/
theorem fullPartition_positive (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) : (0 : Q') < quaternionHaar (blocks extent) W :=
  Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 _)
    (partition_floor hw0 hw1 extent (slabPhysicalFaceEdges extent) (fun _ h => h) K hK)

theorem score_supported (i j : Nat) (tests : PhysicalLink extent → RatPoly) (link : PhysicalLink extent) :
    SupportedQuaternionBlocks (blocks extent) (score w K extent i j tests link) :=
  originalScore_supported w K extent link.val link.property i j (tests link)

/-- A star-local test gives a score on that SAME star, retaining every test link. -/
theorem score_local {i j : Nat} (hi : i < 4) (hj : j < 4)
    (tests : PhysicalLink extent → RatPoly) (link : PhysicalLink extent)
    (ht : LinkLocal extent (starLinks extent link.val) (tests link)) :
    LinkLocal extent (starLinks extent link.val) (score w K extent i j tests link) := by
  apply (originalScore_local w K extent link.val link.property hi hj ht).mono
  intro l hl
  rcases List.mem_cons.mp hl with heq | hmem
  · exact heq ▸ near_refl extent link.val
  · rcases List.mem_append.mp hmem with hface | htest
    · exact List.mem_cons_of_mem _ hface
    · exact htest

theorem off_star_pair_zero {i j : Nat} (hi : i < 4) (hj : j < 4)
    (tests : PhysicalLink extent → RatPoly) (a b : PhysicalLink extent)
    (ha : LinkLocal extent (starLinks extent a.val) (tests a))
    (hfar : ¬ Near extent a.val b.val) :
    quaternionHaar (blocks extent)
      (polyMul (polyMul (score w K extent i j tests a) (score w K extent i j tests b)) W) ≈ 0 :=
  originalScore_pair_zero_of_local w K extent b.val b.property hi hj (tests b) _
    (score_supported w K extent i j tests a) (score_local w K extent hi hj tests a ha) hfar

theorem totalScore_supported (i j : Nat) (tests : PhysicalLink extent → RatPoly) :
    ∀ xs : List (PhysicalLink extent), SupportedQuaternionBlocks (blocks extent) (totalScore w K extent i j tests xs)
  | [] => fun _ h => False.elim (List.not_mem_nil h)
  | link :: xs => supported_add (score_supported w K extent i j tests link)
      (totalScore_supported i j tests xs)

/-- Zero mean of the actual finite total score, under the complete action. -/
theorem totalScore_mean_zero {i j : Nat} (hi : i < 4) (hj : j < 4)
    (tests : PhysicalLink extent → RatPoly) (xs : List (PhysicalLink extent))
    (hW : (0 : Q') < quaternionHaar (blocks extent) W) :
    normalizedMoment (blocks extent) W (totalScore w K extent i j tests xs) hW ≈ 0 := by
  have hz (link : PhysicalLink extent) : normalizedMoment (blocks extent) W (score w K extent i j tests link) hW ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm W _))
      (originalScore_mean_zero w K extent link.val link.property hi hj (tests link)))) (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ _ _ (normalized_sum hW (score w K extent i j tests) xs)
    (Q'.eqv_trans _ _ _ (listQSum_congr hz xs) (listQSum_zero xs))

/-- Only the fixed four-dimensional overlap row bound multiplies the sum
of ACTUAL diagonal costs. The action, partition and signed scores are unchanged. -/
theorem totalScore_cost_le (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (tests : PhysicalLink extent → RatPoly) (xs : List (PhysicalLink extent)) (hxs : xs.Nodup)
    (ht : ∀ link, link ∈ xs → LinkLocal extent (starLinks extent link.val) (tests link)) :
    normalizedMoment (blocks extent) W
      (polyMul (totalScore w K extent i j tests xs) (totalScore w K extent i j tests xs))
      (fullPartition_positive w K extent hw0 hw1 hK) ≤
      Q'.ofNat 25 * listQSum (fun link => normalizedMoment (blocks extent) W
        (polyMul (score w K extent i j tests link) (score w K extent i j tests link))
        (fullPartition_positive w K extent hw0 hw1 hK)) xs := by
  exact sparse_family_cost
    (headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ h => h))
    (fullPartition_positive w K extent hw0 hw1 hK) (score w K extent i j tests) xs
    (fun a b => Near extent a.val b.val) 25 (fun link _ => score_supported w K extent i j tests link)
    (fun _ _ _ _ => ⟨near_symm, near_symm⟩)
    (fun link _ => row_count_injective extent link.val (fun a : PhysicalLink extent => a.val)
      (fun _ _ h => Subtype.ext h) xs hxs)
    (fun a ha b _ hfar => off_star_pair_zero w K extent hi hj tests a b (ht a ha) hfar)

/-- Centered response of the whole signed observable against the actual total
score. A useful lower estimate for this SAME response remains to be proved. -/
theorem totalScore_response_bound (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (tests : PhysicalLink extent → RatPoly) (xs : List (PhysicalLink extent)) (hxs : xs.Nodup)
    (ht : ∀ link, link ∈ xs → LinkLocal extent (starLinks extent link.val) (tests link))
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    let response := normalizedMoment (blocks extent) W (polyMul f (totalScore w K extent i j tests xs)) hW
    response * response ≤ normalizedVariance (blocks extent) W f hW *
      (Q'.ofNat 25 * listQSum (fun link => normalizedMoment (blocks extent) W
        (polyMul (score w K extent i j tests link) (score w K extent i j tests link)) hW) xs) := by
  let H := headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ h => h)
  let hW := fullPartition_positive w K extent hw0 hw1 hK
  exact Q'.le_trans' _ _ _ (centered_response_square_bound H hW hf
    (totalScore_supported w K extent i j tests xs) (totalScore_mean_zero w K extent hi hj tests xs hW))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (totalScore_cost_le w K extent hw0 hw1 hK hi hj tests xs hxs ht)
      (normalizedVariance_nonnegative H hW hf))

end YMGap.Continuum.BF4ExactSlabWardFamilyCost

#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.fullPartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.score_supported
#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.score_local
#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.off_star_pair_zero
#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.totalScore_supported
#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.totalScore_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.totalScore_cost_le
#print axioms YMGap.Continuum.BF4ExactSlabWardFamilyCost.totalScore_response_bound
