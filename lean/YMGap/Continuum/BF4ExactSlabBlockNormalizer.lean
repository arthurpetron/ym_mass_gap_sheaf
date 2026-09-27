/-
# The original interacting normalizer for a finite family of physical links

Integrate the actual incident collar over the selected original coordinates.
Every detached original action factor remains in the background. The resulting
polynomial and inserted numerator have exact full-action marginal identities.
The normalizer has a constructed positive certificate. Two-sided weighted
bounds hold for supported certified-positive tests (hence every supported
square), at every 0<w<1 and late heat cutoff. Constants depend on
nome and the number of selected links, not the ambient volume or cutoff.

This supplies a block-normalizer input for constructive inversion. It does not
yet construct that inverse, an interacting block projection, a useful two-block
angle estimate, or a scaling/OS/physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
import YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
import YMGap.Continuum.SU2QuaternionHaarFamilyCertificate

namespace YMGap.Continuum.BF4ExactSlabBlockNormalizer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Literal original-coordinate indices; no alternate polynomial carrier. -/
def slots (extent : Nat) (links : List Z4Link) : List Nat :=
  links.map (fun link => (boundaryCompleteSlabLinks extent).idxOf link)

theorem slots_valid (extent : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) :
    ∀ i, i ∈ slots extent links → i < blocks extent := by
  intro i hi
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hi
  exact List.idxOf_lt_length_of_mem (hl link hlink)

def collarHeat (w : Q') (K extent : Nat) (links : List Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (collar extent links)

def normalizer (w : Q') (K extent : Nat) (links : List Z4Link) : RatPoly :=
  familyProject (slots extent links) (collarHeat w K extent links)

def insertedNormalizer (w : Q') (K extent : Nat) (links : List Z4Link)
    (p : RatPoly) : RatPoly :=
  familyProject (slots extent links) (polyMul p (collarHeat w K extent links))

theorem normalizer_supported (w : Q') (K extent : Nat) (links : List Z4Link) :
    SupportedQuaternionBlocks (blocks extent) (normalizer w K extent links) :=
  familyProject_supported _ (heatProduct_supported w K extent _)

theorem insertedNormalizer_supported (w : Q') (K extent : Nat)
    (links : List Z4Link) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    SupportedQuaternionBlocks (blocks extent) (insertedNormalizer w K extent links p) :=
  familyProject_supported _ (supported_polyMul hp (heatProduct_supported w K extent _))

theorem normalizer_independent (w : Q') (K extent : Nat) (links : List Z4Link) :
    ∀ i, i ∈ slots extent links →
      QuaternionBlockIndependent i (normalizer w K extent links) :=
  familyProject_independent _ _

theorem insertedNormalizer_independent (w : Q') (K extent : Nat)
    (links : List Z4Link) (p : RatPoly) :
    ∀ i, i ∈ slots extent links →
      QuaternionBlockIndependent i (insertedNormalizer w K extent links p) :=
  familyProject_independent _ _

theorem background_independent (w : Q') (K extent : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) :
    ∀ i, i ∈ slots extent links →
      QuaternionBlockIndependent i (background w K extent links) := by
  intro i hi
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hi
  exact background_independent_on_support w K extent links (hl link hlink) hlink

/-- The full original action has exactly this block marginal, coefficientwise. -/
theorem full_marginal_pin (w : Q') (K extent : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) :
    RatPolyCoeffEqv (familyProject (slots extent links) (fullWeight w K extent))
      (polyMul (background w K extent links) (normalizer w K extent links)) :=
  (familyProject_congr _ (fullWeight_split w K extent links)).trans
    (familyProject_mul_of_independent _ _ _ (background_independent w K extent links hl))

/-- All selected-variable dependence in an observable stays inside its
inserted numerator. No spectator or original heat factor is discarded. -/
theorem full_inserted_marginal_pin (w : Q') (K extent : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) (p : RatPoly) :
    RatPolyCoeffEqv
      (familyProject (slots extent links) (polyMul p (fullWeight w K extent)))
      (polyMul (background w K extent links) (insertedNormalizer w K extent links p)) := by
  have hsplit : RatPolyCoeffEqv (polyMul p (fullWeight w K extent))
      (polyMul (background w K extent links) (polyMul p (collarHeat w K extent links))) :=
    ((RatPolyCoeffEqv.refl p).mul (fullWeight_split w K extent links)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => p | 1 => background w K extent links | _ => collarHeat w K extent links))
  exact (familyProject_congr _ hsplit).trans
    (familyProject_mul_of_independent _ _ _ (background_independent w K extent links hl))

theorem full_insertion_pin (w : Q') (K extent : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) (p : RatPoly) :
    quaternionHaar (blocks extent) (polyMul p (fullWeight w K extent)) ≈
      quaternionHaar (blocks extent)
        (polyMul (background w K extent links) (insertedNormalizer w K extent links p)) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (familyProject_mean _ _ (slots_valid extent links hl) _))
    (haar_of_coeff (full_inserted_marginal_pin w K extent links hl p))

/-- Exact original-action testing against an exterior polynomial. The
inserted numerator is retained before any division by the normalizer. -/
theorem full_test_pin (w : Q') (K extent : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (r p : RatPoly)
    (hr : ∀ i, i ∈ slots extent links → QuaternionBlockIndependent i r) :
    quaternionHaar (blocks extent) (polyMul (polyMul r p) (fullWeight w K extent)) ≈
      quaternionHaar (blocks extent)
        (polyMul (polyMul r (insertedNormalizer w K extent links p))
          (background w K extent links)) := by
  have hn : RatPolyCoeffEqv (insertedNormalizer w K extent links (polyMul r p))
      (polyMul r (insertedNormalizer w K extent links p)) :=
    (familyProject_congr _ (RatPolyCoeffEqv.mul_assoc _ _ _)).trans
      (familyProject_mul_of_independent _ _ _ hr)
  exact Q'.eqv_trans _ _ _ (full_insertion_pin w K extent links hl (polyMul r p))
    (haar_of_coeff (((RatPolyCoeffEqv.refl _).mul hn).trans
      (RatPolyCoeffEqv.mul_comm _ _)))

/-- A positive certificate for the actual integrated collar, for every nome. -/
def normalizer_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) :
    Certificate (blocks extent) (normalizer w K extent links) :=
  familyProject_certificate _ _ (slots_valid extent links hl)
    (heatProduct_supported w K extent _)
    (headProduct_certificate hw0 hw1 K extent hK _ (fun _ hi => collar_physical hi))

/-- Both bounds hold on all supported certified-positive tests, not just
exterior-independent ones. Projection moves onto the positive test/background
certificate. Applying this to a square covers every supported polynomial. -/
theorem normalizer_weighted_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    {q : RatPoly} (hq : SupportedQuaternionBlocks (blocks extent) q)
    (P : Certificate (blocks extent) q) :
    blockLower w links.length *
        quaternionHaar (blocks extent) (polyMul q (background w K extent links)) ≤
      quaternionHaar (blocks extent)
        (polyMul (polyMul q (normalizer w K extent links)) (background w K extent links)) ∧
    quaternionHaar (blocks extent)
        (polyMul (polyMul q (normalizer w K extent links)) (background w K extent links)) ≤
      blockUpper w links.length *
        quaternionHaar (blocks extent) (polyMul q (background w K extent links)) := by
  let s := slots extent links
  let B := background w K extent links
  let A := collarHeat w K extent links
  let qB := polyMul q B
  have hv := slots_valid extent links hl
  have C : Certificate (blocks extent) (familyProject s qB) :=
    familyProject_certificate _ _ hv
      (supported_polyMul hq (heatProduct_supported w K extent _))
      (P.mul (background_certificate hw0 hw1 K extent hK links))
  have bounds := atMostBlockFaces_bounds hw0 hw1 K extent hK links.length C
    (collar extent links) (fun _ hi => collar_physical hi) (collarCount_le extent links)
  have hmean := familyProject_mean (blocks extent) s hv qB
  have hpair := familyProject_selfAdjoint (blocks extent) s hv qB A
  have horder : RatPolyCoeffEqv (polyMul qB (familyProject s A))
      (polyMul (polyMul q (normalizer w K extent links)) B) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => q | 1 => B | _ => normalizer w K extent links)
  have hpin := Q'.eqv_trans _ _ _ hpair (haar_of_coeff horder)
  exact ⟨Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hmean))
      (Q'.le_trans' _ _ _ bounds.1 (Q'.le_of_eqv hpin)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin)
      (Q'.le_trans' _ _ _ bounds.2 (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hmean)))⟩

#print axioms slots
#print axioms slots_valid
#print axioms collarHeat
#print axioms normalizer
#print axioms insertedNormalizer
#print axioms normalizer_supported
#print axioms insertedNormalizer_supported
#print axioms normalizer_independent
#print axioms insertedNormalizer_independent
#print axioms background_independent
#print axioms full_marginal_pin
#print axioms full_inserted_marginal_pin
#print axioms full_insertion_pin
#print axioms full_test_pin
#print axioms normalizer_certificate
#print axioms normalizer_weighted_bounds

end YMGap.Continuum.BF4ExactSlabBlockNormalizer
