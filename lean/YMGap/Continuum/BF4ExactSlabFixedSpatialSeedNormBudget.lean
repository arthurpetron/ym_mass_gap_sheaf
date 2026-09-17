/-
# Degree-independent norm budget for the ACTUAL full-density seed family

With nu the original odd marginal, Phi=H[nu]*f-H[nu*f], and the existing
finite tests q_i, ordinary Haar Pythagoras BEFORE inverse-density
conjugation gives

  ell * sum_i H[nu*q_i^2] <= H[(nu*Phi)^2] <= u*H[nu*Phi^2].

There is no coordinate-count or approximation-degree factor. The actual
second-stage corrected tests contract individually, so the same budget
holds at arbitrary finite correction degrees. The coefficient u/ell still
retains nome, cutoff, spatial width and terminal depth. These are the full
nu tests, NOT tests rebuilt from the active spatial marginal and NOT an
active-only approximation after deleting fringe entries.

This supplies a concrete norm budget for the signed-cost consumer, but
not its required regulator-uniform conditioning or determinant estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
import YMGap.Continuum.SU2QuaternionHaarBlockTelescopeNorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm (test_norm_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels labels_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
  (corrected diagonalRemainder diagonalBudget diagonalRemainder_bounds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost (correctedTest correctedTest_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage (conditionalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse
  (reciprocal multiplierSquareCertificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap majorant_prefix_bound)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockTelescopeNorm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarFamilySquare (qListSum_scale singleCuts_map_fst)
open YMGap.Continuum.QuaternionHaarFamilyErasure (singleCuts)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks activeBlocks

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_le {blocks : Nat} {p q : RatPoly}
    (C : Certificate blocks (polyAdd p (polyNeg q))) :
    quaternionHaar blocks q ≤ quaternionHaar blocks p :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ C.haar_nonnegative (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks q)))))

private theorem sum_le {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≤ g i) : qListSum (ids.map f) ≤ qListSum (ids.map g) := by
  revert h
  induction ids with
  | nil => intro _; exact Q'.le_refl' _
  | cons i ids ih =>
      intro h
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (h i List.mem_cons_self))
        (Q'.add_le_add_left _ _ _ (ih (fun j hj => h j (List.mem_cons_of_mem i hj))))

private theorem sum_perm {xs ys : List Q'} (h : xs.Perm ys) : qListSum xs ≈ qListSum ys := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons a _ ih => exact Q'.add_eqv_congr' (Q'.eqv_refl a) ih
  | swap a b xs =>
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
        (fun | 0 => b | 1 => a | _ => qListSum xs)
  | trans _ _ h1 h2 => exact Q'.eqv_trans _ _ _ h1 h2

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- The actual finite family is controlled before any weighted-orthogonality
claim: only the underlying ordinary Haar telescope is orthogonal. -/
theorem family_norm_le_source (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    lower w K width n * qListSum ((labels width).map (fun i => marginalPair w K width n (qs i) (qs i))) ≤
      quaternionHaar (N width) (polyMul (source w K width n f) (source w K width n f)) := by
  let qs := familyTests hw0 hw1 K width hK n k f
  let norms := fun i => marginalPair w K width n (qs i) (qs i)
  let pieces := fun i => quaternionHaar (N width)
    (polyMul (piece w K width n i f) (piece w K width n i f))
  have hlocal : ∀ i, i ∈ labels width → lower w K width n * norms i ≤ pieces i := by
    intro i hi
    exact test_norm_le hw0 hw1 K width hK n i (labels_lt width i hi) k
      (piece_supported w K width n i hf)
  have hp := sum_perm ((labels_perm_range width).map pieces)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qListSum_scale (labels width) norms (lower w K width n)))
    (Q'.le_trans' _ _ _ (sum_le _ _ _ hlocal)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
        (full_term_square_sum_le (N width) (source w K width n f) (source_supported w K width n hf))))

include hw0 hw1 hK in
/-- Explicit upper-window comparison on the original, partition-cleared source. -/
theorem source_norm_le {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul (source w K width n f) (source w K width n f)) ≤
      upper w K width n * marginalPair w K width n
        (centeredObservable w K width n f) (centeredObservable w K width n f) := by
  let a := marginalWeight w K width n
  let p := centeredObservable w K width n f
  let u := upper w K width n
  have C := ((marginalCertificate hw0 hw1 K width hK n).mul
    (upperCertificate hw0 hw1 K width hK n)).mul
      (.square p (centeredObservable_supported w K width n hf))
  have P : Certificate (N width) (polyAdd (polySmul u (polyMul a (polyMul p p)))
      (polyNeg (polyMul (polyMul a p) (polyMul a p)))) := by
    refine .ofCoeff ((((cap_mul_left u _).symm).add (.refl _)).trans ?_) C
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 2) (.mul (.var 0) (.mul (.var 1) (.var 1))))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))
      (.mul (.mul (.var 0) (.add (.var 2) (.neg (.var 0)))) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => a | 1 => p | _ => cap u)
  exact Q'.le_trans' _ _ _ (haar_le P) (Q'.le_of_eqv (quaternionHaar_polySmul _ _ _))

/-- No coordinate-count or seed-degree factor; the displayed finite density
contrast remains and must not be called regulator-uniform. -/
theorem family_norm_budget (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    lower w K width n * qListSum ((labels width).map (fun i => marginalPair w K width n (qs i) (qs i))) ≤
      upper w K width n * marginalPair w K width n
        (centeredObservable w K width n f) (centeredObservable w K width n f) :=
  Q'.le_trans' _ _ _ (family_norm_le_source hw0 hw1 K width hK n k hf)
    (source_norm_le hw0 hw1 K width hK n hf)

/-- The actual second-stage reciprocal correction contracts each original-nu
norm at every finite degree. Fringe entries remain unchanged. -/
theorem corrected_norm_le (qs : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat)
    (hq : SupportedQuaternionBlocks (N width) (qs i)) :
    marginalPair w K width n (corrected hw0 hw1 K width hK n qs degrees i)
      (corrected hw0 hw1 K width hK n qs degrees i) ≤ marginalPair w K width n (qs i) (qs i) := by
  unfold corrected
  by_cases hi : i ∈ activeBlocks width
  · rw [if_pos hi]
    let a := marginalWeight w K width n
    let p := qs i
    let c := polyMul (conditionalMessage w K width n i)
      (reciprocal hw0 hw1 K width hK n i (degrees i))
    have C := ((marginalCertificate hw0 hw1 K width hK n).mul
      (multiplierSquareCertificate hw0 hw1 K width hK n i hi (degrees i))).mul (.square p hq)
    have P : Certificate (N width) (polyAdd (polyMul a (polyMul p p))
        (polyNeg (polyMul a (polyMul (polyMul c p) (polyMul c p))))) :=
      .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1))))))
        (.mul (.mul (.var 0) (.add (.const 1) (.neg (.mul (.var 2) (.var 2)))))
          (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => a | 1 => p | _ => c)) C
    exact haar_le P
  · rw [if_neg hi]
    exact Q'.le_refl' _

/-- The same actual family budget survives arbitrary finite correction degrees. -/
theorem corrected_family_norm_budget (k : Nat) (degrees : Nat → Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    let cs := corrected hw0 hw1 K width hK n qs degrees
    lower w K width n * qListSum ((labels width).map (fun i => marginalPair w K width n (cs i) (cs i))) ≤
      upper w K width n * marginalPair w K width n
        (centeredObservable w K width n f) (centeredObservable w K width n f) := by
  let qs := familyTests hw0 hw1 K width hK n k f
  have h := sum_le (labels width)
    (fun i => marginalPair w K width n (corrected hw0 hw1 K width hK n qs degrees i)
      (corrected hw0 hw1 K width hK n qs degrees i))
    (fun i => marginalPair w K width n (qs i) (qs i))
    (fun i _ => corrected_norm_le hw0 hw1 K width hK n qs degrees i
      (familyTests_supported hw0 hw1 K width hK n k i hf))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h
    (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n)))
    (family_norm_budget hw0 hw1 K width hK n k hf)

/-- The existing signed-cost theorem's diagonal term is bounded by its actual
component norms, with the common coefficient U-h on active and fringe. -/
theorem diagonal_norm_sum_le (qs : Nat → RatPoly) (degrees : Nat → Nat)
    (hq : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (qs i)) :
    diagonalRemainder hw0 hw1 K width hK n qs degrees ≤
      (prefixCap w + -(headFloor w)) * qListSum ((labels width).map (fun i =>
        marginalPair w K width n (corrected hw0 hw1 K width hK n qs degrees i)
          (corrected hw0 hw1 K width hK n qs degrees i))) := by
  let norms := fun i => marginalPair w K width n (corrected hw0 hw1 K width hK n qs degrees i)
    (corrected hw0 hw1 K width hK n qs degrees i)
  let F := fun i =>
    (if i ∈ activeBlocks width then prefixCap w + -(headFloor w) else (1 : Q') + -(headFloor w)) * norms i
  have hmap : (singleCuts (labels width)).map (fun c => F c.1) = (labels width).map F := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map F) (singleCuts_map_fst (labels width))
  have hD := (diagonalRemainder_bounds hw0 hw1 K width hK n qs degrees hq).2
  change diagonalRemainder hw0 hw1 K width hK n qs degrees ≤
    qListSum ((singleCuts (labels width)).map (fun c => F c.1)) at hD
  rw [hmap] at hD
  have hU := majorant_prefix_bound hw0 hw1 1
  change (1 : Q') ≤ prefixCap w at hU
  have hpoint : ∀ i, i ∈ labels width → F i ≤ (prefixCap w + -(headFloor w)) * norms i := by
    intro i hi
    have hs : SupportedQuaternionBlocks (N width) (corrected hw0 hw1 K width hK n qs degrees i) := by
      unfold corrected
      by_cases ha : i ∈ activeBlocks width
      · rw [if_pos ha]
        exact correctedTest_supported hw0 hw1 K width hK n i (hq i (labels_lt width i hi)) (degrees i)
      · rw [if_neg ha]
        exact hq i (labels_lt width i hi)
    have hn : (0 : Q') ≤ norms i :=
      ((marginalCertificate hw0 hw1 K width hK n).mul (.square _ hs)).haar_nonnegative
    dsimp only [F]
    by_cases ha : i ∈ activeBlocks width
    · rw [if_pos ha]
      exact Q'.le_refl' _
    · rw [if_neg ha]
      exact Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.add_le_add_right _ _ _ hU) hn
  exact Q'.le_trans' _ _ _ hD (Q'.le_trans' _ _ _ (sum_le _ _ _ hpoint)
    (Q'.le_of_eqv (qListSum_scale (labels width) norms (prefixCap w + -(headFloor w)))))

/-- Concrete degree-independent diagonal cost for the ACTUAL produced family.
The finite density contrast remains; the signed determinant sum is not bounded. -/
theorem diagonal_family_norm_budget (k : Nat) (degrees : Nat → Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    lower w K width n * diagonalRemainder hw0 hw1 K width hK n qs degrees ≤
      (prefixCap w + -(headFloor w)) * (upper w K width n * marginalPair w K width n
        (centeredObservable w K width n f) (centeredObservable w K width n f)) := by
  let qs := familyTests hw0 hw1 K width hK n k f
  let c := prefixCap w + -(headFloor w)
  let total := qListSum ((labels width).map (fun i => marginalPair w K width n
    (corrected hw0 hw1 K width hK n qs degrees i) (corrected hw0 hw1 K width hK n qs degrees i)))
  have hU := majorant_prefix_bound hw0 hw1 1
  change (1 : Q') ≤ prefixCap w at hU
  have hc : (0 : Q') ≤ c := Q'.sub_nonneg_of_le
    (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1)
      (Q'.le_trans' _ _ _ (by decide) hU))
  have hD := diagonal_norm_sum_le hw0 hw1 K width hK n qs degrees
    (fun i _ => familyTests_supported hw0 hw1 K width hK n k i hf)
  have he : lower w K width n * (c*total) ≈ c * (lower w K width n * total) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => lower w K width n | 1 => c | _ => total)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hD (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (corrected_family_norm_budget hw0 hw1 K width hK n k degrees hf) hc))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget.family_norm_le_source
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget.source_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget.family_norm_budget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget.corrected_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget.corrected_family_norm_budget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget.diagonal_norm_sum_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget.diagonal_family_norm_budget
