/-
# Nonnegative diagonal remainder of the ORIGINAL full product heat

A valid path follows the actual, input-dependent harmonic degree tree.
One complete path is realized by the corresponding finite product of
dimension-normalized character kernels. Its original-input pairing is
nonnegative by Gram positivity. Summing the nonnegative scalar Taylor
remainders therefore proves the diagonal remainder nonnegative, including
omitted heat modes. No joint orthogonality or positivity of rotating prefixes
is assumed. The consumer removes one error budget from the original signed
source-energy estimate; it does not control the remaining mixed budget.
-/

import YMGap.Continuum.SU2QuaternionCyclicCharacterPositive
import YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

namespace YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCharacterSelection
open YMGap.Continuum.SU2QuaternionCyclicCharacterPositive
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Membership at every branch of the ragged, computed degree tree. -/
def ValidPath (tail : Nat) : RatPoly → List Nat → Prop
  | _, [] => True
  | p, d::ds => d ∈ branchDegrees tail p ∧ ValidPath tail (nextPiece tail p d) ds

/-- The polynomial at the end of a chosen degree path. -/
def pathPiece (tail : Nat) : RatPoly → List Nat → RatPoly
  | p, [] => p
  | p, d::ds => pathPiece tail (nextPiece tail p d) ds

private theorem pathPiece_character_carrier (tail : Nat) :
    ∀ (ds : List Nat) (p : RatPoly), SupportedQuaternionBlocks (tail+1) p →
      ValidPath tail p ds → HaarCarrierEqv (tail+1)
        (characterIterate (tail+1) ds p) (pathPiece tail p ds)
  | [], _, _, _ => HaarCarrierEqv.refl _ _
  | d::ds, p, hp, hpath =>
      (characterIterate_carrier (tail+1) ds
        (characterCycleStep_supported _ _ hp) (nextPiece_supported tail p d)
        (characterCycleStep_branch_carrier tail d p hp hpath.1)).trans
      (pathPiece_character_carrier tail ds (nextPiece tail p d)
        (nextPiece_supported tail p d) hpath.2)

/-- Every VALID full-cycle leaf has a nonnegative pairing with the original
input. This is proved from its product kernel, not asserted from one-head
orthogonality. The degrees need not lie below the heat cutoff. -/
theorem full_path_pairing_nonnegative (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
    (0 : Q') ≤ quaternionHaar (tail+1) (polyMul p (pathPiece tail p ds)) :=
  Q'.le_trans' _ _ _ (characterIterate_diagonal_nonnegative (tail+1) ds hlen p hp)
    (Q'.le_of_eqv (pathPiece_character_carrier tail ds p hp hpath p))

private theorem sum_nonnegative (f : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → (0 : Q') ≤ f d) → (0 : Q') ≤ qListSum (ids.map f)
  | [], _ => Q'.le_refl' _
  | d::ds, h => Q'.zero_le_add _ _ (h d List.mem_cons_self)
      (sum_nonnegative f ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

private theorem leafSum_nonnegative_of_paths (tail : Nat) :
    ∀ (m : Nat) (p test : RatPoly) (weight : List Nat → Q'),
      (∀ ds, ds.length = m → ValidPath tail p ds → (0 : Q') ≤ weight ds) →
      (∀ ds, ds.length = m → ValidPath tail p ds →
        (0 : Q') ≤ quaternionHaar (tail+1) (polyMul test (pathPiece tail p ds))) →
      (0 : Q') ≤ leafSum tail m p test weight
  | 0, p, test, weight, hw, hp => Q'.mul_nonneg _ _ (hw [] rfl True.intro)
      (hp [] rfl True.intro)
  | m+1, p, test, weight, hw, hp => by
      apply sum_nonnegative
      intro d hd
      apply leafSum_nonnegative_of_paths tail m (nextPiece tail p d) test
        (fun ds => weight (d::ds))
      · intro ds hlen hpath
        exact hw (d::ds) (by simp only [List.length_cons, hlen]) ⟨hd,hpath⟩
      · intro ds hlen hpath
        exact hp (d::ds) (by simp only [List.length_cons, hlen]) ⟨hd,hpath⟩

/-- Positive path coefficients give a positive diagonal on the ORIGINAL
full product carrier, although each leaf was initially written as a signed
pairing rather than an orthogonal square. -/
theorem full_leafSum_diagonal_nonnegative (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (weight : List Nat → Q')
    (hw : ∀ ds, ds.length = tail+1 → (0 : Q') ≤ weight ds) :
    (0 : Q') ≤ leafSum tail (tail+1) p p weight :=
  leafSum_nonnegative_of_paths tail (tail+1) p p weight
    (fun ds hlen _ => hw ds hlen)
    (fun ds hlen hpath => full_path_pairing_nonnegative tail p hp ds hlen hpath)

/-- The computed full-product DIAGONAL Taylor remainder is nonnegative under
the existing scalar cutoff guard. No cutoff dominating the source degree is
added; omitted modes are covered by the scalar remainder theorem. -/
theorem pairRemainder_diagonal_nonnegative (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    (0 : Q') ≤ pairRemainder tail w K p p :=
  full_leafSum_diagonal_nonnegative tail p hp (productRemainder w K)
    (fun ds _ => (productRemainder_bounds_of_sufficientCutoff hw0 hw1 hK ds).1)

/-- Actual weighted-energy consumer: the negative diagonal remainder is
discarded by PROVED positivity, leaving only the original mixed-source
quadratic budget. Its dependence through a and f is unchanged. -/
theorem sourceEnergy_le_firstOrder_add_mixed_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*sourceFirstOrder tail a f +
        (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail a (polyMul a (polyMul f f)) := by
  have hd := Q'.neg_le_neg (pairRemainder_diagonal_nonnegative tail hw0 hw1 K hK
    (polyMul a f) (supported_polyMul ha hf))
  have hr := Q'.add_le_add
    (pairRemainder_le_quadratic tail hw0 hw1 K hK a (polyMul a (polyMul f f))) hd
  have hz : (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail a (polyMul a (polyMul f f)) +
      -(0 : Q') ≈
      (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail a (polyMul a (polyMul f f)) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0) (by decide)
      (fun _ => (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail a (polyMul a (polyMul f f)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (sourceEnergy_taylor tail w K a f ha hf))
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hr (Q'.le_of_eqv hz)))

/-- First-order source cancellation and diagonal positivity together leave
one mixed quadratic budget for the actual weighted full-product energy. -/
theorem sourceEnergy_le_angular_add_mixed_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
        (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail a (polyMul a (polyMul f f)) :=
  Q'.le_trans' _ _ _
    (sourceEnergy_le_firstOrder_add_mixed_quadratic tail hw0 hw1 K hK a f ha hf)
    (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (sourceFirstOrder_eq_weightedAngularEnergy tail a f ha hf))
      (Q'.eqv_refl _)))

end YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder

#print axioms YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder.full_path_pairing_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder.full_leafSum_diagonal_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder.pairRemainder_diagonal_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder.sourceEnergy_le_firstOrder_add_mixed_quadratic
#print axioms YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder.sourceEnergy_le_angular_add_mixed_quadratic
