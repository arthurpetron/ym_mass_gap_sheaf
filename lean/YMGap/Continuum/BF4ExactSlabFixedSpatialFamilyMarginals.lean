/-
# Exact finite-family marginals of the original temporal energy

The active-plus-fringe edge flow is twice its one-erasure marginal sum.
Its signed cost is twice the diagonal marginal sum plus four times the
heat floor times the ordered-once two-erasure cross sum. Both endpoint
weights V*T^n1 and every unselected kinetic factor remain unchanged.

This identifies the full finite-family dual estimate on actual marginals.
It does not bound that signed cost by a uniform variance budget, construct
a stable decomposition, or assert a thermodynamic or continuum gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure
import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet (erasedPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual (crossPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported dualTest dualTest_supported dualTest_centered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual (fringeResidual_centered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump marginalPair erased_jump_pairing)
open YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual (marginalPair_perm)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarFiniteFamilyDual
open YMGap.Continuum.QuaternionHaarFamilyErasure

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks kineticWeight activeBlocks

private theorem sum_congr {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≈ g i) :
    qListSum (ids.map f) ≈ qListSum (ids.map g) := by
  revert h
  induction ids with
  | nil => intro _; exact Q'.eqv_refl _
  | cons i ids ih =>
      intro h
      exact Q'.add_eqv_congr' (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem sum_scale {A : Type} (ids : List A) (f : A → Q') (c : Q') :
    qListSum (ids.map (fun i => c*f i)) ≈ c*qListSum (ids.map f) := by
  induction ids with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv c)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

private theorem haar_add (b : Nat) (mu p q : RatPoly) :
    quaternionHaar b (polyMul mu (polyAdd p q)) ≈
      quaternionHaar b (polyMul mu p) + quaternionHaar b (polyMul mu q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right mu p q))
    (quaternionHaar_append _ _ _)

private theorem haar_cap (b : Nat) (mu p : RatPoly) (c : Q') :
    quaternionHaar b (polyMul mu (polyMul (cap c) p)) ≈
      c*quaternionHaar b (polyMul mu p) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => mu | 1 => cap c | _ => p)).trans (cap_mul_left c _)))
    (quaternionHaar_polySmul _ _ _)

private theorem haar_sum (b : Nat) (mu : RatPoly) (ps : List RatPoly) :
    quaternionHaar b (polyMul mu (polySum ps)) ≈
      qListSum (ps.map (fun p => quaternionHaar b (polyMul mu p))) := by
  induction ps with
  | nil => exact haar_of_coeff (RatPolyCoeffEqv.mul_zero_right mu)
  | cons p ps ih =>
      exact Q'.eqv_trans _ _ _ (haar_add b mu p (polySum ps))
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)

/-- One-erasure pairings, once for every retained coordinate, including fringe. -/
def marginalFlow (w : Q') (K width n : Nat) (tests : Nat → RatPoly) (f : RatPoly) : Q' :=
  qListSum ((singleCuts (labels width)).map (fun c => erasedPair w K width n c.1 f (tests c.1)))

/-- The diagonal part of the same signed cost, without discarding any link. -/
def marginalDiagonal (w : Q') (K width n : Nat) (tests : Nat → RatPoly) : Q' :=
  qListSum ((singleCuts (labels width)).map
    (fun c => erasedPair w K width n c.1 (tests c.1) (tests c.1)))

/-- Each distinct positional pair occurs once. Cross pairings remain signed. -/
def marginalCross (w : Q') (K width n : Nat) (tests : Nat → RatPoly) : Q' :=
  qListSum ((pairCuts (labels width)).map
    (fun c => crossPair w K width n c.1 c.2.1 (tests c.1) (tests c.2.1)))

/-- Explicit cost to be controlled by the still-open collective analytic estimate. -/
def marginalCost (w : Q') (K width n : Nat) (tests : Nat → RatPoly) : Q' :=
  marginalDiagonal w K width n tests + ((2 : Q')*headFloor w)*marginalCross w K width n tests

private theorem edge_term (w : Q') (K width n : Nat) (rest : List Nat) (f r : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (polynomialProduct (coordinateFactor w K width) rest)
          (polyMul (jump (N width) f) (jump (N width) r)))) ≈
      weightedPair (N width+N width)
        (edgeWeight (N width) w K (remainingHeat width rest)
          (polyMul (spatialWeight w K width) (terminalMessage w K width n)))
        (jump (N width) f) (jump (N width) r) := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  exact haar_of_coeff (((product_pin w K width rest).mul_right _).mul_left _ |>.trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 3) (.mul (.mul (.var 2) (.var 0)) (.var 1))) (by decide)
      (fun
        | 0 => a | 1 => liftBoundary (N width) a
        | 2 => productHeat (N width) w K (remainingHeat width rest)
        | _ => polyMul (jump (N width) f) (jump (N width) r))))

private theorem single_term (w : Q') (K width n i : Nat) (rest : List Nat)
    (hm : (i,rest) ∈ singleCuts (labels width)) {f r : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hr : SupportedQuaternionBlocks (N width) r)
    (hc : RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) r)) polyZero) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (polynomialProduct (coordinateFactor w K width) rest)
          (polyMul (jump (N width) f) (jump (N width) r)))) ≈
      (2 : Q')*erasedPair w K width n i f r := by
  have hp := singleCuts_perm hm
  have hn := List.nodup_cons.mp (hp.nodup_iff.mp (labels_nodup width))
  have hi := labels_lt width i (hp.mem_iff.mpr List.mem_cons_self)
  have he := erased_jump_pairing (N width) w K i (remainingHeat width rest) hi
    (fun h => hn.1 (List.mem_filter.mp h).1)
    (fun j hj => activeBlocks_lt width j (of_decide_eq_true (List.mem_filter.mp hj).2))
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
    hf hr hc
  exact Q'.eqv_trans _ _ _ (edge_term w K width n rest f r)
    (Q'.eqv_trans _ _ _ he (Q'.mul_eqv_congr_left _ _ _
      (marginalPair_perm (N width) w K (single_remaining_perm hm) _ f r)))

private theorem pair_term (w : Q') (K width n i j : Nat) (rest : List Nat)
    (hm : (i,j,rest) ∈ pairCuts (labels width)) {r s : RatPoly}
    (hr : SupportedQuaternionBlocks (N width) r) (hs : SupportedQuaternionBlocks (N width) s)
    (hc : RatPolyCoeffEqv (project j (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) s)) polyZero) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (polynomialProduct (coordinateFactor w K width) rest)
          (polyMul (jump (N width) r) (jump (N width) s)))) ≈
      (2 : Q')*crossPair w K width n i j r s := by
  have hp := pairCuts_perm hm
  have hn := List.nodup_cons.mp (List.nodup_cons.mp (hp.nodup_iff.mp (labels_nodup width))).2
  have hj := labels_lt width j (hp.mem_iff.mpr (List.mem_cons_of_mem i List.mem_cons_self))
  have he := erased_jump_pairing (N width) w K j (remainingHeat width rest) hj
    (fun h => hn.1 (List.mem_filter.mp h).1)
    (fun k hk => activeBlocks_lt width k (of_decide_eq_true (List.mem_filter.mp hk).2))
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
    hr hs hc
  exact Q'.eqv_trans _ _ _ (edge_term w K width n rest r s)
    (Q'.eqv_trans _ _ _ he (Q'.mul_eqv_congr_left _ _ _
      (marginalPair_perm (N width) w K (pair_remaining_perm hm) _ r s)))

/-- Exact same-object flow pin; only the dual tests need conditional centering. -/
theorem flowPair_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i))
    (hc : ∀ i, i < N width → RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (tests i))) polyZero)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    flowPair w K width n tests f ≈ (2 : Q')*marginalFlow w K width n tests f := by
  let mu := endpointWeight w K width n
  let z := jump (N width) f
  let factors := coordinateFactor w K width
  let xs := fun i => jump (N width) (tests i)
  have hp : RatPolyCoeffEqv (flow (family w K width tests))
      (singleSum factors xs (labels width)) := by
    rw [family_eq_indexed]
    exact flow_expansion _ _ _
  have he : flowPair w K width n tests f ≈ quaternionHaar (N width+N width)
      (polyMul (polyMul mu z) (singleSum factors xs (labels width))) :=
    haar_of_coeff ((hp.mul_right z).mul_left mu |>.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => mu | 1 => singleSum factors xs (labels width) | _ => z)))
  have hsum := haar_sum (N width+N width) (polyMul mu z)
    ((singleCuts (labels width)).map (fun c => polyMul (polynomialProduct factors c.2) (xs c.1)))
  simp only [List.map_map, Function.comp_def] at hsum
  refine Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hsum ?_)
  refine Q'.eqv_trans _ _ _ (sum_congr (singleCuts (labels width)) _
    (fun c => (2 : Q')*erasedPair w K width n c.1 f (tests c.1)) ?_)
    (sum_scale _ _ 2)
  intro c hm
  have hi := labels_lt width c.1 ((singleCuts_perm hm).mem_iff.mpr List.mem_cons_self)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3)))) (by decide)
    (fun | 0 => mu | 1 => z | 2 => polynomialProduct factors c.2 | _ => xs c.1)))
    (single_term w K width n c.1 c.2 hm hf (ht c.1 hi) (hc c.1 hi))

private theorem diagonal_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i))
    (hc : ∀ i, i < N width → RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (tests i))) polyZero) :
    quaternionHaar (N width+N width) (polyMul (endpointWeight w K width n)
      (singleSum (coordinateFactor w K width)
        (fun i => polyMul (jump (N width) (tests i)) (jump (N width) (tests i))) (labels width))) ≈
      (2 : Q')*marginalDiagonal w K width n tests := by
  have h := haar_sum (N width+N width) (endpointWeight w K width n)
    ((singleCuts (labels width)).map (fun c =>
      polyMul (polynomialProduct (coordinateFactor w K width) c.2)
        (polyMul (jump (N width) (tests c.1)) (jump (N width) (tests c.1)))))
  simp only [List.map_map, Function.comp_def] at h
  refine Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (sum_congr (singleCuts (labels width)) _
      (fun c => (2 : Q')*erasedPair w K width n c.1 (tests c.1) (tests c.1)) ?_) (sum_scale _ _ 2))
  intro c hm
  have hi := labels_lt width c.1 ((singleCuts_perm hm).mem_iff.mpr List.mem_cons_self)
  exact single_term w K width n c.1 c.2 hm (ht c.1 hi) (ht c.1 hi) (hc c.1 hi)

private theorem cross_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i))
    (hc : ∀ i, i < N width → RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (tests i))) polyZero) :
    quaternionHaar (N width+N width) (polyMul (endpointWeight w K width n)
      (pairSum (coordinateFactor w K width) (fun i => jump (N width) (tests i)) (labels width))) ≈
      (2 : Q')*marginalCross w K width n tests := by
  have h := haar_sum (N width+N width) (endpointWeight w K width n)
    ((pairCuts (labels width)).map (fun c =>
      polyMul (polynomialProduct (coordinateFactor w K width) c.2.2)
        (polyMul (jump (N width) (tests c.1)) (jump (N width) (tests c.2.1)))))
  simp only [List.map_map, Function.comp_def] at h
  refine Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (sum_congr (pairCuts (labels width)) _
      (fun c => (2 : Q')*crossPair w K width n c.1 c.2.1 (tests c.1) (tests c.2.1)) ?_)
    (sum_scale _ _ 2))
  intro c hm
  have hp := pairCuts_perm hm
  have hi := labels_lt width c.1 (hp.mem_iff.mpr List.mem_cons_self)
  have hj := labels_lt width c.2.1 (hp.mem_iff.mpr (List.mem_cons_of_mem c.1 List.mem_cons_self))
  exact pair_term w K width n c.1 c.2.1 c.2.2 hm (ht c.1 hi) (ht c.2.1 hj) (hc c.2.1 hj)

set_option maxHeartbeats 800000 in
/-- Exact cost pin, including active--fringe and fringe--fringe cross pairings.
The factor four comes from twice the Haar jump identity and the two
orientations in the quadratic cross term, not from pair overcounting. -/
theorem signedCost_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i))
    (hc : ∀ i, i < N width → RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (tests i))) polyZero) :
    signedCost w K width n tests ≈ (2 : Q')*marginalCost w K width n tests := by
  let mu := endpointWeight w K width n
  let d := singleSum (coordinateFactor w K width)
    (fun i => polyMul (jump (N width) (tests i)) (jump (N width) (tests i))) (labels width)
  let c := pairSum (coordinateFactor w K width) (fun i => jump (N width) (tests i)) (labels width)
  have hp : RatPolyCoeffEqv (cost (headFloor w) (family w K width tests))
      (polyAdd d (polyMul (cap (headFloor w)) (polyAdd c c))) := by
    rw [family_eq_indexed]
    exact cost_expansion _ _ _ _
  have hx := cross_pin w K width n tests ht hc
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_left mu))
    (Q'.eqv_trans _ _ _ (haar_add (N width+N width) mu d _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (diagonal_pin w K width n tests ht hc)
          (Q'.eqv_trans _ _ _ (haar_cap (N width+N width) mu (polyAdd c c) (headFloor w))
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (haar_add (N width+N width) mu c c)
              (Q'.add_eqv_congr' hx hx)))))
        (poly_identity_of_normal_eq
          (.add (.mul (.const 2) (.var 0))
            (.mul (.var 1) (.add (.mul (.const 2) (.var 2)) (.mul (.const 2) (.var 2)))))
          (.mul (.const 2) (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2))))
          (by decide) (fun
            | 0 => marginalDiagonal w K width n tests
            | 1 => headFloor w | _ => marginalCross w K width n tests))))

set_option maxHeartbeats 800000 in
/-- All retained centered tests share ONE original energy budget, with their
entire signed marginal cost explicit. No cardinality factor, independent
energy of the tests, changed action, or uniform-cost hypothesis is inserted. -/
theorem original_family_marginal_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i))
    (hc : ∀ i, i < N width → RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (tests i))) polyZero)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    headFloor w*(marginalFlow w K width n tests f * marginalFlow w K width n tests f) ≤
      energy w K width (terminalMessage w K width n) f * marginalCost w K width n tests := by
  let L := marginalFlow w K width n tests f
  let E := energy w K width (terminalMessage w K width n) f
  let C := marginalCost w K width n tests
  have hl := flowPair_pin w K width n tests ht hc hf
  have hr := signedCost_pin w K width n tests ht hc
  have h := original_family_flow_energy hw0 hw1 K width hK n tests ht hf
  have hleft : headFloor w*(flowPair w K width n tests f * flowPair w K width n tests f) ≈
      (4 : Q')*(headFloor w*(L*L)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hl) (Q'.mul_eqv_congr_left _ _ _ hl)))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1))))
        (.mul (.const 4) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (by decide)
        (fun | 0 => headFloor w | _ => L))
  have hright : ((2 : Q')*E)*signedCost w K width n tests ≈ (4 : Q')*(E*C) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr)
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
        (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => E | _ => C))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright)))
    (show (0 : Q') < (4 : Q') by decide)

/-- Actual-nu residuals give explicit polynomial tests on every coordinate.
Only active coordinates use the previously constructed polynomial reciprocal;
fringe residuals are inserted directly. Degrees remain finite, explicit data. -/
def residualTests {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (seeds : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat) : RatPoly :=
  let q := weightedResidual i (marginalWeight w K width n) (seeds i)
  if i ∈ activeBlocks width then dualTest hw0 hw1 K width hK n i q (degrees i) else q

theorem residualTests_supported {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (hs : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (seeds i))
    (i : Nat) (hi : i < N width) :
    SupportedQuaternionBlocks (N width) (residualTests hw0 hw1 K width hK n seeds degrees i) := by
  have hq := weightedResidual_supported i (marginalWeight_supported w K width n) (hs i hi)
  unfold residualTests
  by_cases ha : i ∈ activeBlocks width
  · rw [if_pos ha]
    exact dualTest_supported hw0 hw1 K width hK n i hq (degrees i)
  · rw [if_neg ha]
    exact hq

theorem residualTests_centered {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (seeds : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat) (hi : i < N width) :
    RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n))
      (residualTests hw0 hw1 K width hK n seeds degrees i))) polyZero := by
  unfold residualTests
  by_cases ha : i ∈ activeBlocks width
  · rw [if_pos ha]
    exact dualTest_centered hw0 hw1 K width hK n i ha
      (project_weightedResidual_zero i _ (seeds i)) (degrees i)
  · rw [if_neg ha]
    exact fringeResidual_centered w K width n i hi ha (seeds i)

/-- An instantiated finite-degree family estimate, not merely a theorem
assuming conditional centering. No decomposition of f is assumed or supplied. -/
theorem actualResidual_family_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (hs : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (seeds i))
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let tests := residualTests hw0 hw1 K width hK n seeds degrees
    headFloor w*(marginalFlow w K width n tests f * marginalFlow w K width n tests f) ≤
      energy w K width (terminalMessage w K width n) f * marginalCost w K width n tests :=
  original_family_marginal_energy hw0 hw1 K width hK n _
    (residualTests_supported hw0 hw1 K width hK n seeds degrees hs)
    (residualTests_centered hw0 hw1 K width hK n seeds degrees) hf

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.marginalFlow
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.marginalDiagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.marginalCross
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.marginalCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.flowPair_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.signedCost_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.original_family_marginal_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.residualTests
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.residualTests_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.residualTests_centered
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals.actualResidual_family_energy
