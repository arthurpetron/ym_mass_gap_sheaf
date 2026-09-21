/-
# A constructed nonnegative Ward response for the whole signed plaquette sum

The incident-gradient tests are actual polynomials, independent of nome and
cutoff. Their head derivatives equal those of the entire signed observable,
including arbitrary signs and cancellations. Consequently the total score
pairs with that SAME observable to minus a sum of nonnegative full-action
energies. The bounded-star family cost gives the corresponding energy /
variance inequality without an extra family-size multiplier.

Nonnegativity is not a positive energy floor. Diagonal costs, scaling
control, the OS norm and continuum survival remain separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGradient
import YMGap.Continuum.BF4ExactSlabWardGradientEnergy

namespace YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabWardFamilyCost
open YMGap.Continuum.BF4ExactSlabWardGradientEnergy
open YMGap.Continuum.BF4ExactSlabPlaquetteGradient
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarSparseFamilyCost
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- A concrete test for each witnessed physical link; no analytic test input. -/
def tests (extent i j : Nat) (c : Nat → Q') (link : PhysicalLink extent) : RatPoly :=
  test extent link.val link.property i j c

/-- The test's pullback is the derivative of the WHOLE observable on the
original Haar carrier. Both double-reindex support guards are discharged. -/
theorem test_gradient_pin (extent : Nat) (link : PhysicalLink extent)
    {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    let swap := linkHeadSwap extent link.val link.property
    HaarCarrierEqv (blocks extent) (reindexQuaternionPolynomial swap (tests extent i j c link))
      (angularDerivative i j (reindexQuaternionPolynomial swap (observable extent c))) := by
  let swap := linkHeadSwap extent link.val link.property
  let df := angularDerivative i j (reindexQuaternionPolynomial swap (incidentObservable extent link.val c))
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _)
    (List.idxOf_lt_length_of_mem link.property)
  have hd := angularDerivative_supported hb hi hj
    (reindex_supported swap (incidentObservable extent link.val c))
  exact HaarCarrierEqv.trans
    (carrierOfPrefix (reindex_supported swap (reindexQuaternionPolynomial swap df)) hd
      (reindex_twice_prefix swap df))
    (RatPolyCoeffEqv.haarCarrier
      (observable_derivative_incident extent link.val link.property hi hj c).symm)

private theorem normalized_pair_sum {Index : Type} {blocks : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) (f : RatPoly) (s : Index → RatPoly) :
    ∀ xs : List Index,
    normalizedMoment blocks W (polyMul f (finitePolySum s xs)) hW ≈
      listQSum (fun l => normalizedMoment blocks W (polyMul f (s l)) hW) xs
  | [] => Q'.eqv_trans _ _ _
      (normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl W) (RatPolyCoeffEqv.mul_zero_right f))
      (normalized_zero hW)
  | l :: xs => Q'.eqv_trans _ _ _
      (normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl W)
        (RatPolyCoeffEqv.mul_add_right f (s l) (finitePolySum s xs)))
      (Q'.eqv_trans _ _ _ (normalizedMoment_add hW)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (normalized_pair_sum hW f s xs)))

private theorem sum_neg {Index : Type} (e : Index → Q') : ∀ xs : List Index,
    listQSum (fun l => -(e l)) xs ≈ -(listQSum e xs)
  | [] => by change (0 : Q') ≈ -0; decide
  | l :: xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_neg e xs))
      (Q'.eqv_symm (Q'.neg_add_eqv_split (e l) (listQSum e xs)))

variable (w : Q') (K extent : Nat)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- All energies use the same entire signed observable and the same original
normalizer, though each derivative uses its own selected-link coordinates. -/
def energySum (i j : Nat) (c : Nat → Q') (xs : List (PhysicalLink extent))
    (hW : (0 : Q') < quaternionHaar (blocks extent) W) : Q' :=
  listQSum (fun link => linkEnergy w K extent link.val link.property i j (observable extent c) hW) xs

/-- Exact sign and whole-observable response. This holds even with repeated
links; only the subsequent fixed-row cost estimate needs Nodup. -/
theorem response_energy {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q')
    (xs : List (PhysicalLink extent)) (hW : (0 : Q') < quaternionHaar (blocks extent) W) :
    normalizedMoment (blocks extent) W
      (polyMul (observable extent c) (totalScore w K extent i j (tests extent i j c) xs)) hW ≈
      -(energySum w K extent i j c xs hW) := by
  let s := score w K extent i j (tests extent i j c)
  let e : PhysicalLink extent → Q' := fun link =>
    linkEnergy w K extent link.val link.property i j (observable extent c) hW
  have hpoint : ∀ link : PhysicalLink extent,
      normalizedMoment (blocks extent) W (polyMul (observable extent c) (s link)) hW ≈ -(e link) := by
    intro link
    exact normalized_pair_energy w K extent link.val link.property hi hj
      (tests extent i j c link) (observable extent c) (observable_supported extent c)
      (test_gradient_pin extent link hi hj c) hW
  have hsum := listQSum_congr hpoint xs
  exact Q'.eqv_trans _ _ _ (normalized_pair_sum hW (observable extent c) s xs)
    (Q'.eqv_trans _ _ _ hsum (sum_neg e xs))

theorem energySum_nonnegative (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q')
    (xs : List (PhysicalLink extent)) (hW : (0 : Q') < quaternionHaar (blocks extent) W) :
    (0 : Q') ≤ energySum w K extent i j c xs hW :=
  listQSum_nonnegative_on _ xs (fun link _ =>
    linkEnergy_nonnegative w K extent link.val link.property hw0 hw1 hK hi hj (observable extent c) hW)

/-- A constructed nonnegative-energy response feeds the bounded-star family
inequality. There is no assumed or concluded strict energy floor.
All diagonal costs are still the actual original-action score moments. -/
theorem energySum_squared_le_variance_cost (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q')
    (xs : List (PhysicalLink extent)) (hxs : xs.Nodup) :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    let E := energySum w K extent i j c xs hW
    E * E ≤ normalizedVariance (blocks extent) W (observable extent c) hW *
      (Q'.ofNat 25 * listQSum (fun link => normalizedMoment (blocks extent) W
        (polyMul (score w K extent i j (tests extent i j c) link)
          (score w K extent i j (tests extent i j c) link)) hW) xs) := by
  let hW := fullPartition_positive w K extent hw0 hw1 hK
  let E := energySum w K extent i j c xs hW
  let response := normalizedMoment (blocks extent) W
    (polyMul (observable extent c) (totalScore w K extent i j (tests extent i j c) xs)) hW
  have hr : response ≈ -E := response_energy w K extent hi hj c xs hW
  have hs : response * response ≈ E * E := Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hr) (Q'.mul_eqv_congr_left _ _ _ hr))
    (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => E))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hs)
    (totalScore_response_bound w K extent hw0 hw1 hK hi hj (tests extent i j c) xs hxs
      (fun link _ => test_local extent link.val link.property hi hj c)
      (observable extent c) (observable_supported extent c))

end YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy.test_gradient_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy.response_energy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy.energySum_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy.energySum_squared_le_variance_cost
