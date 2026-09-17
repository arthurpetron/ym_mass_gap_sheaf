/-
# A one-factor dual estimate for the energy of an arbitrary observable

Erase only kinetic factor i and retain the ENTIRE certified endpoint weight a
on both slices. Write d=K_without_i(a) and nu'=a*d. For P_i(a*r)=0,
the two erased mixed pairings vanish, whereas f is arbitrary. Symmetry and
Cauchy--Schwarz on jumps therefore control H[nu'*f*r]^2 by the ORIGINAL
full-edge energy of f and H[nu'*r^2], with one heat-floor factor.

This is not the old estimate on energy(r), or on energy(A*f). It does not
construct a conditional reciprocal or change nu' to the actual marginal
a*K(a). That comparison, and a collective spatial budget, remain open.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry

namespace YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (kernel_pairing_swap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTwoSliceSwap
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem support_pair {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) f :=
  fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (polyNeg f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hf s hs

def jump (n : Nat) (f : RatPoly) : RatPoly := polyAdd f (polyNeg (liftBoundary n f))

theorem jump_supported {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) (jump n f) :=
  supported_add (support_pair hf) (support_neg (lift_supported hf n))

/-- Original heat factors on ANY selected list, including a list with one
factor erased, have the concrete slice-swap symmetry. -/
theorem productHeat_swap (n : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i < n) →
    PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial (swap n) (productHeat n w K ids))
      (productHeat n w K ids)
  | [], _ => PaddedPolynomialCoeffEqv.of_prefix (reindex_polyOne_prefix _)
  | i::ids, hids => by
      have hi := hids i List.mem_cons_self
      have hp : QuaternionPrefixPolyQuaternionEqv (n+n)
          (reindexPolyQuaternion (swap n)
            (PolyQuaternion.mul (PolyQuaternion.coordinateVariable i)
              (PolyQuaternion.conj (PolyQuaternion.coordinateVariable (n+i)))))
          (PolyQuaternion.mul (PolyQuaternion.coordinateVariable (n+i))
            (PolyQuaternion.conj (PolyQuaternion.coordinateVariable i))) := by
        rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_conj]
        exact (reindex_coordinateVariable_prefix (swap n) (by omega) (swap_upper n i hi)).mul
          (reindex_coordinateVariable_prefix (swap n) (by omega) (swap_lower n i hi)).conj
      have hc (spin : Nat) : PaddedPolynomialCoeffEqv (n+n)
          (reindexQuaternionPolynomial (swap n) (characterPolynomial (scalarAt i (n+i)) spin))
          (characterPolynomial (scalarAt (n+i) i) spin) :=
        (PaddedPolynomialCoeffEqv.of_prefix
          (reindexQuaternionPolynomial_character_prefix (swap n) _ spin)).trans
          ((PaddedPolynomialCoeffEqv.of_prefix hp.scalar).character spin)
      have hk : PaddedPolynomialCoeffEqv (n+n)
          (reindexQuaternionPolynomial (swap n) (heatAt i (n+i) w K)) (heatAt i (n+i) w K) := by
        apply PaddedPolynomialCoeffEqv.trans (q := heatAt (n+i) i w K) ?_
          (PaddedPolynomialCoeffEqv.of_coeff (heatAt_symm (n+i) i w K))
        unfold heatAt
        induction List.range (K+1) with
        | nil => exact .refl _ _
        | cons s ss ih =>
            simp only [finitePolySum, reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_smul]
            exact ((hc s).smul _).add ih
      change PaddedPolynomialCoeffEqv (n+n)
        (reindexQuaternionPolynomial (swap n) (polyMul (heatAt i (n+i) w K) (productHeat n w K ids))) _
      rw [reindexQuaternionPolynomial_mul]
      exact hk.mul (productHeat_swap n w K ids (fun j hj => hids j (List.mem_cons_of_mem i hj)))

/-- The marginal of the remaining kernel, with the whole endpoint retained. -/
def marginalPair (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f r : RatPoly) : Q' :=
  H n (polyMul (polyMul a (productMap n w K ids a)) (polyMul f r))

private theorem edge_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f r : RatPoly) :
    weightedPair (n+n) (edgeWeight n w K ids a) f (liftBoundary n r) ≈
      H (n+n) (polyMul (polyMul (productHeat n w K ids) (polyMul a f))
        (liftBoundary n (polyMul a r))) := by
  rw [lift_product]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 3) (.var 4)) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 4)))
    (by decide) (fun
      | 0 => productHeat n w K ids
      | 1 => a
      | 2 => liftBoundary n a
      | 3 => f
      | _ => liftBoundary n r))

private theorem upper_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f r : RatPoly) :
    weightedPair (n+n) (edgeWeight n w K ids a) (liftBoundary n f) (liftBoundary n r) ≈
      marginalPair n w K ids a f r := by
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul (liftBoundary n f) (liftBoundary n r)) (edgeWeight n w K ids a))
      (polyMul (productHeat n w K ids) (polyMul a (liftBoundary n (polyMul a (polyMul f r))))) := by
    simp only [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 3) (.var 4)) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => productHeat n w K ids
        | 1 => a
        | 2 => liftBoundary n a
        | 3 => liftBoundary n f
        | _ => liftBoundary n r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (productMap_pairing n w K ids a (polyMul a (polyMul f r))))
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 3))) (.var 1))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (by decide) (fun | 0 => a | 1 => productMap n w K ids a | 2 => f | _ => r))))

private theorem lower_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {a f r : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (hr : SupportedQuaternionBlocks n r) :
    weightedPair (n+n) (edgeWeight n w K ids a) f r ≈ marginalPair n w K ids a f r := by
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul f r) (edgeWeight n w K ids a))
      (polyMul (polyMul (productHeat n w K ids) (polyMul a (polyMul f r))) (liftBoundary n a)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 3) (.var 4)) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.var 2))
      (by decide) (fun
        | 0 => productHeat n w K ids
        | 1 => a
        | 2 => liftBoundary n a
        | 3 => f
        | _ => r)
  have hs := kernel_pairing_swap (productHeat_supported n w K ids hids)
    (supported_polyMul ha (supported_polyMul hf hr)) ha (productHeat_swap n w K ids hids)
  have hu := Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (productHeat n w K ids) a _))
    (Q'.eqv_symm (productMap_pairing n w K ids a (polyMul a (polyMul f r))))
  have he : H n (polyMul (polyMul a (polyMul f r)) (productMap n w K ids a)) ≈
      marginalPair n w K ids a f r := haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 3))) (.var 1))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => a | 1 => productMap n w K ids a | 2 => f | _ => r))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp) (Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _ hu he))

private theorem mixed_zero (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (a r f : RatPoly) (hc : RatPolyCoeffEqv (project i (polyMul a r)) polyZero) :
    weightedPair (n+n) (edgeWeight n w K ids a) r (liftBoundary n f) ≈ 0 :=
  Q'.eqv_trans _ _ _ (edge_pair n w K ids a r f)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 1) (.var 2)) (.var 0)) (by decide)
      (fun | 0 => productHeat n w K ids | 1 => polyMul a r | _ => liftBoundary n (polyMul a f))))
      (removed_pair_zero n w K i ids hi hnot hids (polyMul a r) (polyMul a f) hc))

private theorem mixed_zero_right (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    {a r f : RatPoly} (ha : SupportedQuaternionBlocks n a)
    (hr : SupportedQuaternionBlocks n r) (hf : SupportedQuaternionBlocks n f)
    (hc : RatPolyCoeffEqv (project i (polyMul a r)) polyZero) :
    weightedPair (n+n) (edgeWeight n w K ids a) f (liftBoundary n r) ≈ 0 :=
  Q'.eqv_trans _ _ _ (edge_pair n w K ids a f r)
    (Q'.eqv_trans _ _ _
      (kernel_pairing_swap (productHeat_supported n w K ids hids)
        (supported_polyMul ha hf) (supported_polyMul ha hr) (productHeat_swap n w K ids hids))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (edge_pair n w K ids a r f))
        (mixed_zero n w K i ids hi hnot hids a r f hc)))

private theorem haar_neg (n : Nat) : ∀ p : RatPoly, H n (polyNeg p) ≈ -(H n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv _ _) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem jump_expansion (n : Nat) (e f r : RatPoly) :
    weightedPair (n+n) e (jump n f) (jump n r) ≈
      weightedPair (n+n) e f r + -(weightedPair (n+n) e f (liftBoundary n r)) +
      (-(weightedPair (n+n) e r (liftBoundary n f)) +
        weightedPair (n+n) e (liftBoundary n f) (liftBoundary n r)) := by
  have hp : RatPolyCoeffEqv (polyMul (polyMul (jump n f) (jump n r)) e)
      (polyAdd
        (polyAdd (polyMul (polyMul f r) e) (polyNeg (polyMul (polyMul f (liftBoundary n r)) e)))
        (polyAdd (polyNeg (polyMul (polyMul r (liftBoundary n f)) e))
          (polyMul (polyMul (liftBoundary n f) (liftBoundary n r)) e))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))) (.var 4))
      (.add (.add (.mul (.mul (.var 0) (.var 2)) (.var 4))
        (.neg (.mul (.mul (.var 0) (.var 3)) (.var 4))))
        (.add (.neg (.mul (.mul (.var 2) (.var 1)) (.var 4)))
          (.mul (.mul (.var 1) (.var 3)) (.var 4))))
      (by decide) (fun | 0 => f | 1 => liftBoundary n f | 2 => r | 3 => liftBoundary n r | _ => e)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg _ _)))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (haar_neg _ _) (Q'.eqv_refl _)))))

/-- Only the dual test r is centered; the energy observable f is arbitrary. -/
theorem erased_jump_pairing (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    {a f r : RatPoly} (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (hc : RatPolyCoeffEqv (project i (polyMul a r)) polyZero) :
    weightedPair (n+n) (edgeWeight n w K ids a) (jump n f) (jump n r) ≈
      (2 : Q')*marginalPair n w K ids a f r :=
  Q'.eqv_trans _ _ _ (jump_expansion n _ f r)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (lower_pair n w K ids hids ha hf hr)
          (Q'.neg_eqv_congr _ _ (mixed_zero_right n w K i ids hi hnot hids ha hr hf hc)))
        (Q'.add_eqv_congr'
          (Q'.neg_eqv_congr _ _ (mixed_zero n w K i ids hi hnot hids a r f hc))
          (upper_pair n w K ids a f r)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.const 0))) (.add (.neg (.const 0)) (.var 0)))
        (.mul (.const 2) (.var 0)) (by decide) (fun _ => marginalPair n w K ids a f r)))

/-- The one-factor floor controls the energy of f itself, not the energy of
the centered test or an observable multiplied by a conditional normalizer. -/
theorem one_factor_dual_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (i : Nat) (ids : List Nat) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) {a f r : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (hr : SupportedQuaternionBlocks n r) (A : Certificate n a)
    (hc : RatPolyCoeffEqv (project i (polyMul a r)) polyZero) :
    ((2 : Q')*headFloor w) *
      (marginalPair n w K ids a f r * marginalPair n w K ids a f r) ≤
      weightedPair (n+n) (edgeWeight n w K (i::ids) a) (jump n f) (jump n f) *
        marginalPair n w K ids a r r := by
  let e := edgeWeight n w K ids a
  let E : Certificate (n+n) e :=
    ((productHeatCertificate n hw0 hw1 K hK ids hids).mul (certificate_extend n ha A)).mul
      (lift_certificate n A)
  let L := marginalPair n w K ids a f r
  let R := marginalPair n w K ids a r r
  let J := weightedPair (n+n) e (jump n f) (jump n f)
  let Jfull := weightedPair (n+n) (edgeWeight n w K (i::ids) a) (jump n f) (jump n f)
  have hR : (0 : Q') ≤ R := Q'.le_trans' _ _ _
    (E.square_insertion_nonnegative (liftBoundary n r) (lift_supported hr n))
    (Q'.le_of_eqv (upper_pair n w K ids a r r))
  have hcross := erased_jump_pairing n w K i ids hi hnot hids ha hf hr hc
  have hdiag := erased_jump_pairing n w K i ids hi hnot hids ha hr hr hc
  have hcs := weighted_cauchySchwarz (n+n) e (jump n f) (jump n r) E
    (jump_supported hf) (jump_supported hr)
  have hbase : ((2 : Q')*L)*((2 : Q')*L) ≤ J*((2 : Q')*R) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hcross hcross))
      (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hdiag)))
  have hfloor : headFloor w * J ≤ Jfull := by
    have h := certified_floor
      (heatAt_floorCertificate (show i < n+n by omega) (show n+i < n+n by omega) hw0 hw1 K hK)
      (E.mul (.square (jump n f) (jump_supported hf)))
    have hleft : J ≈ H (n+n) (polyMul e (polyMul (jump n f) (jump n f))) :=
      haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
    have hright : Jfull ≈ H (n+n)
        (polyMul (heatAt i (n+i) w K) (polyMul e (polyMul (jump n f) (jump n f)))) :=
      Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (factor_pairing n w K i ids a _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hleft))
      (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv hright))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (headFloor w) hbase
    (Q'.le_of_lt (headFloor_positive hw0 hw1))
  have hbound : headFloor w * (((2 : Q')*L)*((2 : Q')*L)) ≤ Jfull*((2 : Q')*R) :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hfloor (Q'.mul_nonneg _ _ (by decide) hR)))
  have hl : headFloor w * (((2 : Q')*L)*((2 : Q')*L)) ≈
      (2 : Q')*(((2 : Q')*headFloor w)*(L*L)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1))))
      (.mul (.const 2) (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => headFloor w | _ => L)
  have hr' : Jfull*((2 : Q')*R) ≈ (2 : Q')*(Jfull*R) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 2) (.var 1)))
      (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => Jfull | _ => R)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hr')))
    (show (0 : Q') < (2 : Q') by decide)

end YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy

#print axioms YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy.productHeat_swap
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy.marginalPair
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy.erased_jump_pairing
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy.one_factor_dual_bound
