/-
# One-factor energy bound with the ENTIRE weighted product retained

Keep a certified supported endpoint weight a on each slice. If the actual
weighted input a*f has zero conditional Haar mean at one selected block,
removing that block's heat factor kills the mixed pairing exactly. The
removed-factor jump norm therefore equals its two diagonal norms. The
original one-factor heat floor and cap compare those SAME quantities to
the full edge, with every remaining heat factor and both weights retained.

The resulting cleared coefficient is headFloor/prefixCap, not a product
over links. Its nome dependence and conditional weighted-centering premise
are explicit. This is not a bound for arbitrary globally centered inputs,
an interacting OS gap, or a spacing/continuum statement.
-/

import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

/-- Literal product heat and both supplied endpoint weights, without normalization. -/
def edgeWeight (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a : RatPoly) : RatPoly :=
  polyMul (polyMul (productHeat n w K ids) a) (liftBoundary n a)

private theorem sum_congr (f g : Nat → RatPoly) : ∀ xs : List Nat,
    (∀ i, i ∈ xs → f i = g i) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | i::xs, h => by
      simp only [finitePolySum, h i List.mem_cons_self,
        sum_congr f g xs (fun j hj => h j (List.mem_cons_of_mem i hj))]

private theorem heatAt_eq_prefix (a b : Nat) (w : Q') (K : Nat) :
    heatAt a b w K = heatPrefix w K (scalarAt a b) := by
  unfold heatAt heatPrefix
  apply sum_congr
  intro spin hspin
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]

private def heatInterval {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    Interval blocks (heatAt a b w K) (prefixCap w) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  have hp : Supported blocks word := (Supported.coordinate ha).mul (Supported.coordinate hb).conj
  have hu : HaarCarrierEqv blocks (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb))
  rw [heatAt_eq_prefix]
  exact QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1 (SquareBound.scalar hp hu) K

private theorem cross_algebra (r a b f h : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyMul r a) b) (polyMul f h))
      (polyMul (polyMul (polyMul a f) (polyMul b h)) r) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 4)))
    (.mul (.mul (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4))) (.var 0))
    (by decide) (fun | 0 => r | 1 => a | 2 => b | 3 => f | _ => h)

/-- Weighted conditional centering kills the erased mixed term, with all
other heat factors and the complete opposite endpoint weight still present. -/
theorem erased_cross_zero (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (a f : RatPoly) (hc : RatPolyCoeffEqv (project i (polyMul a f)) polyZero) :
    quaternionHaar (n+n)
      (polyMul (edgeWeight n w K ids a) (polyMul f (liftBoundary n f))) ≈ 0 := by
  have hp : RatPolyCoeffEqv
      (polyMul (edgeWeight n w K ids a) (polyMul f (liftBoundary n f)))
      (polyMul (polyMul (polyMul a f) (liftBoundary n (polyMul a f))) (productHeat n w K ids)) := by
    simpa only [edgeWeight, lift_product] using
      cross_algebra (productHeat n w K ids) a (liftBoundary n a) f (liftBoundary n f)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (removed_pair_zero n w K i ids hi hnot hids (polyMul a f) (polyMul a f) hc)

private theorem jump_algebra (e f h : RatPoly) :
    RatPolyCoeffEqv
      (polyMul e (polyMul (polyAdd f (polyNeg h)) (polyAdd f (polyNeg h))))
      (polyAdd (polyMul e (polyAdd (polyMul f f) (polyMul h h)))
        (polyAdd (polyNeg (polyMul e (polyMul f h))) (polyNeg (polyMul e (polyMul f h))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))
    (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))))
      (.add (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))))
    (by decide) (fun | 0 => e | 1 => f | _ => h)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem zero_correction (a : Q') : a + (-(0 : Q') + -(0 : Q')) ≈ a :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.add (.neg (.const 0)) (.neg (.const 0)))) (.var 0)
    (by decide) (fun _ => a)

/-- Exact erased-edge equality; neither symmetry nor scalar normalization
is used to identify the two diagonal terms with the jump square. -/
theorem erased_jump_eq_diagonal (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (a f : RatPoly) (hc : RatPolyCoeffEqv (project i (polyMul a f)) polyZero) :
    quaternionHaar (n+n) (polyMul (edgeWeight n w K ids a)
      (polyMul (polyAdd f (polyNeg (liftBoundary n f))) (polyAdd f (polyNeg (liftBoundary n f))))) ≈
      quaternionHaar (n+n) (polyMul (edgeWeight n w K ids a)
        (polyAdd (polyMul f f) (polyMul (liftBoundary n f) (liftBoundary n f)))) := by
  have hz := Q'.eqv_trans _ _ _ (haar_neg (n+n) _)
    (Q'.neg_eqv_congr _ _ (erased_cross_zero n w K i ids hi hnot hids a f hc))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (jump_algebra (edgeWeight n w K ids a) f (liftBoundary n f)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr' hz hz)))
        (zero_correction _)))

private theorem difference_algebra (p q s : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd p (polyNeg q)) s)
      (polyAdd (polyMul p s) (polyNeg (polyMul q s))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
    (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
    (by decide) (fun | 0 => p | 1 => q | _ => s)

private theorem difference_haar (n : Nat) (p q s : RatPoly) :
    quaternionHaar n (polyMul (polyAdd p (polyNeg q)) s) ≈
      quaternionHaar n (polyMul p s) + -(quaternionHaar n (polyMul q s)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (difference_algebra p q s))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg n _)))

private theorem cap_haar (n : Nat) (c : Q') (s : RatPoly) :
    quaternionHaar n (polyMul (cap c) s) ≈ c*quaternionHaar n s :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c s)) (quaternionHaar_polySmul n c s)

private theorem certified_floor {n : Nat} {k s : RatPoly} {c : Q'}
    (K : Certificate n (polyAdd k (polyNeg (cap c)))) (S : Certificate n s) :
    c*quaternionHaar n s ≤ quaternionHaar n (polyMul k s) :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (K.mul S).haar_nonnegative
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (difference_haar n k (cap c) s)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ (cap_haar n c s))))))

private theorem certified_cap {n : Nat} {k s : RatPoly} {c : Q'}
    (K : Certificate n (polyAdd (cap c) (polyNeg k))) (S : Certificate n s) :
    quaternionHaar n (polyMul k s) ≤ c*quaternionHaar n s :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (K.mul S).haar_nonnegative
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (difference_haar n (cap c) k s)
      (Q'.add_eqv_congr' (cap_haar n c s) (Q'.eqv_refl _)))))

private theorem factor_algebra (k r a b s : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyMul (polyMul k r) a) b) s)
      (polyMul k (polyMul (polyMul (polyMul r a) b) s)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
    (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.var 4)))
    (by decide) (fun | 0 => k | 1 => r | 2 => a | 3 => b | _ => s)

private theorem factor_pairing (n : Nat) (w : Q') (K i : Nat) (ids : List Nat) (a s : RatPoly) :
    quaternionHaar (n+n) (polyMul (edgeWeight n w K (i::ids) a) s) ≈
      quaternionHaar (n+n)
        (polyMul (heatAt i (n+i) w K) (polyMul (edgeWeight n w K ids a) s)) :=
  haar_of_coeff (factor_algebra (heatAt i (n+i) w K) (productHeat n w K ids)
    a (liftBoundary n a) s)

private theorem support_pair {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) f :=
  fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (polyNeg f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hf s hs

private theorem scalar_commute (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => c)

/-- A cleared one-factor rate on the actual weighted conditional subspace.
The constants are independent of the number of remaining heat factors;
every factor and both endpoint weights are retained on each side. -/
theorem local_energy_floor (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (i : Nat) (ids : List Nat) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (A : Certificate n a) (hc : RatPolyCoeffEqv (project i (polyMul a f)) polyZero) :
    headFloor w * quaternionHaar (n+n) (polyMul (edgeWeight n w K (i::ids) a)
      (polyAdd (polyMul f f) (polyMul (liftBoundary n f) (liftBoundary n f)))) ≤
      prefixCap w * quaternionHaar (n+n) (polyMul (edgeWeight n w K (i::ids) a)
        (polyMul (polyAdd f (polyNeg (liftBoundary n f))) (polyAdd f (polyNeg (liftBoundary n f))))) := by
  let er := edgeWeight n w K ids a
  let d := polyAdd (polyMul f f) (polyMul (liftBoundary n f) (liftBoundary n f))
  let j := polyAdd f (polyNeg (liftBoundary n f))
  let E : Certificate (n+n) er :=
    ((productHeatCertificate n hw0 hw1 K hK ids hids).mul (certificate_extend n ha A)).mul
      (lift_certificate n A)
  let D : Certificate (n+n) d :=
    (Certificate.square f (support_pair hf)).add
      (Certificate.square (liftBoundary n f) (lift_supported hf n))
  let J : Certificate (n+n) (polyMul j j) :=
    Certificate.square j (supported_add (support_pair hf) (support_neg (lift_supported hf n)))
  have hflo := certified_floor
    (heatAt_floorCertificate (show i < n+n by omega) (show n+i < n+n by omega) hw0 hw1 K hK)
    (E.mul J)
  have hcap := certified_cap
    (heatInterval (show i < n+n by omega) (show n+i < n+n by omega) hw0 hw1 K).upper
    (E.mul D)
  have hd : quaternionHaar (n+n) (polyMul (edgeWeight n w K (i::ids) a) d) ≤
      prefixCap w*quaternionHaar (n+n) (polyMul er d) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (factor_pairing n w K i ids a d)) hcap
  have hj : headFloor w*quaternionHaar (n+n) (polyMul er d) ≤
      quaternionHaar (n+n) (polyMul (edgeWeight n w K (i::ids) a) (polyMul j j)) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (erased_jump_eq_diagonal n w K i ids hi hnot hids a f hc))))
      (Q'.le_trans' _ _ _ hflo
        (Q'.le_of_eqv (Q'.eqv_symm (factor_pairing n w K i ids a (polyMul j j)))))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (headFloor w) hd (Q'.le_of_lt (headFloor_positive hw0 hw1)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (scalar_commute _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ (prefixCap w) hj (prefixCap_nonnegative hw0)))

-- The standard perm_cons_erase carries Classical.choice in this tree.
-- Selecting a Nat index needs only the explicit finite equality decision.
private def eraseIndex (target : Nat) : List Nat → List Nat
  | [] => []
  | head::tail => if head = target then tail else head::eraseIndex target tail

private theorem select_perm (target : Nat) : ∀ {ids : List Nat},
    target ∈ ids → ids.Perm (target::eraseIndex target ids)
  | [], h => False.elim (List.not_mem_nil h)
  | head::tail, h => by
      by_cases he : head = target
      · subst head
        simpa only [eraseIndex, if_pos rfl] using (List.Perm.refl (target::tail))
      · have ht : target ∈ tail :=
          (List.mem_cons.mp h).resolve_left (fun heq => he heq.symm)
        rw [eraseIndex, if_neg he]
        exact (List.Perm.cons head (select_perm target ht)).trans
          (List.Perm.swap target head (eraseIndex target tail))

private theorem mem_of_mem_erase (target : Nat) : ∀ {ids : List Nat} {j : Nat},
    j ∈ eraseIndex target ids → j ∈ ids
  | [], _, h => False.elim (List.not_mem_nil h)
  | head::tail, j, h => by
      by_cases he : head = target
      · rw [eraseIndex, if_pos he] at h
        exact List.mem_cons_of_mem head h
      · rw [eraseIndex, if_neg he] at h
        rcases List.mem_cons.mp h with hj | ht
        · exact List.mem_cons.mpr (Or.inl hj)
        · exact List.mem_cons_of_mem head (mem_of_mem_erase target ht)

private theorem not_mem_erase (target : Nat) : ∀ {ids : List Nat},
    ids.Nodup → target ∉ eraseIndex target ids
  | [], _ => List.not_mem_nil
  | head::tail, hn => by
      have hnd := List.nodup_cons.mp hn
      by_cases he : head = target
      · subst head
        simpa only [eraseIndex, if_pos rfl] using hnd.1
      · rw [eraseIndex, if_neg he]
        intro hm
        rcases List.mem_cons.mp hm with hj | ht
        · exact he hj.symm
        · exact not_mem_erase target hnd.2 ht

/-- The selected coordinate can occur anywhere in the actual finite list.
Constructive first-occurrence selection preserves the full original product;
Nodup ensures that no copy of the selected heat factor remains behind. -/
theorem local_energy_floor_of_mem (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (i : Nat) (ids : List Nat) (hn : ids.Nodup) (hi : i ∈ ids)
    (hids : ∀ j, j ∈ ids → j < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (A : Certificate n a) (hc : RatPolyCoeffEqv (project i (polyMul a f)) polyZero) :
    headFloor w * quaternionHaar (n+n) (polyMul (edgeWeight n w K ids a)
      (polyAdd (polyMul f f) (polyMul (liftBoundary n f) (liftBoundary n f)))) ≤
      prefixCap w * quaternionHaar (n+n) (polyMul (edgeWeight n w K ids a)
        (polyMul (polyAdd f (polyNeg (liftBoundary n f))) (polyAdd f (polyNeg (liftBoundary n f))))) := by
  have hp : RatPolyCoeffEqv (productHeat n w K ids)
      (productHeat n w K (i::eraseIndex i ids)) :=
    polynomialProduct_perm _ (select_perm i hi)
  have he : RatPolyCoeffEqv (edgeWeight n w K ids a)
      (edgeWeight n w K (i::eraseIndex i ids) a) :=
    (hp.mul_right a).mul_right (liftBoundary n a)
  have h := local_energy_floor n hw0 hw1 K hK i (eraseIndex i ids)
    (hids i hi) (not_mem_erase i hn)
    (fun j hj => hids j (mem_of_mem_erase i hj)) ha hf A hc
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (he.mul_right _))))
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (he.symm.mul_right _)))))

end YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

#print axioms YMGap.Continuum.SU2QuaternionWeightedProductLocalGap.edgeWeight
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductLocalGap.erased_cross_zero
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductLocalGap.erased_jump_eq_diagonal
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductLocalGap.local_energy_floor
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductLocalGap.local_energy_floor_of_mem
