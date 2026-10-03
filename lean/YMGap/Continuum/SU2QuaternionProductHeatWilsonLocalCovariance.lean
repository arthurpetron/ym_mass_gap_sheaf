/-
# Word-local conditional source cost under the ORIGINAL full joint heat

The actual hybrid sweep integrates only word lower coordinates, retaining
all other lower/upper coordinates and the complete certified output action.
Weighted orthogonality gives conditional Pythagoras without an exposure
hypothesis, source independence, or an interacting variance substitution.
-/

import YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance
import YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
import YMGap.Continuum.SU2QuaternionProductHeatWilsonStein

namespace YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt productMap_fundamental_word)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo (productMap_fundamental_square)
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n


open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.SU2QuaternionWeightedProjectionSweep
open YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum (pair_vacuum)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance (fullSourceLoss wordCovarianceRate)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonStein
open YMGap.Continuum.SU2QuaternionSelectedHeatStein
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarAngularIBP (angularDerivative_independent_zero)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_congr)
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_smul)

local infixl:70 " ⋄ " => PolyQuaternion.mul

private def centered (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (q : RatPoly) : RatPoly :=
  polyAdd q (polySmul (-1) (liftBoundary n (productMap n w K ids q)))

private theorem support_mono {n : Nat} {q : RatPoly} (hq : SupportedQuaternionBlocks n q) :
    SupportedQuaternionBlocks (n+n) q :=
  fun term hm => Nat.le_trans (hq term hm) (Nat.mul_le_mul_left 4 (by omega))

private theorem word_supported (n : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es, (∀ e, e ∈ es → block e < n) → QuaternionSupported n (wordAt block es)
  | [], _ =>
      ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
        (fun _ h => False.elim (List.not_mem_nil h)), (fun _ h => False.elim (List.not_mem_nil h))⟩
  | e::es, h => by
      have he : QuaternionSupported n (orientedCoordinateQuaternion (block e) e.reverse) := by
        cases e.reverse
        · exact QuaternionSupported.coordinate (h e List.mem_cons_self)
        · exact (QuaternionSupported.coordinate (h e List.mem_cons_self)).conj
      exact he.mul (word_supported n block es (fun f hf => h f (List.mem_cons_of_mem e hf)))

private theorem centered_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q : RatPoly} (hq : SupportedQuaternionBlocks n q) :
    SupportedQuaternionBlocks (n+n) (centered n w K ids q) :=
  supported_add (support_mono hq)
    (polySmul_supported (lift_supported (productMap_supported n w K ids hids hq) n) (-1))

private theorem haar_sub (n : Nat) (p q : RatPoly) :
    H n (polyAdd p (polySmul (-1) q)) ≈ H n p-H n q :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) q)
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))

private theorem weighted_difference (n : Nat) (W x y X Y : RatPoly) :
    weightedPair n W (polyAdd x (polySmul (-1) X)) (polyAdd y (polySmul (-1) Y)) ≈
      (weightedPair n W x y-weightedPair n W x Y)-
        (weightedPair n W X y-weightedPair n W X Y) := by
  have right (p : RatPoly) : weightedPair n W p (polyAdd y (polySmul (-1) Y)) ≈
      weightedPair n W p y-weightedPair n W p Y :=
    Q'.eqv_trans _ _ _ (weighted_symm n W _ _)
      (Q'.eqv_trans _ _ _ (weighted_add_left n W _ _ p)
        (Q'.add_eqv_congr' (weighted_symm n W y p)
          (Q'.eqv_trans _ _ _ (weighted_smul_left n W (-1) Y p)
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (weighted_symm n W Y p))
              (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
                (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))))
  exact Q'.eqv_trans _ _ _ (weighted_add_left n W _ _ _)
    (Q'.add_eqv_congr' (right x)
      (Q'.eqv_trans _ _ _ (weighted_smul_left n W (-1) X _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (right X))
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))))

private theorem lower_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (D x y : RatPoly) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D)) x y ≈
      H n (polyMul D (productMap n w K ids (polyMul x y))) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3))) (by decide)
      (fun | 0 => x | 1 => y | 2 => productHeat n w K ids | _ => liftBoundary n D)))
    (Q'.eqv_symm (productMap_pairing n w K ids (polyMul x y) D))

private theorem mixed_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (D x Y : RatPoly) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D)) x (liftBoundary n Y) ≈
      H n (polyMul D (polyMul Y (productMap n w K ids x))) := by
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul x (liftBoundary n Y))
        (polyMul (productHeat n w K ids) (liftBoundary n D)))
      (polyMul (productHeat n w K ids) (polyMul x (liftBoundary n (polyMul D Y)))) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 2) (.mul (.var 0) (.mul (.var 3) (.var 1)))) (by decide)
      (fun | 0 => x | 1 => liftBoundary n Y | 2 => productHeat n w K ids | _ => liftBoundary n D)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (productMap_pairing n w K ids x (polyMul D Y)))
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc D Y _)))

private theorem upper_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (D X Y : RatPoly)
    (hD : SupportedQuaternionBlocks n D) (hX : SupportedQuaternionBlocks n X)
    (hY : SupportedQuaternionBlocks n Y) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D))
      (liftBoundary n X) (liftBoundary n Y) ≈ H n (polyMul D (polyMul X Y)) := by
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul (liftBoundary n X) (liftBoundary n Y))
        (polyMul (productHeat n w K ids) (liftBoundary n D)))
      (polyMul (productHeat n w K ids) (liftBoundary n (polyMul D (polyMul X Y)))) := by
    rw [lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 2) (.mul (.var 3) (.mul (.var 0) (.var 1)))) (by decide)
      (fun
        | 0 => liftBoundary n X
        | 1 => liftBoundary n Y
        | 2 => productHeat n w K ids
        | _ => liftBoundary n D)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (productHeat_upper_marginal n w K ids hnd hids _
      (supported_polyMul hD (supported_polyMul hX hY)))

private theorem centered_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (D q f : RatPoly)
    (hD : SupportedQuaternionBlocks n D) (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D))
      (centered n w K ids q) (centered n w K ids f) ≈
      H n (polyMul D (polyAdd (productMap n w K ids (polyMul q f))
        (polySmul (-1) (polyMul (productMap n w K ids q) (productMap n w K ids f))))) := by
  let W := polyMul (productHeat n w K ids) (liftBoundary n D)
  let Q := productMap n w K ids q
  let F := productMap n w K ids f
  have hQ := productMap_supported n w K ids hids hq
  have hF := productMap_supported n w K ids hids hf
  have hxy := lower_pair n w K ids D q f
  have hxY := mixed_pair n w K ids D q F
  have hXy := Q'.eqv_trans _ _ _ (weighted_symm (n+n) W _ _)
    (mixed_pair n w K ids D f Q)
  have hXY := upper_pair n w K ids hnd hids D Q F hD hQ hF
  have hcommon : H n (polyMul D (polyMul F Q)) ≈ H n (polyMul D (polyMul Q F)) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_comm F Q).mul_left D)
  have hdiff := weighted_difference (n+n) W q f (liftBoundary n Q) (liftBoundary n F)
  have hs : weightedPair (n+n) W (centered n w K ids q) (centered n w K ids f) ≈
      (H n (polyMul D (productMap n w K ids (polyMul q f)))-H n (polyMul D (polyMul Q F)))-
        (H n (polyMul D (polyMul Q F))-H n (polyMul D (polyMul Q F))) :=
    Q'.eqv_trans _ _ _ hdiff
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' hxy
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ hxY hcommon)))
        (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hXy (Q'.neg_eqv_congr _ _ hXY))))
  have hreorder : RatPolyCoeffEqv
      (polyMul D (polyAdd (productMap n w K ids (polyMul q f)) (polySmul (-1) (polyMul Q F))))
      (polyAdd (polyMul D (productMap n w K ids (polyMul q f)))
        (polySmul (-1) (polyMul D (polyMul Q F)))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right (-1) D _))
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 1)))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun
        | 0 => H n (polyMul D (productMap n w K ids (polyMul q f)))
        | _ => H n (polyMul D (polyMul Q F))))
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff hreorder) (haar_sub n _ _))))

/-- The actual conditional source residual on the ORIGINAL doubled carrier.
Only the supplied selected lower slots are swept; all others are retained. -/
def localSourceResidual (n : Nat) (w : Q') (K : Nat) (selected : List Nat)
    (q : RatPoly) : RatPoly :=
  polyAdd q (polySmul (-1) (hybridSweep n w K selected q))

/-- Literal original-joint square cost, not an observable OWN variance. -/
def localSourceLoss (n : Nat) (w : Q') (K : Nat) (ids selected : List Nat)
    (q R : RatPoly) : Q' :=
  weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R))
    (localSourceResidual n w K selected q) (localSourceResidual n w K selected q)

private theorem local_supported (n : Nat) (w : Q') (K : Nat) (selected : List Nat)
    (hs : ∀ i, i ∈ selected → i < n) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (n+n) q) :
    SupportedQuaternionBlocks (n+n) (localSourceResidual n w K selected q) :=
  supported_add hq (polySmul_supported (hybridSweep_supported n w K selected hs hq) (-1))

private theorem weighted_sub (blocks : Nat) (W p q r : RatPoly) :
    weightedPair blocks W (polyAdd p (polySmul (-1) q)) r ≈
      weightedPair blocks W p r-weightedPair blocks W q r :=
  Q'.eqv_trans _ _ _ (weighted_add_left blocks W p _ r)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (weighted_smul_left blocks W (-1) q r)
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))

private theorem vacuum (n i : Nat) (hi : i < n) (w : Q') (K : Nat)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (n+n) r)
    (hd : QuaternionBlockIndependent i r) :
    H (n+n) (polyMul (heatAt i (n+i) w K) r) ≈ H (n+n) r := by
  have he : (n+n-1)+1 = n+n := by omega
  have h := pair_vacuum (n+n-1) (by omega) ⟨i,by omega⟩ ⟨n+i,by omega⟩
    (by change i ≠ n+i; omega) w K r (by simpa only [he] using hr)
    (independent_has_degree_zero hd)
  simpa only [he] using h

private theorem retained_update (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (i : Nat) (hi : i ∈ ids) (p r R : RatPoly)
    (hp : SupportedQuaternionBlocks (n+n) p)
    (hr : SupportedQuaternionBlocks (n+n) r)
    (hR : SupportedQuaternionBlocks n R) (hir : QuaternionBlockIndependent i r) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R))
      (project i (polyMul (heatAt i (n+i) w K) p)) r ≈
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R)) p r := by
  let rest := eraseIndex i ids
  let ki := heatAt i (n+i) w K
  let Q := project i (polyMul ki p)
  let D := polyMul (productHeat n w K rest) (polyMul (liftBoundary n R) r)
  have hperm := select_perm i hi
  have hn := List.nodup_cons.mp (hperm.nodup_iff.mp hnd)
  have hii := hids i hi
  have hrest : ∀ j, j ∈ rest → j < n :=
    fun j hj => hids j (hperm.mem_iff.mpr (List.mem_cons_of_mem i hj))
  have hD : SupportedQuaternionBlocks (n+n) D :=
    supported_polyMul (productHeat_supported n w K rest hrest)
      (supported_polyMul (lift_supported hR n) hr)
  have hiD : QuaternionBlockIndependent i D :=
    quaternionBlockIndependent_polyMul
      (productHeat_independent_lower n w K rest hrest i hii hn.1)
      (quaternionBlockIndependent_polyMul (lift_lower_independent n R i hii) hir)
  have hQ : SupportedQuaternionBlocks (n+n) Q :=
    project_supported i (supported_polyMul
      (heat_supported (by omega) (by omega) w K) hp)
  have he (x : RatPoly) : weightedPair (n+n)
      (polyMul (productHeat n w K ids) (liftBoundary n R)) x r ≈
      H (n+n) (polyMul ki (polyMul x D)) := by
    have hc := (polynomialProduct_perm (fun j => heatAt j (n+j) w K) hperm).mul_right
      (liftBoundary n R)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (hc.mul_left (polyMul x r)))
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 3)) (.var 4)))
        (.mul (.var 2) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 1)))))
        (by decide) (fun
          | 0 => x
          | 1 => r
          | 2 => ki
          | 3 => productHeat n w K rest
          | _ => liftBoundary n R)))
  have hdrop := vacuum n i hii w K (polyMul Q D) (supported_polyMul hQ hD)
    (quaternionBlockIndependent_polyMul (project_independent i _) hiD)
  have hproj := project_selfAdjoint (n+n) i (by omega) (polyMul ki p) D
  have hfixed := project_fixed i D hiD
  have hrestore : H (n+n) (polyMul (polyMul ki p) D) ≈
      H (n+n) (polyMul ki (polyMul p D)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc ki p D)
  exact Q'.eqv_trans _ _ _ (he Q) (Q'.eqv_trans _ _ _ hdrop
    (Q'.eqv_trans _ _ _ hproj (Q'.eqv_trans _ _ _
      (haar_of_coeff (hfixed.mul_left (polyMul ki p)))
      (Q'.eqv_trans _ _ _ hrestore (Q'.eqv_symm (he p))))))

private theorem retained_sweep (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R) :
    ∀ (selected : List Nat), (∀ i, i ∈ selected → i ∈ ids) →
    ∀ (p r : RatPoly), SupportedQuaternionBlocks (n+n) p →
      SupportedQuaternionBlocks (n+n) r →
      (∀ i, i ∈ selected → QuaternionBlockIndependent i r) →
      weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R))
        (hybridSweep n w K selected p) r ≈
      weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R)) p r
  | [], _, _, _, _, _, _ => Q'.eqv_refl _
  | i::selected, hs, p, r, hp, hr, hir => by
      have ht : ∀ j, j ∈ selected → j ∈ ids :=
        fun j hj => hs j (List.mem_cons_of_mem i hj)
      have htail := retained_sweep n w K ids hnd hids R hR selected ht p r hp hr
        (fun j hj => hir j (List.mem_cons_of_mem i hj))
      exact Q'.eqv_trans _ _ _
        (retained_update n w K ids hnd hids i (hs i List.mem_cons_self)
          (hybridSweep n w K selected p) r R
          (hybridSweep_supported n w K selected (fun j hj => hids j (ht j hj)) hp)
          hr hR (hir i List.mem_cons_self)) htail

/-- Exact weighted orthogonality under the FULL original kinetic kernel.
The source is unrestricted except for support; only the test's selected
lower-slot independence is required. Upper action and all spectators stay. -/
theorem localSourceResidual_orthogonal (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (selected : List Nat) (hs : ∀ i, i ∈ selected → i ∈ ids)
    (q r R : RatPoly) (hq : SupportedQuaternionBlocks (n+n) q)
    (hr : SupportedQuaternionBlocks (n+n) r) (hR : SupportedQuaternionBlocks n R)
    (hir : ∀ i, i ∈ selected → QuaternionBlockIndependent i r) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R))
      (localSourceResidual n w K selected q) r ≈ 0 :=
  Q'.eqv_trans _ _ _ (weighted_sub (n+n) _ q _ r)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (retained_sweep n w K ids hnd hids R hR selected hs q r hq hr hir)))
      (Q'.add_neg_self_eqv _))

/-- Exact conditional Pythagoras. The discarded-looking term is a literal
nonnegative square under the SAME joint action, not an independence claim. -/
theorem localSourceLoss_pythagoras (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (selected : List Nat) (hs : ∀ i, i ∈ selected → i ∈ ids)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R) :
    H n (polyMul R (fullSourceLoss n w K ids q)) ≈
      localSourceLoss n w K ids selected q R +
        weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R))
          (polyAdd (hybridSweep n w K selected q)
            (polySmul (-1) (liftBoundary n (productMap n w K ids q))))
          (polyAdd (hybridSweep n w K selected q)
            (polySmul (-1) (liftBoundary n (productMap n w K ids q)))) := by
  let W := polyMul (productHeat n w K ids) (liftBoundary n R)
  let u := localSourceResidual n w K selected q
  let z := polyAdd (hybridSweep n w K selected q)
    (polySmul (-1) (liftBoundary n (productMap n w K ids q)))
  have hsel : ∀ i, i ∈ selected → i < n := fun i hi => hids i (hs i hi)
  have hz := supported_add (hybridSweep_supported n w K selected hsel (support_mono hq))
    (polySmul_supported (lift_supported (productMap_supported n w K ids hids hq) n) (-1))
  have hind : ∀ i, i ∈ selected → QuaternionBlockIndependent i z :=
    fun i hi => quaternionBlockIndependent_polyAdd
      (hybridSweep_lower_independent n w K selected hsel i hi q)
      (quaternionBlockIndependent_polySmul (-1) (lift_lower_independent n _ i (hsel i hi)))
  have ho := localSourceResidual_orthogonal n w K ids hnd hids selected hs q z R
    (support_mono hq) hz hR hind
  let Q := hybridSweep n w K selected q
  let F := liftBoundary n (productMap n w K ids q)
  have hcancel : RatPolyCoeffEqv (polyAdd (polySmul (-1) Q) Q) polyZero :=
    (RatPolyCoeffEqv.add_comm _ _).trans (RatPolyCoeffEqv.add_neg_smul Q)
  have hc : RatPolyCoeffEqv (polyAdd u z) (centered n w K ids q) :=
    (RatPolyCoeffEqv.add_assoc q (polySmul (-1) Q) (polyAdd Q (polySmul (-1) F))).trans
      ((RatPolyCoeffEqv.refl q).add
        ((RatPolyCoeffEqv.add_assoc (polySmul (-1) Q) Q (polySmul (-1) F)).symm.trans
          ((hcancel.add (RatPolyCoeffEqv.refl _)).trans
            (RatPolyCoeffEqv.zero_add (polySmul (-1) F)))))
  have hexpand : weightedPair (n+n) W (polyAdd u z) (polyAdd u z) ≈
      weightedPair (n+n) W u u + weightedPair (n+n) W z z := by
    have h := Q'.eqv_trans _ _ _ (weighted_add_left (n+n) W u z _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (weighted_symm (n+n) W u _)
          (weighted_add_left (n+n) W u z u))
        (Q'.eqv_trans _ _ _ (weighted_symm (n+n) W z _)
          (weighted_add_left (n+n) W u z z)))
    have ho' := Q'.eqv_trans _ _ _ (weighted_symm (n+n) W z u) ho
    exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr_left _ _ _ ho')
        (Q'.add_eqv_congr_right _ _ _ ho))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.const 0)) (.add (.const 0) (.var 1)))
        (.add (.var 0) (.var 1)) (by decide)
        (fun | 0 => weightedPair (n+n) W u u | _ => weightedPair (n+n) W z z)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (centered_pair n w K ids hnd hids R q q hR hq hq))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff ((hc.mul hc).mul_right W))) hexpand)

/-- Computed positivity of the localized loss under the original action. -/
theorem localSourceLoss_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hhead : headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (selected : List Nat) (hs : ∀ i, i ∈ selected → i ∈ ids)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (R : RatPoly) (PR : Certificate n R) :
    (0 : Q') ≤ localSourceLoss n w K ids selected q R :=
  ((productHeatCertificate n hw0 hw1 K hhead ids hids).mul (lift_certificate n PR)).square_insertion_nonnegative _ (local_supported n w K selected
      (fun i hi => hids i (hs i hi)) (support_mono hq))

/-- Localization cannot enlarge the original full conditional source loss.
The orthogonal remaining source square is retained in the preceding pin. -/
theorem localSourceLoss_le_fullSourceLoss (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hhead : headCutoff w ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (selected : List Nat) (_hselectedNodup : selected.Nodup)
    (hs : ∀ i, i ∈ selected → i ∈ ids)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R) (PR : Certificate n R) :
    localSourceLoss n w K ids selected q R ≤ H n (polyMul R (fullSourceLoss n w K ids q)) := by
  have hsel : ∀ i, i ∈ selected → i < n := fun i hi => hids i (hs i hi)
  have hz := supported_add (hybridSweep_supported n w K selected hsel (support_mono hq))
    (polySmul_supported (lift_supported (productMap_supported n w K ids hids hq) n) (-1))
  have hn := ((productHeatCertificate n hw0 hw1 K hhead ids hids).mul (lift_certificate n PR)).square_insertion_nonnegative _ hz
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn)
    (Q'.ge_of_eqv (localSourceLoss_pythagoras n w K ids hnd hids selected hs q hq R hR))

/-! The computed Green potential stays opaque throughout the zero-source
calculation. No harmonic expansion is normalized during carrier transport. -/
attribute [local irreducible] YMGap.Continuum.SU2QuaternionHeadCasimirInverse.potential

private theorem selected_gradient_zero (tail : Nat) (hb : 0 < tail)
    (a b : Fin (tail+1)) (hab : a.val ≠ b.val) (w : Q') (K : Nat)
    (component : Fin 4) (q r : RatPoly) (hq : HasQuaternionBlockDegree a.val 0 q) :
    selectedGradientPair tail hb a b w K component q r ≈ 0 := by
  let steps := pairSteps (by omega : 1 < tail+1) a b
  have hd : HasQuaternionBlockDegree 0 0 (applyQuaternionBlockSwapChain steps q) := by
    apply chain_degree steps (by omega)
    rw [pair_zero (by omega) a b hab]
    exact hq
  change sixValue (fun j k => H (tail+1)
    (polyMul (polyMul (angularDerivative j k (applyQuaternionBlockSwapChain steps q))
      (applyQuaternionBlockSwapChain steps r))
      (angularDerivative j k (YMGap.Continuum.SU2QuaternionHeadCasimirInverse.potential tail
        (YMGap.Continuum.SU2QuaternionRelativeHeatStein.coordinateDefect w K component))))) ≈ 0
  refine Q'.eqv_trans _ (sixValue (fun _ _ => 0)) _ ?_ (by decide)
  apply sixValue_congr
  intro j k hj hk
  exact haar_of_coeff (blocks := tail+1)
    (((((angularDerivative_independent_zero hj hk _ hd).mul_right _).trans
      (RatPolyCoeffEqv.mul_zero_left _)).mul_right _).trans
        (RatPolyCoeffEqv.mul_zero_left _))

private theorem link_gradient_zero (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (i : Fin n) (p s : PolyQuaternion) (reverse : Bool) (q r : RatPoly)
    (hq : HasQuaternionBlockDegree i.val 0 q) :
    linkGradientSum n w K ids i p s reverse q r ≈ 0 := by
  let tail := n+n-1
  have htail : 0 < tail := by have := i.isLt; omega
  let lower : Fin (tail+1) := ⟨i.val, by have := i.isLt; omega⟩
  let upper : Fin (tail+1) := ⟨n+i.val, by have := i.isLt; omega⟩
  let retain (j : Fin 4) := polyMul (polyMul (productHeat n w K (eraseIndex i.val ids))
    (sandwichCoefficient (liftQuaternion n p) s reverse j)) (liftBoundary n r)
  have h (j : Fin 4) : selectedGradientPair tail htail lower upper w K j q (retain j) ≈ 0 :=
    selected_gradient_zero tail htail lower upper
      (by change i.val ≠ n+i.val; have := i.isLt; omega) w K j q (retain j) hq
  change selectedGradientPair tail htail lower upper w K 0 q (retain 0) +
    (selectedGradientPair tail htail lower upper w K 1 q (retain 1) +
      (selectedGradientPair tail htail lower upper w K 2 q (retain 2) +
        selectedGradientPair tail htail lower upper w K 3 q (retain 3))) ≈ 0
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (h 0)
    (Q'.add_eqv_congr' (h 1) (Q'.add_eqv_congr' (h 2) (h 3)))) (by decide)

private theorem word_gradient_zero (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (block : OrientedBF4Link → Nat) :
    ∀ (es : List OrientedBF4Link) (hrange : ∀ e, e ∈ es → block e < n)
      (p : PolyQuaternion) (q r : RatPoly),
      (∀ e, e ∈ es → HasQuaternionBlockDegree (block e) 0 q) →
      wordGradientSum n w K ids block es hrange p q r ≈ 0
  | [], _, _, _, _, _ => Q'.eqv_refl _
  | e::es, hrange, p, q, r, hd => by
      have hhead := link_gradient_zero n w K ids
        ⟨block e,hrange e List.mem_cons_self⟩ p (wordAt block es) e.reverse q r
        (hd e List.mem_cons_self)
      have htail := word_gradient_zero n w K ids block es
        (fun f hf => hrange f (List.mem_cons_of_mem e hf))
        (p ⋄ orientedCoordinateQuaternion (block e) e.reverse) q r
        (fun f hf => hd f (List.mem_cons_of_mem e hf))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hhead
        (Q'.mul_eqv_congr_left _ _ _ htail))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) (by decide))

private theorem map_output_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (n+n) q) :
    SupportedQuaternionBlocks n (productMap n w K ids q) :=
  partialHaarHeads_supported n n _ (supported_polyMul (productHeat_supported n w K ids hids) hq)

private theorem centered_test_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (D q f : RatPoly) (a : Q')
    (hD : SupportedQuaternionBlocks n D) (hq : SupportedQuaternionBlocks (n+n) q)
    (hf : SupportedQuaternionBlocks n f)
    (himage : SupportedHaarEqv n (productMap n w K ids f) (polySmul a f)) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D))
      q (centered n w K ids f) ≈ H n (polyMul D (multiplicationDefect n w K ids q f a)) := by
  let F := productMap n w K ids f
  let Q := productMap n w K ids q
  have hQ := map_output_supported n w K ids hids hq
  have hF := productMap_supported n w K ids hids hf
  have hs := Q'.eqv_trans _ _ _ (weighted_symm (n+n) _ q _)
    (Q'.eqv_trans _ _ _ (weighted_sub (n+n) _ f (liftBoundary n F) q)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (weighted_symm (n+n) _ f q) (lower_pair n w K ids D q f))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (weighted_symm (n+n) _ _ q)
          (Q'.eqv_trans _ _ _ (mixed_pair n w K ids D q F)
            (haar_of_coeff ((RatPolyCoeffEqv.mul_comm F Q).mul_left D)))))))
  have hp := (SupportedHaarEqv.refl n Q).mul himage hF hQ
  have he : RatPolyCoeffEqv (polySmul (-1) (polyMul Q (polySmul a f)))
      (polySmul (-a) (polyMul Q f)) :=
    ((RatPolyCoeffEqv.polyMul_smul_right a Q f).smul (-1)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) a _).trans
        (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))) _))
  have hcov := (SupportedHaarEqv.refl n (productMap n w K ids (polyMul q f))).add
    ((hp.smul (-1)).trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier he)))
  have hr : RatPolyCoeffEqv
      (polyMul D (polyAdd (productMap n w K ids (polyMul q f)) (polySmul (-1) (polyMul Q F))))
      (polyAdd (polyMul D (productMap n w K ids (polyMul q f)))
        (polySmul (-1) (polyMul D (polyMul Q F)))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right (-1) D _))
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff hr) (haar_sub n _ _)))
      (hcov D hD))


private theorem defect_pair_kernel (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q f r : RatPoly) (a : Q') :
    H n (polyMul r (multiplicationDefect n w K ids q f a)) ≈
      H (n+n) (polyMul (polyMul (productHeat n w K ids) q)
        (polyMul (polyAdd f (polySmul (-a) (liftBoundary n f))) (liftBoundary n r))) := by
  let A := productHeat n w K ids
  have hfirst := productMap_pairing n w K ids (polyMul q f) r
  have hfirst' : RatPolyCoeffEqv (polyMul A (polyMul (polyMul q f) (liftBoundary n r)))
      (polyMul (polyMul A q) (polyMul f (liftBoundary n r))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (by decide)
      (fun | 0 => A | 1 => q | 2 => f | _ => liftBoundary n r)
  have hsecond' : RatPolyCoeffEqv (polyMul r (polyMul (productMap n w K ids q) f))
      (polyMul (polyMul r f) (productMap n w K ids q)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => r | 1 => productMap n w K ids q | _ => f)
  have hsecond := Q'.eqv_trans _ _ _ (haar_of_coeff hsecond')
    (productMap_pairing n w K ids q (polyMul r f))
  rw [lift_product] at hsecond
  have hsecond'' : RatPolyCoeffEqv
      (polyMul A (polyMul q (polyMul (liftBoundary n r) (liftBoundary n f))))
      (polyMul (polyMul A q) (polyMul (liftBoundary n f) (liftBoundary n r))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 2))) (by decide)
      (fun | 0 => A | 1 => q | 2 => liftBoundary n r | _ => liftBoundary n f)
  have hsplit : H (n+n) (polyMul (polyMul A q)
      (polyMul (polyAdd f (polySmul (-a) (liftBoundary n f))) (liftBoundary n r))) ≈
      H (n+n) (polyMul (polyMul A q) (polyMul f (liftBoundary n r)))+
        (-a)*H (n+n) (polyMul (polyMul A q)
          (polyMul (liftBoundary n f) (liftBoundary n r))) := by
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).mul_left _))
          (quaternionHaar_polyMul_smul_right _ _ _ _)))
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ hfirst (haar_of_coeff hfirst'))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ hsecond (haar_of_coeff hsecond'')))))
      (Q'.eqv_symm hsplit))
private theorem insert_test_square (n : Nat) (W R b y : RatPoly) :
    weightedPair (n+n) (polyMul W (liftBoundary n R))
      (polyMul (liftBoundary n b) y) (polyMul (liftBoundary n b) y) ≈
      weightedPair (n+n) (polyMul W (liftBoundary n (polyMul R (polyMul b b)))) y y := by
  unfold weightedPair
  rw [lift_product, lift_product]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.mul (.var 0) (.var 0)))))
    (by decide) (fun | 0 => liftBoundary n b | 1 => y | 2 => W | _ => liftBoundary n R))

private theorem neg_one_mul (a : Q') : (-1)*a ≈ -a :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))

private theorem covariance_variance_coeff (D f : RatPoly) (a d : Q') :
    RatPolyCoeffEqv
      (polyMul D (polyAdd
        (polyAdd polyOne (polySmul d (polyAdd (polyMul f f) (polySmul (-1) polyOne))))
        (polySmul (-1) (polyMul (polySmul a f) (polySmul a f)))))
      (polyAdd (polySmul (1-d) D) (polySmul (d-a*a) (polyMul D (polyMul f f)))) := by
  let ff := polyMul f f
  have hd : RatPolyCoeffEqv (polySmul d (polyAdd ff (polySmul (-1) polyOne)))
      (polyAdd (polySmul d ff) (polySmul (-d) polyOne)) :=
    (RatPolyCoeffEqv.smul_add d ff _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.smul_assoc d (-1) polyOne).trans
          (RatPolyCoeffEqv.smul_coefficient
            (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv d (-1)) (neg_one_mul d)) polyOne)))
  have ha : RatPolyCoeffEqv (polySmul (-1) (polyMul (polySmul a f) (polySmul a f)))
      (polySmul (-(a*a)) ff) :=
    ((((RatPolyCoeffEqv.polyMul_smul_left a f (polySmul a f)).trans
      ((RatPolyCoeffEqv.polyMul_smul_right a f f).smul a)).trans
      (RatPolyCoeffEqv.smul_assoc a a ff)).smul (-1)).trans
        ((RatPolyCoeffEqv.smul_assoc (-1) (a*a) ff).trans
          (RatPolyCoeffEqv.smul_coefficient (neg_one_mul (a*a)) ff))
  have hr : RatPolyCoeffEqv
      (polyAdd (polyAdd polyOne (polyAdd (polySmul d ff) (polySmul (-d) polyOne)))
        (polySmul (-(a*a)) ff))
      (polyAdd (polyAdd polyOne (polySmul (-d) polyOne))
        (polyAdd (polySmul d ff) (polySmul (-(a*a)) ff))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.add (.var 1) (.var 2))) (.var 3))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
      (fun
        | 0 => polyOne
        | 1 => polySmul d ff
        | 2 => polySmul (-d) polyOne
        | _ => polySmul (-(a*a)) ff)
  have hcollect : RatPolyCoeffEqv
      (polyAdd (polyAdd polyOne (polySmul (-d) polyOne))
        (polyAdd (polySmul d ff) (polySmul (-(a*a)) ff)))
      (polyAdd (polySmul (1-d) polyOne) (polySmul (d-a*a) ff)) :=
    (((RatPolyCoeffEqv.one_smul polyOne).symm.add (RatPolyCoeffEqv.refl _)).trans
      (RatPolyCoeffEqv.add_smul_same 1 (-d) polyOne)).add
        (RatPolyCoeffEqv.add_smul_same d (-(a*a)) ff)
  have hc := (((RatPolyCoeffEqv.refl polyOne).add hd).add ha).trans (hr.trans hcollect)
  exact (hc.mul_left D).trans
    ((RatPolyCoeffEqv.mul_add_right D _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right (1-d) D polyOne).trans
        ((RatPolyCoeffEqv.mul_one D).smul (1-d))).add
        (RatPolyCoeffEqv.polyMul_smul_right (d-a*a) D ff)))



private theorem shuffle (A q f r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul A q) (polyMul f r))
      (polyMul (polyMul (polyMul A q) r) f) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun | 0 => A | 1 => q | 2 => f | _ => r)

private theorem bare_word_defect_zero (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (q r : RatPoly) (hq : SupportedQuaternionBlocks (n+n) q)
    (hr : SupportedQuaternionBlocks n r)
    (hd : ∀ e, e ∈ es → HasQuaternionBlockDegree (block e) 0 q) :
    H n (polyMul r (multiplicationDefect n w K ids q (wordAt block es).scalar
      (qpow w (3*es.length)))) ≈ 0 := by
  have hrange : ∀ e, e ∈ es → block e < n := fun e he => hids _ (hselected e he)
  have hw := word_supported n block es hrange
  have hw2 := word_supported (n+n) block es (fun e he => by have := hrange e he; omega)
  have hp : QuaternionSupported n PolyQuaternion.one :=
    word_supported n block [] (fun _ h => False.elim (List.not_mem_nil h))
  have hliftp : QuaternionSupported (n+n) (liftQuaternion n PolyQuaternion.one) :=
    ⟨lift_supported hp.scalar n, lift_supported hp.iPart n,
      lift_supported hp.jPart n, lift_supported hp.kPart n⟩
  let a := qpow w (3*es.length)
  let delta := polyAdd (liftQuaternion n PolyQuaternion.one ⋄ wordAt block es).scalar
    (polySmul (-a) (liftQuaternion n (PolyQuaternion.one ⋄ wordAt block es)).scalar)
  let W := polyMul (polyMul (productHeat n w K ids) q) (liftBoundary n r)
  have hW := supported_polyMul
    (supported_polyMul (productHeat_supported n w K ids hids) hq) (lift_supported hr n)
  have hl := ((liftQuaternion_one (n+n) n).mul
    (PaddedQuaternionCoeffEqv.refl (n+n) (wordAt block es))).trans
      (PaddedQuaternionCoeffEqv.of_coeff (PolyQuaternionCoeffEqv.one_mul _))
  have hu := lift_coeff n (PolyQuaternionCoeffEqv.one_mul (wordAt block es)).scalar
  have hdiff : PaddedPolynomialCoeffEqv (n+n) delta
      (polyAdd (wordAt block es).scalar
        (polySmul (-a) (liftBoundary n (wordAt block es).scalar))) :=
    PaddedPolynomialCoeffEqv.add hl.scalar
      ((PaddedPolynomialCoeffEqv.of_coeff (blocks := n+n) hu).smul (-a))
  have hleft : SupportedQuaternionBlocks (n+n) delta :=
    supported_add ((hliftp.mul hw2).scalar)
      (polySmul_supported (lift_supported ((hp.mul hw).scalar) n) _)
  have hright := supported_add hw2.scalar (polySmul_supported (lift_supported hw.scalar n) (-a))
  have hpin := PaddedPolynomialCoeffEqv.haar_insert hdiff hleft hright W hW
  have ht := word_retained_source_gradient n w K hK ids hnd hids block es hword hselected
    PolyQuaternion.one hp q r hq hr
  change H (n+n) (polyMul (polyMul (productHeat n w K ids) q)
    (polyMul delta (liftBoundary n r))) ≈ _ at ht
  have hz := word_gradient_zero n w K ids block es hrange PolyQuaternion.one q r hd
  exact Q'.eqv_trans _ _ _ (defect_pair_kernel n w K ids q _ r a)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (shuffle _ _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpin)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (shuffle _ _ _ _).symm)
          (Q'.eqv_trans _ _ _ ht hz))))

private theorem fundamental_word_defect_zero (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (q r : RatPoly) (hq : SupportedQuaternionBlocks (n+n) q)
    (hr : SupportedQuaternionBlocks n r)
    (hd : ∀ e, e ∈ es → HasQuaternionBlockDegree (block e) 0 q) :
    H n (polyMul r (multiplicationDefect n w K ids q
      (characterPolynomial (wordAt block es).scalar 1) (qpow w (3*es.length)))) ≈ 0 := by
  let f := (wordAt block es).scalar
  let a := qpow w (3*es.length)
  have hfirst := productMap_congr n w K ids
    ((RatPolyCoeffEqv.polyMul_smul_left 2 q f).trans
      (RatPolyCoeffEqv.polyMul_smul_right 2 q f).symm)
  have hsecond := ((productMap_smul n w K ids 2 q).mul_right f).trans
    ((RatPolyCoeffEqv.polyMul_smul_left 2 (productMap n w K ids q) f).trans
      (RatPolyCoeffEqv.polyMul_smul_right 2 (productMap n w K ids q) f).symm)
  have hc : RatPolyCoeffEqv
      (multiplicationDefect n w K ids (polySmul 2 q) f a)
      (multiplicationDefect n w K ids q (polySmul 2 f) a) :=
    hfirst.add (hsecond.smul (-a))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hc.symm.mul_left r))
    (bare_word_defect_zero n w K hK ids hnd hids block es hword hselected
      (polySmul 2 q) r (polySmul_supported hq 2) hr (fun e he => (hd e he).smul 2))

private theorem fundamental_centered_test_norm (n : Nat) (w : Q') (K : Nat)
    (htwo : 2 ≤ K) (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (R b : RatPoly) (hR : SupportedQuaternionBlocks n R)
    (hb : SupportedQuaternionBlocks n b) :
    let f := characterPolynomial (wordAt block es).scalar 1
    let a := qpow w (3*es.length)
    let d := qpow w (8*es.length)
    let v := polyMul (liftBoundary n b) (centered n w K ids f)
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n R)) v v ≈
      wordCovarianceRate w es.length * H n (polyMul R (polyMul b b)) -
        (a*a-d)*H n (polyMul R (polyMul (polyMul b b) (polyMul f f))) := by
  dsimp only
  let f := characterPolynomial (wordAt block es).scalar 1
  let a := qpow w (3*es.length)
  let d := qpow w (8*es.length)
  let D := polyMul R (polyMul b b)
  have hf : SupportedQuaternionBlocks n f :=
    character_supported (word_supported n block es (fun e he => hids _ (hselected e he))).scalar 1
  have hF := productMap_supported n w K ids hids hf
  have hD := supported_polyMul hR (supported_polyMul hb hb)
  have himage := productMap_fundamental_word n w K (by omega : 1 ≤ K) block es
    ids hnd hids hword hselected
  have hvv0 := Q'.eqv_trans _ _ _ (insert_test_square n (productHeat n w K ids) R b _)
    (centered_pair n w K ids hnd hids D f f hD hf hf)
  have hF2 := himage.mul himage hF (polySmul_supported hf a)
  have hsquare := productMap_fundamental_square n w K htwo block es ids hnd hids hword hselected
  have hquad := (hsquare.add (hF2.smul (-1))) D hD
  have heq : RatPolyCoeffEqv
      (polyMul D (polyAdd (polyAdd polyOne (polySmul d (characterPolynomial (wordAt block es).scalar 2)))
        (polySmul (-1) (polyMul (polySmul a f) (polySmul a f)))))
      (polyAdd (polySmul (1-d) D) (polySmul (d-a*a) (polyMul D (polyMul f f)))) := by
    have hchar : RatPolyCoeffEqv (characterPolynomial (wordAt block es).scalar 2)
        (polyAdd (polyMul f f) (polySmul (-1) polyOne)) := RatPolyCoeffEqv.refl _
    refine ((RatPolyCoeffEqv.refl D).mul
      ((((RatPolyCoeffEqv.refl polyOne).add (hchar.smul d)).add (RatPolyCoeffEqv.refl _)))).trans ?_
    exact covariance_variance_coeff D f a d
  have hnorm := Q'.eqv_trans _ _ _ hvv0
    (Q'.eqv_trans _ _ _ hquad
      (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := n) heq)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
          (Q'.add_eqv_congr' (quaternionHaar_polySmul n (1-d) D)
            (quaternionHaar_polySmul n (d-a*a) _)))))
  have hmoment : H n (polyMul D (polyMul f f)) ≈
      H n (polyMul R (polyMul (polyMul b b) (polyMul f f))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc R (polyMul b b) (polyMul f f))
  exact Q'.eqv_trans _ _ _ hnorm
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left _ _ _ hmoment))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1))
          (.mul (.add (.var 3) (.neg (.mul (.var 2) (.var 2)))) (.var 4)))
        (.add (.mul (.var 0) (.var 1))
          (.neg (.mul (.add (.mul (.var 2) (.var 2)) (.neg (.var 3))) (.var 4))))
        (by decide) (fun
          | 0 => wordCovarianceRate w es.length
          | 1 => H n D
          | 2 => a
          | 3 => d
          | _ => H n (polyMul R (polyMul (polyMul b b) (polyMul f f))))))

/-- Sharp retained word-local cost for the ORIGINAL signed multiplication
defect. Only its selected lower source variation is paid. The complete
kinetic set, certified output action, outside lower variables and exact
negative spin-two moment are retained. No relative reserve is assumed. -/
theorem fundamental_word_local_covariance_pair_retained_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R) (PR : Certificate n R)
    (b : RatPoly) (hb : SupportedQuaternionBlocks n b) :
    let f := characterPolynomial (wordAt block es).scalar 1
    let C := multiplicationDefect n w K ids q f (qpow w (3*es.length))
    H n (polyMul R (polyMul b C))*H n (polyMul R (polyMul b C)) ≤
      localSourceLoss n w K ids (es.map block) q R *
        (wordCovarianceRate w es.length * H n (polyMul R (polyMul b b)) -
          (qpow w (3*es.length)*qpow w (3*es.length)-qpow w (8*es.length)) *
            H n (polyMul R (polyMul (polyMul b b) (polyMul f f)))) := by
  dsimp only
  let f := characterPolynomial (wordAt block es).scalar 1
  let a := qpow w (3*es.length)
  let S := es.map block
  let QS := hybridSweep n w K S q
  let W := polyMul (productHeat n w K ids) (liftBoundary n R)
  let u := localSourceResidual n w K S q
  let v := polyMul (liftBoundary n b) (centered n w K ids f)
  let D := polyMul R b
  have hS : ∀ i, i ∈ S → i ∈ ids := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hi
    exact hselected e he
  have hSlt : ∀ i, i ∈ S → i < n := fun i hi => hids i (hS i hi)
  have hf : SupportedQuaternionBlocks n f :=
    character_supported (word_supported n block es (fun e he => hids _ (hselected e he))).scalar 1
  have hQS := hybridSweep_supported n w K S hSlt (support_mono hq)
  have hu := local_supported n w K S hSlt (support_mono hq)
  have hv := supported_polyMul (lift_supported hb n) (centered_supported n w K ids hids hf)
  have hD := supported_polyMul hR hb
  have himage := productMap_fundamental_word n w K (by omega : 1 ≤ K) block es
    ids hnd hids hword hselected
  have hpair (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p) :
      weightedPair (n+n) W p v ≈ H n (polyMul D (multiplicationDefect n w K ids p f a)) := by
    have hins : weightedPair (n+n) W p v ≈ weightedPair (n+n)
        (polyMul (productHeat n w K ids) (liftBoundary n D)) p (centered n w K ids f) := by
      unfold weightedPair
      rw [lift_product]
      exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.mul (.var 4) (.var 1))))
        (by decide) (fun
          | 0 => p
          | 1 => liftBoundary n b
          | 2 => centered n w K ids f
          | 3 => productHeat n w K ids
          | _ => liftBoundary n R))
    exact Q'.eqv_trans _ _ _ hins
      (centered_test_pair n w K ids hids D p f a hD hp hf himage)
  have hzero : weightedPair (n+n) W QS v ≈ 0 :=
    Q'.eqv_trans _ _ _ (hpair QS hQS)
      (fundamental_word_defect_zero n w K (by omega : 1 ≤ K) ids hnd hids
        block es hword hselected QS D hQS hD (fun e he =>
          independent_has_degree_zero (hybridSweep_lower_independent n w K S hSlt
            (block e) (List.mem_map.mpr ⟨e,he,rfl⟩) q)))
  have huv : weightedPair (n+n) W u v ≈
      H n (polyMul R (polyMul b (multiplicationDefect n w K ids q f a))) :=
    Q'.eqv_trans _ _ _ (weighted_sub (n+n) W q QS v)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hpair q (support_mono hq))
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hzero) (by decide : -(0 : Q') ≈ 0)))
        (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))
          (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R b _))))
  have PW : Certificate (n+n) W :=
    (productHeatCertificate n hw0 hw1 K hhead ids hids).mul (lift_certificate n PR)
  have hcs := weighted_cauchySchwarz (n+n) W u v PW hu hv
  have hnorm := fundamental_centered_test_norm n w K htwo ids hnd hids
    block es hword hselected R b hR hb
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ huv)
      (Q'.mul_eqv_congr_left _ _ _ huv)))
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hnorm)))


end YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance

#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance.localSourceResidual
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance.localSourceLoss
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance.localSourceResidual_orthogonal
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance.localSourceLoss_pythagoras
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance.localSourceLoss_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance.localSourceLoss_le_fullSourceLoss
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonLocalCovariance.fundamental_word_local_covariance_pair_retained_bound
