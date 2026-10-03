/-
# Width-free Efron--Stein in the ORIGINAL joint product heat law

Every selected update is the literal in-place integration against its own
original lower/upper heat pair. The SAME certified surviving weight and all
heat factors remain in every norm. Exact local Pythagoras, contraction and
fixed-source residual commutation give a finite sweep loss bounded by the
sum of ORIGINAL input residual squares, with coefficient ONE. No source
independence from the existing outputs, headMap identification, variance
inverse or analytic gap estimate is assumed.

Unselected lower coordinates remain spectators of the sweep. A subsequent
Haar integration of those coordinates still needs its own variance payment
or an actual independence pin. This is finite conditional reference heat,
not the interacting relative signed-cost or changing-family conclusion.
-/

import YMGap.Continuum.SU2QuaternionWeightedHeatProjection
import YMGap.Continuum.SU2QuaternionProductHeatSweepResidual
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare

namespace YMGap.Continuum.SU2QuaternionProductHeatEfronStein

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
open YMGap.Continuum.SU2QuaternionProductHeatSweepResidual
open YMGap.Continuum.SU2QuaternionWeightedHeatProjection
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm mem_of_mem_erase not_mem_erase)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionAngularReindex

local infix:50 " ≈ " => Q'.eqv

/-- Every input heat factor and the original surviving output weight. -/
def jointWeight (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (W : RatPoly) : RatPoly :=
  polyMul (liftBoundary n W) (productHeat n w K ids)

/-- Squared norm in the SAME joint product law. -/
def jointSquare (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (W p : RatPoly) : Q' :=
  quaternionHaar (n+n) (polyMul (jointWeight n w K ids W) (polyMul p p))

/-- Sum of selected residual norms evaluated on the ORIGINAL input p. -/
def residualEnergy (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (W : RatPoly)
    (p : RatPoly) : List Nat → Q'
  | [] => 0
  | i::xs => jointSquare n w K ids W (residual n w K i p) + residualEnergy n w K ids W p xs

private def restWeight (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (W : RatPoly) (i : Nat) : RatPoly :=
  polyMul (liftBoundary n W) (productHeat n w K (eraseIndex i ids))

private theorem rest_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n) (W : RatPoly) (hW : SupportedQuaternionBlocks n W)
    (i : Nat) : SupportedQuaternionBlocks (n+n) (restWeight n w K ids W i) :=
  supported_polyMul (lift_supported hW n)
    (productHeat_supported n w K _ (fun j hj => hids j (mem_of_mem_erase i hj)))

private theorem rest_independent (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n) (W : RatPoly)
    (i : Nat) (hi : i ∈ ids) : QuaternionBlockIndependent i (restWeight n w K ids W i) :=
  quaternionBlockIndependent_polyMul (lift_lower_independent n W i (hids i hi))
    (productHeat_independent_lower n w K _
      (fun j hj => hids j (mem_of_mem_erase i hj)) i (hids i hi) (not_mem_erase i hn))

private def restCertificate (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n) {W : RatPoly} (P : Certificate n W) (i : Nat) :
    Certificate (n+n) (restWeight n w K ids W i) :=
  (lift_certificate n P).mul
    (productHeatCertificate n hw0 hw1 K hK _ (fun j hj => hids j (mem_of_mem_erase i hj)))

private theorem selected_weight_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (W : RatPoly) (i : Nat) (hi : i ∈ ids) :
    RatPolyCoeffEqv (jointWeight n w K ids W)
      (heatJointWeight i (n+i) w K (restWeight n w K ids W i)) :=
  ((polynomialProduct_perm (fun j => heatAt j (n+j) w K) (select_perm i hi)).mul_left
    (liftBoundary n W)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun
        | 0 => liftBoundary n W
        | 1 => heatAt i (n+i) w K
        | _ => productHeat n w K (eraseIndex i ids)))

private theorem jointSquare_coeff (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (W : RatPoly) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    jointSquare n w K ids W p ≈ jointSquare n w K ids W q :=
  haar_of_coeff ((h.mul h).mul_left (jointWeight n w K ids W))

/-- Exact local split with every remaining heat factor retained. No positivity
or cutoff guard is required for this normalized finite identity. -/
theorem joint_update_square_decomposition (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (W : RatPoly) (hW : SupportedQuaternionBlocks n W) (i : Nat) (hi : i ∈ ids)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p) :
    jointSquare n w K ids W p ≈ jointSquare n w K ids W (update n w K i p) +
      jointSquare n w K ids W (residual n w K i p) := by
  have hin := hids i hi
  have he : (n+n-1)+1 = n+n := by omega
  let R := restWeight n w K ids W i
  have hR := rest_supported n w K ids hids W hW i
  have hRi := rest_independent n w K ids hn hids W i hi
  have hlocal := heatUpdate_weighted_square_decomposition (n+n-1) (by omega)
    ⟨i,by omega⟩ ⟨n+i,by omega⟩ (by change i ≠ n+i; omega) w K R p
    (by simpa only [he] using hR) (by simpa only [he] using hp) hRi
  have hlocal' : quaternionHaar (n+n)
      (polyMul (heatJointWeight i (n+i) w K R) (polyMul p p)) ≈
      quaternionHaar (n+n) (polyMul (heatJointWeight i (n+i) w K R)
        (polyMul (update n w K i p) (update n w K i p))) +
      quaternionHaar (n+n) (polyMul (heatJointWeight i (n+i) w K R)
        (polyMul (residual n w K i p) (residual n w K i p))) := by
    simpa only [he] using hlocal
  have hpin := selected_weight_pin n w K ids W i hi
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hpin.mul_right (polyMul p p)))
    (Q'.eqv_trans _ _ _ hlocal' (Q'.eqv_symm (Q'.add_eqv_congr'
      (haar_of_coeff (hpin.mul_right (polyMul (update n w K i p) (update n w K i p))))
      (haar_of_coeff (hpin.mul_right (polyMul (residual n w K i p) (residual n w K i p)))))))

/-- A genuine joint-law update contracts with coefficient ONE, rather than
discarding the interacting/surviving weight or multiplying by a volume cap. -/
theorem joint_update_square_le (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ j, j ∈ ids → j < n) (W : RatPoly) (hW : SupportedQuaternionBlocks n W)
    (P : Certificate n W) (i : Nat) (hi : i ∈ ids)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p) :
    jointSquare n w K ids W (update n w K i p) ≤ jointSquare n w K ids W p := by
  have hin := hids i hi
  have he : (n+n-1)+1 = n+n := by omega
  let R := restWeight n w K ids W i
  have hR := rest_supported n w K ids hids W hW i
  have hRi := rest_independent n w K ids hn hids W i hi
  have hlocal := heatUpdate_weighted_square_le (n+n-1) (by omega)
    ⟨i,by omega⟩ ⟨n+i,by omega⟩ (by change i ≠ n+i; omega) hw0 hw1 K hK R p
    (by simpa only [he] using hR) (by simpa only [he] using hp) hRi
    (by simpa only [he] using (restCertificate n hw0 hw1 K hK ids hids P i))
  have hlocal' : quaternionHaar (n+n) (polyMul (heatJointWeight i (n+i) w K R)
      (polyMul (update n w K i p) (update n w K i p))) ≤
      quaternionHaar (n+n) (polyMul (heatJointWeight i (n+i) w K R) (polyMul p p)) := by
    simpa only [he] using hlocal
  have hpin := selected_weight_pin n w K ids W i hi
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff (hpin.mul_right (polyMul (update n w K i p) (update n w K i p)))))
    (Q'.le_trans' _ _ _ hlocal' (Q'.ge_of_eqv (haar_of_coeff (hpin.mul_right (polyMul p p)))))

/-- Every finite contained schedule contracts the SAME joint law. Repeated
schedule slots are allowed; distinctness belongs to its fixed kernel ids. -/
theorem joint_sweep_square_le (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ j, j ∈ ids → j < n) (W : RatPoly) (hW : SupportedQuaternionBlocks n W)
    (P : Certificate n W) :
    ∀ (xs : List Nat), (∀ i, i ∈ xs → i ∈ ids) → ∀ (p : RatPoly),
      SupportedQuaternionBlocks (n+n) p →
      jointSquare n w K ids W (hybridSweep n w K xs p) ≤ jointSquare n w K ids W p
  | [], _, p, _ => Q'.le_refl' _
  | i::xs, hs, p, hp => by
      have hsub : ∀ j, j ∈ xs → j ∈ ids := fun j hj => hs j (List.mem_cons_of_mem i hj)
      have hxs : ∀ j, j ∈ xs → j < n := fun j hj => hids j (hsub j hj)
      exact Q'.le_trans' _ _ _
        (joint_update_square_le n hw0 hw1 K hK ids hn hids W hW P i (hs i List.mem_cons_self)
          (hybridSweep n w K xs p) (hybridSweep_supported n w K xs hxs hp))
        (joint_sweep_square_le n hw0 hw1 K hK ids hn hids W hW P xs hsub p hp)

/-- Width-free finite Efron--Stein for an actual contained heat schedule.
Every right-hand residual is evaluated on p, not on a changing sweep source. -/
theorem joint_sweep_loss_le_residualEnergy (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (W : RatPoly) (hW : SupportedQuaternionBlocks n W) (P : Certificate n W) :
    ∀ (xs : List Nat), (∀ i, i ∈ xs → i ∈ ids) → ∀ (p : RatPoly),
      SupportedQuaternionBlocks (n+n) p →
      jointSquare n w K ids W p + -jointSquare n w K ids W (hybridSweep n w K xs p) ≤
        residualEnergy n w K ids W p xs
  | [], _, p, _ =>
      Q'.le_of_eqv (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
        (by decide) (fun _ => jointSquare n w K ids W p))
  | i::xs, hs, p, hp => by
      have hi : i ∈ ids := hs i List.mem_cons_self
      have hin := hids i hi
      have hsub : ∀ j, j ∈ xs → j ∈ ids := fun j hj => hs j (List.mem_cons_of_mem i hj)
      have hxs : ∀ j, j ∈ xs → j < n := fun j hj => hids j (hsub j hj)
      let S := hybridSweep n w K xs p
      have hS := hybridSweep_supported n w K xs hxs hp
      have htail := joint_sweep_loss_le_residualEnergy n hw0 hw1 K hK ids hn hids W hW P xs hsub p hp
      have hsplit := joint_update_square_decomposition n w K ids hn hids W hW i hi S hS
      have hcomm := jointSquare_coeff n w K ids W (residual_sweep_comm n w K i hin xs hxs p)
      have hres : jointSquare n w K ids W (residual n w K i S) ≤
          jointSquare n w K ids W (residual n w K i p) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm)
          (joint_sweep_square_le n hw0 hw1 K hK ids hn hids W hW P xs hsub
            (residual n w K i p) (heatResidual_supported (by omega) (by omega) w K hp))
      have hloss : jointSquare n w K ids W p + -jointSquare n w K ids W (update n w K i S) ≈
          (jointSquare n w K ids W p + -jointSquare n w K ids W S) +
            jointSquare n w K ids W (residual n w K i S) :=
        Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hsplit)) (Q'.eqv_refl _))
          (poly_identity_of_normal_eq
            (.add (.add (.var 0) (.neg (.add (.var 1) (.var 2)))) (.var 2))
            (.add (.var 0) (.neg (.var 1))) (by decide)
            (fun
              | 0 => jointSquare n w K ids W p
              | 1 => jointSquare n w K ids W (update n w K i S)
              | _ => jointSquare n w K ids W (residual n w K i S))))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hloss)
        (Q'.le_trans' _ _ _ (Q'.add_le_add htail hres)
          (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- The literal full selected sweep, with coefficient ONE and no factor
depending on the number of input links. Empty/zero carriers and W=0 remain. -/
theorem joint_sweep_efron_stein (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ j, j ∈ ids → j < n) (W : RatPoly) (hW : SupportedQuaternionBlocks n W)
    (P : Certificate n W) (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p) :
    jointSquare n w K ids W p + -jointSquare n w K ids W (hybridSweep n w K ids p) ≤
      residualEnergy n w K ids W p ids :=
  joint_sweep_loss_le_residualEnergy n hw0 hw1 K hK ids hn hids W hW P ids (fun _ h => h) p hp

/-! ## Angular payment at the ORIGINAL selected inputs -/

/-- Actual pair-chart onset, including a harmless empty-carrier branch.
Every applicable source is p itself, not an intermediate sweep source. -/
def selectedLinkCutoff (n i : Nat) (p : RatPoly) : Nat :=
  if h : i < n then
    selectedPairCutoff (n+n-1) (by omega)
      ⟨i, by omega⟩ ⟨n+i, by omega⟩ p
  else 0

/-- A single computable onset for this fixed original source and schedule. -/
def jointPoincareCutoff (n : Nat) (w : Q') (ids : List Nat) (p : RatPoly) : Nat :=
  max (headCutoff w) (ids.foldr (fun i c => max (selectedLinkCutoff n i p) c) 0)

private theorem selected_cutoff_le_fold (n : Nat) (p : RatPoly) (i : Nat) :
    ∀ ids : List Nat, i ∈ ids →
      selectedLinkCutoff n i p ≤ ids.foldr (fun j c => max (selectedLinkCutoff n j p) c) 0
  | [], hi => False.elim (List.not_mem_nil hi)
  | j::ids, hi => by
      rcases List.mem_cons.mp hi with hij | hit
      · subst j
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (selected_cutoff_le_fold n p i ids hit) (Nat.le_max_right _ _)

/-- Original angular energies in exactly the SAME joint weight. -/
def jointAngularEnergy (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (W p : RatPoly) : List Nat → Q'
  | [] => 0
  | i::xs => quaternionHaar (n+n)
      (polyMul (jointWeight n w K ids W) (blockAngularSquare i p)) +
        jointAngularEnergy n w K ids W p xs

private theorem haar_neg_angular (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -quaternionHaar blocks p
  | [] => by change (0 : Q') ≈ -0; decide
  | t::ps =>
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg_angular blocks ps)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_neg_angular (blocks : Nat) (R p : RatPoly) :
    quaternionHaar blocks (polyMul R (polyNeg p)) ≈
      -quaternionHaar blocks (polyMul R p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
    (by decide) (fun | 0 => R | _ => p))) (haar_neg_angular blocks _)

/-- The original residual norm is exactly the selected conditional variance
integrated against all OTHER heat factors and the unchanged output weight. -/
theorem joint_residual_variance_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (W : RatPoly) (hW : SupportedQuaternionBlocks n W) (i : Nat) (hi : i ∈ ids)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p) :
    jointSquare n w K ids W (residual n w K i p) ≈
      quaternionHaar (n+n) (polyMul
        (polyMul (liftBoundary n W) (productHeat n w K (eraseIndex i ids)))
        (selectedPairVariance i (n+i) w K p)) := by
  have hin := hids i hi
  have he : (n+n-1)+1 = n+n := by omega
  let R := restWeight n w K ids W i
  let U := heatAt i (n+i) w K
  let E := update n w K i p
  have hRi := rest_independent n w K ids hn hids W i hi
  have hR := rest_supported n w K ids hids W hW i
  have hE := heatUpdate_supported (blocks := n+n) (i := i) (j := n+i)
    (by omega) (by omega) w K hp
  have hEi := heatUpdate_independent i (n+i) w K p
  have hpin := selected_weight_pin n w K ids W i hi
  have hmean : quaternionHaar (n+n)
      (polyMul R (selectedPairMean i (n+i) w K (polyMul p p))) ≈
      jointSquare n w K ids W p :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm R _))
      (Q'.eqv_trans _ _ _ (project_selfAdjoint (n+n) i (by omega) _ R)
        (haar_of_coeff (((project_fixed i R hRi).mul_left (polyMul U (polyMul p p))).trans
          ((coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 2)) (.var 1))
            (.mul (.mul (.var 0) (.var 1)) (.var 2)) (by decide)
            (fun | 0 => U | 1 => R | _ => polyMul p p)).trans
              (hpin.symm.mul_right (polyMul p p))))))
  have hvac := pair_vacuum (n+n-1) (by omega)
    ⟨i, by omega⟩ ⟨n+i, by omega⟩ (by change i ≠ n+i; omega) w K
    (polyMul R (polyMul E E))
    (by simpa only [he] using (supported_polyMul hR (supported_polyMul hE hE)))
    (independent_has_degree_zero
      (quaternionBlockIndependent_polyMul hRi (quaternionBlockIndependent_polyMul hEi hEi)))
  have hvac' : quaternionHaar (n+n) (polyMul U (polyMul R (polyMul E E))) ≈
      quaternionHaar (n+n) (polyMul R (polyMul E E)) := by
    simpa only [he] using hvac
  have hremove : jointSquare n w K ids W E ≈
      quaternionHaar (n+n) (polyMul R (polyMul E E)) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((hpin.mul_right (polyMul E E)).trans
        (RatPolyCoeffEqv.mul_assoc U R (polyMul E E)))) hvac'
  have hvar : quaternionHaar (n+n)
      (polyMul R (selectedPairVariance i (n+i) w K p)) ≈
      jointSquare n w K ids W p + -jointSquare n w K ids W E :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (n+n) R _ _)
      (Q'.add_eqv_congr' hmean (Q'.eqv_trans _ _ _
        (weighted_neg_angular (n+n) R (polyMul E E))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hremove))))
  have hsplit := joint_update_square_decomposition n w K ids hn hids W hW i hi p hp
  have hdiff : jointSquare n w K ids W p + -jointSquare n w K ids W E ≈
      jointSquare n w K ids W (residual n w K i p) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hsplit)
      (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
        (.var 1) (by decide) (fun
          | 0 => jointSquare n w K ids W E
          | _ => jointSquare n w K ids W (residual n w K i p)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiff) (Q'.eqv_symm hvar)

/-- Genuine selected angular payment at the charted ORIGINAL source onset. -/
theorem joint_residual_angular_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (W : RatPoly) (hW : SupportedQuaternionBlocks n W) (P : Certificate n W)
    (i : Nat) (hi : i ∈ ids) (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p)
    (hcut : selectedLinkCutoff n i p ≤ K) :
    jointSquare n w K ids W (residual n w K i p) ≤
      (1-w*w)*quaternionHaar (n+n)
        (polyMul (jointWeight n w K ids W) (blockAngularSquare i p)) := by
  have hin := hids i hi
  have he : (n+n-1)+1 = n+n := by omega
  let R := restWeight n w K ids W i
  have hR := rest_supported n w K ids hids W hW i
  have hRi := rest_independent n w K ids hn hids W i hi
  have hc : selectedPairCutoff (n+n-1) (by omega)
      ⟨i, by omega⟩ ⟨n+i, by omega⟩ p ≤ K := by
    simpa only [selectedLinkCutoff, dif_pos hin] using hcut
  have hlocal := selectedPair_weighted_angular_variance (n+n-1) (by omega)
    ⟨i, by omega⟩ ⟨n+i, by omega⟩ (by change i ≠ n+i; omega) w hw0 hw1 K p R
    (by simpa only [he] using hp) (by simpa only [he] using hR)
    (by simpa only [he] using (restCertificate n hw0 hw1 K hK ids hids P i)) hRi hc
  have hlocal' : quaternionHaar (n+n) (polyMul R (selectedPairVariance i (n+i) w K p)) ≤
      (1-w*w)*quaternionHaar (n+n) (polyMul R
        (polyMul (heatAt i (n+i) w K) (blockAngularSquare i p))) := by
    simpa only [he] using hlocal
  have halg : RatPolyCoeffEqv (polyMul R (polyMul (heatAt i (n+i) w K) (blockAngularSquare i p)))
      (polyMul (jointWeight n w K ids W) (blockAngularSquare i p)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => R | 1 => heatAt i (n+i) w K | _ => blockAngularSquare i p)).trans
      ((selected_weight_pin n w K ids W i hi).symm.mul_right (blockAngularSquare i p))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (joint_residual_variance_pin n w K ids hn hids W hW i hi p hp))
    (Q'.le_trans' _ _ _ hlocal' (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (1-w*w) _ _ (haar_of_coeff halg))))

private theorem residualEnergy_angular_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (W : RatPoly) (hW : SupportedQuaternionBlocks n W) (P : Certificate n W)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p) :
    ∀ xs : List Nat, (∀ i, i ∈ xs → i ∈ ids) →
      (∀ i, i ∈ xs → selectedLinkCutoff n i p ≤ K) →
      residualEnergy n w K ids W p xs ≤ (1-w*w)*jointAngularEnergy n w K ids W p xs
  | [], _, _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | i::xs, hs, hc =>
      Q'.le_trans' _ _ _
        (Q'.add_le_add
          (joint_residual_angular_le n hw0 hw1 K hK ids hn hids W hW P i
            (hs i List.mem_cons_self) p hp (hc i List.mem_cons_self))
          (residualEnergy_angular_le n hw0 hw1 K hK ids hn hids W hW P p hp xs
            (fun j hj => hs j (List.mem_cons_of_mem i hj))
            (fun j hj => hc j (List.mem_cons_of_mem i hj))))
        (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))

/-- Product conditional angular Poincare with coefficient ONE, the actual
joint weight, and per-link computed onsets of the SAME original source.
Inactive lower slots are still spectators, not silently integrated away. -/
theorem joint_sweep_angular_poincare (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (W : RatPoly) (hW : SupportedQuaternionBlocks n W) (P : Certificate n W)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p)
    (hcut : ∀ i, i ∈ ids → selectedLinkCutoff n i p ≤ K) :
    jointSquare n w K ids W p + -jointSquare n w K ids W (hybridSweep n w K ids p) ≤
      (1-w*w)*jointAngularEnergy n w K ids W p ids :=
  Q'.le_trans' _ _ _ (joint_sweep_efron_stein n hw0 hw1 K hK ids hn hids W hW P p hp)
    (residualEnergy_angular_le n hw0 hw1 K hK ids hn hids W hW P p hp ids (fun _ h => h) hcut)

/-- The same genuine product-angular bound at ONE explicit fixed-source
onset. It is not a cutoff bound uniform over changing source rows. -/
theorem joint_sweep_angular_poincare_at_cutoff (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j < n)
    (W : RatPoly) (hW : SupportedQuaternionBlocks n W) (P : Certificate n W)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p)
    (hK : jointPoincareCutoff n w ids p ≤ K) :
    jointSquare n w K ids W p + -jointSquare n w K ids W (hybridSweep n w K ids p) ≤
      (1-w*w)*jointAngularEnergy n w K ids W p ids :=
  joint_sweep_angular_poincare n hw0 hw1 K
    (Nat.le_trans (Nat.le_max_left _ _) hK) ids hn hids W hW P p hp
    (fun i hi => Nat.le_trans (selected_cutoff_le_fold n p i ids hi)
      (Nat.le_trans (Nat.le_max_right _ _) hK))

end YMGap.Continuum.SU2QuaternionProductHeatEfronStein

#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.jointWeight
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.jointSquare
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.residualEnergy
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_update_square_decomposition
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_update_square_le
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_sweep_square_le
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_sweep_loss_le_residualEnergy
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_sweep_efron_stein
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.selectedLinkCutoff
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.jointPoincareCutoff
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.jointAngularEnergy
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_residual_variance_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_residual_angular_le
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_sweep_angular_poincare
#print axioms YMGap.Continuum.SU2QuaternionProductHeatEfronStein.joint_sweep_angular_poincare_at_cutoff
