/-
# Exact local-update sweep for the original product heat operator

Each update integrates only its selected LOWER coordinate against its
original UPPER partner. The other coordinates remain on the doubled
carrier. The final ordered-head integration averages every inactive lower
slot and drops the already integrated ones. Equality is proved with EVERY
surviving polynomial insertion, not just for the normalized mean.

The head-chart update is literally the conditional operator used by the
checked local kinetic bound. This file does not yet telescope that bound
over the changing hybrid inputs, nor remove the signed endpoint correction.
It proves no interacting, OS, physical-mass, or continuum gap.
-/

import YMGap.Continuum.SU2QuaternionWeightedProjectionSweep
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionProductHeatTensorization
import YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
import YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification

namespace YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction (squaredHeatRate)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatTensorization
open YMGap.Continuum.SU2QuaternionWeightedProjectionSweep
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Integrating a lower slot early does not change the resulting polynomial
on the surviving Haar carrier. Every surviving insertion is retained. -/
theorem heads_project_carrier (tail heads slot : Nat) (hs : slot < heads) (p : RatPoly) :
    HaarCarrierEqv tail (partialHaarHeads heads (project slot p))
      (partialHaarHeads heads p) := by
  intro r
  have hp := project_fixed slot (liftBoundary heads r)
    (lift_lower_independent heads r slot hs)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing tail heads (project slot p) r))
      (Q'.eqv_trans _ _ _ (project_selfAdjoint (tail+heads) slot (by omega) p _)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_left p))
          (Q'.eqv_trans _ _ _ (head_pairing tail heads p r)
            (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))))

/-- The actual local updates, before any coordinate is discarded or renamed.
The tail of the schedule is processed first, as in `weightedSweep`. -/
def hybridSweep (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) : RatPoly :=
  weightedSweep (fun i => heatAt i (n+i) w K) ids p

/-! ## The exact selected-link stage bridge -/

/-- A head of the hybrid schedule is definitionally the selected-link update
on the doubled carrier.  The predecessor parameter in the selected-link
certificate is chosen so that `tailBlocks + 1 = n+n`; no carrier cast or
surrogate state is introduced. -/
theorem hybridSweep_cons_eq_selectedHeatProjection
    (n i : Nat) (hi : i < n) (ids : List Nat)
    (w : Q') (K : Nat) (p : RatPoly) :
    hybridSweep n w K (i :: ids) p =
      selectedHeatProjection (n+n-1) i (n+i)
        (by omega) (by omega) (by omega) w K
          (hybridSweep n w K ids p) := by
  rfl

/-- Conditional finite defect bound for one actual hybrid stage.  The only
open input is the exposed-chart pairing certificate at that stage; the
remaining expression is the literal `hybridSweep` update on the same doubled
carrier. -/
theorem hybridStep_defect_le_selected_block_energy_of_exposed
    (n i : Nat) (hi : i < n) (hn : 2 ≤ n)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : sufficientCutoff w ≤ K)
    (p : RatPoly)
    (hp : SupportedQuaternionBlocks (n+n) p)
    (exposed :
      SelectedLinkExposedHeadPairing
        (n+n-1) i (n+i)
        (by omega) (by omega) (by omega) (by omega) w K) :
    quaternionHaar (n+n) (polyMul p p) -
        quaternionHaar (n+n)
          (polyMul p
            (project i
              (polyMul (heatAt i (n+i) w K) p))) ≤
      ((1 : Q') - w) *
        quaternionHaar (n+n) (blockAngularSquare i p) := by
  let identification :=
    selectedLinkHeadIdentification_of_exposed
      (n+n-1) i (n+i)
      (by omega) (by omega) (by omega) (by omega) w K exposed
  have hcarrier : n+n-1+1 = n+n := by omega
  have hp' : SupportedQuaternionBlocks (n+n-1+1) p := by
    simpa [hcarrier] using hp
  have h := selectedHeatProjection_defect_le_selected_block_energy
    (n+n-1) i (n+i)
    (by omega) (by omega) (by omega) (by omega)
    hw0 hw1 K hK p hp' identification
  simpa [selectedHeatProjection, hcarrier] using h

/-- The preceding stage bound applies to the actual changing state produced by
the hybrid schedule.  This is still conditional on the exposed certificate,
but it is no longer an arbitrary-state restatement: the recursive tail state
is supplied by `hybridSweep_supported`. -/
theorem hybridSweep_cons_defect_le_selected_block_energy_of_exposed
    (n i : Nat) (hi : i < n) (hn : 2 ≤ n) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : sufficientCutoff w ≤ K)
    (p : RatPoly)
    (hp : SupportedQuaternionBlocks (n+n) p)
    (exposed :
      SelectedLinkExposedHeadPairing
        (n+n-1) i (n+i)
        (by omega) (by omega) (by omega) (by omega) w K) :
    quaternionHaar (n+n)
        (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p)) -
      quaternionHaar (n+n)
        (polyMul (hybridSweep n w K ids p)
          (hybridSweep n w K (i :: ids) p)) ≤
      ((1 : Q') - w) *
        quaternionHaar (n+n)
          (blockAngularSquare i (hybridSweep n w K ids p)) := by
  have htail : SupportedQuaternionBlocks (n+n)
      (hybridSweep n w K ids p) :=
    weightedSweep_supported (fun j => heatAt j (n+j) w K) ids
      (fun j hj => heat_supported (by have := hids j hj; omega)
        (by have := hids j hj; omega) w K) hp
  have h := hybridStep_defect_le_selected_block_energy_of_exposed
    n i hi hn hw0 hw1 K hK (hybridSweep n w K ids p) htail exposed
  simpa [hybridSweep, weightedSweep, selectedHeatProjection] using h

/-- The ordered list of same-object defects generated by the actual hybrid
schedule.  Each entry uses the state obtained from the unprocessed suffix;
the definition deliberately keeps the changing state visible. -/
def hybridSweepStageDefects
    (n : Nat) (w : Q') (K : Nat) : List Nat → RatPoly → List Q'
  | [], _ => []
  | i :: ids, p =>
      (quaternionHaar (n+n)
          (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p)) -
        quaternionHaar (n+n)
          (polyMul (hybridSweep n w K ids p)
            (hybridSweep n w K (i :: ids) p))) ::
        hybridSweepStageDefects n w K ids p

/-- The matching ordered list of selected-block angular energies. -/
def hybridSweepStageAngularEnergies
    (n : Nat) (w : Q') (K : Nat) : List Nat → RatPoly → List Q'
  | [], _ => []
  | i :: ids, p =>
      quaternionHaar (n+n)
          (blockAngularSquare i (hybridSweep n w K ids p)) ::
        hybridSweepStageAngularEnergies n w K ids p

/-- Conditional finite telescope of the changing hybrid stages.  This sums
the checked per-stage defects and keeps the corresponding changing-state
angular energies; it does not identify the sum with the endpoint form, since
inactive projections and signed cross terms are still separate obligations. -/
theorem hybridSweep_defect_budget_of_exposed
    (n : Nat) (ids : List Nat) (hn : 2 ≤ n)
    (hids : ∀ i, i ∈ ids → i < n)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : sufficientCutoff w ≤ K)
    (p : RatPoly)
    (hp : SupportedQuaternionBlocks (n+n) p)
    (exposed : ∀ (i : Nat) (hmem : i ∈ ids),
      SelectedLinkExposedHeadPairing
        (n+n-1) i (n+i)
        (by omega)
        (by have := hids i hmem; omega)
        (by have := hids i hmem; omega)
        (by have := hids i hmem; omega) w K) :
    qListSum (hybridSweepStageDefects n w K ids p) ≤
      ((1 : Q') - w) *
        qListSum (hybridSweepStageAngularEnergies n w K ids p) := by
  induction ids generalizing p with
  | nil =>
      simp only [hybridSweepStageDefects, hybridSweepStageAngularEnergies,
        qListSum]
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.mul_zero_eqv ((1 : Q') - w)))
  | cons i ids ih =>
      have hi : i < n := hids i List.mem_cons_self
      have hidsTail : ∀ j, j ∈ ids → j < n := by
        intro j hj
        exact hids j (List.mem_cons_of_mem i hj)
      have hhead := hybridSweep_cons_defect_le_selected_block_energy_of_exposed
        n i hi hn ids hidsTail hw0 hw1 K hK p hp
        (exposed i List.mem_cons_self)
      have htail := ih
        hidsTail p hp
        (fun j hj => exposed j (List.mem_cons_of_mem i hj))
      simp only [hybridSweepStageDefects, hybridSweepStageAngularEnergies,
        qListSum]
      have hadd := Q'.add_le_add hhead htail
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.mul_add_eqv ((1 : Q') - w)
            (quaternionHaar (n+n)
              (blockAngularSquare i (hybridSweep n w K ids p)))
          (qListSum (hybridSweepStageAngularEnergies n w K ids p)))))

/-- The exact signed endpoint/cross-term contribution of one changing stage.
The first parenthesis is the local defect already bounded above; the second
is retained with its sign because no positivity or cancellation theorem is
available for it. -/
def hybridSweepStageTelescopeTerms
    (n : Nat) (w : Q') (K : Nat) : List Nat → RatPoly → List Q'
  | [], _ => []
  | i :: ids, p =>
      ((quaternionHaar (n+n)
          (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p)) -
        quaternionHaar (n+n)
          (polyMul (hybridSweep n w K ids p)
            (hybridSweep n w K (i :: ids) p))) +
       (quaternionHaar (n+n)
          (polyMul (hybridSweep n w K ids p)
            (hybridSweep n w K (i :: ids) p)) -
        quaternionHaar (n+n)
          (polyMul (hybridSweep n w K (i :: ids) p)
            (hybridSweep n w K (i :: ids) p)))) ::
        hybridSweepStageTelescopeTerms n w K ids p

private theorem telescope_stage_cancel (a b c : Q') :
    (a - b) + (b - c) ≈ a - c := by
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1)))
      (.add (.var 1) (.neg (.var 2))))
    (.add (.var 0) (.neg (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => c)

/-- Exact finite endpoint decomposition for the actual changing hybrid
schedule.  The local defect budget controls only the first term in each
stage; the second, signed cross-term is displayed rather than discarded. -/
theorem hybridSweep_defect_cross_terms_eq_endpoint
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) :
    qListSum (hybridSweepStageTelescopeTerms n w K ids p) ≈
      quaternionHaar (n+n) (polyMul p p) -
        quaternionHaar (n+n)
          (polyMul (hybridSweep n w K ids p)
            (hybridSweep n w K ids p)) := by
  induction ids generalizing p with
  | nil =>
      simp only [hybridSweepStageTelescopeTerms, qListSum, hybridSweep]
      exact Q'.eqv_symm (Q'.add_neg_self_eqv
        (quaternionHaar (n+n) (polyMul p p)))
  | cons i ids ih =>
      have htail := ih p
      simp only [hybridSweepStageTelescopeTerms, qListSum]
      let a := quaternionHaar (n+n)
        (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p))
      let b := quaternionHaar (n+n)
        (polyMul (hybridSweep n w K ids p)
          (hybridSweep n w K (i :: ids) p))
      let c := quaternionHaar (n+n)
        (polyMul (hybridSweep n w K (i :: ids) p)
          (hybridSweep n w K (i :: ids) p))
      let d := quaternionHaar (n+n) (polyMul p p)
      have hstage : (a - b) + (b - c) ≈ a - c :=
        telescope_stage_cancel a b c
      have htail' : qListSum (hybridSweepStageTelescopeTerms n w K ids p) ≈
          d - a := by
        simpa [a, d] using htail
      have hsum : ((a - b) + (b - c)) +
          qListSum (hybridSweepStageTelescopeTerms n w K ids p) ≈
          (a - c) + (d - a) :=
        Q'.add_eqv_congr' hstage htail'
      have hcancel : (a - c) + (d - a) ≈ d - c := by
        exact poly_identity_of_normal_eq
          (.add (.add (.var 0) (.neg (.var 1)))
            (.add (.var 2) (.neg (.var 0))))
          (.add (.var 2) (.neg (.var 1))) (by decide)
          (fun | 0 => a | 1 => c | _ => d)
      exact Q'.eqv_trans _ _ _ hsum hcancel

/-- The final integration explicitly retains the inactive Haar projections.
In particular an empty schedule is Haar averaging, not the identity map. -/
def hybridMap (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) : RatPoly :=
  partialHaarHeads n (hybridSweep n w K ids p)

/-- Distinct original lower/upper pairs can be processed in either order,
coefficientwise, without identifying or averaging spectator variables. -/
theorem hybrid_updates_comm (n : Nat) (w : Q') (K i j : Nat)
    (hi : i < n) (hj : j < n) (hij : i ≠ j) (p : RatPoly) :
    RatPolyCoeffEqv
      (project i (polyMul (heatAt i (n+i) w K)
        (project j (polyMul (heatAt j (n+j) w K) p))))
      (project j (polyMul (heatAt j (n+j) w K)
        (project i (polyMul (heatAt i (n+i) w K) p)))) :=
  weightedUpdate_comm i j _ _ p
    (degree_zero_independent (heat_independent j i (n+i)
      (by intro h; exact hij h.symm) (by omega) w K))
    (degree_zero_independent (heat_independent i j (n+j) hij (by omega) w K))

/-- Intermediate updates keep the entire original doubled carrier. -/
theorem hybridSweep_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (n+n) p) :
    SupportedQuaternionBlocks (n+n) (hybridSweep n w K ids p) :=
  weightedSweep_supported _ ids
    (fun i hi => heat_supported (by have := hids i hi; omega)
      (by have := hids i hi; omega) w K) hp

theorem hybridMap_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (hybridMap n w K ids p) :=
  partialHaarHeads_supported n n _
    (hybridSweep_supported n w K ids hids
      (fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))))

/-- No later local update reintroduces a processed lower coordinate. -/
theorem hybridSweep_lower_independent (n : Nat) (w : Q') (K : Nat) :
    ∀ (ids : List Nat), (∀ i, i ∈ ids → i < n) →
      ∀ (slot : Nat), slot ∈ ids → ∀ p : RatPoly,
        QuaternionBlockIndependent slot (hybridSweep n w K ids p)
  | [], _, _, hs, _ => by cases hs
  | i::ids, hids, slot, hs, p => by
      by_cases he : slot = i
      · subst slot
        exact project_independent i _
      · apply project_preserves_independent
        apply quaternionBlockIndependent_polyMul
        · apply degree_zero_independent
          exact heat_independent slot i (n+i) he
            (by have := hids slot hs; omega) w K
        · exact hybridSweep_lower_independent n w K ids
            (fun j hj => hids j (List.mem_cons_of_mem i hj)) slot
            ((List.mem_cons.mp hs).resolve_left he) p

/-- An unprocessed upper partner is still absent. Its later use in a local
conditional estimate is justified from the original lower-input support. -/
theorem hybridSweep_unused_upper (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (slot : Nat) (hnot : slot ∉ ids)
    {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    QuaternionBlockIndependent (n+slot) (hybridSweep n w K ids p) := by
  apply weightedSweep_independent (n+slot) _ ids
  · intro i hi
    apply degree_zero_independent
    exact heat_independent (n+slot) i (n+i)
      (by have := hids i hi; omega)
      (by
        intro h
        have he : slot = i := by omega
        rw [he] at hnot
        exact hnot hi) w K
  · exact supported_upper_independent hp slot

/-- Exact finite Fubini on the ORIGINAL doubled carrier. No positivity,
nome, cutoff, or input-degree premise is needed for this identity. -/
theorem hybridSweep_pairing (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (p r : RatPoly) :
    quaternionHaar (n+n) (polyMul (hybridSweep n w K ids p) (liftBoundary n r)) ≈
      quaternionHaar (n+n)
        (polyMul (polyMul (productHeat n w K ids) p) (liftBoundary n r)) := by
  apply pairing (n+n) (fun i => heatAt i (n+i) w K) ids p (liftBoundary n r) hn
  · intro i hi
    have := hids i hi
    omega
  · intro i hi j hj hij
    apply degree_zero_independent
    exact heat_independent j i (n+i) (by intro h; exact hij h.symm)
      (by have := hids j hj; omega) w K
  · intro i hi
    exact lift_lower_independent n r i (hids i hi)

/-- This is the actual product-operator join, with EVERY surviving insertion.
The final lower Haar integration includes all inactive slots. -/
theorem hybridMap_carrier (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (p : RatPoly) :
    HaarCarrierEqv n (hybridMap n w K ids p) (productMap n w K ids p) := by
  intro r
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing n n (hybridSweep n w K ids p) r))
      (Q'.eqv_trans _ _ _ (hybridSweep_pairing n w K ids hn hids p r)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
          (Q'.eqv_symm (productMap_pairing n w K ids p r)))))

/-- In particular the same signed input has the same kinetic quadratic form;
the equality is not merely an equality of normalized means. -/
theorem hybridMap_quadratic (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (p : RatPoly) :
    quaternionHaar n (polyMul p (hybridMap n w K ids p)) ≈
      quaternionHaar n (polyMul p (productMap n w K ids p)) :=
  hybridMap_carrier n w K ids hn hids p p

/- The carrier equality also identifies the square norm of the local sweep
with the square norm of the original product operator. This uses the carrier
identity twice, with the two possible insertions, and then only the
coefficient commutativity of the polynomial product. -/
theorem hybridMap_square (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (p : RatPoly) :
    quaternionHaar n
        (polyMul (hybridMap n w K ids p) (hybridMap n w K ids p)) ≈
      quaternionHaar n
        (polyMul (productMap n w K ids p) (productMap n w K ids p)) := by
  have hleft := hybridMap_carrier n w K ids hn hids p
    (hybridMap n w K ids p)
  have hright := hybridMap_carrier n w K ids hn hids p
    (productMap n w K ids p)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm
        (hybridMap n w K ids p) (productMap n w K ids p))) hright)

/- Consequently the checked, width-independent centered product contraction
transfers verbatim to the explicit local-update sweep. This remains an
ordinary-Haar finite estimate; it is not an OS or interacting-transfer gap. -/
theorem hybridMap_centered_square_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (hc : quaternionHaar n f ≈ 0) :
    quaternionHaar n
        (polyMul (hybridMap n w K ids f) (hybridMap n w K ids f)) ≤
      squaredHeatRate w * quaternionHaar n (polyMul f f) := by
  have hsq := hybridMap_square n w K ids hn hids f
  have hprod := productMap_centered_square_bound n hw0 hw1 K hK ids hn hids hf hc
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsq) hprod

/-- A single selected update is exactly the local `headMap` after dropping
its cleared source coordinates. All copied spectator coordinates survive. -/
theorem head_update_eq (w : Q') (K : Nat) (p : RatPoly) :
    dropHeadPolynomial (project 0 (polyMul (heatAt 0 1 w K) (copy p))) =
      headMap w K p :=
  drop_project_head _

end YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.heads_project_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.head_update_eq
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybrid_updates_comm
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_lower_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_unused_upper
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_quadratic
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_square
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_centered_square_bound
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_cons_eq_selectedHeatProjection
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridStep_defect_le_selected_block_energy_of_exposed
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_cons_defect_le_selected_block_energy_of_exposed
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_defect_budget_of_exposed
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweepStageTelescopeTerms
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_defect_cross_terms_eq_endpoint
