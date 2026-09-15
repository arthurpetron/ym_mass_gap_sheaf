/-
# An actual local-heat cutoff limit in the ORIGINAL OS completion

The samples are original plaquette expressions e*H_K on a fixed finite
source region. Their signed tail bound computes a cutoff modulus and a
Cauchy representative in the existing thermodynamic completion. Every
cutoff beyond that modulus approximates the returned state in its actual
completed squared distance. No representative is selected from a quotient.

The modulus depends on the source expression, region size and test nome,
not volume, padding, cutoff increment or the surrounding action cutoff.
The thermodynamic action remains the existing fixed nome 1/1024. This is
not a limit of changing actions or inverse collar corrections, an OS
multiplication operator, or an original T2 preimage.

The allNome construction uses the SAME sample sequence and completion,
with a nome-dependent late-tail modulus for every rational 0<w<1. Where
the older small-nome guard holds, its state equals the older state.
-/

import YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm
import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
import YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff

namespace YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound (bound bound_nonnegative)
open YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval (tailConstant tailConstant_nonnegative)
open YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm (dressed difference thermodynamic_norm_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient (subtract)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (correctionOrder correctionOrder_budget)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (centralExtent)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPlaquetteAt slabPhysicalFaceEdges)
open YMGap.Continuum.BF4ExactSlabLocalBulkSelection (nearIds)
open YMGap.Continuum.BF4ExactSlabLocalBulkCutoff (otherFaces fullNear_length_le)
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion (collar_mem)
open YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff (touching_other_lower)

def cutoffConstant (w : Q') (size : Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  bound e * (tailConstant w size * tailConstant w size)

theorem cutoffConstant_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (size : Nat)
    {half : Nat} (e : PlaquetteExpression half) : (0 : Q') ≤ cutoffConstant w size e :=
  Q'.mul_nonneg _ _ (bound_nonnegative e)
    (Q'.mul_nonneg _ _ (tailConstant_nonnegative hw size) (tailConstant_nonnegative hw size))

/-- A computed natural number, not an existential convergence assertion. -/
def cutoffModulus {w : Q'} (hw : (0 : Q') ≤ w) (size : Nat)
    {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  correctionOrder (cutoffConstant w size e) (cutoffConstant_nonnegative hw size e) epsilon

theorem cutoff_budget {w : Q'} (hw : (0 : Q') ≤ w) (size : Nat)
    {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K : Nat) (hK : cutoffModulus hw size e epsilon ≤ K) :
    bound e * ((tailConstant w size * HalfPow.half^K)*(tailConstant w size * HalfPow.half^K)) ≤ epsilon := by
  let c := cutoffConstant w size e
  have hc := cutoffConstant_nonnegative hw size e
  have hpow : (0 : Q') ≤ HalfPow.half^K := Q'.pow_nonneg _ (by decide) K
  have hsmall : HalfPow.half^K ≤ (1 : Q') := half_pow_antitone 0 K (Nat.zero_le _)
  have hsquare : HalfPow.half^K * HalfPow.half^K ≤ HalfPow.half^K :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall hpow)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hnorm : Q'.eqv
      (bound e * ((tailConstant w size * HalfPow.half^K)*(tailConstant w size * HalfPow.half^K)))
      (c * (HalfPow.half^K * HalfPow.half^K)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => bound e | 1 => tailConstant w size | _ => HalfPow.half^K)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnorm)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hsquare hc)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (half_pow_antitone _ K hK) hc)
        (correctionOrder_budget c hc epsilon he)))

def sample (w : Q') {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) (K : Nat) : Presentation :=
  ⟨half,dressed w K ids hi e⟩

private theorem sameBase_subtract {base : Nat} (e f : PlaquetteExpression base) :
    subtract (embed ⟨base,e⟩) (embed ⟨base,f⟩) =
      embed ⟨base, BF4ExactSlabPlaquetteNullQuotient.subtract e f⟩ := by
  change embed (presentationSubtract ⟨base,e⟩ ⟨base,f⟩) = _
  apply embed_eq_of_coeff _ _ (base+base) (Nat.le_refl _) (Nat.le_add_right _ _)
  intro volume hv
  rw [show presentationSubtract ⟨base,e⟩ ⟨base,f⟩ = add ⟨base,e⟩ (smul (-1) ⟨base,f⟩) from rfl,
    polynomial_add _ _ volume hv]
  exact RatPolyCoeffEqv.refl _

theorem sample_distance (w : Q') {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) (K L : Nat) :
    Equiv (distSq (sample w ids hi e (K+L)) (sample w ids hi e K))
      (formLimit (difference w K L ids hi e) (difference w K L ids hi e)) := by
  apply Quotient.exact (s := crealSetoid)
  rw [distSq_pin]
  unfold sample
  rw [sameBase_subtract, pairing_sameBase]
  rfl

theorem sample_append_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : cutoffModulus hw0 ids.length e epsilon ≤ K) :
    leEv (distSq (sample w ids hi e (K+L)) (sample w ids hi e K)) (ofQ' epsilon) :=
  leEv_trans (leEv_of_equiv (sample_distance w ids hi e K L))
    (leEv_trans (thermodynamic_norm_bound hw0 hw1 hsmall K L ids hi e)
      (leEv_ofQ'_of_approx_ge (fun _ => cutoff_budget hw0 ids.length e epsilon he K hK)))

theorem sample_cauchy {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : cutoffModulus hw0 ids.length e epsilon ≤ m) (hn : cutoffModulus hw0 ids.length e epsilon ≤ n) :
    leEv (distSq (sample w ids hi e m) (sample w ids hi e n)) (ofQ' epsilon) := by
  cases Nat.le_total m n with
  | inl h =>
      have hb := sample_append_bound hw0 hw1 hsmall ids hi e epsilon he m (n-m) hm
      rw [Nat.add_sub_of_le h] at hb
      exact leEv_trans (leEv_of_equiv (distSq_symm _ _)) hb
  | inr h =>
      have hb := sample_append_bound hw0 hw1 hsmall ids hi e epsilon he n (m-n) hn
      rwa [Nat.add_sub_of_le h] at hb

def cauchy {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) : seminorm.Cauchy where
  seq := sample w ids hi e
  modulus := cutoffModulus hw0 ids.length e
  isCauchy := sample_cauchy hw0 hw1 hsmall ids hi e

def state {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) : Completion :=
  Quotient.mk seminorm.completionSetoid (cauchy hw0 hw1 hsmall ids hi e)

theorem state_approximation {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat) (hK : cutoffModulus hw0 ids.length e epsilon ≤ K) :
    RCle (completedDist (embedPresentation (sample w ids hi e K)) (state hw0 hw1 hsmall ids hi e))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  constantApproximation_bound (cauchy hw0 hw1 hsmall ids hi e) epsilon he K hK

/-- The ACTUAL other faces touching the previous selected crossing link. -/
def selectedRegion (half id : Nat) : List Nat :=
  nearIds (centralExtent half) (slabPlaquetteAt (centralExtent half) id) (otherFaces (centralExtent half) id)

private theorem erase_perm (id : Nat) : ∀ {ids : List Nat}, id ∈ ids → ids.Perm (id::ids.erase id)
  | [], h => False.elim (List.not_mem_nil h)
  | head::tail, h => by
      by_cases he : head=id
      · subst head
        rw [List.erase_cons_head]
      · rw [List.erase_cons_tail (a := id) (b := head) (by simp [he])]
        have ht := (List.mem_cons.mp h).resolve_left (fun h => he h.symm)
        exact (List.Perm.cons head (erase_perm id ht)).trans (List.Perm.swap id head _)

theorem selectedRegion_lower {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (j : Nat) (hj : j ∈ selectedRegion half id) : j ∈ centralLowerFaceIds half := by
  have ho := collar_mem hj
  have hp := erase_perm id (mem_centralFixedFaceIds.mp hi).1
  have hn := (List.nodup_cons.mp (hp.nodup (CayleyParentInj.range_nodup _))).1
  have hphys := hp.mem_iff.mpr (List.mem_cons_of_mem id ho)
  exact touching_other_lower hi hphys (fun h => hn (h ▸ ho)) (by
    have ht := (List.mem_filter.mp hj).2
    simpa only [Bool.not_eq_true'] using ht)

theorem selectedRegion_length_le {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    (selectedRegion half id).length ≤ 5 := fullNear_length_le (mem_centralFixedFaceIds.mp hi).1

/-- Heat removal on that fixed source region, in the OLD completion. -/
def selectedState {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (e : PlaquetteExpression half) : Completion :=
  state hw0 hw1 hsmall (selectedRegion half id) (selectedRegion_lower hi) e

theorem selectedState_approximation {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat)
    (hK : cutoffModulus hw0 (selectedRegion half id).length e epsilon ≤ K) :
    RCle (completedDist (embedPresentation (sample w (selectedRegion half id) (selectedRegion_lower hi) e K))
      (selectedState hw0 hw1 hsmall hi e)) (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  state_approximation hw0 hw1 hsmall (selectedRegion half id) (selectedRegion_lower hi) e epsilon he K hK

open YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm (normCutoff thermodynamic_small_norm_allNome)

theorem sample_append_bound_allNome {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat)
    (hK : normCutoff w ids.length (bound e) epsilon ≤ K) :
    leEv (distSq (sample w ids hi e (K+L)) (sample w ids hi e K)) (ofQ' epsilon) :=
  leEv_trans (leEv_of_equiv (sample_distance w ids hi e K L))
    (thermodynamic_small_norm_allNome hw0 hw1 K L ids hi e epsilon he hK)

theorem sample_cauchy_allNome {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : normCutoff w ids.length (bound e) epsilon ≤ m)
    (hn : normCutoff w ids.length (bound e) epsilon ≤ n) :
    leEv (distSq (sample w ids hi e m) (sample w ids hi e n)) (ofQ' epsilon) := by
  cases Nat.le_total m n with
  | inl h =>
      have hb := sample_append_bound_allNome hw0 hw1 ids hi e epsilon he m (n-m) hm
      rw [Nat.add_sub_of_le h] at hb
      exact leEv_trans (leEv_of_equiv (distSq_symm _ _)) hb
  | inr h =>
      have hb := sample_append_bound_allNome hw0 hw1 ids hi e epsilon he n (m-n) hn
      rwa [Nat.add_sub_of_le h] at hb

/-- Original presentations plus an explicit modulus; no representative choice. -/
def cauchy_allNome {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) : seminorm.Cauchy where
  seq := sample w ids hi e
  modulus := normCutoff w ids.length (bound e)
  isCauchy := sample_cauchy_allNome hw0 hw1 ids hi e

def state_allNome {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) : Completion :=
  Quotient.mk seminorm.completionSetoid (cauchy_allNome hw0 hw1 ids hi e)

theorem state_allNome_approximation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat)
    (hK : normCutoff w ids.length (bound e) epsilon ≤ K) :
    RCle (completedDist (embedPresentation (sample w ids hi e K)) (state_allNome hw0 hw1 ids hi e))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  constantApproximation_bound (cauchy_allNome hw0 hw1 ids hi e) epsilon he K hK

/-- Changing the modulus does not change the old completed observable. -/
theorem state_allNome_eq_legacy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) :
    state_allNome hw0 hw1 ids hi e = state (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall ids hi e := by
  apply Quotient.sound
  exact ⟨⟨fun _ => 0,fun _ he _ _ => leEv_trans (leEv_of_equiv (distSq_refl _))
    (leEv_of_le (ofQ'_le_ofQ' (Q'.le_of_lt he)))⟩⟩

/-- The very same selected touching-face region, now at any inserted 0<w<1. -/
def selectedState_allNome {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half id : Nat} (hi : id ∈ centralFixedFaceIds half) (e : PlaquetteExpression half) : Completion :=
  state_allNome hw0 hw1 (selectedRegion half id) (selectedRegion_lower hi) e

theorem selectedState_allNome_approximation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half id : Nat} (hi : id ∈ centralFixedFaceIds half) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat)
    (hK : normCutoff w (selectedRegion half id).length (bound e) epsilon ≤ K) :
    RCle (completedDist (embedPresentation (sample w (selectedRegion half id) (selectedRegion_lower hi) e K))
      (selectedState_allNome hw0 hw1 hi e)) (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  state_allNome_approximation hw0 hw1 (selectedRegion half id) (selectedRegion_lower hi) e epsilon he K hK

end YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.cutoffConstant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.cutoffConstant_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.cutoffModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.cutoff_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.sample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.sample_distance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.sample_append_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.sample_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.cauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.state_approximation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.selectedRegion
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.selectedRegion_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.selectedRegion_length_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.selectedState
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.selectedState_approximation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.sample_append_bound_allNome
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.sample_cauchy_allNome
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.cauchy_allNome
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.state_allNome
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.state_allNome_approximation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.state_allNome_eq_legacy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.selectedState_allNome
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLocalHeatState.selectedState_allNome_approximation
