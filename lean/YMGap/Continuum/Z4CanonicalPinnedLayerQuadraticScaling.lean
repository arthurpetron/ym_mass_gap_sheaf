/-
# Quadratic scaling of canonical face-pinned layers

At cutoff one, the only coupling-dependent factor in a canonical surface
activity is one fundamental heat-kernel coefficient per excited face.  A
one-face support has exactly zero Haar multiplicity.  Consequently every
nonzero term in a face-pinned layer carries at least two powers of any exact
coefficient contraction.

This module records that statement first termwise and then after summing the
complete finite pinned layer.  It is a local strong-coupling estimate; it does
not assert an RG comparison or an infinite-volume limit.
-/

import YMGap.Continuum.Z4CanonicalSingletonActivityZero
import YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor

namespace YMGap.Continuum.Z4CanonicalPinnedLayerQuadraticScaling

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalSingletonActivityZero
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem mul_four_regroup (A B C D : Q') :
    ((A * B) * (C * D)).eqv ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem pow_mul_base_eqv (a b : Q') : ∀ exponent : Nat,
    (a * b) ^ exponent ≈ a ^ exponent * b ^ exponent
  | 0 => by
      simp only [Q'.pow_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | exponent + 1 => by
      simp only [Q'.pow_succ]
      refine Q'.eqv_trans _
        ((a * b) * (a ^ exponent * b ^ exponent)) _
        (Q'.mul_eqv_congr_left (a * b) _ _
          (pow_mul_base_eqv a b exponent)) ?_
      exact mul_four_regroup a b (a ^ exponent) (b ^ exponent)

private theorem pow_eqv_congr_local {a b : Q'} (h : a ≈ b) :
    ∀ exponent : Nat, a ^ exponent ≈ b ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      simp only [Q'.pow_succ]
      exact Q'.eqv_trans _ (b * a ^ exponent) _
        (Q'.mul_eqv_congr_right _ _ _ h)
        (Q'.mul_eqv_congr_left _ _ _
          (pow_eqv_congr_local h exponent))

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ xs : List A,
    (∀ item, item ∈ xs → lower item ≤ upper item) →
      listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_mul_left_local {A : Type}
    (factor : Q') (value : A → Q') : ∀ xs : List A,
    listQSum (fun item => factor * value item) xs ≈
      factor * listQSum value xs
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv factor)
  | head :: tail => by
      change factor * value head +
          listQSum (fun item => factor * value item) tail ≈
        factor * (value head + listQSum value tail)
      exact Q'.eqv_trans _
        (factor * value head + factor * listQSum value tail) _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_mul_left_local factor value tail))
        (Q'.eqv_symm (Q'.mul_add_eqv factor _ _))

/-- Exact factorization of a cutoff-one canonical activity into its one
fundamental coefficient per face and its coupling-independent Haar factor. -/
theorem canonicalSurfaceActivity_eqv_coeffPow_mul_link
    (coupling : Q') {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    canonicalSurfaceActivity coupling n support ≈
      (coeffW coupling 1) ^ support.length *
        explicitLinkMultiplicityProduct 1 n (componentLabel support)
          (touchedIndexedLinks n (componentLabel support)) := by
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  exact Q'.mul_eqv_congr_right _ _ _
    (parametricPhysicalFaceFactor_componentLabel_eqv_pow
      coupling hsupport)

/-- If the fundamental coefficient contracts exactly by `ratio`, then every
canonical activity contracts by `ratio ^ support.length`. -/
theorem canonicalSurfaceActivity_exact_coefficient_scaling
    {lower upper ratio : Q'} {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hcoefficient : coeffW lower 1 ≈ ratio * coeffW upper 1) :
    canonicalSurfaceActivity lower n support ≈
      ratio ^ support.length *
        canonicalSurfaceActivity upper n support := by
  let linkFactor := explicitLinkMultiplicityProduct 1 n
    (componentLabel support)
    (touchedIndexedLinks n (componentLabel support))
  have hlower := canonicalSurfaceActivity_eqv_coeffPow_mul_link
    lower hsupport
  have hupper := canonicalSurfaceActivity_eqv_coeffPow_mul_link
    upper hsupport
  have hcoefficientPow :
      (coeffW lower 1) ^ support.length ≈
        ratio ^ support.length * (coeffW upper 1) ^ support.length := by
    exact Q'.eqv_trans _ ((ratio * coeffW upper 1) ^ support.length) _
      (pow_eqv_congr_local hcoefficient support.length)
      (pow_mul_base_eqv ratio (coeffW upper 1) support.length)
  refine Q'.eqv_trans _
    ((ratio ^ support.length * (coeffW upper 1) ^ support.length) *
      linkFactor) _ ?_ ?_
  · exact Q'.eqv_trans _
      ((coeffW lower 1) ^ support.length * linkFactor) _
      hlower
      (Q'.mul_eqv_congr_right _ _ _ hcoefficientPow)
  · refine Q'.eqv_trans _
      (ratio ^ support.length *
        ((coeffW upper 1) ^ support.length * linkFactor)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hupper)

/-- Singleton vanishing upgrades an exact coefficient contraction to a
uniform quadratic activity contraction on every canonical polymer. -/
theorem canonicalSurfacePolymer_activity_le_ratio_sq_mul
    {lower upper ratio : Q'}
    (hupper : (0 : Q') ≤ upper)
    (hratio0 : (0 : Q') ≤ ratio)
    (hratio1 : ratio ≤ (1 : Q'))
    (hcoefficient : coeffW lower 1 ≈ ratio * coeffW upper 1)
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    canonicalSurfaceActivity lower n polymer ≤
      ratio ^ 2 * canonicalSurfaceActivity upper n polymer := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports hpolymer
  have hscale := canonicalSurfaceActivity_exact_coefficient_scaling
    hsupport hcoefficient
  cases polymer with
  | nil =>
      obtain ⟨face, hface⟩ :=
        canonicalSurfacePolymers_allNonempty n [] hpolymer
      exact absurd hface List.not_mem_nil
  | cons face tail =>
      cases tail with
      | nil =>
          have hzero := canonicalSurfaceActivity_singleton_eqv_zero
            lower hsupport
          have hright0 : (0 : Q') ≤
              ratio ^ 2 * canonicalSurfaceActivity upper n [face] :=
            Q'.mul_nonneg _ _
              (Q'.pow_nonneg ratio hratio0 2)
              (canonicalSurfaceActivity_nonnegative hupper n [face])
          exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero) hright0
      | cons second rest =>
          have hlength : 2 ≤ (face :: second :: rest).length := by
            simp only [List.length_cons]
            omega
          have hpower : ratio ^ (face :: second :: rest).length ≤
              ratio ^ 2 :=
            YMGap.Continuum.HKConvGen.pow_base_antitone
              hratio0 hratio1 hlength
          have hactivity0 : (0 : Q') ≤
              canonicalSurfaceActivity upper n (face :: second :: rest) :=
            canonicalSurfaceActivity_nonnegative hupper n _
          exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
            (Q'.mul_le_mul_of_nonneg_right _ _ _ hpower hactivity0)

/-- The termwise quadratic estimate survives summation over an arbitrary
face-pinned canonical layer. -/
theorem couplingPinnedLayerActivity_le_ratio_sq_mul
    {lower upper ratio : Q'}
    (hupper : (0 : Q') ≤ upper)
    (hratio0 : (0 : Q') ≤ ratio)
    (hratio1 : ratio ≤ (1 : Q'))
    (hcoefficient : coeffW lower 1 ≈ ratio * coeffW upper 1)
    (n rootId : Nat) :
    couplingPinnedLayerActivity lower n rootId ≤
      ratio ^ 2 * couplingPinnedLayerActivity upper n rootId := by
  unfold couplingPinnedLayerActivity markedActivitySum
  let pinned := (canonicalSurfacePolymers n).filter
    (canonicalContainsFaceB rootId)
  have hterm : listQSum (canonicalSurfaceActivity lower n) pinned ≤
      listQSum
        (fun polymer => ratio ^ 2 *
          canonicalSurfaceActivity upper n polymer) pinned := by
    apply listQSum_mono_local
    intro polymer hpolymer
    exact canonicalSurfacePolymer_activity_le_ratio_sq_mul
      hupper hratio0 hratio1 hcoefficient
      (List.mem_filter.mp hpolymer).1
  exact Q'.le_trans' _ _ _ hterm
    (Q'.le_of_eqv
      (listQSum_mul_left_local (ratio ^ 2)
        (canonicalSurfaceActivity upper n) pinned))

/-- At the proved strong-coupling anchor, the complete pinned layer therefore
has the explicit quadratic ceiling `ratio² / 2`. -/
theorem couplingPinnedLayerActivity_le_ratio_sq_mul_half
    {lower ratio : Q'}
    (hratio0 : (0 : Q') ≤ ratio)
    (hratio1 : ratio ≤ (1 : Q'))
    (hcoefficient : coeffW lower 1 ≈
      ratio * anchorFaceCoefficient)
    (n rootId : Nat) :
    couplingPinnedLayerActivity lower n rootId ≤
      ratio ^ 2 * Q'.mkPos 1 2 (by decide) := by
  have hanchorCoefficient : coeffW lower 1 ≈
      ratio * coeffW anchorCoupling 1 :=
    Q'.eqv_trans _ (ratio * anchorFaceCoefficient) _
      hcoefficient
      (Q'.mul_eqv_congr_left ratio _ _
        (Q'.eqv_symm anchorFundamentalCoefficient))
  have hscale := couplingPinnedLayerActivity_le_ratio_sq_mul
    (lower := lower) (upper := anchorCoupling) (ratio := ratio)
    (by decide) hratio0 hratio1 hanchorCoefficient n rootId
  have hratioPow0 : (0 : Q') ≤ ratio ^ 2 :=
    Q'.pow_nonneg ratio hratio0 2
  exact Q'.le_trans' _ _ _ hscale
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (canonicalPinnedLayerActivity_le_half n rootId)
      hratioPow0)

#print axioms canonicalSurfaceActivity_eqv_coeffPow_mul_link
#print axioms canonicalSurfaceActivity_exact_coefficient_scaling
#print axioms canonicalSurfacePolymer_activity_le_ratio_sq_mul
#print axioms couplingPinnedLayerActivity_le_ratio_sq_mul
#print axioms couplingPinnedLayerActivity_le_ratio_sq_mul_half

end YMGap.Continuum.Z4CanonicalPinnedLayerQuadraticScaling
