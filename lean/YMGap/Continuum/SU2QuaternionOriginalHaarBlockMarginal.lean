/-
# Stable-coordinate block marginals for the ORIGINAL quaternion Haar law

The recursive original quaternionHaar and finiteProductHaar are proved to
have the same moments, including their out-of-carrier convention. Existing
one-block spectator Fubini therefore applies to the original functional.
Finite schedules preserve support and remove exactly their selected block
dependencies without renumbering any remaining link coordinate.

These identities marginalize the supplied full polynomial. No incident
action factor may be omitted, and no independence is inferred from geometry.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
import YMGap.Continuum.SU2QuaternionBlockLocality

namespace YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem blockOrder_eq_range : ∀ blocks : Nat,
    quaternionBlockOrder blocks = List.range blocks
  | 0 => rfl
  | blocks+1 => by
      rw [quaternionBlockOrder, blockOrder_eq_range]
      exact List.range_succ_eq_map.symm

private theorem blockProduct_eq_listProduct (m : List Nat) : ∀ bs : List Nat,
    quaternionBlockMomentProduct m bs =
      listQProduct (SU2QuaternionArbitraryHaarBlockReflection.quaternionBlockMoment m) bs
  | [] => rfl
  | b::bs => by
      change SU2QuaternionFiniteProductHaarCarrier.quaternionBlockMoment b m *
        quaternionBlockMomentProduct m bs = _
      rw [blockProduct_eq_listProduct m bs]
      rfl

theorem quaternionHaarMono_eq_finiteProductHaarMono (blocks : Nat) (m : List Nat) :
    quaternionHaarMono blocks m ≈ finiteProductHaarMono blocks m := by
  unfold quaternionHaarMono finiteProductHaarMono
  split
  · rw [blockProduct_eq_listProduct]
    simpa only [blockOrder_eq_range] using quaternionHaarPrefix_eq_block_product blocks m
  · exact Q'.eqv_refl _

/-- Same moments and same raw coefficient fold, with no support premise. -/
theorem quaternionHaar_eq_finiteProductHaar (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p ≈ finiteProductHaar blocks p
  | [] => Q'.eqv_refl _
  | t::p => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (quaternionHaarMono_eq_finiteProductHaarMono blocks t.1))
      (quaternionHaar_eq_finiteProductHaar blocks p)

theorem quaternionHaar_polyMul_eq_after_integratingBlock
    (blocks selected : Nat) (hs : selected < blocks) (spectator factor : RatPoly)
    (hi : QuaternionBlockIndependent selected spectator) :
    quaternionHaar blocks (polyMul spectator factor) ≈
      quaternionHaar blocks (polyMul spectator (integrateQuaternionBlock selected factor)) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_eq_finiteProductHaar blocks _)
    (Q'.eqv_trans _ _ _
      (finiteProductHaar_polyMul_eq_after_integrating_right blocks selected hs spectator factor hi)
      (Q'.eqv_symm (quaternionHaar_eq_finiteProductHaar blocks _)))

/-- Arbitrary in-range schedules, including repeated indices, keep the SAME spectator. -/
theorem quaternionHaar_polyMul_eq_after_integratingBlocks (blocks : Nat) :
    ∀ (schedule : List Nat) (spectator factor : RatPoly),
    (∀ b, b ∈ schedule → b < blocks) →
    (∀ b, b ∈ schedule → QuaternionBlockIndependent b spectator) →
    quaternionHaar blocks (polyMul spectator factor) ≈
      quaternionHaar blocks (polyMul spectator (integrateQuaternionBlocks schedule factor))
  | [], _, _, _, _ => Q'.eqv_refl _
  | b::bs, spectator, factor, hr, hi =>
      Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_eq_after_integratingBlock blocks b (hr b List.mem_cons_self)
          spectator factor (hi b List.mem_cons_self))
        (quaternionHaar_polyMul_eq_after_integratingBlocks blocks bs spectator
          (integrateQuaternionBlock b factor)
          (fun c hc => hr c (List.mem_cons_of_mem b hc))
          (fun c hc => hi c (List.mem_cons_of_mem b hc)))

theorem integrateBlocks_supported {blocks : Nat} : ∀ (schedule : List Nat) {p : RatPoly},
    SupportedQuaternionBlocks blocks p →
      SupportedQuaternionBlocks blocks (integrateQuaternionBlocks schedule p)
  | [], _, hp => hp
  | b::bs, _, hp => integrateBlocks_supported bs (integrateQuaternionBlock_supported b hp)

private theorem clear_eq_of_blockZero {m : List Nat} {b : Nat} (hz : BlockZero m b) :
    clearQuaternionBlock b m = m := by
  apply natList_eq_of_length_getD (clearQuaternionBlock_length b m)
  intro coordinate _
  change exponentAt (clearQuaternionBlock b m) coordinate = exponentAt m coordinate
  rw [exponentAt_clearQuaternionBlock]
  by_cases hc : coordinateInQuaternionBlock b coordinate
  · rw [if_pos hc]
    have hc' := hc
    unfold coordinateInQuaternionBlock at hc'
    have he : 4*b + (coordinate-4*b) = coordinate := by omega
    have hzero := hz (coordinate-4*b) (by omega)
    rw [he] at hzero
    exact hzero.symm
  · rw [if_neg hc]

/-- Existing block locality supplies the exact syntactic spectator predicate. -/
theorem independent_of_local {blocks b : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (hb : b < blocks) (ha : ¬ allowed b) :
    QuaternionBlockIndependent b p :=
  fun t ht => clear_eq_of_blockZero (hp t ht b hb ha)

theorem integrateBlock_local {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (selected : Nat) :
    BlockLocal blocks (fun b => allowed b ∧ b ≠ selected) (integrateQuaternionBlock selected p) := by
  intro t ht b hb hn component hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change exponentAt (clearQuaternionBlock selected s.1) (4*b+component) = 0
  by_cases he : b = selected
  · subst b
    exact exponentAt_clearQuaternionBlock_self s.1 selected component hc
  · rw [exponentAt_clearQuaternionBlock_of_ne s.1 he hc]
    exact hp s hs b hb (fun ha => hn ⟨ha, he⟩) component hc

/-- Every integrated index is absent; all other locality restrictions remain. -/
theorem integrateBlocks_local {blocks : Nat} {allowed : Nat → Prop} :
    ∀ (schedule : List Nat) {p : RatPoly}, BlockLocal blocks allowed p →
      BlockLocal blocks (fun b => allowed b ∧ b ∉ schedule) (integrateQuaternionBlocks schedule p)
  | [], _, hp => by
      intro t ht b hb hn
      exact hp t ht b hb (fun ha => hn ⟨ha, List.not_mem_nil⟩)
  | selected::rest, p, hp => by
      have h := integrateBlocks_local (allowed := fun b => allowed b ∧ b ≠ selected) rest
        (integrateBlock_local hp selected)
      intro t ht b hb hn
      exact h t ht b hb (fun ha => hn ⟨ha.1.1, fun hm =>
        (List.mem_cons.mp hm).elim ha.1.2 ha.2⟩)

/-- Every selected block has zero exponents in every residual monomial. -/
theorem integrateBlocks_zero (blocks : Nat) (schedule : List Nat) (p : RatPoly) :
    ∀ t, t ∈ integrateQuaternionBlocks schedule p →
      ∀ b, b < blocks → b ∈ schedule → BlockZero t.1 b := by
  have hp : BlockLocal blocks (fun _ => True) p :=
    fun _ _ _ _ hn => False.elim (hn True.intro)
  have h := integrateBlocks_local schedule hp
  intro t ht b hb hs
  exact h t ht b hb (fun ha => ha.2 hs)

/-- A literal filtered carrier complement leaves only the retained blocks. -/
theorem integrateFiltered_local {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (remove : Nat → Bool) :
    BlockLocal blocks (fun b => allowed b ∧ remove b = false)
      (integrateQuaternionBlocks ((List.range blocks).filter remove) p) := by
  have h := integrateBlocks_local ((List.range blocks).filter remove) hp
  intro t ht b hb hn
  apply h t ht b hb
  intro ha
  apply hn
  refine ⟨ha.1, ?_⟩
  cases he : remove b with
  | false => rfl
  | true => exact False.elim (ha.2 (List.mem_filter.mpr ⟨List.mem_range.mpr hb, he⟩))

/-- Original-Haar conditional integration, consuming the caller's actual locality proof. -/
theorem quaternionHaar_polyMul_eq_after_integratingBlocks_of_local
    {blocks : Nat} {allowed : Nat → Prop} {spectator : RatPoly}
    (hp : BlockLocal blocks allowed spectator) (schedule : List Nat) (factor : RatPoly)
    (hs : ∀ b, b ∈ schedule → b < blocks ∧ ¬ allowed b) :
    quaternionHaar blocks (polyMul spectator factor) ≈
      quaternionHaar blocks (polyMul spectator (integrateQuaternionBlocks schedule factor)) :=
  quaternionHaar_polyMul_eq_after_integratingBlocks blocks schedule spectator factor
    (fun b hb => (hs b hb).1)
    (fun b hb => independent_of_local hp (hs b hb).1 (hs b hb).2)

end YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal

#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaarMono_eq_finiteProductHaarMono
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_eq_finiteProductHaar
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_polyMul_eq_after_integratingBlock
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_polyMul_eq_after_integratingBlocks
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.integrateBlocks_supported
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.independent_of_local
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.integrateBlock_local
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.integrateBlocks_local
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.integrateBlocks_zero
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.integrateFiltered_local
#print axioms YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_polyMul_eq_after_integratingBlocks_of_local
