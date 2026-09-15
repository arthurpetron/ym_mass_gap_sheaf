/-
# The actual integer-slice boundary factors are fixed by reflection

Every fixed link is spatial and is literally fixed by the existing even-slab
link involution. Thus every boundary-local polynomial is fixed by the actual
orientation-correct polynomial reflection, up to its existing common padding.
This discharges the finite boundary-reflection input of site Haar factorization;
it is not supplied as an analytic hypothesis.

The resulting square identity is finite and unweighted. The original full
heat action, its thermodynamic one-step form, transfer range and continuum
construction are not identified by this result.
-/

import YMGap.Continuum.BF4ExactSlabSiteHaarFactorization

namespace YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

theorem fixed_link {radius : Nat} {link : Z4Link}
    (h : adjacentEvenLinkSide radius link = .fixed) :
    timeReflectLink (adjacentEvenExtent radius) link = link ∧ link.2 ≠ .x3 := by
  obtain ⟨⟨a,b,c,t⟩,dir⟩ := link
  cases dir <;>
    simp only [adjacentEvenLinkSide, adjacentEvenSpatialSide, adjacentEvenTemporalSide] at h
  all_goals split at h
  all_goals first | contradiction | skip
  all_goals split at h
  all_goals first | contradiction | skip
  all_goals rename_i ht
  all_goals subst t
  all_goals
    have hc : adjacentEvenExtent radius - adjacentEvenCenter radius = adjacentEvenCenter radius := by
      unfold adjacentEvenExtent centralExtent adjacentEvenCenter
      omega
  all_goals constructor
  all_goals simp only [timeReflectLink, hc]
  all_goals intro he; cases he

theorem fixed_block {radius b : Nat} (hb : b < blockCount radius) (h : blockSide radius b = .fixed) :
    correctedSlabLinkReflectBlock (adjacentEvenExtent radius) b = b := by
  have hm := List.mem_range.mpr hb
  apply correctedSlabLinkAt_injective_on_physical (correctedSlabLinkReflectBlock_physical hm) hm
  rw [correctedSlabLinkAt_reflectBlock hm]
  exact (fixed_link h).1

private theorem fixed_reindex_exponent {radius : Nat} {m : List Nat}
    (hm : ∀ b, b < blockCount radius → blockSide radius b ≠ .fixed → BlockZero m b)
    {i : Nat} (hi : i < 4 * blockCount radius) :
    exponentAt (reindexQuaternionExponents (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius)) m) i =
      exponentAt m i := by
  rw [exponentAt_reindexQuaternionExponents
    (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius)) m hi]
  have hblock : i / 4 < blockCount radius := by omega
  have hcomponent : i % 4 < 4 := Nat.mod_lt _ (by decide)
  by_cases h : blockSide radius (i/4) = .fixed
  · change exponentAt m (4 * correctedSlabLinkReflectBlock (adjacentEvenExtent radius) (i/4) + i%4) = _
    rw [fixed_block hblock h, show 4*(i/4)+i%4=i by omega]
  · have hr : blockSide radius (correctedSlabLinkReflectBlock (adjacentEvenExtent radius) (i/4)) ≠ .fixed := by
      rw [blockSide_reflection radius hblock]
      cases hs : blockSide radius (i/4) <;> intro he
      · cases he
      · exact h hs
      · cases he
    have hb := (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius)).map_lt (i/4) hblock
    rw [hm _ hb hr _ hcomponent, ← show 4*(i/4)+i%4=i by omega,
      hm _ hblock h _ hcomponent]

private theorem reindex_fixed {radius : Nat} : ∀ p : RatPoly, Local radius .fixed p →
    QuaternionPrefixPolynomialEqv (blockCount radius)
      (reindexQuaternionPolynomial (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius)) p) p
  | [], _ => .nil
  | t :: p, hp => .cons
      ⟨Q'.eqv_refl _, fun _ hi => fixed_reindex_exponent (hp t List.mem_cons_self) hi⟩
      (reindex_fixed p (fun s hs => hp s (List.mem_cons_of_mem t hs)))

private theorem parity_zero (coordinates : Nat) (selected : Nat → Bool) (m : List Nat)
    (hm : ∀ i, i < coordinates → selected i = true → exponentAt m i = 0) :
    selectedExponentParity coordinates selected m = false := by
  unfold selectedExponentParity
  have step : ∀ xs : List Nat,
      (∀ i, i ∈ xs → selected i = true → exponentAt m i = 0) →
      xs.foldl (fun parity i => if selected i then xor parity (decide (exponentAt m i % 2 = 1)) else parity) false = false := by
    intro xs hx
    induction xs with
    | nil => rfl
    | cons i xs ih =>
        simp only [List.foldl_cons]
        by_cases hs : selected i = true
        · rw [if_pos hs, hx i List.mem_cons_self hs]
          exact ih (fun j hj => hx j (List.mem_cons_of_mem i hj))
        · rw [if_neg hs]
          exact ih (fun j hj => hx j (List.mem_cons_of_mem i hj))
  exact step _ (fun i hi => hm i (List.mem_range.mp hi))

private theorem sign_fixed {radius : Nat} : ∀ p : RatPoly, Local radius .fixed p →
    signSelectedPolynomial (4 * blockCount radius) (correctedSlabTimeVectorCoordinate (adjacentEvenExtent radius)) p = p
  | [], _ => rfl
  | t :: p, hp => by
      have hz : selectedExponentParity (4 * blockCount radius)
          (correctedSlabTimeVectorCoordinate (adjacentEvenExtent radius)) t.1 = false := by
        apply parity_zero
        intro i hi hs
        have hd : (correctedSlabLinkAt (adjacentEvenExtent radius) (i/4)).2 = .x3 :=
          (of_decide_eq_true hs).1
        have hn : blockSide radius (i/4) ≠ .fixed := fun h => (fixed_link h).2 hd
        have he := hp t List.mem_cons_self (i/4) (by omega) hn (i%4) (Nat.mod_lt _ (by decide))
        rw [show 4*(i/4)+i%4=i by omega] at he
        exact he
      change signSelectedTerm _ _ t :: signSelectedPolynomial _ _ p = t :: p
      rw [sign_fixed p (fun s hs => hp s (List.mem_cons_of_mem t hs))]
      unfold signSelectedTerm
      rw [hz]
      rfl

/-- No separate reflection hypothesis is needed for a boundary-local polynomial. -/
theorem boundary_reflection {radius : Nat} {p : RatPoly} (hp : Local radius .fixed p) :
    ReflectionImage (adjacentEvenExtent radius) p p := by
  have h := (reindex_fixed p hp).signSelected (correctedSlabTimeVectorCoordinate (adjacentEvenExtent radius))
  rw [sign_fixed p hp] at h
  exact PaddedPolynomialCoeffEqv.of_prefix h

/-- Finite conditional square using only the actual geometric locality data. -/
theorem site_reflected_square {A : Type} (radius : Nat) (lower boundary : A → RatPoly)
    (hl : ∀ a, SupportedQuaternionBlocks (blockCount radius) (lower a))
    (hb : ∀ a, SupportedQuaternionBlocks (blockCount radius) (boundary a))
    (ll : ∀ a, Local radius .lower (lower a)) (lb : ∀ a, Local radius .fixed (boundary a)) (xs : List A) :
    quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lowerSum lower boundary xs))
        (lowerSum lower boundary xs)) ≈
      quaternionHaar (blockCount radius)
        (polyMul (boundarySum radius lower boundary xs) (boundarySum radius lower boundary xs)) :=
  reflected_square radius lower boundary hl hb ll lb (fun a => boundary_reflection (lb a)) xs

theorem site_reflected_nonnegative {A : Type} (radius : Nat) (lower boundary : A → RatPoly)
    (hl : ∀ a, SupportedQuaternionBlocks (blockCount radius) (lower a))
    (hb : ∀ a, SupportedQuaternionBlocks (blockCount radius) (boundary a))
    (ll : ∀ a, Local radius .lower (lower a)) (lb : ∀ a, Local radius .fixed (boundary a)) (xs : List A) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lowerSum lower boundary xs))
        (lowerSum lower boundary xs)) :=
  reflected_nonnegative radius lower boundary hl hb ll lb (fun a => boundary_reflection (lb a)) xs

end YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection

#print axioms YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection.fixed_link
#print axioms YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection.fixed_block
#print axioms YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection.boundary_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection.site_reflected_square
#print axioms YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection.site_reflected_nonnegative
