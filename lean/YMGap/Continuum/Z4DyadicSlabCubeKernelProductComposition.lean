/-
# Product composition of projected closed-cube kernels

Two independently normalized fine-support projectors compose on the exact
four-state Cartesian carrier of the odd fine cube and its time-reflected
copy.  Every retained coordinate passes the literal incidence audit.  The
product is strictly positive, row normalized, and invariant under the
corrected-slab time reflection, which constructively permutes the carrier.

For comparison the older product of complete conditional cube-channel laws
is retained.  The final section now bridges the projected raw mass itself to
genuine fine production summands and proves exact union factorization when
the two physical supports are face-disjoint and link-separated.  That last
step is intentionally conditional on geometric separation: normalization
alone cannot manufacture it.
-/

import YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
import YMGap.Continuum.Z4LinkSeparatedComponentFactorization

namespace YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition

set_option maxRecDepth 20000
set_option maxHeartbeats 7000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
open YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem nodupMapInjective {A B : Type}
    (f : A → B) (hinjective : Function.Injective f) :
    ∀ {xs : List A}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
        exact hparts.1 ((hinjective heq) ▸ hsource)
      · exact nodupMapInjective f hinjective hparts.2

/-! ## 1. Product of the globally projected fine-support laws -/

abbrev TwoClosedCubeFineSlotTarget :=
  CubeFineSlotAssignment × CubeFineSlotAssignment

def twoClosedCubeFineSlotStateSpace :
    List TwoClosedCubeFineSlotTarget :=
  cartesian closedCubeFineSlotStateSpace
    closedCubeFineSlotStateSpace

theorem mem_twoClosedCubeFineSlotStateSpace_iff
    (target : TwoClosedCubeFineSlotTarget) :
    target ∈ twoClosedCubeFineSlotStateSpace ↔
      target.1 ∈ closedCubeFineSlotStateSpace ∧
        target.2 ∈ closedCubeFineSlotStateSpace :=
  mem_cartesian_iff _ _ _

theorem twoClosedCubeFineSlotStateSpace_eq :
    twoClosedCubeFineSlotStateSpace =
      [(oddFineCubeSlotAssignment, oddFineCubeSlotAssignment),
       (oddFineCubeSlotAssignment,
        reflectedOddFineCubeSlotAssignment),
       (reflectedOddFineCubeSlotAssignment,
        oddFineCubeSlotAssignment),
       (reflectedOddFineCubeSlotAssignment,
        reflectedOddFineCubeSlotAssignment)] := by
  rw [twoClosedCubeFineSlotStateSpace,
    closedCubeFineSlotStateSpace_eq]
  rfl

theorem twoClosedCubeFineSlotStateSpace_length :
    twoClosedCubeFineSlotStateSpace.length = 4 := by
  rw [twoClosedCubeFineSlotStateSpace_eq]
  rfl

theorem twoClosedCubeFineSlotStateSpace_nodup :
    twoClosedCubeFineSlotStateSpace.Nodup := by
  exact cartesian_nodup _ _
    closedCubeFineSlotStateSpace_nodup
    closedCubeFineSlotStateSpace_nodup

/-- Every coordinate in the product carrier independently passes the literal
fine-link incidence audit. -/
theorem mem_twoClosedCubeFineSlotStateSpace_incidenceClosed
    {target : TwoClosedCubeFineSlotTarget}
    (htarget : target ∈ twoClosedCubeFineSlotStateSpace) :
    cubeFineSlotIncidenceClosedB target.1 = true ∧
      cubeFineSlotIncidenceClosedB target.2 = true := by
  have hparts :=
    (mem_twoClosedCubeFineSlotStateSpace_iff target).mp htarget
  exact ⟨mem_closedCubeFineSlotStateSpace_incidenceClosed hparts.1,
    mem_closedCubeFineSlotStateSpace_incidenceClosed hparts.2⟩

def twoClosedCubeFineSlotProductKernel
    (w : Q') (hw : (0 : Q') < w)
    (target : TwoClosedCubeFineSlotTarget) : Q' :=
  closedCubeFineSlotKernel w hw target.1 *
    closedCubeFineSlotKernel w hw target.2

theorem twoClosedCubeFineSlotProductKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w)
    (target : TwoClosedCubeFineSlotTarget) :
    (0 : Q') ≤ twoClosedCubeFineSlotProductKernel w hw target := by
  unfold twoClosedCubeFineSlotProductKernel
  exact Q'.mul_nonneg _ _
    (closedCubeFineSlotKernel_nonnegative w hw target.1)
    (closedCubeFineSlotKernel_nonnegative w hw target.2)

theorem closedCubeFineSlotKernel_pos
    (w : Q') (hw : (0 : Q') < w)
    (assignment : CubeFineSlotAssignment) :
    (0 : Q') < closedCubeFineSlotKernel w hw assignment := by
  unfold closedCubeFineSlotKernel closedCubeFineSlotRawWeight Q'.divPos
  exact Q'.mul_pos
    (compatibleCubeRawWeight_pos hw 1
      (cubeFineSlotSource assignment))
    (Q'.recipPos_pos _ _)

theorem twoClosedCubeFineSlotProductKernel_pos
    (w : Q') (hw : (0 : Q') < w)
    (target : TwoClosedCubeFineSlotTarget) :
    (0 : Q') < twoClosedCubeFineSlotProductKernel w hw target := by
  unfold twoClosedCubeFineSlotProductKernel
  exact Q'.mul_pos
    (closedCubeFineSlotKernel_pos w hw target.1)
    (closedCubeFineSlotKernel_pos w hw target.2)

theorem twoClosedCubeFineSlotProductKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) :
    listQSum (twoClosedCubeFineSlotProductKernel w hw)
        twoClosedCubeFineSlotStateSpace ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (closedCubeFineSlotKernel w hw)
        closedCubeFineSlotStateSpace *
      listQSum (closedCubeFineSlotKernel w hw)
        closedCubeFineSlotStateSpace) _ ?_ ?_
  · exact listQSum_cartesian_product
      (closedCubeFineSlotKernel w hw)
      (closedCubeFineSlotKernel w hw)
      closedCubeFineSlotStateSpace
      closedCubeFineSlotStateSpace
  · exact Q'.eqv_trans _ (1 * 1) _
      (qmul_congr
        (closedCubeFineSlotKernel_row_normalized w hw)
        (closedCubeFineSlotKernel_row_normalized w hw))
      (Q'.one_mul_eqv 1)

/-! ### Corrected-slab reflection of the projected product -/

def reflectFineFaceSlotTime : FineFaceSlot → FineFaceSlot
  | .slot0 => .slot2
  | .slot1 => .slot3
  | .slot2 => .slot0
  | .slot3 => .slot1

theorem reflectFineFaceSlotTime_involutive (slot : FineFaceSlot) :
    reflectFineFaceSlotTime (reflectFineFaceSlotTime slot) = slot := by
  cases slot <;> rfl

def reflectCubeFineSlotAssignmentTime :
    CubeFineSlotAssignment → CubeFineSlotAssignment
  | (bottom, (top, (front, (back, (left, right))))) =>
      (reflectFineFaceSlotTime bottom,
        (reflectFineFaceSlotTime top,
          (reflectFineFaceSlotTime front,
            (reflectFineFaceSlotTime back,
              (reflectFineFaceSlotTime left,
                reflectFineFaceSlotTime right)))))

theorem reflectCubeFineSlotAssignmentTime_involutive
    (assignment : CubeFineSlotAssignment) :
    reflectCubeFineSlotAssignmentTime
        (reflectCubeFineSlotAssignmentTime assignment) = assignment := by
  rcases assignment with
    ⟨bottom, ⟨top, ⟨front, ⟨back, ⟨left, right⟩⟩⟩⟩⟩
  simp only [reflectCubeFineSlotAssignmentTime,
    reflectFineFaceSlotTime_involutive]

theorem reflectCubeFineSlotAssignmentTime_odd :
    reflectCubeFineSlotAssignmentTime oddFineCubeSlotAssignment =
      reflectedOddFineCubeSlotAssignment := by
  rfl

theorem reflectCubeFineSlotAssignmentTime_reflected :
    reflectCubeFineSlotAssignmentTime
        reflectedOddFineCubeSlotAssignment =
      oddFineCubeSlotAssignment := by
  rfl

theorem reflectCubeFineSlotAssignmentTime_mem_closed
    {assignment : CubeFineSlotAssignment}
    (hassignment : assignment ∈ closedCubeFineSlotStateSpace) :
    reflectCubeFineSlotAssignmentTime assignment ∈
      closedCubeFineSlotStateSpace := by
  rw [closedCubeFineSlotStateSpace_eq] at hassignment ⊢
  rcases List.mem_cons.mp hassignment with hodd | hreflected
  · subst assignment
    rw [reflectCubeFineSlotAssignmentTime_odd]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · have heq := List.mem_singleton.mp hreflected
    subst assignment
    rw [reflectCubeFineSlotAssignmentTime_reflected]
    exact List.mem_cons_self

def reflectTwoClosedCubeFineSlotTarget
    (target : TwoClosedCubeFineSlotTarget) :
    TwoClosedCubeFineSlotTarget :=
  (reflectCubeFineSlotAssignmentTime target.1,
    reflectCubeFineSlotAssignmentTime target.2)

theorem reflectTwoClosedCubeFineSlotTarget_involutive
    (target : TwoClosedCubeFineSlotTarget) :
    reflectTwoClosedCubeFineSlotTarget
        (reflectTwoClosedCubeFineSlotTarget target) = target := by
  apply Prod.ext
  · exact reflectCubeFineSlotAssignmentTime_involutive target.1
  · exact reflectCubeFineSlotAssignmentTime_involutive target.2

theorem reflectTwoClosedCubeFineSlotTarget_mem
    {target : TwoClosedCubeFineSlotTarget}
    (htarget : target ∈ twoClosedCubeFineSlotStateSpace) :
    reflectTwoClosedCubeFineSlotTarget target ∈
      twoClosedCubeFineSlotStateSpace := by
  have hparts :=
    (mem_twoClosedCubeFineSlotStateSpace_iff target).mp htarget
  apply (mem_twoClosedCubeFineSlotStateSpace_iff _).mpr
  exact ⟨reflectCubeFineSlotAssignmentTime_mem_closed hparts.1,
    reflectCubeFineSlotAssignmentTime_mem_closed hparts.2⟩

private theorem reflectTwoClosedCubeFineSlotTarget_injective :
    Function.Injective reflectTwoClosedCubeFineSlotTarget := by
  intro left right heq
  exact (reflectTwoClosedCubeFineSlotTarget_involutive left).symm.trans
    ((congrArg reflectTwoClosedCubeFineSlotTarget heq).trans
      (reflectTwoClosedCubeFineSlotTarget_involutive right))

theorem reflectTwoClosedCubeFineSlotStateSpace_perm :
    (twoClosedCubeFineSlotStateSpace.map
      reflectTwoClosedCubeFineSlotTarget).Perm
        twoClosedCubeFineSlotStateSpace := by
  letI : DecidableEq CubeFineSlotAssignment := inferInstance
  letI : DecidableEq TwoClosedCubeFineSlotTarget := inferInstance
  apply perm_of_nodup_mem_iff
  · exact nodupMapInjective
      reflectTwoClosedCubeFineSlotTarget
      reflectTwoClosedCubeFineSlotTarget_injective
      twoClosedCubeFineSlotStateSpace_nodup
  · exact twoClosedCubeFineSlotStateSpace_nodup
  · intro target
    constructor
    · intro htarget
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
      rw [← heq]
      exact reflectTwoClosedCubeFineSlotTarget_mem hsource
    · intro htarget
      apply List.mem_map.mpr
      exact ⟨reflectTwoClosedCubeFineSlotTarget target,
        reflectTwoClosedCubeFineSlotTarget_mem htarget,
        reflectTwoClosedCubeFineSlotTarget_involutive target⟩

/-! The compatible six-face raw mass depends only on the common total one,
not on which of the four one-fundamental slots realizes it. -/

private theorem compatibleTotalOneCubeFaceRawWeight_eqv_pow_six
    (w : Q') (source : CubeStretchedCompatibleSource 1)
    (htotal : source.commonTotal = 1) :
    cubeFaceRawProduct w 1 source (compatibleCubeTarget source) ≈
      (coeffW w 1) ^ 6 := by
  unfold cubeFaceRawProduct
  change
    packetPairChannelRawWeight w (source.packet .bottomXY).val
        (stretchedPairChannelState (source.packet .bottomXY).val) *
      (packetPairChannelRawWeight w (source.packet .topXY).val
          (stretchedPairChannelState (source.packet .topXY).val) *
        (packetPairChannelRawWeight w (source.packet .frontXZ).val
            (stretchedPairChannelState (source.packet .frontXZ).val) *
          (packetPairChannelRawWeight w (source.packet .backXZ).val
              (stretchedPairChannelState (source.packet .backXZ).val) *
            (packetPairChannelRawWeight w (source.packet .leftYZ).val
                (stretchedPairChannelState (source.packet .leftYZ).val) *
              (packetPairChannelRawWeight w (source.packet .rightYZ).val
                  (stretchedPairChannelState
                    (source.packet .rightYZ).val) * 1))))) ≈
      (coeffW w 1) ^ 6
  have hbottom := stretchedPairChannelRawWeight_eqv_coarseCoefficient
    w (source.packet .bottomXY).val
  have htop := stretchedPairChannelRawWeight_eqv_coarseCoefficient
    w (source.packet .topXY).val
  have hfront := stretchedPairChannelRawWeight_eqv_coarseCoefficient
    w (source.packet .frontXZ).val
  have hback := stretchedPairChannelRawWeight_eqv_coarseCoefficient
    w (source.packet .backXZ).val
  have hleft := stretchedPairChannelRawWeight_eqv_coarseCoefficient
    w (source.packet .leftYZ).val
  have hright := stretchedPairChannelRawWeight_eqv_coarseCoefficient
    w (source.packet .rightYZ).val
  rw [source.total_eq .bottomXY, htotal] at hbottom
  rw [source.total_eq .topXY, htotal] at htop
  rw [source.total_eq .frontXZ, htotal] at hfront
  rw [source.total_eq .backXZ, htotal] at hback
  rw [source.total_eq .leftYZ, htotal] at hleft
  rw [source.total_eq .rightYZ, htotal] at hright
  rw [Q'.pow_succ, Q'.pow_succ, Q'.pow_succ,
    Q'.pow_succ, Q'.pow_succ, Q'.pow_succ, Q'.pow_zero]
  exact qmul_congr hbottom
    (qmul_congr htop
      (qmul_congr hfront
        (qmul_congr hback
          (qmul_congr hleft
            (qmul_congr hright (Q'.eqv_refl 1))))))

theorem closedCubeFineSlotRawWeight_eqv_pow_six
    (w : Q') (assignment : CubeFineSlotAssignment) :
    closedCubeFineSlotRawWeight w assignment ≈
      (coeffW w 1) ^ 6 := by
  unfold closedCubeFineSlotRawWeight cubeCoupledRawWeight
  exact Q'.eqv_trans _ ((coeffW w 1) ^ 6 * 1) _
    (qmul_congr
      (compatibleTotalOneCubeFaceRawWeight_eqv_pow_six w
        (cubeFineSlotSource assignment) rfl)
      (compatibleCubeProductionLinkProduct_eqv_one
        (cubeFineSlotSource assignment)))
    (Q'.mul_one_eqv _)

theorem closedCubeFineSlotKernel_reflection_invariant
    (w : Q') (hw : (0 : Q') < w)
    (assignment : CubeFineSlotAssignment) :
    closedCubeFineSlotKernel w hw
        (reflectCubeFineSlotAssignmentTime assignment) ≈
      closedCubeFineSlotKernel w hw assignment := by
  unfold closedCubeFineSlotKernel Q'.divPos
  apply Q'.mul_eqv_congr_right
  exact Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
    (closedCubeFineSlotRawWeight_eqv_pow_six w _)
    (Q'.eqv_symm
      (closedCubeFineSlotRawWeight_eqv_pow_six w assignment))

theorem twoClosedCubeFineSlotProductKernel_reflection_invariant
    (w : Q') (hw : (0 : Q') < w)
    (target : TwoClosedCubeFineSlotTarget) :
    twoClosedCubeFineSlotProductKernel w hw
        (reflectTwoClosedCubeFineSlotTarget target) ≈
      twoClosedCubeFineSlotProductKernel w hw target := by
  unfold twoClosedCubeFineSlotProductKernel
    reflectTwoClosedCubeFineSlotTarget
  exact qmul_congr
    (closedCubeFineSlotKernel_reflection_invariant w hw target.1)
    (closedCubeFineSlotKernel_reflection_invariant w hw target.2)

/-! ## 2. Duplicate-free two-cube conditional target carrier -/

abbrev TwoCubeTarget := CubePairChannelState × CubePairChannelState

def twoCubeTargetStateSpace (cutoff : Nat) : List TwoCubeTarget :=
  cartesian (cubePairChannelStateSpace cutoff)
    (cubePairChannelStateSpace cutoff)

theorem mem_twoCubeTargetStateSpace_iff
    (cutoff : Nat) (target : TwoCubeTarget) :
    target ∈ twoCubeTargetStateSpace cutoff ↔
      target.1 ∈ cubePairChannelStateSpace cutoff ∧
        target.2 ∈ cubePairChannelStateSpace cutoff :=
  mem_cartesian_iff _ _ _

theorem twoCubeTargetStateSpace_nodup (cutoff : Nat) :
    (twoCubeTargetStateSpace cutoff).Nodup := by
  unfold twoCubeTargetStateSpace
  exact cartesian_nodup _ _
    (cubePairChannelStateSpace_nodup cutoff)
    (cubePairChannelStateSpace_nodup cutoff)

/-! ## 3. Product kernel and exact row normalization -/

abbrev TwoCubeSource (cutoff : Nat) :=
  CubeStretchedCompatibleSource cutoff ×
    CubeStretchedCompatibleSource cutoff

def twoCubeProductKernel
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : TwoCubeSource cutoff) (target : TwoCubeTarget) : Q' :=
  cubeCoupledConditionalKernel w hw cutoff source.1 target.1 *
    cubeCoupledConditionalKernel w hw cutoff source.2 target.2

theorem twoCubeProductKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : TwoCubeSource cutoff) (target : TwoCubeTarget) :
    (0 : Q') ≤ twoCubeProductKernel w hw cutoff source target := by
  unfold twoCubeProductKernel
  exact Q'.mul_nonneg _ _
    (cubeCoupledConditionalKernel_nonnegative
      w hw cutoff source.1 target.1)
    (cubeCoupledConditionalKernel_nonnegative
      w hw cutoff source.2 target.2)

theorem twoCubeProductKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : TwoCubeSource cutoff) :
    listQSum (twoCubeProductKernel w hw cutoff source)
        (twoCubeTargetStateSpace cutoff) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
        (cubeCoupledConditionalKernel w hw cutoff source.1)
        (cubePairChannelStateSpace cutoff) *
      listQSum
        (cubeCoupledConditionalKernel w hw cutoff source.2)
        (cubePairChannelStateSpace cutoff)) _ ?_ ?_
  · exact listQSum_cartesian_product
      (cubeCoupledConditionalKernel w hw cutoff source.1)
      (cubeCoupledConditionalKernel w hw cutoff source.2)
      (cubePairChannelStateSpace cutoff)
      (cubePairChannelStateSpace cutoff)
  · exact Q'.eqv_trans _ (1 * 1) _
      (qmul_congr
        (cubeCoupledConditionalKernel_row_normalized
          w hw cutoff source.1)
        (cubeCoupledConditionalKernel_row_normalized
          w hw cutoff source.2))
      (Q'.one_mul_eqv 1)

theorem twoCubeCompatibleTarget_mem
    {cutoff : Nat} (source : TwoCubeSource cutoff) :
    (compatibleCubeTarget source.1,
      compatibleCubeTarget source.2) ∈
        twoCubeTargetStateSpace cutoff := by
  apply (mem_twoCubeTargetStateSpace_iff cutoff _).mpr
  exact ⟨compatibleCubeTarget_mem source.1,
    compatibleCubeTarget_mem source.2⟩

theorem twoCubeProductKernel_compatibleTarget_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : TwoCubeSource cutoff) :
    (0 : Q') < twoCubeProductKernel w hw cutoff source
      (compatibleCubeTarget source.1,
        compatibleCubeTarget source.2) := by
  unfold twoCubeProductKernel cubeCoupledConditionalKernel Q'.divPos
  exact Q'.mul_pos
    (Q'.mul_pos
      (compatibleCubeRawWeight_pos hw cutoff source.1)
      (Q'.recipPos_pos _ _))
    (Q'.mul_pos
      (compatibleCubeRawWeight_pos hw cutoff source.2)
      (Q'.recipPos_pos _ _))

/-! ## 4. Independent and reflection-paired cubes -/

abbrev TwoCubeReflectionPlanes :=
  CubeReflectionPlanes × CubeReflectionPlanes

def reflectTwoCubeSource
    (cutoff : Nat) (planes : TwoCubeReflectionPlanes)
    (source : TwoCubeSource cutoff) : TwoCubeSource cutoff :=
  (reflectCubeCompatibleSource cutoff planes.1 source.1,
    reflectCubeCompatibleSource cutoff planes.2 source.2)

def reflectTwoCubeTarget
    (planes : TwoCubeReflectionPlanes)
    (target : TwoCubeTarget) : TwoCubeTarget :=
  (reflectCubeTarget planes.1 target.1,
    reflectCubeTarget planes.2 target.2)

theorem reflectTwoCubeTarget_involutive
    (planes : TwoCubeReflectionPlanes) (target : TwoCubeTarget) :
    reflectTwoCubeTarget planes
        (reflectTwoCubeTarget planes target) = target := by
  apply Prod.ext
  · exact reflectCubeTarget_involutive planes.1 target.1
  · exact reflectCubeTarget_involutive planes.2 target.2

private theorem reflectTwoCubeTarget_injective
    (planes : TwoCubeReflectionPlanes) :
    Function.Injective (reflectTwoCubeTarget planes) := by
  intro left right heq
  exact (reflectTwoCubeTarget_involutive planes left).symm.trans
    ((congrArg (reflectTwoCubeTarget planes) heq).trans
      (reflectTwoCubeTarget_involutive planes right))

theorem reflectTwoCubeTarget_mem
    {cutoff : Nat} {target : TwoCubeTarget}
    (htarget : target ∈ twoCubeTargetStateSpace cutoff)
    (planes : TwoCubeReflectionPlanes) :
    reflectTwoCubeTarget planes target ∈
      twoCubeTargetStateSpace cutoff := by
  have hparts :=
    (mem_twoCubeTargetStateSpace_iff cutoff target).mp htarget
  apply (mem_twoCubeTargetStateSpace_iff cutoff _).mpr
  exact ⟨reflectCubeTarget_mem hparts.1 planes.1,
    reflectCubeTarget_mem hparts.2 planes.2⟩

theorem reflectTwoCubeTargetStateSpace_perm
    (cutoff : Nat) (planes : TwoCubeReflectionPlanes) :
    ((twoCubeTargetStateSpace cutoff).map
      (reflectTwoCubeTarget planes)).Perm
        (twoCubeTargetStateSpace cutoff) := by
  letI : DecidableEq CubePairChannelState :=
    @instDecidableEqProd PairChannelState
      (PairChannelState ×
        (PairChannelState ×
          (PairChannelState ×
            (PairChannelState × PairChannelState))))
      (inferInstance)
      (@instDecidableEqProd PairChannelState
        (PairChannelState ×
          (PairChannelState ×
            (PairChannelState × PairChannelState)))
        (inferInstance)
        (@instDecidableEqProd PairChannelState
          (PairChannelState × (PairChannelState × PairChannelState))
          (inferInstance)
          (@instDecidableEqProd PairChannelState
            (PairChannelState × PairChannelState)
            (inferInstance)
            (@instDecidableEqProd PairChannelState PairChannelState
              (inferInstance) (inferInstance)))))
  letI : DecidableEq TwoCubeTarget := inferInstance
  apply perm_of_nodup_mem_iff
  · exact nodupMapInjective
      (reflectTwoCubeTarget planes)
      (reflectTwoCubeTarget_injective planes)
      (twoCubeTargetStateSpace_nodup cutoff)
  · exact twoCubeTargetStateSpace_nodup cutoff
  · intro target
    constructor
    · intro htarget
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
      rw [← heq]
      exact reflectTwoCubeTarget_mem hsource planes
    · intro htarget
      apply List.mem_map.mpr
      exact ⟨reflectTwoCubeTarget planes target,
        reflectTwoCubeTarget_mem htarget planes,
        reflectTwoCubeTarget_involutive planes target⟩

theorem twoCubeProductKernel_reflection_equivariant
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (planes : TwoCubeReflectionPlanes)
    (source : TwoCubeSource cutoff) (target : TwoCubeTarget) :
    twoCubeProductKernel w hw cutoff
        (reflectTwoCubeSource cutoff planes source)
        (reflectTwoCubeTarget planes target) ≈
      twoCubeProductKernel w hw cutoff source target := by
  unfold twoCubeProductKernel reflectTwoCubeSource reflectTwoCubeTarget
  exact qmul_congr
    (cubeCoupledConditionalKernel_reflection_equivariant
      w hw cutoff planes.1 source.1 target.1)
    (cubeCoupledConditionalKernel_reflection_equivariant
      w hw cutoff planes.2 source.2 target.2)

/-! ## 5. Exact physical composition interface -/

structure ProjectedFineCubeSummandBridge (w : Q') (n : Nat) where
  assignment : CubeFineSlotAssignment
  assignment_mem : assignment ∈ closedCubeFineSlotStateSpace
  physical : EdgeLabelling
  physical_mem : physical ∈ explicitPhysicalLabellings 1 n
  raw_eqv : closedCubeFineSlotRawWeight w assignment ≈
    parametricLocalizedSpinFoamWeight w n physical

/-- Concrete non-vacuity of the repair interface: the globally closed odd
fine cube supplies an actual bridge, not merely a coarse surrogate. -/
def oddFineCubeProjectedSummandBridge (w : Q') :
    ProjectedFineCubeSummandBridge w 4 where
  assignment := oddFineCubeSlotAssignment
  assignment_mem := oddFineCubeSlotAssignment_mem_closed
  physical := componentLabel oddFineUnitCubeSupportIds
  physical_mem := by
    simpa [dyadicParityFineStateSpace] using
      oddFineUnitCubeLabel_mem_fineStateSpace
  raw_eqv := by
    exact Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
      (closedCubeFineSlotRawWeight_eqv_pow_six w
        oddFineCubeSlotAssignment)
      (Q'.eqv_trans _
        (cubeCoupledRawWeight w 1 oddFineCubeCompatibleSource
          (compatibleCubeTarget oddFineCubeCompatibleSource)) _
        (Q'.eqv_symm (oddFineCubeRawWeight_eqv_pow_six w))
        (oddFineCubeRawWeight_eqv_fineProductionSummand w))

structure LinkSeparatedProjectedFineCubePair (w : Q') (n : Nat) where
  left : ProjectedFineCubeSummandBridge w n
  right : ProjectedFineCubeSummandBridge w n
  faceDisjoint : FaceDisjoint n left.physical right.physical
  linkSeparated : LinkSeparated n left.physical right.physical

def bridgedProjectedTwoCubeRawProduct
    {w : Q'} {n : Nat}
    (pair : LinkSeparatedProjectedFineCubePair w n) : Q' :=
  closedCubeFineSlotRawWeight w pair.left.assignment *
    closedCubeFineSlotRawWeight w pair.right.assignment

/-- For genuinely bridged, disjoint cubes the algebraic product is exactly
the actual production summand of the union.  This is the precise point where
geometric disjointness enters; the unconditional normalized product theorem
above does not assert it. -/
theorem bridgedProjectedTwoCubeRawProduct_eqv_unionProductionSummand
    {w : Q'} {n : Nat}
    (pair : LinkSeparatedProjectedFineCubePair w n) :
    bridgedProjectedTwoCubeRawProduct pair ≈
      parametricLocalizedSpinFoamWeight w n
        (binaryUnionLabel pair.left.physical pair.right.physical) := by
  exact Q'.eqv_trans _
    (parametricLocalizedSpinFoamWeight w n pair.left.physical *
      parametricLocalizedSpinFoamWeight w n pair.right.physical) _
    (qmul_congr pair.left.raw_eqv pair.right.raw_eqv)
    (Q'.eqv_symm
      (parametricLocalizedSpinFoamWeight_union_factor
        pair.left.physical_mem pair.right.physical_mem
        pair.faceDisjoint pair.linkSeparated))

/-! ## Dependency gates -/

#print axioms twoClosedCubeFineSlotStateSpace_eq
#print axioms twoClosedCubeFineSlotStateSpace_nodup
#print axioms mem_twoClosedCubeFineSlotStateSpace_incidenceClosed
#print axioms twoClosedCubeFineSlotProductKernel_nonnegative
#print axioms closedCubeFineSlotKernel_pos
#print axioms twoClosedCubeFineSlotProductKernel_pos
#print axioms twoClosedCubeFineSlotProductKernel_row_normalized
#print axioms reflectTwoClosedCubeFineSlotTarget_involutive
#print axioms reflectTwoClosedCubeFineSlotStateSpace_perm
#print axioms closedCubeFineSlotRawWeight_eqv_pow_six
#print axioms closedCubeFineSlotKernel_reflection_invariant
#print axioms twoClosedCubeFineSlotProductKernel_reflection_invariant
#print axioms twoCubeTargetStateSpace_nodup
#print axioms twoCubeProductKernel_nonnegative
#print axioms twoCubeProductKernel_row_normalized
#print axioms twoCubeCompatibleTarget_mem
#print axioms twoCubeProductKernel_compatibleTarget_pos
#print axioms reflectTwoCubeTarget_involutive
#print axioms reflectTwoCubeTargetStateSpace_perm
#print axioms twoCubeProductKernel_reflection_equivariant
#print axioms oddFineCubeProjectedSummandBridge
#print axioms bridgedProjectedTwoCubeRawProduct_eqv_unionProductionSummand

end YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition
