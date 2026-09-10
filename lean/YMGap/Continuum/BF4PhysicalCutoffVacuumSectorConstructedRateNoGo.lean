/-
# The global path-ceiling constructed rate is not cutoff-uniform

At half-extent zero, the cutoff-`K` canonical vacuum sector contains `K`
distinct excited all-spin cube states.  The global path ceiling sums a
nonnegative amplification scale over every ordered pair in the sector.  Each
vacuum-to-excited pair has distinct endpoints, hence its canonical positive
path has amplification scale at least one.  Therefore the global ceiling is
at least `K`.

The persistent positive-edge floor used by the constructed fixed-base rate is
at most one: it lies below a positive pulled kernel entry, that entry lies
below its pulled row mass, and the row mass is at most one.  Thus the explicit
rate

  pathCeiling / (pathCeiling + floor)

converges to one along the expanding spin-cube ray.  No single rational
`q < 1` can bound these constructed rates at every cutoff.

This rules out the compiler based on one global all-pairs path ceiling and one
global positive-edge floor.  It does not rule out a localized posterior
Dirichlet estimate, capacity-weighted routing, a multiscale Poincare estimate,
or a direct operator proof.  No spectral gap, continuum theory, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorUniformFloorPathRate
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
import YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo

set_option maxRecDepth 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

private theorem listQSum_one_local {A : Type} :
    ∀ items : List A,
      listQSum (fun _item => (1 : Q')) items ≈
        Q'.ofNat items.length
  | [] => Q'.eqv_refl 0
  | _first :: rest => by
      refine Q'.eqv_trans _
        ((1 : Q') + Q'.ofNat rest.length) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ _ (listQSum_one_local rest)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length + 1) _
        (Q'.add_comm_eqv 1 (Q'.ofNat rest.length)) ?_
      exact Q'.eqv_symm (Q'.ofNat_add_eqv rest.length 1)

private theorem listQSum_nonnegative_on_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      (0 : Q') ≤ listQSum value items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hvalue =>
      Q'.zero_le_add _ _
        (hvalue head List.mem_cons_self)
        (listQSum_nonnegative_on_local value tail
          (fun item hitem =>
            hvalue item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {target : A}, target ∈ items →
      value target ≤ listQSum value items
  | [], _, htarget => False.elim (List.not_mem_nil htarget)
  | head :: tail, target, htarget => by
      rcases List.mem_cons.mp htarget with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on_local value tail
            (fun item _hitem => hvalue item))
      · exact Q'.le_trans' _ _ _
          (listQSum_member_le_nonnegative_local value hvalue tail htail)
          (Q'.le_trans' _ _ _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head) (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv (listQSum value tail) (value head))))

/-! ## 1. The all-pairs ceiling grows along the SU(2) spin-cube ray -/

theorem amplificationScale_one_le_of_ne
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State}
    (path : PositiveKernelChainIn kernel support first last)
    (hne : first ≠ last) :
    (1 : Q') ≤
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
        path := by
  cases path with
  | refl state => exact False.elim (hne rfl)
  | step positive nextMem rest =>
      have hrest : (0 : Q') ≤
          BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
            rest :=
        BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale_nonnegative
          rest
      have hone : (1 : Q') ≤
          1 +
            BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
              rest :=
        Q'.add_le_self_of_nonneg 1 _ hrest
      exact Q'.le_trans' _ _ _ hone
        (Q'.add_le_self_of_nonneg _ _
          (Q'.zero_le_add _ _ (by decide) hrest))

theorem cutoff_le_centralPhysicalFiniteVacuumSectorPathCeiling
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    Q'.ofNat K ≤
      centralPhysicalFiniteVacuumSectorPathCeiling
        w (Q'.le_of_lt hw) K 0 := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let source := (List.range K).attach
  let zeroEntry : {index // index ∈ states} :=
    ⟨0, zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0⟩
  let encode : {offset // offset ∈ List.range K} →
      {index // index ∈ states} × {index // index ∈ states} :=
    fun offset =>
      (zeroEntry,
        ⟨centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset.val,
          centralLowerSpinCubeIndex_mem_vacuumSector hw
            (by
              have hoffset : offset.val < K :=
                List.mem_range.mp offset.property
              omega)⟩)
  let target := cartesian states.attach states.attach
  have hsum :
      listQSum (fun _item : {offset // offset ∈ List.range K} => (1 : Q'))
          source ≤
        centralPhysicalFiniteVacuumSectorPathScaleSum
          w (Q'.le_of_lt hw) K 0 := by
    unfold centralPhysicalFiniteVacuumSectorPathScaleSum
    apply listQSum_le_of_injective_nodup
      source target
      (fun _item : {offset // offset ∈ List.range K} => (1 : Q'))
      (centralPhysicalFiniteVacuumSectorPathScale
        w (Q'.le_of_lt hw) K 0)
      encode
    · exact attach_nodup_of_nodup (List.range K) (rangeNodupLocal K)
    · exact cartesian_nodup states.attach states.attach
        (attach_nodup_of_nodup states
          (centralPhysicalFiniteVacuumSectorIndices_nodup
            w (Q'.le_of_lt hw) K 0))
        (attach_nodup_of_nodup states
          (centralPhysicalFiniteVacuumSectorIndices_nodup
            w (Q'.le_of_lt hw) K 0))
    · intro offset _hoffset
      apply (mem_cartesian_iff states.attach states.attach (encode offset)).mpr
      exact ⟨List.mem_attach states zeroEntry,
        List.mem_attach states (encode offset).2⟩
    · intro left _hleft right _hright heq
      apply Subtype.ext
      apply centralLowerExcitedSpinCubeIndex_injective_on hw
      · exact List.mem_range.mp left.property
      · exact List.mem_range.mp right.property
      · exact congrArg (fun pair => pair.2.val) heq
    · intro offset _hoffset
      unfold centralPhysicalFiniteVacuumSectorPathScale
      apply amplificationScale_one_le_of_ne
      intro hzero
      exact centralLowerExcitedSpinCubeIndex_ne_zero hw
        (List.mem_range.mp offset.property) hzero.symm
    · intro pair _hpair
      exact centralPhysicalFiniteVacuumSectorPathScale_nonnegative
        w (Q'.le_of_lt hw) K 0 pair
  have hsource : Q'.ofNat K ≤
      listQSum (fun _item : {offset // offset ∈ List.range K} => (1 : Q'))
        source := by
    apply Q'.le_of_eqv
    refine Q'.eqv_trans _ (Q'.ofNat source.length) _ ?_ ?_
    · unfold source
      simp only [List.length_attach, List.length_range]
      exact Q'.eqv_refl _
    · exact Q'.eqv_symm (listQSum_one_local source)
  have hKsum : Q'.ofNat K ≤
      centralPhysicalFiniteVacuumSectorPathScaleSum
        w (Q'.le_of_lt hw) K 0 :=
    Q'.le_trans' _ _ _ hsource hsum
  have hsumCeiling :
      centralPhysicalFiniteVacuumSectorPathScaleSum
          w (Q'.le_of_lt hw) K 0 ≤
        centralPhysicalFiniteVacuumSectorPathCeiling
          w (Q'.le_of_lt hw) K 0 := by
    unfold centralPhysicalFiniteVacuumSectorPathCeiling
    have h := Q'.add_le_add_right
      (0 : Q') 1
      (centralPhysicalFiniteVacuumSectorPathScaleSum
        w (Q'.le_of_lt hw) K 0)
      (by decide)
    rwa [Q'.zero_add'] at h
  exact Q'.le_trans' _ _ _ hKsum hsumCeiling

/-! ## 2. The constructed pulled floor is at most one -/

theorem fixedBasePulledPositiveEdgeFloor_floor_le_one
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    {left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw base half left right) :
    certificate.floor ≤ 1 := by
  have hfloor := certificate.floor_le certificate.start
    (Nat.le_refl certificate.start) left right hleft hright hpositive
  have hbaseStart : base ≤ certificate.start := certificate.start_ge_base
  have hleftLater := centralPhysicalFiniteVacuumSectorIndexMap_mem
    hbaseStart hleft
  have hrightLater := centralPhysicalFiniteVacuumSectorIndexMap_mem
    hbaseStart hright
  let leftLater := centralPhysicalFiniteCutoffIndexMap
    w hw base certificate.start half left
  let rightLater := centralPhysicalFiniteCutoffIndexMap
    w hw base certificate.start half right
  let laterStates := centralPhysicalFiniteVacuumSectorIndices
    w hw certificate.start half
  let laterRow := centralPhysicalFiniteKernel
    w hw certificate.start half leftLater
  have hentryRow : laterRow rightLater ≤
      listQSum laterRow laterStates := by
    apply listQSum_member_le_nonnegative_local
    · intro index
      unfold laterRow centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        hw certificate.start half _ _
    · exact hrightLater
  have hrowWeight : listQSum laterRow laterStates ≈
      centralPhysicalFiniteWeight
        w hw certificate.start half leftLater := by
    exact centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hleftLater
  have hweightOne :
      centralPhysicalFiniteWeight
          w hw certificate.start half leftLater ≤ 1 := by
    change centralPhysicalFinitePulledWeight
      w hw base certificate.start half left ≤ 1
    exact centralPhysicalFinitePulledWeight_le_one hbaseStart hleft
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ hentryRow
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrowWeight) hweightOne))

theorem constructedFixedBaseFloor_le_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (hbase : 1 ≤ base) :
    (fixedBasePulledPositiveEdgeFloor hw0 hw1 base 0).floor ≤ 1 := by
  let spinIndex := centralLowerSpinCubeIndex
    w (Q'.le_of_lt hw0) base 1
  exact fixedBasePulledPositiveEdgeFloor_floor_le_one
    (fixedBasePulledPositiveEdgeFloor hw0 hw1 base 0)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base 0)
    (centralLowerSpinCubeIndex_mem_vacuumSector hw0 hbase)
    (centralPhysicalFiniteKernel_zero_spinCubeIndex_pos hw0 hbase)

/-! ## 3. No strict common rate can bound the constructed family -/

theorem uniformConstructedRate_forces_ceiling_le_rate_mul_denominator
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 0 q)
    (base : Nat) :
    centralPhysicalFiniteVacuumSectorPathCeiling
        w (Q'.le_of_lt hw0) base 0 ≤
      q *
        (centralPhysicalFiniteVacuumSectorPathCeiling
            w (Q'.le_of_lt hw0) base 0 +
          (fixedBasePulledPositiveEdgeFloor hw0 hw1 base 0).floor) := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base 0
  let data := fixedBaseConstructedUniformGapData hw0 hw1 base 0
  have hrate :
      FixedBasePulledPositiveEdgeFloor.uniformPoincareRate certificate ≤ q := by
    have h := family.constructedRate_le base
    rw [data.rate_eq_uniformPoincareRate] at h
    exact h
  have hdenominator0 : (0 : Q') ≤
      FixedBasePulledPositiveEdgeFloor.uniformGapDenominator certificate :=
    Q'.le_of_lt
      (FixedBasePulledPositiveEdgeFloor.uniformGapDenominator_pos certificate)
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    (FixedBasePulledPositiveEdgeFloor.uniformPoincareRate certificate) q
    (FixedBasePulledPositiveEdgeFloor.uniformGapDenominator certificate)
    hrate hdenominator0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (centralPhysicalFiniteVacuumSectorPathCeiling
          w (Q'.le_of_lt hw0) base 0)
        (FixedBasePulledPositiveEdgeFloor.uniformGapDenominator certificate)
        (FixedBasePulledPositiveEdgeFloor.uniformGapDenominator_pos certificate)))
    hscaled

private theorem rate_deficit_mul_ceiling_le_rate_mul_floor
    {q ceiling floor : Q'}
    (hceiling : ceiling ≤ q * (ceiling + floor)) :
    (1 + -q) * ceiling ≤ q * floor := by
  have hshift := Q'.add_le_add_right
    ceiling (q * (ceiling + floor)) (-(q * ceiling)) hceiling
  have hleft :
      ceiling + -(q * ceiling) ≈ (1 + -q) * ceiling := by
    q_ring
  have hright :
      q * (ceiling + floor) + -(q * ceiling) ≈ q * floor := by
    refine Q'.eqv_trans _
      ((q * ceiling + q * floor) + -(q * ceiling)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_add_eqv q ceiling floor)
    refine Q'.eqv_trans _
      (q * ceiling + (q * floor + -(q * ceiling))) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (q * ceiling + (-(q * ceiling) + q * floor)) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.add_comm_eqv (q * floor) (-(q * ceiling)))) ?_
    refine Q'.eqv_trans _
      ((q * ceiling + -(q * ceiling)) + q * floor) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + q * floor) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv _)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (q * floor))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

namespace FixedNomeUniformConstructedVacuumSectorRateBound

/-- A purported strict all-cutoff rate would force its positive deficit times
every sufficiently nonzero cutoff below one. -/
theorem deficit_mul_cutoff_le_one
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 0 q)
    {K : Nat} (hK : 1 ≤ K) :
    (1 + -q) * Q'.ofNat K ≤ 1 := by
  let ceiling := centralPhysicalFiniteVacuumSectorPathCeiling
    w (Q'.le_of_lt hw0) K 0
  let floor := (fixedBasePulledPositiveEdgeFloor hw0 hw1 K 0).floor
  have hdeltaPos : (0 : Q') < 1 + -q :=
    YMGap.Continuum.HKPos.one_sub_pos family.rate_lt_one
  have hKCeiling : Q'.ofNat K ≤ ceiling :=
    cutoff_le_centralPhysicalFiniteVacuumSectorPathCeiling hw0 K
  have hscaled : (1 + -q) * Q'.ofNat K ≤
      (1 + -q) * ceiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hKCeiling
      (Q'.le_of_lt hdeltaPos)
  have hdeficit : (1 + -q) * ceiling ≤ q * floor :=
    rate_deficit_mul_ceiling_le_rate_mul_floor
      (uniformConstructedRate_forces_ceiling_le_rate_mul_denominator
        family K)
  have hfloorOne : floor ≤ 1 :=
    constructedFixedBaseFloor_le_one hw0 hw1 hK
  have hqFloor : q * floor ≤ q * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfloorOne
      family.rate_nonnegative
  have hqOne : q * 1 ≤ 1 :=
    Q'.le_trans' _ q _
      (Q'.le_of_eqv (Q'.mul_one_eqv q))
      (Q'.le_of_lt family.rate_lt_one)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ hdeficit
      (Q'.le_trans' _ _ _ hqFloor hqOne))

/-- **The global all-pairs ceiling / global edge-floor rate compiler is
empty at half-extent zero.**  The contradiction uses an explicit cutoff built
from the denominator of the positive rational rate deficit. -/
theorem impossible
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 0 q) : False := by
  let delta := (1 : Q') + -q
  let request := (delta.den + 1) * (delta.den + 1)
  have hrequest : 1 ≤ request := by
    have hpositive : 0 < request := by
      unfold request
      exact Nat.mul_pos (Nat.succ_pos delta.den) (Nat.succ_pos delta.den)
    exact hpositive
  have hle : delta * Q'.ofNat request ≤ 1 := by
    exact deficit_mul_cutoff_le_one family hrequest
  have hdelta : (0 : Q') < delta :=
    YMGap.Continuum.HKPos.one_sub_pos family.rate_lt_one
  have hlt : (1 : Q') < delta * Q'.ofNat request := by
    exact
      BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo.one_lt_mul_den_succ_square
        delta hdelta
  exact (Int.not_lt_of_ge hle) hlt

end FixedNomeUniformConstructedVacuumSectorRateBound

/-- There is no strict rational common bound on the constructed fixed-base
rates at half-extent zero, for any positive nome below one. -/
theorem no_fixedNomeUniformConstructedVacuumSectorRateBound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q : Q') :
    Not (Nonempty
      (FixedNomeUniformConstructedVacuumSectorRateBound
        w hw0 hw1 0 q)) := by
  intro hfamily
  rcases hfamily with ⟨family⟩
  exact FixedNomeUniformConstructedVacuumSectorRateBound.impossible family

/-- The matched physical producer built from the global constructed rates is
therefore uninhabited: its scale-zero field already asks for the impossible
all-cutoff ceiling. -/
theorem no_matchedPhysicalConstructedRateGapProducer
    {family : BF4MatchedPhysicalAFBridge.MatchedBlockFamily}
    {law : BF4MatchedPhysicalAFBridge.CubicMarginLaw family}
    {spacing : BF4MatchedPhysicalAFBridge.PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory
        family law spacing) :
    Not (Nonempty
      (MatchedPhysicalConstructedRateGapProducer trajectory)) := by
  intro hproducer
  rcases hproducer with ⟨producer⟩
  exact no_fixedNomeUniformConstructedVacuumSectorRateBound
    (trajectory.nome_pos 0) (trajectory.nome_lt_one 0)
    (producer.rate 0)
    ⟨producer.uniformConstructedRateBound 0⟩

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.amplificationScale_one_le_of_ne
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.cutoff_le_centralPhysicalFiniteVacuumSectorPathCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.fixedBasePulledPositiveEdgeFloor_floor_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.constructedFixedBaseFloor_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.uniformConstructedRate_forces_ceiling_le_rate_mul_denominator
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.FixedNomeUniformConstructedVacuumSectorRateBound.deficit_mul_cutoff_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.FixedNomeUniformConstructedVacuumSectorRateBound.impossible
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.no_fixedNomeUniformConstructedVacuumSectorRateBound
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo.no_matchedPhysicalConstructedRateGapProducer
