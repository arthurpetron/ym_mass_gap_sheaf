/-
# Complete ground-relative activity of one cutoff-four lowering target

The face and shared-link estimates are now independent proved branches.  This
file contracts them into one rational activity for a complete target's
ground-relative excitation factor.  If `K` is its additive two-spin
excitation mass, then the face branch contributes `(5*w^8)^K` and the link
branch contributes at most `15625^(4*K)`.  Their product is the `K`th power
of one explicit activity.

This is a pointwise summand bound.  It deliberately does not claim that the
single global parity-ground configuration has a volume-uniform posterior
fraction: an anchored connected-support sum is required before extensive
target entropy can be controlled.

Constructive contract: exact rationals and already-certified finite SU(2)
products only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceParityExcitationLinkBound

namespace YMGap.Continuum.Z4DyadicBinarySourceParityExcitationFullActivityBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationLinkBound
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound
open YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit complete activity -/

/-- One excitation pays four worst-case cutoff-four link factors in addition
to the exact full SU(2) face activity. -/
def spinFourParityExcitationFullActivityRate (w : Q') : Q' :=
  Q'.ofNat (cutoffFourLocalMultiplicityNatBound ^ 4) *
    spinFourParityExcitationFaceActivityRate w

private theorem ofNat_mul_eqv_local (left right : Nat) :
    Q'.ofNat left * Q'.ofNat right ≈ Q'.ofNat (left * right) := by
  show ((left : Int) * (right : Int)) * 1 =
    ((left * right : Nat) : Int) * 1
  push_cast
  simp

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem wholeSlabFiniteQProduct_congr_on_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≈ right item) →
      wholeSlabFiniteQProduct left items ≈
        wholeSlabFiniteQProduct right items
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree => by
      change
        left head * wholeSlabFiniteQProduct left tail ≈
          right head * wholeSlabFiniteQProduct right tail
      exact Q'.eqv_trans _
        (right head * wholeSlabFiniteQProduct left tail) _
        (Q'.mul_eqv_congr_right _ _ _
          (hagree head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (wholeSlabFiniteQProduct_congr_on_local left right tail
            (fun item hmem =>
              hagree item (List.mem_cons_of_mem head hmem))))

private theorem ofNat_natListProduct_eqv_wholeSlabFiniteQProduct_local
    {A : Type} (value : A → Nat) : ∀ items : List A,
    Q'.ofNat (natListProduct value items) ≈
      wholeSlabFiniteQProduct (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [natListProduct, wholeSlabFiniteQProduct]
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (ofNat_mul_eqv_local (value head) (natListProduct value tail)))
        (Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_wholeSlabFiniteQProduct_local
            value tail))

private theorem wholeSlabFiniteQProduct_qpow_eqv_qpow_listNatWeight_local
    {A : Type} (w : Q') (exponent : A → Nat) : ∀ items : List A,
    wholeSlabFiniteQProduct (fun item => qpow w (exponent item)) items ≈
      qpow w (listNatWeight exponent items)
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [wholeSlabFiniteQProduct, listNatWeight]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (wholeSlabFiniteQProduct_qpow_eqv_qpow_listNatWeight_local
            w exponent tail)) ?_
      exact Q'.eqv_symm
        (qpow_add w (exponent head) (listNatWeight exponent tail))

private theorem listNatWeight_eq_zero_of_pointwise_local {A : Type}
    (weight : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → weight item = 0) →
      listNatWeight weight items = 0
  | [], _ => rfl
  | head :: tail, hzero => by
      simp only [listNatWeight]
      rw [hzero head List.mem_cons_self]
      simpa only [Nat.zero_add] using
        (listNatWeight_eq_zero_of_pointwise_local weight tail
          (fun item hmem => hzero item (List.mem_cons_of_mem head hmem)))

private theorem qpow_ofNat_eqv_ofNat_pow (base : Nat) : ∀ exponent : Nat,
    qpow (Q'.ofNat base) exponent ≈ Q'.ofNat (base ^ exponent)
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      show qpow (Q'.ofNat base) exponent * Q'.ofNat base ≈
        Q'.ofNat (base ^ (exponent + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Q'.ofNat base)
          (qpow_ofNat_eqv_ofNat_pow base exponent)) ?_
      rw [Nat.pow_succ]
      exact ofNat_mul_eqv_local _ _

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d)))
  refine Q'.mul_eqv_congr_left a _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

private theorem wholeSlabFiniteQProduct_pointwise_mul_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    wholeSlabFiniteQProduct (fun item => left item * right item) items ≈
      wholeSlabFiniteQProduct left items *
        wholeSlabFiniteQProduct right items
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail => by
      simp only [wholeSlabFiniteQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left head * right head) _ _
          (wholeSlabFiniteQProduct_pointwise_mul_local left right tail)) ?_
      exact mul_four_regroup_local _ _ _ _

private theorem mul_four_ground_activity_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * d) * (c * b) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (a * b) _ _ (Q'.mul_comm_eqv c d)) ?_
  refine Q'.eqv_trans _ _ _
    (mul_four_regroup_local a b d c) ?_
  exact Q'.mul_eqv_congr_left (a * d) _ _ (Q'.mul_comm_eqv b c)

private theorem qpow_mul_base_local (left right : Q') : ∀ exponent : Nat,
    qpow (left * right) exponent ≈
      qpow left exponent * qpow right exponent
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | exponent + 1 => by
      show qpow (left * right) exponent * (left * right) ≈
        (qpow left exponent * left) * (qpow right exponent * right)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (left * right)
          (qpow_mul_base_local left right exponent)) ?_
      exact mul_four_regroup_local _ _ _ _

/-- The displayed complete activity has exactly the two factors supplied by
the independent face and link estimates. -/
theorem qpow_spinFourParityExcitationFullActivityRate_eqv
    (w : Q') (excitationMass : Nat) :
    qpow (spinFourParityExcitationFullActivityRate w) excitationMass ≈
      Q'.ofNat
          (cutoffFourLocalMultiplicityNatBound ^ (4 * excitationMass)) *
        qpow (spinFourParityExcitationFaceActivityRate w) excitationMass := by
  unfold spinFourParityExcitationFullActivityRate
  refine Q'.eqv_trans _ _ _
    (qpow_mul_base_local
      (Q'.ofNat (cutoffFourLocalMultiplicityNatBound ^ 4))
      (spinFourParityExcitationFaceActivityRate w) excitationMass) ?_
  refine Q'.mul_eqv_congr_right _ _
    (qpow (spinFourParityExcitationFaceActivityRate w) excitationMass) ?_
  refine Q'.eqv_trans _ _ _
    (qpow_ofNat_eqv_ofNat_pow
      (cutoffFourLocalMultiplicityNatBound ^ 4) excitationMass) ?_
  rw [Nat.pow_mul]
  exact Q'.eqv_refl _

/-- At the production anchor `w = 1/400`, the complete one-excitation
activity simplifies to `5^9 / 2^32`, far below one. -/
theorem spinFourParityExcitationFullActivityRate_anchor_eqv :
    spinFourParityExcitationFullActivityRate
        (Q'.mkPos 1 400 (by decide)) ≈
      Q'.mkPos 1953125 4294967296 (by decide) := by
  decide

theorem spinFourParityExcitationFullActivityRate_anchor_lt_one :
    spinFourParityExcitationFullActivityRate
        (Q'.mkPos 1 400 (by decide)) < (1 : Q') := by
  have hle : spinFourParityExcitationFullActivityRate
        (Q'.mkPos 1 400 (by decide)) ≤
      Q'.mkPos 1953125 4294967296 (by decide) :=
    Q'.le_of_eqv spinFourParityExcitationFullActivityRate_anchor_eqv
  exact HeatKernelGap.lt_of_le_of_lt hle (by decide)

/-- The complete activity remains strictly subunit throughout the explicitly
named strong-coupling corridor. -/
theorem spinFourParityExcitationFullActivityRate_lt_one
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwAnchor : w ≤ Q'.mkPos 1 400 (by decide)) :
    spinFourParityExcitationFullActivityRate w < (1 : Q') := by
  have hpower : qpow w 8 ≤
      qpow (Q'.mkPos 1 400 (by decide)) 8 :=
    HeatKernelGap.qpow_mono hw0 hwAnchor 8
  have hface : spinFourParityExcitationFaceActivityRate w ≤
      spinFourParityExcitationFaceActivityRate
        (Q'.mkPos 1 400 (by decide)) := by
    unfold spinFourParityExcitationFaceActivityRate
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpower (zero_le_ofNat 5)
  have hfull : spinFourParityExcitationFullActivityRate w ≤
      spinFourParityExcitationFullActivityRate
        (Q'.mkPos 1 400 (by decide)) := by
    unfold spinFourParityExcitationFullActivityRate
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hface (zero_le_ofNat _)
  exact HeatKernelGap.lt_of_le_of_lt hfull
    spinFourParityExcitationFullActivityRate_anchor_lt_one

/-! ## 2. Complete relative excitation factor -/

/-- Source-determined parity-ground Casimir exponent over the complete coarse
face carrier.  This is the common heat exponent of every target in the same
pointwise parity-preserving lowering row. -/
def positivePhysicalSourceParityGroundCasimirExponent
    (S : SlabScalePair) (source : PositivePhysicalSource S) : Nat :=
  listNatWeight
    (fun faceId => spinFourParityGroundCasimirExponent
      (wholeSlabFinePacketTotalLabelling S source.1 faceId))
    S.coarse.faceEdges

/-- The common source-row parity-ground heat factor. -/
def positivePhysicalSourceParityGroundHeatFactor
    (S : SlabScalePair) (source : PositivePhysicalSource S) : Q' :=
  qpow S.coarse.coupling
    (positivePhysicalSourceParityGroundCasimirExponent S source)

/-- Face coefficient, excitation heat, and complete shared-link product of
one lowering target, with the source-dependent ground heat factored out. -/
def positivePhysicalSourceRelativeExcitationWeight
    (S : SlabScalePair) (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling) : Q' :=
  (Q'.ofNat
      (positivePhysicalSourceLoweringFaceCoefficientProduct
        S source targetState) *
    qpow S.coarse.coupling
      (positivePhysicalSourceParityExcitationCasimirExcess
        S source targetState)) *
  Q'.ofNat
    (slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent targetState)

/-- The corresponding parity-ground face coefficient and complete link
product, again omitting only the common parity-ground heat factor. -/
def positivePhysicalSourceParityGroundRelativeCoefficient
    (S : SlabScalePair) (source : PositivePhysicalSource S) : Q' :=
  Q'.ofNat
      (positivePhysicalSourceParityGroundFaceCoefficientProduct S source) *
    Q'.ofNat
      (slabExplicitLinkMultiplicityProduct
        S.coarse.cutoff S.coarse.extent
        (YMGap.Continuum.CompactDualCutoffOneParitySlabTarget.cutoffOneCoarseParityState
          S source.1))

private theorem spinFourLoweringFaceWeight_eqv_groundHeat_mul_relative
    (w : Q') {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    spinFourLoweringFaceWeight w sourceSpin targetSpin ≈
      qpow w (spinFourParityGroundCasimirExponent sourceSpin) *
        (Q'.ofNat
            (spinFourLoweringMultiplicity sourceSpin targetSpin *
              (targetSpin + 1)) *
          qpow w
            (spinFourParityExcitationCasimirExcess
              sourceSpin targetSpin)) := by
  have hheat := qpow_spinFourTargetCasimir_eqv_ground_mul_excitation
    w hsource htarget hlowering
  unfold spinFourLoweringFaceWeight coeffW dimQ
  refine Q'.eqv_trans _
    (Q'.ofNat (spinFourLoweringMultiplicity sourceSpin targetSpin) *
      (Q'.ofNat (targetSpin + 1) *
        (qpow w (spinFourParityGroundCasimirExponent sourceSpin) *
          qpow w
            (spinFourParityExcitationCasimirExcess
              sourceSpin targetSpin)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hheat)
  refine Q'.eqv_trans _
    (qpow w (spinFourParityGroundCasimirExponent sourceSpin) *
      ((Q'.ofNat (spinFourLoweringMultiplicity sourceSpin targetSpin) *
          Q'.ofNat (targetSpin + 1)) *
        qpow w
          (spinFourParityExcitationCasimirExcess
            sourceSpin targetSpin))) _ ?_ ?_
  · ring_qeqv
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv_local
        (spinFourLoweringMultiplicity sourceSpin targetSpin)
        (targetSpin + 1)))

private theorem spinFourLoweringFaceProduct_eqv_groundHeat_mul_relative
    (w : Q') (sourceState targetState : EdgeLabelling) (faces : List Nat)
    (hsource : ∀ faceId, faceId ∈ faces → sourceState faceId ≤ 4)
    (htarget : ∀ faceId, faceId ∈ faces → targetState faceId ≤ 4)
    (hlowering : ∀ faceId, faceId ∈ faces →
      targetState faceId ≤ sourceState faceId ∧
        targetState faceId % 2 = sourceState faceId % 2) :
    wholeSlabFiniteQProduct
        (fun faceId => spinFourLoweringFaceWeight w
          (sourceState faceId) (targetState faceId)) faces ≈
      qpow w
          (listNatWeight
            (fun faceId => spinFourParityGroundCasimirExponent
              (sourceState faceId)) faces) *
        (Q'.ofNat
            (spinFourLoweringFaceCoefficientProductOn
              sourceState targetState faces) *
          qpow w
            (spinFourParityExcitationCasimirExcessOn
              sourceState targetState faces)) := by
  let groundHeat : Nat → Q' := fun faceId =>
    qpow w (spinFourParityGroundCasimirExponent (sourceState faceId))
  let relativeFace : Nat → Q' := fun faceId =>
    Q'.ofNat
        (spinFourLoweringMultiplicity
            (sourceState faceId) (targetState faceId) *
          (targetState faceId + 1)) *
      qpow w
        (spinFourParityExcitationCasimirExcess
          (sourceState faceId) (targetState faceId))
  have hpointwise : ∀ faceId, faceId ∈ faces →
      spinFourLoweringFaceWeight w
          (sourceState faceId) (targetState faceId) ≈
        groundHeat faceId * relativeFace faceId := by
    intro faceId hface
    exact spinFourLoweringFaceWeight_eqv_groundHeat_mul_relative
      w (hsource faceId hface) (htarget faceId hface)
        (hlowering faceId hface)
  have hfactor :
      wholeSlabFiniteQProduct
          (fun faceId => spinFourLoweringFaceWeight w
            (sourceState faceId) (targetState faceId)) faces ≈
        wholeSlabFiniteQProduct groundHeat faces *
          wholeSlabFiniteQProduct relativeFace faces :=
    Q'.eqv_trans _ _ _
      (wholeSlabFiniteQProduct_congr_on_local _ _ faces hpointwise)
      (wholeSlabFiniteQProduct_pointwise_mul_local
        groundHeat relativeFace faces)
  have hground : wholeSlabFiniteQProduct groundHeat faces ≈
      qpow w
        (listNatWeight
          (fun faceId => spinFourParityGroundCasimirExponent
            (sourceState faceId)) faces) := by
    exact wholeSlabFiniteQProduct_qpow_eqv_qpow_listNatWeight_local
      w _ faces
  have hrelativeSplit : wholeSlabFiniteQProduct relativeFace faces ≈
      wholeSlabFiniteQProduct
          (fun faceId => Q'.ofNat
            (spinFourLoweringMultiplicity
                (sourceState faceId) (targetState faceId) *
              (targetState faceId + 1))) faces *
        wholeSlabFiniteQProduct
          (fun faceId => qpow w
            (spinFourParityExcitationCasimirExcess
              (sourceState faceId) (targetState faceId))) faces := by
    exact wholeSlabFiniteQProduct_pointwise_mul_local _ _ faces
  have hcoefficient :
      wholeSlabFiniteQProduct
          (fun faceId => Q'.ofNat
            (spinFourLoweringMultiplicity
                (sourceState faceId) (targetState faceId) *
              (targetState faceId + 1))) faces ≈
        Q'.ofNat
          (spinFourLoweringFaceCoefficientProductOn
            sourceState targetState faces) := by
    unfold spinFourLoweringFaceCoefficientProductOn
    exact Q'.eqv_symm
      (ofNat_natListProduct_eqv_wholeSlabFiniteQProduct_local _ faces)
  have hexcess :
      wholeSlabFiniteQProduct
          (fun faceId => qpow w
            (spinFourParityExcitationCasimirExcess
              (sourceState faceId) (targetState faceId))) faces ≈
        qpow w
          (spinFourParityExcitationCasimirExcessOn
            sourceState targetState faces) := by
    unfold spinFourParityExcitationCasimirExcessOn
    exact wholeSlabFiniteQProduct_qpow_eqv_qpow_listNatWeight_local
      w _ faces
  have hrelative : wholeSlabFiniteQProduct relativeFace faces ≈
      Q'.ofNat
          (spinFourLoweringFaceCoefficientProductOn
            sourceState targetState faces) *
        qpow w
          (spinFourParityExcitationCasimirExcessOn
            sourceState targetState faces) :=
    Q'.eqv_trans _ _ _ hrelativeSplit
      (qmul_congr_local hcoefficient hexcess)
  exact Q'.eqv_trans _ _ _ hfactor
    (qmul_congr_local hground hrelative)

/-- The actual complete lower-triangular slab weight separates exactly into
the source-row parity-ground heat factor and the relative excitation weight
bounded below. -/
theorem spinFourLoweringWholeSlabRawWeight_eqv_groundHeat_mul_relative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    spinFourLoweringWholeSlabRawWeight S
        (wholeSlabFinePacketTotalLabelling S source.1) targetState ≈
      positivePhysicalSourceParityGroundHeatFactor S source *
        positivePhysicalSourceRelativeExcitationWeight
          S source targetState := by
  have hparts := (mem_spinFourLoweringTargets_iff S _ _).mp htarget
  have hsourceBound : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      wholeSlabFinePacketTotalLabelling S source.1 faceId ≤ 4 := by
    intro faceId hface
    exact wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff source.2.1 faceId hface
  have htargetBound : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      targetState faceId ≤ 4 := by
    intro faceId hface
    have hsound := boundedEdgeLabellings_sound
      S.coarse.cutoff S.coarse.faceEdges targetState hparts.1
    have hbound := Nat.le_of_lt_succ (hsound.1 faceId hface)
    rw [S.coarse_cutoff, hfineCutoff] at hbound
    omega
  have hfaces := spinFourLoweringFaceProduct_eqv_groundHeat_mul_relative
    S.coarse.coupling
    (wholeSlabFinePacketTotalLabelling S source.1) targetState
    S.coarse.faceEdges hsourceBound htargetBound hparts.2
  unfold spinFourLoweringWholeSlabRawWeight
    positivePhysicalSourceParityGroundHeatFactor
    positivePhysicalSourceParityGroundCasimirExponent
    positivePhysicalSourceRelativeExcitationWeight
    positivePhysicalSourceLoweringFaceCoefficientProduct
    positivePhysicalSourceParityExcitationCasimirExcess
  refine Q'.eqv_trans _
    ((qpow S.coarse.coupling
        (listNatWeight
          (fun faceId => spinFourParityGroundCasimirExponent
            (wholeSlabFinePacketTotalLabelling S source.1 faceId))
          S.coarse.faceEdges) *
      (Q'.ofNat
          (spinFourLoweringFaceCoefficientProductOn
            (wholeSlabFinePacketTotalLabelling S source.1)
            targetState S.coarse.faceEdges) *
        qpow S.coarse.coupling
          (spinFourParityExcitationCasimirExcessOn
            (wholeSlabFinePacketTotalLabelling S source.1)
            targetState S.coarse.faceEdges))) *
      Q'.ofNat
        (slabExplicitLinkMultiplicityProduct
          S.coarse.cutoff S.coarse.extent targetState)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hfaces
  exact Q'.mul_assoc_eqv _ _ _

/-- The integer-tilted Gibbs summand itself has the same exact factorization;
this is the bridge from the relative activity estimate to the actual finite
production law. -/
theorem positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_groundHeat_mul_relative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    positivePhysicalSourceTiltedGibbsFullRawWeight
        S source targetState ≈
      positivePhysicalSourceParityGroundHeatFactor S source *
        positivePhysicalSourceRelativeExcitationWeight
          S source targetState := by
  have hparts := (mem_spinFourLoweringTargets_iff S _ _).mp htarget
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
        S (wholeSlabFinePacketTotalLabelling S source.1)
          targetState hparts.1))
    (spinFourLoweringWholeSlabRawWeight_eqv_groundHeat_mul_relative
      S hfineCutoff source targetState htarget)

private theorem positivePhysicalSourceParityGroundFaceCoefficient_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceLoweringFaceCoefficientProduct S source
        (YMGap.Continuum.CompactDualCutoffOneParitySlabTarget.cutoffOneCoarseParityState
          S source.1) =
      positivePhysicalSourceParityGroundFaceCoefficientProduct S source := by
  unfold positivePhysicalSourceLoweringFaceCoefficientProduct
    positivePhysicalSourceParityGroundFaceCoefficientProduct
    spinFourLoweringFaceCoefficientProductOn
    spinFourParityGroundFaceCoefficientProductOn
  apply natListProduct_congr
  intro faceId hface
  rw [YMGap.Continuum.Z4DyadicBinarySourceParityGroundState.cutoffOneCoarseParityState_face_eq_total_mod_two
    S hfineCutoff source.2.1 hface]
  rw [spinFourLoweringMultiplicity_parityGround
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff source.2.1 faceId hface)]
  rfl

private theorem positivePhysicalSourceParityGroundExcitationExcess_eq_zero
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceParityExcitationCasimirExcess S source
        (YMGap.Continuum.CompactDualCutoffOneParitySlabTarget.cutoffOneCoarseParityState
          S source.1) = 0 := by
  unfold positivePhysicalSourceParityExcitationCasimirExcess
    spinFourParityExcitationCasimirExcessOn
  apply listNatWeight_eq_zero_of_pointwise_local
  intro faceId hface
  rw [YMGap.Continuum.Z4DyadicBinarySourceParityGroundState.cutoffOneCoarseParityState_face_eq_total_mod_two
    S hfineCutoff source.2.1 hface]
  unfold spinFourParityExcitationCasimirExcess
    spinFourParityGroundCasimirExponent
  omega

private theorem positivePhysicalSourceRelativeExcitationWeight_parityGround_eqv
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceRelativeExcitationWeight S source
        (YMGap.Continuum.CompactDualCutoffOneParitySlabTarget.cutoffOneCoarseParityState
          S source.1) ≈
      positivePhysicalSourceParityGroundRelativeCoefficient S source := by
  unfold positivePhysicalSourceRelativeExcitationWeight
    positivePhysicalSourceParityGroundRelativeCoefficient
  rw [positivePhysicalSourceParityGroundFaceCoefficient_eq
    S hfineCutoff source]
  rw [positivePhysicalSourceParityGroundExcitationExcess_eq_zero
    S hfineCutoff source]
  change (Q'.ofNat _ * 1) * Q'.ofNat _ ≈
    Q'.ofNat _ * Q'.ofNat _
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)

private theorem positivePhysicalSourceParityGroundHeat_mul_relative_eqv_mass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceParityGroundHeatFactor S source *
        positivePhysicalSourceParityGroundRelativeCoefficient S source ≈
      positivePhysicalSourceParityGroundMass S source := by
  have htarget := cutoffOneCoarseParityState_mem_totalLoweringTargets
    S hfineCutoff source.2.1
  have hfactor :=
    positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_groundHeat_mul_relative
      S hfineCutoff source
      (YMGap.Continuum.CompactDualCutoffOneParitySlabTarget.cutoffOneCoarseParityState
        S source.1) htarget
  have hmass : positivePhysicalSourceParityGroundMass S source ≈
      positivePhysicalSourceParityGroundHeatFactor S source *
        positivePhysicalSourceRelativeExcitationWeight S source
          (YMGap.Continuum.CompactDualCutoffOneParitySlabTarget.cutoffOneCoarseParityState
            S source.1) := by
    simpa only [positivePhysicalSourceParityGroundMass,
      positivePhysicalSourceTiltedGibbsFullRawWeight] using hfactor
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (positivePhysicalSourceRelativeExcitationWeight_parityGround_eqv
          S hfineCutoff source)))
    (Q'.eqv_symm hmass)

/-- Face and link losses contract into one explicit power per excitation for
every target in the actual positive cutoff-one lowering row. -/
theorem positivePhysicalSourceRelativeExcitationWeight_le_ground_mul_activity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarse0 : (0 : Q') ≤ S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    positivePhysicalSourceRelativeExcitationWeight S source targetState ≤
      positivePhysicalSourceParityGroundRelativeCoefficient S source *
        qpow
          (spinFourParityExcitationFullActivityRate S.coarse.coupling)
          (positivePhysicalSourceParityExcitationActivity
            S source targetState) := by
  let activity := positivePhysicalSourceParityExcitationActivity
    S source targetState
  let targetFace :=
    Q'.ofNat
        (positivePhysicalSourceLoweringFaceCoefficientProduct
          S source targetState) *
      qpow S.coarse.coupling
        (positivePhysicalSourceParityExcitationCasimirExcess
          S source targetState)
  let groundFace := Q'.ofNat
    (positivePhysicalSourceParityGroundFaceCoefficientProduct S source)
  let targetLink := Q'.ofNat
    (slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent targetState)
  let groundLinkNat := slabExplicitLinkMultiplicityProduct
    S.coarse.cutoff S.coarse.extent
    (YMGap.Continuum.CompactDualCutoffOneParitySlabTarget.cutoffOneCoarseParityState
      S source.1)
  let groundLink := Q'.ofNat groundLinkNat
  let linkPowerNat :=
    cutoffFourLocalMultiplicityNatBound ^ (4 * activity)
  let linkPower := Q'.ofNat linkPowerNat
  have hface : targetFace ≤ groundFace *
      qpow (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
        activity := by
    exact positivePhysicalSourceLoweringFaceCoefficient_mul_excitationHeat_le_ground_mul_activity
      S hfineCutoff hcoarse0 hcoarse1 source targetState htarget
  have hlinkNat :
      slabExplicitLinkMultiplicityProduct
          S.coarse.cutoff S.coarse.extent targetState ≤
        linkPowerNat * groundLinkNat := by
    exact positivePhysicalSourceLoweringLinkProduct_le_ground_mul_activityPow
      S hfineCutoff source targetState htarget
  have hlinkCast : targetLink ≤ Q'.ofNat (linkPowerNat * groundLinkNat) :=
    CReal.ofNat_le_ofNat hlinkNat
  have hlink : targetLink ≤ linkPower * groundLink :=
    Q'.le_trans' _ _ _ hlinkCast
      (Q'.le_of_eqv (Q'.eqv_symm
        (ofNat_mul_eqv_local linkPowerNat groundLinkNat)))
  have htargetLink0 : (0 : Q') ≤ targetLink := zero_le_ofNat _
  have hgroundFace0 : (0 : Q') ≤ groundFace := zero_le_ofNat _
  have hfaceActivity0 : (0 : Q') ≤
      qpow (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
        activity := by
    apply qpow_nonneg
    exact Q'.mul_nonneg _ _ (zero_le_ofNat _)
      (qpow_nonneg S.coarse.coupling hcoarse0 8)
  have hfaceRhs0 : (0 : Q') ≤ groundFace *
      qpow (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
        activity :=
    Q'.mul_nonneg _ _ hgroundFace0 hfaceActivity0
  have hfirst : targetFace * targetLink ≤
      (groundFace *
        qpow (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
          activity) * targetLink :=
    Q'.mul_le_mul_of_nonneg_right _ _ targetLink hface htargetLink0
  have hsecond :
      (groundFace *
        qpow (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
          activity) * targetLink ≤
      (groundFace *
        qpow (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
          activity) * (linkPower * groundLink) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hlink hfaceRhs0
  have hregroup :
      (groundFace *
        qpow (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
          activity) * (linkPower * groundLink) ≈
      (groundFace * groundLink) *
        qpow
          (spinFourParityExcitationFullActivityRate S.coarse.coupling)
          activity := by
    refine Q'.eqv_trans _ _ _
      (mul_four_ground_activity_regroup_local groundFace
        (qpow
          (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
          activity)
        linkPower groundLink) ?_
    exact Q'.mul_eqv_congr_left (groundFace * groundLink) _ _
      (Q'.eqv_symm
        (qpow_spinFourParityExcitationFullActivityRate_eqv
          S.coarse.coupling activity))
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hregroup))

/-! ## 3. The complete actual tilted-summand bound -/

/-- Every supported summand of the actual positive cutoff-one production row
is bounded by its literal parity-ground summand times one explicit power of
the complete excitation activity.  The source-dependent common heat factor
has been identified exactly on both sides rather than discarded. -/
theorem positivePhysicalSourceTiltedGibbsFullRawWeight_le_parityGroundMass_mul_activity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarse0 : (0 : Q') ≤ S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    positivePhysicalSourceTiltedGibbsFullRawWeight S source targetState ≤
      positivePhysicalSourceParityGroundMass S source *
        qpow
          (spinFourParityExcitationFullActivityRate S.coarse.coupling)
          (positivePhysicalSourceParityExcitationActivity
            S source targetState) := by
  have hrelative :=
    positivePhysicalSourceRelativeExcitationWeight_le_ground_mul_activity
      S hfineCutoff hcoarse0 hcoarse1 source targetState htarget
  have hheat0 : (0 : Q') ≤
      positivePhysicalSourceParityGroundHeatFactor S source := by
    unfold positivePhysicalSourceParityGroundHeatFactor
    exact qpow_nonneg _ hcoarse0 _
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (positivePhysicalSourceParityGroundHeatFactor S source)
    hrelative hheat0
  have hactual :=
    positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_groundHeat_mul_relative
      S hfineCutoff source targetState htarget
  have hground :=
    positivePhysicalSourceParityGroundHeat_mul_relative_eqv_mass
      S hfineCutoff source
  have hregroup :
      positivePhysicalSourceParityGroundHeatFactor S source *
          (positivePhysicalSourceParityGroundRelativeCoefficient S source *
            qpow
              (spinFourParityExcitationFullActivityRate S.coarse.coupling)
              (positivePhysicalSourceParityExcitationActivity
                S source targetState)) ≈
        positivePhysicalSourceParityGroundMass S source *
          qpow
            (spinFourParityExcitationFullActivityRate S.coarse.coupling)
            (positivePhysicalSourceParityExcitationActivity
              S source targetState) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (positivePhysicalSourceParityGroundHeatFactor S source)
          (positivePhysicalSourceParityGroundRelativeCoefficient S source)
          (qpow
            (spinFourParityExcitationFullActivityRate S.coarse.coupling)
            (positivePhysicalSourceParityExcitationActivity
              S source targetState)))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ hground
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hactual)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hregroup))

/-- Expanded form of the preceding theorem: the bounded object is literally
the fusion-path tilt times the complete coarse SU(2) Gibbs physical term. -/
theorem spinFourLoweringMultiplicityProduct_mul_physicalTerm_le_parityGroundMass_mul_activity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarse0 : (0 : Q') ≤ S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    Q'.ofNat
        (spinFourLoweringMultiplicityProduct S
          (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
      S.coarse.physicalTerm targetState ≤
        positivePhysicalSourceParityGroundMass S source *
          qpow
            (spinFourParityExcitationFullActivityRate S.coarse.coupling)
            (positivePhysicalSourceParityExcitationActivity
              S source targetState) := by
  exact positivePhysicalSourceTiltedGibbsFullRawWeight_le_parityGroundMass_mul_activity
    S hfineCutoff hcoarse0 hcoarse1 source targetState htarget

#print axioms spinFourParityExcitationFullActivityRate
#print axioms qpow_spinFourParityExcitationFullActivityRate_eqv
#print axioms spinFourParityExcitationFullActivityRate_anchor_eqv
#print axioms spinFourParityExcitationFullActivityRate_anchor_lt_one
#print axioms spinFourParityExcitationFullActivityRate_lt_one
#print axioms positivePhysicalSourceRelativeExcitationWeight
#print axioms positivePhysicalSourceParityGroundRelativeCoefficient
#print axioms positivePhysicalSourceParityGroundCasimirExponent
#print axioms positivePhysicalSourceParityGroundHeatFactor
#print axioms spinFourLoweringWholeSlabRawWeight_eqv_groundHeat_mul_relative
#print axioms positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_groundHeat_mul_relative
#print axioms positivePhysicalSourceRelativeExcitationWeight_le_ground_mul_activity
#print axioms positivePhysicalSourceTiltedGibbsFullRawWeight_le_parityGroundMass_mul_activity
#print axioms spinFourLoweringMultiplicityProduct_mul_physicalTerm_le_parityGroundMass_mul_activity

end YMGap.Continuum.Z4DyadicBinarySourceParityExcitationFullActivityBound
