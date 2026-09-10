/-
# Cubic suppression of the accepted support-swap response defect

The accepted target-rooted support swap fixes the selected root on the left
and moves the selected target to the right.  At cutoff one, both switched
rows therefore contain an occupied face.  The two heat exponents in their
antisymmetric occupation cofactor have a common prefix of three, so that
cofactor contains an exact factor `w^3`.

The analytic row-response defect need not vanish.  What is universally true
is enough for the next estimate: every event response is a probability, each
two-row response difference lies in `[-1,1]`, and the change of such a
difference has absolute value at most two.

This module keeps those two facts separate.  It exposes the exact cubic
factor in the complete response-defect summand and supplies the uniform
probability bound on the remaining defect.  It does not yet sum the cubic
residual over accepted sources or prove the final covariance contraction.

Constructive contract: finite-list probability bounds and rational setoid
algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
import YMGap.Continuum.LargeFieldSuppression

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.LargeFieldSuppression
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

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

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem common_add_sub_eqv_local
    (common left right : Q') :
    (common + left) - (common + right) ≈ left - right := by
  change (common + left) + (-(common + right)) ≈ left + (-right)
  refine Q'.eqv_trans _
    (common + left + ((-common) + (-right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_eqv common right)
  refine Q'.eqv_trans _
    ((common + (-common)) + (left + (-right))) _ ?_ ?_
  · exact Q'.add_swap_inner common left (-common) (-right)
  refine Q'.eqv_trans _
    ((0 : Q') + (left + (-right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_neg_self_eqv common)
  · exact Q'.eqv_of_eq (Q'.zero_add' (left + (-right)))

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈
      factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _
    (Q'.mul_add_eqv factor left (-right)) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

/-! ## 1. A reusable common-prefix identity -/

/-- Removing the same initial segment from two geometric sums exposes its
power as an exact common factor of their skew. -/
theorem geomSumQpowSkew_add_common_eqv
    (w : Q') (base left right : Nat) :
    geomSumQpowSkew w (base + left) (base + right) ≈
      qpow w base * geomSumQpowSkew w left right := by
  refine Q'.eqv_trans _
    (geomSum w (base + left) - geomSum w (base + right)) _
    (geomSumQpowSkew_eqv_geomSum_sub
      w (base + left) (base + right)) ?_
  refine Q'.eqv_trans _
    ((geomSum w base + qpow w base * geomSum w left) -
      (geomSum w base + qpow w base * geomSum w right)) _ ?_ ?_
  · exact sub_eqv_both_local
      (geomSum_add_eqv w base left)
      (geomSum_add_eqv w base right)
  refine Q'.eqv_trans _
    (qpow w base * geomSum w left -
      qpow w base * geomSum w right) _
    (common_add_sub_eqv_local
      (geomSum w base)
      (qpow w base * geomSum w left)
      (qpow w base * geomSum w right)) ?_
  refine Q'.eqv_trans _
    (qpow w base * (geomSum w left - geomSum w right)) _
    (Q'.eqv_symm
      (mul_sub_expand_local
        (qpow w base) (geomSum w left) (geomSum w right))) ?_
  exact Q'.mul_eqv_congr_left (qpow w base) _ _
    (Q'.eqv_symm
      (geomSumQpowSkew_eqv_geomSum_sub w left right))

/-! ## 2. Positive switched occupations -/

/-- A displayed spin-one face is retained by the cutoff-one occupation
selector. -/
theorem mem_slabCutoffOneOccupiedFaces_of_mem_of_spin_one
    (physical : EdgeLabelling) : ∀ (faces : List Nat) (faceId : Nat),
    faceId ∈ faces → physical faceId = 1 →
      faceId ∈ slabCutoffOneOccupiedFaces physical faces
  | [], faceId, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: rest, faceId, hmem, hone => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp only [slabCutoffOneOccupiedFaces, hone, if_true,
          List.mem_cons, true_or]
      · by_cases hhead : physical head = 1
        · simp only [slabCutoffOneOccupiedFaces, hhead, if_true,
            List.mem_cons]
          exact Or.inr
            (mem_slabCutoffOneOccupiedFaces_of_mem_of_spin_one
              physical rest faceId htail hone)
        · simp only [slabCutoffOneOccupiedFaces, hhead, if_false]
          exact mem_slabCutoffOneOccupiedFaces_of_mem_of_spin_one
            physical rest faceId htail hone

/-- At cutoff one, positivity at one displayed face forces a positive global
occupation count. -/
theorem fineCouplingPhysicalOccupiedFaceCount_pos_of_face_positive
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings)
    (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (hpositive : 0 < source faceId) :
    0 < fineCouplingPhysicalOccupiedFaceCount S source := by
  have hbinary := finePhysicalFaceSpin_zero_or_one
    S hfineCutoff source hsource faceId hface
  have hone : source faceId = 1 := by
    rcases hbinary with hzero | hone
    · rw [hzero] at hpositive
      omega
    · exact hone
  unfold fineCouplingPhysicalOccupiedFaceCount
  exact List.length_pos_of_mem
    (mem_slabCutoffOneOccupiedFaces_of_mem_of_spin_one
      source (slabPhysicalFaceEdges S.fine.extent)
      faceId hface hone)

/-- The canonical support switch moves the positive target face from the
source left row to the switched right row. -/
theorem slabObservablePairedSupportSwitchedRightPhysical_target_positive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    0 < slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1 targetFaceId := by
  unfold slabObservablePairSupportSwitchedRightPhysical
    twoReplicaFaceSwapRight
  rw [slabObservableTwoReplicaPairPairedSupportSwapMask_target
    D rootFaceId targetFaceId htarget source.1 source.pair_mem_fourCell]
  exact slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
    D rootFaceId targetFaceId source.1 source.pair_mem_fourCell

/-- The accepted switched left row is occupied because the disconnected
support switch fixes its positive root face. -/
theorem fineCouplingAcceptedSeparated_swappedLeft_occupiedFaceCount_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    0 < fineCouplingPhysicalOccupiedFaceCount S
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source)).1 := by
  rw [fineCouplingAcceptedSeparated_supportSwapped_left
    S rootFaceId targetFaceId source]
  exact fineCouplingPhysicalOccupiedFaceCount_pos_of_face_positive
    S hfineCutoff
    (slabObservablePairSupportSwitchedLeftPhysical
      S.fine targetFaceId source.1)
    (slabObservablePairedSupportSwitchedLeftPhysical_mem S.fine source)
    rootFaceId hroot
    (slabObservablePairedSupportSwitchedLeftPhysical_root_positive
      S.fine rootFaceId targetFaceId source)

/-- The accepted switched right row is occupied because the support switch
moves the source's positive target face to it. -/
theorem fineCouplingAcceptedSeparated_swappedRight_occupiedFaceCount_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    0 < fineCouplingPhysicalOccupiedFaceCount S
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source)).2 := by
  rw [fineCouplingAcceptedSeparated_supportSwapped_right
    S rootFaceId targetFaceId source]
  exact fineCouplingPhysicalOccupiedFaceCount_pos_of_face_positive
    S hfineCutoff
    (slabObservablePairSupportSwitchedRightPhysical
      S.fine targetFaceId source.1)
    (slabObservablePairedSupportSwitchedRightPhysical_mem S.fine source)
    targetFaceId htarget
    (slabObservablePairedSupportSwitchedRightPhysical_target_positive
      S.fine rootFaceId targetFaceId htarget source)

/-! ## 3. Exact cubic factor of the occupation cofactor -/

/-- The signed residual obtained after removing one occupied face from each
row's heat exponent. -/
def fineCouplingPhysicalOccupationSkewCubicResidual
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair) : Q' :=
  geomSumQpowSkew S.fine.coupling
    (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.1 - 1))
    (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 - 1))

/-- If both rows are occupied, their antisymmetric occupation cofactor has
an exact common factor `w^3`. -/
theorem fineCouplingPhysicalOccupationSkewCoefficient_eqv_cubic
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair)
    (hleft : 0 < fineCouplingPhysicalOccupiedFaceCount S pair.1)
    (hright : 0 < fineCouplingPhysicalOccupiedFaceCount S pair.2) :
    fineCouplingPhysicalOccupationSkewCoefficient S pair ≈
      qpow S.fine.coupling 3 *
        fineCouplingPhysicalOccupationSkewCubicResidual S pair := by
  have hleftExponent :
      3 * fineCouplingPhysicalOccupiedFaceCount S pair.1 =
        3 + 3 * (fineCouplingPhysicalOccupiedFaceCount S pair.1 - 1) := by
    omega
  have hrightExponent :
      3 * fineCouplingPhysicalOccupiedFaceCount S pair.2 =
        3 + 3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 - 1) := by
    omega
  unfold fineCouplingPhysicalOccupationSkewCoefficient
    fineCouplingPhysicalOccupationSkewCubicResidual
  change geomSumQpowSkew S.fine.coupling
      (3 * fineCouplingPhysicalOccupiedFaceCount S pair.1)
      (3 * fineCouplingPhysicalOccupiedFaceCount S pair.2) ≈ _
  rw [hleftExponent, hrightExponent]
  exact geomSumQpowSkew_add_common_eqv S.fine.coupling 3
    (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.1 - 1))
    (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 - 1))

/-- On the accepted disconnected carrier, the switched occupation cofactor
has the exact cubic heat factor forced by the retained root and target. -/
theorem fineCouplingAcceptedSeparated_swappedOccupationSkew_eqv_cubic
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingPhysicalSupportSwappedPair
      S targetFaceId pair
    fineCouplingPhysicalOccupationSkewCoefficient S swapped ≈
      qpow S.fine.coupling 3 *
        fineCouplingPhysicalOccupationSkewCubicResidual S swapped := by
  dsimp only
  exact fineCouplingPhysicalOccupationSkewCoefficient_eqv_cubic
    S _
    (fineCouplingAcceptedSeparated_swappedLeft_occupiedFaceCount_pos
      S hfineCutoff rootFaceId targetFaceId hroot source)
    (fineCouplingAcceptedSeparated_swappedRight_occupiedFaceCount_pos
      S hfineCutoff rootFaceId targetFaceId htarget source)

/-! ## 4. Universal probability bound on the response defect -/

private theorem fineCouplingKernelOutputEventMass_eqv_finiteEventMass_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (source : EdgeLabelling) (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass K source event ≈
      finiteEventMass (K.kernel source)
        S.coarse.physicalLabellings event := by
  unfold fineCouplingKernelOutputEventMass finiteEventMass
  exact listQSum_filter (K.kernel source) event
    S.coarse.physicalLabellings

/-- Every event response of a normalized kernel row lies in `[0,1]`. -/
theorem fineCouplingKernelOutputEventMass_unitInterval
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤ fineCouplingKernelOutputEventMass K source event ∧
      fineCouplingKernelOutputEventMass K source event ≤ (1 : Q') := by
  have heqv := fineCouplingKernelOutputEventMass_eqv_finiteEventMass_local
    K source event
  constructor
  · exact Q'.le_trans' _ _ _
      (finiteEventMass_nonnegative
        (K.kernel source) S.coarse.physicalLabellings event
        (fun target htarget =>
          K.nonnegative source target hsource htarget))
      (Q'.ge_of_eqv heqv)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv heqv)
      (finiteEventMass_le_one
        (K.kernel source) S.coarse.physicalLabellings event
        (fun target htarget =>
          K.nonnegative source target hsource htarget)
        (K.row_normalized source hsource))

/-- A difference of two event responses lies in `[-1,1]`. -/
theorem fineCouplingPhysicalPairEventResponseDifference_unitInterval
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalSourcePair)
    (hleft : pair.1 ∈ S.fine.physicalLabellings)
    (hright : pair.2 ∈ S.fine.physicalLabellings) :
    (-(1 : Q')) ≤
        fineCouplingPhysicalPairEventResponseDifference K event pair ∧
      fineCouplingPhysicalPairEventResponseDifference K event pair ≤
        (1 : Q') := by
  let left := fineCouplingKernelOutputEventMass K pair.1 event
  let right := fineCouplingKernelOutputEventMass K pair.2 event
  have hleftBounds := fineCouplingKernelOutputEventMass_unitInterval
    K pair.1 hleft event
  have hrightBounds := fineCouplingKernelOutputEventMass_unitInterval
    K pair.2 hright event
  change (-(1 : Q')) ≤ left - right ∧ left - right ≤ (1 : Q')
  constructor
  · have hadd := Q'.add_le_add
      (Q'.neg_le_neg hrightBounds.2) hleftBounds.1
    rw [Q'.add_zero'] at hadd
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (Q'.add_comm_eqv (-right) left))
  · have hadd := Q'.add_le_add hleftBounds.2
      (Q'.nonpos_neg_of_nonneg hrightBounds.1)
    rwa [Q'.add_zero'] at hadd

/-- The change of a two-row event-response difference has absolute value at
most two.  This is independent of the coupling and of the event. -/
theorem fineCouplingPhysicalSupportSwapResponseDefect_abs_le_two
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (hleft : pair.1 ∈ S.fine.physicalLabellings)
    (hright : pair.2 ∈ S.fine.physicalLabellings)
    (hswappedLeft :
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair).1 ∈
        S.fine.physicalLabellings)
    (hswappedRight :
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair).2 ∈
        S.fine.physicalLabellings) :
    Q'.abs (fineCouplingPhysicalSupportSwapResponseDefect
      K event targetFaceId pair) ≤ (2 : Q') := by
  let response := fineCouplingPhysicalPairEventResponseDifference
    K event pair
  let switchedResponse := fineCouplingPhysicalPairEventResponseDifference
    K event (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair)
  have hresponse :=
    fineCouplingPhysicalPairEventResponseDifference_unitInterval
      K event pair hleft hright
  have hswitched :=
    fineCouplingPhysicalPairEventResponseDifference_unitInterval
      K event (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair)
      hswappedLeft hswappedRight
  unfold fineCouplingPhysicalSupportSwapResponseDefect
  change Q'.abs (response - switchedResponse) ≤ (2 : Q')
  apply Q'.abs_le
  · have hadd := Q'.add_le_add hresponse.1
      (Q'.neg_le_neg hswitched.2)
    exact Q'.le_trans' _ _ _ (by decide) hadd
  · have hadd := Q'.add_le_add hresponse.2
      (Q'.neg_le_neg hswitched.1)
    exact Q'.le_trans' _ _ _ hadd (by decide)

/-- Accepted specialization of the universal response-defect bound. -/
theorem fineCouplingAcceptedSeparated_responseDefect_abs_le_two
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    Q'.abs (fineCouplingPhysicalSupportSwapResponseDefect K event targetFaceId
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)) ≤ (2 : Q') := by
  apply fineCouplingPhysicalSupportSwapResponseDefect_abs_le_two
  · exact source.1.1.physical_mem
  · exact (mem_slabExpandedFineSources_iff.mp source.1.2.2).1
  · rw [fineCouplingAcceptedSeparated_supportSwapped_left
      S rootFaceId targetFaceId source]
    exact slabObservablePairedSupportSwitchedLeftPhysical_mem S.fine source
  · rw [fineCouplingAcceptedSeparated_supportSwapped_right
      S rootFaceId targetFaceId source]
    exact slabObservablePairedSupportSwitchedRightPhysical_mem S.fine source

/-! ## 5. Volume-independent cubic coefficient bounds -/

/-- The geometric skew of two arbitrary exponents is bounded by the infinite
geometric-series ceiling.  The sharper single-ceiling bound uses that both
finite geometric sums lie in the same interval `[0, 1/(1-w)]`. -/
theorem geomSumQpowSkew_abs_le_recip
    (w : Q') (hw0 : (0 : Q') ≤ w)
    (hgap : (0 : Q') < (1 : Q') - w)
    (left right : Nat) :
    Q'.abs (geomSumQpowSkew w left right) ≤
      Q'.divPos 1 ((1 : Q') - w) hgap := by
  let ceiling := Q'.divPos 1 ((1 : Q') - w) hgap
  have hleft0 : (0 : Q') ≤ geomSum w left :=
    geomSum_nonneg hw0 left
  have hright0 : (0 : Q') ≤ geomSum w right :=
    geomSum_nonneg hw0 right
  have hleftCeiling : geomSum w left ≤ ceiling :=
    geomSum_le_recip hw0 hgap left
  have hrightCeiling : geomSum w right ≤ ceiling :=
    geomSum_le_recip hw0 hgap right
  have hdiff : Q'.abs (geomSum w left - geomSum w right) ≤ ceiling := by
    apply Q'.abs_le
    · have hadd := Q'.add_le_add
        (Q'.neg_le_neg hrightCeiling) hleft0
      rw [Q'.add_zero'] at hadd
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv
          (Q'.add_comm_eqv (-(geomSum w right)) (geomSum w left)))
    · have hadd := Q'.add_le_add hleftCeiling
        (Q'.nonpos_neg_of_nonneg hright0)
      rwa [Q'.add_zero'] at hadd
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (geomSumQpowSkew_eqv_geomSum_sub w left right)))
    hdiff

/-- The cubic residual is bounded independently of both occupation counts
and hence independently of the slab volume. -/
theorem fineCouplingPhysicalOccupationSkewCubicResidual_abs_le_recip
    (S : SlabScalePair) (hw0 : (0 : Q') ≤ S.fine.coupling)
    (hgap : (0 : Q') < (1 : Q') - S.fine.coupling)
    (pair : FineCouplingPhysicalSourcePair) :
    Q'.abs (fineCouplingPhysicalOccupationSkewCubicResidual S pair) ≤
      Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap := by
  unfold fineCouplingPhysicalOccupationSkewCubicResidual
  exact geomSumQpowSkew_abs_le_recip
    S.fine.coupling hw0 hgap _ _

/-- If both rows are occupied, the complete occupation cofactor is bounded
by `w^3/(1-w)`, uniformly in both occupation counts and the slab volume. -/
theorem fineCouplingPhysicalOccupationSkewCoefficient_abs_le_cubic_recip
    (S : SlabScalePair) (hw0 : (0 : Q') ≤ S.fine.coupling)
    (hgap : (0 : Q') < (1 : Q') - S.fine.coupling)
    (pair : FineCouplingPhysicalSourcePair)
    (hleft : 0 < fineCouplingPhysicalOccupiedFaceCount S pair.1)
    (hright : 0 < fineCouplingPhysicalOccupiedFaceCount S pair.2) :
    Q'.abs (fineCouplingPhysicalOccupationSkewCoefficient S pair) ≤
      qpow S.fine.coupling 3 *
        Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap := by
  have heqv := fineCouplingPhysicalOccupationSkewCoefficient_eqv_cubic
    S pair hleft hright
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr heqv)) ?_
  have hmul := ExpNeg.abs_mul_le
    (qpow S.fine.coupling 3)
    (fineCouplingPhysicalOccupationSkewCubicResidual S pair)
  rw [ExpNeg.abs_of_nonneg (qpow_nonneg S.fine.coupling hw0 3)] at hmul
  exact Q'.le_trans' _ _ _ hmul
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (fineCouplingPhysicalOccupationSkewCubicResidual_abs_le_recip
        S hw0 hgap pair)
      (qpow_nonneg S.fine.coupling hw0 3))

/-- Every literal coupling-one assignment-pair weight is nonnegative. -/
theorem fineUnitCouplingExpandedFiberPairWeight_nonnegative
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair)
    (assignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :
    (0 : Q') ≤
      fineUnitCouplingExpandedFiberPairWeight S pair assignments := by
  unfold fineUnitCouplingExpandedFiberPairWeight
  apply Q'.mul_nonneg
  · simpa only [fineUnitCouplingSlabPhysicalData] using
      retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        (w := (1 : Q')) (by decide)
        S.fine.cutoff S.fine.half pair.1 assignments.1
  · simpa only [fineUnitCouplingSlabPhysicalData] using
      retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        (w := (1 : Q')) (by decide)
        S.fine.cutoff S.fine.half pair.2 assignments.2

/-! ## 6. The complete cubic response-defect summand -/

/-- The residual response term after removing the exact common `w^3` from
the switched occupation cofactor. -/
def fineCouplingAcceptedSeparatedResponseCubicResidualTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) : Q' :=
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingPhysicalSupportSwappedPair
    S targetFaceId pair
  fineCouplingPhysicalOccupationSkewCubicResidual S swapped *
    (fineUnitCouplingExpandedFiberPairWeight
        S swapped targetAssignments *
      fineCouplingPhysicalSupportSwapResponseDefect
        K event targetFaceId pair)

/-- The entire accepted response-defect summand, not merely its scalar
cofactor, contains the exact cubic heat factor. -/
theorem fineCouplingAcceptedSeparated_responseDefectTerm_eqv_cubic
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool)
    (rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingPhysicalSupportSwappedPair
      S targetFaceId pair
    fineCouplingPhysicalOccupationSkewCoefficient S swapped *
        (fineUnitCouplingExpandedFiberPairWeight
            S swapped targetAssignments *
          fineCouplingPhysicalSupportSwapResponseDefect
            K event targetFaceId pair) ≈
      qpow S.fine.coupling 3 *
        fineCouplingAcceptedSeparatedResponseCubicResidualTerm
          K event rootFaceId targetFaceId source targetAssignments := by
  dsimp only
  refine Q'.eqv_trans _
    ((qpow S.fine.coupling 3 *
        fineCouplingPhysicalOccupationSkewCubicResidual S
          (fineCouplingPhysicalSupportSwappedPair S targetFaceId
            (fineCouplingAcceptedSeparatedPhysicalPair
              S rootFaceId targetFaceId source))) *
      (fineUnitCouplingExpandedFiberPairWeight S
          (fineCouplingPhysicalSupportSwappedPair S targetFaceId
            (fineCouplingAcceptedSeparatedPhysicalPair
              S rootFaceId targetFaceId source)) targetAssignments *
        fineCouplingPhysicalSupportSwapResponseDefect K event targetFaceId
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (fineCouplingAcceptedSeparated_swappedOccupationSkew_eqv_cubic
        S hfineCutoff rootFaceId targetFaceId hroot htarget source)
  · exact Q'.mul_assoc_eqv
      (qpow S.fine.coupling 3)
      (fineCouplingPhysicalOccupationSkewCubicResidual S
        (fineCouplingPhysicalSupportSwappedPair S targetFaceId
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source)))
      (fineUnitCouplingExpandedFiberPairWeight S
          (fineCouplingPhysicalSupportSwappedPair S targetFaceId
            (fineCouplingAcceptedSeparatedPhysicalPair
              S rootFaceId targetFaceId source)) targetAssignments *
        fineCouplingPhysicalSupportSwapResponseDefect K event targetFaceId
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source))

/-- The accepted response-defect summand has a pointwise, volume-independent
bound: at most `2*w^3/(1-w)` times its nonnegative coupling-one assignment
weight.  The remaining global task is therefore a weighted residual-fiber
sum, not a source-row locality identity. -/
theorem fineCouplingAcceptedSeparated_responseDefectTerm_abs_le_cubic_recip
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (hw0 : (0 : Q') ≤ S.fine.coupling)
    (hgap : (0 : Q') < (1 : Q') - S.fine.coupling)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool)
    (rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingPhysicalSupportSwappedPair
      S targetFaceId pair
    Q'.abs
      (fineCouplingPhysicalOccupationSkewCoefficient S swapped *
        (fineUnitCouplingExpandedFiberPairWeight
            S swapped targetAssignments *
          fineCouplingPhysicalSupportSwapResponseDefect
            K event targetFaceId pair)) ≤
      (qpow S.fine.coupling 3 *
        Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap) *
        (fineUnitCouplingExpandedFiberPairWeight
          S swapped targetAssignments * (2 : Q')) := by
  dsimp only
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingPhysicalSupportSwappedPair
    S targetFaceId pair
  let coefficient := fineCouplingPhysicalOccupationSkewCoefficient S swapped
  let weight := fineUnitCouplingExpandedFiberPairWeight
    S swapped targetAssignments
  let defect := fineCouplingPhysicalSupportSwapResponseDefect
    K event targetFaceId pair
  let ceiling := qpow S.fine.coupling 3 *
    Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap
  have hcoefficient : Q'.abs coefficient ≤ ceiling := by
    exact fineCouplingPhysicalOccupationSkewCoefficient_abs_le_cubic_recip
      S hw0 hgap swapped
      (fineCouplingAcceptedSeparated_swappedLeft_occupiedFaceCount_pos
        S hfineCutoff rootFaceId targetFaceId hroot source)
      (fineCouplingAcceptedSeparated_swappedRight_occupiedFaceCount_pos
        S hfineCutoff rootFaceId targetFaceId htarget source)
  have hweight : (0 : Q') ≤ weight :=
    fineUnitCouplingExpandedFiberPairWeight_nonnegative
      S swapped targetAssignments
  have hdefect : Q'.abs defect ≤ (2 : Q') :=
    fineCouplingAcceptedSeparated_responseDefect_abs_le_two
      K event rootFaceId targetFaceId source
  have hinner : Q'.abs (weight * defect) ≤ weight * (2 : Q') := by
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le weight defect) ?_
    rw [ExpNeg.abs_of_nonneg hweight]
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hdefect hweight
  have hceiling : (0 : Q') ≤ ceiling := by
    exact Q'.mul_nonneg _ _
      (qpow_nonneg S.fine.coupling hw0 3)
      (Q'.le_of_lt
        (Q'.divPos_pos 1 ((1 : Q') - S.fine.coupling)
          hgap (by decide)))
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le coefficient (weight * defect)) ?_
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcoefficient
      (Q'.abs_nonneg (weight * defect)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hceiling)

/-- **Cubic accepted response decomposition.**  The exact support-swap
cocycle can be stated with its analytic response residue already carrying
the explicit `w^3` factor. -/
theorem fineCouplingAcceptedSeparatedOccupationResponse_decomposition_cubic
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingPhysicalSupportSwappedPair
      S targetFaceId pair
    let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
      S rootFaceId targetFaceId source
    let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
      S rootFaceId targetFaceId htarget source choice
    fineCouplingExpandedOccupationResponseTerm
        K event pair sourceAssignments ≈
      fineCouplingExpandedOccupationResponseTerm
          K event swapped targetAssignments +
        (((qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.1) +
            qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.2)) *
          fineCouplingPhysicalComponentOccupationSkewCoefficient
            S targetFaceId pair) *
          (fineUnitCouplingExpandedFiberPairWeight
              S pair sourceAssignments *
            fineCouplingPhysicalPairEventResponseDifference
              K event pair) +
          qpow S.fine.coupling 3 *
            fineCouplingAcceptedSeparatedResponseCubicResidualTerm
              K event rootFaceId targetFaceId source
                targetAssignments) := by
  dsimp only
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingPhysicalSupportSwappedPair
    S targetFaceId pair
  let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
    S rootFaceId targetFaceId source
  let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
    S rootFaceId targetFaceId htarget source choice
  let switchedTerm := fineCouplingExpandedOccupationResponseTerm
    K event swapped targetAssignments
  let componentTerm :=
    ((qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.1) +
        qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.2)) *
      fineCouplingPhysicalComponentOccupationSkewCoefficient
        S targetFaceId pair) *
      (fineUnitCouplingExpandedFiberPairWeight
          S pair sourceAssignments *
        fineCouplingPhysicalPairEventResponseDifference K event pair)
  let responseTerm :=
    fineCouplingPhysicalOccupationSkewCoefficient S swapped *
      (fineUnitCouplingExpandedFiberPairWeight
          S swapped targetAssignments *
        fineCouplingPhysicalSupportSwapResponseDefect
          K event targetFaceId pair)
  let cubicTerm :=
    qpow S.fine.coupling 3 *
      fineCouplingAcceptedSeparatedResponseCubicResidualTerm
        K event rootFaceId targetFaceId source targetAssignments
  have hdecomposition :
      fineCouplingExpandedOccupationResponseTerm
          K event pair sourceAssignments ≈
        switchedTerm + (componentTerm + responseTerm) := by
    exact fineCouplingExpandedOccupationResponseTerm_supportSwap_decomposition
      K event targetFaceId pair sourceAssignments targetAssignments
  have hcubic : responseTerm ≈ cubicTerm := by
    exact fineCouplingAcceptedSeparated_responseDefectTerm_eqv_cubic
      hfineCutoff K event rootFaceId targetFaceId hroot htarget
      source targetAssignments
  exact Q'.eqv_trans _ _ _ hdecomposition
    (Q'.add_eqv_congr_left switchedTerm _ _
      (Q'.add_eqv_congr_left componentTerm _ _ hcubic))

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic

#print axioms YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic.geomSumQpowSkew_add_common_eqv
#print axioms YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic.fineCouplingAcceptedSeparated_swappedOccupationSkew_eqv_cubic
#print axioms YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic.fineCouplingAcceptedSeparated_responseDefect_abs_le_two
#print axioms YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic.fineCouplingPhysicalOccupationSkewCoefficient_abs_le_cubic_recip
#print axioms YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic.fineCouplingAcceptedSeparated_responseDefectTerm_eqv_cubic
#print axioms YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic.fineCouplingAcceptedSeparated_responseDefectTerm_abs_le_cubic_recip
#print axioms YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic.fineCouplingAcceptedSeparatedOccupationResponse_decomposition_cubic
