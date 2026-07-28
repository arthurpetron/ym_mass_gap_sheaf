/-
# BF4 fixed-plane magnetic refinement and exact Mehler window

The fixed-plane Choi carrier already retains every accepted SU(2) link
intertwiner.  Its spatial weight still contains the representation dimension

    coeffW w s = (s+1) * w^(C4 s).

This module removes that last cutoff-dependent prefactor from the channel
weight without discarding it.  For every fixed face of spin `s`, it enlarges
the carrier by the literal magnetic list `0, ..., s`.  Summation over this
new finite fiber reconstructs the factor `s+1` exactly.  Every refined
channel therefore carries only the heat-semigroup eigenweight

    w^(C4 s),

on each fixed face.

Consequences:

* conditional integration over the magnetic and link-intertwiner fibers
  recovers the genuine BF4 fixed-interface weight;
* the refined all-label Choi contraction is exactly the physical reflected
  kernel;
* on this enlarged carrier the physical spatial insertion and its Mehler
  reference agree, so the pointwise order window is the spacing-uniform
  interval `[1,1]`; and
* the growth of one magnetic fiber is absorbed by the existing
  spacing-dependent SU(2) heat-tail majorant.

Honest scope: the last estimate is the local entry estimate.  This module
does not yet normalize the full growing BF4 endpoint matrix, prove the
global Hilbert--Schmidt modulus, or identify its physical Perron eigenmode.

## Axiom gate

Finite `List`, `Nat`, and exact `Q'` algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FixedIntertwinerPhysicalChoi
import YMGap.Continuum.BF4RetainedGramReferenceOrder
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

namespace YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4RetainedGramReferenceOrder
open YMGap.Continuum.BF4SU2FixedIntertwinerPhysicalChoi
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Literal magnetic fibers -/

/-- One fixed-face magnetic assignment, displayed as `(faceId, magneticIndex)`
pairs in the same order as the fixed-face list. -/
abbrev FixedMagneticAssignment :=
  List (Nat × Nat)

/-- Cartesian enumeration of the literal magnetic indices
`0, ..., boundary(id)` on every displayed fixed face. -/
def fixedFaceMagneticAssignments
    (boundary : EdgeLabelling) :
    List Nat → List FixedMagneticAssignment
  | [] => [[]]
  | id :: rest =>
      (List.range (boundary id + 1)).flatMap
        (fun magnetic =>
          (fixedFaceMagneticAssignments boundary rest).map
            (fun tail => (id, magnetic) :: tail))

private theorem length_flatMap_map_local
    {A B C : Type} (entries : List A) (tails : List B)
    (combine : A → B → C) :
    (entries.flatMap
        (fun entry => tails.map (combine entry))).length =
      entries.length * tails.length := by
  induction entries with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- The magnetic carrier has exactly the product of the SU(2)
representation dimensions. -/
theorem fixedFaceMagneticAssignments_length
    (boundary : EdgeLabelling) :
    ∀ ids : List Nat,
      (fixedFaceMagneticAssignments boundary ids).length =
        natListProduct (fun id => boundary id + 1) ids
  | [] => rfl
  | id :: rest => by
      unfold fixedFaceMagneticAssignments natListProduct
      rw [length_flatMap_map_local, List.length_range,
        fixedFaceMagneticAssignments_length boundary rest]

/-- The actual fixed-plane magnetic fiber for one BF4 boundary labelling. -/
def centralFixedMagneticCarrier
    (half : Nat) (boundary : EdgeLabelling) :
    List FixedMagneticAssignment :=
  fixedFaceMagneticAssignments boundary
    (centralFixedFaceIds half)

/-! ## 2. Pure heat-eigenvalue weight and magnetic reconstruction -/

/-- Product of the vacuum-normalized SU(2) heat-semigroup eigenvalues on a
displayed face list.  Unlike `slabFaceFactorOn`, it carries no representation
dimension. -/
def slabFaceHeatEigenvalueOn
    (w : Q') (physical : EdgeLabelling)
    (ids : List Nat) : Q' :=
  eliminateLinks
    (fun id => qpow w (c4 (physical id))) ids

/-- One magnetic fiber has the heat eigenvalue as the weight of each of its
`s+1` members. -/
def singleFaceMagneticMass
    (w : Q') (spin : Nat) : Q' :=
  Q'.ofNat (spin + 1) * qpow w (c4 spin)

theorem singleFaceMagneticMass_eq_coeffW
    (w : Q') (spin : Nat) :
    singleFaceMagneticMass w spin = coeffW w spin :=
  rfl

private theorem listQSum_const_eqv_length_mul
    {A : Type} (value : Q') :
    ∀ items : List A,
      listQSum (fun _ => value) items ≈
        Q'.ofNat items.length * value
  | [] => by
      refine Q'.eqv_trans _ 0 _ (Q'.eqv_refl 0) ?_
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ value
            Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv value))
  | _ :: tail => by
      refine Q'.eqv_trans _
        (value + Q'.ofNat tail.length * value) _ ?_ ?_
      · exact Q'.add_eqv_congr_left value _ _
          (listQSum_const_eqv_length_mul value tail)
      · have hcount :
          Q'.ofNat (List.length tail + 1) ≈
            Q'.ofNat tail.length + 1 :=
          Q'.ofNat_add_eqv tail.length 1
        refine Q'.eqv_trans _
          ((Q'.ofNat tail.length + 1) * value) _ ?_ ?_
        · refine Q'.eqv_trans _
            (1 * value + Q'.ofNat tail.length * value) _ ?_ ?_
          · exact Q'.add_eqv_congr_right _ _ _
              (Q'.eqv_symm (Q'.one_mul_eqv value))
          · refine Q'.eqv_trans _
              (Q'.ofNat tail.length * value + 1 * value) _
              (Q'.add_comm_eqv
                (1 * value)
                (Q'.ofNat tail.length * value)) ?_
            exact Q'.eqv_symm
              (Q'.add_mul_eqv
                (Q'.ofNat tail.length) 1 value)
        · rw [List.length_cons]
          refine Q'.mul_eqv_congr_right _ _ value ?_
          exact Q'.eqv_symm hcount

private theorem ofNat_natListProduct_eqv_dimensions
    (physical : EdgeLabelling) :
    ∀ ids : List Nat,
      Q'.ofNat
          (natListProduct
            (fun id => physical id + 1) ids) ≈
        eliminateLinks
          (fun id => dimQ (physical id)) ids
  | [] => by
      change Q'.ofNat 1 ≈ (1 : Q')
      exact Q'.eqv_refl 1
  | id :: rest => by
      unfold natListProduct eliminateLinks dimQ
      refine Q'.eqv_trans _
        (Q'.ofNat (physical id + 1) *
          Q'.ofNat
            (natListProduct
              (fun item => physical item + 1) rest)) _ ?_ ?_
      · exact Q'.eqv_symm
          (ofNat_mul_eqv
            (physical id + 1)
            (natListProduct
              (fun item => physical item + 1) rest))
      · exact Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_dimensions
            physical rest)

private theorem rearrange_pointwise_products
    (a b c d : Q') :
    (a * b) * (c * d) ≈
      (a * c) * (b * d) := by
  show ((a * b) * (c * d)).num *
      (((a * c) * (b * d)).den : Int) =
    ((a * c) * (b * d)).num *
      (((a * b) * (c * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem eliminateLinks_pointwise_mul
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      eliminateLinks
          (fun id => left id * right id) ids ≈
        eliminateLinks left ids *
          eliminateLinks right ids
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | id :: rest => by
      unfold eliminateLinks
      refine Q'.eqv_trans _
        ((left id * right id) *
          (eliminateLinks left rest *
            eliminateLinks right rest)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_pointwise_mul
            left right rest)
      · exact rearrange_pointwise_products
          (left id) (right id)
          (eliminateLinks left rest)
          (eliminateLinks right rest)

private theorem slabFaceFactorOn_eqv_dimension_mul_eigenvalue
    (w : Q') (K : Nat)
    (physical : EdgeLabelling) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → physical id < K + 1) →
      slabFaceFactorOn w K physical ids ≈
        eliminateLinks
            (fun id => dimQ (physical id)) ids *
          slabFaceHeatEigenvalueOn w physical ids
  | [], _ => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | id :: rest, hbounded => by
      unfold slabFaceFactorOn slabFaceHeatEigenvalueOn
        eliminateLinks
      rw [coeffAt_heatKernelPacket
        (hbounded id List.mem_cons_self)]
      refine Q'.eqv_trans _
        ((dimQ (physical id) *
            qpow w (c4 (physical id))) *
          (eliminateLinks
              (fun item =>
                dimQ (physical item)) rest *
            eliminateLinks
              (fun item =>
                qpow w (c4 (physical item))) rest)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (slabFaceFactorOn_eqv_dimension_mul_eigenvalue
            w K physical rest
            (fun item hitem =>
              hbounded item
                (List.mem_cons_of_mem id hitem)))
      · exact rearrange_pointwise_products
          (dimQ (physical id))
          (qpow w (c4 (physical id)))
          (eliminateLinks
            (fun item => dimQ (physical item)) rest)
          (eliminateLinks
            (fun item =>
              qpow w (c4 (physical item))) rest)

private theorem assembled_fixed_eq_boundary
    (half : Nat) (boundary : EdgeLabelling)
    {id : Nat} (hid : id ∈ centralFixedFaceIds half) :
    assembleReflectedSlabLabelling
        half zeroEdgeLabelling boundary zeroEdgeLabelling id =
      boundary id := by
  have hparts := mem_centralFixedFaceIds.mp hid
  exact assembleReflectedSlabLabelling_fixed
    hparts.1 hparts.2

private theorem eliminateLinks_congr_fixed_assembled
    (w : Q') (half : Nat)
    (boundary : EdgeLabelling) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
      slabFaceHeatEigenvalueOn
          w
          (assembleReflectedSlabLabelling
            half zeroEdgeLabelling boundary zeroEdgeLabelling)
          ids ≈
        slabFaceHeatEigenvalueOn w boundary ids
  | [], _ => Q'.eqv_refl 1
  | id :: rest, hfixed => by
      unfold slabFaceHeatEigenvalueOn eliminateLinks
      rw [assembled_fixed_eq_boundary
        half boundary (hfixed id List.mem_cons_self)]
      exact Q'.mul_eqv_congr_left _ _ _
        (eliminateLinks_congr_fixed_assembled
          w half boundary rest
          (fun item hitem =>
            hfixed item
              (List.mem_cons_of_mem id hitem)))

private theorem eliminateLinks_congr_on_local
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈
        eliminateLinks right ids
  | [], _ => Q'.eqv_refl 1
  | id :: rest, hpointwise =>
      q_mul_congr
        (hpointwise id List.mem_cons_self)
        (eliminateLinks_congr_on_local
          left right rest
          (fun item hitem =>
            hpointwise item
              (List.mem_cons_of_mem id hitem)))

/-- Summation over the literal magnetic fiber reconstructs the complete
fixed-face heat-kernel coefficient product exactly. -/
theorem centralFixedMagneticHeatWeight_total
    (w : Q') (K half : Nat)
    (boundary : EdgeLabelling)
    (hboundary :
      boundary ∈ centralBoundaryChannels K half) :
    listQSum
        (fun _ =>
          slabFaceHeatEigenvalueOn
            w boundary (centralFixedFaceIds half))
        (centralFixedMagneticCarrier half boundary) ≈
      slabFaceFactorOn w K
        (assembleReflectedSlabLabelling
          half zeroEdgeLabelling boundary zeroEdgeLabelling)
        (centralFixedFaceIds half) := by
  have hsound :=
    (boundedEdgeLabellings_sound K
      (centralFixedFaceIds half)
      boundary hboundary).1
  let assembled :=
    assembleReflectedSlabLabelling
      half zeroEdgeLabelling boundary zeroEdgeLabelling
  let ids := centralFixedFaceIds half
  refine Q'.eqv_trans _
    (Q'.ofNat
        (natListProduct
          (fun id => boundary id + 1) ids) *
      slabFaceHeatEigenvalueOn w boundary ids) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (listQSum_const_eqv_length_mul
        (slabFaceHeatEigenvalueOn w boundary ids)
        (centralFixedMagneticCarrier half boundary))
      (Q'.mul_eqv_congr_right _ _
        (slabFaceHeatEigenvalueOn w boundary ids)
        (Q'.eqv_of_eq
          (congrArg Q'.ofNat
            (fixedFaceMagneticAssignments_length
              boundary ids))))
  · refine Q'.eqv_trans _
      (eliminateLinks
          (fun id => dimQ (boundary id)) ids *
        slabFaceHeatEigenvalueOn w boundary ids) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _
        (slabFaceHeatEigenvalueOn w boundary ids)
        (ofNat_natListProduct_eqv_dimensions
          boundary ids)
    · refine Q'.eqv_trans _
        (eliminateLinks
            (fun id => dimQ (assembled id)) ids *
          slabFaceHeatEigenvalueOn w assembled ids) _ ?_ ?_
      · apply q_mul_congr
        · apply eliminateLinks_congr_on_local
          intro id hid
          dsimp only [assembled]
          rw [assembled_fixed_eq_boundary
            half boundary hid]
          exact Q'.eqv_refl _
        · exact Q'.eqv_symm
            (eliminateLinks_congr_fixed_assembled
              w half boundary ids
              (fun id hid => hid))
      · exact Q'.eqv_symm
          (slabFaceFactorOn_eqv_dimension_mul_eigenvalue
            w K assembled ids
            (fun id hid => by
              dsimp only [assembled]
              rw [assembled_fixed_eq_boundary
                half boundary hid]
              exact hsound id hid))

/-! ## 3. The enlarged physical Choi carrier -/

abbrev CentralFixedMagneticIntertwinerChannel :=
  EdgeLabelling ×
    (SlabFusionWitnessAssignment × FixedMagneticAssignment)

/-- Every fixed boundary, every accepted fixed-link intertwiner, and every
literal fixed-face magnetic assignment. -/
def centralFixedMagneticIntertwinerChannels
    (K half : Nat) :
    List CentralFixedMagneticIntertwinerChannel :=
  (centralBoundaryChannels K half).flatMap
    (fun boundary =>
      (centralFixedFineIntertwinerCarrier
        K half boundary).flatMap
        (fun witness =>
          (centralFixedMagneticCarrier half boundary).map
            (fun magnetic =>
              (boundary, (witness, magnetic)))))

/-- On the enlarged carrier the physical fixed-plane insertion is the pure
heat-semigroup eigenweight.  The dimension is represented by the magnetic
fiber cardinality. -/
def centralFixedMagneticIntertwinerWeight
    (w : Q') (half : Nat)
    (channel : CentralFixedMagneticIntertwinerChannel) : Q' :=
  slabFaceHeatEigenvalueOn
    w channel.1 (centralFixedFaceIds half)

def centralFixedMagneticIntertwinerHalfAmplitude
    (w : Q') (K half : Nat)
    (state : EdgeLabelling)
    (channel : CentralFixedMagneticIntertwinerChannel) : Q' :=
  centralHalfAmplitude w K half state channel.1

/-- Integrating the magnetic refinement above one fixed-link witness
recovers that witness's genuine physical spatial insertion. -/
theorem centralFixedMagneticFiber_total
    (w : Q') (K half : Nat)
    (boundary : EdgeLabelling)
    (hboundary :
      boundary ∈ centralBoundaryChannels K half)
    (witness : SlabFusionWitnessAssignment) :
    listQSum
        (fun _ =>
          slabFaceHeatEigenvalueOn
            w boundary (centralFixedFaceIds half))
        (centralFixedMagneticCarrier half boundary) ≈
      centralFixedFineIntertwinerSpatialWeight
        w K half boundary witness := by
  unfold centralFixedFineIntertwinerSpatialWeight
    centralFixedFineIntertwinerRawWeight
  exact Q'.eqv_trans _ _ _
    (centralFixedMagneticHeatWeight_total
      w K half boundary hboundary)
    (Q'.eqv_symm
      (Q'.mul_one_eqv
        (slabFaceFactorOn w K
          (assembleReflectedSlabLabelling
            half zeroEdgeLabelling boundary zeroEdgeLabelling)
          (centralFixedFaceIds half))))

/-- Conditional integration over both enlarged fibers gives exactly the
genuine fixed-interface BF4 weight. -/
theorem centralFixedMagneticIntertwinerWeight_total
    (w : Q') (K half : Nat)
    (boundary : EdgeLabelling)
    (hboundary :
      boundary ∈ centralBoundaryChannels K half) :
    listQSum
        (fun channel =>
          centralFixedMagneticIntertwinerWeight
            w half channel)
        ((centralFixedFineIntertwinerCarrier
            K half boundary).flatMap
          (fun witness =>
            (centralFixedMagneticCarrier half boundary).map
              (fun magnetic =>
                (boundary, (witness, magnetic))))) ≈
      centralBoundaryWeight w K half boundary := by
  refine Q'.eqv_trans _
    (listQSum
      (fun witness =>
        listQSum
          (fun _ =>
            slabFaceHeatEigenvalueOn
              w boundary (centralFixedFaceIds half))
          (centralFixedMagneticCarrier half boundary))
      (centralFixedFineIntertwinerCarrier
        K half boundary)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_flatMap _ _ _) ?_
    apply listQSum_congr
    intro witness
    rw [listQSum_map]
    exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      (listQSum
        (centralFixedFineIntertwinerSpatialWeight
          w K half boundary)
        (centralFixedFineIntertwinerCarrier
          K half boundary)) _ ?_ ?_
    · apply listQSum_congr
      intro witness
      exact centralFixedMagneticFiber_total
        w K half boundary hboundary witness
    · exact centralFixedFineIntertwinerSpatialWeight_total
        w K half boundary

def centralFixedMagneticIntertwinerChoiEntry
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) : Q' :=
  weightedGram
    (centralFixedMagneticIntertwinerChannels K half)
    (centralFixedMagneticIntertwinerWeight w half)
    (centralFixedMagneticIntertwinerHalfAmplitude
      w K half)
    left right

private theorem weightedGram_flatMap_fiber_total
    {State Base Channel : Type}
    (bases : List Base)
    (fiber : Base → List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (baseWeight : Base → Q')
    (baseAmplitude : State → Base → Q')
    (hamplitude :
      ∀ state base channel,
        channel ∈ fiber base →
          amplitude state channel ≈
            baseAmplitude state base)
    (htotal :
      ∀ base, base ∈ bases →
        listQSum weight (fiber base) ≈
          baseWeight base)
    (left right : State) :
    weightedGram
        (bases.flatMap fiber)
        weight amplitude left right ≈
      weightedGram
        bases baseWeight baseAmplitude left right := by
  unfold weightedGram
  refine Q'.eqv_trans _
    (listQSum
      (fun base =>
        listQSum
          (fun channel =>
            weight channel *
              (amplitude left channel *
                amplitude right channel))
          (fiber base))
      bases) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr_on
    intro base hbase
    refine Q'.eqv_trans _
      (listQSum weight (fiber base) *
        (baseAmplitude left base *
          baseAmplitude right base)) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun channel =>
            weight channel *
              (baseAmplitude left base *
                baseAmplitude right base))
          (fiber base)) _ ?_ ?_
      · apply listQSum_congr_on
        intro channel hchannel
        exact Q'.mul_eqv_congr_left
          (weight channel) _ _
          (q_mul_congr
            (hamplitude left base channel hchannel)
            (hamplitude right base channel hchannel))
      · exact listQSum_mul_right _ _ _
    · exact Q'.mul_eqv_congr_right _ _
        (baseAmplitude left base *
          baseAmplitude right base)
        (htotal base hbase)

/-- Integrating the enlarged fixed-plane carrier gives the old fixed-link
Choi entry exactly. -/
theorem centralFixedMagneticIntertwinerChoiEntry_eq
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) :
    centralFixedMagneticIntertwinerChoiEntry
        w K half left right ≈
      weightedGram
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half)
        left right := by
  unfold centralFixedMagneticIntertwinerChoiEntry
    centralFixedMagneticIntertwinerChannels
  exact weightedGram_flatMap_fiber_total
    (centralBoundaryChannels K half)
    (fun boundary =>
      (centralFixedFineIntertwinerCarrier
          K half boundary).flatMap
        (fun witness =>
          (centralFixedMagneticCarrier half boundary).map
            (fun magnetic =>
              (boundary, (witness, magnetic)))))
    (centralFixedMagneticIntertwinerWeight w half)
    (centralFixedMagneticIntertwinerHalfAmplitude
      w K half)
    (centralBoundaryWeight w K half)
    (centralHalfAmplitude w K half)
    (fun state boundary channel hchannel => by
      obtain ⟨witness, _hwitness, hmagneticMap⟩ :=
        List.mem_flatMap.mp hchannel
      obtain ⟨magnetic, _hmagnetic, hchannelEq⟩ :=
        List.mem_map.mp hmagneticMap
      rw [← hchannelEq]
      unfold centralFixedMagneticIntertwinerHalfAmplitude
      exact Q'.eqv_refl _)
    (fun boundary hboundary =>
      centralFixedMagneticIntertwinerWeight_total
        w K half boundary hboundary)
    left right

/-- **Exact physical identification on the magnetically enlarged carrier.** -/
theorem centralPhysicalReflectedKernel_eq_fixedMagneticChoi
    (w : Q') {K half : Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    centralPhysicalReflectedKernel w K half left right ≈
      centralFixedMagneticIntertwinerChoiEntry
        w K half left right := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_eq_weightedGram
      w hleft hright)
    (Q'.eqv_symm
      (centralFixedMagneticIntertwinerChoiEntry_eq
        w K half left right))

/-! ## 4. Spacing-uniform pointwise order and CP -/

theorem centralFixedMagneticIntertwinerWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (half : Nat)
    (channel : CentralFixedMagneticIntertwinerChannel) :
    (0 : Q') ≤
      centralFixedMagneticIntertwinerWeight
        w half channel := by
  unfold centralFixedMagneticIntertwinerWeight
    slabFaceHeatEigenvalueOn
  induction centralFixedFaceIds half with
  | nil => exact Q'.zero_le_one
  | cons id rest ih =>
      exact Q'.mul_nonneg _ _
        (qpow_nonneg w hw (c4 (channel.1 id)))
        ih

/-- The physical/refence lower factor is exactly one, independently of
spacing, cutoff, boundary labels, and the size of the enlarged carrier. -/
theorem centralFixedMagneticWeight_unit_lower
    (w : Q') (half : Nat)
    (channel : CentralFixedMagneticIntertwinerChannel) :
    (1 : Q') *
        centralFixedMagneticIntertwinerWeight
          w half channel ≤
      centralFixedMagneticIntertwinerWeight
        w half channel := by
  exact Q'.le_of_eqv
    (Q'.one_mul_eqv _)

/-- The matching upper factor is also exactly one. -/
theorem centralFixedMagneticWeight_unit_upper
    (w : Q') (half : Nat)
    (channel : CentralFixedMagneticIntertwinerChannel) :
    centralFixedMagneticIntertwinerWeight
        w half channel ≤
      (1 : Q') *
        centralFixedMagneticIntertwinerWeight
          w half channel := by
  exact Q'.ge_of_eqv
    (Q'.one_mul_eqv _)

/-- Constructive unit Harnack/order window on the genuine enlarged physical
carrier.  No spacing-dependent constant remains in the pointwise ratio. -/
def centralFixedMagneticUnitWindow
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    NonnegativeGramReferenceWindow
      (centralFixedMagneticIntertwinerChannels K half)
      (centralFixedMagneticIntertwinerWeight w half)
      (centralFixedMagneticIntertwinerWeight w half) where
  lower := 1
  upper := 1
  lower_nonnegative := Q'.zero_le_one
  upper_nonnegative := Q'.zero_le_one
  reference_nonnegative := by
    intro channel _
    exact centralFixedMagneticIntertwinerWeight_nonnegative
      hw half channel
  lower_bound := by
    intro channel _
    exact centralFixedMagneticWeight_unit_lower
      w half channel
  upper_bound := by
    intro channel _
    exact centralFixedMagneticWeight_unit_upper
      w half channel

def centralFixedMagneticChoiQuadratic
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling → Q') : Q' :=
  weightedGramQuadratic
    (centralHalfStates K half)
    (centralFixedMagneticIntertwinerChannels K half)
    (centralFixedMagneticIntertwinerWeight w half)
    (centralFixedMagneticIntertwinerHalfAmplitude
      w K half)
    coefficient

theorem centralFixedMagneticChoiQuadratic_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (coefficient : EdgeLabelling → Q') :
    (0 : Q') ≤
      centralFixedMagneticChoiQuadratic
        w K half coefficient := by
  unfold centralFixedMagneticChoiQuadratic
  exact weightedGramQuadratic_nonnegative
    (centralHalfStates K half)
    (centralFixedMagneticIntertwinerChannels K half)
    (centralFixedMagneticIntertwinerWeight w half)
    (centralFixedMagneticIntertwinerHalfAmplitude
      w K half)
    coefficient
    (fun channel _ =>
      centralFixedMagneticIntertwinerWeight_nonnegative
        hw half channel)

/-- The complete quadratic order window is `[1,1]` on every spacing and
cutoff. -/
theorem centralFixedMagneticChoi_unit_sandwich
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (coefficient : EdgeLabelling → Q') :
    (1 : Q') *
        centralFixedMagneticChoiQuadratic
          w K half coefficient ≤
      centralFixedMagneticChoiQuadratic
          w K half coefficient ∧
    centralFixedMagneticChoiQuadratic
          w K half coefficient ≤
      (1 : Q') *
        centralFixedMagneticChoiQuadratic
          w K half coefficient := by
  exact
    (centralFixedMagneticUnitWindow hw K half).quadratic_sandwich
      (centralHalfStates K half)
      (centralFixedMagneticIntertwinerChannels K half)
      (centralFixedMagneticIntertwinerWeight w half)
      (centralFixedMagneticIntertwinerWeight w half)
      (centralFixedMagneticIntertwinerHalfAmplitude
        w K half)
      coefficient

/-! ## 5. Magnetic-carrier growth is absorbed by Mehler decay -/

/-- One magnetic fiber is bounded by the standard degree-two SU(2)
pointwise heat majorant.  This is the exact carrier-growth/entry-decay
comparison: the carrier contributes one factor `s+1`, while the majorant
already pays two. -/
theorem singleFaceMagneticMass_le_pointwiseHeatMajorant
    {w : Q'} (hw : (0 : Q') ≤ w)
    (spin : Nat) :
    singleFaceMagneticMass w spin ≤
      pointwiseHeatMajorant w spin := by
  unfold singleFaceMagneticMass
    pointwiseHeatMajorant tailTerm
  have hdim :
      Q'.ofNat (spin + 1) ≤
        Q'.ofNat ((spin + 1) ^ 2) := by
    apply Q'.ofNat_le_ofNat
    have hpos : 1 ≤ spin + 1 := by omega
    simpa [Nat.pow_two] using
      (Nat.le_mul_of_pos_right (spin + 1) hpos)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    hdim (qpow_nonneg w hw (c4 spin))

/-- Past the explicit spacing-dependent label cutoff, magnetic carrier growth
is dominated by the same geometric Mehler envelope as the completed SU(2)
heat kernel. -/
theorem shiftedSingleFaceMagneticMass_le_geometric
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (offset : Nat) :
    singleFaceMagneticMass
        w (spacingLabelCutoff w + offset) ≤
      spacingTailHead w *
        spacingTailRatio w ^ offset := by
  exact Q'.le_trans' _ _ _
    (singleFaceMagneticMass_le_pointwiseHeatMajorant
      (Q'.le_of_lt hw0)
      (spacingLabelCutoff w + offset))
    (shiftedMajorant_le_geometric hw0 hw1 offset)

#print axioms fixedFaceMagneticAssignments_length
#print axioms singleFaceMagneticMass_eq_coeffW
#print axioms centralFixedMagneticHeatWeight_total
#print axioms centralFixedMagneticFiber_total
#print axioms centralFixedMagneticIntertwinerWeight_total
#print axioms centralFixedMagneticIntertwinerChoiEntry_eq
#print axioms centralPhysicalReflectedKernel_eq_fixedMagneticChoi
#print axioms centralFixedMagneticIntertwinerWeight_nonnegative
#print axioms centralFixedMagneticWeight_unit_lower
#print axioms centralFixedMagneticWeight_unit_upper
#print axioms centralFixedMagneticUnitWindow
#print axioms centralFixedMagneticChoiQuadratic_nonnegative
#print axioms centralFixedMagneticChoi_unit_sandwich
#print axioms singleFaceMagneticMass_le_pointwiseHeatMajorant
#print axioms shiftedSingleFaceMagneticMass_le_geometric

end YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
