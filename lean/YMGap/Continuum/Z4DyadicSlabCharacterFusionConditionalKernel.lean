/-
# A literal character-fusion conditional kernel on the corrected dyadic slab

The four-label slab packet is the smallest face carrier that does not collapse
SU(2) twice-spin labels to centre parity.  A single coarse character still
forgets how the two reflected halves fuse.  This file therefore retains the
two pair channels together with the final coarse character:

    ((xL, xR), s).

For a packet `(a,b,c,d)`, its unnormalised local weight is the literal finite
Clebsch--Gordan character sum term

    coeffW w s * N_ab^xL * N_cd^xR * N_xL,xR^s.

All factors are existing exact rationals.  The row denominator is the finite
sum of these terms, and is strictly positive because the stretched channel
`xL=a+b`, `xR=c+d`, `s=a+b+c+d` occurs with multiplicity one.  Division by
that derived denominator gives a positive, exactly row-normalised conditional
kernel.  Spatial half-time reflection exchanges `(a,b)` with `(c,d)` and
simultaneously exchanges `xL` with `xR`; temporal fibres are fixed.  Hence the
kernel intertwines corrected-slab reflection exactly.

This is a genuine local character/fusion kernel and is source-dependent.  It
is not yet an identification with the full four-dimensional block Gibbs law:
neighbouring faces still have to be glued through shared link holonomies and
their production fusion multiplicities before an iteratable physical RG step
is obtained.
-/

import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.FusionResidualBound
import YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

namespace YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The finite pair-channel target -/

/-- Left pair channel, right pair channel, and final coarse character. -/
abbrev PairChannelState := (Nat × Nat) × Nat

def pairChannelStateSpace (cutoff : Nat) : List PairChannelState :=
  cartesian
    (cartesian (List.range (2 * cutoff + 1))
      (List.range (2 * cutoff + 1)))
    (List.range (4 * cutoff + 1))

theorem mem_pairChannelStateSpace_iff
    (cutoff : Nat) (state : PairChannelState) :
    state ∈ pairChannelStateSpace cutoff ↔
      state.1.1 ≤ 2 * cutoff ∧ state.1.2 ≤ 2 * cutoff ∧
        state.2 ≤ 4 * cutoff := by
  unfold pairChannelStateSpace
  constructor
  · intro hstate
    have hparts := (mem_cartesian_iff _ _ state).mp hstate
    have hpairs := (mem_cartesian_iff _ _ state.1).mp hparts.1
    simp only [List.mem_range] at hpairs hparts
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hleft, hright, hcoarse⟩
    apply (mem_cartesian_iff _ _ _).mpr
    constructor
    · exact (mem_cartesian_iff _ _ _).mpr
        ⟨List.mem_range.mpr (by omega),
          List.mem_range.mpr (by omega)⟩
    · exact List.mem_range.mpr (by omega)

private theorem rangeNodupLocal (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = k := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl k)

theorem pairChannelStateSpace_nodup (cutoff : Nat) :
    (pairChannelStateSpace cutoff).Nodup := by
  unfold pairChannelStateSpace
  apply cartesian_nodup
  · exact cartesian_nodup _ _ (rangeNodupLocal _) (rangeNodupLocal _)
  · exact rangeNodupLocal _

def reflectPairChannelState
    (plane : Z4Plane) (state : PairChannelState) : PairChannelState :=
  match plane with
  | .p01 | .p02 | .p12 => ((state.1.2, state.1.1), state.2)
  | .p03 | .p13 | .p23 => state

theorem reflectPairChannelState_involutive
    (plane : Z4Plane) (state : PairChannelState) :
    reflectPairChannelState plane
        (reflectPairChannelState plane state) = state := by
  cases plane <;> cases state with
  | mk pair coarse => cases pair <;> rfl

theorem reflectPairChannelState_mem
    {cutoff : Nat} {state : PairChannelState}
    (hstate : state ∈ pairChannelStateSpace cutoff)
    (plane : Z4Plane) :
    reflectPairChannelState plane state ∈
      pairChannelStateSpace cutoff := by
  have hbounds := (mem_pairChannelStateSpace_iff cutoff state).mp hstate
  apply (mem_pairChannelStateSpace_iff cutoff _).mpr
  cases plane <;> simp only [reflectPairChannelState]
  all_goals omega

/-! ## 2. Literal character weights and a positive row denominator -/

/-- The exact local character/fusion summand.  Each `fusionInd` is the
derived SU(2) Clebsch--Gordan multiplicity (zero or one). -/
def packetPairChannelRawWeight
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState) : Q' :=
  coeffW w state.2 *
    (fusionInd packet.spin0 packet.spin1 state.1.1 *
      (fusionInd packet.spin2 packet.spin3 state.1.2 *
        fusionInd state.1.1 state.1.2 state.2))

theorem packetPairChannelRawWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (packet : FaceSpinPacket) (state : PairChannelState) :
    (0 : Q') ≤ packetPairChannelRawWeight w packet state := by
  unfold packetPairChannelRawWeight
  exact Q'.mul_nonneg _ _
    (coeffW_nonneg hw state.2)
    (Q'.mul_nonneg _ _
      (fusionInd_nonneg packet.spin0 packet.spin1 state.1.1)
      (Q'.mul_nonneg _ _
        (fusionInd_nonneg packet.spin2 packet.spin3 state.1.2)
        (fusionInd_nonneg state.1.1 state.1.2 state.2)))

def packetPairChannelPartition
    (w : Q') (cutoff : Nat) (packet : FaceSpinPacket) : Q' :=
  listQSum (packetPairChannelRawWeight w packet)
    (pairChannelStateSpace cutoff)

theorem fusionInd_add_eq_one (a b : Nat) :
    fusionInd a b (a + b) = 1 := by
  unfold fusionInd
  rw [if_pos]
  exact (fusionOK_iff_ladder a b (a + b)).2
    ⟨0, Nat.zero_le _, Nat.zero_le _, by omega⟩

theorem stretchedPairChannel_mem
    (cutoff : Nat) (packet : FaceSpinPacket)
    (hpacket : packet ∈ faceSpinPacketStateSpace cutoff) :
    ((packet.spin0 + packet.spin1,
        packet.spin2 + packet.spin3),
      packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3) ∈
      pairChannelStateSpace cutoff := by
  obtain ⟨spin0, spin1, spin2, spin3⟩ := packet
  have hbounds :=
    (mem_faceSpinPacketStateSpace_iff cutoff
      (⟨spin0, spin1, spin2, spin3⟩ : FaceSpinPacket)).mp hpacket
  change spin0 ≤ cutoff ∧ spin1 ≤ cutoff ∧
    spin2 ≤ cutoff ∧ spin3 ≤ cutoff at hbounds
  apply (mem_pairChannelStateSpace_iff cutoff _).mpr
  have hleft : spin0 + spin1 ≤ 2 * cutoff := by
    rw [Nat.two_mul]
    exact Nat.add_le_add hbounds.1 hbounds.2.1
  have hright : spin2 + spin3 ≤ 2 * cutoff := by
    rw [Nat.two_mul]
    exact Nat.add_le_add hbounds.2.2.1 hbounds.2.2.2
  have hfour : 2 * cutoff + 2 * cutoff = 4 * cutoff := by
    calc
      2 * cutoff + 2 * cutoff = (2 + 2) * cutoff :=
        (Nat.add_mul 2 2 cutoff).symm
      _ = 4 * cutoff := by rfl
  refine ⟨hleft, hright, ?_⟩
  rw [← hfour]
  simpa only [Nat.add_assoc] using Nat.add_le_add hleft hright

theorem stretchedPairChannelRawWeight_pos
    {w : Q'} (hw : (0 : Q') < w)
    (packet : FaceSpinPacket) :
    (0 : Q') < packetPairChannelRawWeight w packet
      ((packet.spin0 + packet.spin1,
          packet.spin2 + packet.spin3),
        packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3) := by
  unfold packetPairChannelRawWeight
  change (0 : Q') <
    coeffW w
        (packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3) *
      (fusionInd packet.spin0 packet.spin1
          (packet.spin0 + packet.spin1) *
        (fusionInd packet.spin2 packet.spin3
            (packet.spin2 + packet.spin3) *
          fusionInd (packet.spin0 + packet.spin1)
            (packet.spin2 + packet.spin3)
            (packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3)))
  rw [fusionInd_add_eq_one, fusionInd_add_eq_one]
  have htop :
      fusionInd (packet.spin0 + packet.spin1)
          (packet.spin2 + packet.spin3)
          (packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3) = 1 := by
    rw [show packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3 =
      (packet.spin0 + packet.spin1) + (packet.spin2 + packet.spin3) by omega]
    exact fusionInd_add_eq_one _ _
  rw [htop]
  exact Q'.mul_pos
    (YMGap.Continuum.FusionResidualBound.coeffW_pos hw _)
    (by decide)

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, h => absurd h List.not_mem_nil
  | head :: tail, x, h => by
      rcases List.mem_cons.mp h with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

theorem packetPairChannelPartition_pos
    {w : Q'} (hw : (0 : Q') < w)
    (cutoff : Nat) (packet : FaceSpinPacket)
    (hpacket : packet ∈ faceSpinPacketStateSpace cutoff) :
    (0 : Q') < packetPairChannelPartition w cutoff packet := by
  have hterm := stretchedPairChannelRawWeight_pos hw packet
  have hle :
      packetPairChannelRawWeight w packet
          ((packet.spin0 + packet.spin1,
              packet.spin2 + packet.spin3),
            packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3) ≤
        packetPairChannelPartition w cutoff packet := by
    unfold packetPairChannelPartition
    exact listQSum_member_le_local
      (packetPairChannelRawWeight w packet)
      (packetPairChannelRawWeight_nonnegative (Q'.le_of_lt hw) packet)
      _ (stretchedPairChannel_mem cutoff packet hpacket)
  exact Q'.pos_of_lt_of_le hterm hle

/-! ## 3. Exact row normalization -/

abbrev BoundedFaceSpinPacket (cutoff : Nat) :=
  {packet : FaceSpinPacket //
    packet ∈ faceSpinPacketStateSpace cutoff}

def packetPairChannelConditionalKernel
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : BoundedFaceSpinPacket cutoff)
    (target : PairChannelState) : Q' :=
  Q'.divPos
    (packetPairChannelRawWeight w source.val target)
    (packetPairChannelPartition w cutoff source.val)
    (packetPairChannelPartition_pos hw cutoff source.val source.property)

theorem packetPairChannelConditionalKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : BoundedFaceSpinPacket cutoff)
    (target : PairChannelState) :
    (0 : Q') ≤
      packetPairChannelConditionalKernel w hw cutoff source target := by
  unfold packetPairChannelConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (packetPairChannelRawWeight_nonnegative
      (Q'.le_of_lt hw) source.val target)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem packetPairChannelConditionalKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : BoundedFaceSpinPacket cutoff) :
    listQSum
        (packetPairChannelConditionalKernel w hw cutoff source)
        (pairChannelStateSpace cutoff) ≈ 1 := by
  unfold packetPairChannelConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (packetPairChannelPartition w cutoff source.val *
      Q'.recipPos (packetPairChannelPartition w cutoff source.val)
        (packetPairChannelPartition_pos hw cutoff source.val source.property)) _
    (listQSum_mul_right
      (packetPairChannelRawWeight w source.val)
      (Q'.recipPos (packetPairChannelPartition w cutoff source.val)
        (packetPairChannelPartition_pos hw cutoff source.val source.property))
      (pairChannelStateSpace cutoff))
    (Q'.mul_recipPos_eqv _
      (packetPairChannelPartition_pos hw cutoff source.val source.property))

/-! ## 4. Exact reflection intertwining -/

theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab]

private theorem mul_swap_nested (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  exact Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ ((b * a) * c) _
      (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

private theorem packetPairChannelRawWeight_swap_halves
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState) :
    packetPairChannelRawWeight w
        ⟨packet.spin2, packet.spin3, packet.spin0, packet.spin1⟩
        ((state.1.2, state.1.1), state.2) ≈
      packetPairChannelRawWeight w packet state := by
  unfold packetPairChannelRawWeight
  apply Q'.mul_eqv_congr_left (coeffW w state.2)
  refine Q'.eqv_trans _
    (fusionInd packet.spin2 packet.spin3 state.1.2 *
      (fusionInd packet.spin0 packet.spin1 state.1.1 *
        fusionInd state.1.1 state.1.2 state.2)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_of_eq
          (fusionInd_comm state.1.2 state.1.1 state.2)))
  · exact mul_swap_nested
      (fusionInd packet.spin2 packet.spin3 state.1.2)
      (fusionInd packet.spin0 packet.spin1 state.1.1)
      (fusionInd state.1.1 state.1.2 state.2)

theorem packetPairChannelRawWeight_reflection
    (w : Q') (plane : Z4Plane)
    (packet : FaceSpinPacket) (state : PairChannelState) :
    packetPairChannelRawWeight w
        (reflectFaceSpinPacket plane packet)
        (reflectPairChannelState plane state) ≈
      packetPairChannelRawWeight w packet state := by
  cases plane with
  | p01 => exact packetPairChannelRawWeight_swap_halves w packet state
  | p02 => exact packetPairChannelRawWeight_swap_halves w packet state
  | p03 => exact Q'.eqv_refl _
  | p12 => exact packetPairChannelRawWeight_swap_halves w packet state
  | p13 => exact Q'.eqv_refl _
  | p23 => exact Q'.eqv_refl _

/-- The same literal partition written as its three nested character sums. -/
def packetPairChannelTripleSum
    (w : Q') (cutoff : Nat) (packet : FaceSpinPacket) : Q' :=
  fsum (fun x =>
    fsum (fun y =>
      fsum (fun s =>
        packetPairChannelRawWeight w packet ((x, y), s))
        (4 * cutoff + 1))
      (2 * cutoff + 1))
    (2 * cutoff + 1)

private theorem listQSum_cartesian_nested
    {A B : Type} (weight : A × B → Q')
    (xs : List A) (ys : List B) :
    listQSum weight (cartesian xs ys) ≈
      listQSum (fun x =>
        listQSum (fun y => weight (x, y)) ys) xs := by
  unfold cartesian
  exact Q'.eqv_trans _
    (listQSum (fun x =>
      listQSum weight (ys.map fun y => (x, y))) xs) _
    (listQSum_flatMap weight (fun x => ys.map fun y => (x, y)) xs)
    (listQSum_congr_on _ _ xs (fun x _ =>
      Q'.eqv_of_eq (listQSum_map weight (fun y => (x, y)) ys)))

private theorem nestedRangeSum_eqv_tripleFsum
    (weight : PairChannelState → Q') (pairCutoff coarseCutoff : Nat) :
    listQSum
        (fun x => listQSum
          (fun y => listQSum
            (fun s => weight ((x, y), s))
            (List.range coarseCutoff))
          (List.range pairCutoff))
        (List.range pairCutoff) ≈
      fsum (fun x => fsum
        (fun y => fsum
          (fun s => weight ((x, y), s)) coarseCutoff)
        pairCutoff)
      pairCutoff := by
  refine Q'.eqv_trans _
    (listQSum
      (fun x => listQSum
        (fun y => fsum
          (fun s => weight ((x, y), s)) coarseCutoff)
        (List.range pairCutoff))
      (List.range pairCutoff)) _ ?_ ?_
  · apply listQSum_congr_on
    intro x _
    apply listQSum_congr_on
    intro y _
    exact listQSum_range_eq_fsum _ coarseCutoff
  refine Q'.eqv_trans _
    (listQSum
      (fun x => fsum
        (fun y => fsum
          (fun s => weight ((x, y), s)) coarseCutoff)
        pairCutoff)
      (List.range pairCutoff)) _ ?_ ?_
  · apply listQSum_congr_on
    intro x _
    exact listQSum_range_eq_fsum _ pairCutoff
  exact listQSum_range_eq_fsum _ pairCutoff

theorem packetPairChannelPartition_eqv_tripleSum
    (w : Q') (cutoff : Nat) (packet : FaceSpinPacket) :
    packetPairChannelPartition w cutoff packet ≈
      packetPairChannelTripleSum w cutoff packet := by
  unfold packetPairChannelPartition pairChannelStateSpace
    packetPairChannelTripleSum
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => listQSum
        (fun s => packetPairChannelRawWeight w packet (pair, s))
        (List.range (4 * cutoff + 1)))
      (cartesian (List.range (2 * cutoff + 1))
        (List.range (2 * cutoff + 1)))) _ ?_ ?_
  · exact listQSum_cartesian_nested _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun x => listQSum
        (fun y => listQSum
          (fun s => packetPairChannelRawWeight w packet ((x, y), s))
          (List.range (4 * cutoff + 1)))
        (List.range (2 * cutoff + 1)))
      (List.range (2 * cutoff + 1))) _ ?_ ?_
  · exact listQSum_cartesian_nested _ _ _
  exact nestedRangeSum_eqv_tripleFsum
    (packetPairChannelRawWeight w packet)
    (2 * cutoff + 1) (4 * cutoff + 1)

private theorem packetPairChannelTripleSum_swap_halves
    (w : Q') (cutoff : Nat) (packet : FaceSpinPacket) :
    packetPairChannelTripleSum w cutoff
        ⟨packet.spin2, packet.spin3, packet.spin0, packet.spin1⟩ ≈
      packetPairChannelTripleSum w cutoff packet := by
  unfold packetPairChannelTripleSum
  let pairBound := 2 * cutoff + 1
  let coarseBound := 4 * cutoff + 1
  let original := fun x y =>
    fsum (fun s => packetPairChannelRawWeight w packet ((x, y), s))
      coarseBound
  refine Q'.eqv_trans _
    (fsum (fun x => fsum (fun y => original y x) pairBound)
      pairBound) _ ?_ ?_
  · apply fsum_eqv_congr
    intro x
    apply fsum_eqv_congr
    intro y
    apply fsum_eqv_congr
    intro s
    exact packetPairChannelRawWeight_swap_halves w packet ((y, x), s)
  · exact Q'.eqv_symm (fsum_swap original pairBound pairBound)

theorem packetPairChannelPartition_reflection
    (w : Q') (cutoff : Nat) (plane : Z4Plane)
    (packet : FaceSpinPacket) :
    packetPairChannelPartition w cutoff
        (reflectFaceSpinPacket plane packet) ≈
      packetPairChannelPartition w cutoff packet := by
  refine Q'.eqv_trans _
    (packetPairChannelTripleSum w cutoff
      (reflectFaceSpinPacket plane packet)) _
    (packetPairChannelPartition_eqv_tripleSum w cutoff _)
    ?_
  refine Q'.eqv_trans _
    (packetPairChannelTripleSum w cutoff packet) _ ?_
    (Q'.eqv_symm
      (packetPairChannelPartition_eqv_tripleSum w cutoff packet))
  cases plane with
  | p01 => exact packetPairChannelTripleSum_swap_halves w cutoff packet
  | p02 => exact packetPairChannelTripleSum_swap_halves w cutoff packet
  | p03 => exact Q'.eqv_refl _
  | p12 => exact packetPairChannelTripleSum_swap_halves w cutoff packet
  | p13 => exact Q'.eqv_refl _
  | p23 => exact Q'.eqv_refl _

def reflectBoundedFaceSpinPacket
    (cutoff : Nat) (plane : Z4Plane)
    (source : BoundedFaceSpinPacket cutoff) :
    BoundedFaceSpinPacket cutoff :=
  ⟨reflectFaceSpinPacket plane source.val,
    reflectFaceSpinPacket_mem_stateSpace source.property plane⟩

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (haEq : a ≈ a') (hbEq : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hbEq))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) haEq))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hbEq)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm haEq)))

theorem packetPairChannelConditionalKernel_reflection_equivariant
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (plane : Z4Plane) (source : BoundedFaceSpinPacket cutoff)
    (target : PairChannelState) :
    packetPairChannelConditionalKernel w hw cutoff
        (reflectBoundedFaceSpinPacket cutoff plane source)
        (reflectPairChannelState plane target) ≈
      packetPairChannelConditionalKernel w hw cutoff source target := by
  unfold packetPairChannelConditionalKernel
  exact divPos_eqv_congr_local
    (packetPairChannelPartition_pos hw cutoff
      (reflectFaceSpinPacket plane source.val)
      (reflectFaceSpinPacket_mem_stateSpace source.property plane))
    (packetPairChannelPartition_pos hw cutoff source.val source.property)
    (packetPairChannelRawWeight_reflection w plane source.val target)
    (packetPairChannelPartition_reflection w cutoff plane source.val)

/-! ## 5. Specialization to the actual corrected-slab dyadic fibre -/

def slabBoundedFaceSpinPacket
    (cutoff : Nat) (fineSpin : Z4Plaq → Nat)
    (hbounded : ∀ plaquette, fineSpin plaquette ≤ cutoff)
    (coarsePlaquette : Z4Plaq) : BoundedFaceSpinPacket cutoff :=
  ⟨dyadicFaceSpinPacket fineSpin coarsePlaquette,
    dyadicFaceSpinPacket_mem_stateSpace
      cutoff fineSpin hbounded coarsePlaquette⟩

theorem slabBoundedFaceSpinPacket_reflection
    (cutoff extent : Nat) (fineSpin : Z4Plaq → Nat)
    (hbounded : ∀ plaquette, fineSpin plaquette ≤ cutoff)
    (coarsePlaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent coarsePlaquette) :
    slabBoundedFaceSpinPacket cutoff
        (reflectSlabFaceSpinLabelling (dyadicSlabFineExtent extent)
          fineSpin)
        (fun plaquette =>
          hbounded (timeReflectPlaquette
            (dyadicSlabFineExtent extent) plaquette))
        coarsePlaquette =
      reflectBoundedFaceSpinPacket cutoff coarsePlaquette.2
        (slabBoundedFaceSpinPacket cutoff fineSpin hbounded
          (timeReflectPlaquette extent coarsePlaquette)) := by
  apply Subtype.ext
  exact dyadicFaceSpinPacket_reflection
    extent fineSpin coarsePlaquette hadmissible

def dyadicSlabPairChannelConditionalKernel
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (fineSpin : Z4Plaq → Nat)
    (hbounded : ∀ plaquette, fineSpin plaquette ≤ cutoff)
    (coarsePlaquette : Z4Plaq) (target : PairChannelState) : Q' :=
  packetPairChannelConditionalKernel w hw cutoff
    (slabBoundedFaceSpinPacket cutoff fineSpin hbounded coarsePlaquette)
    target

theorem dyadicSlabPairChannelConditionalKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (fineSpin : Z4Plaq → Nat)
    (hbounded : ∀ plaquette, fineSpin plaquette ≤ cutoff)
    (coarsePlaquette : Z4Plaq) :
    listQSum
        (dyadicSlabPairChannelConditionalKernel w hw cutoff
          fineSpin hbounded coarsePlaquette)
        (pairChannelStateSpace cutoff) ≈ 1 := by
  exact packetPairChannelConditionalKernel_row_normalized
    w hw cutoff
    (slabBoundedFaceSpinPacket cutoff fineSpin hbounded coarsePlaquette)

theorem dyadicSlabPairChannelConditionalKernel_reflection_equivariant
    (w : Q') (hw : (0 : Q') < w) (cutoff extent : Nat)
    (fineSpin : Z4Plaq → Nat)
    (hbounded : ∀ plaquette, fineSpin plaquette ≤ cutoff)
    (coarsePlaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent coarsePlaquette)
    (target : PairChannelState) :
    dyadicSlabPairChannelConditionalKernel w hw cutoff
        (reflectSlabFaceSpinLabelling (dyadicSlabFineExtent extent)
          fineSpin)
        (fun plaquette =>
          hbounded (timeReflectPlaquette
            (dyadicSlabFineExtent extent) plaquette))
        coarsePlaquette
        (reflectPairChannelState coarsePlaquette.2 target) ≈
      dyadicSlabPairChannelConditionalKernel w hw cutoff
        fineSpin hbounded
        (timeReflectPlaquette extent coarsePlaquette) target := by
  unfold dyadicSlabPairChannelConditionalKernel
  rw [slabBoundedFaceSpinPacket_reflection
    cutoff extent fineSpin hbounded coarsePlaquette hadmissible]
  exact packetPairChannelConditionalKernel_reflection_equivariant
    w hw cutoff coarsePlaquette.2
      (slabBoundedFaceSpinPacket cutoff fineSpin hbounded
        (timeReflectPlaquette extent coarsePlaquette)) target

/-! ## 6. A checked source-dependence witness -/

def vacuumFaceSpinPacket : FaceSpinPacket := ⟨0, 0, 0, 0⟩

def oneFaceFundamentalPacket : FaceSpinPacket := ⟨1, 0, 0, 0⟩

theorem vacuumFaceSpinPacket_mem :
    vacuumFaceSpinPacket ∈ faceSpinPacketStateSpace 1 := by
  apply (mem_faceSpinPacketStateSpace_iff 1 _).mpr
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem oneFaceFundamentalPacket_mem :
    oneFaceFundamentalPacket ∈ faceSpinPacketStateSpace 1 := by
  apply (mem_faceSpinPacketStateSpace_iff 1 _).mpr
  exact ⟨by decide, by decide, by decide, by decide⟩

def vacuumBoundedFaceSpinPacket : BoundedFaceSpinPacket 1 :=
  ⟨vacuumFaceSpinPacket, vacuumFaceSpinPacket_mem⟩

def oneFaceFundamentalBoundedPacket : BoundedFaceSpinPacket 1 :=
  ⟨oneFaceFundamentalPacket, oneFaceFundamentalPacket_mem⟩

theorem vacuumPacket_zeroChannel_kernel_pos
    (w : Q') (hw : (0 : Q') < w) :
    (0 : Q') < packetPairChannelConditionalKernel w hw 1
      vacuumBoundedFaceSpinPacket ((0, 0), 0) := by
  unfold packetPairChannelConditionalKernel
  apply Q'.divPos_pos
  simpa [vacuumBoundedFaceSpinPacket, vacuumFaceSpinPacket] using
    stretchedPairChannelRawWeight_pos hw vacuumFaceSpinPacket

theorem oneFaceFundamental_zeroChannel_raw_eqv_zero (w : Q') :
    packetPairChannelRawWeight w oneFaceFundamentalPacket ((0, 0), 0) ≈
      0 := by
  unfold packetPairChannelRawWeight oneFaceFundamentalPacket
  change coeffW w 0 *
    (fusionInd 1 0 0 * (fusionInd 0 0 0 * fusionInd 0 0 0)) ≈ 0
  rw [show fusionInd 1 0 0 = (0 : Q') by decide]
  exact Q'.eqv_trans _ (coeffW w 0 * 0) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
    (Q'.mul_zero_eqv _)

theorem oneFaceFundamental_zeroChannel_kernel_eqv_zero
    (w : Q') (hw : (0 : Q') < w) :
    packetPairChannelConditionalKernel w hw 1
        oneFaceFundamentalBoundedPacket ((0, 0), 0) ≈ 0 := by
  unfold packetPairChannelConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    ((0 : Q') *
      Q'.recipPos
        (packetPairChannelPartition w 1
          oneFaceFundamentalBoundedPacket.val)
        (packetPairChannelPartition_pos hw 1
          oneFaceFundamentalBoundedPacket.val
          oneFaceFundamentalBoundedPacket.property)) _
    (Q'.mul_eqv_congr_right _ _ _
      (oneFaceFundamental_zeroChannel_raw_eqv_zero w))
    (Q'.zero_mul_eqv _)

/-- The normalized kernel is not a source-independent refresh: at the same
target channel the vacuum source has strictly positive mass, whereas a source
with one fundamental fine character has exactly zero mass. -/
theorem packetPairChannelConditionalKernel_source_dependent
    (w : Q') (hw : (0 : Q') < w) :
    (0 : Q') < packetPairChannelConditionalKernel w hw 1
        vacuumBoundedFaceSpinPacket ((0, 0), 0) ∧
      packetPairChannelConditionalKernel w hw 1
        oneFaceFundamentalBoundedPacket ((0, 0), 0) ≈ 0 :=
  ⟨vacuumPacket_zeroChannel_kernel_pos w hw,
    oneFaceFundamental_zeroChannel_kernel_eqv_zero w hw⟩

/-! ## Axiom audit -/

#print axioms mem_pairChannelStateSpace_iff
#print axioms pairChannelStateSpace_nodup
#print axioms reflectPairChannelState_involutive
#print axioms packetPairChannelRawWeight_nonnegative
#print axioms fusionInd_add_eq_one
#print axioms stretchedPairChannel_mem
#print axioms stretchedPairChannelRawWeight_pos
#print axioms packetPairChannelPartition_pos
#print axioms packetPairChannelConditionalKernel_nonnegative
#print axioms packetPairChannelConditionalKernel_row_normalized
#print axioms packetPairChannelRawWeight_reflection
#print axioms packetPairChannelPartition_eqv_tripleSum
#print axioms packetPairChannelPartition_reflection
#print axioms packetPairChannelConditionalKernel_reflection_equivariant
#print axioms slabBoundedFaceSpinPacket_reflection
#print axioms dyadicSlabPairChannelConditionalKernel_row_normalized
#print axioms dyadicSlabPairChannelConditionalKernel_reflection_equivariant
#print axioms packetPairChannelConditionalKernel_source_dependent

end YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
