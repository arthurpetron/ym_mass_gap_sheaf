/-
# A reflection-equivariant four-character packet kernel on the corrected slab

The mod-two slab kernel retains only the center-parity shadow of the four
nondegenerate fine faces above a coarse face.  This file records the smallest
local lift that does not discard their SU(2) twice-spin labels: a coarse face
carries the ordered packet of all four labels.  Spatial time reflection swaps
the lower and upper two-entry halves, while time-oriented fibres keep their
order.  With the affine fine extent `2 * extent + 1`, this packet map therefore
intertwines half-time reflection exactly.

For any finite spin cutoff, the induced exact-rational Dirac kernel is
nonnegative and row-normalized on the finite four-packet state space.  Packet
parity recovers the cellular XOR coefficient definitionally.  This is a
multi-character carrier, not yet the physical block kernel: the remaining
step is to contract each packet with derived local Haar/fusion amplitudes and
prove compatibility with the interacting corrected-slab weight.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4DyadicSlabReflectionParityKernel

namespace YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Four-character packets and their finite state space -/

structure FaceSpinPacket where
  spin0 : Nat
  spin1 : Nat
  spin2 : Nat
  spin3 : Nat
deriving DecidableEq

def rawFaceSpinPacketStateSpace (cutoff : Nat) : List FaceSpinPacket :=
  (cartesian
    (cartesian (List.range (cutoff + 1)) (List.range (cutoff + 1)))
    (cartesian (List.range (cutoff + 1)) (List.range (cutoff + 1)))).map
      fun pair => ⟨pair.1.1, pair.1.2, pair.2.1, pair.2.2⟩

def faceSpinPacketStateSpace (cutoff : Nat) : List FaceSpinPacket :=
  rawFaceSpinPacketStateSpace cutoff

theorem mem_rawFaceSpinPacketStateSpace_iff
    (cutoff : Nat) (packet : FaceSpinPacket) :
    packet ∈ rawFaceSpinPacketStateSpace cutoff ↔
      packet.spin0 ≤ cutoff ∧ packet.spin1 ≤ cutoff ∧
        packet.spin2 ≤ cutoff ∧ packet.spin3 ≤ cutoff := by
  unfold rawFaceSpinPacketStateSpace
  constructor
  · intro hmem
    obtain ⟨pair, hpair, hpacket⟩ := List.mem_map.mp hmem
    have hpairParts := (mem_cartesian_iff _ _ pair).mp hpair
    have hleft := (mem_cartesian_iff _ _ pair.1).mp hpairParts.1
    have hright := (mem_cartesian_iff _ _ pair.2).mp hpairParts.2
    simp only [List.mem_range] at hleft hright
    constructor
    · rw [← hpacket]
      change pair.1.1 ≤ cutoff
      omega
    · constructor
      · rw [← hpacket]
        change pair.1.2 ≤ cutoff
        omega
      · constructor
        · rw [← hpacket]
          change pair.2.1 ≤ cutoff
          omega
        · rw [← hpacket]
          change pair.2.2 ≤ cutoff
          omega
  · rintro ⟨hspin0, hspin1, hspin2, hspin3⟩
    apply List.mem_map.mpr
    refine ⟨((packet.spin0, packet.spin1),
      (packet.spin2, packet.spin3)), ?_, by cases packet; rfl⟩
    apply (mem_cartesian_iff _ _ _).mpr
    constructor
    · exact (mem_cartesian_iff _ _ _).mpr
        ⟨List.mem_range.mpr (by
            change packet.spin0 < cutoff + 1
            omega),
          List.mem_range.mpr (by
            change packet.spin1 < cutoff + 1
            omega)⟩
    · exact (mem_cartesian_iff _ _ _).mpr
        ⟨List.mem_range.mpr (by
            change packet.spin2 < cutoff + 1
            omega),
          List.mem_range.mpr (by
            change packet.spin3 < cutoff + 1
            omega)⟩

theorem mem_faceSpinPacketStateSpace_iff
    (cutoff : Nat) (packet : FaceSpinPacket) :
    packet ∈ faceSpinPacketStateSpace cutoff ↔
      packet.spin0 ≤ cutoff ∧ packet.spin1 ≤ cutoff ∧
        packet.spin2 ≤ cutoff ∧ packet.spin3 ≤ cutoff := by
  exact mem_rawFaceSpinPacketStateSpace_iff cutoff packet

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

theorem faceSpinPacketStateSpace_nodup (cutoff : Nat) :
    (faceSpinPacketStateSpace cutoff).Nodup := by
  let labels := List.range (cutoff + 1)
  let pairs := cartesian labels labels
  have hlabels : labels.Nodup := rangeNodupLocal _
  have hpairs : pairs.Nodup := cartesian_nodup labels labels hlabels hlabels
  unfold faceSpinPacketStateSpace rawFaceSpinPacketStateSpace
  apply nodupMapInjective
    (fun pair : (Nat × Nat) × (Nat × Nat) =>
      (⟨pair.1.1, pair.1.2, pair.2.1, pair.2.2⟩ : FaceSpinPacket))
  · intro first second heq
    obtain ⟨⟨first0, first1⟩, ⟨first2, first3⟩⟩ := first
    obtain ⟨⟨second0, second1⟩, ⟨second2, second3⟩⟩ := second
    injection heq with h0 h1 h2 h3
    change first0 = second0 at h0
    change first1 = second1 at h1
    change first2 = second2 at h2
    change first3 = second3 at h3
    subst second0
    subst second1
    subst second2
    subst second3
    rfl
  · exact cartesian_nodup pairs pairs hpairs hpairs

/-! ## 2. The local packet map and its parity shadow -/

/-- All four twice-spin labels in the explicit nondegenerate fine-face fibre.
The fibre always has length four, so the fallback is unreachable. -/
def dyadicFaceSpinPacket
    (fineSpin : Z4Plaq → Nat) (coarsePlaquette : Z4Plaq) :
    FaceSpinPacket :=
  let fibre := dyadicFacePreimages coarsePlaquette
  ⟨fineSpin (fibre.getD 0 fallbackPlaquette),
    fineSpin (fibre.getD 1 fallbackPlaquette),
    fineSpin (fibre.getD 2 fallbackPlaquette),
    fineSpin (fibre.getD 3 fallbackPlaquette)⟩

theorem dyadicFaceSpinPacket_mem_stateSpace
    (cutoff : Nat) (fineSpin : Z4Plaq → Nat)
    (hbounded : ∀ plaquette, fineSpin plaquette ≤ cutoff)
    (coarsePlaquette : Z4Plaq) :
    dyadicFaceSpinPacket fineSpin coarsePlaquette ∈
      faceSpinPacketStateSpace cutoff := by
  apply (mem_faceSpinPacketStateSpace_iff cutoff _).mpr
  exact ⟨hbounded _, hbounded _, hbounded _, hbounded _⟩

def faceSpinPacketParity (packet : FaceSpinPacket) : Bool :=
  decide (packet.spin0 % 2 = 1) ^^
    (decide (packet.spin1 % 2 = 1) ^^
      (decide (packet.spin2 % 2 = 1) ^^
        (decide (packet.spin3 % 2 = 1) ^^ false)))

/-- The full character packet strictly lifts the existing cellular parity
coefficient: applying the odd-label shadow to the packet gives the same XOR
over the same four fine faces. -/
theorem dyadicFaceSpinPacket_refines_parity
    (fineSpin : Z4Plaq → Nat) (coarsePlaquette : Z4Plaq) :
    faceSpinPacketParity
        (dyadicFaceSpinPacket fineSpin coarsePlaquette) =
      dyadicFacePushforward
        (fun plaquette => decide (fineSpin plaquette % 2 = 1))
        coarsePlaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
  cases plane <;>
    rfl

/-! ## 3. Exact half-time reflection of packets -/

def reflectSlabFaceSpinLabelling
    (extent : Nat) (fineSpin : Z4Plaq → Nat) : Z4Plaq → Nat :=
  fun plaquette => fineSpin (timeReflectPlaquette extent plaquette)

/-- Spatial fibres have two fine time layers and reflection exchanges the
two-entry halves.  Time-oriented fibres have one odd base-time layer. -/
def reflectFaceSpinPacket
    (plane : Z4Plane) (packet : FaceSpinPacket) : FaceSpinPacket :=
  match plane with
  | .p01 | .p02 | .p12 =>
      ⟨packet.spin2, packet.spin3, packet.spin0, packet.spin1⟩
  | .p03 | .p13 | .p23 => packet

theorem reflectFaceSpinPacket_involutive
    (plane : Z4Plane) (packet : FaceSpinPacket) :
    reflectFaceSpinPacket plane
        (reflectFaceSpinPacket plane packet) = packet := by
  cases plane <;> cases packet <;> rfl

theorem reflectFaceSpinPacket_mem_stateSpace
    {cutoff : Nat} {packet : FaceSpinPacket}
    (hpacket : packet ∈ faceSpinPacketStateSpace cutoff)
    (plane : Z4Plane) :
    reflectFaceSpinPacket plane packet ∈
      faceSpinPacketStateSpace cutoff := by
  have hbounds := (mem_faceSpinPacketStateSpace_iff cutoff packet).mp hpacket
  apply (mem_faceSpinPacketStateSpace_iff cutoff _).mpr
  cases plane with
  | p01 => exact ⟨hbounds.2.2.1, hbounds.2.2.2,
      hbounds.1, hbounds.2.1⟩
  | p02 => exact ⟨hbounds.2.2.1, hbounds.2.2.2,
      hbounds.1, hbounds.2.1⟩
  | p03 => exact hbounds
  | p12 => exact ⟨hbounds.2.2.1, hbounds.2.2.2,
      hbounds.1, hbounds.2.1⟩
  | p13 => exact hbounds
  | p23 => exact hbounds

/-- The four-character packet itself, not merely its parity shadow, commutes
with corrected-slab reflection. -/
theorem dyadicFaceSpinPacket_reflection
    (extent : Nat) (fineSpin : Z4Plaq → Nat)
    (coarsePlaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent coarsePlaquette) :
    dyadicFaceSpinPacket
        (reflectSlabFaceSpinLabelling (dyadicSlabFineExtent extent)
          fineSpin)
        coarsePlaquette =
      reflectFaceSpinPacket coarsePlaquette.2
        (dyadicFaceSpinPacket fineSpin
          (timeReflectPlaquette extent coarsePlaquette)) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
  cases plane with
  | p01 =>
      have hd : d ≤ extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have heven : 2 * extent + 1 - 2 * d = 2 * (extent - d) + 1 := by
        omega
      have hodd : 2 * extent + 1 - (2 * d + 1) = 2 * (extent - d) := by
        omega
      simp [dyadicFaceSpinPacket, reflectSlabFaceSpinLabelling,
        reflectFaceSpinPacket, dyadicSlabFineExtent,
        dyadicFacePreimages, timeReflectPlaquette, heven, hodd]
  | p02 =>
      have hd : d ≤ extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have heven : 2 * extent + 1 - 2 * d = 2 * (extent - d) + 1 := by
        omega
      have hodd : 2 * extent + 1 - (2 * d + 1) = 2 * (extent - d) := by
        omega
      simp [dyadicFaceSpinPacket, reflectSlabFaceSpinLabelling,
        reflectFaceSpinPacket, dyadicSlabFineExtent,
        dyadicFacePreimages, timeReflectPlaquette, heven, hodd]
  | p03 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have htime :
          2 * extent + 1 - (2 * d + 1 + 1) =
            2 * (extent - (d + 1)) + 1 := by
        omega
      simp [dyadicFaceSpinPacket, reflectSlabFaceSpinLabelling,
        reflectFaceSpinPacket, dyadicSlabFineExtent,
        dyadicFacePreimages, timeReflectPlaquette, htime]
  | p12 =>
      have hd : d ≤ extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have heven : 2 * extent + 1 - 2 * d = 2 * (extent - d) + 1 := by
        omega
      have hodd : 2 * extent + 1 - (2 * d + 1) = 2 * (extent - d) := by
        omega
      simp [dyadicFaceSpinPacket, reflectSlabFaceSpinLabelling,
        reflectFaceSpinPacket, dyadicSlabFineExtent,
        dyadicFacePreimages, timeReflectPlaquette, heven, hodd]
  | p13 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have htime :
          2 * extent + 1 - (2 * d + 1 + 1) =
            2 * (extent - (d + 1)) + 1 := by
        omega
      simp [dyadicFaceSpinPacket, reflectSlabFaceSpinLabelling,
        reflectFaceSpinPacket, dyadicSlabFineExtent,
        dyadicFacePreimages, timeReflectPlaquette, htime]
  | p23 =>
      have hd : d < extent := by
        simpa [plaquetteTimeAdmissible] using hadmissible
      have htime :
          2 * extent + 1 - (2 * d + 1 + 1) =
            2 * (extent - (d + 1)) + 1 := by
        omega
      simp [dyadicFaceSpinPacket, reflectSlabFaceSpinLabelling,
        reflectFaceSpinPacket, dyadicSlabFineExtent,
        dyadicFacePreimages, timeReflectPlaquette, htime]

/-! ## 4. Positive normalized packet kernel -/

def dyadicFaceSpinPacketKernel
    (fineSpin : Z4Plaq → Nat) (coarsePlaquette : Z4Plaq)
    (target : FaceSpinPacket) : Q' :=
  deterministicKernel
    (fun source : Z4Plaq → Nat =>
      dyadicFaceSpinPacket source coarsePlaquette)
    fineSpin target

theorem dyadicFaceSpinPacketKernel_nonnegative
    (fineSpin : Z4Plaq → Nat) (coarsePlaquette : Z4Plaq)
    (target : FaceSpinPacket) :
    (0 : Q') ≤
      dyadicFaceSpinPacketKernel fineSpin coarsePlaquette target := by
  exact deterministicKernel_nonnegative
    (fun source : Z4Plaq → Nat =>
      dyadicFaceSpinPacket source coarsePlaquette)
    fineSpin target

theorem dyadicFaceSpinPacketKernel_row_normalized
    (cutoff : Nat) (fineSpin : Z4Plaq → Nat)
    (hbounded : ∀ plaquette, fineSpin plaquette ≤ cutoff)
    (coarsePlaquette : Z4Plaq) :
    listQSum (dyadicFaceSpinPacketKernel fineSpin coarsePlaquette)
        (faceSpinPacketStateSpace cutoff) ≈ 1 := by
  exact deterministicKernel_row_normalized
    (fun source : Z4Plaq → Nat =>
      dyadicFaceSpinPacket source coarsePlaquette)
    fineSpin (faceSpinPacketStateSpace cutoff)
    (faceSpinPacketStateSpace_nodup cutoff)
    (dyadicFaceSpinPacket_mem_stateSpace
      cutoff fineSpin hbounded coarsePlaquette)

/-- Exact reflection intertwining for the full local character packet kernel.
The target packet is transformed by the same half-layer exchange as the
source fibre. -/
theorem dyadicFaceSpinPacketKernel_reflection_equivariant
    (extent : Nat) (fineSpin : Z4Plaq → Nat)
    (coarsePlaquette : Z4Plaq)
    (hadmissible : plaquetteTimeAdmissible extent coarsePlaquette)
    (target : FaceSpinPacket) :
    dyadicFaceSpinPacketKernel
        (reflectSlabFaceSpinLabelling (dyadicSlabFineExtent extent)
          fineSpin)
        coarsePlaquette
        (reflectFaceSpinPacket coarsePlaquette.2 target) =
      dyadicFaceSpinPacketKernel fineSpin
        (timeReflectPlaquette extent coarsePlaquette) target := by
  unfold dyadicFaceSpinPacketKernel deterministicKernel
  change (if reflectFaceSpinPacket coarsePlaquette.2 target =
        dyadicFaceSpinPacket
          (reflectSlabFaceSpinLabelling (dyadicSlabFineExtent extent)
            fineSpin)
          coarsePlaquette then (1 : Q') else 0) =
    if target = dyadicFaceSpinPacket fineSpin
        (timeReflectPlaquette extent coarsePlaquette) then 1 else 0
  rw [dyadicFaceSpinPacket_reflection
    extent fineSpin coarsePlaquette hadmissible]
  by_cases htarget : target =
      dyadicFaceSpinPacket fineSpin
        (timeReflectPlaquette extent coarsePlaquette)
  · subst target
    simp
  · have hreflectedNe :
        reflectFaceSpinPacket coarsePlaquette.2 target ≠
          reflectFaceSpinPacket coarsePlaquette.2
            (dyadicFaceSpinPacket fineSpin
              (timeReflectPlaquette extent coarsePlaquette)) := by
      intro hreflected
      have htwice := congrArg
        (reflectFaceSpinPacket coarsePlaquette.2) hreflected
      rw [reflectFaceSpinPacket_involutive,
        reflectFaceSpinPacket_involutive] at htwice
      exact htarget htwice
    simp [htarget, hreflectedNe]

/-! ## Axiom audit -/

#print axioms mem_faceSpinPacketStateSpace_iff
#print axioms mem_rawFaceSpinPacketStateSpace_iff
#print axioms faceSpinPacketStateSpace_nodup
#print axioms dyadicFaceSpinPacket_mem_stateSpace
#print axioms dyadicFaceSpinPacket_refines_parity
#print axioms reflectFaceSpinPacket_involutive
#print axioms reflectFaceSpinPacket_mem_stateSpace
#print axioms dyadicFaceSpinPacket_reflection
#print axioms dyadicFaceSpinPacketKernel_nonnegative
#print axioms dyadicFaceSpinPacketKernel_row_normalized
#print axioms dyadicFaceSpinPacketKernel_reflection_equivariant

end YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
