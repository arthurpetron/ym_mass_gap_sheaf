/-
# Coefficient-level XOR assembly for dyadic spins zero through four

Literal subdivision supplies the parity child of an odd coarse spin.  A
lower or upper closed pair bubble supplies two further children in one coarse
fibre.  This module combines those generators over a duplicate-free finite
coarse carrier using pointwise F2 addition.

The coefficient construction is important: list append would retain even
multiplicities when side faces of two bubbles coincide.  XOR cancels those
coincidences and preserves cellular closure.  Under closure of the coarse
odd-spin support, the assembled fine coefficient is closed and has the exact
ordered four-child packet for every carrier face with spin at most four.

The Boolean coefficient is realized constructively as a canonical finite,
duplicate-free support.  Corrected-slab containment is reduced to the exact
condition that every actually selected local bubble stays in that slab.  No
receiver, measure, continuum, or mass-gap claim is made here.
-/

import YMGap.Continuum.Z4DyadicClosedPairBubble

namespace YMGap.Continuum.Z4DyadicSpinFourXorAssembly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicSubdivisionClosure
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Linear closure calculus -/

theorem modTwoClosed_zero :
    ModTwoClosed (fun _ : Z4Plaq => false) := by
  intro link
  obtain ⟨vertex, direction⟩ := link
  cases direction <;>
    simp [cellularBoundaryCoefficient, incidentPlanePairCoefficient,
      backwardFaceCoefficient]

theorem modTwoClosed_pointwise_xor
    {left right : Z4Plaq → Bool}
    (hleft : ModTwoClosed left) (hright : ModTwoClosed right) :
    ModTwoClosed (fun fine => left fine ^^ right fine) := by
  intro link
  rw [cellularBoundaryCoefficient_pointwise_xor,
    hleft link, hright link]
  rfl

theorem pairBubble_supportCoefficient_modTwoClosed
    (coarse : Z4Plaq) (upper : Bool) :
    ModTwoClosed (supportCoefficient (dyadicPairBubble coarse upper)) := by
  exact (modTwoClosed_supportCoefficient_iff_evenFaceIncidence
    (dyadicPairBubble coarse upper)
    (dyadicPairBubble_nodup coarse upper)).2
      (dyadicPairBubble_evenFaceIncidence coarse upper)

/-! ## 2. Local bubble contribution selected by one coarse spin -/

/-- Pair-bubble contribution associated with one coarse face.  Spin two uses
the lower pair, spin three uses the upper pair in addition to its separate
parity child, and spin four uses both pairs. -/
def localPairBubbleCoefficient
    (spin : Z4Plaq → Nat) (coarse : Z4Plaq) : Z4Plaq → Bool :=
  if spin coarse = 2 then
    supportCoefficient (dyadicPairBubble coarse false)
  else if spin coarse = 3 then
    supportCoefficient (dyadicPairBubble coarse true)
  else if spin coarse = 4 then
    fun fine =>
      supportCoefficient (dyadicPairBubble coarse false) fine ^^
        supportCoefficient (dyadicPairBubble coarse true) fine
  else
    fun _ => false

theorem localPairBubbleCoefficient_modTwoClosed
    (spin : Z4Plaq → Nat) (coarse : Z4Plaq) :
    ModTwoClosed (localPairBubbleCoefficient spin coarse) := by
  by_cases htwo : spin coarse = 2
  · simp only [localPairBubbleCoefficient, if_pos htwo]
    exact pairBubble_supportCoefficient_modTwoClosed coarse false
  · rw [localPairBubbleCoefficient, if_neg htwo]
    by_cases hthree : spin coarse = 3
    · rw [if_pos hthree]
      exact pairBubble_supportCoefficient_modTwoClosed coarse true
    · rw [if_neg hthree]
      by_cases hfour : spin coarse = 4
      · rw [if_pos hfour]
        exact modTwoClosed_pointwise_xor
          (pairBubble_supportCoefficient_modTwoClosed coarse false)
          (pairBubble_supportCoefficient_modTwoClosed coarse true)
      · rw [if_neg hfour]
        exact modTwoClosed_zero

/-- A local bubble contribution vanishes on every nondegenerate face over a
different coarse plaquette. -/
theorem localPairBubbleCoefficient_eq_false_of_ne
    {spin : Z4Plaq → Nat} {coarse query fine : Z4Plaq}
    (hquery : fine ∈ dyadicFacePreimages query)
    (hne : query ≠ coarse) :
    localPairBubbleCoefficient spin coarse fine = false := by
  by_cases htwo : spin coarse = 2
  · rw [localPairBubbleCoefficient, if_pos htwo]
    exact supportCoefficient_pairBubble_eq_false_of_ne hquery hne
  · rw [localPairBubbleCoefficient, if_neg htwo]
    by_cases hthree : spin coarse = 3
    · rw [if_pos hthree]
      exact supportCoefficient_pairBubble_eq_false_of_ne hquery hne
    · rw [if_neg hthree]
      by_cases hfour : spin coarse = 4
      · rw [if_pos hfour]
        rw [supportCoefficient_pairBubble_eq_false_of_ne
            hquery hne (upper := false),
          supportCoefficient_pairBubble_eq_false_of_ne
            hquery hne (upper := true)]
        rfl
      · rw [if_neg hfour]

/-- Packet contributed by the bubble part alone. -/
def localPairBubblePacket : Nat → FaceSpinPacket
  | 2 => ⟨1, 1, 0, 0⟩
  | 3 => ⟨0, 0, 1, 1⟩
  | 4 => ⟨1, 1, 1, 1⟩
  | _ => ⟨0, 0, 0, 0⟩

private theorem bool_eq_true_of_toNat_eq_one
    {bit : Bool} (hbit : bit.toNat = 1) : bit = true := by
  cases bit <;> simp at hbit ⊢

private theorem bool_eq_false_of_toNat_eq_zero
    {bit : Bool} (hbit : bit.toNat = 0) : bit = false := by
  cases bit <;> simp at hbit ⊢

/-- Lower and upper pair bubbles occupy disjoint halves of the target fibre,
so their pointwise XOR has all four target bits. -/
theorem dyadicFaceSpinPacket_bothPairBubbles_target
    (coarse : Z4Plaq) :
    dyadicFaceSpinPacket
        (fun fine =>
          (supportCoefficient (dyadicPairBubble coarse false) fine ^^
            supportCoefficient (dyadicPairBubble coarse true) fine).toNat)
        coarse =
      ⟨1, 1, 1, 1⟩ := by
  let fibre := dyadicFacePreimages coarse
  have hlower := dyadicFaceSpinPacket_pairBubble_target coarse false
  have hupper := dyadicFaceSpinPacket_pairBubble_target coarse true
  have hlower0Nat :
      (supportCoefficient (dyadicPairBubble coarse false)
        (fibre.getD 0 fallbackPlaquette)).toNat = 1 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin0 hlower
  have hlower1Nat :
      (supportCoefficient (dyadicPairBubble coarse false)
        (fibre.getD 1 fallbackPlaquette)).toNat = 1 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin1 hlower
  have hlower2Nat :
      (supportCoefficient (dyadicPairBubble coarse false)
        (fibre.getD 2 fallbackPlaquette)).toNat = 0 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin2 hlower
  have hlower3Nat :
      (supportCoefficient (dyadicPairBubble coarse false)
        (fibre.getD 3 fallbackPlaquette)).toNat = 0 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin3 hlower
  have hupper0Nat :
      (supportCoefficient (dyadicPairBubble coarse true)
        (fibre.getD 0 fallbackPlaquette)).toNat = 0 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin0 hupper
  have hupper1Nat :
      (supportCoefficient (dyadicPairBubble coarse true)
        (fibre.getD 1 fallbackPlaquette)).toNat = 0 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin1 hupper
  have hupper2Nat :
      (supportCoefficient (dyadicPairBubble coarse true)
        (fibre.getD 2 fallbackPlaquette)).toNat = 1 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin2 hupper
  have hupper3Nat :
      (supportCoefficient (dyadicPairBubble coarse true)
        (fibre.getD 3 fallbackPlaquette)).toNat = 1 := by
    simpa only [dyadicFaceSpinPacket, pairBubblePacket, fibre] using
      congrArg FaceSpinPacket.spin3 hupper
  have hlower0 := bool_eq_true_of_toNat_eq_one hlower0Nat
  have hlower1 := bool_eq_true_of_toNat_eq_one hlower1Nat
  have hlower2 := bool_eq_false_of_toNat_eq_zero hlower2Nat
  have hlower3 := bool_eq_false_of_toNat_eq_zero hlower3Nat
  have hupper0 := bool_eq_false_of_toNat_eq_zero hupper0Nat
  have hupper1 := bool_eq_false_of_toNat_eq_zero hupper1Nat
  have hupper2 := bool_eq_true_of_toNat_eq_one hupper2Nat
  have hupper3 := bool_eq_true_of_toNat_eq_one hupper3Nat
  simp only [dyadicFaceSpinPacket]
  rw [hlower0, hlower1, hlower2, hlower3,
    hupper0, hupper1, hupper2, hupper3]
  rfl

theorem dyadicFaceSpinPacket_localPairBubbleCoefficient
    (spin : Z4Plaq → Nat) (coarse : Z4Plaq) :
    dyadicFaceSpinPacket
        (fun fine => (localPairBubbleCoefficient spin coarse fine).toNat)
        coarse =
      localPairBubblePacket (spin coarse) := by
  by_cases htwo : spin coarse = 2
  · rw [localPairBubbleCoefficient, if_pos htwo, htwo]
    exact dyadicFaceSpinPacket_pairBubble_target coarse false
  · rw [localPairBubbleCoefficient, if_neg htwo]
    by_cases hthree : spin coarse = 3
    · rw [if_pos hthree, hthree]
      exact dyadicFaceSpinPacket_pairBubble_target coarse true
    · rw [if_neg hthree]
      by_cases hfour : spin coarse = 4
      · rw [if_pos hfour, hfour]
        exact dyadicFaceSpinPacket_bothPairBubbles_target coarse
      · rw [if_neg hfour]
        have hother : localPairBubblePacket (spin coarse) = ⟨0, 0, 0, 0⟩ := by
          unfold localPairBubblePacket
          split <;> rename_i heq
          · exact absurd heq htwo
          · exact absurd heq hthree
          · exact absurd heq hfour
          · rfl
        rw [hother]
        rfl

/-! ## 3. Finite XOR of every local bubble contribution -/

def pairBubbleAssemblyCoefficient
    (spin : Z4Plaq → Nat) : List Z4Plaq → Z4Plaq → Bool
  | [] => fun _ => false
  | coarse :: rest => fun fine =>
      localPairBubbleCoefficient spin coarse fine ^^
        pairBubbleAssemblyCoefficient spin rest fine

theorem pairBubbleAssemblyCoefficient_modTwoClosed
    (spin : Z4Plaq → Nat) : ∀ carrier : List Z4Plaq,
    ModTwoClosed (pairBubbleAssemblyCoefficient spin carrier)
  | [] => modTwoClosed_zero
  | coarse :: rest =>
      modTwoClosed_pointwise_xor
        (localPairBubbleCoefficient_modTwoClosed spin coarse)
        (pairBubbleAssemblyCoefficient_modTwoClosed spin rest)

private theorem pairBubbleAssemblyCoefficient_eq_false_of_all_ne
    {spin : Z4Plaq → Nat} {query fine : Z4Plaq}
    (hquery : fine ∈ dyadicFacePreimages query) :
    ∀ carrier : List Z4Plaq,
      (∀ coarse, coarse ∈ carrier → query ≠ coarse) →
      pairBubbleAssemblyCoefficient spin carrier fine = false
  | [], _ => rfl
  | coarse :: rest, hall => by
      have hhead : query ≠ coarse :=
        hall coarse List.mem_cons_self
      have htail : ∀ item, item ∈ rest → query ≠ item := by
        intro item hitem
        exact hall item (List.mem_cons_of_mem coarse hitem)
      rw [pairBubbleAssemblyCoefficient]
      change
        (localPairBubbleCoefficient spin coarse fine ^^
            pairBubbleAssemblyCoefficient spin rest fine) = false
      rw [
        localPairBubbleCoefficient_eq_false_of_ne hquery hhead,
        pairBubbleAssemblyCoefficient_eq_false_of_all_ne
          hquery rest htail]
      rfl

/-- On a fibre whose coarse face occurs exactly once in the carrier, the
whole bubble assembly is pointwise equal to that face's local contribution. -/
theorem pairBubbleAssemblyCoefficient_eq_local_on_fibre
    {spin : Z4Plaq → Nat} {carrier : List Z4Plaq}
    (hnodup : carrier.Nodup) {query fine : Z4Plaq}
    (hqueryMem : query ∈ carrier)
    (hfine : fine ∈ dyadicFacePreimages query) :
    pairBubbleAssemblyCoefficient spin carrier fine =
      localPairBubbleCoefficient spin query fine := by
  induction carrier with
  | nil => exact False.elim (List.not_mem_nil hqueryMem)
  | cons coarse rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hqueryMem with hhead | htail
      · subst coarse
        have hrestOutside : ∀ item, item ∈ rest → query ≠ item := by
          intro item hitem heq
          subst item
          exact hparts.1 hitem
        rw [pairBubbleAssemblyCoefficient]
        change
          (localPairBubbleCoefficient spin query fine ^^
              pairBubbleAssemblyCoefficient spin rest fine) =
            localPairBubbleCoefficient spin query fine
        rw [
          pairBubbleAssemblyCoefficient_eq_false_of_all_ne
            hfine rest hrestOutside]
        cases localPairBubbleCoefficient spin query fine <;> rfl
      · have hne : query ≠ coarse := by
          intro heq
          subst coarse
          exact hparts.1 htail
        rw [pairBubbleAssemblyCoefficient]
        change
          (localPairBubbleCoefficient spin coarse fine ^^
              pairBubbleAssemblyCoefficient spin rest fine) =
            localPairBubbleCoefficient spin query fine
        rw [
          localPairBubbleCoefficient_eq_false_of_ne hfine hne,
          ih hparts.2 htail]
        cases localPairBubbleCoefficient spin query fine <;> rfl

theorem dyadicFaceSpinPacket_pairBubbleAssemblyCoefficient
    {spin : Z4Plaq → Nat} {carrier : List Z4Plaq}
    (hnodup : carrier.Nodup) {query : Z4Plaq}
    (hquery : query ∈ carrier) :
    dyadicFaceSpinPacket
        (fun fine =>
          (pairBubbleAssemblyCoefficient spin carrier fine).toNat)
        query =
      localPairBubblePacket (spin query) := by
  have hslots := dyadicFacePreimage_slots_mem query
  simp only [dyadicFaceSpinPacket]
  rw [pairBubbleAssemblyCoefficient_eq_local_on_fibre
      hnodup hquery hslots.1,
    pairBubbleAssemblyCoefficient_eq_local_on_fibre
      hnodup hquery hslots.2.1,
    pairBubbleAssemblyCoefficient_eq_local_on_fibre
      hnodup hquery hslots.2.2.1,
    pairBubbleAssemblyCoefficient_eq_local_on_fibre
      hnodup hquery hslots.2.2.2]
  exact dyadicFaceSpinPacket_localPairBubbleCoefficient spin query

/-! ## 4. Add the literal odd-spin subdivision -/

def oddSpinSupport
    (carrier : List Z4Plaq) (spin : Z4Plaq → Nat) : List Z4Plaq :=
  carrier.filter (fun coarse => decide (spin coarse % 2 = 1))

theorem oddSpinSupport_nodup
    {carrier : List Z4Plaq} (hnodup : carrier.Nodup)
    (spin : Z4Plaq → Nat) :
    (oddSpinSupport carrier spin).Nodup := by
  exact List.filter_sublist.nodup hnodup

/-- The complete finitely generated fine coefficient. -/
def dyadicSpinFourCoefficient
    (carrier : List Z4Plaq) (spin : Z4Plaq → Nat) : Z4Plaq → Bool :=
  fun fine =>
    supportCoefficient
        (dyadicSupportCells (oddSpinSupport carrier spin)) fine ^^
      pairBubbleAssemblyCoefficient spin carrier fine

theorem dyadicSpinFourCoefficient_modTwoClosed
    {carrier : List Z4Plaq} (hnodup : carrier.Nodup)
    (spin : Z4Plaq → Nat)
    (hoddClosed : EvenFaceIncidence (oddSpinSupport carrier spin)) :
    ModTwoClosed (dyadicSpinFourCoefficient carrier spin) := by
  have hsubdivisionClosed :
      ModTwoClosed
        (supportCoefficient
          (dyadicSupportCells (oddSpinSupport carrier spin))) :=
    (modTwoClosed_supportCoefficient_iff_evenFaceIncidence
      (dyadicSupportCells (oddSpinSupport carrier spin))
      (dyadicSupportCells_nodup (oddSpinSupport_nodup hnodup spin))).2
        (dyadicSupportCells_preserves_evenFaceIncidence
          (oddSpinSupport_nodup hnodup spin) hoddClosed)
  exact modTwoClosed_pointwise_xor hsubdivisionClosed
    (pairBubbleAssemblyCoefficient_modTwoClosed spin carrier)

/-- Bitwise F2 addition of zero-one spin packets. -/
def faceSpinPacketXor (left right : FaceSpinPacket) : FaceSpinPacket :=
  ⟨(decide (left.spin0 = 1) ^^ decide (right.spin0 = 1)).toNat,
   (decide (left.spin1 = 1) ^^ decide (right.spin1 = 1)).toNat,
   (decide (left.spin2 = 1) ^^ decide (right.spin2 = 1)).toNat,
   (decide (left.spin3 = 1) ^^ decide (right.spin3 = 1)).toNat⟩

private theorem boolXor_toNat (left right : Bool) :
    (left ^^ right).toNat =
      (decide (left.toNat = 1) ^^ decide (right.toNat = 1)).toNat := by
  cases left <;> cases right <;> rfl

private theorem faceSpinPacket_eq
    {left right : FaceSpinPacket}
    (hzero : left.spin0 = right.spin0)
    (hone : left.spin1 = right.spin1)
    (htwo : left.spin2 = right.spin2)
    (hthree : left.spin3 = right.spin3) :
    left = right := by
  cases left
  cases right
  simp_all only

theorem dyadicFaceSpinPacket_pointwise_xor
    (left right : Z4Plaq → Bool) (coarse : Z4Plaq) :
    dyadicFaceSpinPacket
        (fun fine => (left fine ^^ right fine).toNat) coarse =
      faceSpinPacketXor
        (dyadicFaceSpinPacket (fun fine => (left fine).toNat) coarse)
        (dyadicFaceSpinPacket (fun fine => (right fine).toNat) coarse) := by
  unfold dyadicFaceSpinPacket faceSpinPacketXor
  apply faceSpinPacket_eq <;>
    dsimp only <;>
    apply boolXor_toNat

/-- Canonical ordered packet used for total spins zero through four. -/
def spinFourPacket : Nat → FaceSpinPacket
  | 0 => ⟨0, 0, 0, 0⟩
  | 1 => ⟨1, 0, 0, 0⟩
  | 2 => ⟨1, 1, 0, 0⟩
  | 3 => ⟨1, 0, 1, 1⟩
  | 4 => ⟨1, 1, 1, 1⟩
  | _ => ⟨0, 0, 0, 0⟩

/-- Exact all-generator packet on every carrier face. -/
theorem dyadicFaceSpinPacket_dyadicSpinFourCoefficient
    {carrier : List Z4Plaq} (hnodup : carrier.Nodup)
    (spin : Z4Plaq → Nat) {query : Z4Plaq}
    (hquery : query ∈ carrier) (hspin : spin query ≤ 4) :
    dyadicFaceSpinPacket
        (fun fine => (dyadicSpinFourCoefficient carrier spin fine).toNat)
        query =
      spinFourPacket (spin query) := by
  unfold dyadicSpinFourCoefficient
  rw [dyadicFaceSpinPacket_pointwise_xor]
  rw [dyadicFaceSpinPacket_dyadicSupportCells]
  rw [dyadicFaceSpinPacket_pairBubbleAssemblyCoefficient hnodup hquery]
  have hoddMem :
      query ∈ oddSpinSupport carrier spin ↔ spin query % 2 = 1 := by
    simp only [oddSpinSupport, List.mem_filter, decide_eq_true_eq]
    exact and_iff_right hquery
  have hcases : spin query = 0 ∨ spin query = 1 ∨ spin query = 2 ∨
      spin query = 3 ∨ spin query = 4 := by
    omega
  rcases hcases with hzero | hone | htwo | hthree | hfour
  · have hnotMem : query ∉ oddSpinSupport carrier spin := by
      intro hmem
      have hparity := hoddMem.mp hmem
      omega
    simp [hnotMem, hzero, faceSpinPacketXor, localPairBubblePacket,
      spinFourPacket]
  · have hmem : query ∈ oddSpinSupport carrier spin :=
      hoddMem.mpr (by omega)
    simp [hmem, hone, faceSpinPacketXor, localPairBubblePacket,
      spinFourPacket]
  · have hnotMem : query ∉ oddSpinSupport carrier spin := by
      intro hmem
      have hparity := hoddMem.mp hmem
      omega
    simp [hnotMem, htwo, faceSpinPacketXor, localPairBubblePacket,
      spinFourPacket]
  · have hmem : query ∈ oddSpinSupport carrier spin :=
      hoddMem.mpr (by omega)
    simp [hmem, hthree, faceSpinPacketXor, localPairBubblePacket,
      spinFourPacket]
  · have hnotMem : query ∉ oddSpinSupport carrier spin := by
      intro hmem
      have hparity := hoddMem.mp hmem
      omega
    simp [hnotMem, hfour, faceSpinPacketXor, localPairBubblePacket,
      spinFourPacket]

def faceSpinPacketTotal (packet : FaceSpinPacket) : Nat :=
  packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3

theorem faceSpinPacketTotal_spinFourPacket
    {spin : Nat} (hspin : spin ≤ 4) :
    faceSpinPacketTotal (spinFourPacket spin) = spin := by
  have hcases : spin = 0 ∨ spin = 1 ∨ spin = 2 ∨ spin = 3 ∨ spin = 4 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem dyadicSpinFourCoefficient_faceSpinTotal
    {carrier : List Z4Plaq} (hnodup : carrier.Nodup)
    (spin : Z4Plaq → Nat) {query : Z4Plaq}
    (hquery : query ∈ carrier) (hspin : spin query ≤ 4) :
    faceSpinPacketTotal
        (dyadicFaceSpinPacket
          (fun fine => (dyadicSpinFourCoefficient carrier spin fine).toNat)
          query) =
      spin query := by
  rw [dyadicFaceSpinPacket_dyadicSpinFourCoefficient
    hnodup spin hquery hspin]
  exact faceSpinPacketTotal_spinFourPacket hspin

/-! ## 5. Canonical finite support of the assembled coefficient -/

/-- A finite list containing every fine face that can occur in the assembled
coefficient.  Both bubble layers are retained in the ambient list even when
the local spin selects only one; the final Boolean filter removes the unused
faces and cancels overlaps. -/
def dyadicSpinFourAmbient
    (carrier : List Z4Plaq) (spin : Z4Plaq → Nat) : List Z4Plaq :=
  dyadicSupportCells (oddSpinSupport carrier spin) ++
    carrier.flatMap fun coarse =>
      dyadicPairBubble coarse false ++ dyadicPairBubble coarse true

private theorem bool_or_of_xor_eq_true
    {left right : Bool} (htrue : (left ^^ right) = true) :
    left = true ∨ right = true := by
  cases left <;> cases right
  · cases htrue
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

private theorem mem_of_supportCoefficient_eq_true
    {support : List Z4Plaq} {fine : Z4Plaq}
    (htrue : supportCoefficient support fine = true) :
    fine ∈ support := by
  unfold supportCoefficient at htrue
  exact of_decide_eq_true htrue

private theorem localPairBubbleCoefficient_true_mem_ambient
    {spin : Z4Plaq → Nat} {coarse fine : Z4Plaq}
    (htrue : localPairBubbleCoefficient spin coarse fine = true) :
    fine ∈ dyadicPairBubble coarse false ++ dyadicPairBubble coarse true := by
  by_cases htwo : spin coarse = 2
  · rw [localPairBubbleCoefficient, if_pos htwo] at htrue
    exact List.mem_append.mpr
      (Or.inl (mem_of_supportCoefficient_eq_true htrue))
  · rw [localPairBubbleCoefficient, if_neg htwo] at htrue
    by_cases hthree : spin coarse = 3
    · rw [if_pos hthree] at htrue
      exact List.mem_append.mpr
        (Or.inr (mem_of_supportCoefficient_eq_true htrue))
    · rw [if_neg hthree] at htrue
      by_cases hfour : spin coarse = 4
      · rw [if_pos hfour] at htrue
        rcases bool_or_of_xor_eq_true htrue with hlower | hupper
        · exact List.mem_append.mpr
            (Or.inl (mem_of_supportCoefficient_eq_true hlower))
        · exact List.mem_append.mpr
            (Or.inr (mem_of_supportCoefficient_eq_true hupper))
      · rw [if_neg hfour] at htrue
        cases htrue

private theorem pairBubbleAssemblyCoefficient_true_mem_ambient
    {spin : Z4Plaq → Nat} {fine : Z4Plaq} :
    ∀ {carrier : List Z4Plaq},
      pairBubbleAssemblyCoefficient spin carrier fine = true →
        fine ∈ carrier.flatMap fun coarse =>
          dyadicPairBubble coarse false ++ dyadicPairBubble coarse true
  | [], htrue => by cases htrue
  | coarse :: rest, htrue => by
      change
        (localPairBubbleCoefficient spin coarse fine ^^
          pairBubbleAssemblyCoefficient spin rest fine) = true at htrue
      rcases bool_or_of_xor_eq_true htrue with hlocal | hrest
      · apply List.mem_flatMap.mpr
        exact ⟨coarse, List.mem_cons_self,
          localPairBubbleCoefficient_true_mem_ambient hlocal⟩
      · obtain ⟨source, hsource, hfine⟩ := List.mem_flatMap.mp
          (pairBubbleAssemblyCoefficient_true_mem_ambient hrest)
        apply List.mem_flatMap.mpr
        exact ⟨source, List.mem_cons_of_mem coarse hsource, hfine⟩

theorem dyadicSpinFourCoefficient_true_mem_ambient
    {carrier : List Z4Plaq} {spin : Z4Plaq → Nat} {fine : Z4Plaq}
    (htrue : dyadicSpinFourCoefficient carrier spin fine = true) :
    fine ∈ dyadicSpinFourAmbient carrier spin := by
  unfold dyadicSpinFourCoefficient at htrue
  change
    (supportCoefficient
        (dyadicSupportCells (oddSpinSupport carrier spin)) fine ^^
      pairBubbleAssemblyCoefficient spin carrier fine) = true at htrue
  rcases bool_or_of_xor_eq_true htrue with hsubdivision | hbubbles
  · unfold dyadicSpinFourAmbient
    exact List.mem_append.mpr
      (Or.inl (mem_of_supportCoefficient_eq_true hsubdivision))
  · unfold dyadicSpinFourAmbient
    exact List.mem_append.mpr
      (Or.inr
        (pairBubbleAssemblyCoefficient_true_mem_ambient hbubbles))

/-- The canonical finite list support: filter the finite generator ambient by
the assembled coefficient, then erase duplicates caused by overlapping
bubble side faces. -/
def dyadicSpinFourSupport
    (carrier : List Z4Plaq) (spin : Z4Plaq → Nat) : List Z4Plaq :=
  ((dyadicSpinFourAmbient carrier spin).filter
    (dyadicSpinFourCoefficient carrier spin)).eraseDups

private theorem filteredEraseDupsNodup_local {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool,
      (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun item => (!(item == head)) && predicate item)⟩
        intro hmem
        have hfiltered : head ∈ tail.filter
            (fun item => (!(item == head)) && predicate item) :=
          List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih predicate

theorem dyadicSpinFourSupport_nodup
    (carrier : List Z4Plaq) (spin : Z4Plaq → Nat) :
    (dyadicSpinFourSupport carrier spin).Nodup := by
  unfold dyadicSpinFourSupport
  exact filteredEraseDupsNodup_local _ _

theorem mem_dyadicSpinFourSupport_iff
    (carrier : List Z4Plaq) (spin : Z4Plaq → Nat) (fine : Z4Plaq) :
    fine ∈ dyadicSpinFourSupport carrier spin ↔
      dyadicSpinFourCoefficient carrier spin fine = true := by
  constructor
  · intro hmem
    unfold dyadicSpinFourSupport at hmem
    exact (List.mem_filter.mp (List.mem_eraseDups.mp hmem)).2
  · intro htrue
    unfold dyadicSpinFourSupport
    apply List.mem_eraseDups.mpr
    apply List.mem_filter.mpr
    exact ⟨dyadicSpinFourCoefficient_true_mem_ambient htrue, htrue⟩

theorem dyadicSpinFourSupport_subset_ambient
    {carrier : List Z4Plaq} {spin : Z4Plaq → Nat} {fine : Z4Plaq}
    (hmem : fine ∈ dyadicSpinFourSupport carrier spin) :
    fine ∈ dyadicSpinFourAmbient carrier spin := by
  exact dyadicSpinFourCoefficient_true_mem_ambient
    ((mem_dyadicSpinFourSupport_iff carrier spin fine).mp hmem)

theorem supportCoefficient_dyadicSpinFourSupport
    (carrier : List Z4Plaq) (spin : Z4Plaq → Nat) :
    supportCoefficient (dyadicSpinFourSupport carrier spin) =
      dyadicSpinFourCoefficient carrier spin := by
  funext fine
  unfold supportCoefficient
  by_cases htrue : dyadicSpinFourCoefficient carrier spin fine = true
  · have hmem :=
      (mem_dyadicSpinFourSupport_iff carrier spin fine).mpr htrue
    rw [show decide (fine ∈ dyadicSpinFourSupport carrier spin) = true from
      decide_eq_true hmem, htrue]
  · have hnotMem : fine ∉ dyadicSpinFourSupport carrier spin := by
      intro hmem
      exact htrue
        ((mem_dyadicSpinFourSupport_iff carrier spin fine).mp hmem)
    rw [show decide (fine ∈ dyadicSpinFourSupport carrier spin) = false from
      decide_eq_false hnotMem]
    cases hvalue : dyadicSpinFourCoefficient carrier spin fine
    · rfl
    · exact False.elim (htrue hvalue)

theorem dyadicSpinFourSupport_evenFaceIncidence
    {carrier : List Z4Plaq} (hnodup : carrier.Nodup)
    (spin : Z4Plaq → Nat)
    (hoddClosed : EvenFaceIncidence (oddSpinSupport carrier spin)) :
    EvenFaceIncidence (dyadicSpinFourSupport carrier spin) := by
  apply (modTwoClosed_supportCoefficient_iff_evenFaceIncidence
    (dyadicSpinFourSupport carrier spin)
    (dyadicSpinFourSupport_nodup carrier spin)).1
  rw [supportCoefficient_dyadicSpinFourSupport]
  exact dyadicSpinFourCoefficient_modTwoClosed hnodup spin hoddClosed

theorem dyadicSpinFourSupport_faceSpinTotal
    {carrier : List Z4Plaq} (hnodup : carrier.Nodup)
    (spin : Z4Plaq → Nat) {query : Z4Plaq}
    (hquery : query ∈ carrier) (hspin : spin query ≤ 4) :
    faceSpinPacketTotal
        (dyadicFaceSpinPacket
          (fun fine =>
            (supportCoefficient
              (dyadicSpinFourSupport carrier spin) fine).toNat)
          query) =
      spin query := by
  rw [supportCoefficient_dyadicSpinFourSupport]
  exact dyadicSpinFourCoefficient_faceSpinTotal
    hnodup spin hquery hspin

/-! ## 6. Exact corrected-slab boundary interface -/

/-- Minimal local boundary obligation for the selected bubble coefficient.
It asks for containment only when the spin-selected local coefficient is
true, so unused bubble layers are not charged. -/
def PairBubbleSlabAdmissible
    (fineExtent : Nat) (carrier : List Z4Plaq)
    (spin : Z4Plaq → Nat) : Prop :=
  ∀ coarse, coarse ∈ carrier → ∀ fine,
    localPairBubbleCoefficient spin coarse fine = true →
      fine ∈ boundaryCompleteSlabPlaquettes fineExtent

private theorem pairBubbleAssemblyCoefficient_true_mem_slab
    {fineExtent : Nat} {spin : Z4Plaq → Nat} {fine : Z4Plaq} :
    ∀ {carrier : List Z4Plaq},
      PairBubbleSlabAdmissible fineExtent carrier spin →
      pairBubbleAssemblyCoefficient spin carrier fine = true →
        fine ∈ boundaryCompleteSlabPlaquettes fineExtent
  | [], _, htrue => by cases htrue
  | coarse :: rest, hadmissible, htrue => by
      change
        (localPairBubbleCoefficient spin coarse fine ^^
          pairBubbleAssemblyCoefficient spin rest fine) = true at htrue
      rcases bool_or_of_xor_eq_true htrue with hlocal | hrest
      · exact hadmissible coarse List.mem_cons_self fine hlocal
      · exact pairBubbleAssemblyCoefficient_true_mem_slab
          (carrier := rest) (spin := spin)
          (fun source hsource selected hselected =>
            hadmissible source
              (List.mem_cons_of_mem coarse hsource) selected hselected)
          hrest

/-- The canonical finite support lies in the corrected fine slab once the
literal subdivision input is a coarse-slab carrier and the precisely selected
local bubbles satisfy the boundary interface above. -/
theorem dyadicSpinFourSupport_subset_boundaryCompleteFineSlab
    {coarseExtent : Nat} {carrier : List Z4Plaq}
    {spin : Z4Plaq → Nat}
    (hcarrier : ∀ coarse, coarse ∈ carrier →
      coarse ∈ boundaryCompleteSlabPlaquettes coarseExtent)
    (hbubbles : PairBubbleSlabAdmissible
      (dyadicSlabFineExtent coarseExtent) carrier spin) :
    ∀ fine, fine ∈ dyadicSpinFourSupport carrier spin →
      fine ∈ boundaryCompleteSlabPlaquettes
        (dyadicSlabFineExtent coarseExtent) := by
  intro fine hmem
  have htrue :=
    (mem_dyadicSpinFourSupport_iff carrier spin fine).mp hmem
  unfold dyadicSpinFourCoefficient at htrue
  change
    (supportCoefficient
        (dyadicSupportCells (oddSpinSupport carrier spin)) fine ^^
      pairBubbleAssemblyCoefficient spin carrier fine) = true at htrue
  rcases bool_or_of_xor_eq_true htrue with hsubdivision | hbubble
  · have hfine : fine ∈
        dyadicSupportCells (oddSpinSupport carrier spin) :=
      mem_of_supportCoefficient_eq_true hsubdivision
    apply dyadicSupportCells_subset_boundaryCompleteFineSlab
      (support := oddSpinSupport carrier spin)
    · intro coarse hodd
      exact hcarrier coarse (List.mem_filter.mp hodd).1
    · exact hfine
  · exact pairBubbleAssemblyCoefficient_true_mem_slab
      hbubbles hbubble

#print axioms modTwoClosed_pointwise_xor
#print axioms localPairBubbleCoefficient_modTwoClosed
#print axioms dyadicFaceSpinPacket_bothPairBubbles_target
#print axioms dyadicFaceSpinPacket_localPairBubbleCoefficient
#print axioms pairBubbleAssemblyCoefficient_modTwoClosed
#print axioms pairBubbleAssemblyCoefficient_eq_local_on_fibre
#print axioms dyadicFaceSpinPacket_pairBubbleAssemblyCoefficient
#print axioms dyadicSpinFourCoefficient_modTwoClosed
#print axioms dyadicFaceSpinPacket_pointwise_xor
#print axioms dyadicFaceSpinPacket_dyadicSpinFourCoefficient
#print axioms dyadicSpinFourCoefficient_faceSpinTotal
#print axioms dyadicSpinFourCoefficient_true_mem_ambient
#print axioms dyadicSpinFourSupport_nodup
#print axioms mem_dyadicSpinFourSupport_iff
#print axioms supportCoefficient_dyadicSpinFourSupport
#print axioms dyadicSpinFourSupport_evenFaceIncidence
#print axioms dyadicSpinFourSupport_faceSpinTotal
#print axioms pairBubbleAssemblyCoefficient_true_mem_slab
#print axioms dyadicSpinFourSupport_subset_boundaryCompleteFineSlab

end YMGap.Continuum.Z4DyadicSpinFourXorAssembly
