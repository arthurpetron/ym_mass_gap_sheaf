/-
# A same-geometry U(1) corrected-slab law and dyadic pushforward

This module constructs the abelian control side of the BF4 discriminator on
the *same corrected-slab geometry* as the SU(2) law.

Labels encode signed integer charges:

* `0` encodes charge `0`;
* `2n+1` encodes charge `+(n+1)`;
* `2n+2` encodes charge `-(n+1)`.

At every link the exact U(1) Haar rule is the Kronecker factor requiring the
oriented sum of incident face charges to vanish.  Face weights are the
Villain/heat coefficients `w^(charge^2)` already formalized as
`AbelianFusionCLT.abelCoeff`.

The dyadic block adds the four signed charges in the explicit
`dyadicFacePreimages` fibre.  A total bounded wrapper is used only to make the
map defined on arbitrary functions; it is definitionally within the coarse
charge carrier.  The resulting supported Dirac kernel pushes the normalized
fine U(1) law to a normalized coarse law.  No SU(2) parity or recoupling
amplitude is reused.

## Honest scope

This is a finite-cutoff physical U(1) law and an exact deterministic
pushforward.  Reflection positivity of its gauge-constrained Gram and removal
of the charge cutoff are separate theorems.

## Axiom gate

Finite lists, integers, and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.AbelianFusionCLT
import YMGap.Continuum.BF4ObservableMatchedOneStep
import YMGap.Continuum.CompactDualCutoffOneTotalKernel
import YMGap.Continuum.Z4DyadicModTwoCellularKernel
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.BF4U1SameCarrierPushforward

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

abbrev ChargeLabelling := EdgeLabelling

/-! ## 1. Signed charge encoding -/

/-- Decode a natural carrier label as a signed integer U(1) charge. -/
def decodeCharge : Nat → Int
  | 0 => 0
  | index + 1 =>
      if index % 2 = 0 then
        Int.ofNat (index / 2 + 1)
      else
        -(Int.ofNat (index / 2 + 1))

/-- Encode a signed integer charge back into the natural carrier. -/
def encodeCharge : Int → Nat
  | .ofNat magnitude =>
      if magnitude = 0 then 0 else 2 * magnitude - 1
  | .negSucc predecessor => 2 * (predecessor + 1)

/-- Absolute charge magnitude read directly from its alternating label. -/
def chargeMagnitude (label : Nat) : Nat :=
  (label + 1) / 2

@[simp] theorem decodeCharge_zero : decodeCharge 0 = 0 := rfl

@[simp] theorem chargeMagnitude_zero : chargeMagnitude 0 = 0 := rfl

@[simp] theorem encodeCharge_zero : encodeCharge 0 = 0 := rfl

/-- The alternating natural label records exactly the absolute value of its
decoded signed charge. -/
theorem decodeCharge_natAbs (label : Nat) :
    (decodeCharge label).natAbs = chargeMagnitude label := by
  cases label with
  | zero => rfl
  | succ index =>
      by_cases heven : index % 2 = 0
      · rw [decodeCharge, if_pos heven]
        change index / 2 + 1 = (index + 2) / 2
        omega
      · rw [decodeCharge, if_neg heven, Int.natAbs_neg]
        change index / 2 + 1 = (index + 2) / 2
        have hmod : index % 2 = 1 := by omega
        omega

/-- Encoding costs at most twice the absolute charge. -/
theorem encodeCharge_le_twice_natAbs (charge : Int) :
    encodeCharge charge ≤ 2 * charge.natAbs := by
  cases charge with
  | ofNat magnitude =>
      by_cases hzero : magnitude = 0
      · subst magnitude
        exact Nat.le_refl 0
      · simp only [encodeCharge, hzero, ↓reduceIte]
        change 2 * magnitude - 1 ≤ 2 * magnitude
        omega
  | negSucc predecessor =>
      simp [encodeCharge, Int.natAbs_negSucc]

/-- A carrier label bounded by `2K` decodes to charge magnitude at most `K`. -/
theorem chargeMagnitude_le_of_label_lt
    {label cutoff : Nat} (hlabel : label < 2 * cutoff + 1) :
    chargeMagnitude label ≤ cutoff := by
  unfold chargeMagnitude
  omega

/-! ## 2. Oriented U(1) Haar conservation on the corrected slab -/

/-- Standard oriented cubical boundary coefficient of a positively oriented
plaquette.  The edge order is

`(v,a) - (v,b) - (v+e_b,a) + (v+e_a,b)`.
-/
def orientedBoundaryCoefficient
    (plaquette : Z4Plaq) (link : Z4Link) : Int :=
  let a := (dirsOf plaquette.2).1
  let b := (dirsOf plaquette.2).2
  if link = (plaquette.1, a) then 1
  else if link = (plaquette.1, b) then -1
  else if link = (addE plaquette.1 b, a) then -1
  else if link = (addE plaquette.1 a, b) then 1
  else 0

def listIntSum {A : Type} (value : A → Int) : List A → Int
  | [] => 0
  | head :: tail => value head + listIntSum value tail

/-- Oriented charge divergence at one physical corrected-slab link. -/
def u1LinkCharge
    (extent : Nat) (state : ChargeLabelling) (link : Z4Link) : Int :=
  listIntSum
    (fun id =>
      orientedBoundaryCoefficient (slabPlaquetteAt extent id) link *
        decodeCharge (state id))
    (slabIncidentPlaqIds extent link)

/-- Exact U(1) Haar Fourier integral: one iff the total oriented charge
vanishes, zero otherwise. -/
def u1HaarLinkFactor
    (extent : Nat) (state : ChargeLabelling) (link : Z4Link) : Q' :=
  if u1LinkCharge extent state link = 0 then 1 else 0

theorem u1HaarLinkFactor_charge_conservation
    (extent : Nat) (state : ChargeLabelling) (link : Z4Link) :
    u1HaarLinkFactor extent state link = 1 ↔
      u1LinkCharge extent state link = 0 := by
  unfold u1HaarLinkFactor
  by_cases h : u1LinkCharge extent state link = 0
  · simp [h]
  · rw [if_neg h]
    constructor
    · intro hzeroOne
      exact absurd hzeroOne (by decide)
    · intro hzero
      exact absurd hzero h

/-! ## 3. Finite physical U(1) slab law -/

/-- Same corrected-slab geometry, now with a symmetric signed-charge cutoff.
`chargeCutoff = K` uses natural labels `0,...,2K`. -/
structure U1SlabData : Type where
  coupling : Q'
  coupling_nonnegative : (0 : Q') ≤ coupling
  chargeCutoff : Nat
  half : Nat

namespace U1SlabData

def extent (D : U1SlabData) : Nat :=
  centralExtent D.half

def labelCutoff (D : U1SlabData) : Nat :=
  2 * D.chargeCutoff

/-- The shared finite Cartesian carrier, packaged through the existing slab
geometry record.  Its SU(2) mass is not used. -/
def carrierData (D : U1SlabData) : SlabPhysicalData where
  coupling := D.coupling
  coupling_nonnegative := D.coupling_nonnegative
  cutoff := D.labelCutoff
  half := D.half

def faceEdges (D : U1SlabData) : List Nat :=
  D.carrierData.faceEdges

def states (D : U1SlabData) : List ChargeLabelling :=
  D.carrierData.physicalLabellings

def faceFactor (D : U1SlabData) (state : ChargeLabelling) : Q' :=
  listQProduct
    (fun id => abelCoeff D.coupling (chargeMagnitude (state id)))
    D.faceEdges

def haarFactor (D : U1SlabData) (state : ChargeLabelling) : Q' :=
  listQProduct
    (u1HaarLinkFactor D.extent state)
    (boundaryCompleteSlabLinks D.extent)

/-- Complete finite U(1) physical summand: heat face weights times all exact
link Haar constraints. -/
def physicalTerm (D : U1SlabData) (state : ChargeLabelling) : Q' :=
  D.faceFactor state * D.haarFactor state

def partition (D : U1SlabData) : Q' :=
  listQSum D.physicalTerm D.states

private theorem listQProduct_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQProduct value items
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (listQProduct_nonnegative_local value hvalue tail)

private theorem u1HaarLinkFactor_nonnegative
    (extent : Nat) (state : ChargeLabelling) (link : Z4Link) :
    (0 : Q') ≤ u1HaarLinkFactor extent state link := by
  unfold u1HaarLinkFactor
  split
  · exact Q'.zero_le_one
  · exact Q'.le_refl' 0

theorem physicalTerm_nonnegative
    (D : U1SlabData) (state : ChargeLabelling) :
    (0 : Q') ≤ D.physicalTerm state := by
  unfold physicalTerm faceFactor haarFactor
  exact Q'.mul_nonneg _ _
    (listQProduct_nonnegative_local _
      (fun id => abelCoeff_nonneg D.coupling_nonnegative
        (chargeMagnitude (state id))) _)
    (listQProduct_nonnegative_local _
      (u1HaarLinkFactor_nonnegative D.extent state) _)

private theorem listIntSum_zero_local {A : Type} :
    ∀ items : List A, listIntSum (fun _ => (0 : Int)) items = 0
  | [] => rfl
  | _ :: tail => by
      simp only [listIntSum, Int.zero_add]
      exact listIntSum_zero_local tail

theorem u1LinkCharge_zero
    (extent : Nat) (link : Z4Link) :
    u1LinkCharge extent zeroEdgeLabelling link = 0 := by
  unfold u1LinkCharge
  simpa [zeroEdgeLabelling] using
    (listIntSum_zero_local (slabIncidentPlaqIds extent link))

private theorem listQProduct_one_local {A : Type}
    (value : A → Q') :
    ∀ items : List A, (∀ item, item ∈ items → value item = 1) →
      listQProduct value items = 1
  | [], _ => rfl
  | head :: tail, hvalue => by
      simp only [listQProduct]
      rw [hvalue head List.mem_cons_self,
        listQProduct_one_local value tail
          (fun item hitem =>
            hvalue item (List.mem_cons_of_mem head hitem))]
      rfl

theorem physicalTerm_zero_eq_one (D : U1SlabData) :
    D.physicalTerm zeroEdgeLabelling = 1 := by
  unfold physicalTerm faceFactor haarFactor
  have hface :
      listQProduct
          (fun id =>
            abelCoeff D.coupling
              (chargeMagnitude (zeroEdgeLabelling id)))
          D.faceEdges = 1 := by
    apply listQProduct_one_local
    intro id _
    simp [zeroEdgeLabelling, abelCoeff_zero]
  have hhaar :
      listQProduct
          (u1HaarLinkFactor D.extent zeroEdgeLabelling)
          (boundaryCompleteSlabLinks D.extent) = 1 := by
    apply listQProduct_one_local
    intro link _
    simp [u1HaarLinkFactor, u1LinkCharge_zero]
  rw [hface, hhaar]
  rfl

theorem zero_mem_states (D : U1SlabData) :
    zeroEdgeLabelling ∈ D.states := by
  unfold states carrierData SlabPhysicalData.physicalLabellings
    SlabPhysicalData.faceEdges
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < D.labelCutoff + 1
    omega
  · intro _ _
    rfl

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A}, selected ∈ items →
      value selected ≤ listQSum value items
  | [], _, h => absurd h List.not_mem_nil
  | head :: tail, selected, h => by
      rcases List.mem_cons.mp h with heq | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · exact Q'.le_trans' _ _ _
          (listQSum_member_le_local value hvalue tail htail)
          (by
            have hadd := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail)
              (hvalue head)
            simpa only [Q'.zero_add'] using hadd)

theorem partition_one_le (D : U1SlabData) :
    (1 : Q') ≤ D.partition := by
  unfold partition
  have hmember := listQSum_member_le_local
    D.physicalTerm D.physicalTerm_nonnegative
    D.states D.zero_mem_states
  simpa [D.physicalTerm_zero_eq_one] using hmember

theorem partition_pos (D : U1SlabData) :
    (0 : Q') < D.partition :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide) D.partition_one_le

def normalizedMass
    (D : U1SlabData) (state : ChargeLabelling) : Q' :=
  Q'.divPos (D.physicalTerm state) D.partition D.partition_pos

theorem normalizedMass_nonnegative
    (D : U1SlabData) (state : ChargeLabelling) :
    (0 : Q') ≤ D.normalizedMass state := by
  unfold normalizedMass Q'.divPos
  exact Q'.mul_nonneg _ _ (D.physicalTerm_nonnegative state)
    (Q'.le_of_lt (Q'.recipPos_pos D.partition D.partition_pos))

theorem normalizedMass_total (D : U1SlabData) :
    listQSum D.normalizedMass D.states ≈ 1 := by
  unfold normalizedMass Q'.divPos partition
  exact Q'.eqv_trans _
    (D.partition * Q'.recipPos D.partition D.partition_pos) _
    (listQSum_mul_right D.physicalTerm
      (Q'.recipPos D.partition D.partition_pos) D.states)
    (Q'.mul_recipPos_eqv D.partition D.partition_pos)

end U1SlabData

/-! ## 4. Exact signed-charge dyadic block -/

def listChargeSum
    (charge : Z4Plaq → Int) : List Z4Plaq → Int
  | [] => 0
  | head :: tail => charge head + listChargeSum charge tail

/-- Direct signed sum over the four nondegenerate fine faces above one coarse
face. -/
def dyadicFaceChargeSum
    (fineExtent : Nat) (fineState : ChargeLabelling)
    (coarsePlaquette : Z4Plaq) : Int :=
  listChargeSum
    (fun finePlaquette =>
      decodeCharge
        (slabSpinAtPlaquette fineExtent fineState finePlaquette))
    (dyadicFacePreimages coarsePlaquette)

/-- Reading a listed U(1) state at any geometric plaquette stays within its
alternating signed-charge label cutoff; outside the slab it is zero. -/
theorem slabChargeLabel_lt
    {D : U1SlabData} {state : ChargeLabelling}
    (hstate : state ∈ D.states) (plaquette : Z4Plaq) :
    slabSpinAtPlaquette D.extent state plaquette <
      D.labelCutoff + 1 := by
  by_cases hslab :
      plaquette ∈ boundaryCompleteSlabPlaquettes D.extent
  · rw [slabSpinAtPlaquette_eq_of_mem hslab]
    have hidLt :=
      listIndexOf_lt_of_mem plaquette
        (boundaryCompleteSlabPlaquettes D.extent) hslab
    have hidMem :
        listIndexOf plaquette
            (boundaryCompleteSlabPlaquettes D.extent) ∈
          D.faceEdges := by
      unfold U1SlabData.faceEdges U1SlabData.carrierData
        SlabPhysicalData.faceEdges slabPhysicalFaceEdges
      exact List.mem_range.mpr hidLt
    exact
      (boundedEdgeLabellings_sound
        D.labelCutoff D.faceEdges state hstate).1 _ hidMem
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    omega

private theorem listChargeSum_natAbs_le_length_mul
    (charge : Z4Plaq → Int) (cutoff : Nat)
    (hcharge : ∀ plaquette, (charge plaquette).natAbs ≤ cutoff) :
    ∀ plaquettes : List Z4Plaq,
      (listChargeSum charge plaquettes).natAbs ≤
        plaquettes.length * cutoff
  | [] => by simp [listChargeSum]
  | head :: tail => by
      have hadd :
          (charge head + listChargeSum charge tail).natAbs ≤
            (charge head).natAbs +
              (listChargeSum charge tail).natAbs :=
        Int.natAbs_add_le _ _
      have hparts :
          (charge head).natAbs +
              (listChargeSum charge tail).natAbs ≤
            cutoff + tail.length * cutoff :=
        Nat.add_le_add (hcharge head)
          (listChargeSum_natAbs_le_length_mul
            charge cutoff hcharge tail)
      simp only [listChargeSum, List.length_cons]
      exact Nat.le_trans hadd
        (by
          calc
            (charge head).natAbs +
                (listChargeSum charge tail).natAbs
                ≤ cutoff + tail.length * cutoff := hparts
            _ = tail.length * cutoff + cutoff := Nat.add_comm _ _
            _ = (tail.length + 1) * cutoff := by
              rw [Nat.add_mul]
              simp)

/-- Four fine charges of magnitude at most `K` have total magnitude at most
`4K`. -/
theorem dyadicFaceChargeSum_natAbs_le_four
    {D : U1SlabData} {state : ChargeLabelling}
    (hstate : state ∈ D.states)
    (coarsePlaquette : Z4Plaq) :
    (dyadicFaceChargeSum D.extent state coarsePlaquette).natAbs ≤
      4 * D.chargeCutoff := by
  have hlabel : ∀ finePlaquette,
      (decodeCharge
        (slabSpinAtPlaquette D.extent state finePlaquette)).natAbs ≤
          D.chargeCutoff := by
    intro finePlaquette
    rw [decodeCharge_natAbs]
    exact chargeMagnitude_le_of_label_lt
      (slabChargeLabel_lt hstate finePlaquette)
  have hsum := listChargeSum_natAbs_le_length_mul
    (fun finePlaquette =>
      decodeCharge
        (slabSpinAtPlaquette D.extent state finePlaquette))
    D.chargeCutoff hlabel (dyadicFacePreimages coarsePlaquette)
  unfold dyadicFaceChargeSum
  obtain ⟨vertex, plane⟩ := coarsePlaquette
  cases plane <;> simpa [dyadicFacePreimages] using hsum

/-- Therefore the encoded direct four-charge sum is strictly inside the
coarse alternating label carrier. -/
theorem encode_dyadicFaceChargeSum_lt
    {D : U1SlabData} {state : ChargeLabelling}
    (hstate : state ∈ D.states)
    (coarsePlaquette : Z4Plaq) :
    encodeCharge (dyadicFaceChargeSum D.extent state coarsePlaquette) <
      2 * (4 * D.chargeCutoff) + 1 := by
  have hencode :=
    encodeCharge_le_twice_natAbs
      (dyadicFaceChargeSum D.extent state coarsePlaquette)
  have hsum :=
    dyadicFaceChargeSum_natAbs_le_four hstate coarsePlaquette
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans hencode (Nat.mul_le_mul_left 2 hsum))
    (Nat.lt_succ_self (2 * (4 * D.chargeCutoff)))

/-- Total bounded wrapper for a charge label.  On a physically bounded fine
state the direct four-charge sum lies in this branch; the zero branch only
totalizes the function away from that proof domain. -/
def boundedChargeLabel (chargeCutoff : Nat) (charge : Int) : Nat :=
  let label := encodeCharge charge
  if label < 2 * chargeCutoff + 1 then label else 0

/-- On every listed fine U(1) state the total wrapper is the literal encoded
signed-charge sum. -/
theorem boundedChargeLabel_dyadic_eq_direct
    {D : U1SlabData} {state : ChargeLabelling}
    (hstate : state ∈ D.states)
    (coarsePlaquette : Z4Plaq) :
    boundedChargeLabel (4 * D.chargeCutoff)
        (dyadicFaceChargeSum D.extent state coarsePlaquette) =
      encodeCharge
        (dyadicFaceChargeSum D.extent state coarsePlaquette) := by
  unfold boundedChargeLabel
  rw [if_pos (encode_dyadicFaceChargeSum_lt hstate coarsePlaquette)]

/-- The direct same-geometry U(1) block.  Four charges of magnitude at most
`K` produce a coarse carrier with charge cutoff `4K`. -/
def u1BlockState
    (G : CutoffOneGeometry) (fineChargeCutoff : Nat)
    (fineState : ChargeLabelling) : ChargeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges (centralExtent G.coarseHalf) then
      boundedChargeLabel (4 * fineChargeCutoff)
        (dyadicFaceChargeSum (centralExtent G.fineHalf) fineState
          (slabPlaquetteAt (centralExtent G.coarseHalf) id))
    else 0

def fineU1Data
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat) : U1SlabData where
  coupling := g
  coupling_nonnegative := hg
  chargeCutoff := fineChargeCutoff
  half := G.fineHalf

def coarseU1Data
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat) : U1SlabData where
  coupling := candidate
  coupling_nonnegative := Q'.le_of_lt hcandidate
  chargeCutoff := 4 * fineChargeCutoff
  half := G.coarseHalf

/-- On every physical fine state and physical coarse face, `u1BlockState` is
exactly the encoded sum of the four signed fine charges.  The totalization
fallback is absent from the physical pushforward. -/
theorem u1BlockState_eq_direct_on_physical
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    {fineState : ChargeLabelling}
    (hfine :
      fineState ∈ (fineU1Data G g hg fineChargeCutoff).states)
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈
      slabPhysicalFaceEdges (centralExtent G.coarseHalf)) :
    u1BlockState G fineChargeCutoff fineState coarseFaceId =
      encodeCharge
        (dyadicFaceChargeSum (centralExtent G.fineHalf) fineState
          (slabPlaquetteAt (centralExtent G.coarseHalf) coarseFaceId)) := by
  unfold u1BlockState
  rw [if_pos hface]
  simpa [fineU1Data, U1SlabData.extent] using
    (boundedChargeLabel_dyadic_eq_direct
      (D := fineU1Data G g hg fineChargeCutoff)
      hfine
      (slabPlaquetteAt (centralExtent G.coarseHalf) coarseFaceId))

theorem u1BlockState_mem_coarse
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (fineState : ChargeLabelling) :
    u1BlockState G fineChargeCutoff fineState ∈
      (coarseU1Data G candidate hcandidate fineChargeCutoff).states := by
  unfold U1SlabData.states U1SlabData.carrierData
    SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
    U1SlabData.labelCutoff
  apply boundedEdgeLabellings_complete
  · intro id hid
    change id ∈
      slabPhysicalFaceEdges (centralExtent G.coarseHalf) at hid
    change
      u1BlockState G fineChargeCutoff fineState id <
        2 * (4 * fineChargeCutoff) + 1
    unfold u1BlockState
    rw [if_pos hid]
    simp only [boundedChargeLabel]
    split
    · omega
    · omega
  · intro id hid
    change id ∉
      slabPhysicalFaceEdges (centralExtent G.coarseHalf) at hid
    change u1BlockState G fineChargeCutoff fineState id = 0
    unfold u1BlockState
    rw [if_neg hid]

/-! ## 5. The normalized deterministic U(1) pushforward -/

def u1BlockKernel
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (fineState coarseState : ChargeLabelling) : Q' :=
  let coarse :=
    coarseU1Data G candidate hcandidate fineChargeCutoff
  supportedDirac coarse.faceEdges
    (u1BlockState G fineChargeCutoff fineState) coarseState

def u1BlockedMass
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coarseState : ChargeLabelling) : Q' :=
  let fine := fineU1Data G g hg fineChargeCutoff
  listQSum
    (fun fineState =>
      fine.normalizedMass fineState *
        u1BlockKernel G candidate hcandidate fineChargeCutoff
          fineState coarseState)
    fine.states

theorem u1BlockKernel_nonnegative
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (fineState coarseState : ChargeLabelling) :
    (0 : Q') ≤
      u1BlockKernel G candidate hcandidate fineChargeCutoff
        fineState coarseState := by
  unfold u1BlockKernel
  exact supportedDirac_nonnegative _ _ _

theorem u1BlockedMass_nonnegative
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coarseState : ChargeLabelling) :
    (0 : Q') ≤
      u1BlockedMass G g hg candidate hcandidate
        fineChargeCutoff coarseState := by
  unfold u1BlockedMass
  apply listQSum_nonnegative_on
  intro fineState _
  exact Q'.mul_nonneg _ _
    ((fineU1Data G g hg fineChargeCutoff).normalizedMass_nonnegative
      fineState)
    (u1BlockKernel_nonnegative G candidate hcandidate
      fineChargeCutoff fineState coarseState)

theorem u1BlockKernel_row_normalized
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (fineState : ChargeLabelling) :
    listQSum
        (u1BlockKernel G candidate hcandidate fineChargeCutoff fineState)
        (coarseU1Data G candidate hcandidate fineChargeCutoff).states ≈
      1 := by
  unfold u1BlockKernel U1SlabData.states
  exact supportedDirac_slab_row_normalized
    (coarseU1Data G candidate hcandidate fineChargeCutoff).carrierData
    (u1BlockState_mem_coarse G candidate hcandidate
      fineChargeCutoff fineState)

/-- The same-geometry U(1) pushforward is an exact probability law. -/
theorem u1BlockedMass_total
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat) :
    listQSum
        (u1BlockedMass G g hg candidate hcandidate fineChargeCutoff)
        (coarseU1Data G candidate hcandidate fineChargeCutoff).states ≈
      1 := by
  let fine := fineU1Data G g hg fineChargeCutoff
  let coarse :=
    coarseU1Data G candidate hcandidate fineChargeCutoff
  refine Q'.eqv_trans _
    (listQSum
      (fun fineState =>
        listQSum
          (fun coarseState =>
            fine.normalizedMass fineState *
              u1BlockKernel G candidate hcandidate fineChargeCutoff
                fineState coarseState)
          coarse.states)
      fine.states) _ ?_ ?_
  · unfold u1BlockedMass
    exact listQSum_swap
      (fun fineState coarseState =>
        fine.normalizedMass fineState *
          u1BlockKernel G candidate hcandidate fineChargeCutoff
            fineState coarseState)
      fine.states coarse.states
  · refine Q'.eqv_trans _
      (listQSum (fun fineState => fine.normalizedMass fineState)
        fine.states) _ ?_ fine.normalizedMass_total
    apply listQSum_congr_on
    intro fineState _
    refine Q'.eqv_trans _
      (fine.normalizedMass fineState *
        listQSum
          (u1BlockKernel G candidate hcandidate
            fineChargeCutoff fineState)
          coarse.states) _
      (listQSum_mul_left
        (fine.normalizedMass fineState)
        (u1BlockKernel G candidate hcandidate
          fineChargeCutoff fineState)
        coarse.states)
      ?_
    exact Q'.eqv_trans _ _
      (fine.normalizedMass fineState)
      (Q'.mul_eqv_congr_left _ _ _
        (u1BlockKernel_row_normalized G candidate hcandidate
          fineChargeCutoff fineState))
      (Q'.mul_one_eqv _)

end YMGap.Continuum.BF4U1SameCarrierPushforward

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.u1HaarLinkFactor_charge_conservation
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.U1SlabData.physicalTerm_nonnegative
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.U1SlabData.physicalTerm_zero_eq_one
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.U1SlabData.partition_pos
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.U1SlabData.normalizedMass_total
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.decodeCharge_natAbs
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.dyadicFaceChargeSum_natAbs_le_four
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.u1BlockState_eq_direct_on_physical
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.u1BlockState_mem_coarse
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.u1BlockedMass_nonnegative
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.u1BlockKernel_row_normalized
#print axioms YMGap.Continuum.BF4U1SameCarrierPushforward.u1BlockedMass_total
