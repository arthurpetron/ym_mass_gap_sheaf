/-
# A one-charge tail bridge for the genuine finite BF4 U(1) exponent Gram

This module keeps the already-constructed normalized U(1) slab law fixed and
cuts only its finite signed-charge carrier.  A state is retained when every
physical face has charge magnitude at most `M`.  If a state is omitted, one
of its face factors is an `abelCoeff` above `M`; hence a supplied one-charge
tail bounds the entire physical summand.  All remaining face and Haar
factors lie in `[0,1]`.

For a slab datum `D`, the resulting explicit amplification is

    ofNat D.states.length * oneChargeTail M.

The generic reflection-quadratic bound is specialized twice:

* to the genuine orientation-correct exponent-Gram diagonal identified in
  `BF4U1ExponentGramPositivity`;
* through `u1BlockedFullReflectionQuadratic_eq_finePullback`, to the actual
  deterministic BF4 blocked law of `BF4U1BlockReflectionCP`.

The analytic one-charge decay is deliberately supplied as data.  The theorem
here is the finite-carrier lifting step, not an assertion of a new U(1)
Poisson/theta tail.

## Constructivity

The omitted-charge witness is a finite-list sigma datum.  There is no
`Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4U1BlockReflectionCP

namespace YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1BlockReflectionCP
open YMGap.Continuum.BF4U1ExponentGramPositivity
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1TwistedPhysicalReindex
open YMGap.Continuum.BF4U1TwistedReflectionGram
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A finite same-carrier charge cutoff -/

/-- Boolean test that all named face charges have magnitude at most `cutoff`.
The explicit list recursion gives a constructive omitted-face witness. -/
def chargeWithinOn
    (cutoff : Nat) (state : ChargeLabelling) :
    List Nat → Bool
  | [] => true
  | id :: rest =>
      decide (chargeMagnitude (state id) ≤ cutoff) &&
        chargeWithinOn cutoff state rest

/-- A full slab state lies in the retained charge window on every physical
face of `D`. -/
def u1StateWithinChargeCutoff
    (D : U1SlabData) (cutoff : Nat)
    (state : ChargeLabelling) : Bool :=
  chargeWithinOn cutoff state D.faceEdges

/-- If the finite Boolean test fails, it returns an actual offending face as
`Type`-level data. -/
def chargeWithinOn_false_witness
    (cutoff : Nat) (state : ChargeLabelling) :
    ∀ ids : List Nat,
      chargeWithinOn cutoff state ids = false →
      Σ' id : Nat,
        id ∈ ids ∧
          cutoff < chargeMagnitude (state id)
  | [], hfalse => by
      simp [chargeWithinOn] at hfalse
  | id :: rest, hfalse => by
      by_cases hid :
          chargeMagnitude (state id) ≤ cutoff
      · have hrest :
          chargeWithinOn cutoff state rest = false := by
          simpa [chargeWithinOn, hid] using hfalse
        let witness :=
          chargeWithinOn_false_witness
            cutoff state rest hrest
        exact
          ⟨witness.1,
            List.mem_cons_of_mem id witness.2.1,
            witness.2.2⟩
      · exact
          ⟨id, List.mem_cons_self,
            Nat.lt_of_not_ge hid⟩

/-- Slab-level omitted-state witness. -/
def u1StateOutsideChargeCutoff_witness
    (D : U1SlabData) (cutoff : Nat)
    (state : ChargeLabelling)
    (houtside :
      u1StateWithinChargeCutoff
        D cutoff state = false) :
    Σ' id : Nat,
      id ∈ D.faceEdges ∧
        cutoff < chargeMagnitude (state id) :=
  chargeWithinOn_false_witness
    cutoff state D.faceEdges houtside

/-! ## 2. Supplied one-charge analytic data -/

/-- A supplied pointwise tail for one U(1) Fourier charge. -/
structure OneChargeTail (D : U1SlabData) : Type where
  tail : Nat → Q'
  tail_nonnegative :
    ∀ cutoff, (0 : Q') ≤ tail cutoff
  charge_bound :
    ∀ cutoff charge,
      cutoff < charge →
      abelCoeff D.coupling charge ≤ tail cutoff

/-- A fully explicit tolerance-to-cutoff package for the one-charge tail
after the finite carrier amplification required below. -/
structure OneChargeTailModulus
    (D : U1SlabData) : Type extends OneChargeTail D where
  cutoff : Q' → Nat
  scaled_tail :
    ∀ ε : Q', (0 : Q') < ε →
      ∀ M : Nat, cutoff ε ≤ M →
        Q'.ofNat D.states.length * tail M ≤ ε

/-! ## 3. Product and finite-sum order helpers -/

private theorem listQProduct_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A,
      (0 : Q') ≤ listQProduct value items
  | [] => Q'.zero_le_one
  | head :: rest =>
      Q'.mul_nonneg _ _
        (hvalue head)
        (listQProduct_nonnegative_local
          value hvalue rest)

private theorem listQProduct_le_one_local
    {A : Type} (value : A → Q')
    (hvalue0 : ∀ item, (0 : Q') ≤ value item)
    (hvalue1 : ∀ item, value item ≤ (1 : Q')) :
    ∀ items : List A,
      listQProduct value items ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | head :: rest => by
      have hrest0 :=
        listQProduct_nonnegative_local
          value hvalue0 rest
      have hmul :
          value head *
              listQProduct value rest ≤
            (1 : Q') *
              listQProduct value rest :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _
          (hvalue1 head) hrest0
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.one_mul_eqv
              (listQProduct value rest)))
          (listQProduct_le_one_local
            value hvalue0 hvalue1 rest))

private theorem listQProduct_le_selected_local
    {A : Type} (value : A → Q')
    (hvalue0 : ∀ item, (0 : Q') ≤ value item)
    (hvalue1 : ∀ item, value item ≤ (1 : Q'))
    (selected : A) :
    ∀ items : List A,
      selected ∈ items →
      listQProduct value items ≤ value selected
  | [], hmem => by
      simp at hmem
  | head :: rest, hmem => by
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst head
        have hselected0 := hvalue0 selected
        have hrest1 :=
          listQProduct_le_one_local
            value hvalue0 hvalue1 rest
        have hmul :
            value selected *
                listQProduct value rest ≤
              value selected * (1 : Q') :=
          Q'.mul_le_mul_of_nonneg_left
            _ _ (value selected)
            hrest1 hselected0
        exact Q'.le_trans' _ _ _ hmul
          (Q'.le_of_eqv
            (Q'.mul_one_eqv
              (value selected)))
      · have htail :=
          listQProduct_le_selected_local
            value hvalue0 hvalue1
            selected rest hrest
        have hhead0 := hvalue0 head
        have hscale :
            value head *
                listQProduct value rest ≤
              value head * value selected :=
          Q'.mul_le_mul_of_nonneg_left
            _ _ (value head) htail hhead0
        have hhead1 := hvalue1 head
        have hselected0 := hvalue0 selected
        have hcap :
            value head * value selected ≤
              (1 : Q') * value selected :=
          Q'.mul_le_mul_of_nonneg_right
            _ _ (value selected)
            hhead1 hselected0
        exact Q'.le_trans' _ _ _ hscale
          (Q'.le_trans' _ _ _ hcap
            (Q'.le_of_eqv
              (Q'.one_mul_eqv
                (value selected))))

private theorem listQSum_mono_local
    {A : Type} (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items →
        lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: rest, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_local
          lower upper rest
          (fun item hitem =>
            hbound item
              (List.mem_cons_of_mem head hitem)))

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q')
    {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items →
        value item ≤ bound) →
      listQSum value items ≤
        Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.zero_mul_eqv bound))
  | head :: rest, hbound => by
      have hhead :=
        hbound head List.mem_cons_self
      have hrest :=
        listQSum_le_length_mul_local
          value hbound0 rest
          (fun item hitem =>
            hbound item
              (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value rest ≤
            bound +
              Q'.ofNat rest.length * bound :=
        Q'.add_le_add hhead hrest
      have htarget :
          bound +
              Q'.ofNat rest.length * bound ≈
            Q'.ofNat (head :: rest).length *
              bound := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            bound
            ((1 : Q') * bound)
            (Q'.ofNat rest.length * bound)
            (Q'.eqv_symm
              (Q'.one_mul_eqv bound))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              1 (Q'.ofNat rest.length) bound)) ?_
        apply Q'.mul_eqv_congr_right
        exact Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv
            1 (Q'.ofNat rest.length))
          (Q'.eqv_symm
            (YMGap.Continuum.HKConvGen.ofNat_succ_eqv
              rest.length))
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv htarget)

/-! ## 4. One omitted charge bounds a complete normalized state -/

theorem abelCoeff_le_one
    {D : U1SlabData}
    (hcoupling : D.coupling ≤ (1 : Q'))
    (charge : Nat) :
    abelCoeff D.coupling charge ≤ (1 : Q') :=
  YMGap.Continuum.HeatKernelGap.qpow_le_one
    D.coupling_nonnegative hcoupling _

theorem u1HaarLinkFactor_le_one
    (extent : Nat) (state : ChargeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    u1HaarLinkFactor extent state link ≤ (1 : Q') := by
  unfold u1HaarLinkFactor
  split
  · exact Q'.le_refl' 1
  · exact Q'.zero_le_one

theorem u1FaceFactor_le_one
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (state : ChargeLabelling) :
    D.faceFactor state ≤ (1 : Q') := by
  unfold U1SlabData.faceFactor
  exact listQProduct_le_one_local
    (fun id =>
      abelCoeff D.coupling
        (chargeMagnitude (state id)))
    (fun id =>
      abelCoeff_nonneg
        D.coupling_nonnegative _)
    (fun id =>
      abelCoeff_le_one
        hcoupling _)
    D.faceEdges

theorem u1HaarFactor_le_one
    (D : U1SlabData)
    (state : ChargeLabelling) :
    D.haarFactor state ≤ (1 : Q') := by
  unfold U1SlabData.haarFactor
  exact listQProduct_le_one_local
    (u1HaarLinkFactor D.extent state)
    (fun link => by
      unfold u1HaarLinkFactor
      split
      · exact Q'.zero_le_one
      · exact Q'.le_refl' 0)
    (u1HaarLinkFactor_le_one
      D.extent state)
    (boundaryCompleteSlabLinks D.extent)

theorem u1FaceFactor_le_oneChargeTail_of_outside
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (cutoff : Nat) (state : ChargeLabelling)
    (houtside :
      u1StateWithinChargeCutoff
        D cutoff state = false) :
    D.faceFactor state ≤ tailData.tail cutoff := by
  let witness :=
    u1StateOutsideChargeCutoff_witness
      D cutoff state houtside
  have hselected :
      listQProduct
          (fun id =>
            abelCoeff D.coupling
              (chargeMagnitude (state id)))
          D.faceEdges ≤
        abelCoeff D.coupling
          (chargeMagnitude (state witness.1)) :=
    listQProduct_le_selected_local
      (fun id =>
        abelCoeff D.coupling
          (chargeMagnitude (state id)))
      (fun id =>
        abelCoeff_nonneg
          D.coupling_nonnegative _)
      (fun id =>
        abelCoeff_le_one hcoupling _)
      witness.1 D.faceEdges witness.2.1
  unfold U1SlabData.faceFactor
  exact Q'.le_trans' _ _ _ hselected
    (tailData.charge_bound
      cutoff
      (chargeMagnitude (state witness.1))
      witness.2.2)

theorem u1PhysicalTerm_le_oneChargeTail_of_outside
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (cutoff : Nat) (state : ChargeLabelling)
    (houtside :
      u1StateWithinChargeCutoff
        D cutoff state = false) :
    D.physicalTerm state ≤ tailData.tail cutoff := by
  unfold U1SlabData.physicalTerm
  have hface :=
    u1FaceFactor_le_oneChargeTail_of_outside
      D hcoupling tailData cutoff state houtside
  have hhaar0 :=
    listQProduct_nonnegative_local
      (u1HaarLinkFactor D.extent state)
      (fun link => by
        unfold u1HaarLinkFactor
        split
        · exact Q'.zero_le_one
        · exact Q'.le_refl' 0)
      (boundaryCompleteSlabLinks D.extent)
  have hscaled :
      D.faceFactor state * D.haarFactor state ≤
        tailData.tail cutoff * D.haarFactor state :=
    Q'.mul_le_mul_of_nonneg_right
      _ _ _ hface hhaar0
  have hcap :
      tailData.tail cutoff * D.haarFactor state ≤
        tailData.tail cutoff * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left
      _ _ _
      (u1HaarFactor_le_one D state)
      (tailData.tail_nonnegative cutoff)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ hcap
      (Q'.le_of_eqv
        (Q'.mul_one_eqv
          (tailData.tail cutoff))))

theorem u1NormalizedMass_le_oneChargeTail_of_outside
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (cutoff : Nat) (state : ChargeLabelling)
    (houtside :
      u1StateWithinChargeCutoff
        D cutoff state = false) :
    D.normalizedMass state ≤ tailData.tail cutoff := by
  have hphysicalPartition :
      D.physicalTerm state ≤
        D.physicalTerm state * D.partition := by
    have hscaled :
        D.physicalTerm state * (1 : Q') ≤
          D.physicalTerm state * D.partition :=
      Q'.mul_le_mul_of_nonneg_left
        _ _ _
        D.partition_one_le
        (D.physicalTerm_nonnegative state)
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (Q'.mul_one_eqv
          (D.physicalTerm state)))
      hscaled
  have hnormalizedPhysical :
      D.normalizedMass state ≤
        D.physicalTerm state := by
    unfold U1SlabData.normalizedMass
    exact Q'.divPos_le_of_le_mul
      (D.physicalTerm state)
      D.partition D.partition_pos
      hphysicalPartition
  exact Q'.le_trans' _ _ _
    hnormalizedPhysical
    (u1PhysicalTerm_le_oneChargeTail_of_outside
      D hcoupling tailData cutoff state houtside)

/-! ## 5. Cutoff reflection quadratics on the genuine normalized law -/

/-- The genuine normalized orientation-correct reflection quadratic with
high-charge full states masked out on the same finite carrier. -/
def u1FullNormalizedReflectionChargeCutoff
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q')
    (cutoff : Nat) : Q' :=
  listQSum
    (fun physical =>
      if u1StateWithinChargeCutoff
          D cutoff physical then
        (coefficient
            (centralLowerRestriction D.half physical) *
          coefficient
            (u1ReflectedUpperRestriction
              D.half physical)) *
        D.normalizedMass physical
      else 0)
    D.states

private def u1FullNormalizedReflectionOmitted
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q')
    (cutoff : Nat) : Q' :=
  listQSum
    (fun physical =>
      if u1StateWithinChargeCutoff
          D cutoff physical then 0
      else
        (coefficient
            (centralLowerRestriction D.half physical) *
          coefficient
            (u1ReflectedUpperRestriction
              D.half physical)) *
        D.normalizedMass physical)
    D.states

private theorem cutoff_add_omitted_eqv_full
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q')
    (cutoff : Nat) :
    u1FullNormalizedReflectionChargeCutoff
          D coefficient cutoff +
        u1FullNormalizedReflectionOmitted
          D coefficient cutoff ≈
      u1FullNormalizedMassReflectionQuadratic
        D coefficient := by
  unfold u1FullNormalizedReflectionChargeCutoff
    u1FullNormalizedReflectionOmitted
    u1FullNormalizedMassReflectionQuadratic
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_add
        (fun physical =>
          if u1StateWithinChargeCutoff
              D cutoff physical then
            (coefficient
                (centralLowerRestriction D.half physical) *
              coefficient
                (u1ReflectedUpperRestriction
                  D.half physical)) *
            D.normalizedMass physical
          else 0)
        (fun physical =>
          if u1StateWithinChargeCutoff
              D cutoff physical then 0
          else
            (coefficient
                (centralLowerRestriction D.half physical) *
              coefficient
                (u1ReflectedUpperRestriction
                  D.half physical)) *
            D.normalizedMass physical)
        D.states)) ?_
  apply listQSum_congr_on
  intro physical hphysical
  cases hwithin :
      u1StateWithinChargeCutoff D cutoff physical
  · exact Q'.eqv_of_eq
      (Q'.zero_add' _)
  · exact Q'.eqv_of_eq
      (Q'.add_zero' _)

theorem u1FullNormalizedReflectionOmitted_le
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coefficient : ChargeLabelling → Q')
    (coefficient_nonnegative :
      ∀ state, (0 : Q') ≤ coefficient state)
    (coefficient_le_one :
      ∀ state, coefficient state ≤ (1 : Q'))
    (cutoff : Nat) :
    u1FullNormalizedReflectionOmitted
        D coefficient cutoff ≤
      Q'.ofNat D.states.length *
        tailData.tail cutoff := by
  unfold u1FullNormalizedReflectionOmitted
  apply listQSum_le_length_mul_local
    _ (tailData.tail_nonnegative cutoff)
  intro physical hphysical
  cases hwithin :
      u1StateWithinChargeCutoff
        D cutoff physical
  · have hlower0 :=
      coefficient_nonnegative
        (centralLowerRestriction
          D.half physical)
    have hlower1 :=
      coefficient_le_one
        (centralLowerRestriction
          D.half physical)
    have hupper0 :=
      coefficient_nonnegative
        (u1ReflectedUpperRestriction
          D.half physical)
    have hupper1 :=
      coefficient_le_one
        (u1ReflectedUpperRestriction
          D.half physical)
    have hproduct0 :
        (0 : Q') ≤
          coefficient
              (centralLowerRestriction
                D.half physical) *
            coefficient
              (u1ReflectedUpperRestriction
                D.half physical) :=
      Q'.mul_nonneg _ _ hlower0 hupper0
    have hproduct1 :
        coefficient
              (centralLowerRestriction
                D.half physical) *
            coefficient
              (u1ReflectedUpperRestriction
                D.half physical) ≤
          (1 : Q') := by
      have hscale :
          coefficient
                (centralLowerRestriction
                  D.half physical) *
              coefficient
                (u1ReflectedUpperRestriction
                  D.half physical) ≤
            (1 : Q') *
              coefficient
                (u1ReflectedUpperRestriction
                  D.half physical) :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ hlower1 hupper0
      exact Q'.le_trans' _ _ _ hscale
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.one_mul_eqv _))
          hupper1)
    have hmass0 :=
      D.normalizedMass_nonnegative physical
    have hscaled :
        (coefficient
              (centralLowerRestriction
                D.half physical) *
            coefficient
              (u1ReflectedUpperRestriction
                D.half physical)) *
            D.normalizedMass physical ≤
          (1 : Q') *
            D.normalizedMass physical :=
      Q'.mul_le_mul_of_nonneg_right
        _ _ _ hproduct1 hmass0
    have hmassTail :=
      u1NormalizedMass_le_oneChargeTail_of_outside
        D hcoupling tailData cutoff physical hwithin
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.one_mul_eqv
            (D.normalizedMass physical)))
        hmassTail)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.zero_add' 0 ▸ Q'.eqv_refl 0))
      (tailData.tail_nonnegative cutoff)

/-- The full genuine reflection quadratic differs from its same-carrier
charge cutoff by at most the explicit carrier-count amplification. -/
theorem u1FullNormalizedReflectionChargeCutoff_tail_upper
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coefficient : ChargeLabelling → Q')
    (coefficient_nonnegative :
      ∀ state, (0 : Q') ≤ coefficient state)
    (coefficient_le_one :
      ∀ state, coefficient state ≤ (1 : Q'))
    (cutoff : Nat) :
    u1FullNormalizedMassReflectionQuadratic
          D coefficient +
        -u1FullNormalizedReflectionChargeCutoff
          D coefficient cutoff ≤
      Q'.ofNat D.states.length *
        tailData.tail cutoff := by
  have hsplit :=
    cutoff_add_omitted_eqv_full
      D coefficient cutoff
  have homitted :=
    u1FullNormalizedReflectionOmitted_le
      D hcoupling tailData coefficient
      coefficient_nonnegative coefficient_le_one
      cutoff
  have hfull :
      u1FullNormalizedMassReflectionQuadratic
          D coefficient ≤
        u1FullNormalizedReflectionChargeCutoff
            D coefficient cutoff +
          Q'.ofNat D.states.length *
            tailData.tail cutoff := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hsplit)
      (Q'.add_le_add_left
        (u1FullNormalizedReflectionChargeCutoff
          D coefficient cutoff)
        _ _ homitted)
  exact Q'.sub_le_of_le_add hfull

/-! ## 6. Genuine exponent-Gram specialization -/

theorem u1ExponentCoefficient_nonnegative
    (half exponent : Nat)
    (state : ChargeLabelling) :
    (0 : Q') ≤
      u1ExponentCoefficient half exponent state := by
  unfold u1ExponentCoefficient
  split
  · exact Q'.zero_le_one
  · exact Q'.le_refl' 0

theorem u1ExponentCoefficient_le_one
    (half exponent : Nat)
    (state : ChargeLabelling) :
    u1ExponentCoefficient half exponent state ≤
      (1 : Q') := by
  unfold u1ExponentCoefficient
  split
  · exact Q'.le_refl' 1
  · exact Q'.zero_le_one

/-- Same-carrier cutoff approximation to the genuine diagonal exponent Gram. -/
def u1ExponentGramDiagonalChargeCutoff
    (D : U1SlabData)
    (exponent cutoff : Nat) : Q' :=
  u1FullNormalizedReflectionChargeCutoff
    D (u1ExponentCoefficient D.half exponent)
    cutoff

/-- Explicit finite-carrier tail for the existing exponent-Gram diagonal. -/
theorem u1ExponentGramDiagonalChargeCutoff_tail
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (exponent cutoff : Nat) :
    u1ExponentGramEntry
          D.half D.states D.normalizedMass
          { leftExponent := exponent,
            rightExponent := exponent } +
        -u1ExponentGramDiagonalChargeCutoff
          D exponent cutoff ≤
      Q'.ofNat D.states.length *
        tailData.tail cutoff := by
  have hfull :=
    u1FullNormalizedReflectionChargeCutoff_tail_upper
      D hcoupling tailData
      (u1ExponentCoefficient D.half exponent)
      (u1ExponentCoefficient_nonnegative
        D.half exponent)
      (u1ExponentCoefficient_le_one
        D.half exponent)
      cutoff
  have hentry :=
    u1ExponentGramEntry_diagonal_eq_fullNormalized
      D exponent
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_eqv_congr_right
        _ _ _
        hentry))
    hfull

/-- The supplied scaled modulus becomes an explicit convergence modulus for
the genuine finite-carrier exponent-Gram diagonal. -/
theorem u1ExponentGramDiagonalChargeCutoff_modulus
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTailModulus D)
    (exponent : Nat)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat) (hM : tailData.cutoff ε ≤ M) :
    u1ExponentGramEntry
          D.half D.states D.normalizedMass
          { leftExponent := exponent,
            rightExponent := exponent } +
        -u1ExponentGramDiagonalChargeCutoff
          D exponent M ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (u1ExponentGramDiagonalChargeCutoff_tail
      D hcoupling tailData.toOneChargeTail
      exponent M)
    (tailData.scaled_tail ε hε M hM)

/-! ## 7. Deterministic BF4 block / CP specialization -/

/-- Fine-carrier charge cutoff for the actual blocked exponent-Gram
coordinate, written through its proved fine pullback. -/
def u1BlockedExponentGramDiagonalChargeCutoff
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff exponent retainedCharge : Nat) :
    Q' :=
  u1FullNormalizedReflectionChargeCutoff
    (fineU1Data G g hg fineChargeCutoff)
    (u1BlockPullbackCoefficient
      G fineChargeCutoff
      (u1ExponentCoefficient
        G.coarseHalf exponent))
    retainedCharge

private theorem u1BlockExponentPullback_nonnegative
    (G : CutoffOneGeometry)
    (fineChargeCutoff exponent : Nat)
    (state : ChargeLabelling) :
    (0 : Q') ≤
      u1BlockPullbackCoefficient
        G fineChargeCutoff
        (u1ExponentCoefficient
          G.coarseHalf exponent)
        state := by
  unfold u1BlockPullbackCoefficient
  exact u1ExponentCoefficient_nonnegative
    G.coarseHalf exponent _

private theorem u1BlockExponentPullback_le_one
    (G : CutoffOneGeometry)
    (fineChargeCutoff exponent : Nat)
    (state : ChargeLabelling) :
    u1BlockPullbackCoefficient
        G fineChargeCutoff
        (u1ExponentCoefficient
          G.coarseHalf exponent)
        state ≤ (1 : Q') := by
  unfold u1BlockPullbackCoefficient
  exact u1ExponentCoefficient_le_one
    G.coarseHalf exponent _

private theorem u1BlockedExponentGramEntry_eq_fineQuadratic
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff exponent : Nat) :
    u1BlockedExponentGramEntry
        G g hg candidate hcandidate fineChargeCutoff
        { leftExponent := exponent,
          rightExponent := exponent } ≈
      u1FullNormalizedMassReflectionQuadratic
        (fineU1Data G g hg fineChargeCutoff)
        (u1BlockPullbackCoefficient
          G fineChargeCutoff
          (u1ExponentCoefficient
            G.coarseHalf exponent)) := by
  exact Q'.eqv_trans _ _ _
    (u1BlockedExponentGramEntry_diagonal_eq_full
      G g hg candidate hcandidate
      fineChargeCutoff exponent)
    (u1BlockedFullReflectionQuadratic_eq_finePullback
      G g hg candidate hcandidate
      fineChargeCutoff
      (u1ExponentCoefficient
        G.coarseHalf exponent))

/-- Explicit one-charge tail lifted through the actual deterministic BF4
block and its CP-preserving fine-pullback identity. -/
theorem u1BlockedExponentGramDiagonalChargeCutoff_tail
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (hg1 : g ≤ (1 : Q'))
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (tailData :
      OneChargeTail
        (fineU1Data G g hg fineChargeCutoff))
    (exponent retainedCharge : Nat) :
    u1BlockedExponentGramEntry
          G g hg candidate hcandidate fineChargeCutoff
          { leftExponent := exponent,
            rightExponent := exponent } +
        -u1BlockedExponentGramDiagonalChargeCutoff
          G g hg fineChargeCutoff exponent retainedCharge ≤
      Q'.ofNat
          (fineU1Data G g hg
            fineChargeCutoff).states.length *
        tailData.tail retainedCharge := by
  have hfull :=
    u1FullNormalizedReflectionChargeCutoff_tail_upper
      (fineU1Data G g hg fineChargeCutoff)
      hg1 tailData
      (u1BlockPullbackCoefficient
        G fineChargeCutoff
        (u1ExponentCoefficient
          G.coarseHalf exponent))
      (u1BlockExponentPullback_nonnegative
        G fineChargeCutoff exponent)
      (u1BlockExponentPullback_le_one
        G fineChargeCutoff exponent)
      retainedCharge
  have hentry :=
    u1BlockedExponentGramEntry_eq_fineQuadratic
      G g hg candidate hcandidate
      fineChargeCutoff exponent
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_eqv_congr_right
        _ _ _ hentry))
    hfull

/-- Explicit convergence modulus after the genuine BF4 deterministic block. -/
theorem u1BlockedExponentGramDiagonalChargeCutoff_modulus
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (hg1 : g ≤ (1 : Q'))
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (tailData :
      OneChargeTailModulus
        (fineU1Data G g hg fineChargeCutoff))
    (exponent : Nat)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat) (hM : tailData.cutoff ε ≤ M) :
    u1BlockedExponentGramEntry
          G g hg candidate hcandidate fineChargeCutoff
          { leftExponent := exponent,
            rightExponent := exponent } +
        -u1BlockedExponentGramDiagonalChargeCutoff
          G g hg fineChargeCutoff exponent M ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (u1BlockedExponentGramDiagonalChargeCutoff_tail
      G g hg hg1 candidate hcandidate
      fineChargeCutoff tailData.toOneChargeTail
      exponent M)
    (tailData.scaled_tail ε hε M hM)

/-! ## Axiom gates -/

#print axioms chargeWithinOn_false_witness
#print axioms u1PhysicalTerm_le_oneChargeTail_of_outside
#print axioms u1NormalizedMass_le_oneChargeTail_of_outside
#print axioms u1FullNormalizedReflectionChargeCutoff_tail_upper
#print axioms u1ExponentGramDiagonalChargeCutoff_tail
#print axioms u1ExponentGramDiagonalChargeCutoff_modulus
#print axioms u1BlockedExponentGramDiagonalChargeCutoff_tail
#print axioms u1BlockedExponentGramDiagonalChargeCutoff_modulus

end YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge
