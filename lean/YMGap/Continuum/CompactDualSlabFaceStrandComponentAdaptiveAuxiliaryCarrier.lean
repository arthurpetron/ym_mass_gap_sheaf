/-
# Link-adaptive finite carriers for component auxiliary rows

For a link with selected physical mass `t` and `w` used auxiliary
coordinates, the sharp pointwise bound places its auxiliary word in
`allSeqs (t + 1) w`.  This module constructs the Cartesian carrier over a
list of `(t,w)` specifications and proves the size estimate needed by the
component inverse-counting route.

If every width is at most three, then

  (t + 1)^w <= 8^t.

Consequently a family whose total link mass is at most `4*n` has carrier size
at most `4096^n`.  This is the abstract finite combinatorics layer; attaching
the production component rows to the carrier is a separate theorem.

Constructive contract: finite-list recursion and natural arithmetic only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryPointwiseBound
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection

/-- Cartesian enumeration of one bounded word for every `(mass,width)`
specification. -/
def adaptiveAuxiliaryCarrier :
    List (Nat × Nat) -> List (List (List Nat))
  | [] => [[]]
  | specification :: specifications =>
      (allSeqs (specification.1 + 1) specification.2).flatMap fun row =>
        (adaptiveAuxiliaryCarrier specifications).map fun rows => row :: rows

/-- The corresponding product cardinality, written recursively to avoid an
opaque library product. -/
def adaptiveAuxiliaryCarrierSize : List (Nat × Nat) -> Nat
  | [] => 1
  | specification :: specifications =>
      (specification.1 + 1) ^ specification.2 *
        adaptiveAuxiliaryCarrierSize specifications

/-- Total mass carried by the link specifications. -/
def adaptiveAuxiliaryMass : List (Nat × Nat) -> Nat
  | [] => 0
  | specification :: specifications =>
      specification.1 + adaptiveAuxiliaryMass specifications

/-- Pointwise row-fit relation used to state production membership without
erasing the link-dependent bounds. -/
inductive AdaptiveAuxiliaryRowsFit :
    List (Nat × Nat) -> List (List Nat) -> Prop
  | nil : AdaptiveAuxiliaryRowsFit [] []
  | cons
      {mass width : Nat} {specifications : List (Nat × Nat)}
      {row : List Nat} {rows : List (List Nat)}
      (length_eq : row.length = width)
      (entry_lt : forall value, value ∈ row -> value < mass + 1)
      (tail : AdaptiveAuxiliaryRowsFit specifications rows) :
      AdaptiveAuxiliaryRowsFit
        ((mass, width) :: specifications) (row :: rows)

/-- The recursive Cartesian carrier has exactly the recursive product size. -/
theorem adaptiveAuxiliaryCarrier_length : forall specifications,
    (adaptiveAuxiliaryCarrier specifications).length =
      adaptiveAuxiliaryCarrierSize specifications
  | [] => rfl
  | specification :: specifications => by
      unfold adaptiveAuxiliaryCarrier adaptiveAuxiliaryCarrierSize
      rw [length_flatMap_const
        (fun row => (adaptiveAuxiliaryCarrier specifications).map
          fun rows => row :: rows)
        (adaptiveAuxiliaryCarrier specifications).length
        (allSeqs (specification.1 + 1) specification.2)
        (fun _ _ => List.length_map _),
        length_allSeqs,
        adaptiveAuxiliaryCarrier_length specifications]

/-- Every row family satisfying its literal length and entry bounds belongs
to the adaptive Cartesian carrier. -/
theorem AdaptiveAuxiliaryRowsFit.mem_carrier :
    forall {specifications rows},
      AdaptiveAuxiliaryRowsFit specifications rows ->
        rows ∈ adaptiveAuxiliaryCarrier specifications
  | [], [], .nil => List.mem_cons_self
  | (_mass, _width) :: _specifications, _row :: _rows,
      .cons hlength hentries htail => by
        unfold adaptiveAuxiliaryCarrier
        apply List.mem_flatMap.mpr
        refine ⟨_row,
          mem_allSeqs (_mass + 1) _width _row hlength hentries, ?_⟩
        apply List.mem_map.mpr
        exact ⟨_rows, AdaptiveAuxiliaryRowsFit.mem_carrier htail, rfl⟩

/-- Pointwise length and radix bounds over a common source list assemble into
the typed row-fit relation. -/
theorem adaptiveAuxiliaryRowsFit_map
    {A : Type} (mass width : A -> Nat) (row : A -> List Nat) :
    forall items : List A,
      (forall item, item ∈ items -> (row item).length = width item) ->
      (forall item, item ∈ items -> forall value, value ∈ row item ->
        value < mass item + 1) ->
      AdaptiveAuxiliaryRowsFit
        (items.map fun item => (mass item, width item))
        (items.map row)
  | [], _, _ => .nil
  | item :: items, hlength, hentry =>
      .cons
        (hlength item List.mem_cons_self)
        (hentry item List.mem_cons_self)
        (adaptiveAuxiliaryRowsFit_map mass width row items
          (fun next hnext =>
            hlength next (List.mem_cons_of_mem item hnext))
          (fun next hnext =>
            hentry next (List.mem_cons_of_mem item hnext)))

/-- Elementary exponential envelope for a successor. -/
theorem nat_succ_le_two_pow : forall mass : Nat,
    mass + 1 <= 2 ^ mass
  | 0 => by decide
  | mass + 1 => by
      have ih := nat_succ_le_two_pow mass
      rw [Nat.pow_succ]
      calc
        mass + 1 + 1 <= 2 * (mass + 1) := by omega
        _ <= 2 * 2 ^ mass := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ mass * 2 := Nat.mul_comm _ _

/-- A width-at-most-three row contributes at most `8^mass` words. -/
theorem localAdaptiveAuxiliaryFactor_le_eight_pow
    (mass width : Nat) (hwidth : width <= 3) :
    (mass + 1) ^ width <= 8 ^ mass := by
  calc
    (mass + 1) ^ width <= (mass + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) hwidth
    _ <= (2 ^ mass) ^ 3 :=
      Nat.pow_le_pow_left (nat_succ_le_two_pow mass) 3
    _ = 8 ^ mass := by
      change (2 ^ mass) ^ 3 = (2 ^ 3) ^ mass
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]

/-- Multiplying the local adaptive carriers costs at most one factor `8` per
unit of total physical link mass. -/
theorem adaptiveAuxiliaryCarrierSize_le_eight_pow_mass :
    forall specifications : List (Nat × Nat),
      (forall specification, specification ∈ specifications ->
        specification.2 <= 3) ->
      adaptiveAuxiliaryCarrierSize specifications <=
        8 ^ adaptiveAuxiliaryMass specifications
  | [], _ => by decide
  | specification :: specifications, hwidth => by
      have hlocal := localAdaptiveAuxiliaryFactor_le_eight_pow
        specification.1 specification.2
        (hwidth specification List.mem_cons_self)
      have htail := adaptiveAuxiliaryCarrierSize_le_eight_pow_mass
        specifications
        (fun item hitem =>
          hwidth item (List.mem_cons_of_mem specification hitem))
      unfold adaptiveAuxiliaryCarrierSize adaptiveAuxiliaryMass
      calc
        (specification.1 + 1) ^ specification.2 *
              adaptiveAuxiliaryCarrierSize specifications <=
            8 ^ specification.1 *
              8 ^ adaptiveAuxiliaryMass specifications :=
          Nat.mul_le_mul hlocal htail
        _ = 8 ^
            (specification.1 + adaptiveAuxiliaryMass specifications) := by
          rw [Nat.pow_add]

/-- Global form of the carrier bound at component peel size `n`. -/
theorem adaptiveAuxiliaryCarrier_length_le_4096_pow
    (specifications : List (Nat × Nat)) (peelSize : Nat)
    (hwidth : forall specification, specification ∈ specifications ->
      specification.2 <= 3)
    (hmass : adaptiveAuxiliaryMass specifications <= 4 * peelSize) :
    (adaptiveAuxiliaryCarrier specifications).length <=
      4096 ^ peelSize := by
  rw [adaptiveAuxiliaryCarrier_length]
  calc
    adaptiveAuxiliaryCarrierSize specifications <=
        8 ^ adaptiveAuxiliaryMass specifications :=
      adaptiveAuxiliaryCarrierSize_le_eight_pow_mass specifications hwidth
    _ <= 8 ^ (4 * peelSize) :=
      Nat.pow_le_pow_right (by decide) hmass
    _ = 4096 ^ peelSize := by
      rw [Nat.pow_mul]

#print axioms adaptiveAuxiliaryCarrier
#print axioms adaptiveAuxiliaryCarrierSize
#print axioms adaptiveAuxiliaryMass
#print axioms AdaptiveAuxiliaryRowsFit
#print axioms adaptiveAuxiliaryCarrier_length
#print axioms AdaptiveAuxiliaryRowsFit.mem_carrier
#print axioms adaptiveAuxiliaryRowsFit_map
#print axioms nat_succ_le_two_pow
#print axioms localAdaptiveAuxiliaryFactor_le_eight_pow
#print axioms adaptiveAuxiliaryCarrierSize_le_eight_pow_mass
#print axioms adaptiveAuxiliaryCarrier_length_le_4096_pow

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
