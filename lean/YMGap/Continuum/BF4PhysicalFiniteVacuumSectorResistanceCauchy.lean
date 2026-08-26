/-
# Resistance-weighted Cauchy--Schwarz on positive physical paths

The previous canonical-path estimate first forgot the physical edge weights,
paid an unweighted path-length Cauchy--Schwarz factor, and only afterwards
compared the resulting traffic with the kernel.  That route necessarily sees
the minimum positive edge of the whole finite carrier.

This module proves the sharper constructive inequality

    (sum d_e)^2 <= (sum 1 / k_e) * (sum k_e * d_e^2)

for a finite list of strictly positive rational conductances `k_e`.  Applied
to a positive physical-kernel path, endpoint telescoping gives the exact
resistance form

    (f(first) - f(last))^2
      <= pathResistance * physicalPathEnergy.

No square roots are introduced.  The proof is a finite weighted
Cauchy--Schwarz induction whose cross term is paid by the literal
sum-of-squares inequality `2xy <= x^2 + y^2`; positive rational cancellation
is the only division step.

This is a genuine quantitative improvement of the proof method, but it does
not bound the aggregate resistance traffic uniformly in the cutoff.  No
completed gap, thermodynamic or continuum limit, continuum QFT, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealAlg
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_local (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_local, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem square_nonnegative_local (value : Q') :
    (0 : Q') ≤ value * value :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg value

private theorem square_eqv_congr_local {left right : Q'}
    (heq : left ≈ right) :
    left * left ≈ right * right := by
  exact Q'.eqv_trans _ (right * left) _
    (Q'.mul_eqv_congr_right left right left heq)
    (Q'.mul_eqv_congr_left right left right heq)

/-! ## 1. A finite positive-conductance weighted Cauchy inequality -/

/-- One signed increment together with the strictly positive conductance that
pays its square.  The positivity proof is data because it constructs the
reciprocal resistance. -/
structure PositiveConductanceIncrement : Type where
  conductance : Q'
  conductance_pos : (0 : Q') < conductance
  increment : Q'

/-- Electrical resistance of one positive conductance. -/
def PositiveConductanceIncrement.resistance
    (item : PositiveConductanceIncrement) : Q' :=
  Q'.recipPos item.conductance item.conductance_pos

/-- Conductance-weighted square of one increment. -/
def PositiveConductanceIncrement.energy
    (item : PositiveConductanceIncrement) : Q' :=
  item.conductance * (item.increment * item.increment)

def totalIncrement (items : List PositiveConductanceIncrement) : Q' :=
  listQSum (fun item => item.increment) items

def totalResistance (items : List PositiveConductanceIncrement) : Q' :=
  listQSum (fun item => item.resistance) items

def totalEnergy (items : List PositiveConductanceIncrement) : Q' :=
  listQSum (fun item => item.energy) items

theorem PositiveConductanceIncrement.resistance_pos
    (item : PositiveConductanceIncrement) :
    (0 : Q') < item.resistance :=
  Q'.recipPos_pos item.conductance item.conductance_pos

theorem PositiveConductanceIncrement.energy_nonnegative
    (item : PositiveConductanceIncrement) :
    (0 : Q') ≤ item.energy := by
  unfold PositiveConductanceIncrement.energy
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt item.conductance_pos)
    (square_nonnegative_local item.increment)

theorem totalResistance_nonnegative
    (items : List PositiveConductanceIncrement) :
    (0 : Q') ≤ totalResistance items := by
  unfold totalResistance
  apply listQSum_nonnegative_on
  intro item _
  exact Q'.le_of_lt item.resistance_pos

theorem totalResistance_pos_of_nonempty
    {items : List PositiveConductanceIncrement}
    (hitems : items ≠ []) :
    (0 : Q') < totalResistance items := by
  cases items with
  | nil => exact False.elim (hitems rfl)
  | cons head tail =>
      unfold totalResistance
      exact Q'.pos_add_nonneg head.resistance_pos
        (totalResistance_nonnegative tail)

theorem totalEnergy_nonnegative
    (items : List PositiveConductanceIncrement) :
    (0 : Q') ≤ totalEnergy items := by
  unfold totalEnergy
  apply listQSum_nonnegative_on
  intro item _
  exact item.energy_nonnegative

/-- One resistance times its matching conductance energy is exactly the
unweighted square. -/
theorem resistance_mul_energy_eqv_square
    (item : PositiveConductanceIncrement) :
    item.resistance * item.energy ≈
      item.increment * item.increment := by
  unfold PositiveConductanceIncrement.resistance
    PositiveConductanceIncrement.energy
  refine Q'.eqv_trans _
    ((item.conductance *
      Q'.recipPos item.conductance item.conductance_pos) *
        (item.increment * item.increment)) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (1 * (item.increment * item.increment)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_recipPos_eqv item.conductance item.conductance_pos)
  · exact Q'.one_mul_eqv _

/-- The weighted cross term used by the induction.  It is the rational,
square-root-free form of the two-vector Cauchy--Schwarz inequality. -/
private theorem weighted_cross_le
    {r e d R E D : Q'}
    (hr : (0 : Q') < r) (hR : (0 : Q') < R)
    (hhead : r * e ≈ d * d)
    (hrest : D * D ≤ R * E) :
    (d * D) + (d * D) ≤ r * E + R * e := by
  let x := r * D
  let y := R * d
  have hamgm : (x * y) + (x * y) ≤ x * x + y * y :=
    CRealAlg.amgm_two x y
  have hrr0 : (0 : Q') ≤ r * r := square_nonnegative_local r
  have hxxScaled :
      (r * r) * (D * D) ≤ (r * r) * (R * E) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (r * r) hrest hrr0
  have hxx : x * x ≤ (r * r) * (R * E) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by unfold x; ring_qeqv)) hxxScaled
  have hyy : y * y ≤ (R * R) * (r * e) := by
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ ((R * R) * (d * d)) _
        (by unfold y; ring_qeqv)
        (Q'.mul_eqv_congr_left (R * R) _ _ (Q'.eqv_symm hhead)))
  have hxy :
      x * x + y * y ≤
        (r * r) * (R * E) + (R * R) * (r * e) :=
    Q'.add_le_add hxx hyy
  have hscaled :
      (r * R) * ((d * D) + (d * D)) ≤
        (r * R) * (r * E + R * e) := by
    refine Q'.le_trans' _ ((x * y) + (x * y)) _
      (Q'.le_of_eqv (by unfold x y; ring_qeqv)) ?_
    refine Q'.le_trans' _ (x * x + y * y) _ hamgm ?_
    refine Q'.le_trans' _
      ((r * r) * (R * E) + (R * R) * (r * e)) _ hxy ?_
    exact Q'.le_of_eqv (by ring_qeqv)
  exact Q'.le_of_mul_le_mul_left hscaled (Q'.mul_pos hr hR)

/-- Constructive finite weighted Cauchy--Schwarz, with no square roots:

`(sum increment)^2 <= (sum 1/conductance) *
  (sum conductance * increment^2)`.
-/
theorem finite_positive_conductance_cauchy :
    ∀ items : List PositiveConductanceIncrement,
      totalIncrement items * totalIncrement items ≤
        totalResistance items * totalEnergy items
  | [] => Q'.le_refl' 0
  | [item] => by
      have hincrement : totalIncrement [item] ≈ item.increment := by
        unfold totalIncrement listQSum
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      have hresistance : totalResistance [item] ≈ item.resistance := by
        unfold totalResistance listQSum
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      have henergy : totalEnergy [item] ≈ item.energy := by
        unfold totalEnergy listQSum
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ (item.increment * item.increment) _
          (square_eqv_congr_local hincrement)
          (Q'.eqv_trans _ (item.resistance * item.energy) _
            (Q'.eqv_symm (resistance_mul_energy_eqv_square item))
            (Q'.eqv_trans _ (totalResistance [item] * item.energy) _
              (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hresistance))
              (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm henergy)))))
  | item :: next :: tail => by
      let rest := next :: tail
      let d := item.increment
      let r := item.resistance
      let e := item.energy
      let D := totalIncrement rest
      let R := totalResistance rest
      let E := totalEnergy rest
      have hrest : D * D ≤ R * E :=
        finite_positive_conductance_cauchy rest
      have hR : (0 : Q') < R :=
        totalResistance_pos_of_nonempty (items := rest) (by simp [rest])
      have hhead : r * e ≈ d * d := by
        exact resistance_mul_energy_eqv_square item
      have hcross :
          (d * D) + (d * D) ≤ r * E + R * e :=
        weighted_cross_le item.resistance_pos hR hhead hrest
      have hparts :
          d * d + ((d * D + d * D) + D * D) ≤
            r * e + ((r * E + R * e) + R * E) := by
        exact Q'.add_le_add
          (Q'.le_of_eqv (Q'.eqv_symm hhead))
          (Q'.add_le_add hcross hrest)
      change (d + D) * (d + D) ≤ (r + R) * (e + E)
      refine Q'.le_trans' _
        (d * d + ((d * D + d * D) + D * D)) _
        (Q'.le_of_eqv (by ring_qeqv)) ?_
      refine Q'.le_trans' _
        (r * e + ((r * E + R * e) + R * E)) _ hparts ?_
      exact Q'.le_of_eqv (by ring_qeqv)

/-! ## 2. Exact resistance Cauchy on a positive-kernel chain -/

namespace PositiveKernelChainIn

/-- The conductance/increment list read directly from a positive-kernel
chain. -/
def conductanceIncrements
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      PositiveKernelChainIn kernel support first last →
        List PositiveConductanceIncrement
  | _, _, PositiveKernelChainIn.refl _ => []
  | first, _, PositiveKernelChainIn.step (next := next) positive _ rest =>
      { conductance := kernel first next
        conductance_pos := positive
        increment := coefficient first + -coefficient next } ::
        conductanceIncrements coefficient rest

/-- Sum of reciprocal physical conductances along the displayed path. -/
def resistance
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      PositiveKernelChainIn kernel support first last → Q'
  | _, _, PositiveKernelChainIn.refl _ => 0
  | first, _, PositiveKernelChainIn.step (next := next) positive _ rest =>
      Q'.recipPos (kernel first next) positive + resistance rest

theorem resistance_nonnegative
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      (0 : Q') ≤ resistance path
  | _, _, PositiveKernelChainIn.refl _ => Q'.le_refl' 0
  | _, _, PositiveKernelChainIn.step positive _ rest =>
      Q'.zero_le_add _ _
        (Q'.le_of_lt (Q'.recipPos_pos _ positive))
        (resistance_nonnegative rest)

theorem conductanceIncrements_totalIncrement_eqv_edgeDifferencesSum
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      totalIncrement (conductanceIncrements coefficient path) ≈
        listQSum (fun value => value)
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeDifferences
            coefficient path)
  | _, _, PositiveKernelChainIn.refl _ => Q'.eqv_refl 0
  | _, _, PositiveKernelChainIn.step _ _ rest =>
      Q'.add_eqv_congr' (Q'.eqv_refl _)
        (conductanceIncrements_totalIncrement_eqv_edgeDifferencesSum
          coefficient rest)

theorem conductanceIncrements_totalIncrement_eqv_endpoint
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    {first last : State}
    (path : PositiveKernelChainIn kernel support first last) :
    totalIncrement (conductanceIncrements coefficient path) ≈
      coefficient first + -coefficient last := by
  exact Q'.eqv_trans _ _ _
    (conductanceIncrements_totalIncrement_eqv_edgeDifferencesSum
      coefficient path)
    (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeDifferences_sum_eqv_endpoint
      coefficient path)

theorem conductanceIncrements_totalResistance_eqv
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      totalResistance (conductanceIncrements coefficient path) ≈
        resistance path
  | _, _, PositiveKernelChainIn.refl _ => Q'.eqv_refl 0
  | _, _, PositiveKernelChainIn.step _ _ rest =>
      Q'.add_eqv_congr' (Q'.eqv_refl _)
        (conductanceIncrements_totalResistance_eqv coefficient rest)

theorem conductanceIncrements_totalEnergy_eqv_linearEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      totalEnergy (conductanceIncrements coefficient path) ≈
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
          coefficient path
  | _, _, PositiveKernelChainIn.refl _ => Q'.eqv_refl 0
  | _, _, PositiveKernelChainIn.step _ _ rest =>
      Q'.add_eqv_congr' (Q'.eqv_refl _)
        (conductanceIncrements_totalEnergy_eqv_linearEnergy coefficient rest)

/-- Endpoint telescoping plus resistance-weighted finite Cauchy--Schwarz.
Unlike the old length/minimum-edge estimate, every physical conductance is
absorbed locally through its exact reciprocal. -/
theorem endpointDifference_sq_le_resistance_mul_linearEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      (coefficient first + -coefficient last) *
          (coefficient first + -coefficient last) ≤
        resistance path *
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
            coefficient path := by
  intro first last path
  let items := conductanceIncrements coefficient path
  have hcauchy := finite_positive_conductance_cauchy items
  have hsum := conductanceIncrements_totalIncrement_eqv_endpoint
    coefficient path
  have hresistance := conductanceIncrements_totalResistance_eqv
    coefficient path
  have henergy := conductanceIncrements_totalEnergy_eqv_linearEnergy
    coefficient path
  refine Q'.le_trans' _
    (totalIncrement items * totalIncrement items) _
    (Q'.le_of_eqv (Q'.eqv_symm
      (square_eqv_congr_local hsum))) ?_
  refine Q'.le_trans' _
    (totalResistance items * totalEnergy items) _ hcauchy ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      (resistance path * totalEnergy items) _
      (Q'.mul_eqv_congr_right _ _ _ hresistance)
      (Q'.mul_eqv_congr_left _ _ _ henergy))

end PositiveKernelChainIn

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy.finite_positive_conductance_cauchy
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.endpointDifference_sq_le_resistance_mul_linearEnergy
