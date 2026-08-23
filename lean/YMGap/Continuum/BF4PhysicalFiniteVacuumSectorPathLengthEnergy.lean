/-
# Polynomial canonical-path energy for the finite BF4 vacuum sector

The first canonical-path compiler recursively doubled the entire remaining
energy at every edge.  Its amplification scale is therefore exponential in
the chosen path length.  This module replaces that bookkeeping by finite
Cauchy--Schwarz on the literal list of edge differences.

For a positive-kernel chain of length `n`, a common edge floor controls its
endpoint square by `n` times its weighted path energy.  Bounding each displayed
edge term by the full directed Dirichlet energy then costs one further factor
of `n`.  The resulting global scale is `n^2`, not the earlier exponential
recursion.

This is a quantitative improvement of the finite proof method.  It does not
assert that path lengths or physical edge weights are uniform on expanding
carriers, and it does not assert a completed, thermodynamic, continuum, or
Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
import YMGap.Continuum.ThetaExponentConvexity

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem square_nonnegative (value : Q') :
    (0 : Q') ≤ value * value :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg value

private theorem square_eqv_congr {left right : Q'}
    (heq : left ≈ right) :
    left * left ≈ right * right := by
  exact Q'.eqv_trans _ (right * left) _
    (Q'.mul_eqv_congr_right left right left heq)
    (Q'.mul_eqv_congr_left right left right heq)

/-! ## 1. Finite-list Cauchy--Schwarz with the exact length factor -/

/-- Total fallback indexing of a rational list. -/
def qListAt (values : List Q') (index : Nat) : Q' :=
  (values[index]?).getD 0

@[simp] theorem qListAt_cons_zero (value : Q') (values : List Q') :
    qListAt (value :: values) 0 = value := by
  rfl

@[simp] theorem qListAt_cons_succ
    (value : Q') (values : List Q') (index : Nat) :
    qListAt (value :: values) (index + 1) = qListAt values index := by
  unfold qListAt
  simp

private theorem fsum_head_tail_local (function : Nat → Q') : ∀ length,
    fsum function (length + 1) ≈
      function 0 + fsum (fun index => function (index + 1)) length
  | 0 => by
      change (0 + function 0) ≈ function 0 + 0
      exact Q'.eqv_trans _ (function 0) _
        (Q'.eqv_of_eq (Q'.zero_add' _))
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))
  | length + 1 => by
      rw [fsum_succ, fsum_succ]
      exact Q'.eqv_trans _
        ((function 0 + fsum (fun index => function (index + 1)) length) +
          function (length + 1)) _
        (Q'.add_eqv_congr'
          (fsum_head_tail_local function length) (Q'.eqv_refl _))
        (Q'.add_assoc_eqv _ _ _)

theorem fsum_qListAt_eq_listQSum : ∀ values : List Q',
    fsum (qListAt values) values.length ≈
      listQSum (fun value => value) values
  | [] => Q'.eqv_refl 0
  | value :: values => by
      change fsum (qListAt (value :: values)) (values.length + 1) ≈
        value + listQSum (fun item => item) values
      refine Q'.eqv_trans _
        (qListAt (value :: values) 0 +
          fsum (fun index => qListAt (value :: values) (index + 1))
            values.length) _
        (fsum_head_tail_local (qListAt (value :: values)) values.length) ?_
      rw [qListAt_cons_zero]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _
          (fsum (qListAt values) values.length) _
          (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _
            (fun index => by
              rw [qListAt_cons_succ]
              exact Q'.eqv_refl _) values.length)
          (fsum_qListAt_eq_listQSum values))

theorem fsum_qListAt_square_eq_listQSum : ∀ values : List Q',
    fsum (fun index => qListAt values index * qListAt values index)
        values.length ≈
      listQSum (fun value => value * value) values
  | [] => Q'.eqv_refl 0
  | value :: values => by
      change fsum
          (fun index =>
            qListAt (value :: values) index * qListAt (value :: values) index)
          (values.length + 1) ≈
        value * value + listQSum (fun item => item * item) values
      refine Q'.eqv_trans _
        (qListAt (value :: values) 0 * qListAt (value :: values) 0 +
          fsum (fun index =>
            qListAt (value :: values) (index + 1) *
              qListAt (value :: values) (index + 1)) values.length) _
        (fsum_head_tail_local _ values.length) ?_
      rw [qListAt_cons_zero]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _
          (fsum (fun index => qListAt values index * qListAt values index)
            values.length) _
          (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _
            (fun index => by
              rw [qListAt_cons_succ]
              exact Q'.eqv_refl _) values.length)
          (fsum_qListAt_square_eq_listQSum values))

theorem fsum_one_eqv_ofNat : ∀ length : Nat,
    fsum (fun _ => (1 : Q')) length ≈ Q'.ofNat length
  | 0 => Q'.eqv_refl 0
  | length + 1 => by
      change fsum (fun _ => (1 : Q')) length + 1 ≈
        Q'.ofNat (length + 1)
      exact Q'.eqv_trans _ (Q'.ofNat length + 1) _
        (Q'.add_eqv_congr' (fsum_one_eqv_ofNat length) (Q'.eqv_refl 1))
        (Q'.eqv_trans _ (Q'.ofNat length + Q'.ofNat 1) _
          (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (by decide)))
          (Q'.eqv_symm (Q'.ofNat_add_eqv length 1)))

/-- Exact finite-list Cauchy--Schwarz with the list length as the constant. -/
theorem listQSum_square_le_length_mul_squareSum (values : List Q') :
    listQSum (fun value => value) values *
          listQSum (fun value => value) values ≤
      Q'.ofNat values.length *
        listQSum (fun value => value * value) values := by
  have hcs := YMGap.Continuum.ThetaExponentConvexity.cauchy_schwarz
    (qListAt values) (fun _ => 1) values.length
  have hsum := fsum_qListAt_eq_listQSum values
  have hsquares := fsum_qListAt_square_eq_listQSum values
  have hones := fsum_one_eqv_ofNat values.length
  have hcross :
      fsum (fun index => qListAt values index * 1) values.length ≈
        listQSum (fun value => value) values :=
    Q'.eqv_trans _ (fsum (qListAt values) values.length) _
      (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _
        (fun index => Q'.mul_one_eqv _) values.length)
      hsum
  have honeSquares :
      fsum (fun _ => (1 : Q') * 1) values.length ≈
        Q'.ofNat values.length :=
    Q'.eqv_trans _ (fsum (fun _ => (1 : Q')) values.length) _
      (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _
        (fun _ => Q'.one_mul_eqv 1) values.length)
      hones
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm (square_eqv_congr hcross))) ?_
  refine Q'.le_trans' _ _ _ hcs ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      (listQSum (fun value => value * value) values *
        Q'.ofNat values.length) _
      (Q'.eqv_trans _
        (listQSum (fun value => value * value) values *
          fsum (fun _ => (1 : Q') * 1) values.length) _
        (Q'.mul_eqv_congr_right _ _ _ hsquares)
        (Q'.mul_eqv_congr_left _ _ _ honeSquares))
      (Q'.eqv_trans _
        (Q'.ofNat values.length *
          listQSum (fun value => value * value) values) _
        (Q'.mul_comm_eqv _ _)
        (Q'.eqv_refl _)))

/-! ## 2. Literal edge differences and linear weighted path energy -/

namespace PositiveKernelChainIn

/-- The ordered list of coefficient increments along a positive chain. -/
def edgeDifferences
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      PositiveKernelChainIn kernel support first last → List Q'
  | _, _, PositiveKernelChainIn.refl _ => []
  | first, _, PositiveKernelChainIn.step (next := next) _ _ rest =>
      (coefficient first + -coefficient next) ::
        edgeDifferences coefficient rest

/-- Number of steps in the displayed positive chain. -/
def edgeLength
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      PositiveKernelChainIn kernel support first last → Nat
  | _, _, PositiveKernelChainIn.refl _ => 0
  | _, _, PositiveKernelChainIn.step _ _ rest => edgeLength rest + 1

/-- The polynomial global-energy scale attached to a displayed chain. -/
def quadraticLengthScale
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State}
    (path : PositiveKernelChainIn kernel support first last) : Q' :=
  Q'.ofNat (edgeLength path * edgeLength path)

/-- The actual kernel-weighted edge-square sum, with no recursive doubling. -/
def linearEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      PositiveKernelChainIn kernel support first last → Q'
  | _, _, PositiveKernelChainIn.refl _ => 0
  | first, _, PositiveKernelChainIn.step (next := next) _ _ rest =>
      kernel first next *
          ((coefficient first + -coefficient next) *
            (coefficient first + -coefficient next)) +
        linearEnergy coefficient rest

theorem edgeDifferences_length
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      (edgeDifferences coefficient path).length = edgeLength path
  | _, _, PositiveKernelChainIn.refl _ => rfl
  | first, last,
      PositiveKernelChainIn.step (next := next) positive hnext rest => by
      simp only [edgeDifferences, List.length_cons, edgeLength]
      exact congrArg (fun n => n + 1) (edgeDifferences_length coefficient rest)

private theorem endpointDifference_step_local
    {State : Type} (coefficient : State → Q')
    (first next last : State) :
    coefficient first + -coefficient last ≈
      (coefficient first + -coefficient next) +
        (coefficient next + -coefficient last) := by
  have hinner :
      (-coefficient next) +
          (coefficient next + -coefficient last) ≈
        -coefficient last := by
    refine Q'.eqv_trans _
      ((-coefficient next + coefficient next) + -coefficient last) _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv
          (-coefficient next) (coefficient next) (-coefficient last))) ?_
    exact Q'.eqv_trans _ (0 + -coefficient last) _
      (Q'.add_eqv_congr'
        (Q'.neg_add_self_eqv (coefficient next)) (Q'.eqv_refl _))
      (Q'.eqv_of_eq (Q'.zero_add' _))
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (coefficient first +
        ((-coefficient next) +
          (coefficient next + -coefficient last))) _
      (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hinner))

theorem edgeDifferences_sum_eqv_endpoint
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      listQSum (fun value => value) (edgeDifferences coefficient path) ≈
        coefficient first + -coefficient last
  | first, _, PositiveKernelChainIn.refl _ => by
      exact Q'.eqv_trans _ (0 : Q') _ (Q'.eqv_refl 0)
        (Q'.eqv_symm (Q'.add_neg_self_eqv (coefficient first)))
  | first, last,
      PositiveKernelChainIn.step (next := next) _ _ rest => by
      exact Q'.eqv_trans _
        ((coefficient first + -coefficient next) +
          (coefficient next + -coefficient last)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (edgeDifferences_sum_eqv_endpoint coefficient rest))
        (Q'.eqv_symm (endpointDifference_step_local
          coefficient first next last))

/-- Endpoint telescoping and finite Cauchy--Schwarz before any comparison
with the physical kernel.  This floor-free form is the right input for
weighted-flow arguments: the stationary endpoint weight and path length can
be charged directly to each literal edge occurrence, and only afterwards
compared pointwise with physical edge capacity. -/
theorem endpointDifference_sq_le_length_mul_edgeSquareSum
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      (coefficient first + -coefficient last) *
          (coefficient first + -coefficient last) ≤
        Q'.ofNat (edgeLength path) *
          listQSum (fun value => value * value)
            (edgeDifferences coefficient path) := by
  intro first last path
  have hsum := edgeDifferences_sum_eqv_endpoint coefficient path
  have hlength := edgeDifferences_length coefficient path
  have hcs := listQSum_square_le_length_mul_squareSum
    (edgeDifferences coefficient path)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (square_eqv_congr hsum))) ?_
  simpa only [hlength] using hcs

private theorem ofNat_nonnegative (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

/-- A common floor below every used positive edge converts the unweighted
edge-square sum into the literal kernel-weighted path energy. -/
theorem floor_mul_edgeSquareSum_le_linearEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgeFloor : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      floor ≤ kernel first next) :
    {first last : State} → first ∈ support →
      (path : PositiveKernelChainIn kernel support first last) →
      floor *
          listQSum (fun value => value * value)
            (edgeDifferences coefficient path) ≤
        linearEnergy coefficient path
  | _, _, _, PositiveKernelChainIn.refl _ => by
      exact Q'.le_of_eqv (Q'.mul_zero_eqv floor)
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) positive hnext rest => by
      let difference := coefficient first + -coefficient next
      have hedge : floor * (difference * difference) ≤
          kernel first next * (difference * difference) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (edgeFloor first next hfirst hnext positive)
          (square_nonnegative difference)
      have hrest := floor_mul_edgeSquareSum_le_linearEnergy
        coefficient floor hfloor0 edgeFloor hnext rest
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_add_eqv floor (difference * difference)
            (listQSum (fun value => value * value)
              (edgeDifferences coefficient rest))))
        (Q'.add_le_add hedge hrest)

/-- Endpoint telescoping plus finite Cauchy--Schwarz costs exactly one factor
of the path length before the literal weighted path energy. -/
theorem floor_mul_endpointDifference_sq_le_length_mul_linearEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgeFloor : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      floor ≤ kernel first next) :
    {first last : State} → first ∈ support →
      (path : PositiveKernelChainIn kernel support first last) →
      floor *
          ((coefficient first + -coefficient last) *
            (coefficient first + -coefficient last)) ≤
        Q'.ofNat (edgeLength path) * linearEnergy coefficient path := by
  intro first last hfirst path
  let differences := edgeDifferences coefficient path
  let squareSum := listQSum (fun value => value * value) differences
  let lengthQ := Q'.ofNat (edgeLength path)
  have hsum := edgeDifferences_sum_eqv_endpoint coefficient path
  have hlength := edgeDifferences_length coefficient path
  have hcs0 := listQSum_square_le_length_mul_squareSum differences
  have hcs :
      listQSum (fun value => value) differences *
            listQSum (fun value => value) differences ≤
        lengthQ * squareSum := by
    simpa only [differences, squareSum, lengthQ, hlength] using hcs0
  have hfloorSquares := floor_mul_edgeSquareSum_le_linearEnergy
    coefficient floor hfloor0 edgeFloor hfirst path
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ floor hcs hfloor0
  have hreorder : floor * (lengthQ * squareSum) ≈
      lengthQ * (floor * squareSum) := by
    exact Q'.eqv_trans _ ((floor * lengthQ) * squareSum) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv floor lengthQ squareSum))
      (Q'.eqv_trans _ ((lengthQ * floor) * squareSum) _
        (Q'.mul_eqv_congr_right _ _ squareSum
          (Q'.mul_comm_eqv floor lengthQ))
        (Q'.mul_assoc_eqv lengthQ floor squareSum))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left floor _ _
        (Q'.eqv_symm (square_eqv_congr hsum))))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.mul_le_mul_of_nonneg_left _ _ lengthQ hfloorSquares
          (ofNat_nonnegative (edgeLength path)))))

private theorem ofNat_succ_eqv_add_one (n : Nat) :
    Q'.ofNat (n + 1) ≈ Q'.ofNat n + 1 :=
  Q'.eqv_trans _ (Q'.ofNat n + Q'.ofNat 1) _
    (Q'.ofNat_add_eqv n 1)
    (Q'.add_eqv_congr_left _ _ _ (by decide))

/-- The quadratic length scale is pointwise no larger than the earlier
recursively doubled amplification scale. -/
theorem quadraticLengthScale_le_amplificationScale
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      quadraticLengthScale path ≤
        BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path
  | _, _, PositiveKernelChainIn.refl _ => Q'.le_refl' 0
  | first, last,
      PositiveKernelChainIn.step (next := next) positive hnext rest => by
      let n := edgeLength rest
      let nQ := Q'.ofNat n
      let oldScale :=
        BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          rest
      have ih := quadraticLengthScale_le_amplificationScale rest
      have hlengthSquare :
          quadraticLengthScale
              (PositiveKernelChainIn.step positive hnext rest) ≈
            (nQ + 1) * (nQ + 1) := by
        dsimp [quadraticLengthScale, edgeLength, n, nQ]
        exact Q'.eqv_trans _
          (Q'.ofNat (edgeLength rest + 1) *
            Q'.ofNat (edgeLength rest + 1)) _
          (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
            (edgeLength rest + 1) (edgeLength rest + 1))
          (square_eqv_congr
            (ofNat_succ_eqv_add_one (edgeLength rest)))
      have hyoung :=
        BF4PhysicalFiniteVacuumSectorPathEnergy.square_add_le_double_square_sum
          nQ 1
      have hnSquare : nQ * nQ ≈ quadraticLengthScale rest := by
        dsimp [quadraticLengthScale, n, nQ]
        exact Q'.eqv_symm
          (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
            (edgeLength rest) (edgeLength rest))
      have hmiddle :
          (nQ * nQ + 1 * 1) + (nQ * nQ + 1 * 1) ≈
            (1 + quadraticLengthScale rest) +
              (1 + quadraticLengthScale rest) := by
        have hpiece : nQ * nQ + 1 * 1 ≈
            1 + quadraticLengthScale rest :=
          Q'.eqv_trans _ (quadraticLengthScale rest + 1) _
            (Q'.add_eqv_congr' hnSquare (Q'.one_mul_eqv 1))
            (Q'.add_comm_eqv _ _)
        exact Q'.add_eqv_congr' hpiece hpiece
      have hmono :
          (1 + quadraticLengthScale rest) +
              (1 + quadraticLengthScale rest) ≤
            (1 + oldScale) + (1 + oldScale) :=
        Q'.add_le_add
          (Q'.add_le_add_left 1 _ _ ih)
          (Q'.add_le_add_left 1 _ _ ih)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hlengthSquare)
        (Q'.le_trans' _ _ _ hyoung
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle) hmono))

/-- The literal weighted path energy is at most the path length times the full
directed Dirichlet energy.  This remains valid even if the displayed chain
repeats an edge. -/
theorem linearEnergy_le_length_mul_finiteJointDirichletEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (hkernel : ∀ left right, (0 : Q') ≤ kernel left right) :
    {first last : State} → first ∈ support →
      (path : PositiveKernelChainIn kernel support first last) →
      linearEnergy coefficient path ≤
        Q'.ofNat (edgeLength path) *
          finiteJointDirichletEnergy support coefficient kernel
  | _, _, _, PositiveKernelChainIn.refl _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.zero_mul_eqv
            (finiteJointDirichletEnergy support coefficient kernel)))
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) _positive hnext rest => by
      let globalEnergy :=
        finiteJointDirichletEnergy support coefficient kernel
      let edgeEnergy := kernel first next *
        ((coefficient first + -coefficient next) *
          (coefficient first + -coefficient next))
      let restLength := edgeLength rest
      have hedge : edgeEnergy ≤ globalEnergy :=
        finiteJointDirichletEnergy_term_le
          support coefficient kernel hkernel first next hfirst hnext
      have hrest : linearEnergy coefficient rest ≤
          Q'.ofNat restLength * globalEnergy :=
        linearEnergy_le_length_mul_finiteJointDirichletEnergy
          coefficient hkernel hnext rest
      have hadd : edgeEnergy + linearEnergy coefficient rest ≤
          globalEnergy + Q'.ofNat restLength * globalEnergy :=
        Q'.add_le_add hedge hrest
      have hscale :
          Q'.ofNat (restLength + 1) * globalEnergy ≈
            globalEnergy + Q'.ofNat restLength * globalEnergy := by
        refine Q'.eqv_trans _
          ((Q'.ofNat restLength + 1) * globalEnergy) _
          (Q'.mul_eqv_congr_right _ _ globalEnergy
            (ofNat_succ_eqv_add_one restLength)) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat restLength * globalEnergy + 1 * globalEnergy) _
          (Q'.add_mul_eqv _ _ _) ?_
        exact Q'.eqv_trans _
          (Q'.ofNat restLength * globalEnergy + globalEnergy) _
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.one_mul_eqv globalEnergy))
          (Q'.add_comm_eqv _ _)
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (Q'.eqv_symm hscale))

/-- Combining telescoping and global domination gives a quadratic, rather
than exponential, path-length scale. -/
theorem floor_mul_endpointDifference_sq_le_length_sq_mul_finiteJointDirichletEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (hkernel : ∀ left right, (0 : Q') ≤ kernel left right)
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgeFloor : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      floor ≤ kernel first next) :
    {first last : State} → first ∈ support →
      (path : PositiveKernelChainIn kernel support first last) →
      floor *
          ((coefficient first + -coefficient last) *
            (coefficient first + -coefficient last)) ≤
        Q'.ofNat (edgeLength path * edgeLength path) *
          finiteJointDirichletEnergy support coefficient kernel := by
  intro first last hfirst path
  let lengthQ := Q'.ofNat (edgeLength path)
  let globalEnergy :=
    finiteJointDirichletEnergy support coefficient kernel
  have hendpoint :=
    floor_mul_endpointDifference_sq_le_length_mul_linearEnergy
      coefficient floor hfloor0 edgeFloor hfirst path
  have henergy :=
    linearEnergy_le_length_mul_finiteJointDirichletEnergy
      coefficient hkernel hfirst path
  have hlength0 : (0 : Q') ≤ lengthQ :=
    ofNat_nonnegative (edgeLength path)
  have hscaled :
      lengthQ * linearEnergy coefficient path ≤
        lengthQ * (lengthQ * globalEnergy) :=
    Q'.mul_le_mul_of_nonneg_left _ _ lengthQ henergy hlength0
  have hfactor :
      lengthQ * (lengthQ * globalEnergy) ≈
        Q'.ofNat (edgeLength path * edgeLength path) * globalEnergy := by
    refine Q'.eqv_trans _ ((lengthQ * lengthQ) * globalEnergy) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv lengthQ lengthQ globalEnergy)) ?_
    exact Q'.mul_eqv_congr_right _ _ globalEnergy
      (Q'.eqv_symm
        (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
          (edgeLength path) (edgeLength path)))
  exact Q'.le_trans' _ _ _ hendpoint
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfactor))

/-! ## 2b. The same polynomial estimate after rekernel transport -/

theorem edgeLength_rekernel
    {State : Type} {kernel replacement : State → State → Q'}
    {support : List State}
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      (0 : Q') < replacement first next) :
    {first last : State} → (hfirst : first ∈ support) →
      (path : PositiveKernelChainIn kernel support first last) →
      edgeLength
          (BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.rekernel
            edgePositive hfirst path) =
        edgeLength path
  | _, _, _, PositiveKernelChainIn.refl _ => rfl
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) positive hnext rest => by
      simp only [BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.rekernel,
        edgeLength]
      exact congrArg (fun n => n + 1)
        (edgeLength_rekernel edgePositive hnext rest)

/-- A floor required only on the positive edges of the base chain controls
the edge-square sum after that same chain is rekernelled. -/
theorem floor_mul_edgeSquareSum_le_rekernel_linearEnergy
    {State : Type} {kernel replacement : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      (0 : Q') < replacement first next)
    (edgeFloor : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      floor ≤ replacement first next) :
    {first last : State} → (hfirst : first ∈ support) →
      (path : PositiveKernelChainIn kernel support first last) →
      floor *
          listQSum (fun value => value * value)
            (edgeDifferences coefficient path) ≤
        linearEnergy coefficient
          (BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.rekernel
            edgePositive hfirst path)
  | _, _, _, PositiveKernelChainIn.refl _ => by
      exact Q'.le_of_eqv (Q'.mul_zero_eqv floor)
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) positive hnext rest => by
      let difference := coefficient first + -coefficient next
      have hedge : floor * (difference * difference) ≤
          replacement first next * (difference * difference) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (edgeFloor first next hfirst hnext positive)
          (square_nonnegative difference)
      have hrest := floor_mul_edgeSquareSum_le_rekernel_linearEnergy
        coefficient floor hfloor0 edgePositive edgeFloor hnext rest
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_add_eqv floor (difference * difference)
            (listQSum (fun value => value * value)
              (edgeDifferences coefficient rest))))
        (Q'.add_le_add hedge hrest)

theorem floor_mul_endpointDifference_sq_le_length_mul_rekernel_linearEnergy
    {State : Type} {kernel replacement : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      (0 : Q') < replacement first next)
    (edgeFloor : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      floor ≤ replacement first next) :
    {first last : State} → (hfirst : first ∈ support) →
      (path : PositiveKernelChainIn kernel support first last) →
      floor *
          ((coefficient first + -coefficient last) *
            (coefficient first + -coefficient last)) ≤
        Q'.ofNat (edgeLength path) *
          linearEnergy coefficient
            (BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.rekernel
              edgePositive hfirst path) := by
  intro first last hfirst path
  let differences := edgeDifferences coefficient path
  let squareSum := listQSum (fun value => value * value) differences
  let lengthQ := Q'.ofNat (edgeLength path)
  have hsum := edgeDifferences_sum_eqv_endpoint coefficient path
  have hlength := edgeDifferences_length coefficient path
  have hcs0 := listQSum_square_le_length_mul_squareSum differences
  have hcs :
      listQSum (fun value => value) differences *
            listQSum (fun value => value) differences ≤
        lengthQ * squareSum := by
    simpa only [differences, squareSum, lengthQ, hlength] using hcs0
  have hfloorSquares := floor_mul_edgeSquareSum_le_rekernel_linearEnergy
    coefficient floor hfloor0 edgePositive edgeFloor hfirst path
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ floor hcs hfloor0
  have hreorder : floor * (lengthQ * squareSum) ≈
      lengthQ * (floor * squareSum) := by
    exact Q'.eqv_trans _ ((floor * lengthQ) * squareSum) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv floor lengthQ squareSum))
      (Q'.eqv_trans _ ((lengthQ * floor) * squareSum) _
        (Q'.mul_eqv_congr_right _ _ squareSum
          (Q'.mul_comm_eqv floor lengthQ))
        (Q'.mul_assoc_eqv lengthQ floor squareSum))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left floor _ _
        (Q'.eqv_symm (square_eqv_congr hsum))))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.mul_le_mul_of_nonneg_left _ _ lengthQ hfloorSquares
          (ofNat_nonnegative (edgeLength path)))))

/-- Quadratic base-path control survives replacement of the kernel when every
used base edge remains positive and has the supplied replacement floor. -/
theorem floor_mul_endpointDifference_sq_le_quadraticLength_mul_rekernel_Dirichlet
    {State : Type} {kernel replacement : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (hreplacement : ∀ left right, (0 : Q') ≤ replacement left right)
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      (0 : Q') < replacement first next)
    (edgeFloor : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      floor ≤ replacement first next) :
    {first last : State} → (hfirst : first ∈ support) →
      (path : PositiveKernelChainIn kernel support first last) →
      floor *
          ((coefficient first + -coefficient last) *
            (coefficient first + -coefficient last)) ≤
        quadraticLengthScale path *
          finiteJointDirichletEnergy support coefficient replacement := by
  intro first last hfirst path
  let replacementPath :=
    BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.rekernel
      edgePositive hfirst path
  let lengthQ := Q'.ofNat (edgeLength path)
  let globalEnergy :=
    finiteJointDirichletEnergy support coefficient replacement
  have hendpoint :=
    floor_mul_endpointDifference_sq_le_length_mul_rekernel_linearEnergy
      coefficient floor hfloor0 edgePositive edgeFloor hfirst path
  have henergy :=
    linearEnergy_le_length_mul_finiteJointDirichletEnergy
      coefficient hreplacement hfirst replacementPath
  have hlength := edgeLength_rekernel edgePositive hfirst path
  rw [hlength] at henergy
  have hlength0 : (0 : Q') ≤ lengthQ :=
    ofNat_nonnegative (edgeLength path)
  have hscaled :
      lengthQ * linearEnergy coefficient replacementPath ≤
        lengthQ * (lengthQ * globalEnergy) :=
    Q'.mul_le_mul_of_nonneg_left _ _ lengthQ henergy hlength0
  have hfactor :
      lengthQ * (lengthQ * globalEnergy) ≈
        quadraticLengthScale path * globalEnergy := by
    unfold quadraticLengthScale
    refine Q'.eqv_trans _ ((lengthQ * lengthQ) * globalEnergy) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv lengthQ lengthQ globalEnergy)) ?_
    exact Q'.mul_eqv_congr_right _ _ globalEnergy
      (Q'.eqv_symm
        (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
          (edgeLength path) (edgeLength path)))
  exact Q'.le_trans' _ _ _ hendpoint
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfactor))

end PositiveKernelChainIn

/-! ## 3. BF4 specialization on every canonical sector path -/

/-- The explicit finite BF4 edge floor and canonical path satisfy the new
quadratic-length global Dirichlet estimate. -/
theorem centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_quadraticLength_mul_Dirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      PositiveKernelChainIn.quadraticLengthScale
          (centralPhysicalFiniteVacuumSectorPositivePath
            w hw cutoff half left right hleft hright) *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) := by
  let path := centralPhysicalFiniteVacuumSectorPositivePath
    w hw cutoff half left right hleft hright
  have hbound :=
    PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_length_sq_mul_finiteJointDirichletEnergy
      coefficient
      (fun source target => by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          hw cutoff half _ _)
      (centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half)
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
          w hw cutoff half))
      (fun source target hsource htarget hpositive =>
        centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
          w hw cutoff half source target hsource htarget hpositive)
      hleft path
  change centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half *
      ((coefficient left + -coefficient right) *
        (coefficient left + -coefficient right)) ≤
    Q'.ofNat
        (PositiveKernelChainIn.edgeLength path *
          PositiveKernelChainIn.edgeLength path) *
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        coefficient (centralPhysicalFiniteKernel w hw cutoff half)
  exact hbound

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.listQSum_square_le_length_mul_squareSum
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.endpointDifference_sq_le_length_mul_edgeSquareSum
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_length_mul_linearEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.quadraticLengthScale_le_amplificationScale
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_length_sq_mul_finiteJointDirichletEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength_rekernel
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_quadraticLength_mul_rekernel_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy.centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_quadraticLength_mul_Dirichlet
