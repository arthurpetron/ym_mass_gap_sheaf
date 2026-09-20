/-
# Complementary deficit fractions on finite BF4 carrier prefixes

The finite-prefix compiler already returns one strict rate `q < 1` for every
base carrier up to a chosen finite bound.  This file records the complementary
fraction `epsilon = 1 - q` as explicit data and proves the equivalent moving
form margin

    epsilon * diagonal <= diagonal - transfer.

This is the finite backward face of the forward completed-carrier route.  It
does not identify the moving deficit with the original finite conditional
pairwise variance, and it does not construct a cofinal fraction: the fraction
may shrink as the finite prefix expands.  Consequently no completed,
thermodynamic, continuum, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedRateNoGo
open YMGap.Continuum.HKPos

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

/- The rational normalizer is used only for the cancellation
   `q*d + (1-q)*d = d`; it introduces no axiom. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem rate_add_complement_mul_eqv_local
    (rate diagonal : Q') :
    rate * diagonal + ((1 : Q') + (-rate)) * diagonal ≈ diagonal := by
  have hcomp :
      ((1 : Q') + (-rate)) * diagonal ≈
        diagonal + (-(rate * diagonal)) := by
    q_ring
  refine Q'.eqv_trans _
    (rate * diagonal + (diagonal + (-(rate * diagonal)))) _
    (Q'.add_eqv_congr_left (rate * diagonal) _ _ hcomp) ?_
  refine Q'.eqv_trans _
    (rate * diagonal + ((-(rate * diagonal)) + diagonal)) _
    (Q'.add_eqv_congr_left (rate * diagonal) _ _
      (Q'.add_comm_eqv diagonal (-(rate * diagonal)))) ?_
  refine Q'.eqv_trans _
    ((rate * diagonal + (-(rate * diagonal))) + diagonal) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (rate * diagonal) (-(rate * diagonal)) diagonal)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + diagonal) _
    (Q'.add_eqv_congr_right
      (rate * diagonal + (-(rate * diagonal))) 0 diagonal
      (Q'.add_neg_self_eqv (rate * diagonal))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' diagonal)

private theorem one_sub_one_sub_eqv_local (rate : Q') :
    (1 : Q') + (-((1 : Q') + (-rate))) ≈ rate := by
  have hneg :
      (-((1 : Q') + (-rate))) ≈ (-(1 : Q')) + rate := by
    refine Q'.eqv_trans _ ((-(1 : Q')) + (-(-rate))) _
      (Q'.neg_add_eqv 1 (-rate)) ?_
    exact Q'.add_eqv_congr_left (-(1 : Q')) _ _
      (Q'.neg_neg_eqv rate)
  refine Q'.eqv_trans _ ((1 : Q') + ((-(1 : Q')) + rate)) _
    (Q'.add_eqv_congr_left 1 _ _ hneg) ?_
  refine Q'.eqv_trans _ (((1 : Q') + (-(1 : Q'))) + rate) _
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) rate)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + rate) _
    (Q'.add_eqv_congr_right _ _ rate
      (Q'.add_neg_self_eqv 1)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' rate)

private theorem le_sub_of_add_le_local {left moved upper : Q'}
    (h : left + moved ≤ upper) :
    left ≤ upper + (-moved) := by
  have hshift :
      (left + moved) + (-moved) ≤ upper + (-moved) :=
    Q'.add_le_add_right (left + moved) upper (-moved) h
  have hcollapse : (left + moved) + (-moved) ≈ left := by
    refine Q'.eqv_trans _ (left + (moved + (-moved))) _
      (Q'.add_assoc_eqv left moved (-moved)) ?_
    refine Q'.eqv_trans _ (left + 0) _
      (Q'.add_eqv_congr_left left _ _ (Q'.add_neg_self_eqv moved)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' left)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) hshift

/-! ## The finite-prefix backward package -/

/-- Located maximum of the already-constructed fixed-base rates on the finite
prefix `0, ..., bound`.  This local wrapper avoids importing the larger
generated boundary-CSP tree used by the broader finite-prefix consumer. -/
def finitePrefixRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) : Q' :=
  Q'.runningMax (fun base =>
    (fixedBaseConstructedUniformGapData hw0 hw1 base half).rate) bound

theorem fixedBaseRate_le_finitePrefixRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half base bound : Nat) (hbase : base ≤ bound) :
    (fixedBaseConstructedUniformGapData hw0 hw1 base half).rate ≤
      finitePrefixRate hw0 hw1 half bound := by
  induction bound with
  | zero =>
      have hbaseEq : base = 0 := Nat.eq_zero_of_le_zero hbase
      subst base
      exact Q'.le_runningMax _ 0
  | succ bound ih =>
      by_cases hprevious : base ≤ bound
      · exact Q'.le_trans' _ _ _ (ih hprevious)
          (Q'.le_runningMax_succ _ bound)
      · have hbaseEq : base = bound + 1 := by omega
        subst base
        exact Q'.le_runningMax _ (bound + 1)

private theorem max'_lt_local {left right ceiling : Q'}
    (hleft : left < ceiling) (hright : right < ceiling) :
    Q'.max' left right < ceiling := by
  unfold Q'.max'
  by_cases h : left ≤ right
  · rw [if_pos h]
    exact hright
  · rw [if_neg h]
    exact hleft

theorem finitePrefixRate_lt_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : ∀ bound : Nat,
    finitePrefixRate hw0 hw1 half bound < (1 : Q')
  | 0 => (fixedBaseConstructedUniformGapData hw0 hw1 0 half).rate_lt_one
  | bound + 1 => by
      exact max'_lt_local
        (finitePrefixRate_lt_one hw0 hw1 half bound)
        (fixedBaseConstructedUniformGapData hw0 hw1 (bound + 1) half).rate_lt_one

theorem finitePrefixRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) :
    (0 : Q') ≤ finitePrefixRate hw0 hw1 half bound := by
  exact Q'.le_trans' _ _ _
    (fixedBaseConstructedUniformGapData hw0 hw1 0 half).rate_nonnegative
    (fixedBaseRate_le_finitePrefixRate
      hw0 hw1 half 0 bound (Nat.zero_le _))

/-- One complementary fraction for a finite prefix of the already-constructed
carriers.  It is the exact rational complement of the common prefix rate. -/
def finitePrefixDeficitFraction
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) : Q' :=
  (1 : Q') + -(finitePrefixRate hw0 hw1 half bound)

theorem finitePrefixDeficitFraction_pos
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) :
    (0 : Q') < finitePrefixDeficitFraction hw0 hw1 half bound := by
  unfold finitePrefixDeficitFraction
  exact HKPos.one_sub_pos (finitePrefixRate_lt_one hw0 hw1 half bound)

theorem finitePrefixDeficitFraction_le_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) :
    finitePrefixDeficitFraction hw0 hw1 half bound ≤ (1 : Q') := by
  unfold finitePrefixDeficitFraction
  have hnonpositive :
      -(finitePrefixRate hw0 hw1 half bound) ≤ (0 : Q') :=
    Q'.nonpos_neg_of_nonneg
      (finitePrefixRate_nonnegative hw0 hw1 half bound)
  exact Q'.le_trans' _ ((1 : Q') + 0) _
    (Q'.add_le_add_left 1 _ _ hnonpositive)
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))

theorem finitePrefixDeficitFraction_complement_rate_eqv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) :
    (1 : Q') + -finitePrefixDeficitFraction hw0 hw1 half bound ≈
      finitePrefixRate hw0 hw1 half bound := by
  unfold finitePrefixDeficitFraction
  exact one_sub_one_sub_eqv_local (finitePrefixRate hw0 hw1 half bound)

/-! ## The moving posterior/deficit margin -/

/-- A finite-prefix package with an explicit complementary fraction and a
moving diagonal-minus-transfer margin.  The fields deliberately retain the
finite prefix and its later-cutoff start, so this record cannot be mistaken
for a cofinal uniform certificate. -/
structure FixedCarrierPrefixDeficitFractionData
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  fraction_eq : fraction = finitePrefixDeficitFraction hw0 hw1 half bound
  moving_margin : ∀ base : Nat, base ≤ bound → ∀ later : Nat,
      (fixedBaseConstructedUniformGapData
        hw0 hw1 base half).start ≤ later →
      ∀ coefficient : Nat → Q',
      let moving :=
        centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient
      fraction *
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w (Q'.le_of_lt hw0) base later half moving ≤
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w (Q'.le_of_lt hw0) base later half moving +
          (-centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w (Q'.le_of_lt hw0) base later half moving)

/- The rate bound is first converted to a one-sided matrix bound, using the
   already-proved nonnegativity of the moving matrix. -/
private theorem moving_matrix_le_rate_mul_diagonal_local
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound base later : Nat) (hbase : base ≤ bound)
    (hlater : (fixedBaseConstructedUniformGapData
      hw0 hw1 base half).start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half moving ≤
      finitePrefixRate hw0 hw1 half bound *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) base later half moving := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w (Q'.le_of_lt hw0) base later half coefficient
  have hgap :=
    (fixedBaseConstructedUniformGapData
      hw0 hw1 base half).moving_abs_gap later hlater coefficient
  have hmatrixNonnegative :=
    fixedBasePulledMovingMatrix_nonnegative
      (w := w) (hw := Q'.le_of_lt hw0) base later half
      (Nat.le_trans
        (fixedBaseConstructedUniformGapData
          hw0 hw1 base half).start_ge_base hlater) coefficient
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
      (w := w) (hw := Q'.le_of_lt hw0) base later half
      (Nat.le_trans
        (fixedBaseConstructedUniformGapData
          hw0 hw1 base half).start_ge_base hlater) coefficient
  have hdiagonal : (0 : Q') ≤
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half moving :=
    Q'.le_trans' _ _ _ hmatrixNonnegative hmatrixDiagonal
  dsimp [moving] at hgap hmatrixNonnegative hmatrixDiagonal hdiagonal ⊢
  rw [ExpNeg.abs_of_nonneg hmatrixNonnegative] at hgap
  exact Q'.le_trans' _ _ _ hgap
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (fixedBaseRate_le_finitePrefixRate
        hw0 hw1 half base bound hbase) hdiagonal)

/-- The finite-prefix rate package canonically yields the complementary
fraction package. -/
def fixedCarrierPrefixDeficitFractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound : Nat) :
    FixedCarrierPrefixDeficitFractionData w hw0 hw1 half bound where
  fraction := finitePrefixDeficitFraction hw0 hw1 half bound
  fraction_pos := finitePrefixDeficitFraction_pos hw0 hw1 half bound
  fraction_le_one := finitePrefixDeficitFraction_le_one hw0 hw1 half bound
  fraction_eq := rfl
  moving_margin := by
    intro base hbase later hlater coefficient
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient
    let rate := finitePrefixRate hw0 hw1 half bound
    let diagonal :=
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half moving
    let matrix :=
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half moving
    have hmatrix : matrix ≤ rate * diagonal :=
      moving_matrix_le_rate_mul_diagonal_local
        hw0 hw1 half bound base later hbase hlater coefficient
    have hsum : matrix + ((1 : Q') + (-rate)) * diagonal ≤
        rate * diagonal + ((1 : Q') + (-rate)) * diagonal :=
      Q'.add_le_add_right matrix (rate * diagonal)
        (((1 : Q') + (-rate)) * diagonal) hmatrix
    have hright :
        rate * diagonal + ((1 : Q') + (-rate)) * diagonal ≤ diagonal :=
      Q'.le_of_eqv (rate_add_complement_mul_eqv_local rate diagonal)
    have htotal : matrix + ((1 : Q') + (-rate)) * diagonal ≤ diagonal :=
      Q'.le_trans' _ _ _ hsum hright
    have hmargin : ((1 : Q') + (-rate)) * diagonal ≤
        diagonal + (-matrix) :=
      le_sub_of_add_le_local
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.add_comm_eqv
            (((1 : Q') + (-rate)) * diagonal) matrix)) htotal)
    exact hmargin

/-! ## The missing cofinal floor as a minimal backward certificate -/

/-- A single positive floor below every finite-prefix deficit.  This is the
minimal cofinal input needed to turn the finite forward estimates into one
carrier-independent strict rate; no producer for this structure is claimed. -/
structure FixedNomeCofinalFinitePrefixDeficitFloor
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (fraction : Q') : Type 1 where
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  fraction_le_prefix : ∀ bound : Nat,
    fraction ≤ finitePrefixDeficitFraction hw0 hw1 half bound

namespace FixedNomeCofinalFinitePrefixDeficitFloor

private theorem finitePrefixRate_mono_local
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half bound later : Nat) (hbound : bound ≤ later) :
    finitePrefixRate hw0 hw1 half bound ≤
      finitePrefixRate hw0 hw1 half later := by
  induction later with
  | zero =>
      have hboundEq : bound = 0 := Nat.eq_zero_of_le_zero hbound
      subst bound
      exact Q'.le_refl' _
  | succ later ih =>
      by_cases hprevious : bound ≤ later
      · exact Q'.le_trans' _ _ _ (ih hprevious)
          (Q'.le_runningMax_succ _ later)
      · have hboundEq : bound = later + 1 := by omega
        subst bound
        exact Q'.le_refl' _

/-- A schedule-shaped cofinal strict rate ceiling is exactly a positive
complementary deficit floor.  The schedule is used only to enlarge each
requested finite prefix; no infinite supremum or new uniform estimate is
constructed. -/
def ofCofinalRateCeiling
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeCofinalFinitePrefixRateCeiling
      w hw0 hw1 half q) :
    FixedNomeCofinalFinitePrefixDeficitFloor
      w hw0 hw1 half ((1 : Q') + (-q)) where
  fraction_pos := by
    exact HKPos.one_sub_pos family.rate_lt_one
  fraction_le_one := by
    have hneg : -q ≤ (0 : Q') :=
      Q'.nonpos_neg_of_nonneg family.rate_nonnegative
    exact Q'.le_trans' _ ((1 : Q') + 0) _
      (Q'.add_le_add_left 1 _ _ hneg)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))
  fraction_le_prefix := by
    intro bound
    unfold finitePrefixDeficitFraction
    have hanchor : bound ≤ family.anchor bound :=
      family.anchor_ge bound
    have hmonotone := finitePrefixRate_mono_local
      hw0 hw1 half bound (family.anchor bound) hanchor
    have hceiling := family.prefixRate_le bound
    change finitePrefixRate hw0 hw1 half (family.anchor bound) ≤ q at hceiling
    have hq : (1 : Q') + (-q) ≤
        (1 : Q') + (-(finitePrefixRate hw0 hw1 half (family.anchor bound))) :=
      Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hceiling)
    have hrequest : (1 : Q') +
        (-(finitePrefixRate hw0 hw1 half (family.anchor bound))) ≤
        (1 : Q') + (-(finitePrefixRate hw0 hw1 half bound)) :=
      Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hmonotone)
    exact Q'.le_trans' _ _ _ hq hrequest

/-- The same conversion can be driven directly by the existing all-base
uniform-rate certificate.  The identity schedule is supplied by the
cofinal-rate bridge; this definition adds no new estimate. -/
def ofUniformConstructedVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q) :
    FixedNomeCofinalFinitePrefixDeficitFloor
      w hw0 hw1 half ((1 : Q') + (-q)) :=
  ofCofinalRateCeiling
    (YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge.FixedNomeUniformConstructedVacuumSectorRateBound.toCofinalFinitePrefixRateCeiling
      family)

private theorem one_sub_lt_one_local (fraction : Q')
    (hfraction : (0 : Q') < fraction) :
    (1 : Q') + (-fraction) < (1 : Q') := by
  have hnum : (0 : Int) < fraction.num := Q'.num_pos_of_pos hfraction
  change (((1 : Int) * (fraction.den : Int) +
      (-fraction.num) * (1 : Int)) * (1 : Int)) <
    ((1 : Int) * (((1 : Nat) * fraction.den : Nat) : Int))
  simp only [Nat.one_mul, Int.one_mul, Int.mul_one]
  omega

/-- The cofinal deficit floor is exactly the complementary uniform rate
`q = 1 - fraction` required by the existing centered-rate bridge. -/
def toUniformConstructedVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {fraction : Q'}
    (family : FixedNomeCofinalFinitePrefixDeficitFloor
      w hw0 hw1 half fraction) :
    FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half ((1 : Q') + (-fraction)) where
  rate_nonnegative := Q'.sub_nonneg_of_le family.fraction_le_one
  rate_lt_one := one_sub_lt_one_local fraction family.fraction_pos
  constructedRate_le := by
    intro base
    have hprefix : finitePrefixRate hw0 hw1 half base ≤
        (1 : Q') + (-fraction) := by
      have hfloor := family.fraction_le_prefix base
      unfold finitePrefixDeficitFraction at hfloor
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv
          (Q'.neg_neg_eqv (finitePrefixRate hw0 hw1 half base)))
        (Q'.neg_le_sub_of_le_add hfloor)
    exact Q'.le_trans' _ _ _
      (fixedBaseRate_le_finitePrefixRate
        hw0 hw1 half base base (Nat.le_refl base)) hprefix

/-- A cofinal deficit floor can be returned to the schedule-shaped rate
certificate with the identity schedule.  Together with
`ofCofinalRateCeiling`, this exposes the exact typed forward/backward
interface between the two certificates. -/
def toCofinalFinitePrefixRateCeiling
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {fraction : Q'}
    (family : FixedNomeCofinalFinitePrefixDeficitFloor
      w hw0 hw1 half fraction) :
    FixedNomeCofinalFinitePrefixRateCeiling
      w hw0 hw1 half ((1 : Q') + (-fraction)) :=
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge.FixedNomeUniformConstructedVacuumSectorRateBound.toCofinalFinitePrefixRateCeiling
    family.toUniformConstructedVacuumSectorRateBound

/-! ## The half-zero global-path obstruction -/

/-- At half-extent zero, the existing global path-ceiling/global edge-floor
compiler makes a positive cofinal deficit floor impossible. -/
theorem no_halfZero_cofinalDeficitFloor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {fraction : Q'}
    (floor : FixedNomeCofinalFinitePrefixDeficitFloor
      w hw0 hw1 0 fraction) : False := by
  exact
    FixedNomeUniformConstructedVacuumSectorRateBound.impossible
      floor.toUniformConstructedVacuumSectorRateBound

/-- The same obstruction stated at the witness boundary. -/
theorem no_halfZero_cofinalDeficitFloor_nonempty
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {fraction : Q'} :
    Not (Nonempty
      (FixedNomeCofinalFinitePrefixDeficitFloor
        w hw0 hw1 0 fraction)) := by
  intro hfloor
  rcases hfloor with ⟨floor⟩
  exact no_halfZero_cofinalDeficitFloor hw0 hw1 floor

/-- The schedule-shaped half-zero ceiling is ruled out by the same
ceiling-to-floor conversion. -/
theorem no_halfZero_cofinalRateCeiling
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {q : Q'}
    (ceiling : FixedNomeCofinalFinitePrefixRateCeiling
      w hw0 hw1 0 q) : False := by
  exact
    FixedNomeUniformConstructedVacuumSectorRateBound.impossible
      ceiling.toUniformConstructedVacuumSectorRateBound

end FixedNomeCofinalFinitePrefixDeficitFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.finitePrefixDeficitFraction_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.finitePrefixDeficitFraction_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.fixedCarrierPrefixDeficitFractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.FixedNomeCofinalFinitePrefixDeficitFloor.ofCofinalRateCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.FixedNomeCofinalFinitePrefixDeficitFloor.ofUniformConstructedVacuumSectorRateBound
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.FixedNomeCofinalFinitePrefixDeficitFloor.toUniformConstructedVacuumSectorRateBound
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.FixedNomeCofinalFinitePrefixDeficitFloor.toCofinalFinitePrefixRateCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.FixedNomeCofinalFinitePrefixDeficitFloor.no_halfZero_cofinalDeficitFloor
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.FixedNomeCofinalFinitePrefixDeficitFloor.no_halfZero_cofinalDeficitFloor_nonempty
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixDeficitFraction.FixedNomeCofinalFinitePrefixDeficitFloor.no_halfZero_cofinalRateCeiling
