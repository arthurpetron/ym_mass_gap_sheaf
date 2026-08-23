/-
# Canonical LDL checks restricted to the physical vacuum component

The same-object coefficient is supported on the canonical vacuum component,
whereas the earlier canonical LDL bridge asked for a certificate on the whole
positive physical carrier.  This module reindexes only the duplicate-free
vacuum-sector list, constructs its canonical positive-head restriction, and
compiles upper-only ordinary or cleared LDL checks on that smaller matrix to
the same-object centered cutoff-limit interface.

Reflection positivity supplies the lower form bound.  No cofinal LDL family,
uniform strict rate, completed-space theorem, thermodynamic or continuum
limit, or Clay conclusion is constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalHeadCenteredPullback
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite coordinates on the vacuum-sector list -/

def centralPhysicalFiniteVacuumSectorCoordinateSize
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length

def centralPhysicalFiniteVacuumSectorCoordinateAt
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half coordinate : Nat) : Nat :=
  finiteListStateAt
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    0 coordinate

def centralPhysicalFiniteVacuumSectorCoordinateWeight
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half coordinate : Nat) : Q' :=
  centralPhysicalFiniteWeight w hw cutoff half
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half coordinate)

def centralPhysicalFiniteVacuumSectorCoordinateKernel
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half left right : Nat) : Q' :=
  centralPhysicalFiniteKernel w hw cutoff half
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half left)
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half right)

def centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coefficient : Nat → Q')
    (coordinate : Nat) : Q' :=
  coefficient
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half coordinate)

/-- Constructive lookup of a coordinate vector by the corresponding ambient
natural-number label. -/
def natListCoordinateLift :
    List Nat → (Nat → Q') → Nat → Q'
  | [], _, _ => 0
  | head :: tail, coordinate, index =>
      if index = head then coordinate 0
      else natListCoordinateLift tail
        (fun position => coordinate (position + 1)) index

/-- Extend a sector-coordinate vector back to ambient positive-carrier
indices using an explicit structurally recursive lookup in the duplicate-free
sector list.  Values outside the sector are irrelevant. -/
def centralPhysicalFiniteVacuumSectorCoordinateLift
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coordinate : Nat → Q')
    (index : Nat) : Q' :=
  natListCoordinateLift
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coordinate index

theorem natList_getD_mem_of_lt
    (fallback : Nat) :
    ∀ (items : List Nat) (coordinate : Nat),
      coordinate < items.length →
        items.getD coordinate fallback ∈ items
  | [], coordinate, hlt => False.elim (Nat.not_lt_zero coordinate hlt)
  | _ :: _, 0, _ => List.mem_cons_self
  | head :: tail, coordinate + 1, hlt =>
      List.mem_cons_of_mem head
        (natList_getD_mem_of_lt fallback tail coordinate
          (Nat.succ_lt_succ_iff.mp hlt))

theorem natListCoordinateLift_getD_of_nodup
    (fallback : Nat) (coordinate : Nat → Q') :
    ∀ (items : List Nat) (position : Nat),
      items.Nodup → position < items.length →
        natListCoordinateLift items coordinate
            (items.getD position fallback) =
          coordinate position := by
  intro items
  induction items generalizing coordinate with
  | nil =>
      intro position _ hposition
      exact False.elim (Nat.not_lt_zero position hposition)
  | cons head tail ih =>
      intro position hnodup hposition
      have hparts := List.nodup_cons.mp hnodup
      cases position with
      | zero =>
          simp only [List.getD_cons_zero, natListCoordinateLift, if_pos]
      | succ position =>
          have htailLt : position < tail.length :=
            Nat.succ_lt_succ_iff.mp hposition
          have htailMem : tail.getD position fallback ∈ tail :=
            natList_getD_mem_of_lt fallback tail position htailLt
          have hne : tail.getD position fallback ≠ head := by
            intro heq
            exact hparts.1 (heq ▸ htailMem)
          simp only [List.getD_cons_succ, natListCoordinateLift,
            if_neg hne]
          exact ih (fun index => coordinate (index + 1))
            position hparts.2 htailLt

theorem centralPhysicalFiniteVacuumSectorCoordinateLift_recovers
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coordinate : Nat → Q') {position : Nat}
    (hposition : position <
      centralPhysicalFiniteVacuumSectorCoordinateSize
        w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
        w hw cutoff half
        (centralPhysicalFiniteVacuumSectorCoordinateLift
          w hw cutoff half coordinate)
        position =
      coordinate position := by
  unfold centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    centralPhysicalFiniteVacuumSectorCoordinateLift
    centralPhysicalFiniteVacuumSectorCoordinateAt finiteListStateAt
  exact natListCoordinateLift_getD_of_nodup 0 coordinate
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    position
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw cutoff half)
    (by simpa [centralPhysicalFiniteVacuumSectorCoordinateSize]
      using hposition)

private theorem finiteWeightedMean_coefficient_congr_local
    (n : Nat) (weight left right : Nat → Q')
    (hagrees : ∀ i, i < n → left i ≈ right i) :
    finiteWeightedMean n weight left ≈
      finiteWeightedMean n weight right := by
  unfold finiteWeightedMean
  apply listQSum_congr_on
  intro i hi
  exact Q'.mul_eqv_congr_right _ _ _
    (hagrees i (List.mem_range.mp hi))

theorem centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteWeightedMean
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateCoefficient
          w hw cutoff half coefficient) ≈
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient := by
  unfold finiteWeightedMean
    centralPhysicalFiniteVacuumSectorCoordinateSize
    centralPhysicalFiniteVacuumSectorCoordinateWeight
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    centralPhysicalFiniteVacuumSectorCoordinateAt
    centralPhysicalFiniteVacuumSectorWeightedMean
  exact Q'.eqv_of_eq
    (finiteIndexSum_eq_listQSum
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) 0
      (fun index => coefficient index *
        centralPhysicalFiniteWeight w hw cutoff half index))

theorem centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteDiagonalQuadratic
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateCoefficient
          w hw cutoff half coefficient) ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  unfold finiteDiagonalQuadratic
    centralPhysicalFiniteVacuumSectorCoordinateSize
    centralPhysicalFiniteVacuumSectorCoordinateWeight
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    centralPhysicalFiniteVacuumSectorCoordinateAt
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
  exact Q'.eqv_of_eq
    (finiteIndexSum_eq_listQSum
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) 0
      (fun index =>
        (coefficient index * coefficient index) *
          centralPhysicalFiniteWeight w hw cutoff half index))

theorem centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateKernel
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateCoefficient
          w hw cutoff half coefficient) ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient := by
  unfold finiteMatrixQuadratic
    centralPhysicalFiniteVacuumSectorCoordinateSize
    centralPhysicalFiniteVacuumSectorCoordinateKernel
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    centralPhysicalFiniteVacuumSectorCoordinateAt
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
    finiteJointQuadratic
  exact finiteIndexDoubleSum_eqv_listQSum
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) 0
    (fun left right =>
      (coefficient left * coefficient right) *
        centralPhysicalFiniteKernel w hw cutoff half left right)

/-- A mean-zero absolute sector estimate is independent of the enumeration
chosen for the duplicate-free sector list.  The explicit coordinate lift is
a right inverse on all in-range positions, so the ambient estimate transports
back to the generated coordinate order without permuting an LDL factor. -/
theorem centralPhysicalFiniteVacuumSectorCoordinateAbsGap_of_sectorAbsGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (hsector : ∀ coefficient : Nat → Q',
      centralPhysicalFiniteVacuumSectorWeightedMean
          w hw cutoff half coefficient ≈ 0 →
        Q'.abs
            (centralPhysicalFiniteVacuumSectorMatrixQuadratic
              w hw cutoff half coefficient) ≤
          q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient)
    (coordinate : Nat → Q')
    (hcenter : finiteWeightedMean
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        coordinate ≈ 0) :
    Q'.abs
        (finiteMatrixQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateKernel
            w hw cutoff half)
          coordinate) ≤
      q * finiteDiagonalQuadratic
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        coordinate := by
  let ambient :=
    centralPhysicalFiniteVacuumSectorCoordinateLift
      w hw cutoff half coordinate
  let recoded :=
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
      w hw cutoff half ambient
  have hrecovers : ∀ i,
      i < centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half →
        recoded i ≈ coordinate i := by
    intro i hi
    exact Q'.eqv_of_eq
      (centralPhysicalFiniteVacuumSectorCoordinateLift_recovers
        w hw cutoff half coordinate hi)
  have hcoordinateMean :
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          recoded ≈ 0 :=
    Q'.eqv_trans _ _ _
      (finiteWeightedMean_coefficient_congr_local
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        recoded coordinate hrecovers)
      hcenter
  have hambientCenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
          w hw cutoff half ambient ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
          w hw cutoff half ambient))
      hcoordinateMean
  have hambientGap := hsector ambient hambientCenter
  have hmatrix :
      finiteMatrixQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateKernel
            w hw cutoff half)
          coordinate ≈
        centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half ambient :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finiteMatrixQuadratic_coefficient_congr hrecovers))
      (centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
        w hw cutoff half ambient)
  have hdiagonal :
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half ambient ≈
        finiteDiagonalQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          coordinate :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
          w hw cutoff half ambient))
      (finiteDiagonalQuadratic_coefficient_congr hrecovers)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hmatrix))
    (Q'.le_trans' _ _ _ hambientGap
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

private theorem finiteListStateAt_zero_mem_of_ne_nil
    {A : Type} (items : List A) (fallback : A)
    (hne : items ≠ []) :
    finiteListStateAt items fallback 0 ∈ items := by
  cases items with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
      simp only [finiteListStateAt, List.getD_cons_zero,
        List.mem_cons, true_or]

theorem centralPhysicalFiniteVacuumSectorCoordinateAt_zero_mem
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorCoordinateAt w hw cutoff half 0 ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half := by
  apply finiteListStateAt_zero_mem_of_ne_nil
  intro hempty
  have hzero := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w hw cutoff half
  rw [hempty] at hzero
  exact List.not_mem_nil hzero

theorem centralPhysicalFiniteVacuumSectorCoordinateWeight_zero_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorCoordinateWeight
        w hw cutoff half 0 := by
  unfold centralPhysicalFiniteVacuumSectorCoordinateWeight
  exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
    (centralPhysicalFiniteVacuumSectorCoordinateAt_zero_mem
      w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorCoordinateSize_pred_succ
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half - 1 + 1 =
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half := by
  apply Nat.sub_add_cancel
  exact Nat.succ_le_iff.mpr
    (List.length_pos_of_mem
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w hw cutoff half))

/-! ## 2. Canonical sector-local upper LDL certificates -/

def centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') :
    FiniteCenteredTwoSidedRestriction
      (centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half)
      q
      (centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorCoordinateKernel
        w hw cutoff half) := by
  let n :=
    centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half - 1
  have hsize : n + 1 =
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half :=
    centralPhysicalFiniteVacuumSectorCoordinateSize_pred_succ
      w hw cutoff half
  rw [← hsize]
  exact finiteCanonicalHeadCenteredRestriction n q
    (centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorCoordinateKernel w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorCoordinateWeight_zero_pos
      w hw cutoff half)

/-- Order-invariant upper certificate for a centered restriction.  Unlike an
LDL table, this retains only the mathematical content needed downstream:
nonnegativity of the reduced upper quadratic in the restriction's own order. -/
structure FiniteCenteredRestrictionUpperPSDCertificate
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    (restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel) : Type 1 where
  upper_nonnegative : ∀ reduced,
    (0 : Q') ≤ finiteMatrixQuadratic
      restriction.reducedSize restriction.upperMatrix reduced

namespace FiniteCenteredRestrictionUpperPSDCertificate

/-- Upper PSD is precisely enough to prove the centered upper contraction;
the restriction supplies both centering and constructive completeness. -/
theorem upperContraction
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    {restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel}
    (certificate :
      FiniteCenteredRestrictionUpperPSDCertificate restriction)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finiteMatrixQuadratic n kernel coefficient ≤
      q * finiteDiagonalQuadratic n weight coefficient := by
  let chosen := restriction.complete coefficient hcenter
  let reduced : Nat → Q' := chosen.val
  have hagrees : ∀ i, i < n →
      coefficient i ≈ restriction.lift reduced i :=
    chosen.property
  have hlift :
      finiteMatrixQuadratic n kernel (restriction.lift reduced) ≤
        q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) := by
    apply finiteReversibleContraction_of_penalized
    · exact Q'.le_trans' _ _ _
        (certificate.upper_nonnegative reduced)
        (Q'.le_of_eqv (restriction.upperIdentify reduced))
    · exact restriction.liftCentered reduced
  have hleft :
      finiteMatrixQuadratic n kernel coefficient ≈
        finiteMatrixQuadratic n kernel (restriction.lift reduced) :=
    finiteMatrixQuadratic_coefficient_congr hagrees
  have hright :
      q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) ≈
        q * finiteDiagonalQuadratic n weight coefficient :=
    Q'.mul_eqv_congr_left q _ _
      (Q'.eqv_symm
        (finiteDiagonalQuadratic_coefficient_congr hagrees))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hlift (Q'.le_of_eqv hright))

end FiniteCenteredRestrictionUpperPSDCertificate

abbrev CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionUpperLDLCertificate
    (centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
      w hw cutoff half q)

abbrev CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionUpperPSDCertificate
    (centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
      w hw cutoff half q)

abbrev CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionUpperClearedLDLCertificate
    (centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
      w hw cutoff half q)

private theorem centralPhysicalFiniteVacuumSectorMeanZeroUpperGap_of_coordinate
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (hupper : ∀ coordinate : Nat → Q',
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          coordinate ≈ 0 →
        finiteMatrixQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorCoordinateKernel
              w hw cutoff half)
            coordinate ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw cutoff half)
            coordinate)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient ≤
      q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  let coordinate :=
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
      w hw cutoff half coefficient
  have hcoordinateCenter :
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          coordinate ≈ 0 :=
    Q'.eqv_trans _ _ _
      (centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
        w hw cutoff half coefficient)
      hcenter
  have hcoordinate := hupper coordinate hcoordinateCenter
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
      w hw cutoff half coefficient
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
      w hw cutoff half coefficient
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hmatrix))
    (Q'.le_trans' _ _ _ hcoordinate
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

namespace CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate

/-- Package an already proved physical-sector absolute gap into the generated
canonical restriction.  This construction uses the coordinate right inverse,
so it is valid under arbitrary enumeration of the duplicate-free sector list. -/
def ofMeanZeroAbsGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (hsector : ∀ coefficient : Nat → Q',
      centralPhysicalFiniteVacuumSectorWeightedMean
          w hw cutoff half coefficient ≈ 0 →
        Q'.abs
            (centralPhysicalFiniteVacuumSectorMatrixQuadratic
              w hw cutoff half coefficient) ≤
          q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient) :
    CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate
      w hw cutoff half q := by
  let restriction :=
    centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
      w hw cutoff half q
  refine { upper_nonnegative := ?_ }
  intro reduced
  have hcenter :
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          (restriction.lift reduced) ≈ 0 :=
    restriction.liftCentered reduced
  have habs :=
    centralPhysicalFiniteVacuumSectorCoordinateAbsGap_of_sectorAbsGap
      hsector (restriction.lift reduced) hcenter
  have hupper :
      finiteMatrixQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateKernel
            w hw cutoff half)
          (restriction.lift reduced) ≤
        q * finiteDiagonalQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          (restriction.lift reduced) :=
    Q'.le_trans' _ _ _
      (Q'.le_abs_self
        (finiteMatrixQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateKernel
            w hw cutoff half)
          (restriction.lift reduced)))
      habs
  have hdifference : (0 : Q') ≤
      q * finiteDiagonalQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          (restriction.lift reduced) +
        -(finiteMatrixQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateKernel
            w hw cutoff half)
          (restriction.lift reduced)) :=
    Q'.sub_nonneg_of_le hupper
  have hpenalized : (0 : Q') ≤
      finitePenalizedReversibleQuadratic
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        q
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateKernel
          w hw cutoff half)
        (restriction.lift reduced) :=
    Q'.le_trans' _ _ _ hdifference
      (Q'.ge_of_eqv
        (finitePenalizedReversibleQuadratic_centered hcenter))
  exact Q'.le_trans' _ _ _ hpenalized
    (Q'.ge_of_eqv (restriction.upperIdentify reduced))

theorem meanZeroAbsGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate
        w hw cutoff half q)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) ≤
      q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w hw cutoff half coefficient)]
  exact centralPhysicalFiniteVacuumSectorMeanZeroUpperGap_of_coordinate
    (fun coordinate hcoordinate =>
      certificate.upperContraction coordinate hcoordinate)
    coefficient hcenter

end CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate

namespace CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate

theorem meanZeroAbsGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate
        w hw cutoff half q)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) ≤
      q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w hw cutoff half coefficient)]
  exact centralPhysicalFiniteVacuumSectorMeanZeroUpperGap_of_coordinate
    (fun coordinate hcoordinate =>
      certificate.upperContraction coordinate hcoordinate)
    coefficient hcenter

end CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate

namespace CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate

theorem meanZeroAbsGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate
        w hw cutoff half q)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) ≤
      q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w hw cutoff half coefficient)]
  exact centralPhysicalFiniteVacuumSectorMeanZeroUpperGap_of_coordinate
    (fun coordinate hcoordinate =>
      certificate.upperContraction coordinate hcoordinate)
    coefficient hcenter

end CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate

/-! ## 3. Cofinal sector-local certificates and the same-object limit -/

abbrev FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionUpperLDLCertificate
    q
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateKernel w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
        w hw cutoff half q)

abbrev FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionUpperClearedLDLCertificate
    q
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateKernel w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
        w hw cutoff half q)

private def toVacuumSectorCenteredStrictGap_of_coordinateUpper
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (anchor : Nat → Nat)
    (anchor_ge : ∀ request, request ≤ anchor request)
    (hupper : ∀ request (coordinate : Nat → Q'),
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw (anchor request) half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw (anchor request) half)
          coordinate ≈ 0 →
        finiteMatrixQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw (anchor request) half)
            (centralPhysicalFiniteVacuumSectorCoordinateKernel
              w hw (anchor request) half)
            coordinate ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw (anchor request) half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw (anchor request) half)
            coordinate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := fun base threshold => anchor (max base threshold)
  anchor_ge := by
    intro base threshold
    exact anchor_ge (max base threshold)
  centeredGap := by
    intro base threshold coefficient
    let request := max base threshold
    let later := anchor request
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    let coordinate :=
      centralPhysicalFiniteVacuumSectorCoordinateCoefficient
        w hw later half extended
    have hrequestLater : request ≤ later := anchor_ge request
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold) hrequestLater
    have hsectorCenter :
        centralPhysicalFiniteVacuumSectorWeightedMean
          w hw later half extended ≈ 0 :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hcoordinateCenter :
        finiteWeightedMean
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw later half)
            coordinate ≈ 0 :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
          w hw later half extended)
        hsectorCenter
    have hcoordinateUpper :
        finiteMatrixQuadratic
              (centralPhysicalFiniteVacuumSectorCoordinateSize
                w hw later half)
              (centralPhysicalFiniteVacuumSectorCoordinateKernel
                w hw later half)
              coordinate ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw later half)
            coordinate :=
      hupper request coordinate hcoordinateCenter
    have hmatrix :
        finiteMatrixQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateKernel
              w hw later half)
            coordinate ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
          w hw later half extended)
        (centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
          hbaseLater coefficient)
    have hdiagonal :
        finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw later half)
            coordinate ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
          w hw later half extended)
        (centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
          hbaseLater coefficient)
    have hpulledNonnegative :
        (0 : Q') ≤
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      fixedBasePulledMovingMatrix_nonnegative
        base later half hbaseLater coefficient
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hpulledNonnegative]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hmatrix))
      (Q'.le_trans' _ _ _ hcoordinateUpper
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

namespace FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate
        w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q :=
  toVacuumSectorCenteredStrictGap_of_coordinateUpper
    hq0 hq1 certificate.anchor certificate.anchor_ge
    (fun request coordinate hcenter =>
      (certificate.certificate request).upperContraction
        coordinate hcenter)

theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate
        w (Q'.le_of_lt hw0) half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
      hw0 hw1 half
      (toVacuumSectorCenteredStrictGap hq0 hq1 certificate)
      base coefficient

end FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate

namespace FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate
        w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q :=
  toVacuumSectorCenteredStrictGap_of_coordinateUpper
    hq0 hq1 certificate.anchor certificate.anchor_ge
    (fun request coordinate hcenter =>
      (certificate.certificate request).upperContraction
        coordinate hcenter)

theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate
        w (Q'.le_of_lt hw0) half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
      hw0 hw1 half
      (toVacuumSectorCenteredStrictGap hq0 hq1 certificate)
      base coefficient

end FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.natList_getD_mem_of_lt
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.natListCoordinateLift_getD_of_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateLift_recovers
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateAbsGap_of_sectorAbsGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FiniteCenteredRestrictionUpperPSDCertificate.upperContraction
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate.ofMeanZeroAbsGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate.meanZeroAbsGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate.meanZeroAbsGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate.meanZeroAbsGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
