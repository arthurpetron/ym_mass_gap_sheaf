/-
# Exact head centering inside the growing physical vacuum sector

An arbitrary coefficient on a fixed base vacuum component can now be
extended by zero to every later component.  To place that vector in the
later vacuum complement without adding coefficients in other superselection
sectors, this file changes only the distinguished root coefficient.  The
correction is the negative pulled mean divided by the strictly positive
later root weight.

The resulting base coefficient is exactly centered for the pulled later
weights, and its arbitrary-coefficient extension is therefore exactly
centered on the full later canonical component.  This constructs the moving
centering witness.  It does not yet prove that the moving centered forms are
Cauchy or satisfy a strict rate uniform in the base cutoff.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_ite_single_local
    {A : Type} [DecidableEq A] (selected : A) (value : A → Q') :
    ∀ items : List A,
      items.Nodup → selected ∈ items →
      listQSum
          (fun item => if item = selected then value item else 0)
          items ≈
        value selected
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum
                (fun item => if item = selected then value item else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _item => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro item hitem
            rw [if_neg]
            · exact Q'.eqv_refl 0
            intro heq
            exact hparts.1 (heq ▸ hitem)
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : head ≠ selected := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left _ _ _
            (listQSum_ite_single_local selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

/-! ## 1. Generic finite-list root centering -/

/-- Change only coefficient zero by the negative weighted mean divided by
the positive root weight. -/
def finiteListRootCenteredCoefficient
    (states : List Nat) (weight : Nat → Q')
    (hrootWeight : (0 : Q') < weight 0)
    (coefficient : Nat → Q') (index : Nat) : Q' :=
  let mean := listQSum
    (fun item => coefficient item * weight item) states
  coefficient index +
    if index = 0 then
      -(Q'.divPos mean (weight 0) hrootWeight)
    else 0

/-- The one-coordinate correction has exactly zero weighted mean. -/
theorem finiteListRootCenteredCoefficient_meanZero
    (states : List Nat) (weight : Nat → Q')
    (hrootWeight : (0 : Q') < weight 0)
    (hnodup : states.Nodup) (hroot : 0 ∈ states)
    (coefficient : Nat → Q') :
    listQSum
        (fun index =>
          finiteListRootCenteredCoefficient
              states weight hrootWeight coefficient index *
            weight index)
        states ≈ 0 := by
  let mean := listQSum
    (fun item => coefficient item * weight item) states
  let ratio := Q'.divPos mean (weight 0) hrootWeight
  have hsplit :
      listQSum
          (fun index =>
            finiteListRootCenteredCoefficient
                states weight hrootWeight coefficient index *
              weight index)
          states ≈
        listQSum
            (fun index => coefficient index * weight index)
            states +
          listQSum
            (fun index =>
              (if index = 0 then -ratio else 0) * weight index)
            states := by
    refine Q'.eqv_trans _
      (listQSum
        (fun index =>
          coefficient index * weight index +
            (if index = 0 then -ratio else 0) * weight index)
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro index _hindex
      exact Q'.add_mul_eqv _ _ _
    · exact listQSum_add _ _ states
  have hcorrectionPointwise :
      listQSum
          (fun index =>
            (if index = 0 then -ratio else 0) * weight index)
          states ≈
        listQSum
          (fun index =>
            if index = 0 then (-ratio) * weight index else 0)
          states := by
    apply listQSum_congr_on
    intro index _hindex
    by_cases hzero : index = 0
    · simp only [if_pos hzero]
      exact Q'.eqv_refl _
    · simp only [if_neg hzero]
      exact Q'.zero_mul_eqv (weight index)
  have hsingle :
      listQSum
          (fun index =>
            (if index = 0 then (-ratio) * weight index else 0))
          states ≈
        (-ratio) * weight 0 :=
    listQSum_ite_single_local 0
      (fun index => (-ratio) * weight index)
      states hnodup hroot
  have hratio : (-ratio) * weight 0 ≈ -mean := by
    refine Q'.eqv_trans _ (-(ratio * weight 0)) _
      (Q'.neg_mul_eqv ratio (weight 0)) ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.divPos_mul_eqv mean (weight 0) hrootWeight)
  have hcorrection :
      listQSum
          (fun index =>
            (if index = 0 then -ratio else 0) * weight index)
          states ≈ -mean :=
    Q'.eqv_trans _ _ _ hcorrectionPointwise
      (Q'.eqv_trans _ _ _ hsingle hratio)
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _ (mean + -mean) _
      (Q'.add_eqv_congr' (Q'.eqv_refl mean) hcorrection)
      (Q'.add_neg_self_eqv mean))

/-! ## 2. The physical pulled root and moving centered coefficient -/

/-- The pulled distinguished root weight is strictly positive at every later
cutoff.  The cutoff index map fixes zero, so this is exactly the later
positive-carrier head weight. -/
theorem centralPhysicalFinitePulledWeight_zero_pos
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (0 : Q') <
      centralPhysicalFinitePulledWeight w hw base later half 0 := by
  unfold centralPhysicalFinitePulledWeight
  rw [centralPhysicalFiniteCutoffIndexMap_zero]
  exact centralPhysicalFiniteWeight_zero_pos w hw later half

/-- Center a fixed base-component coefficient against the pulled weights at
one later cutoff by changing only its root coordinate. -/
def centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Nat → Q' :=
  finiteListRootCenteredCoefficient
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (centralPhysicalFinitePulledWeight w hw base later half)
    (centralPhysicalFinitePulledWeight_zero_pos
      w hw base later half)
    coefficient

/-- The moving head-centered coefficient has exactly zero pulled weighted
mean on the fixed base component. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorWeightedMean
        w hw base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w hw base later half coefficient) ≈ 0 := by
  unfold centralPhysicalFinitePulledVacuumSectorWeightedMean
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
  exact finiteListRootCenteredCoefficient_meanZero
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (centralPhysicalFinitePulledWeight w hw base later half)
    (centralPhysicalFinitePulledWeight_zero_pos w hw base later half)
    (centralPhysicalFiniteVacuumSectorIndices_nodup w hw base half)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw base half)
    coefficient

/-! ## 3. Exact centering after extension to the later component -/

/-- Extending the moving head-centered base coefficient by zero gives an
exactly centered coefficient on the full later canonical vacuum component. -/
theorem centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorWeightedMean w hw later half
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
            w hw base later half coefficient)) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalFiniteVacuumSectorCoefficientExtensionMean_eqv_pulled
      hcutoff
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient))
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
      w hw base later half coefficient)

/-- The diagonal form of the exactly centered later extension is precisely
the pulled diagonal form of the moving head-centered base coefficient. -/
theorem centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw later half
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
            w hw base later half coefficient)) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w hw base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w hw base later half coefficient) :=
  centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled
    hcutoff _

/-- The reflected form of the exactly centered later extension is precisely
the pulled reflected form of the moving head-centered base coefficient. -/
theorem centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw later half
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
            w hw base later half coefficient)) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w hw base later half coefficient) :=
  centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
    hcutoff _

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering.finiteListRootCenteredCoefficient_meanZero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering.centralPhysicalFinitePulledWeight_zero_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering.centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering.centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering.centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering.centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
