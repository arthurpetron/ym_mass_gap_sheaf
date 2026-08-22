/-
# Moving root recentering on the cutoff-two physical carrier

The same raw coefficient is centered against a different pulled weight at
each representation cutoff.  This module identifies that motion exactly:
the difference of two moving centered coefficients is supported only at the
distinguished root, and its finite `l1` norm is exactly the absolute change
of the scalar head correction.  The already verified head-correction Cauchy
modulus therefore becomes an `l1` Cauchy modulus for the moving coefficient.

This is the coefficient-side seam needed before same-law matrix and diagonal
form perturbations can be combined with the entrywise cutoff perturbations.
It does not supply a cutoff-two-to-limit error budget or a spectral gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem root_shift_sub_eqv
    (raw firstCorrection laterCorrection indicator : Q') :
    (raw + (-firstCorrection) * indicator) +
        (-(raw + (-laterCorrection) * indicator)) ≈
      (laterCorrection + (-firstCorrection)) * indicator := by
  refine Q'.eqv_trans _
    ((raw + (-firstCorrection) * indicator) +
      ((-raw) + (-((-laterCorrection) * indicator)))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_eqv raw ((-laterCorrection) * indicator))
  · refine Q'.eqv_trans _
      ((raw + (-raw)) +
        (((-firstCorrection) * indicator) +
          (-((-laterCorrection) * indicator)))) _
      (Q'.add_swap_inner raw ((-firstCorrection) * indicator)
        (-raw) (-((-laterCorrection) * indicator))) ?_
    refine Q'.eqv_trans _
      (0 + (((-firstCorrection) * indicator) +
        (-((-laterCorrection) * indicator)))) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv raw)) ?_
    refine Q'.eqv_trans _
      (((-firstCorrection) * indicator) +
        (-((-laterCorrection) * indicator))) _
      (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
    have hnegLater :
        (-((-laterCorrection) * indicator)) ≈
          laterCorrection * indicator := by
      refine Q'.eqv_trans _ (-(-(laterCorrection * indicator))) _ ?_ ?_
      · exact Q'.neg_eqv_congr _ _
          (Q'.neg_mul_eqv laterCorrection indicator)
      · exact Q'.neg_neg_eqv _
    refine Q'.eqv_trans _
      (((-firstCorrection) * indicator) +
        laterCorrection * indicator) _
      (Q'.add_eqv_congr_left _ _ _ hnegLater) ?_
    refine Q'.eqv_trans _
      (laterCorrection * indicator +
        (-firstCorrection) * indicator) _
      (Q'.add_comm_eqv _ _) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv laterCorrection (-firstCorrection) indicator)

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

private theorem coefficientL1_root_scaled_eqv
    (states : List Nat) (hnodup : states.Nodup) (hroot : 0 ∈ states)
    (delta : Q') :
    coefficientL1 states
        (fun index => delta * finiteRootIndicator index) ≈
      Q'.abs delta := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index => if index = 0 then Q'.abs delta else 0)
      states) _ ?_ ?_
  · unfold coefficientL1
    apply listQSum_congr_on
    intro index _hindex
    by_cases hzero : index = 0
    · subst index
      simp only [if_pos]
      apply Q'.abs_eqv_congr
      unfold finiteRootIndicator
      simp only [if_pos]
      exact Q'.mul_one_eqv delta
    · simp only [if_neg hzero]
      refine Q'.eqv_trans _ (Q'.abs (0 : Q')) _ ?_ ?_
      · apply Q'.abs_eqv_congr
        unfold finiteRootIndicator
        simp only [if_neg hzero]
        exact Q'.mul_zero_eqv delta
      · exact Q'.eqv_of_eq (by decide : Q'.abs (0 : Q') = 0)
  · exact listQSum_ite_single_local 0
      (fun _index => Q'.abs delta) states hnodup hroot

/-! ## 1. Compact cutoff-two moving-centering aliases -/

def cutoffTwoPulledHeadCorrectionAt
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
    (by decide : (0 : Q') < cutoffTwoHalfCoupling)
    2 0 coefficient cutoff

def cutoffTwoPulledMovingCenteredCoefficientAt
    (cutoff : Nat) (coefficient : Nat → Q') : Nat → Q' :=
  centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
    cutoffTwoHalfCoupling (by decide) 2 cutoff 0 coefficient

/-! ## 2. Exact root-only motion -/

/-- Two moving centerings of one raw coefficient differ by exactly one scalar
multiple of the distinguished root indicator. -/
theorem cutoffTwoPulledMovingCenteredCoefficient_sub_eqv_rootCorrection
    (first later index : Nat) (coefficient : Nat → Q') :
    cutoffTwoPulledMovingCenteredCoefficientAt first coefficient index +
        (-cutoffTwoPulledMovingCenteredCoefficientAt
          later coefficient index) ≈
      (cutoffTwoPulledHeadCorrectionAt later coefficient +
          (-cutoffTwoPulledHeadCorrectionAt first coefficient)) *
        finiteRootIndicator index := by
  have hfirst :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_eqv_rootShift
      (by decide : (0 : Q') < cutoffTwoHalfCoupling)
      2 first 0 index coefficient
  have hlater :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_eqv_rootShift
      (by decide : (0 : Q') < cutoffTwoHalfCoupling)
      2 later 0 index coefficient
  unfold cutoffTwoPulledMovingCenteredCoefficientAt
    cutoffTwoPulledHeadCorrectionAt
  refine Q'.eqv_trans _
    ((coefficient index +
        (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
          (by decide : (0 : Q') < cutoffTwoHalfCoupling)
          2 0 coefficient first) * finiteRootIndicator index) +
      (-(coefficient index +
        (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
          (by decide : (0 : Q') < cutoffTwoHalfCoupling)
          2 0 coefficient later) * finiteRootIndicator index))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      hfirst (Q'.neg_eqv_congr _ _ hlater)
  · exact root_shift_sub_eqv
      (coefficient index)
      (centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        2 0 coefficient first)
      (centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        2 0 coefficient later)
      (finiteRootIndicator index)

/-- The finite `l1` size of moving recentering is exactly the absolute change
of the scalar head correction; no carrier-size factor is lost. -/
theorem cutoffTwoPulledMovingCenteredCoefficient_sub_l1_eqv_headCorrection
    (first later : Nat) (coefficient : Nat → Q') :
    coefficientL1 cutoffTwoPulledStates
        (fun index =>
          cutoffTwoPulledMovingCenteredCoefficientAt first coefficient index +
            (-cutoffTwoPulledMovingCenteredCoefficientAt
              later coefficient index)) ≈
      Q'.abs
        (cutoffTwoPulledHeadCorrectionAt later coefficient +
          (-cutoffTwoPulledHeadCorrectionAt first coefficient)) := by
  refine Q'.eqv_trans _
    (coefficientL1 cutoffTwoPulledStates
      (fun index =>
        (cutoffTwoPulledHeadCorrectionAt later coefficient +
          (-cutoffTwoPulledHeadCorrectionAt first coefficient)) *
            finiteRootIndicator index)) _ ?_ ?_
  · unfold coefficientL1
    apply listQSum_congr_on
    intro index _hindex
    exact Q'.abs_eqv_congr
      (cutoffTwoPulledMovingCenteredCoefficient_sub_eqv_rootCorrection
        first later index coefficient)
  · exact coefficientL1_root_scaled_eqv
      cutoffTwoPulledStates
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) 2 0)
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0)
      (cutoffTwoPulledHeadCorrectionAt later coefficient +
        (-cutoffTwoPulledHeadCorrectionAt first coefficient))

/-! ## 3. The scalar Cauchy modulus becomes coefficient `l1` control -/

theorem cutoffTwoPulledMovingCenteredCoefficient_l1_cauchy
    (coefficient : Nat → Q') :
    ∀ epsilon : Q', (0 : Q') < epsilon →
      ∃ cutoff : Nat, ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        coefficientL1 cutoffTwoPulledStates
            (fun index =>
              cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient index +
                (-cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient index)) ≤
          epsilon := by
  intro epsilon hepsilon
  obtain ⟨cutoff, hcorrection⟩ :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrection_cauchy
      (by decide : (0 : Q') < cutoffTwoHalfCoupling)
      (by decide : cutoffTwoHalfCoupling < (1 : Q'))
      2 0 coefficient epsilon hepsilon
  refine ⟨cutoff, ?_⟩
  intro first later hfirst hlater
  have htwo := hcorrection first later hfirst hlater
  have habs :
      Q'.abs
          (cutoffTwoPulledHeadCorrectionAt later coefficient +
            (-cutoffTwoPulledHeadCorrectionAt first coefficient)) ≤
        epsilon := by
    unfold cutoffTwoPulledHeadCorrectionAt
    exact CReal.abs_sub_le_of_bounds htwo.2 htwo.1
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (cutoffTwoPulledMovingCenteredCoefficient_sub_l1_eqv_headCorrection
        first later coefficient))
    habs

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation.cutoffTwoPulledMovingCenteredCoefficient_sub_eqv_rootCorrection
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation.cutoffTwoPulledMovingCenteredCoefficient_sub_l1_eqv_headCorrection
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation.cutoffTwoPulledMovingCenteredCoefficient_l1_cauchy
