/-
# The exact component-mass defect in the BF4 vacuum-sector density

Conditioning a closed stationary component of mass `m` changes the density,
not merely the probability weight.  If `k` is the full-carrier stationary
density and `k_S` is the component-conditioned density, then on the component

    k_S(x,y) = m * k(x,y),
    k_S(x,y) - 1 = m * (k(x,y) - 1) + (m - 1).

This file proves both identities constructively and records the resulting
pointwise error bound.  It is the exact interface required before any
full-carrier Faraut or local-slice estimate can be reused on the canonical
vacuum sector: the component-mass defect may not be dropped.

No estimate on that mass defect is asserted here.  No thermodynamic or
continuum limit is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
import YMGap.Continuum.BF4PhysicalConditionalDensity
import YMGap.Continuum.BF4LocalContractionGluing

namespace YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

/-- The elementary affine recentering identity, kept explicit because it is
the cancellation step that a subtraction-free AC normalizer cannot close. -/
private theorem mul_centered_add_mass_defect_eqv
    (mass value : Q') :
    mass * (value + (-1)) + (mass + (-1)) ≈
      mass * value + (-1) := by
  have hmulNeg : mass * (-1) ≈ -mass := by
    refine Q'.eqv_trans _ (-(mass * 1)) _
      (Q'.mul_neg_eqv mass 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv mass)
  refine Q'.eqv_trans _
    ((mass * value + (-mass)) + (mass + (-1))) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv mass value (-1))
        (Q'.add_eqv_congr_left (mass * value) _ _ hmulNeg))
  · exact reassoc_cancel_local (mass * value) mass (-1)

/-! ## 1. Generic density rescaling -/

/-- If a joint is reconstructed by a full stationary density, then its
component-conditioned density is exactly the component mass times that full
density. -/
theorem finiteCarrierMassNormalizedDensity_eqv_mass_mul_of_joint_reconstruction
    {State : Type} {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint fullDensity : State → State → Q'}
    {source target : State}
    (hsource : (0 : Q') < weight source)
    (htarget : (0 : Q') < weight target)
    (hreconstruct :
      joint source target ≈
        (weight source * weight target) * fullDensity source target) :
    finiteCarrierMassNormalizedDensity
        mass mass_pos weight joint source target ≈
      mass * fullDensity source target := by
  let reference :=
    finiteCarrierMassNormalizedStationaryProductJoint
      mass mass_pos weight source target
  have hreferencePos : (0 : Q') < reference := by
    exact finiteCarrierMassNormalizedStationaryProductJoint_pos
      hsource htarget
  apply Q'.mul_left_cancel_of_pos hreferencePos
  have hleft :
      reference *
          finiteCarrierMassNormalizedDensity
            mass mass_pos weight joint source target ≈
        joint source target := by
    exact
      finiteCarrierMassNormalizedStationaryProduct_mul_density_eqv_joint
        hsource htarget
  have hreciprocalCancel :
      Q'.recipPos mass mass_pos * mass ≈ 1 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (Q'.recipPos mass mass_pos) mass)
      (Q'.mul_recipPos_eqv mass mass_pos)
  have hright :
      reference * (mass * fullDensity source target) ≈
        joint source target := by
    refine Q'.eqv_trans _
      ((weight source * weight target) * fullDensity source target) _ ?_
      (Q'.eqv_symm hreconstruct)
    unfold reference finiteCarrierMassNormalizedStationaryProductJoint
      finiteStationaryProductJoint
    refine Q'.eqv_trans _
      ((weight source * weight target) *
        (Q'.recipPos mass mass_pos *
          (mass * fullDensity source target))) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      ((weight source * weight target) *
        ((Q'.recipPos mass mass_pos * mass) *
          fullDensity source target)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.recipPos mass mass_pos) mass
            (fullDensity source target)))
    refine Q'.eqv_trans _
      ((weight source * weight target) *
        (1 * fullDensity source target)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hreciprocalCancel)
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.one_mul_eqv (fullDensity source target))
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

/-- The centered conditioned density splits exactly into the rescaled full
density error and the component-mass defect. -/
theorem finiteCarrierMassNormalizedDensity_centered_eqv_mass_mul_full_centered_add_mass_defect
    {State : Type} {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint fullDensity : State → State → Q'}
    {source target : State}
    (hsource : (0 : Q') < weight source)
    (htarget : (0 : Q') < weight target)
    (hreconstruct :
      joint source target ≈
        (weight source * weight target) * fullDensity source target) :
    finiteCarrierMassNormalizedDensity
          mass mass_pos weight joint source target + (-1) ≈
      mass * (fullDensity source target + (-1)) + (mass + (-1)) := by
  refine Q'.eqv_trans _
    (mass * fullDensity source target + (-1)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (finiteCarrierMassNormalizedDensity_eqv_mass_mul_of_joint_reconstruction
        hsource htarget hreconstruct)
  · exact Q'.eqv_symm
      (mul_centered_add_mass_defect_eqv
        mass (fullDensity source target))

/-- Quantitative consequence of the exact split: full-density error is
multiplied by the component mass, while `|m-1|` remains as an unavoidable
additive defect. -/
theorem finiteCarrierMassNormalizedDensity_centered_abs_le_mass_mul_error_add_mass_defect
    {State : Type} {mass error : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint fullDensity : State → State → Q'}
    {source target : State}
    (hsource : (0 : Q') < weight source)
    (htarget : (0 : Q') < weight target)
    (hreconstruct :
      joint source target ≈
        (weight source * weight target) * fullDensity source target)
    (herror : Q'.abs (fullDensity source target + (-1)) ≤ error) :
    Q'.abs
        (finiteCarrierMassNormalizedDensity
          mass mass_pos weight joint source target + (-1)) ≤
      mass * error + Q'.abs (mass + (-1)) := by
  let fullCentered := fullDensity source target + (-1)
  let massDefect := mass + (-1)
  have hsplit :=
    finiteCarrierMassNormalizedDensity_centered_eqv_mass_mul_full_centered_add_mass_defect
      (mass := mass) (mass_pos := mass_pos)
      hsource htarget hreconstruct
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le' (mass * fullCentered) massDefect) ?_
  have hmassNonnegative : (0 : Q') ≤ mass := Q'.le_of_lt mass_pos
  have habsMass : Q'.abs mass ≈ mass :=
    Q'.eqv_of_eq (by
      unfold Q'.abs
      rw [if_pos hmassNonnegative])
  have hproduct :
      Q'.abs (mass * fullCentered) ≈
        mass * Q'.abs fullCentered :=
    Q'.eqv_trans _ _ _
      (q_abs_mul_eqv mass fullCentered)
      (Q'.mul_eqv_congr_right _ _ _ habsMass)
  refine Q'.le_trans' _
    (mass * Q'.abs fullCentered + Q'.abs massDefect) _
    (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv hproduct)) ?_
  exact Q'.add_le_add_right _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ herror hmassNonnegative)

/-- Multiplying a component-conditioned weight by the component mass exactly
recovers the original stationary weight. -/
theorem finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
    {State : Type} (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (state : State) :
    finiteCarrierMassNormalizedWeight mass mass_pos weight state * mass ≈
      weight state := by
  unfold finiteCarrierMassNormalizedWeight Q'.divPos
  refine Q'.eqv_trans _
    (weight state *
      (Q'.recipPos mass mass_pos * mass)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (weight state * 1) _ ?_
    (Q'.mul_one_eqv _)
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (Q'.recipPos mass mass_pos) mass)
      (Q'.mul_recipPos_eqv mass mass_pos))

/-- **Weighted-row mass-defect compiler.**  The conditioned density row is
bounded by the original-weight full-density error restricted to the same
component, plus exactly one copy of `|m-1|`. -/
theorem finiteCarrierMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect
    {State : Type} {states : List State}
    {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint fullDensity : State → State → Q'}
    {source : State}
    (hsource : (0 : Q') < weight source)
    (htarget : ∀ target, target ∈ states →
      (0 : Q') < weight target)
    (hreconstruct : ∀ target, target ∈ states →
      joint source target ≈
        (weight source * weight target) * fullDensity source target)
    (hmass : listQSum weight states ≈ mass) :
    finiteWeightedCenteredRowMass states
        (finiteCarrierMassNormalizedWeight mass mass_pos weight)
        (finiteCarrierMassNormalizedDensity
          mass mass_pos weight joint)
        source ≤
      listQSum
          (fun target =>
            weight target *
              Q'.abs (finiteCenteredDensity fullDensity source target))
          states +
        Q'.abs (mass + (-1)) := by
  let normalizedWeight :=
    finiteCarrierMassNormalizedWeight mass mass_pos weight
  let normalizedDensity :=
    finiteCarrierMassNormalizedDensity mass mass_pos weight joint
  let massDefect := Q'.abs (mass + (-1))
  let restrictedFull := fun target =>
    weight target * Q'.abs (finiteCenteredDensity fullDensity source target)
  let defectTerm := fun target => normalizedWeight target * massDefect
  have hnormalizedNonnegative : ∀ target, target ∈ states →
      (0 : Q') ≤ normalizedWeight target := by
    intro target htargetMem
    unfold normalizedWeight finiteCarrierMassNormalizedWeight Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.le_of_lt (htarget target htargetMem))
      (Q'.le_of_lt (Q'.recipPos_pos mass mass_pos))
  have hrowRewrite :
      finiteWeightedCenteredRowMass states normalizedWeight
          normalizedDensity source ≈
        listQSum
          (fun target =>
            normalizedWeight target *
              Q'.abs
                (finiteCenteredDensity normalizedDensity source target))
          states :=
    finiteWeightedCenteredRowMass_eq_weight_abs
      states normalizedWeight normalizedDensity hnormalizedNonnegative source
  have hpointwise : ∀ target, target ∈ states →
      normalizedWeight target *
          Q'.abs (finiteCenteredDensity normalizedDensity source target) ≤
        restrictedFull target + defectTerm target := by
    intro target htargetMem
    have hcenteredBound :=
      finiteCarrierMassNormalizedDensity_centered_abs_le_mass_mul_error_add_mass_defect
        (mass := mass) (mass_pos := mass_pos)
        hsource (htarget target htargetMem)
        (hreconstruct target htargetMem)
        (Q'.le_refl'
          (Q'.abs (finiteCenteredDensity fullDensity source target)))
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hcenteredBound
      (hnormalizedNonnegative target htargetMem)
    have hright :
        normalizedWeight target *
            (mass *
                Q'.abs (finiteCenteredDensity fullDensity source target) +
              massDefect) ≈
          restrictedFull target + defectTerm target := by
      refine Q'.eqv_trans _
        (normalizedWeight target *
              (mass * Q'.abs
                (finiteCenteredDensity fullDensity source target)) +
          normalizedWeight target * massDefect) _
        (Q'.mul_add_eqv _ _ _) ?_
      apply Q'.add_eqv_congr'
      · refine Q'.eqv_trans _
          ((normalizedWeight target * mass) *
            Q'.abs (finiteCenteredDensity fullDensity source target)) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
        exact Q'.mul_eqv_congr_right _ _ _
          (finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
            mass mass_pos weight target)
      · exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright)
  have hsum := listQSum_mono
    (fun target =>
      normalizedWeight target *
        Q'.abs (finiteCenteredDensity normalizedDensity source target))
    (fun target => restrictedFull target + defectTerm target)
    states hpointwise
  have hnormalizedTotal : listQSum normalizedWeight states ≈ 1 :=
    finiteCarrierMassNormalizedWeight_total_one
      states mass mass_pos weight hmass
  have hsumRight :
      listQSum (fun target => restrictedFull target + defectTerm target)
          states ≈
        listQSum restrictedFull states + massDefect := by
    refine Q'.eqv_trans _
      (listQSum restrictedFull states + listQSum defectTerm states) _
      (listQSum_add restrictedFull defectTerm states) ?_
    apply Q'.add_eqv_congr_left
    refine Q'.eqv_trans _
      (listQSum normalizedWeight states * massDefect) _
      (listQSum_mul_right normalizedWeight massDefect states) ?_
    refine Q'.eqv_trans _ (1 * massDefect) _ ?_
      (Q'.one_mul_eqv massDefect)
    exact Q'.mul_eqv_congr_right _ _ _ hnormalizedTotal
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrowRewrite)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hsumRight))

/-! ## 2. Canonical BF4 vacuum-sector specialization -/

/-- On canonical vacuum-sector indices, the conditioned density is exactly
the vacuum-sector mass times the full physical BF4 density evaluated at the
corresponding carrier states. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedDensity_eqv_mass_mul_fullDensity
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity
        w hw cutoff half source target ≈
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
        centralPhysicalConditionalDensity w hw cutoff half
          (centralPhysicalFiniteStateAt w hw cutoff half source)
          (centralPhysicalFiniteStateAt w hw cutoff half target) := by
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedDensity
  apply
    finiteCarrierMassNormalizedDensity_eqv_mass_mul_of_joint_reconstruction
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
  unfold centralPhysicalFiniteKernel centralPhysicalFiniteWeight
  exact normalizedJoint_eq_marginals_mul_density
    (centralPhysicalFiniteStateAt_mem_positive w hw cutoff half
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw cutoff half hsource))
    (centralPhysicalFiniteStateAt_mem_positive w hw cutoff half
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw cutoff half htarget))

/-- The canonical BF4 conditioned-density error has the exact
mass-rescaled-full-density plus mass-defect decomposition. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centered_eqv_mass_mul_full_centered_add_mass_defect
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half source target + (-1) ≈
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
          (centralPhysicalConditionalDensity w hw cutoff half
            (centralPhysicalFiniteStateAt w hw cutoff half source)
            (centralPhysicalFiniteStateAt w hw cutoff half target) + (-1)) +
        (centralPhysicalFiniteVacuumSectorMass w hw cutoff half + (-1)) := by
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
        centralPhysicalConditionalDensity w hw cutoff half
          (centralPhysicalFiniteStateAt w hw cutoff half source)
          (centralPhysicalFiniteStateAt w hw cutoff half target) + (-1)) _
    (Q'.add_eqv_congr_right _ _ _
      (centralPhysicalFiniteVacuumSectorMassNormalizedDensity_eqv_mass_mul_fullDensity
        hsource htarget)) ?_
  exact Q'.eqv_symm
    (mul_centered_add_mass_defect_eqv
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      (centralPhysicalConditionalDensity w hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half source)
        (centralPhysicalFiniteStateAt w hw cutoff half target)))

/-- On a canonical BF4 vacuum-sector row, the conditioned weighted density
error is bounded by the original physical-density error restricted to that
sector, plus the explicit component-mass defect. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteWeightedCenteredRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half)
        source ≤
      listQSum
          (fun target =>
            centralPhysicalFiniteWeight w hw cutoff half target *
              Q'.abs
                (finiteCenteredDensity
                  (fun left right =>
                    centralPhysicalConditionalDensity w hw cutoff half
                      (centralPhysicalFiniteStateAt
                        w hw cutoff half left)
                      (centralPhysicalFiniteStateAt
                        w hw cutoff half right))
                  source target))
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) +
        Q'.abs
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half + (-1)) := by
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedWeight
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity
  apply
    finiteCarrierMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
      (fun target htarget =>
        centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
  · intro target htarget
    unfold centralPhysicalFiniteKernel centralPhysicalFiniteWeight
    exact normalizedJoint_eq_marginals_mul_density
      (centralPhysicalFiniteStateAt_mem_positive w hw cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half hsource))
      (centralPhysicalFiniteStateAt_mem_positive w hw cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half htarget))
  · unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
    exact Q'.eqv_refl _

end YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.finiteCarrierMassNormalizedDensity_eqv_mass_mul_of_joint_reconstruction
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.finiteCarrierMassNormalizedDensity_centered_eqv_mass_mul_full_centered_add_mass_defect
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.finiteCarrierMassNormalizedDensity_centered_abs_le_mass_mul_error_add_mass_defect
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.finiteCarrierMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.centralPhysicalFiniteVacuumSectorMassNormalizedDensity_eqv_mass_mul_fullDensity
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centered_eqv_mass_mul_full_centered_add_mass_defect
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect.centralPhysicalFiniteVacuumSectorMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect
