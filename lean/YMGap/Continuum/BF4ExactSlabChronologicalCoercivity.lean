/-
# Centered original Dirichlet bound with chronological area cost

The exact original partition and replica factor cancel before the final
coefficient is stated. Every energy is the pre-existing physical-link
conditional residual on the unchanged full-action completion. The explicit
coefficient remains nome- and area-dependent, not scaling-uniform.
-/

import YMGap.Continuum.BF4ExactSlabOriginalVariancePins
import YMGap.Continuum.BF4ExactSlabChronologicalCostBound
import YMGap.Continuum.BF4ExactSlabChronologicalDirichletSum
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4ExactSlabChronologicalCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.BF4ExactSlabOrderedPathVariance
open YMGap.Continuum.BF4ExactSlabOrderedPathEnergy
open YMGap.Continuum.BF4ExactSlabChronologicalLinkOrder
open YMGap.Continuum.BF4ExactSlabChronologicalPathSum
open YMGap.Continuum.BF4ExactSlabChronologicalCostBound
open YMGap.Continuum.BF4ExactSlabChronologicalDirichletSum
open YMGap.Continuum.BF4ExactSlabOriginalVariancePins
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem embedded_norm (D : GNSData) (p : D.V) :
    normSq (embedV D p) = rat (D.B p p) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem payment_eq (c z : Q') (E : RC) :
    RCscale (c*z) (RCadd E E) = RCscale (2*z) (RCscale c E) := by
  refine Quotient.inductionOn E ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.add (.var 2) (.var 2)))
      (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => c | 1 => z | _ => X.approx n)))

private theorem scale_cancel {c : Q'} (hc : (0 : Q') < c) {x y : RC}
    (h : RCle (RCscale c x) (RCscale c y)) : RCle x y := by
  have hs := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos c hc)) h
  have he : Q'.recipPos c hc*c ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  simpa only [RCscale_RCscale, RCSignedPairBudget.scale_congr he, RCscale_one] using hs

/-- Exactly N times the chronological area comparison, with no partition
or representation cutoff in the coefficient. -/
def poincareCost {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : Q' :=
  Q'.ofNat (blocks extent) * areaCost hw0 hw1 extent

/-- A time-zero spatial plaquette witnesses a physical link even at extent zero. -/
theorem blocks_positive (extent : Nat) : 0 < blocks extent := by
  have hp : ((0,0,0,0), Z4Plane.p01) ∈ boundaryCompleteSlabPlaquettes extent := by
    apply (mem_boundaryCompleteSlabPlaquettes extent _).mpr
    constructor
    · apply (mem_boxPlaquettes _ _).mpr
      exact ⟨Nat.succ_pos extent, Nat.succ_pos extent,
        Nat.succ_pos extent, Nat.succ_pos extent⟩
    · exact Nat.zero_le extent
  have hl : ((0,0,0,0), Dir4.x0) ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent _).mpr
      ⟨((0,0,0,0), Z4Plane.p01), hp, List.mem_cons_self⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)

theorem poincareCost_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : (0 : Q') < poincareCost hw0 hw1 extent := by
  apply Q'.mul_pos _ (areaCost_positive hw0 hw1 extent)
  have hN := blocks_positive extent
  cases hn : blocks extent with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

/-- Positive lower Dirichlet coefficient; late K is absent from its data. -/
def areaCoercivity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : Q' :=
  Q'.recipPos (poincareCost hw0 hw1 extent) (poincareCost_positive hw0 hw1 extent)

theorem areaCoercivity_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : (0 : Q') < areaCoercivity hw0 hw1 extent := Q'.recipPos_pos _ _

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "Z" => originalPartition w K extent
local notation "U" => (Subtype.mk polyOne (supported_one (blocks extent)))

private theorem energyTerm_le_area (p : (F).V) (k : Nat) (hk : k < blocks extent) :
    RCle (chronologicalEnergyTerm hw0 hw1 K extent hK p k)
      (RCscale (2*Z) (RCscale (areaCost hw0 hw1 extent)
        (chronologicalResidualEnergy hw0 hw1 K extent hK p k))) := by
  have hcost := chronological_stepCost_le_areaCost hw0 hw1 extent k hk
  have he := chronologicalResidualEnergy_nonnegative hw0 hw1 K extent hK p k
  have h := RCscale_mono
    (Q'.le_of_lt (Q'.mul_pos (by decide : (0 : Q') < 2)
      (originalPartition_positive hw0 hw1 K extent hK)))
    (RCscale_scalar_mono hcost he)
  simpa only [chronologicalEnergyTerm, chronologicalResidualEnergy, dif_pos hk,
    payment_eq] using h

private theorem sum_energyTerm_le_area (p : (F).V) :
    RCle (sumOn (List.range (blocks extent))
      (chronologicalEnergyTerm hw0 hw1 K extent hK p))
      (RCscale (2*Z) (RCscale (areaCost hw0 hw1 extent)
        ((P).finalEnergy (schedule extent) (embedV F p)))) := by
  have h := sumOn_mono (List.range (blocks extent))
    (chronologicalEnergyTerm hw0 hw1 K extent hK p)
    (fun k => RCscale (2*Z) (RCscale (areaCost hw0 hw1 extent)
      (chronologicalResidualEnergy hw0 hw1 K extent hK p k)))
    (fun k hk => energyTerm_le_area hw0 hw1 K extent hK p k (List.mem_range.mp hk))
  rw [sumOn_scale, sumOn_scale, chronologicalResidualEnergy_sum] at h
  exact h

/-- Centered ORIGINAL finite-volume Poincare upper bound, uniform over
K >= headCutoff(w). Nome and extent remain in the explicit coefficient. -/
theorem dense_centered_poincare (p : (F).V) (hcenter : (F).B p U ≈ 0) :
    RCle (normSq (embedV F p))
      (RCscale (poincareCost hw0 hw1 extent)
        ((P).finalEnergy (schedule extent) (embedV F p))) := by
  have h := RCle_trans (original_chronological_path_energy_bound hw0 hw1 K extent hK p)
    (RCscale_mono (Q'.ofNat_nonneg (blocks extent))
      (sum_energyTerm_le_area hw0 hw1 K extent hK p))
  have hleft : Quotient.mk crealSetoid (ofQ' (2 * varianceDeterminant w K extent p.val)) =
      RCscale (2*Z) (normSq (embedV F p)) := by
    rw [embedded_norm, scale_rat]
    exact Quotient.sound (ofQ'_equiv_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (centered_determinant_pin hw0 hw1 K extent hK p hcenter))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))
  have hright (E : RC) :
      RCscale (Q'.ofNat (blocks extent))
        (RCscale (2*Z) (RCscale (areaCost hw0 hw1 extent) E)) =
      RCscale (2*Z) (RCscale (poincareCost hw0 hw1 extent) E) := by
    simp only [RCscale_RCscale, poincareCost]
    apply RCSignedPairBudget.scale_congr
    exact RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => Q'.ofNat (blocks extent) | 1 => 2*Z | _ => areaCost hw0 hw1 extent)
  rw [hleft, hright] at h
  exact scale_cancel
    (Q'.mul_pos (by decide : (0 : Q') < 2) (originalPartition_positive hw0 hw1 K extent hK)) h

/-- Positive centered coercivity with the SAME explicit area-dependent cost. -/
theorem dense_centered_area_coercivity (p : (F).V) (hcenter : (F).B p U ≈ 0) :
    RCle (RCscale (areaCoercivity hw0 hw1 extent) (normSq (embedV F p)))
      ((P).finalEnergy (schedule extent) (embedV F p)) := by
  have h := RCscale_mono (Q'.le_of_lt (areaCoercivity_positive hw0 hw1 extent))
    (dense_centered_poincare hw0 hw1 K extent hK p hcenter)
  rw [RCscale_RCscale] at h
  have he : areaCoercivity hw0 hw1 extent * poincareCost hw0 hw1 extent ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  rw [RCSignedPairBudget.scale_congr he, RCscale_one] at h
  exact h

#print axioms poincareCost
#print axioms blocks_positive
#print axioms poincareCost_positive
#print axioms areaCoercivity_positive
#print axioms dense_centered_poincare
#print axioms dense_centered_area_coercivity

end YMGap.Continuum.BF4ExactSlabChronologicalCoercivity
