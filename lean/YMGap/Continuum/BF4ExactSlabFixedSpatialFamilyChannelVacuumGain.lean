/-
# Quantified passive gain in the ORIGINAL complete signed-family energy

The computed SU(2) channel contraction is instantiated on the literal
projected terminal source, the complete signed plaquette family and its
actual spectator schedule. Nome-zero/one are auxiliary channel-weight tests
with that SAME source fixed; no Yang--Mills law at a different coupling is
substituted. The original signed Taylor debt and cutoff remain unchanged.

The gain is measured against raw-minus-projected SOURCE angular cost, NOT
interacting variance. The original Ward identity places this nonnegative
gain in the SAME-variance budget without dropping either signed correction.
Its useful variance-relative floor and the complete signed physical-scaling
estimate remain OPEN; its energy prefactor is second-order as nome tends to one.
-/

import YMGap.Continuum.SU2QuaternionPassiveChannelStrictAngular
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointCorrection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVacuumGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound (familyChannelFirstOrder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointCorrection
  (family_firstOrder_defect_ward)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (angularWeightDefect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance wardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionPassiveChannelStrictAngular

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass oddVariance
  angularWeightDefect wardResidual

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width depth : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))

/-- Raw angular cost of the unchanged, already fringe-projected terminal
source. This is not the odd-marginal variance. -/
def familyRawAngularCost (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  weightedAngularEnergy (N width-1)
    (projectedEndpointSource w K width (terminalMessage w K width depth))
    (spatialSpan width c qs)

/-- Passive vacuum CHANNEL cost: the literal conditional projection of the
SAME source. This is not a new physical vacuum or replacement measure. -/
def familyVacuumAngularCost (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  weightedAngularEnergy (N width-1)
    (familyProject (familySpectatorBlocks width qs)
      (projectedEndpointSource w K width (terminalMessage w K width depth)))
    (spatialSpan width c qs)

/-- Actual nonnegativity of the raw-minus-vacuum source cost. No terminal
fluctuation or variance-relative lower bound is assumed. -/
theorem family_vacuum_cost_le_raw (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    familyVacuumAngularCost w K width depth c qs ≤ familyRawAngularCost w K width depth c qs := by
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have h := channel_angular_vacuum_le_raw (N width-1) K
    (familySpectatorBlocks width qs)
    (by simpa only [hn] using familySpectatorBlocks_lt width qs)
    (familySpectatorBlocks_nodup width qs)
    (projectedEndpointSource w K width (terminalMessage w K width depth))
    (spatialSpan width c qs)
    (by simpa only [hn] using source_supported w K width depth)
    (by simpa only [hn] using spatialSpan_supported width c qs)
    (spatialSpan_familySpectator_independent width c qs)
  simpa only [familyVacuumAngularCost, familyRawAngularCost] using h

/-- Every width, depth and cutoff; the complete signed family is retained.
The coefficient w^3 depends on nome, not width or the number of channels. -/
theorem family_first_order_vacuum_bound {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    familyChannelFirstOrder w K width depth c qs ≤
      ((1 : Q')-qpow w 3)*familyVacuumAngularCost w K width depth c qs +
        qpow w 3*familyRawAngularCost w K width depth c qs := by
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have h := channel_angular_vacuum_bound (N width-1) hw0 hw1 K
    (familySpectatorBlocks width qs)
    (by simpa only [hn] using familySpectatorBlocks_lt width qs)
    (familySpectatorBlocks_nodup width qs)
    (projectedEndpointSource w K width (terminalMessage w K width depth))
    (spatialSpan width c qs)
    (by simpa only [hn] using source_supported w K width depth)
    (by simpa only [hn] using spatialSpan_supported width c qs)
    (spatialSpan_familySpectator_independent width c qs)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (familyChannelFirstOrder_eq_angular w K width depth c qs))
    (by simpa only [hn, familyRawAngularCost, familyVacuumAngularCost] using h)

/-- Explicit lower budget for the ACTUAL retained source/channel gain.
No lower comparison of raw-minus-vacuum cost with SAME variance is supplied. -/
theorem family_angular_gain_lower {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    ((1 : Q')-qpow w 3)*(familyRawAngularCost w K width depth c qs-
      familyVacuumAngularCost w K width depth c qs) ≤
      familyRawAngularCost w K width depth c qs-familyChannelFirstOrder w K width depth c qs := by
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have h := channel_angular_gain_lower (N width-1) hw0 hw1 K
    (familySpectatorBlocks width qs)
    (by simpa only [hn] using familySpectatorBlocks_lt width qs)
    (familySpectatorBlocks_nodup width qs)
    (projectedEndpointSource w K width (terminalMessage w K width depth))
    (spatialSpan width c qs)
    (by simpa only [hn] using source_supported w K width depth)
    (by simpa only [hn] using spatialSpan_supported width c qs)
    (spatialSpan_familySpectator_independent width c qs)
  refine Q'.le_trans' _ _ _ (by simpa only [hn, familyRawAngularCost, familyVacuumAngularCost] using h) ?_
  exact Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ (familyChannelFirstOrder_eq_angular w K width depth c qs).symm))

/-- Complete ORIGINAL energy consumer. Both signed cubic/cutoff remainders
are unchanged; no absolute-value debt replaces their cancellation. -/
theorem padded_family_energy_vacuum_bound {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K : Nat) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    energy w K width (terminalMessage w K width depth) (spatialSpan width c qs) ≤
      ((1 : Q')-w)*(((1 : Q')-qpow w 3)*familyVacuumAngularCost w K width depth c qs +
        qpow w 3*familyRawAngularCost w K width depth c qs) +
        familyChannelTaylorDebt w K width depth c qs :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (padded_family_channel_energy_taylor w K hwidth depth c qs hqs))
    (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ _
      (family_first_order_vacuum_bound hw0 hw1 K width depth c qs) (Q'.sub_nonneg_of_le hw1))
      (Q'.le_refl' _))

/-- Normalize only by the SAME proved-positive original odd partition.
The source and signed channel debt remain the actual ones at nome w. -/
theorem padded_family_normalized_energy_vacuum_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK depth (spatialSpan width c qs) ≤
      (((1 : Q')-w)*(((1 : Q')-qpow w 3)*familyVacuumAngularCost w K width depth c qs +
        qpow w 3*familyRawAngularCost w K width depth c qs) +
        familyChannelTaylorDebt w K width depth c qs) *
          Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth) :=
  Q'.mul_le_mul_of_nonneg_right _ _ _
    (padded_family_energy_vacuum_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K hwidth depth c qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem vacuum_budget_ward (h r V A D delta R M : Q')
    (hward : (A+delta)+R ≈ 12*M) :
    h*(((1 : Q')-r)*V+r*A)+D ≈
      12*(h*M)+D-h*(delta+R+((1 : Q')-r)*(A-V)) := by
  have hr : h*(((1 : Q')-r)*V+r*A)+D ≈
      h*((A+delta)+R)+D-h*(delta+R+((1 : Q')-r)*(A-V)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
        (.mul (.var 1) (.var 3)))) (.var 4))
      (.add (.add (.mul (.var 0) (.add (.add (.var 3) (.var 5)) (.var 6))) (.var 4))
        (.neg (.mul (.var 0) (.add (.add (.var 5) (.var 6))
          (.mul (.add (.const 1) (.neg (.var 1))) (.add (.var 3) (.neg (.var 2))))))))
      (by decide) (fun
        | 0 => h | 1 => r | 2 => V | 3 => A | 4 => D | 5 => delta | _ => R)
  have hs : h*((A+delta)+R) ≈ 12*(h*M) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left h _ _ hward)
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 12) (.var 1)))
        (.mul (.const 12) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => h | _ => M))
  exact Q'.eqv_trans _ _ _ hr
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hs (Q'.eqv_refl D)) (Q'.eqv_refl _))

/-- Quantified passive gain in the SAME interacting-variance budget.
All original signed Taylor, complete-weight and Ward terms are retained.
No useful bound on their complete combination along a scaling family is
asserted. The gain's prefactor (1-w)*(1-w^3) is second-order near w=1. -/
theorem padded_family_energy_ward_gain {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width) (n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width c qs
    energy w K width (terminalMessage w K width (n+1)) f ≤
      12*(((1 : Q')-w)*(oddMass w K width (n+1)*
        oddVariance hw0 hw1 K width hK (n+1) f)) +
      familyChannelTaylorDebt w K width (n+1) c qs -
      ((1 : Q')-w)*(angularWeightDefect w K width (n+1) f +
        wardResidual hw0 hw1 K width hK (n+1) f +
        ((1 : Q')-qpow w 3)*(familyRawAngularCost w K width (n+1) c qs-
          familyVacuumAngularCost w K width (n+1) c qs)) := by
  dsimp only
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hfirst := sourceFirstOrder_eq_weightedAngularEnergy (N width-1) q f
    (by simpa only [hn] using source_supported w K width (n+1))
    (by simpa only [hn] using spatialSpan_supported width c qs)
  have hraw : familyRawAngularCost w K width (n+1) c qs ≈
      sourceFirstOrder (N width-1) q f := Q'.eqv_symm hfirst
  have hward : (familyRawAngularCost w K width (n+1) c qs+
      angularWeightDefect w K width (n+1) f)+
      wardResidual hw0 hw1 K width hK (n+1) f ≈
      12*(oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' hraw (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (family_firstOrder_defect_ward hw0 hw1 K hwidth hK n qs c hqs)
  exact Q'.le_trans' _ _ _
    (padded_family_energy_vacuum_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      K hwidth (n+1) c qs hqs)
    (Q'.le_of_eqv (vacuum_budget_ward ((1 : Q')-w) (qpow w 3)
      (familyVacuumAngularCost w K width (n+1) c qs)
      (familyRawAngularCost w K width (n+1) c qs)
      (familyChannelTaylorDebt w K width (n+1) c qs)
      (angularWeightDefect w K width (n+1) f)
      (wardResidual hw0 hw1 K width hK (n+1) f)
      (oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f) hward))

#print axioms family_vacuum_cost_le_raw
#print axioms family_first_order_vacuum_bound
#print axioms family_angular_gain_lower
#print axioms padded_family_energy_vacuum_bound
#print axioms padded_family_normalized_energy_vacuum_bound
#print axioms padded_family_energy_ward_gain

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVacuumGain
