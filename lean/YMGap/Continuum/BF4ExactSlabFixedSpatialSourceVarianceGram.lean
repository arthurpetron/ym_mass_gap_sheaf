/-
# The centered source-test norm in the SAME interacting variance

Center the observable at the actual original odd-marginal mean, not at a
raw q^2 mean. The symmetric product-heat test norm is exactly

  D + 8*H[q^2*psi*P psi] + 8*Z*Var_odd(f).

The source-increment cost D is unchanged by this centering. The resulting
joint Gram energy inequality retains the original energy, source and odd
partition. The mixed raw-source moment still has no useful upper bound
relative to Z*Var_odd; no survival or scaling conclusion is asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSumNorm
import YMGap.Continuum.SU2QuaternionProductHeatSourceCentering
import YMGap.Continuum.SU2QuaternionProductHeatJumpMean
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
import YMGap.Continuum.GNSUnitCenteredGram

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatJumpMean (productHeat_mass_one)
open YMGap.Continuum.SU2QuaternionProductHeatSumTest (sumTest sumTest_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSumNorm (sumTest_norm_pin)
open YMGap.Continuum.SU2QuaternionProductHeatSourceCentering (sourceIncrementCost_shifted)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair weightedGNSData)
open YMGap.Continuum.GNSUnitCenteredGram (centered_nonnegative joint_energy_budget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_pin marginalMass_positive marginalVariance_pin oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource oddMoment_projected_source energy_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks spatialWeight terminalMessage

/-- Subtract the computed mean of the COMPLETE original marginal. -/
def oddCentered {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (f : RatPoly) : RatPoly :=
  shifted f (normalizedMoment (N width) (marginalWeight w K width depth) f
    (marginalMass_positive hw0 hw1 K width hK depth))

theorem oddCentered_supported {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (oddCentered hw0 hw1 K width hK depth f) :=
  shifted_supported hf _

theorem oddCentered_independent {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (i : Nat) (hi : QuaternionBlockIndependent i f) :
    QuaternionBlockIndependent i (oddCentered hw0 hw1 K width hK depth f) :=
  quaternionBlockIndependent_polyAdd (quaternionBlockIndependent_polySmul 1 hi)
    (quaternionBlockIndependent_polySmul _ (quaternionBlockIndependent_polyOne i))

/-- The projected-source centered square is exactly Z times the EXISTING
interacting variance. No replacement measure or raw q^2 centering is used. -/
theorem centered_source_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let psi := oddCentered hw0 hw1 K width hK depth f
    sourceMoment (N width) w K (List.range (N width)) q (polyMul psi psi) ≈
      oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  let W := marginalWeight w K width depth
  let z := H (N width) W
  let hz := marginalMass_positive hw0 hw1 K width hK depth
  let a := Q'.recipPos z hz
  let psi := oddCentered hw0 hw1 K width hK depth f
  let v := oddVariance hw0 hw1 K width hK depth f
  let A := H (N width) (polyMul W (polyMul psi psi))
  have hp := oddCentered_supported hw0 hw1 K width hK depth hf
  have hind' : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i psi :=
    fun i hi => oddCentered_independent hw0 hw1 K width hK depth i (hind i hi)
  have hpin := oddMoment_projected_source w K width depth (polyMul psi psi)
    (supported_polyMul hp hp)
    (fun i hi => quaternionBlockIndependent_polyMul (hind' i hi) (hind' i hi))
  have hown : A*a ≈ v := Q'.eqv_trans _ _ _
    (own_mean_pin (marginalCertificate hw0 hw1 K width hK depth) hf hz)
    (marginalVariance_pin hw0 hw1 K width hK depth f)
  have hcancel : (A*a)*z ≈ A :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A a z)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_comm_eqv a z))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv z hz))
          (Q'.mul_one_eqv A)))
  have hraw : A ≈ z*v :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z hown)
        (Q'.mul_comm_eqv v z))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hpin)
    (Q'.eqv_trans _ _ _ hraw
      (Q'.mul_eqv_congr_right _ _ v (marginalMass_pin w K width depth)))

/-- The remaining raw-source mixed moment is explicit, but unestimated.
The center is the original q*Pq mean, not the q^2 mean. -/
def centeredMixedMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth f
  H (N width) (polyMul (polyMul q q)
    (polyMul psi (productMap (N width) w K (List.range (N width)) psi)))

/-- The EXACT test norm, with its interacting-variance contribution exposed. -/
def centeredNormExpression {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  sourceIncrementCost (N width) w K (List.range (N width)) q f +
    8*centeredMixedMoment hw0 hw1 K width hK depth f +
    8*(oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f)

theorem centered_sum_norm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let psi := oddCentered hw0 hw1 K width hK depth f
    weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
        (sumTest (N width) q psi) (sumTest (N width) q psi) ≈
      centeredNormExpression hw0 hw1 K width hK depth f := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  have hp := oddCentered_supported hw0 hw1 K width hK depth hf
  have hd := sourceIncrementCost_shifted (N width) w K (List.range (N width))
    (fun _ hi => List.mem_range.mp hi) hq hf
    (normalizedMoment (N width) (marginalWeight w K width depth) f
      (marginalMass_positive hw0 hw1 K width hK depth))
  exact Q'.eqv_trans _ _ _
    (sumTest_norm_pin (N width) w K (List.range (N width))
      (fun _ hi => List.mem_range.mp hi) hq hp)
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hd (Q'.eqv_refl _))
      (Q'.mul_eqv_congr_left 8 _ _
        (centered_source_square hw0 hw1 K width hK depth hf hind)))

/-- The exact centered denominator is nonnegative. This is not a positive
lower bound, and it supplies no upper comparison with the interacting variance. -/
theorem centered_denominator_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let psi := oddCentered hw0 hw1 K width hK depth f
    let W := productHeat (N width) w K (List.range (N width))
    let M := weightedPair (N width+N width) W (sumTest (N width) q psi) polyOne
    (0 : Q') ≤ centeredNormExpression hw0 hw1 K width hK depth f-M*M := by
  dsimp only
  let n := N width
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth f
  let W := productHeat n w K (List.range n)
  let G := weightedGNSData (n+n) W (productHeatCertificate n hw0 hw1 K hK
    (List.range n) (fun _ hi => List.mem_range.mp hi))
  have hq : SupportedQuaternionBlocks n q :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  let o : G.V := ⟨polyOne, supported_one _⟩
  let s : G.V := ⟨sumTest n q psi,
    sumTest_supported hq (oddCentered_supported hw0 hw1 K width hK depth hf)⟩
  have ho : G.B o o ≈ 1 := productHeat_mass_one n w K (List.range n)
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
  exact Q'.le_trans' _ _ _ (centered_nonnegative G o ho s)
    (Q'.le_of_eqv (Q'.add_eqv_congr'
      (centered_sum_norm hw0 hw1 K width hK depth hf hind) (Q'.eqv_refl _)))

/-- Joint centered response budget for the ORIGINAL temporal energy, now
with the SAME interacting variance explicitly in its denominator. The
unestimated mixed moment and both actual means remain; no sign, stationary
source, nonzero response, inverse source norm, or scaling premise is added. -/
theorem original_centered_energy_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let n := N width
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let psi := oddCentered hw0 hw1 K width hK depth f
    let W := productHeat n w K (List.range n)
    let r := polyMul (jump n q) (jump n f)
    let s := sumTest n q psi
    let J := weightedPair (n+n) W r polyOne
    let M := weightedPair (n+n) W s polyOne
    let V := centeredNormExpression hw0 hw1 K width hK depth f-M*M
    let X := weightedPair (n+n) W r s-J*M
    4*V*energy w K width (terminalMessage w K width depth) f +
        V*(J*J)+X*X ≤ 2*V*singleEndedCost n w K (List.range n) q f := by
  dsimp only
  let n := N width
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth f
  let W := productHeat n w K (List.range n)
  let G := weightedGNSData (n+n) W (productHeatCertificate n hw0 hw1 K hK
    (List.range n) (fun _ hi => List.mem_range.mp hi))
  have hq : SupportedQuaternionBlocks n q :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  let o : G.V := ⟨polyOne, supported_one _⟩
  let r : G.V := ⟨polyMul (jump n q) (jump n f),
    supported_polyMul (jump_supported hq) (jump_supported hf)⟩
  let s : G.V := ⟨sumTest n q psi,
    sumTest_supported hq (oddCentered_supported hw0 hw1 K width hK depth hf)⟩
  have ho : G.B o o ≈ 1 := productHeat_mass_one n w K (List.range n)
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
  have he : 4*energy w K width (terminalMessage w K width depth) f+G.B r r ≈
      2*singleEndedCost n w K (List.range n) q f :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left 4 _ _ (energy_projected_source w K width
          (terminalMessage w K width depth) f
          (terminalMessage_supported w K width depth) hf hind)) (Q'.eqv_refl _))
      (four_mul_sourceEnergy_add_increment_eq_two_singleEnded n w K
        (List.range n) (fun _ hi => List.mem_range.mp hi) hq hf)
  exact joint_energy_budget G o ho r s
    (centeredNormExpression hw0 hw1 K width hK depth f)
    (energy w K width (terminalMessage w K width depth) f)
    (singleEndedCost n w K (List.range n) q f)
    (Q'.le_of_eqv (centered_sum_norm hw0 hw1 K width hK depth hf hind)) he

#print axioms oddCentered
#print axioms oddCentered_supported
#print axioms oddCentered_independent
#print axioms centered_source_square
#print axioms centeredMixedMoment
#print axioms centeredNormExpression
#print axioms centered_sum_norm
#print axioms centered_denominator_nonnegative
#print axioms original_centered_energy_budget

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
