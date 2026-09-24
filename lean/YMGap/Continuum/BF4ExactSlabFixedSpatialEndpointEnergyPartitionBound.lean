/-
# Fixed-nome endpoint energy versus the original partition

This combines the spectator-channel geometric energy budget with the computed
first-moment channel floor.  The resulting constant is explicit at each fixed
nome.  No centered-variance or changing-spacing conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelHeatFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelHeatFloor
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss (familyChannelQuadratic)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage energy marginalWeight

/-- The explicit coefficient multiplying the original partition. -/
def endpointEnergyPartitionCoefficient (w : Q') : Q' :=
  (32 : Q') * ((1 : Q') - w) +
    (960 : Q') * (((1 : Q') - w) * ((1 : Q') - w))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_le (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → left c.2 ≤ right c.2) →
      channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self)
        (hw c List.mem_cons_self))
      (channelSum_le left right cs
        (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a * value c) ≈ a * channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => value c.2))
        (channelSum_scale a value cs))
      (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

private theorem rawSourceSquare_nonnegative (width : Nat) (face : Z4Plaq)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    (0 : Q') ≤ rawSourceSquare width face q := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have hf : SupportedQuaternionBlocks (N width) f :=
    character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hs := (Certificate.square (polyMul q f) (supported_polyMul hq hf)).haar_nonnegative
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (haar_of_coeff
    (RatPolyCoeffEqv.mul_four_swap q f q f)))

/-- The literal plaquette square can only decrease the four-times raw mass
upper bound. -/
theorem geometricSourceCost_le_four_rawSourceMass (width : Nat) (face : Z4Plaq)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    geometricSourceCost width face q ≤ (4 : Q') * rawSourceMass width q := by
  unfold geometricSourceCost
  have hn := rawSourceSquare_nonnegative width face q hq
  have hneg : -rawSourceSquare width face q ≤ (0 : Q') := by
    have hadd := Q'.add_le_add_right 0 (rawSourceSquare width face q)
      (-rawSourceSquare width face q) hn
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (QPoly.q_zero_add_eqv (-rawSourceSquare width face q))))
      (Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (Q'.add_neg_self_eqv (rawSourceSquare width face q))))
  have h := Q'.add_le_add_left ((4 : Q') * rawSourceMass width q)
    (-rawSourceSquare width face q) 0 hneg
  rw [Q'.add_zero'] at h
  exact h

private theorem geometricBudget_le_coefficient_mass {w : Q'} (hw1 : w ≤ (1 : Q'))
    (width : Nat) (face : Z4Plaq) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    geometricBudget w width face q ≤
      endpointEnergyPartitionCoefficient w * rawSourceMass width q := by
  let eps := (1 : Q') - w
  let A := rawSourceMass width q
  have heps : (0 : Q') ≤ eps := Q'.sub_nonneg_of_le hw1
  have h8 : (0 : Q') ≤ (8 : Q') * eps := Q'.mul_nonneg _ _ (by decide) heps
  have hgeom := Q'.mul_le_mul_of_nonneg_left _ _ ((8 : Q') * eps)
    (geometricSourceCost_le_four_rawSourceMass width face q hq) h8
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hgeom)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 8) (.var 0)) (.mul (.const 4) (.var 1)))
        (.mul (.mul (.const 960) (.mul (.var 0) (.var 0))) (.var 1)))
      (.mul (.add (.mul (.const 32) (.var 0))
        (.mul (.const 960) (.mul (.var 0) (.var 0)))) (.var 1))
      (by decide) (fun | 0 => eps | _ => A)))

/-- The complete passive geometric budget is controlled by the SAME
conditional channel quadratic. -/
theorem passiveGeometricBudget_le_channelQuadratic {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K width depth : Nat) (face : Z4Plaq) :
    passiveGeometricBudget w K width depth face ≤
      endpointEnergyPartitionCoefficient w *
        familyChannelQuadratic (N width) w K (spectatorBlocks width face)
          (projectedEndpointSource w K width (terminalMessage w K width depth)) := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let b := fun c => plaquetteChannelSource w K width
    (terminalMessage w K width depth) face c
  let mass := fun c => H width (polyMul (b c) (b c))
  have hb (c : GramChannel) (hc : c ∈ cs) : SupportedQuaternionBlocks (N width) (b c.2) :=
    plaquetteChannelSource_supported w K width _
      (terminalMessage_supported w K width depth) face c hc
  have hpoint : channelSum cs (fun c => geometricBudget w width face (b c)) ≤
      channelSum cs (fun c => endpointEnergyPartitionCoefficient w * mass c) :=
    channelSum_le _ _ cs (productChannels_nonnegative (N width) hw0 K _)
      (fun c hc => Q'.le_trans' _ _ _
        (geometricBudget_le_coefficient_mass hw1 width face (b c.2) (hb c hc))
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul (b c.2) (b c.2)))))))
  have hmass : channelSum cs mass ≈
      familyChannelQuadratic (N width) w K (spectatorBlocks width face) q := by
    dsimp [mass, b, cs, q, familyChannelQuadratic, plaquetteChannelSource,
      channelSource]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hpoint (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (channelSum_scale _ mass cs)
      (Q'.mul_eqv_congr_left _ _ _ hmass)))

/-- At fixed nome, the actual original plaquette energy is bounded by the
ORIGINAL marginal partition with a completely explicit coefficient. -/
theorem padded_endpoint_energy_le_originalPartition {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hHead : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (hEndpoint : endpointChannelHeatCutoff w ≤ K)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let f := characterPolynomial (plaquette width face).scalar 1
    (2 : Q') * endpointChannelHeatFloor w * energy w K width g f ≤
      endpointEnergyPartitionCoefficient w * H width (marginalWeight w K width depth) := by
  dsimp only
  let A := familyChannelQuadratic (N width) w K (spectatorBlocks width face)
    (projectedEndpointSource w K width (terminalMessage w K width depth))
  let B := passiveGeometricBudget w K width depth face
  let rho := endpointChannelHeatFloor w
  let kappa := endpointEnergyPartitionCoefficient w
  let Z := H width (marginalWeight w K width depth)
  let E := energy w K width (terminalMessage w K width depth)
    (characterPolynomial (plaquette width face).scalar 1)
  have hE := padded_terminal_plaquette_passive_energy_geometric_budget
    hw0 hw1 K hK2 hHead hwidth depth face hf
  have hB : B ≤ kappa*A := passiveGeometricBudget_le_channelQuadratic
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K width depth face
  have hfloor : rho*A ≤ Z := padded_channelNorm_le_originalPartition
    hw0 hw1 K hwidth hEndpoint depth face hf
  have hrho : (0 : Q') ≤ rho := Q'.le_of_lt (endpointChannelHeatFloor_positive hw0)
  have hkappa : (0 : Q') ≤ kappa := by
    unfold kappa endpointEnergyPartitionCoefficient
    have heps := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide) heps)
      (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ heps heps))
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ rho hE hrho
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ rho hB hrho
  have h3 := Q'.mul_le_mul_of_nonneg_left _ _ kappa hfloor hkappa
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.var 1))
      (.mul (.var 0) (.mul (.const 2) (.var 1)))
      (by decide) (fun | 0 => rho | _ => E)))
    (Q'.le_trans' _ _ _ h1
      (Q'.le_trans' _ _ _ h2
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide) (fun | 0 => rho | 1 => kappa | _ => A))) h3)))

#print axioms endpointEnergyPartitionCoefficient
#print axioms geometricSourceCost_le_four_rawSourceMass
#print axioms passiveGeometricBudget_le_channelQuadratic
#print axioms padded_endpoint_energy_le_originalPartition

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound
