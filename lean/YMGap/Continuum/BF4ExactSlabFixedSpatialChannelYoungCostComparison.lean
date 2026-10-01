/-
# Exact Young-cost contraction after integrating spectator heat channels

For one literal plaquette, the complete positive Gram-channel family has an
exact Young cost no larger than the original one-ended cost.  The signed
spin-one coefficient is handled before comparison: its negative branch uses
the already-proved three-vector contraction of `4-f²`.  This statement does
not split a signed plaquette family or remove its cross terms.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
import YMGap.Continuum.SU2HeatFundamentalIncrementBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.HeatKernelGap (qpow_le_one)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelGeometricContraction
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
open YMGap.Continuum.SU2HeatFundamentalIncrementBudget (fundamental_curvature_bounds)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks plaquette channelSource plaquetteChannelCost

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_add (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => left c + right c) ≈
        channelSum cs left + channelSum cs right
  | [] => Q'.eqv_refl _
  | c::cs => by
      change c.1*(left c.2+right c.2) + channelSum cs (fun d => left d+right d) ≈
        (c.1*left c.2+channelSum cs left) +
          (c.1*right c.2+channelSum cs right)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add left right cs))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide)
          (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
               | 2 => channelSum cs left | _ => channelSum cs right))

private theorem channelSum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a*value c) ≈ a*channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => value c.2))
        (channelSum_scale a value cs))
      (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

/-- The exact one-ended cost of the complete spectator-integrated channel
family, with the original unnormalized Gram weights. -/
def channelYoungCost (width : Nat) (face : Z4Plaq) (w : Q') (K : Nat)
    (q : RatPoly) : Q' :=
  channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
    plaquetteChannelCost width face w
      (channelSource (spectatorBlocks width face) q c))

/-- The missing plaquette-square comparison is a direct application of the
coefficient-one weighted Bessel theorem, since the whole face is independent
of every spectator block. -/
theorem channelSourceSquare_le_raw (width : Nat) (face : Z4Plaq) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    channelSum (productChannels (N width) w K (spectatorBlocks width face))
      (fun c => rawSourceSquare width face
        (channelSource (spectatorBlocks width face) q c)) ≤
      rawSourceSquare width face q := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have hf : SupportedQuaternionBlocks (N width) f :=
    character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hnd : (spectatorBlocks width face).Nodup :=
    List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))
  have h := productChannels_familyProject_weighted_square_le (N width) hw0 hw1 K
    (spectatorBlocks width face) hnd (spectatorBlocks_lt width face) q f hq hf
    (plaquette_spectator_independent width face)
  change channelSum (productChannels (N width) w K (spectatorBlocks width face))
    (fun c => H width (polyMul
      (polyMul (channelSource (spectatorBlocks width face) q c)
        (channelSource (spectatorBlocks width face) q c))
      (polyMul f f))) ≤
      H width (polyMul (polyMul q q) (polyMul f f))
  simpa only [channelSource] using h

private theorem channelYoungCost_collected (width : Nat) (face : Z4Plaq)
    (w : Q') (K : Nat) (q : RatPoly) :
    channelYoungCost width face w K q ≈
      ((1 : Q')-qpow w 32) *
        channelSum (productChannels (N width) w K (spectatorBlocks width face))
          (fun c => rawSourceMass width
            (channelSource (spectatorBlocks width face) q c)) +
      ((1 : Q')+qpow w 32-(2 : Q')*qpow w 12) *
        channelSum (productChannels (N width) w K (spectatorBlocks width face))
          (fun c => rawSourceSquare width face
            (channelSource (spectatorBlocks width face) q c)) := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => channelSource (spectatorBlocks width face) q c
  let beta : Q' := 1-qpow w 32
  let alpha : Q' := 1+qpow w 32-2*qpow w 12
  change channelSum cs (fun c => plaquetteChannelCost width face w (b c)) ≈
    beta*channelSum cs (fun c => rawSourceMass width (b c)) +
      alpha*channelSum cs (fun c => rawSourceSquare width face (b c))
  have hcol : channelSum cs (fun c => plaquetteChannelCost width face w (b c)) ≈
      channelSum cs (fun c =>
        beta*rawSourceMass width (b c) + alpha*rawSourceSquare width face (b c)) :=
    channelSum_congr _ _ cs (fun c _ =>
      plaquetteChannelCost_collected w width face (b c.2))
  have hadd := channelSum_add
    (fun c => beta*rawSourceMass width (b c))
    (fun c => alpha*rawSourceSquare width face (b c)) cs
  have hmass := channelSum_scale beta (fun c => rawSourceMass width (b c)) cs
  have hsquare := channelSum_scale alpha
    (fun c => rawSourceSquare width face (b c)) cs
  exact Q'.eqv_trans _ _ _ hcol
    (Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr' hmass hsquare))

private theorem channelYoungCost_curvature (width : Nat) (face : Z4Plaq)
    (w : Q') (K : Nat) (q : RatPoly) :
    channelYoungCost width face w K q ≈
      ((5 : Q')+ -(8*qpow w 12)+3*qpow w 32) *
        channelSum (productChannels (N width) w K (spectatorBlocks width face))
          (fun c => rawSourceMass width
            (channelSource (spectatorBlocks width face) q c)) +
      (-((1 : Q')+qpow w 32-2*qpow w 12)) *
        channelGeometricCost width face w K q := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => channelSource (spectatorBlocks width face) q c
  let gamma : Q' := 5+ -(8*qpow w 12)+3*qpow w 32
  let alpha : Q' := 1+qpow w 32-2*qpow w 12
  have hpoint (c : RatPoly) : plaquetteChannelCost width face w c ≈
      gamma*rawSourceMass width c + (-alpha)*geometricSourceCost width face c := by
    let A := rawSourceMass width c
    let F := rawSourceSquare width face c
    have hcol := plaquetteChannelCost_collected w width face c
    have hring : ((1 : Q')-qpow w 32)*A + alpha*F ≈
        gamma*A + (-alpha)*(4*A+-F) :=
      poly_identity_of_normal_eq
        (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
          (.mul (.add (.add (.const 1) (.var 1))
            (.neg (.mul (.const 2) (.var 0)))) (.var 3)))
        (.add
          (.mul (.add (.add (.const 5) (.neg (.mul (.const 8) (.var 0))))
            (.mul (.const 3) (.var 1))) (.var 2))
          (.mul (.neg (.add (.add (.const 1) (.var 1))
            (.neg (.mul (.const 2) (.var 0)))))
            (.add (.mul (.const 4) (.var 2)) (.neg (.var 3)))))
        (by decide) (fun | 0 => qpow w 12 | 1 => qpow w 32
                         | 2 => A | _ => F)
    exact Q'.eqv_trans _ _ _ hcol hring
  change channelSum cs (fun c => plaquetteChannelCost width face w (b c)) ≈
    gamma*channelSum cs (fun c => rawSourceMass width (b c)) +
      (-alpha)*channelSum cs (fun c => geometricSourceCost width face (b c))
  have hcol : channelSum cs (fun c => plaquetteChannelCost width face w (b c)) ≈
      channelSum cs (fun c => gamma*rawSourceMass width (b c) +
        (-alpha)*geometricSourceCost width face (b c)) :=
    channelSum_congr _ _ cs (fun c _ => hpoint (b c.2))
  have hadd := channelSum_add
    (fun c => gamma*rawSourceMass width (b c))
    (fun c => (-alpha)*geometricSourceCost width face (b c)) cs
  have hmass := channelSum_scale gamma (fun c => rawSourceMass width (b c)) cs
  have hgeom := channelSum_scale (-alpha)
    (fun c => geometricSourceCost width face (b c)) cs
  exact Q'.eqv_trans _ _ _ hcol
    (Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr' hmass hgeom))

/-- Retaining all spectator heat channels cannot increase the exact literal
plaquette Young cost.  No positivity of an individual signed channel source
and no interacting-variance comparison is used. -/
theorem channelYoungCost_le_raw (width : Nat) (face : Z4Plaq) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    channelYoungCost width face w K q ≤ plaquetteChannelCost width face w q := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => channelSource (spectatorBlocks width face) q c
  let A := rawSourceMass width q
  let F := rawSourceSquare width face q
  let Ac := channelSum cs (fun c => rawSourceMass width (b c))
  let Fc := channelSum cs (fun c => rawSourceSquare width face (b c))
  let beta : Q' := 1-qpow w 32
  let alpha : Q' := 1+qpow w 32-2*qpow w 12
  have hA : Ac ≤ A := channelSourceMass_le_raw width face hw0 hw1 K q hq
  have hF : Fc ≤ F := channelSourceSquare_le_raw width face hw0 hw1 K q hq
  have hG : channelGeometricCost width face w K q ≤ geometricSourceCost width face q :=
    channelGeometricCost_le_raw width face hw0 hw1 K q hq
  have hb0 : (0 : Q') ≤ beta := Q'.sub_nonneg_of_le (qpow_le_one hw0 hw1 32)
  by_cases ha0 : (0 : Q') ≤ alpha
  · have hleft := channelYoungCost_collected width face w K q
    have hright := plaquetteChannelCost_collected w width face q
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add
          (Q'.mul_le_mul_of_nonneg_left _ _ beta hA hb0)
          (Q'.mul_le_mul_of_nonneg_left _ _ alpha hF ha0))
        (Q'.le_of_eqv hright.symm))
  · let gamma : Q' := 5+ -(8*qpow w 12)+3*qpow w 32
    have hg0 : (0 : Q') ≤ gamma :=
      (fundamental_curvature_bounds hw0 hw1).1
    have hna0 : (0 : Q') ≤ -alpha := by
      have hle : alpha ≤ (0 : Q') := Q'.le_of_not_le ha0
      simpa using Q'.neg_le_neg hle
    have hright : gamma*A+(-alpha)*geometricSourceCost width face q ≈
        plaquetteChannelCost width face w q := by
      have hcol := plaquetteChannelCost_collected w width face q
      have hring : gamma*A+(-alpha)*(4*A+-F) ≈ beta*A+alpha*F :=
        poly_identity_of_normal_eq
          (.add
            (.mul (.add (.add (.const 5) (.neg (.mul (.const 8) (.var 0))))
              (.mul (.const 3) (.var 1))) (.var 2))
            (.mul (.neg (.add (.add (.const 1) (.var 1))
              (.neg (.mul (.const 2) (.var 0)))))
              (.add (.mul (.const 4) (.var 2)) (.neg (.var 3)))))
          (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
            (.mul (.add (.add (.const 1) (.var 1))
              (.neg (.mul (.const 2) (.var 0)))) (.var 3)))
          (by decide) (fun | 0 => qpow w 12 | 1 => qpow w 32
                           | 2 => A | _ => F)
      exact Q'.eqv_trans _ _ _ hring hcol.symm
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (channelYoungCost_curvature width face w K q))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add
          (Q'.mul_le_mul_of_nonneg_left _ _ gamma hA hg0)
          (Q'.mul_le_mul_of_nonneg_left _ _ (-alpha) hG hna0))
        (Q'.le_of_eqv hright))

/-- The aggregate above is exactly the channel sum of the actual full-range
single-ended Young costs.  The sources have been spectator-integrated before
the costs are formed. -/
theorem channelYoungCost_pin (width : Nat) (face : Z4Plaq)
    (hface : face ∈ spatialFaces width) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := characterPolynomial (plaquette width face).scalar 1
    channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
      singleEndedCost (N width) w K (List.range (N width))
        (channelSource (spectatorBlocks width face) q c) f) ≈
      channelYoungCost width face w K q := by
  dsimp only
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  have hsource (c : GramChannel) (hc : c ∈ cs) :
      SupportedQuaternionBlocks (N width)
        (channelSource (spectatorBlocks width face) q c.2) := by
    unfold channelSource
    exact familyProject_supported _ (supported_polyMul hq
      (productChannels_supported (N width) w K (spectatorBlocks width face)
        (spectatorBlocks_lt width face) c hc))
  exact channelSum_congr _ _ cs (fun c hc =>
    plaquette_singleEndedCost width face hface w K hK _ (hsource c hc))

/-- Exact coefficient-one contraction of the spectator-integrated Young
cost against the original source, with no replacement normalization. -/
theorem channelSingleEndedCost_le_original (width : Nat) (face : Z4Plaq)
    (hface : face ∈ spatialFaces width) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (hK : 2 ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := characterPolynomial (plaquette width face).scalar 1
    channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
      singleEndedCost (N width) w K (List.range (N width))
        (channelSource (spectatorBlocks width face) q c) f) ≤
      singleEndedCost (N width) w K (List.range (N width)) q f := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (channelYoungCost_pin width face hface w K hK q hq))
    (Q'.le_trans' _ _ _ (channelYoungCost_le_raw width face hw0 hw1 K q hq)
      (Q'.le_of_eqv (plaquette_singleEndedCost width face hface w K hK q hq).symm))

end YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison.channelSourceSquare_le_raw
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison.channelYoungCost_le_raw
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison.channelYoungCost_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison.channelSingleEndedCost_le_original
