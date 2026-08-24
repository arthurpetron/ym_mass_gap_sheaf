/-
# The global-floor off-ray residual ratios are not cofinal

Both scalar off-ray residual compilers replace every local positive-kernel
edge by the single minimum positive entry of the complete finite vacuum
sector.  Their costs are padded by one.  Hence either cofinal ratio would
already force the fixed positive spin-ray capacity `delta` below that global
edge minimum at every sufficiently large cutoff.

The all-spin vacuum spokes prove that the minimum times `K` is at most one.
An explicit denominator witness for the fixed positive rational therefore
contradicts either proposed cofinal scalar ratio.  This remains true even if
the carrier-size or endpoint-mass estimate in those scalar costs is improved:
the global edge minimum itself is the fatal loss.

This no-go result does not rule out the exact pointwise residual-flow
capacity, a weight-cancelled local comparison, a multiscale Poincare proof,
or a direct operator estimate.  No uniform full-sector gap, continuum theory,
or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The common global-minimum contradiction -/

private theorem impossible_of_delta_le_globalFloor
    {w delta : Q'} (hw : (0 : Q') < w) (hdelta : (0 : Q') < delta)
    (start : Nat)
    (hfloor : ∀ K, start ≤ K →
      delta ≤ centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K 0) : False := by
  let request := (delta.den + 1) * (delta.den + 1)
  let K := max start request
  have hstart : start ≤ K := Nat.le_max_left _ _
  have hrequest : request ≤ K := Nat.le_max_right _ _
  have hrequestQ : Q'.ofNat request ≤ Q'.ofNat K :=
    Q'.ofNat_le_ofNat hrequest
  have hscaledRequest :
      delta * Q'.ofNat request ≤ delta * Q'.ofNat K :=
    Q'.mul_le_mul_of_nonneg_left _ _ delta hrequestQ
      (Q'.le_of_lt hdelta)
  have hscaledFloor :
      delta * Q'.ofNat K ≤
        centralPhysicalFiniteVacuumSectorEdgeFloor
            w (Q'.le_of_lt hw) K 0 * Q'.ofNat K :=
    Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat K)
      (hfloor K hstart)
      (Q'.ofNat_le_ofNat (Nat.zero_le K))
  have hle : delta * Q'.ofNat request ≤ 1 :=
    Q'.le_trans' _ _ _ hscaledRequest
      (Q'.le_trans' _ _ _ hscaledFloor
        (centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_one hw K))
  have hlt : (1 : Q') < delta * Q'.ofNat request :=
    one_lt_mul_den_succ_square delta hdelta
  exact (Int.not_lt_of_ge hle) hlt

/-! ## 2. The exact endpoint-mass scalar ratio is impossible -/

namespace FixedNomeCofinalSpinCubeOffRayResidualLinearRatio

theorem delta_le_edgeFloor
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualLinearRatio
      hw rayCapacity)
    {K : Nat} (hK : rayCapacity.start ≤ K) :
    rayCapacity.delta ≤ centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K 0 := by
  let cost := centralLowerExcitedSpinCubeOffRayResidualLinearCost
    w (Q'.le_of_lt hw) K
  have hcostOne : (1 : Q') ≤ cost := by
    unfold cost centralLowerExcitedSpinCubeOffRayResidualLinearCost
    exact Q'.add_le_self_of_nonneg 1 _
      (Q'.mul_nonneg _ _
        (Q'.ofNat_le_ofNat (Nat.zero_le _))
        (centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_nonnegative
          w (Q'.le_of_lt hw) K))
  have hdeltaCost : rayCapacity.delta * 1 ≤
      rayCapacity.delta * cost :=
    Q'.mul_le_mul_of_nonneg_left _ _ rayCapacity.delta hcostOne
      (Q'.le_of_lt rayCapacity.delta_pos)
  have hratio := (family.ratio K hK).ratio_bound
  unfold centralLowerExcitedSpinCubeSharedCoercivityFloor at hratio
  have hhalfRatio :
      HalfPow.half * (rayCapacity.delta * cost) ≤
        HalfPow.half * centralPhysicalFiniteVacuumSectorEdgeFloor
          w (Q'.le_of_lt hw) K 0 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv HalfPow.half rayCapacity.delta cost)))
      hratio
  have hratioCanceled : rayCapacity.delta * cost ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K 0 :=
    Q'.le_of_mul_le_mul_left hhalfRatio
      (by decide : (0 : Q') < HalfPow.half)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv rayCapacity.delta)))
      hdeltaCost)
    hratioCanceled

theorem impossible
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualLinearRatio
      hw rayCapacity) : False := by
  exact impossible_of_delta_le_globalFloor hw rayCapacity.delta_pos
    rayCapacity.start
    (fun _K hK => delta_le_edgeFloor family hK)

end FixedNomeCofinalSpinCubeOffRayResidualLinearRatio

theorem no_fixedNomeCofinalSpinCubeOffRayResidualLinearRatio
    {w : Q'} {hw : (0 : Q') < w}
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) :
    Not (Nonempty
      (FixedNomeCofinalSpinCubeOffRayResidualLinearRatio
        hw rayCapacity)) := by
  intro hfamily
  rcases hfamily with ⟨family⟩
  exact FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.impossible family

/-! ## 3. Even the mass-free carrier-linear scalar ratio is impossible -/

namespace FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio

theorem delta_le_edgeFloor
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
      hw rayCapacity)
    {K : Nat} (hK : rayCapacity.start ≤ K) :
    rayCapacity.delta ≤ centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K 0 := by
  let cost := centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
    w (Q'.le_of_lt hw) K
  have hcostOne : (1 : Q') ≤ cost := by
    unfold cost centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
    exact Q'.add_le_self_of_nonneg 1 _
      (Q'.ofNat_le_ofNat (Nat.zero_le _))
  have hdeltaCost : rayCapacity.delta * 1 ≤
      rayCapacity.delta * cost :=
    Q'.mul_le_mul_of_nonneg_left _ _ rayCapacity.delta hcostOne
      (Q'.le_of_lt rayCapacity.delta_pos)
  have hratio := (family.ratio K hK).ratio_bound
  unfold centralLowerExcitedSpinCubeSharedCoercivityFloor at hratio
  have hhalfRatio :
      HalfPow.half * (rayCapacity.delta * cost) ≤
        HalfPow.half * centralPhysicalFiniteVacuumSectorEdgeFloor
          w (Q'.le_of_lt hw) K 0 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv HalfPow.half rayCapacity.delta cost)))
      hratio
  have hratioCanceled : rayCapacity.delta * cost ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K 0 :=
    Q'.le_of_mul_le_mul_left hhalfRatio
      (by decide : (0 : Q') < HalfPow.half)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv rayCapacity.delta)))
      hdeltaCost)
    hratioCanceled

theorem impossible
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
      hw rayCapacity) : False := by
  exact impossible_of_delta_le_globalFloor hw rayCapacity.delta_pos
    rayCapacity.start
    (fun _K hK => delta_le_edgeFloor family hK)

end FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio

theorem no_fixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
    {w : Q'} {hw : (0 : Q') < w}
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) :
    Not (Nonempty
      (FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
        hw rayCapacity)) := by
  intro hfamily
  rcases hfamily with ⟨family⟩
  exact
    FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.impossible
      family

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo.FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.delta_le_edgeFloor
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo.FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.impossible
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo.no_fixedNomeCofinalSpinCubeOffRayResidualLinearRatio
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo.FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.delta_le_edgeFloor
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo.FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.impossible
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo.no_fixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
