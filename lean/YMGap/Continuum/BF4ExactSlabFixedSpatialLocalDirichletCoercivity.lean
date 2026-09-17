/-
# Local coercivity in the SAME original temporal marginal

For a genuine active link i, conditional centering of (V*g)*f kills the
mixed term after deleting exactly that link's kinetic heat factor. The
one-factor floor and cap give
  headFloor(w) * m(g*Tg*f^2) <= prefixCap(w) * energy(g,f).
The constants depend on nome, but not width, boundary depth or late cutoff.
Every other kinetic factor and both full V*g endpoint weights are retained.

The actual terminal residual is constructed without division:
  R_i = P_i(V*T^n1)*f - P_i(V*T^n1*f).
Its weighted conditional centering is proved, not assumed.

OPEN: a stable decomposition/cross-energy estimate for arbitrary observables
under the original odd-chain marginal. These residuals need not be centered
in that marginal or mutually orthogonal, and change with cutoff and depth.
No transfer-invariance of a conditional sector is asserted.
No global vacuum-complement, completed OS, spacing or continuum gap follows
from this local-sector theorem alone.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
import YMGap.Continuum.SU2QuaternionWeightedBlockCentering

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

private theorem edge_eq (w : Q') (K width : Nat) (g : RatPoly) :
    edgeDensity w K width g =
      edgeWeight (N width) w K (activeBlocks width) (polyMul (spatialWeight w K width) g) := by
  unfold edgeDensity edgeWeight
  rw [kineticWeight_eq_indexedProduct]
  rfl

private theorem twice_reorder (a b : Q') : (2 : Q')*(a*b) ≈ a*((2 : Q')*b) :=
  poly_identity_of_normal_eq (.mul (.const 2) (.mul (.var 0) (.var 1)))
    (.mul (.var 0) (.mul (.const 2) (.var 1))) (by decide)
    (fun | 0 => a | _ => b)

/-- Coercivity on a stated weighted conditional sector, in the ORIGINAL
temporal marginal, with a single heat-factor comparison and no volume power. -/
theorem local_sector_coercivity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (i : Nat) (hi : i ∈ activeBlocks width) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g)
    (hc : RatPolyCoeffEqv
      (project i (polyMul (polyMul (spatialWeight w K width) g) f)) polyZero) :
    headFloor w * weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) (polyMul f f)) ≤
      prefixCap w * energy w K width g f := by
  have ha := supported_polyMul (spatialWeight_supported w K width) hg
  let A := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul G
  have hb := local_energy_floor_of_mem (N width) hw0 hw1 K hK
    i (activeBlocks width) (activeBlocks_nodup width) hi (activeBlocks_lt width) ha hf A hc
  rw [← edge_eq w K width g] at hb
  have hd := edge_diagonal_identity w K width hg hf
  have he := energy_identity w K width hg hf
  have hl := Q'.eqv_trans _ _ _ (twice_reorder (headFloor w) _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hd))
  have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (prefixCap w) _ _ (Q'.eqv_symm he))
    (Q'.eqv_symm (twice_reorder (prefixCap w) _))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hl) (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hr)))
    (show (0 : Q') < (2 : Q') by decide)

/-- An explicit polynomial residual for the ACTUAL finite terminal weight.
This is a scaled residual, not an asserted conditional projection. -/
def terminalResidual (w : Q') (K width n i : Nat) (f : RatPoly) : RatPoly :=
  weightedResidual i (polyMul (spatialWeight w K width) (terminalMessage w K width n)) f

theorem terminalResidual_supported (w : Q') (K width n i : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (terminalResidual w K width n i f) :=
  weightedResidual_supported i
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)) hf

/-- The actual terminal residual satisfies the local estimate with no new
centering or message-positivity hypothesis. Width, n and K do not enter the
one-factor constants; the residual itself retains their full dependence. -/
theorem terminalResidual_coercivity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i ∈ activeBlocks width) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let g := terminalMessage w K width n
    let r := terminalResidual w K width n i f
    headFloor w * weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) (polyMul r r)) ≤
      prefixCap w * energy w K width g r :=
  local_sector_coercivity hw0 hw1 K width hK i hi
    (terminalMessage_supported w K width n) (terminalResidual_supported w K width n i hf)
    (terminalMessage_certificate hw0 hw1 K width hK n)
    (project_weightedResidual_zero i _ f)

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity.local_sector_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity.terminalResidual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity.terminalResidual_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity.terminalResidual_coercivity
