/-
# Arbitrary-observable dual control by the ORIGINAL finite temporal energy

Let g=T^n1, a=Vg, and d_i be the actual last-step message with only kinetic
factor i erased. For a supported test r with P_i(a*r)=0, prove
  headFloor(w) * H[a*d_i*f*r]^2 <= energy(g,f) * H[a*d_i*r^2].
The observable f is arbitrary. Both full endpoint weights and every other
kinetic factor remain, and the RHS is energy(f), not energy(r) or energy(Af).
The actual terminalResidual supplies such tests without any new hypothesis.

The reference here is a*d_i, NOT the actual odd marginal a*Tg. Passing to
that marginal requires the constructive independent reciprocal approximation
and the one-factor cap. A collective spatial/cross-energy budget also remains
open. This finite dual estimate is not a completed or continuum gap.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity
import YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity energy energy_identity)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage (conditionalMessage)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks kineticWeight

/-- The actual erased marginal; neither V nor the previous message is omitted. -/
def erasedPair (w : Q') (K width n i : Nat) (f r : RatPoly) : Q' :=
  quaternionHaar (N width)
    (polyMul
      (polyMul (polyMul (spatialWeight w K width) (terminalMessage w K width n))
        (conditionalMessage w K width n i))
      (polyMul f r))

private theorem selected_edge (w : Q') (K width i : Nat) (hi : i ∈ activeBlocks width) (g : RatPoly) :
    RatPolyCoeffEqv
      (edgeWeight (N width) w K (i::eraseIndex i (activeBlocks width)) (polyMul (spatialWeight w K width) g))
      (edgeDensity w K width g) := by
  unfold edgeWeight edgeDensity
  rw [kineticWeight_eq_indexedProduct]
  exact ((polynomialProduct_perm _ (select_perm i hi)).symm.mul_right _).mul_right _

/-- A one-factor estimate for arbitrary f in the SAME original temporal
energy. Only the dual test has the explicitly stated a-weighted centering. -/
theorem terminal_dual_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i ∈ activeBlocks width) {f r : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hr : SupportedQuaternionBlocks (N width) r)
    (hc : RatPolyCoeffEqv
      (project i (polyMul (polyMul (spatialWeight w K width) (terminalMessage w K width n)) r)) polyZero) :
    headFloor w * (erasedPair w K width n i f r * erasedPair w K width n i f r) ≤
      energy w K width (terminalMessage w K width n) f * erasedPair w K width n i r r := by
  let g := terminalMessage w K width n
  let a := polyMul (spatialWeight w K width) g
  let ids := eraseIndex i (activeBlocks width)
  have ha := supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)
  let A := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)
  have h := one_factor_dual_bound (N width) hw0 hw1 K hK i ids
    (activeBlocks_lt width i hi) (not_mem_erase i (activeBlocks_nodup width))
    (fun j hj => activeBlocks_lt width j (mem_of_mem_erase i hj)) ha hf hr A hc
  have hj : weightedPair (N width+N width) (edgeWeight (N width) w K (i::ids) a)
      (jump (N width) f) (jump (N width) f) ≈
      (2 : Q')*energy w K width g f :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((selected_edge w K width i hi g).mul_left _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_symm (energy_identity w K width (terminalMessage_supported w K width n) hf)))
  have he := Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hj))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ he (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))))
    (show (0 : Q') < (2 : Q') by decide)

/-- Concrete terminal residuals inhabit the dual-test sector; no new
centering field is required. The observable whose energy is bounded stays f. -/
theorem terminalResidual_dual_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i ∈ activeBlocks width) {f s : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hs : SupportedQuaternionBlocks (N width) s) :
    let r := terminalResidual w K width n i s
    headFloor w * (erasedPair w K width n i f r * erasedPair w K width n i f r) ≤
      energy w K width (terminalMessage w K width n) f * erasedPair w K width n i r r :=
  terminal_dual_energy hw0 hw1 K width hK n i hi hf
    (terminalResidual_supported w K width n i hs) (project_weightedResidual_zero i _ s)

end YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet.erasedPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet.terminal_dual_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet.terminalResidual_dual_energy
