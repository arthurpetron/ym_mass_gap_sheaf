/-
# Selected heat-nome comparison in the ORIGINAL slab edge

Only one active kinetic factor is changed. Both complete spatial/terminal
sources and every spectator heat factor remain at the original nome.
The changed-nome and erased-link masses are at most the SAME odd partition.
Absolute constant kernel errors therefore need no inverse heat minimum.

The affine consumer still needs its explicit positive-polynomial kernel
certificate. No quartic shape estimate, relative variance or scaling theorem
is supplied here, and the altered factor is not a new Yang--Mills theory.
-/

import YMGap.Continuum.SU2QuaternionHeatNomeComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (edgeWeight eraseIndex select_perm mem_of_mem_erase heatAt_eq_prefix)
open YMGap.Continuum.SU2QuaternionHeatFusionQuadratic (vacuum_le_prefix)
open YMGap.Continuum.SU2QuaternionHeatNomeComparison
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage oddMass

private def spectators (w : Q') (K width i : Nat) : RatPoly :=
  productHeat (N width) w K (eraseIndex i (activeBlocks width))

private def originalSource (w : Q') (K width depth : Nat) : RatPoly :=
  endpointSource w K width (terminalMessage w K width depth)

private theorem source_supported (w : Q') (K width depth : Nat) :
    SupportedQuaternionBlocks (N width) (originalSource w K width depth) :=
  supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width depth)

private theorem rest_lt (width i : Nat) :
    ∀ j, j ∈ eraseIndex i (activeBlocks width) → j < N width :=
  fun j hj => activeBlocks_lt width j (mem_of_mem_erase i hj)

/-- An arbitrary selected insertion in the literal unchanged spectator and
complete endpoint-source quadratic. -/
def selectedInsertion (w : Q') (K width depth i : Nat) (p : RatPoly) : Q' :=
  insertion (N width) (spectators w K width i) (originalSource w K width depth) p

/-- Only the selected kinetic factor has nome u. Source and spectators still
have nome w. At u=w this is exactly the original odd partition. -/
def selectedMass (w u : Q') (K width depth i : Nat) : Q' :=
  selectedInsertion w K width depth i (heatPrefix u K (scalarAt (N width+i) i))

theorem selectedMass_pin (w : Q') (K width depth i : Nat) (hi : i ∈ activeBlocks width) :
    selectedMass w w K width depth i ≈ oddMass w K width depth := by
  let a := originalSource w K width depth
  let W := spectators w K width i
  let H := heatPrefix w K (scalarAt (N width+i) i)
  have hprod : RatPolyCoeffEqv (productHeat (N width) w K (activeBlocks width)) (polyMul H W) := by
    have hp := polynomialProduct_perm (fun j => heatAt j (N width+j) w K) (select_perm i hi)
    have hh := (heatAt_symm i (N width+i) w K).mul_right W
    rw [heatAt_eq_prefix (N width+i) i w K] at hh
    exact hp.trans hh
  have hedge : RatPolyCoeffEqv (edgeWeight (N width) w K (activeBlocks width) a)
      (polyMul (polyMul W (polyMul a (liftBoundary (N width) a))) H) :=
    ((hprod.mul_right a).mul_right (liftBoundary (N width) a)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 3))) (.var 0)) (by decide)
        (fun | 0 => H | 1 => W | 2 => a | _ => liftBoundary (N width) a))
  have hp : edgeWeight (N width) w K (activeBlocks width) a =
      edgeDensity w K width (terminalMessage w K width depth) := by
    unfold edgeWeight edgeDensity productHeat
    rw [kineticWeight_eq_indexedProduct]
    rfl
  rw [hp] at hedge
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hedge.symm) (edge_total_mass w K width depth)

/-- Exact original-source order, without a lower-cutoff or heat-minimum
guard. All coupling, cutoff, width and depth parameters remain explicit. -/
theorem selectedMass_le_original {u w : Q'} (hu : (0 : Q') ≤ u) (huw : u ≤ w)
    (K width depth i : Nat) (hi : i ∈ activeBlocks width) :
    selectedMass w u K width depth i ≤ oddMass w K width depth :=
  Q'.le_trans' _ _ _
    (prefix_nome_mono (activeBlocks_lt width i hi)
      (productHeat_supported (N width) w K _ (rest_lt width i))
      (productHeat_quadratic_nonnegative (N width) w (Q'.le_trans' _ _ _ hu huw) K _ (rest_lt width i))
      (source_supported w K width depth) hu huw K)
    (Q'.le_of_eqv (selectedMass_pin w K width depth i hi))

/-- The constant error left after a pointwise kernel approximation is paid
by the SAME original partition, not by a reciprocal heat floor. -/
theorem constant_error_le_original {w e : Q'} (hw : (0 : Q') ≤ w) (he : (0 : Q') ≤ e)
    (K width depth i : Nat) (hi : i ∈ activeBlocks width) :
    selectedInsertion w K width depth i (cap e) ≤ e * oddMass w K width depth :=
  Q'.le_trans' _ _ _
    (constant_error_le (activeBlocks_lt width i hi)
      (productHeat_supported (N width) w K _ (rest_lt width i))
      (productHeat_quadratic_nonnegative (N width) w hw K _ (rest_lt width i))
      (source_supported w K width depth) hw he K)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (selectedMass_pin w K width depth i hi)))

/-- Affine kernel domination with the actual certified original sources.
The supplied shape certificate is still a substantive hypothesis; in
particular no quartic heat-widening bound is manufactured by this consumer. -/
theorem affine_original_bound {u w c e : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hu : (0 : Q') ≤ u) (huw : u ≤ w) (hc : (0 : Q') ≤ c) (he : (0 : Q') ≤ e)
    (K width depth i : Nat) (hK : headCutoff w ≤ K) (hi : i ∈ activeBlocks width)
    (p : RatPoly)
    (S : Certificate (N width+N width) (polyAdd
      (polyAdd (polySmul c (heatPrefix u K (scalarAt (N width+i) i))) (cap e)) (polyNeg p))) :
    selectedInsertion w K width depth i p ≤ (c+e) * oddMass w K width depth := by
  let a := originalSource w K width depth
  have ha := source_supported w K width depth
  let A : Certificate (N width) a :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK depth)
  have R : Certificate (N width+N width)
      (polyMul (spectators w K width i) (polyMul a (liftBoundary (N width) a))) :=
    (productHeatCertificate (N width) hw0 hw1 K hK _ (rest_lt width i)).mul
      ((certificate_extend (N width) ha A).mul (lift_certificate (N width) A))
  exact Q'.le_trans' _ _ _
    (affine_prefix_bound (activeBlocks_lt width i hi)
      (productHeat_supported (N width) w K _ (rest_lt width i))
      (productHeat_quadratic_nonnegative (N width) w (Q'.le_of_lt hw0) K _ (rest_lt width i))
      ha R hu huw hc he K S)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (selectedMass_pin w K width depth i hi)))

#print axioms selectedMass_pin
#print axioms selectedMass_le_original
#print axioms constant_error_le_original
#print axioms affine_original_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison
