/-
# Floor-free angular smoothing of the ORIGINAL interacting transfer

The actual inactive coordinates are integrated from the COMPLETE spatial
source V*f before applying full-product smoothing.  This is an exact output
identity, not deletion of spatial factors.  The resulting RHS is the original
V-weighted transfer quadratic, and for a literal terminal successor it is
the SAME odd-window partition.  This does not bound the endpoint-source
observable energy by interacting variance or construct a scaling limit.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSmoothing
import YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyParentInj (range_nodup)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (labels_perm_range)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next oddMass)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2QuaternionProductHeatSmoothing
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n

attribute [local irreducible] baseLinks spatialWeight activeBlocks terminalMessage

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem fringe_active_cover (width : Nat) :
    (fringeBlocks width ++ activeBlocks width).Perm (List.range (N width)) :=
  List.perm_append_comm.trans (by simpa only [labels] using labels_perm_range width)

private theorem fringe_not_active (width i : Nat) (hi : i ∈ fringeBlocks width) :
    i ∉ activeBlocks width := ((fringeBlocks_mem_iff width i).mp hi).2

/-- Integrate the complete source on the ORIGINAL absent kinetic blocks.
No spatial factor is deleted, and the identity holds for all signed inputs. -/
theorem transferStep_projected_full_heat (w : Q') (K width : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedHaarEqv (N width) (transferStep w K width f)
      (productMap (N width) w K (List.range (N width))
        (familyProject (fringeBlocks width) (polyMul (spatialWeight w K width) f))) := by
  let a := polyMul (spatialWeight w K width) f
  let q := familyProject (fringeBlocks width) a
  have ha := supported_polyMul (spatialWeight_supported w K width) hf
  have hq := familyProject_supported (fringeBlocks width) ha
  have hc := fringe_active_cover width
  have hd := productMap_drop_independent_prefix (N width) w K (activeBlocks width)
    (fringeBlocks width) (hc.symm.nodup (range_nodup _))
    (fun i hi => List.mem_range.mp (hc.mem_iff.mp hi)) q hq
    (familyProject_independent (fringeBlocks width) a)
  have he : RatPolyCoeffEqv
      (productMap (N width) w K (fringeBlocks width++activeBlocks width) q)
      (productMap (N width) w K (List.range (N width)) q) :=
    partialHaarHeads_congr (N width) ((polynomialProduct_perm _ hc).mul_right q)
  intro test ht
  rw [transferStep_eq_productMap]
  exact Q'.eqv_trans _ _ _
    (productMap_family_input_pairing (N width) w K (activeBlocks width)
      (fringeBlocks width) (activeBlocks_lt width) (fringeBlocks_lt width)
      (fringe_not_active width) a test)
    (Q'.eqv_trans _ _ _ (hd test ht).symm (haar_of_coeff (he.mul_left test)))

private theorem angular_energy_congr (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (heq : SupportedHaarEqv n p q) :
    angularListSum n (List.range n) p ≈ angularListSum n (List.range n) q := by
  let C := activeCasimirPolynomial (List.range n)
  have hCp := activeCasimirPolynomial_supported (List.range n)
    (fun i hi => List.mem_range.mp hi) hp
  have hCq := activeCasimirPolynomial_supported (List.range n)
    (fun i hi => List.mem_range.mp hi) hq
  exact Q'.eqv_trans _ _ _ (haar_activeCasimir_self n _
      (fun i hi => List.mem_range.mp hi) p).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (heq (C p) hCp)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
          (Q'.eqv_trans _ _ _ (literalPair_symm n (List.range n)
            (fun i hi => List.mem_range.mp hi) p q)
            (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
              (Q'.eqv_trans _ _ _ (heq (C q) hCq)
                (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
                  (haar_activeCasimir_self n _ (fun i hi => List.mem_range.mp hi) q))))))))

/-- Extent-free smoothing of the actual interacting transfer output, paid by
its SAME original spatially weighted quadratic. EVERY cutoff is retained. -/
theorem transferStep_angular_smoothing {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K width : Nat)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f) :
    ((1 : Q')-w)*angularListSum (N width) (List.range (N width))
      (transferStep w K width f) ≤
      weightedMass w K width (polyMul f (transferStep w K width f)) := by
  let a := polyMul (spatialWeight w K width) f
  let q := familyProject (fringeBlocks width) a
  let Pq := productMap (N width) w K (List.range (N width)) q
  have ha := supported_polyMul (spatialWeight_supported w K width) hf
  have hq := familyProject_supported (fringeBlocks width) ha
  have hPq := productMap_supported (N width) w K (List.range (N width))
    (fun i hi => List.mem_range.mp hi) hq
  have he := angular_energy_congr (N width) _ Pq
    (transferStep_supported w K width hf) hPq
    (transferStep_projected_full_heat w K width f hf)
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hs := productMap_angular_smoothing (N width-1) hw0 hw1 K q (by rwa [hn])
  rw [hn] at hs
  have hquad : weightedMass w K width (polyMul f (transferStep w K width f)) ≈
      H (N width) (polyMul q Pq) :=
    Q'.eqv_trans _ _ _ (original_quadratic_pin w K width f)
      (productMap_inactive_to_full_pairing (N width) w K (activeBlocks width)
        (fringeBlocks width) (activeBlocks_lt width) (fringeBlocks_lt width)
        (fringe_not_active width) (fringe_active_cover width) a ha)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left ((1 : Q')-w) _ _ he))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hquad.symm))

/-- The literal terminal successor's complete angular energy is paid by the
SAME odd-window partition, with no depth, width, cutoff or heat-floor factor. -/
theorem terminalMessage_angular_smoothing {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K width n : Nat) :
    ((1 : Q')-w)*angularListSum (N width) (List.range (N width))
      (terminalMessage w K width (n+1)) ≤ oddMass w K width n := by
  have h := transferStep_angular_smoothing hw0 hw1 K width
    (terminalMessage w K width n) (terminalMessage_supported w K width n)
  rw [terminalMessage_next] at h
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (weightedMass_congr w K width
      (RatPolyCoeffEqv.mul_comm _ _)))

#print axioms transferStep_projected_full_heat
#print axioms transferStep_angular_smoothing
#print axioms terminalMessage_angular_smoothing

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing
