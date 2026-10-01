/-
# Extent-free angular smoothing of the ORIGINAL full product heat

Use the actual computed degree paths, their concrete heat and Casimir
actions, and their proved nonnegative diagonal input pairings.  No joint
orthogonality premise, coefficient norm, positive heat floor, or number of
links enters the estimate.  The RHS is the original UNCENTERED Haar heat
pairing, not the interacting terminal variance or a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionCyclicPathHeatEigen
import YMGap.Continuum.SU2HeatProductCasimirSmoothing

namespace YMGap.Continuum.SU2QuaternionProductHeatSmoothing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.SU2QuaternionCyclicPathHeatEigen
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductCasimirSmoothing
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sum_le (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≤ g d) → qListSum (ids.map f) ≤ qListSum (ids.map g)
  | [], _ => Q'.le_refl' _
  | d::ds, h => Q'.add_le_add (h d List.mem_cons_self)
      (sum_le f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

/-- Ordered summation over precisely the original ragged path tree. -/
theorem leafSum_pairing_le (tail : Nat) :
    ∀ (m : Nat) (p leftTest rightTest : RatPoly)
      (leftWeight rightWeight : List Nat → Q'),
    (∀ ds, ds.length = m → ValidPath tail p ds →
      leftWeight ds * H (tail+1) (polyMul leftTest (pathPiece tail p ds)) ≤
      rightWeight ds * H (tail+1) (polyMul rightTest (pathPiece tail p ds))) →
    leafSum tail m p leftTest leftWeight ≤ leafSum tail m p rightTest rightWeight
  | 0, _, _, _, _, _, h => h [] rfl True.intro
  | m+1, p, leftTest, rightTest, leftWeight, rightWeight, h =>
      sum_le _ _ (branchDegrees tail p) (fun d hd =>
        leafSum_pairing_le tail m (nextPiece tail p d) leftTest rightTest
          (fun ds => leftWeight (d::ds)) (fun ds => rightWeight (d::ds))
          (fun ds hlen hpath => h (d::ds)
            (by simp only [List.length_cons, hlen]) ⟨hd, hpath⟩))

private theorem path_output_pairing (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
    H (tail+1) (polyMul
      (productMap (tail+1) w K (List.range (tail+1)) p) (pathPiece tail p ds)) ≈
      productAttenuation w K ds * H (tail+1) (polyMul p (pathPiece tail p ds)) := by
  have hs := path_supported tail ds p hp
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _
      (kineticPair_symm (tail+1) w K (List.range (tail+1))
        (fun i hi => List.mem_range.mp hi) (pathPiece tail p ds) p hs hp)
      (full_path_heat_pairing tail w K p hp ds hlen hpath p hp))

/-- Exact original output Casimir energy, with squared actual attenuation
and nonnegative full-path input masses. No spectral decomposition is assumed. -/
theorem productMap_casimir_grouped (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    H (tail+1) (polyMul (productMap (tail+1) w K (List.range (tail+1)) p)
      (activeCasimirPolynomial (List.range (tail+1))
        (productMap (tail+1) w K (List.range (tail+1)) p))) ≈
      leafSum tail (tail+1) p p (fun ds =>
        totalCasimir ds * (productAttenuation w K ds*productAttenuation w K ds)) := by
  let Pp := productMap (tail+1) w K (List.range (tail+1)) p
  let CPp := activeCasimirPolynomial (List.range (tail+1)) Pp
  have hsum : H (tail+1) (polyMul Pp CPp) ≈
      leafSum tail (tail+1) p CPp (productAttenuation w K) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (productMap_modeFold tail w K p hp CPp)
        (leafSum_modeFold tail (tail+1) p CPp _))
  apply Q'.eqv_trans _ _ _ hsum
  apply leafSum_pairing_congr
  intro ds hlen hpath
  let a := productAttenuation w K ds
  let c := totalCasimir ds
  let leaf := pathPiece tail p ds
  have hcas : H (tail+1) (polyMul CPp leaf) ≈ c*H (tail+1) (polyMul Pp leaf) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (literalPair_symm (tail+1) (List.range (tail+1))
          (fun i hi => List.mem_range.mp hi) Pp leaf)
        (Q'.eqv_trans _ _ _
          (full_path_activeCasimir_carrier tail p hp ds hlen hpath Pp)
          (quaternionHaar_polyMul_smul_right (tail+1) c Pp leaf)))
  have hpair := path_output_pairing tail w K p hp ds hlen hpath
  have hterm : H (tail+1) (polyMul CPp leaf) ≈
      c*(a*H (tail+1) (polyMul p leaf)) :=
    Q'.eqv_trans _ _ _ hcas (Q'.mul_eqv_congr_left _ _ _ hpair)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ hterm)
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 0) (.var 2))))
      (.mul (.mul (.var 1) (.mul (.var 0) (.var 0))) (.var 2))
      (by decide) (fun | 0 => a | 1 => c | _ => H (tail+1) (polyMul p leaf)))

/-- Full original product heat pays its COMPLETE output angular energy
without a lattice-size factor, heat floor, or cutoff-largeness guard. -/
theorem productMap_angular_smoothing (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    ((1 : Q')-w) * angularListSum (tail+1) (List.range (tail+1))
      (productMap (tail+1) w K (List.range (tail+1)) p) ≤
      H (tail+1) (polyMul p (productMap (tail+1) w K (List.range (tail+1)) p)) := by
  let h := (1 : Q')-w
  let weight := fun ds => totalCasimir ds *
    (productAttenuation w K ds*productAttenuation w K ds)
  have henergy := Q'.eqv_trans _ _ _
    (haar_activeCasimir_self (tail+1) (List.range (tail+1))
      (fun i hi => List.mem_range.mp hi)
      (productMap (tail+1) w K (List.range (tail+1)) p)).symm
    (productMap_casimir_grouped tail w K p hp)
  have hscaled := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left h _ _ henergy)
    (leafSum_smul tail (tail+1) p p h weight).symm
  have hle : leafSum tail (tail+1) p p (fun ds => h*weight ds) ≤
      leafSum tail (tail+1) p p (productAttenuation w K) := by
    apply leafSum_pairing_le
    intro ds hlen hpath
    have hscalar := product_squared_casimir_smoothing hw0 hw1 K ds
    have hreassoc : h*weight ds ≈
        (h*totalCasimir ds)*(productAttenuation w K ds*productAttenuation w K ds) :=
      (Q'.mul_assoc_eqv _ _ _).symm
    have hweight := Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) hscalar
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hweight
      (full_path_pairing_nonnegative tail p hp ds hlen hpath)
  have hpair : H (tail+1)
      (polyMul p (productMap (tail+1) w K (List.range (tail+1)) p)) ≈
      leafSum tail (tail+1) p p (productAttenuation w K) :=
    Q'.eqv_trans _ _ _ (productMap_modeFold tail w K p hp p)
      (leafSum_modeFold tail (tail+1) p p _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled)
    (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv hpair.symm))

#print axioms leafSum_pairing_le
#print axioms productMap_casimir_grouped
#print axioms productMap_angular_smoothing

end YMGap.Continuum.SU2QuaternionProductHeatSmoothing
