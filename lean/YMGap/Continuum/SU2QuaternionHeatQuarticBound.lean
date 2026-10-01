/-
# Quartic moment bound for the original same-source heat insertion

The complete finite character expansion is split into a guarded head and
a dimension-controlled tail. All spectator and endpoint-source factors
remain. The result is relative to the same heat mass, NOT to centered
variance, and the displayed nome guards are not a physical scaling law.
-/

import YMGap.Continuum.SU2QuaternionHeatQuarticMoment
import YMGap.Continuum.SU2HeatQuarticHeadComparison
import YMGap.Continuum.SU2HeatQuarticTailComparison

namespace YMGap.Continuum.SU2QuaternionHeatQuarticBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RGTransport (dimQ qpow qpow_nonneg)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionHeatFusionQuadratic (vacuum_le_prefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup
open YMGap.Continuum.SU2HeatQuarticBulkCoefficient (relativeBudget)
open YMGap.Continuum.SU2HeatQuarticHeadComparison
open YMGap.Continuum.SU2HeatQuarticTailComparison
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion (defect)
open YMGap.Continuum.SU2QuaternionHeatQuarticMoment

local infix:50 " ≈ " => Q'.eqv

/-- Explicit finite head plus tail budget; no opaque parameter dependence. -/
def quarticBudget (w : Q') (S : Nat) : Q' :=
  relativeBudget (Q'.ofNat (S+2)) (1 + -w) +
    80 * Q'.ofNat (S^3) * qpow w (S*S)

/-- Signed response bound with both head and cutoff edge retained. The
dimension cap is used only AFTER the signed head has been controlled. -/
theorem response_bound {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (S K : Nat) (hS : 1 ≤ S) (hK : S+3 ≤ K)
    (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide))
    (Gamma : Nat → Q') (J : Q')
    (hGamma0 : ∀ j, (0 : Q') ≤ Gamma j)
    (hGammaCap : ∀ j, Gamma j ≤ dimQ j * J)
    (hJ : (0 : Q') ≤ J)
    (hJmass : J ≤ finSum (fun j => coeffW w j * Gamma j) (K+1)) :
    finSum (fun j => quarticCoeff (cutCoeff w K) j * Gamma j) (K+3) ≤
      quarticBudget w S * finSum (fun j => coeffW w j * Gamma j) (K+1) := by
  let L := S+2
  let N := K+3-L
  let f := fun j => quarticCoeff (cutCoeff w K) j * Gamma j
  let I := finSum (fun j => coeffW w j * Gamma j) (K+1)
  let E := 80 * Q'.ofNat (S^3) * qpow w (S*S)
  have he : L+N = K+3 := by dsimp [L,N]; omega
  have hsplit := FiveHolonomyPerronCutoff.finSum_split f L N
  rw [he] at hsplit
  have hhead := head_response_bound hw0 hw1 L K (by dsimp [L]; omega)
    (by dsimp [L]; omega) hhalf Gamma hGamma0
  have ht := high_response_tail_bound hw0 hw1 S K N hS hq Gamma J
    hGamma0 hGammaCap hJ
  have hindices : finSum (fun t => f (L+t)) N ≈
      finSum (fun t => quarticCoeff (cutCoeff w K) (S+t+2) * Gamma (S+t+2)) N :=
    finSum_eqv_congr _ _ (fun t => by
      have hi : L+t = S+t+2 := by dsimp [L]; omega
      dsimp [f]; rw [hi]; exact Q'.eqv_refl _) N
  have hE : (0 : Q') ≤ E := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) (Q'.ofNat_nonneg _)) (qpow_nonneg w hw0 _)
  have htail : finSum (fun t => f (L+t)) N ≤ E * I :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hindices)
      (Q'.le_trans' _ _ _ ht (Q'.mul_le_mul_of_nonneg_left _ _ E hJmass hE))
  have hend : relativeBudget (Q'.ofNat L) (1 + -w)*I + E*I ≈ quarticBudget w S*I :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (.mul (.add (.var 0) (.var 1)) (.var 2)) (by decide)
      (fun | 0 => relativeBudget (Q'.ofNat L) (1 + -w) | 1 => E | _ => I)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ (Q'.add_le_add hhead htail) (Q'.le_of_eqv hend))

/-- The actual complete finite quartic insertion is bounded by the SAME
heat mass. Source, spectator, cutoff, nome and spin split are all explicit.
The full pointwise background certificate is stronger than PSD alone. -/
theorem prefix_quartic_bound {n i : Nat} (hi : i < n) {W a : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a)
    (R : Certificate (n+n) (polyMul W (polyMul a (liftBoundary n a))))
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (S K : Nat) (hS : 1 ≤ S) (hK : S+3 ≤ K)
    (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide)) :
    insertion n W a
      (polyMul (polyMul (defect (scalarAt (n+i) i)) (defect (scalarAt (n+i) i)))
        (heatPrefix w K (scalarAt (n+i) i))) ≤
      quarticBudget w S * insertion n W a (heatPrefix w K (scalarAt (n+i) i)) := by
  let x := scalarAt (n+i) i
  let Gamma := response n W a x
  let J := haarQuadratic n W a
  have hGamma0 : ∀ j, (0 : Q') ≤ Gamma j :=
    character_insertion_nonnegative hi hW hpositive ha
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable (n+i))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable i))
  have hs : Supported (n+n) word :=
    (Supported.coordinate (by omega)).mul (Supported.coordinate (by omega)).conj
  have hu : HaarCarrierEqv (n+n) (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate (by omega))
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate (by omega)))
  have hcap : ∀ j, Gamma j ≤ dimQ j * J := fun j =>
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (character_weighted_haar_bound (SquareBound.scalar hs hu) R j)
  have hmass := prefix_value n W a x w K
  have hJmass : J ≤ finSum (fun j => coeffW w j * Gamma j) (K+1) :=
    Q'.le_trans' _ _ _ (vacuum_le_prefix hi hW hpositive ha hw0 K) (Q'.le_of_eqv hmass)
  have h := response_bound hw0 hw1 S K hS hK hhalf hq Gamma J hGamma0 hcap
    (hpositive a ha) hJmass
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (quartic_value_regrouped n W a x w K))
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hmass))))

#print axioms quarticBudget
#print axioms response_bound
#print axioms prefix_quartic_bound

end YMGap.Continuum.SU2QuaternionHeatQuarticBound
