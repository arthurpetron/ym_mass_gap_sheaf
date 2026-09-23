/-
# The retained inactive-projection residual of the actual hybrid sweep

Final ordered-head integration is an orthogonal Haar projection. Its square
norm equals the doubled-carrier sweep square norm minus the square norm of
the explicit residual. In particular, the residual is not discarded when
passing from a sweep endpoint deficit to the actual hybrid-map deficit.

These are finite ordinary-Haar identities and a supported square certificate.
They do not estimate the residual by angular energy, supply exposed-link
certificates, bound signed cross terms, or assert an interacting/OS gap.
-/

import YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Exact head-projection Pythagoras, including zero heads and zero survivors.
Support is unnecessary for the identity; it is needed for square positivity. -/
theorem partialHaarHeads_square_decomposition (tail heads : Nat) (f : RatPoly) :
    quaternionHaar (tail+heads) (polyMul f f) ≈
      quaternionHaar tail (polyMul (partialHaarHeads heads f) (partialHaarHeads heads f)) +
        quaternionHaar (tail+heads)
          (polyMul (polyAdd f (polyNeg (liftBoundary heads (partialHaarHeads heads f))))
            (polyAdd f (polyNeg (liftBoundary heads (partialHaarHeads heads f))))) := by
  let a := partialHaarHeads heads f
  let p := liftBoundary heads a
  let q := polyAdd f (polyNeg p)
  have hpp : quaternionHaar (tail+heads) (polyMul p p) ≈
      quaternionHaar tail (polyMul a a) := by
    rw [show polyMul p p = liftBoundary heads (polyMul a a) from
      (lift_product heads a a).symm]
    exact haar_liftBoundary heads tail (polyMul a a)
  have hfp : quaternionHaar (tail+heads) (polyMul f p) ≈
      quaternionHaar tail (polyMul a a) := head_pairing tail heads f a
  have hc : quaternionHaar (tail+heads) (polyMul p q) ≈ 0 := by
    have he : RatPolyCoeffEqv (polyMul p q)
        (polyAdd (polyMul f p) (polyNeg (polyMul p p))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 1) (.var 1))))
        (by decide) (fun | 0 => f | _ => p)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hfp
            (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ hpp)))
          (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0)))
            (.const 0) (by decide) (fun _ => quaternionHaar tail (polyMul a a)))))
  have halg : RatPolyCoeffEqv (polyMul f f)
      (polyAdd (polyMul p p) (polyAdd (polyMul q q)
        (polyAdd (polyMul p q) (polyMul p q)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
          (.add
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1)))))))
      (by decide) (fun | 0 => f | _ => p)
  have hz : quaternionHaar (tail+heads) (polyAdd (polyMul p q) (polyMul p q)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc hc) (by decide : (0 : Q') + 0 ≈ 0))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff halg)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' hpp
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))))))

/-- The actual doubled-carrier sweep minus its lifted final Haar projection.
Every inactive lower coordinate remains in this residual. -/
def hybridInactiveResidual (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) : RatPoly :=
  polyAdd (hybridSweep n w K ids p) (polyNeg (liftBoundary n (hybridMap n w K ids p)))

theorem hybridInactiveResidual_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (n+n) p) :
    SupportedQuaternionBlocks (n+n) (hybridInactiveResidual n w K ids p) := by
  have hs := hybridSweep_supported n w K ids hids hp
  have ha := partialHaarHeads_supported n n _ hs
  have hl := lift_supported ha n
  apply supported_add hs
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hl s hs

/-- Computed positivity witness for the residual square on the SAME carrier. -/
def hybridInactiveResidual_squareCertificate (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (n+n) p) :
    Certificate (n+n)
      (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p)) :=
  .square _ (hybridInactiveResidual_supported n w K ids hids hp)

theorem hybridInactiveResidual_square_nonnegative (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (n+n) p) :
    (0 : Q') ≤ quaternionHaar (n+n)
      (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p)) :=
  Certificate.haar_nonnegative (hybridInactiveResidual_squareCertificate n w K ids hids hp)

/-- Exact sweep/map square comparison, with the inactive-projection square retained. -/
theorem hybridSweep_square_decomposition (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (p : RatPoly) :
    quaternionHaar (n+n) (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p)) ≈
      quaternionHaar n (polyMul (hybridMap n w K ids p) (hybridMap n w K ids p)) +
        quaternionHaar (n+n)
          (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p)) :=
  partialHaarHeads_square_decomposition n n (hybridSweep n w K ids p)

/-- Final Haar projection cannot increase the square norm. No nome/cutoff
condition or distinctness of the schedule is required. -/
theorem hybridMap_square_le_sweep (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (n+n) p) :
    quaternionHaar n (polyMul (hybridMap n w K ids p) (hybridMap n w K ids p)) ≤
      quaternionHaar (n+n) (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p)) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (hybridInactiveResidual_square_nonnegative n w K ids hids hp))
    (Q'.ge_of_eqv (hybridSweep_square_decomposition n w K ids p))

/-- The actual projected endpoint deficit includes the residual square with
a PLUS sign. An upper bound for the sweep deficit must still control it. -/
theorem hybridMap_endpoint_eq_sweep_endpoint_add_inactive_square
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) :
    quaternionHaar (n+n) (polyMul p p) -
        quaternionHaar n (polyMul (hybridMap n w K ids p) (hybridMap n w K ids p)) ≈
      (quaternionHaar (n+n) (polyMul p p) -
        quaternionHaar (n+n) (polyMul (hybridSweep n w K ids p) (hybridSweep n w K ids p))) +
        quaternionHaar (n+n)
          (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p)) := by
  have h := hybridSweep_square_decomposition n w K ids p
  apply Q'.eqv_symm
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ h)))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.add (.var 1) (.var 2)))) (.var 2))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => quaternionHaar (n+n) (polyMul p p)
           | 1 => quaternionHaar n (polyMul (hybridMap n w K ids p) (hybridMap n w K ids p))
           | _ => quaternionHaar (n+n)
             (polyMul (hybridInactiveResidual n w K ids p) (hybridInactiveResidual n w K ids p))))

end YMGap.Continuum.SU2QuaternionProductHeatHybridSweep

#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.partialHaarHeads_square_decomposition
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridInactiveResidual
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridInactiveResidual_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridInactiveResidual_squareCertificate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridInactiveResidual_square_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridSweep_square_decomposition
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_square_le_sweep
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHybridSweep.hybridMap_endpoint_eq_sweep_endpoint_add_inactive_square
