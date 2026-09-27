/-
# A neighboring heat update does not preserve a free-centered sector

Use the ORIGINAL two-link relative heat packet h(y,x), with the positive
endpoint factor B(x)=1+x_0/2 retained. The input f=x_0*(y_0-2*w^3)
has zero free x-average AND zero mean under B*h. Its actual conditional
y-update has free x-average w^3/4>0, while its B-weighted mean stays zero.

Thus global centering does not repair the missing free-sector invariance
needed to iterate a directional local estimate. This is a two-site weighted
heat diagnostic, NOT an identification with full-slab conditional operators,
gauge-invariant Wilson probes, an OS gap, or a Yang--Mills counterexample.
Every heat spin through K is retained. Positivity is constructed for
0<w<1 and K>=headCutoff(w); transmission additionally needs K>=1.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (quaternionHaar_partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar (liftHead_mul)
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv

def endpoint : RatPoly := polyAdd polyOne (polySmul HalfPow.half (polyVar 0))
def source (w : Q') : RatPoly :=
  polyMul (polyAdd (polyVar 0) (polySmul (-(2*qpow w 3)) polyOne))
    (liftHead (polyVar 0))
def weight (w : Q') (K : Nat) : RatPoly :=
  polyMul (relativeHeat w K) (liftHead endpoint)
def output (w : Q') (K : Nat) : RatPoly := conditionalHeat w K (source w)

private theorem endpoint_supported : SupportedQuaternionBlocks 1 endpoint :=
  supported_add (supported_one 1)
    (polySmul_supported (coordinateInterval (by decide : 0 < 4*1)).support _)

theorem source_supported (w : Q') : SupportedQuaternionBlocks 2 (source w) :=
  supported_polyMul (supported_add (coordinateInterval (by decide : 0 < 4*2)).support
    (polySmul_supported (supported_one 2) _))
    (coordinateInterval (by decide : 4 < 4*2)).support

/-- The retained endpoint has a constructed floor one half. -/
def endpoint_floor : Certificate 1 (polyAdd endpoint (polyNeg (cap HalfPow.half))) := by
  apply Certificate.ofCoeff
    (q := polySmul HalfPow.half (polyAdd (cap 1) (polyVar 0)))
  · apply RatPolyCoeffEqv.of_canon_termwise
    decide +kernel
  · exact .smul HalfPow.half (by decide) (coordinateInterval (by decide : 0 < 4*1)).lower

private def endpoint_certificate : Certificate 1 endpoint := by
  apply Certificate.ofCoeff
    (q := polyAdd (polyAdd endpoint (polyNeg (cap HalfPow.half))) (cap HalfPow.half))
  · exact coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
      (fun | 0 => endpoint | _ => cap HalfPow.half)
  · exact endpoint_floor.add (.constant 1 HalfPow.half (by decide))

/-- The actual B*h weight is positive without a small-nome hypothesis. -/
def weight_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) : Certificate 2 (weight w K) :=
  (relativeHeat_certificate hw0 hw1 K hK).mul (lift_certificate 1 endpoint_certificate)

private theorem lifted_moment (w : Q') (K : Nat) (r : RatPoly) :
    quaternionHaar 2 (polyMul (relativeHeat w K) (liftHead r)) ≈ quaternionHaar 1 r :=
  Q'.eqv_trans _ _ _ (heat_vacuum 1 (by decide) w K _ (lifted_independent r))
    (haar_liftBoundary 1 1 r)

theorem weight_mass (w : Q') (K : Nat) : quaternionHaar 2 (weight w K) ≈ 1 :=
  Q'.eqv_trans _ _ _ (lifted_moment w K endpoint) (by decide)

/-- Exact free integration of the OTHER endpoint, before the heat update. -/
theorem source_free_centered (w : Q') : RatPolyCoeffEqv (project 1 (source w)) polyZero := by
  have hx : RatPolyCoeffEqv (project 1 (liftHead (polyVar 0))) polyZero := by
    apply RatPolyCoeffEqv.of_canon_termwise
    decide +kernel
  have hi : QuaternionBlockIndependent 1
      (polyAdd (polyVar 0) (polySmul (-(2*qpow w 3)) polyOne)) := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have he := List.mem_singleton.mp ht
      subst t
      rfl
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have he := List.mem_singleton.mp hs
      subst s
      rfl
  exact (project_mul_of_independent 1 _ _ hi).trans
    (((RatPolyCoeffEqv.refl _).mul hx).trans (RatPolyCoeffEqv.mul_zero_right _))

/-- Exact boundary-tested conditional value; all cutoff spins are retained. -/
theorem source_pairing (w : Q') (K : Nat) (hK : 1 ≤ K) (r : RatPoly) :
    quaternionHaar 2 (polyMul (polyMul (relativeHeat w K) (source w)) (liftHead r)) ≈
      qpow w 3 * quaternionHaar 1 (polyMul (polyVar 0) (polyMul (polyVar 0) r)) +
        (-(2*qpow w 3)) * quaternionHaar 1 (polyMul (polyVar 0) r) := by
  let a := -(2*qpow w 3)
  let s := polyMul (polyVar 0) r
  have halg : RatPolyCoeffEqv
      (polyMul (polyMul (relativeHeat w K) (source w)) (liftHead r))
      (polyAdd (polyMul (polyMul (relativeHeat w K) (polyVar 0)) (liftHead s))
        (polySmul a (polyMul (relativeHeat w K) (liftHead s)))) := by
    dsimp only [s]
    rw [liftHead_mul]
    have h := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.add (.var 1) (.var 4)) (.var 2))) (.var 3))
      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.var 4) (.mul (.var 0) (.mul (.var 2) (.var 3)))))
      (by decide) (fun
        | 0 => relativeHeat w K
        | 1 => polyVar 0
        | 2 => liftHead (polyVar 0)
        | 3 => liftHead r
        | _ => cap a)
    exact h.trans ((RatPolyCoeffEqv.refl _).add (cap_mul_left a _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff halg)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append 2 _ _)
      (Q'.add_eqv_congr'
        (coordinate_transmission 1 (by decide) w K hK (0 : Fin 4) s)
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 2 a _)
          (Q'.mul_eqv_congr_left _ _ _ (lifted_moment w K s)))))

/-- The computed conditional output reproduces EVERY endpoint test with
the actual B*h law and its actual B marginal. No endpoint is discarded. -/
theorem output_weighted_pairing (w : Q') (K : Nat) (r : RatPoly) :
    quaternionHaar 1 (polyMul (output w K) (polyMul endpoint r)) ≈
      quaternionHaar 2 (polyMul (weight w K) (polyMul (source w) (liftHead r))) := by
  have h := conditionalHeat_pairing 1 w K (source w) (polyMul endpoint r)
  apply Q'.eqv_trans _ _ _ (Q'.eqv_symm h)
  change quaternionHaar 2
    (polyMul (polyMul (source w) (liftHead (polyMul endpoint r))) (relativeHeat w K)) ≈ _
  rw [liftHead_mul]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 3) (.var 1)) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => source w | 1 => liftHead endpoint | 2 => liftHead r | _ => relativeHeat w K))

theorem source_weighted_mean_zero (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar 2 (polyMul (weight w K) (source w)) ≈ 0 := by
  have he := haar_of_coeff (blocks := 2) (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => relativeHeat w K | 1 => liftHead endpoint | _ => source w))
  have h := source_pairing w K hK endpoint
  have h2 : quaternionHaar 1 (polyMul (polyVar 0) (polyMul (polyVar 0) endpoint)) ≈
      Q'.mkPos 1 4 (by decide) := by decide
  have h1 : quaternionHaar 1 (polyMul (polyVar 0) endpoint) ≈ Q'.mkPos 1 8 (by decide) := by decide
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ h2)
      (Q'.mul_eqv_congr_left _ _ _ h1))
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1))
          (.mul (.neg (.mul (.const 2) (.var 0))) (.var 2)))
        (.mul (.var 0) (.add (.var 1) (.neg (.mul (.const 2) (.var 2)))))
        (by decide) (fun
          | 0 => qpow w 3
          | 1 => Q'.mkPos 1 4 (by decide)
          | _ => Q'.mkPos 1 8 (by decide)))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (by decide : Q'.mkPos 1 4 (by decide) + -(2*Q'.mkPos 1 8 (by decide)) ≈ 0))
          (Q'.mul_zero_eqv _)))))

theorem output_weighted_mean_zero (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar 1 (polyMul (output w K) endpoint) ≈ 0 := by
  have h := conditionalHeat_pairing 1 w K (source w) endpoint
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm h)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 2) (.var 1)) (.var 0)) (by decide)
      (fun | 0 => source w | 1 => liftHead endpoint | _ => relativeHeat w K)))
      (source_weighted_mean_zero w K hK))

/-- A positive free mean appears even though the weighted global mean is zero. -/
theorem output_free_mean (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar 1 (output w K) ≈ qpow w 3 * Q'.mkPos 1 4 (by decide) := by
  have he (p : RatPoly) : quaternionHaar 2 (polyMul p (liftHead polyOne)) ≈ quaternionHaar 2 p :=
    Q'.eqv_trans _ _ _ (head_pairing 1 1 p polyOne)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _))
        (quaternionHaar_partialHaarHeads 1 1 p))
  have h := source_pairing w K hK polyOne
  have h2 : quaternionHaar 1 (polyMul (polyVar 0) (polyMul (polyVar 0) polyOne)) ≈
      Q'.mkPos 1 4 (by decide) := by decide
  have h1 : quaternionHaar 1 (polyMul (polyVar 0) polyOne) ≈ 0 := by decide
  exact Q'.eqv_trans _ _ _ (quaternionHaar_partialHaarHeads 1 1 _)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (he _))
      (Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ h2)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h1) (Q'.mul_zero_eqv _)))
        (Q'.eqv_of_eq (Q'.add_zero' _)))))

theorem output_not_free_centered {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K) :
    ¬ quaternionHaar 1 (output w K) ≈ 0 := by
  intro hz
  have hp : (0 : Q') < qpow w 3 :=
    Q'.mul_pos (Q'.mul_pos (Q'.mul_pos (by decide : (0 : Q') < 1) hw) hw) hw
  have hpos := Q'.mul_pos hp (by decide : (0 : Q') < Q'.mkPos 1 4 (by decide))
  have hbad : (0 : Q') < 0 := Q'.pos_of_lt_of_le hpos
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (output_free_mean w K hK)) hz))
  exact (by decide : ¬ ((0 : Q') < 0)) hbad

/-- Even restricting to globally centered supported inputs does not make
the free-endpoint sector invariant under this neighboring conditional map. -/
theorem free_sector_preservation_false {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K) :
    ¬ (∀ p : RatPoly, SupportedQuaternionBlocks 2 p →
      RatPolyCoeffEqv (project 1 p) polyZero →
      quaternionHaar 2 (polyMul (weight w K) p) ≈ 0 →
      quaternionHaar 1 (conditionalHeat w K p) ≈ 0) := by
  intro h
  exact output_not_free_centered hw K hK
    (h (source w) (source_supported w) (source_free_centered w) (source_weighted_mean_zero w K hK))

end YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction

#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.endpoint_floor
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.weight_certificate
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.weight_mass
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.source_supported
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.source_free_centered
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.source_pairing
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.output_weighted_pairing
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.source_weighted_mean_zero
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.output_weighted_mean_zero
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.output_free_mean
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.output_not_free_centered
#print axioms YMGap.Continuum.SU2QuaternionHeatFreeSectorObstruction.free_sector_preservation_false
