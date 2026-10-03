/-
# Original one-link scalar alignment does not amplify to quaternion sources

For u=(a,b,c,d), the supported quaternion source v=(3a,b,c,d) has
Haar squared norm three and degree-one heat eigenvalue w^3. Its ACTUAL
left product uv=(3a^2-b^2-c^2-d^2,4ab,4ac,4ad) consists of four trace-free
quadratic modes, hence has the same norm three and heat eigenvalue w^8.
Every original prefix K>=2 therefore violates the proposed vector lift
by 3w^8<3w^6. This refutes that amplification step only: the scalar-source,
distinct-link Wilson-word target and original positive terminal remain open.
-/

import YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission
import YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
import YMGap.Continuum.QuaternionHaarWordComponents
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.SU2QuaternionHeatAlignmentAmplificationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftHead)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat coordinate_transmission)
open YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission
  (quadratic quadratic_heat_transmission)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarWordComponents (component)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.HeatKernelRGStep (qpow_add lt_of_lt_of_le)
open YMGap.Continuum.HeatKernelGap (qpow_succ_lt_one lt_of_le_of_lt)

local infix:50 " ≈ " => Q'.eqv

/-- The explicit original one-link quaternion-valued source. -/
def vectorSource : PolyQuaternion :=
  ⟨polySmul 3 (polyVar 0), polyVar 1, polyVar 2, polyVar 3⟩

/-- Literal left quaternion multiplication, not a surrogate heat image. -/
def productSource : PolyQuaternion :=
  PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0) vectorSource

private theorem supported_scale {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem vectorSource_supported : Supported 1 vectorSource := by
  have h := Supported.coordinate (by decide : 0<1)
  exact ⟨supported_scale h.scalar 3, h.iPart, h.jPart, h.kPart⟩

theorem productSource_supported : Supported 1 productSource :=
  (Supported.coordinate (by decide : 0<1)).mul vectorSource_supported

/-- Exact degree-one coordinates; only the scalar coefficient is three. -/
theorem vectorSource_component (i : Fin 4) :
    RatPolyCoeffEqv (component i.val vectorSource)
      (polySmul (if i.val=0 then 3 else 1) (polyVar i.val)) := by
  have h : ∀ i : Fin 4, RatPolyTermwiseEqv
      (canonRat (component i.val vectorSource))
      (canonRat (polySmul (if i.val=0 then 3 else 1) (polyVar i.val))) := by
    decide +kernel
  exact RatPolyCoeffEqv.of_canon_termwise (h i)

/-- All four actual product coordinates are explicit trace-free quadratics.
The scalar is 4(a²-radius/4), and the others are 4ab,4ac,4ad. -/
theorem productSource_component (i : Fin 4) :
    RatPolyCoeffEqv (component i.val productSource) (polySmul 4 (quadratic 0 i)) := by
  have h : ∀ i : Fin 4, RatPolyTermwiseEqv
      (canonRat (component i.val productSource)) (canonRat (polySmul 4 (quadratic 0 i))) := by
    decide +kernel
  exact RatPolyCoeffEqv.of_canon_termwise (h i)

theorem vectorSource_norm : quaternionHaar 1 (polyQuaternionNorm vectorSource) ≈ (3 : Q') := by
  decide +kernel

theorem productSource_norm : quaternionHaar 1 (polyQuaternionNorm productSource) ≈ (3 : Q') := by
  decide +kernel

private def haarPair (p r : RatPoly) : Q' := quaternionHaar 1 (polyMul p r)

private def heatPair (w : Q') (K : Nat) (p r : RatPoly) : Q' :=
  quaternionHaar 2 (polyMul (polyMul (relativeHeat w K) p) (liftHead r))

private theorem haarPair_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) (r : RatPoly) :
    haarPair p r ≈ haarPair q r := haar_of_coeff (h.mul_right r)

private theorem heatPair_congr (w : Q') (K : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) (r : RatPoly) :
    heatPair w K p r ≈ heatPair w K q r :=
  haar_of_coeff ((h.mul_left (relativeHeat w K)).mul_right (liftHead r))

private theorem haarPair_smul (c : Q') (p r : RatPoly) :
    haarPair (polySmul c p) r ≈ c*haarPair p r :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul 1 c (polyMul p r))

private theorem heatPair_smul (w : Q') (K : Nat) (c : Q') (p r : RatPoly) :
    heatPair w K (polySmul c p) r ≈ c*heatPair w K p r :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    (((RatPolyCoeffEqv.polyMul_smul_right c (relativeHeat w K) p).mul_right (liftHead r)).trans
      (RatPolyCoeffEqv.polyMul_smul_left c (polyMul (relativeHeat w K) p) (liftHead r))))
    (quaternionHaar_polySmul 2 c _)

private theorem scaled_transmission (w : Q') (K : Nat) (p r : RatPoly) (c z : Q')
    (h : heatPair w K p r ≈ z*haarPair p r) :
    heatPair w K (polySmul c p) r ≈ z*haarPair (polySmul c p) r :=
  Q'.eqv_trans _ _ _ (heatPair_smul w K c p r)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h)
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c | 1 => z | _ => haarPair p r))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haarPair_smul c p r)))))

private theorem recoded_transmission (w : Q') (K : Nat) {p q : RatPoly}
    (hp : RatPolyCoeffEqv p q) (r : RatPoly) (z : Q')
    (h : heatPair w K q r ≈ z*haarPair q r) :
    heatPair w K p r ≈ z*haarPair p r :=
  Q'.eqv_trans _ _ _ (heatPair_congr w K hp r)
    (Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left _ _ _ (haarPair_congr hp.symm r)))

/-- Original inclusive prefix, arbitrary retained boundary and exact w³. -/
theorem vectorSource_transmission (w : Q') (K : Nat) (hK : 2≤K)
    (i : Fin 4) (r : RatPoly) :
    heatPair w K (component i.val vectorSource) r ≈
      qpow w 3*haarPair (component i.val vectorSource) r :=
  recoded_transmission w K (vectorSource_component i) r _
    (scaled_transmission w K (polyVar i.val) r _ _
      (coordinate_transmission 1 (by decide) w K (by omega) i r))

/-- Original inclusive prefix, arbitrary retained boundary and exact w⁸;
no infinite-series or Fourier oracle is used. -/
theorem productSource_transmission (w : Q') (K : Nat) (hK : 2≤K)
    (i : Fin 4) (r : RatPoly) :
    heatPair w K (component i.val productSource) r ≈
      qpow w 8*haarPair (component i.val productSource) r :=
  recoded_transmission w K (productSource_component i) r _
    (scaled_transmission w K (quadratic 0 i) r 4 _
      (quadratic_heat_transmission 1 (by decide) w K hK 0 i r))

/-- Sum of four ACTUAL one-link heat quadratic pairings on the two-link carrier. -/
def vectorHeatPairing (w : Q') (K : Nat) (v : PolyQuaternion) : Q' :=
  heatPair w K v.scalar v.scalar+
    (heatPair w K v.iPart v.iPart+
      (heatPair w K v.jPart v.jPart+heatPair w K v.kPart v.kPart))

private theorem vector_heat_pin (w : Q') (K : Nat) (v : PolyQuaternion) (z : Q')
    (h : ∀ i : Fin 4, heatPair w K (component i.val v) (component i.val v) ≈
      z*haarPair (component i.val v) (component i.val v)) :
    vectorHeatPairing w K v ≈ z*quaternionHaar 1 (polyQuaternionNorm v) := by
  have hn : quaternionHaar 1 (polyQuaternionNorm v) ≈
      haarPair v.scalar v.scalar+(haarPair v.iPart v.iPart+
        (haarPair v.jPart v.jPart+haarPair v.kPart v.kPart)) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (Q'.add_eqv_congr_left _ _ _ (quaternionHaar_append 1 _ _))))
  have he := Q'.add_eqv_congr' (h 0) (Q'.add_eqv_congr' (h 1) (Q'.add_eqv_congr' (h 2) (h 3)))
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 4)))))
      (.mul (.var 0) (.add (.var 1) (.add (.var 2) (.add (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => z
        | 1 => haarPair v.scalar v.scalar
        | 2 => haarPair v.iPart v.iPart
        | 3 => haarPair v.jPart v.jPart
        | _ => haarPair v.kPart v.kPart))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hn)))

theorem vectorSource_heat_pin (w : Q') (K : Nat) (hK : 2≤K) :
    vectorHeatPairing w K vectorSource ≈ 3*qpow w 3 :=
  Q'.eqv_trans _ _ _ (vector_heat_pin w K vectorSource _
    (fun i => vectorSource_transmission w K hK i _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ vectorSource_norm) (Q'.mul_comm_eqv _ _))

theorem productSource_heat_pin (w : Q') (K : Nat) (hK : 2≤K) :
    vectorHeatPairing w K productSource ≈ 3*qpow w 8 :=
  Q'.eqv_trans _ _ _ (vector_heat_pin w K productSource _
    (fun i => productSource_transmission w K hK i _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ productSource_norm) (Q'.mul_comm_eqv _ _))

private theorem power_positive {w : Q'} (hw : (0 : Q')<w) : ∀ n, (0 : Q')<qpow w n
  | 0 => by change (0 : Q')<1; decide
  | n+1 => Q'.mul_pos (power_positive hw n) hw

private theorem strict_rate {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q')) :
    (3 : Q')*qpow w 8 < 3*qpow w 6 := by
  have hs := Q'.mul_lt_mul_of_pos_left
    (Q'.mul_pos (by decide : (0 : Q')<3) (power_positive hw0 6))
    (qpow_succ_lt_one (Q'.le_of_lt hw0) hw1 1)
  have hl : (3 : Q')*qpow w 8 ≈ (3*qpow w 6)*qpow w 2 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (qpow_add w 6 2))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  exact lt_of_le_of_lt (Q'.le_of_eqv hl)
    (lt_of_lt_of_le hs (Q'.le_of_eqv (Q'.mul_one_eqv _)))

/-- Exact failure of the proposed quaternion-vector amplification for EVERY
strict nome and EVERY original inclusive prefix K>=2. It is not a
counterexample to the narrower distinct-word scalar-source target. -/
theorem quaternion_vector_amplification_fails {w : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q')) (K : Nat) (hK : 2≤K) :
    vectorHeatPairing w K productSource < qpow w 3*vectorHeatPairing w K vectorSource := by
  have hr : qpow w 3*vectorHeatPairing w K vectorSource ≈ (3 : Q')*qpow w 6 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (vectorSource_heat_pin w K hK))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 3) (.var 0)))
          (.mul (.const 3) (.mul (.var 0) (.var 0))) (by decide) (fun _ => qpow w 3))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_add w 3 3))))
  exact lt_of_le_of_lt (Q'.le_of_eqv (productSource_heat_pin w K hK))
    (lt_of_lt_of_le (strict_rate hw0 hw1) (Q'.ge_of_eqv hr))

#print axioms vectorSource
#print axioms productSource
#print axioms vectorSource_supported
#print axioms productSource_supported
#print axioms vectorSource_component
#print axioms productSource_component
#print axioms vectorSource_norm
#print axioms productSource_norm
#print axioms vectorSource_transmission
#print axioms productSource_transmission
#print axioms vectorHeatPairing
#print axioms vectorSource_heat_pin
#print axioms productSource_heat_pin
#print axioms quaternion_vector_amplification_fails

end YMGap.Continuum.SU2QuaternionHeatAlignmentAmplificationObstruction
