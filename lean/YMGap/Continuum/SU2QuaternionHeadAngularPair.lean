/-
# Mixed head-Casimir pairing for a computed polynomial expansion

The computed complete harmonic-degree groups resolve both the zeroth-order
Haar pairing and the mixed angular-generator pairing of an arbitrary supported
polynomial.  The second input is arbitrary and retains every spectator.

These are finite algebraic identities for one quaternion head.  They contain
no heat-cutoff guard and make no product-transfer, physical-time, or continuum
claim.
-/

import YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
import YMGap.Continuum.QuaternionHaarExposedHeatCasimir

namespace YMGap.Continuum.SU2QuaternionHeadAngularPair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.QuaternionHaarExposedHeatCasimir
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem haar_pair_sum (blocks : Nat) (q : RatPoly) (f : Nat → RatPoly) :
    ∀ ids : List Nat,
    quaternionHaar blocks (polyMul (polySum (ids.map f)) q) ≈
      qListSum (ids.map fun d => quaternionHaar blocks (polyMul (f d) q))
  | [] => haar_of_coeff (RatPolyCoeffEqv.mul_zero_left q)
  | d :: ds => by
      have he : RatPolyCoeffEqv
          (polyMul (polyAdd (f d) (polySum (ds.map f))) q)
          (polyAdd (polyMul (f d) q) (polyMul (polySum (ds.map f)) q)) :=
        by
          rw [polyMul_add_left_exact]
          exact RatPolyCoeffEqv.refl _
      exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_pair_sum blocks q f ds)))

/-- The original zeroth-order pairing is the sum of the pairings with its
computed complete harmonic-degree groups.  The arbitrary second factor keeps
all head dependence and all spectators. -/
theorem polynomial_pair_decomposition (tail : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail + 1) p) :
    quaternionHaar (tail + 1) (polyMul p q) ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail + 1) (by omega) p))).map fun d =>
        quaternionHaar (tail + 1)
          (polyMul (grouped d (modes (tail + 1) (by omega) p)) q)) := by
  let ms := modes (tail + 1) (by omega) p
  let ids := headDegrees (sumHarmonics ms)
  have hc : HaarCarrierEqv (tail + 1) p (polySum (ids.map fun d => grouped d ms)) :=
    (polynomial_harmonic_carrier (by omega : 0 < tail + 1) p hp).trans
      (RatPolyCoeffEqv.haarCarrier (headComponent_reassembly (sumHarmonics ms)).symm)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm p q))
    (Q'.eqv_trans _ _ _ (hc q)
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm q (polySum (ids.map fun d => grouped d ms))))
        (haar_pair_sum (tail + 1) q (fun d => grouped d ms) ids)))

private theorem secondAngular_add (i j : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polyAdd p q)))
      (polyAdd (angularDerivative i j (angularDerivative i j p))
        (angularDerivative i j (angularDerivative i j q))) :=
  (angularDerivative_congr i j (angularDerivative_add i j p q)).trans
    (angularDerivative_add i j (angularDerivative i j p) (angularDerivative i j q))

private theorem six_add (f g : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polyAdd (f i j) (g i j)))
      (polyAdd (six f) (six g)) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (by decide) (fun
      | 0 => f 0 1 | 1 => f 0 2 | 2 => f 0 3
      | 3 => f 1 2 | 4 => f 1 3 | 5 => f 2 3
      | 6 => g 0 1 | 7 => g 0 2 | 8 => g 0 3
      | 9 => g 1 2 | 10 => g 1 3 | _ => g 2 3)

private theorem angularLaplacian_add (p q : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polyAdd p q))
      (polyAdd (angularLaplacian p) (angularLaplacian q)) := by
  unfold angularLaplacian
  exact ((secondAngular_add 0 1 p q).add
    ((secondAngular_add 0 2 p q).add
      ((secondAngular_add 0 3 p q).add
        ((secondAngular_add 1 2 p q).add
          ((secondAngular_add 1 3 p q).add (secondAngular_add 2 3 p q)))))).trans
    (six_add
      (fun i j => angularDerivative i j (angularDerivative i j p))
      (fun i j => angularDerivative i j (angularDerivative i j q)))

private theorem angularLaplacian_sum (f : Nat → RatPoly) : ∀ ids : List Nat,
    RatPolyCoeffEqv (angularLaplacian (polySum (ids.map f)))
      (polySum (ids.map fun d => angularLaplacian (f d)))
  | [] => RatPolyCoeffEqv.refl _
  | _d :: ds => (angularLaplacian_add _ _).trans
      ((RatPolyCoeffEqv.refl _).add (angularLaplacian_sum f ds))

private theorem harmonic_generator_pair (tail d : Nat) (p q : RatPoly)
    (hp : HasQuaternionBlockDegree 0 d p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    Q'.ofNat (d * (d + 2)) * quaternionHaar (tail + 1) (polyMul p q) ≈
      -(quaternionHaar (tail + 1) (polyMul (angularLaplacian p) q)) := by
  let c := Q'.ofNat d * (Q'.ofNat d + 2)
  have hc : Q'.ofNat (d * (d + 2)) ≈ c :=
    Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv d (d + 2))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv d 2)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))))
  have hl0 := harmonic_angularLaplacian (Nat.zero_lt_succ tail) p hp hh q
  have hl : quaternionHaar (tail + 1) (polyMul (angularLaplacian p) q) ≈
      quaternionHaar (tail + 1) (polyMul (polySmul (-c) p) q) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm (angularLaplacian p) q))
      (Q'.eqv_trans _ _ _ hl0
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm q (polySmul (-c) p))))
  have hs : quaternionHaar (tail + 1)
      (polyMul (polySmul (-c) p) q) ≈
      (-c) * quaternionHaar (tail + 1) (polyMul p q) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left (-c) p q))
      (quaternionHaar_polySmul (tail + 1) (-c) (polyMul p q))
  have halg : -((-c) * quaternionHaar (tail + 1) (polyMul p q)) ≈
      c * quaternionHaar (tail + 1) (polyMul p q) :=
    poly_identity_of_normal_eq (.neg (.mul (.neg (.var 0)) (.var 1)))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun k => if k = 0 then c else quaternionHaar (tail + 1) (polyMul p q))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
    (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ hl hs)) halg))

private theorem generator_sum (tail : Nat) (q : RatPoly) (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero) : ∀ ids : List Nat,
    qListSum (ids.map fun d =>
      Q'.ofNat (d * (d + 2)) * quaternionHaar (tail + 1) (polyMul (f d) q)) ≈
      -(quaternionHaar (tail + 1)
        (polyMul (polySum (ids.map fun d => angularLaplacian (f d))) q))
  | [] => by
      change (0 : Q') ≈ -(quaternionHaar (tail + 1) (polyMul polyZero q))
      have hz : quaternionHaar (tail + 1) (polyMul polyZero q) ≈ 0 :=
        haar_of_coeff (RatPolyCoeffEqv.mul_zero_left q)
      exact Q'.eqv_trans _ _ _ (by decide)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hz))
  | d :: ds => by
      have hd := harmonic_generator_pair tail d (f d) q (hf d) (hh d)
      have hds := generator_sum tail q f hf hh ds
      have he : RatPolyCoeffEqv
          (polyMul (polyAdd (angularLaplacian (f d))
            (polySum (ds.map fun k => angularLaplacian (f k)))) q)
          (polyAdd (polyMul (angularLaplacian (f d)) q)
            (polyMul (polySum (ds.map fun k => angularLaplacian (f k))) q)) :=
        by
          rw [polyMul_add_left_exact]
          exact RatPolyCoeffEqv.refl _
      have hp := haar_of_coeff (blocks := tail+1) he
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hd hds)
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_add_eqv _ _))
          (Q'.neg_eqv_congr _ _
            (Q'.eqv_symm (Q'.eqv_trans _ _ _ hp (quaternionHaar_append (tail + 1) _ _)))))

/-- The Casimir-weighted mixed pairing of the computed groups is the negative
angular-Laplacian pairing of the original polynomial. -/
theorem polynomial_generator_pair (tail : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail + 1) p) :
    qListSum ((headDegrees (sumHarmonics (modes (tail + 1) (by omega) p))).map fun d =>
      Q'.ofNat (d * (d + 2)) * quaternionHaar (tail + 1)
        (polyMul (grouped d (modes (tail + 1) (by omega) p)) q)) ≈
      -(quaternionHaar (tail + 1) (polyMul (angularLaplacian p) q)) := by
  let ms := modes (tail + 1) (by omega) p
  let f := fun d => grouped d ms
  let ids := headDegrees (sumHarmonics ms)
  have hc : HaarCarrierEqv (tail + 1) p (polySum (ids.map f)) :=
    (polynomial_harmonic_carrier (by omega : 0 < tail + 1) p hp).trans
      (RatPolyCoeffEqv.haarCarrier (headComponent_reassembly (sumHarmonics ms)).symm)
  have hl := angularLaplacian_carrier (by omega : 0 < tail + 1) hc
  exact Q'.eqv_trans _ _ _
    (generator_sum tail q f (fun d => grouped_degree d ms) (fun d => grouped_harmonic d ms) ids)
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (haar_of_coeff ((angularLaplacian_sum f ids).mul_right q).symm)
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm (angularLaplacian (polySum (ids.map f))) q))
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (hl q))
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm q (angularLaplacian p)))))))

end YMGap.Continuum.SU2QuaternionHeadAngularPair

#print axioms YMGap.Continuum.SU2QuaternionHeadAngularPair.polynomial_pair_decomposition
#print axioms YMGap.Continuum.SU2QuaternionHeadAngularPair.polynomial_generator_pair
