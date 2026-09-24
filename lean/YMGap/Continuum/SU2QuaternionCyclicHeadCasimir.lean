/-
# The grouped head Casimir in the actual cyclic decomposition

The complete computed head-harmonic grouping reassembles not only the input
polynomial but also its signed angular Casimir.  Rotating the result gives the
one-step source used by the cyclic first-order recurrence.  These are carrier
identities: no positivity or joint orthogonality of the groups is asserted.
-/

import YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
import YMGap.Continuum.SU2QuaternionHeadAngularPair

namespace YMGap.Continuum.SU2QuaternionCyclicHeadCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicHeatLinear
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionHeadAngularPair
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

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

/-- The six-direction head Laplacian is coefficient-linear under addition. -/
theorem angularLaplacian_add (p q : RatPoly) :
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

private theorem secondAngular_smul (i j : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polySmul c p)))
      (polySmul c (angularDerivative i j (angularDerivative i j p))) :=
  (angularDerivative_congr i j (angularDerivative_smul i j c p)).trans
    (angularDerivative_smul i j c (angularDerivative i j p))

private theorem six_smul (c : Q') (f : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polySmul c (f i j))) (polySmul c (six f)) := by
  unfold six
  have h4 := (RatPolyCoeffEqv.smul_add c (f 1 3) (f 2 3)).symm
  have h3 := ((RatPolyCoeffEqv.refl _).add h4).trans
    (RatPolyCoeffEqv.smul_add c (f 1 2) (polyAdd (f 1 3) (f 2 3))).symm
  have h2 := ((RatPolyCoeffEqv.refl _).add h3).trans
    (RatPolyCoeffEqv.smul_add c (f 0 3)
      (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3)))).symm
  have h1 := ((RatPolyCoeffEqv.refl _).add h2).trans
    (RatPolyCoeffEqv.smul_add c (f 0 2)
      (polyAdd (f 0 3) (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3))))).symm
  exact ((RatPolyCoeffEqv.refl _).add h1).trans
    (RatPolyCoeffEqv.smul_add c (f 0 1)
      (polyAdd (f 0 2) (polyAdd (f 0 3)
        (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3)))))).symm

/-- The six-direction head Laplacian is coefficient-linear under scaling. -/
theorem angularLaplacian_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polySmul c p))
      (polySmul c (angularLaplacian p)) := by
  unfold angularLaplacian
  exact ((secondAngular_smul 0 1 c p).add
    ((secondAngular_smul 0 2 c p).add
      ((secondAngular_smul 0 3 c p).add
        ((secondAngular_smul 1 2 c p).add
          ((secondAngular_smul 1 3 c p).add (secondAngular_smul 2 3 c p)))))).trans
    (six_smul c (fun i j => angularDerivative i j (angularDerivative i j p)))

/-- The head Laplacian annihilates the zero polynomial coefficient-exactly. -/
theorem angularLaplacian_zero :
    RatPolyCoeffEqv (angularLaplacian polyZero) polyZero :=
  RatPolyCoeffEqv.refl _

/-- The head Laplacian preserves a nonempty quaternion-block support prefix. -/
theorem angularLaplacian_supported {blocks : Nat} (hb : 0 < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (angularLaplacian p) := by
  unfold angularLaplacian six
  exact polyAdd_supported
    (angularDerivative_supported hb (by decide) (by decide)
      (angularDerivative_supported hb (by decide) (by decide) hp))
    (polyAdd_supported
      (angularDerivative_supported hb (by decide) (by decide)
        (angularDerivative_supported hb (by decide) (by decide) hp))
      (polyAdd_supported
        (angularDerivative_supported hb (by decide) (by decide)
          (angularDerivative_supported hb (by decide) (by decide) hp))
        (polyAdd_supported
          (angularDerivative_supported hb (by decide) (by decide)
            (angularDerivative_supported hb (by decide) (by decide) hp))
          (polyAdd_supported
            (angularDerivative_supported hb (by decide) (by decide)
              (angularDerivative_supported hb (by decide) (by decide) hp))
            (angularDerivative_supported hb (by decide) (by decide)
              (angularDerivative_supported hb (by decide) (by decide) hp))))))

/-- Public carrier transport for the head Laplacian. -/
theorem angularLaplacian_carrier {blocks : Nat} (hb : 0 < blocks)
    {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (angularLaplacian p) (angularLaplacian q) :=
  QuaternionHaarExposedHeatCasimir.angularLaplacian_carrier hb h

private theorem sum_supported {A : Type} (n : Nat) (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks n (f a)) : ∀ ids : List A,
    SupportedQuaternionBlocks n (polySum (ids.map f))
  | [] => by intro t ht; contradiction
  | a::ids => polyAdd_supported (hf a) (sum_supported n f hf ids)

private theorem weighted_pair_sum (tail : Nat) (test : RatPoly)
    (f : Nat → RatPoly) (c : Nat → Q') : ∀ ids : List Nat,
    quaternionHaar (tail+1)
        (polyMul test (polySum (ids.map fun d => polySmul (c d) (f d)))) ≈
      qListSum (ids.map fun d =>
        c d * quaternionHaar (tail+1) (polyMul (f d) test))
  | [] => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test)
  | d::ids => by
      exact Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append (tail+1) _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _
              (quaternionHaar_polyMul_smul_right (tail+1) (c d) test (f d))
              (Q'.mul_eqv_congr_left _ _ _
                (haar_of_coeff (RatPolyCoeffEqv.mul_comm test (f d)))))
            (weighted_pair_sum tail test f c ids)))

/-- The complete computed head groups reassemble the negative head Casimir. -/
theorem branchCasimir_head_carrier (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1)
      (polySum ((branchDegrees tail p).map fun d =>
        polySmul (Q'.ofNat (d*(d+2))) (branchPiece tail p d)))
      (polyNeg (angularLaplacian p)) := by
  intro test
  exact Q'.eqv_trans _ _ _
    (weighted_pair_sum tail test (branchPiece tail p)
      (fun d => Q'.ofNat (d*(d+2))) (branchDegrees tail p))
    (Q'.eqv_trans _ _ _ (polynomial_generator_pair tail p test hp)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (haar_of_coeff
            (((neg_smul (angularLaplacian p)).mul_right test).trans
              (RatPolyCoeffEqv.polyMul_smul_left (-1) (angularLaplacian p) test)))
          (Q'.eqv_trans _ _ _
            (quaternionHaar_polySmul (tail+1) (-1)
              (polyMul (angularLaplacian p) test))
            (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
              (.neg (.var 0)) (by decide)
              (fun _ => quaternionHaar (tail+1)
                (polyMul (angularLaplacian p) test))))))
        (haar_of_coeff
          (RatPolyCoeffEqv.mul_comm (polyNeg (angularLaplacian p)) test))))

private theorem rotation_sum {A : Type} (n : Nat) (f : A → RatPoly) : ∀ ids : List A,
    cycleRotation n (polySum (ids.map f)) =
      polySum (ids.map fun a => cycleRotation n (f a))
  | [] => rfl
  | a::ids => by
      simp only [List.map_cons, polySum, cycleRotation_add, rotation_sum n f ids]

/-- After the actual cyclic coordinate rotation, the weighted next pieces are
the rotated negative head Casimir source. -/
theorem branchCasimir_rotation_carrier (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1)
      (polySum ((branchDegrees tail p).map fun d =>
        polySmul (Q'.ofNat (d*(d+2))) (nextPiece tail p d)))
      (cycleRotation (tail+1) (polyNeg (angularLaplacian p))) := by
  have hhead := branchCasimir_head_carrier tail p hp
  have hleft : SupportedQuaternionBlocks (tail+1)
      (polySum ((branchDegrees tail p).map fun d =>
        polySmul (Q'.ofNat (d*(d+2))) (branchPiece tail p d))) :=
    sum_supported (tail+1) _
      (fun d => polySmul_supported (grouped_supported d _) _) _
  have hright : SupportedQuaternionBlocks (tail+1)
      (polyNeg (angularLaplacian p)) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact angularLaplacian_supported (by omega) hp s hs
  have hrot := cycleRotation_carrier (tail+1) hleft hright hhead
  have heq : cycleRotation (tail+1)
      (polySum ((branchDegrees tail p).map fun d =>
        polySmul (Q'.ofNat (d*(d+2))) (branchPiece tail p d))) =
      polySum ((branchDegrees tail p).map fun d =>
        polySmul (Q'.ofNat (d*(d+2))) (nextPiece tail p d)) := by
    rw [rotation_sum]
    simp only [cycleRotation_smul, nextPiece]
  exact heq ▸ hrot

end YMGap.Continuum.SU2QuaternionCyclicHeadCasimir

#print axioms YMGap.Continuum.SU2QuaternionCyclicHeadCasimir.angularLaplacian_add
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeadCasimir.angularLaplacian_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeadCasimir.angularLaplacian_zero
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeadCasimir.angularLaplacian_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeadCasimir.angularLaplacian_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeadCasimir.branchCasimir_head_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeadCasimir.branchCasimir_rotation_carrier
