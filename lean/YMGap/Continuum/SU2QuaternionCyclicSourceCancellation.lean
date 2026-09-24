/-
# Cyclic source cancellation

The differential Casimir sweep is paired in the same rotating frame as its
test polynomial.  Its successor law isolates the genuine signed head source;
this is the recurrence used to cancel endpoint derivatives block by block.
-/

import YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
import YMGap.Continuum.SU2QuaternionCyclicWeightedAngular
import YMGap.Continuum.QuaternionHaarWeightedAngularCancellation
import YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor

namespace YMGap.Continuum.SU2QuaternionCyclicSourceCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionCyclicHeatLinear
open YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionCyclicWeightedAngular
open YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarWeightedAngularCancellation
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sixValue_neg_local (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

private theorem angular_pair_ibp (tail : Nat) (p q : RatPoly) :
    angularPairValue (tail+1) p q ≈
      -(H (tail+1) (polyMul p (angularLaplacian q))) := by
  let second := fun i j => H (tail+1)
    (polyMul p (angularDerivative i j (angularDerivative i j q)))
  have hplane (i j : Nat) (hi : i < 4) (hj : j < 4) :
      H (tail+1) (polyMul (angularDerivative i j p) (angularDerivative i j q)) ≈
        -(second i j) := by
    have hz := quaternionHaar_weighted_angular tail hi hj p (angularDerivative i j q)
    have he : H (tail+1)
        (polyMul (angularDerivative i j p) (angularDerivative i j q)) + second i j ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _)) hz
    apply QPoly.q_eqv_of_sub_zero
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
        (.add (.var 0) (.var 1)) (by decide)
        (fun k => if k = 0 then H (tail+1)
          (polyMul (angularDerivative i j p) (angularDerivative i j q)) else second i j)) he
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j hi hj => hplane i j hi hj))
    (Q'.eqv_trans _ _ _ (sixValue_neg_local second)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (haar_six (tail+1) p _))))

/-- Haar integration by parts identifies the unweighted head angular square
with the negative head-Laplacian pairing. -/
theorem head_self_ibp (tail : Nat) (p : RatPoly) :
    H (tail+1) (angularSquare p) ≈
      -(H (tail+1) (polyMul p (angularLaplacian p))) := by
  have hs : H (tail+1) (angularSquare p) ≈ angularPairValue (tail+1) p p := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
      (Q'.eqv_trans _ _ _ (haar_six (tail+1) polyOne _)
        (sixValue_congr _ _
          (fun _ _ _ _ => haar_of_coeff (RatPolyCoeffEqv.one_mul _))))
  exact Q'.eqv_trans _ _ _ hs (angular_pair_ibp tail p p)

/-- Pair a differential sweep in the coordinate frame reached after the same
number of cyclic steps. -/
def sweepPair (tail m : Nat) (p test : RatPoly) : Q' :=
  H (tail+1) (polyMul (rotateIterate (tail+1) m test) (casimirSweep tail m p))

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem step_pair (tail m : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    H (tail+1) (polyMul (rotateIterate (tail+1) (m+1) test)
      (rotateIterate (tail+1) m (casimirStep tail p))) ≈
      H (tail+1) (polyMul test (polyNeg (angularLaplacian p))) := by
  rw [rotateIterate_succ_right]
  exact Q'.eqv_trans _ _ _
    (rotateIterate_pairing_invariant (tail+1) m
      (cycleRotation (tail+1) test) (casimirStep tail p)
      (rotateIterate_supported (tail+1) 1 ht) (casimirStep_supported tail hp))
    (rotateIterate_pairing_invariant (tail+1) 1 test
      (polyNeg (angularLaplacian p)) ht
      (neg_supported (angularLaplacian_supported (by omega) hp)))

/-- One sweep step is one signed head Laplacian pairing plus the same problem
in the next cyclic frame. -/
theorem sweepPair_succ (tail m : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    sweepPair tail (m+1) p test ≈
      H (tail+1) (polyMul test (polyNeg (angularLaplacian p))) +
        sweepPair tail m (cycleRotation (tail+1) p)
          (cycleRotation (tail+1) test) := by
  change H (tail+1) (polyMul (rotateIterate (tail+1) (m+1) test)
      (polyAdd (rotateIterate (tail+1) m (casimirStep tail p))
        (casimirSweep tail m (cycleRotation (tail+1) p)))) ≈ _
  rw [rotateIterate_succ_right]
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append (tail+1) _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (rotateIterate_pairing_invariant (tail+1) m
            (cycleRotation (tail+1) test) (casimirStep tail p)
            (rotateIterate_supported (tail+1) 1 ht) (casimirStep_supported tail hp))
          (rotateIterate_pairing_invariant (tail+1) 1 test
            (polyNeg (angularLaplacian p)) ht
            (neg_supported (angularLaplacian_supported (by omega) hp))))
        (Q'.eqv_refl _)))

/-- The two Casimir sweeps occurring in the weighted source coefficient,
kept in their common rotating frame. -/
def sourceSweep (tail m : Nat) (a f : RatPoly) : Q' :=
  sweepPair tail m (polyMul a f) (polyMul a f) +
    -(sweepPair tail m a (polyMul a (polyMul f f)))

/-- The local source emitted by the paired recurrence is exactly the head
weighted angular square; all derivatives of the signed endpoint cancel. -/
theorem sourceSweep_succ (tail m : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceSweep tail (m+1) a f ≈
      H (tail+1) (polyMul (polyMul a a) (angularSquare f)) +
        sourceSweep tail m (cycleRotation (tail+1) a)
          (cycleRotation (tail+1) f) := by
  have haf := supported_polyMul ha hf
  have haff := supported_polyMul ha (supported_polyMul hf hf)
  have hfirst := sweepPair_succ tail m (polyMul a f) (polyMul a f) haf haf
  have hsecond := sweepPair_succ tail m a (polyMul a (polyMul f f)) ha haff
  have hcancel := weighted_angular_cancellation tail a f
  have hneg (p q : RatPoly) :
      H (tail+1) (polyMul p (polyNeg q)) ≈
        -(H (tail+1) (polyMul p q)) := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (((QuaternionHaarAngularCarrier.neg_smul q).mul_left p).trans
          (RatPolyCoeffEqv.polyMul_smul_right (-1) p q)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) (-1) _)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
          (.neg (.var 0)) (by decide)
          (fun _ => H (tail+1) (polyMul p q))))
  have hlocal :
      H (tail+1) (polyMul (polyMul a f)
        (polyNeg (angularLaplacian (polyMul a f)))) +
      -(H (tail+1) (polyMul (polyMul a (polyMul f f))
        (polyNeg (angularLaplacian a)))) ≈
      H (tail+1) (polyMul (polyMul a a) (angularSquare f)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (hneg _ _)
        (Q'.neg_eqv_congr _ _ (hneg _ _)))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_symm (head_self_ibp tail (polyMul a f)))
          (poly_identity_of_normal_eq (.neg (.neg (.var 0))) (.var 0)
            (by decide) (fun _ => H (tail+1)
              (polyMul (polyMul a (polyMul f f)) (angularLaplacian a)))))
        hcancel)
  have hrest :
      sweepPair tail m (cycleRotation (tail+1) (polyMul a f))
          (cycleRotation (tail+1) (polyMul a f)) +
        -(sweepPair tail m (cycleRotation (tail+1) a)
          (cycleRotation (tail+1) (polyMul a (polyMul f f)))) ≈
      sourceSweep tail m (cycleRotation (tail+1) a)
        (cycleRotation (tail+1) f) := by
    apply Q'.eqv_of_eq
    simp only [sourceSweep, cycleRotation_mul]
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hfirst (Q'.neg_eqv_congr _ _ hsecond))
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 3))))
        (.add (.add (.var 0) (.neg (.var 1)))
          (.add (.var 2) (.neg (.var 3))))
        (by decide) (fun
          | 0 => H (tail+1) (polyMul (polyMul a f)
              (polyNeg (angularLaplacian (polyMul a f))))
          | 1 => H (tail+1) (polyMul (polyMul a (polyMul f f))
              (polyNeg (angularLaplacian a)))
          | 2 => sweepPair tail m (cycleRotation (tail+1) (polyMul a f))
              (cycleRotation (tail+1) (polyMul a f))
          | _ => sweepPair tail m (cycleRotation (tail+1) a)
              (cycleRotation (tail+1) (polyMul a (polyMul f f)))))
      (Q'.add_eqv_congr' hlocal hrest))

/-- The recursively emitted head energies, with both endpoint and observable
rotated into the frame in which that head is differentiated. -/
def rotatedAngularSum (tail : Nat) : Nat → RatPoly → RatPoly → Q'
  | 0, _, _ => 0
  | m+1, a, f =>
      H (tail+1) (polyMul (polyMul a a) (angularSquare f)) +
        rotatedAngularSum tail m (cycleRotation (tail+1) a)
          (cycleRotation (tail+1) f)

/-- Iterating the paired sweep recurrence leaves exactly the recursively
rotated weighted angular squares. -/
theorem sourceSweep_eq_rotatedAngularSum (tail : Nat) :
    ∀ (m : Nat) (a f : RatPoly),
    SupportedQuaternionBlocks (tail+1) a →
    SupportedQuaternionBlocks (tail+1) f →
    sourceSweep tail m a f ≈ rotatedAngularSum tail m a f
  | 0, a, f, _, _ => by
      have hz (p test : RatPoly) : sweepPair tail 0 p test ≈ 0 :=
        haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test)
      unfold sourceSweep rotatedAngularSum
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (hz (polyMul a f) (polyMul a f))
          (Q'.neg_eqv_congr _ _ (hz a (polyMul a (polyMul f f)))))
        (by decide)
  | m+1, a, f, ha, hf => by
      have hs := sourceSweep_succ tail m a f ha hf
      have hi := sourceSweep_eq_rotatedAngularSum tail m
        (cycleRotation (tail+1) a) (cycleRotation (tail+1) f)
        (rotateIterate_supported (tail+1) 1 ha)
        (rotateIterate_supported (tail+1) 1 hf)
      exact Q'.eqv_trans _ _ _ hs (Q'.add_eqv_congr' (Q'.eqv_refl _) hi)

end YMGap.Continuum.SU2QuaternionCyclicSourceCancellation

#print axioms YMGap.Continuum.SU2QuaternionCyclicSourceCancellation.head_self_ibp
#print axioms YMGap.Continuum.SU2QuaternionCyclicSourceCancellation.sweepPair_succ
#print axioms YMGap.Continuum.SU2QuaternionCyclicSourceCancellation.sourceSweep_succ
#print axioms YMGap.Continuum.SU2QuaternionCyclicSourceCancellation.sourceSweep_eq_rotatedAngularSum
