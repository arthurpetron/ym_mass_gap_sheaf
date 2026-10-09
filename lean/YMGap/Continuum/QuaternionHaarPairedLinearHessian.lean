/-
Exact paired Hessian of an arbitrary head-linear quaternion polynomial.
Euler decomposition retains all spectator coefficients. The coordinate Clifford
identities are checked sparsely; the result is arbitrary-insertion Haar carrier
equality, not just equality of unweighted moments. Frozen direction coefficients
are multiplied only after the raw second jets. This supplies algebra for actual
plaquette curvature transport, not an original marginal curvature or gap bound.
-/

import YMGap.Continuum.QuaternionHaarLinearAngularEnergy
import YMGap.Continuum.SU2QuaternionPairedFrameScalarJets

namespace YMGap.Continuum.QuaternionHaarPairedLinearHessian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angular_partial_zero)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets
open YMGap.Continuum.SU2QuaternionHaarSparseEquality (carrier_of_canon_check)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem paired_add (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i (polyAdd p q))
      (polyAdd (pairedDerivative i p) (pairedDerivative i q)) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angularDerivative_add 0 1 p q).add
      (angularDerivative_add 2 3 p q)).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)
  · refine (RatPolyCoeffEqv.add (angularDerivative_add 0 2 p q)
      (RatPolyCoeffEqv.neg (angularDerivative_add 1 3 p q))).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun
        | 0 => angularDerivative 0 2 p
        | 1 => angularDerivative 0 2 q | 2 => angularDerivative 1 3 p
        | _ => angularDerivative 1 3 q)
  · exact ((angularDerivative_add 0 3 p q).add
      (angularDerivative_add 1 2 p q)).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem paired_factor (i : Fin 3) (a b : RatPoly)
    (hz : ∀ k l, k < 4 → l < 4 →
      RatPolyCoeffEqv (angularDerivative k l b) polyZero) :
    RatPolyCoeffEqv (pairedDerivative i (polyMul a b))
      (polyMul (pairedDerivative i a) b) := by
  have h (k l : Nat) (hk : k < 4) (hl : l < 4) : RatPolyCoeffEqv
      (angularDerivative k l (polyMul a b)) (polyMul (angularDerivative k l a) b) :=
    (angularDerivative_mul k l a b).trans
      ((RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
        ((hz k l hk hl).mul_left a)).trans
        ((RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (RatPolyCoeffEqv.mul_zero_right a)).trans (RatPolyCoeffEqv.add_zero _)))
  have hplus (x y : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyMul x b) (polyMul y b)) (polyMul (polyAdd x y) b) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => x | 1 => y | _ => b)
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((h 0 1 (by decide) (by decide)).add
      (h 2 3 (by decide) (by decide))).trans (hplus _ _)
  · refine (RatPolyCoeffEqv.add (h 0 2 (by decide) (by decide))
      (RatPolyCoeffEqv.neg (h 1 3 (by decide) (by decide)))).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (by decide) (fun
        | 0 => angularDerivative 0 2 a
        | 1 => angularDerivative 1 3 a | _ => b)
  · exact ((h 0 3 (by decide) (by decide)).add
      (h 1 2 (by decide) (by decide))).trans (hplus _ _)

private theorem second_add {blocks : Nat} (hb : 0 < blocks)
    (i j : Fin 3) (p q : RatPoly) : HaarCarrierEqv blocks
      (pairedDerivative i (pairedDerivative j (polyAdd p q)))
      (polyAdd (pairedDerivative i (pairedDerivative j p))
        (pairedDerivative i (pairedDerivative j q))) :=
  (pairedDerivative_carrier hb i (RatPolyCoeffEqv.haarCarrier (paired_add j p q))).trans
    (RatPolyCoeffEqv.haarCarrier (paired_add i _ _))

private theorem mixed_add {blocks : Nat} (hb : 0 < blocks)
    (i j : Fin 3) (p q : RatPoly) : HaarCarrierEqv blocks
      (polyAdd (pairedDerivative i (pairedDerivative j (polyAdd p q)))
        (pairedDerivative j (pairedDerivative i (polyAdd p q))))
      (polyAdd
        (polyAdd (pairedDerivative i (pairedDerivative j p))
          (pairedDerivative j (pairedDerivative i p)))
        (polyAdd (pairedDerivative i (pairedDerivative j q))
          (pairedDerivative j (pairedDerivative i q)))) :=
  (HaarCarrierEqv.add (second_add hb i j p q) (second_add hb j i p q)).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.four_add_swap _ _ _ _))

private theorem second_factor {blocks : Nat} (hb : 0 < blocks)
    (i j : Fin 3) (a b : RatPoly)
    (hz : ∀ k l, k < 4 → l < 4 →
      RatPolyCoeffEqv (angularDerivative k l b) polyZero) : HaarCarrierEqv blocks
      (pairedDerivative i (pairedDerivative j (polyMul a b)))
      (polyMul (pairedDerivative i (pairedDerivative j a)) b) :=
  (pairedDerivative_carrier hb i (RatPolyCoeffEqv.haarCarrier
    (paired_factor j a b hz))).trans
      (RatPolyCoeffEqv.haarCarrier (paired_factor i _ b hz))

private def coordinateFirstJet (i : Fin 3) (k : Nat) : RatPoly :=
  match i.val, k with
  | 0, 0 => polyNeg (polyVar 1)
  | 0, 1 => polyVar 0
  | 0, 2 => polyNeg (polyVar 3)
  | 0, _ => polyVar 2
  | 1, 0 => polyNeg (polyVar 2)
  | 1, 1 => polyVar 3
  | 1, 2 => polyVar 0
  | 1, _ => polyNeg (polyVar 1)
  | _, 0 => polyNeg (polyVar 3)
  | _, 1 => polyNeg (polyVar 2)
  | _, 2 => polyVar 1
  | _, _ => polyVar 0

private theorem coordinate_first_jet (blocks : Nat) (i : Fin 3)
    (k : Nat) (hk : k < 4) : HaarCarrierEqv blocks
      (pairedDerivative i (polyVar k)) (coordinateFirstJet i k) := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases direction_cases i with rfl | rfl | rfl
  all_goals (apply carrier_of_canon_check; decide +kernel)

private theorem coordinate_neg_first_jet (blocks : Nat) (i : Fin 3)
    (k : Nat) (hk : k < 4) : HaarCarrierEqv blocks
      (pairedDerivative i (polyNeg (polyVar k)))
      (polyNeg (coordinateFirstJet i k)) := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases direction_cases i with rfl | rfl | rfl
  all_goals (apply carrier_of_canon_check; decide +kernel)

private def coordinateSecondJet (i j : Fin 3) (k : Nat) : RatPoly :=
  match j.val, k with
  | 0, 0 => polyNeg (coordinateFirstJet i 1)
  | 0, 1 => coordinateFirstJet i 0
  | 0, 2 => polyNeg (coordinateFirstJet i 3)
  | 0, _ => coordinateFirstJet i 2
  | 1, 0 => polyNeg (coordinateFirstJet i 2)
  | 1, 1 => coordinateFirstJet i 3
  | 1, 2 => coordinateFirstJet i 0
  | 1, _ => polyNeg (coordinateFirstJet i 1)
  | _, 0 => polyNeg (coordinateFirstJet i 3)
  | _, 1 => polyNeg (coordinateFirstJet i 2)
  | _, 2 => coordinateFirstJet i 1
  | _, _ => coordinateFirstJet i 0

private theorem coordinate_second_jet (blocks : Nat)
    (i j : Fin 3) (k : Nat) (hk : k < 4) : HaarCarrierEqv blocks
      (pairedDerivative i (coordinateFirstJet j k)) (coordinateSecondJet i j k) := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · rcases direction_cases j with rfl | rfl | rfl
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyNeg (polyVar 1))) (polyNeg (coordinateFirstJet i 1))
      exact coordinate_neg_first_jet blocks i 1 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyNeg (polyVar 2))) (polyNeg (coordinateFirstJet i 2))
      exact coordinate_neg_first_jet blocks i 2 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyNeg (polyVar 3))) (polyNeg (coordinateFirstJet i 3))
      exact coordinate_neg_first_jet blocks i 3 (by decide)
  · rcases direction_cases j with rfl | rfl | rfl
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyVar 0)) (coordinateFirstJet i 0)
      exact coordinate_first_jet blocks i 0 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyVar 3)) (coordinateFirstJet i 3)
      exact coordinate_first_jet blocks i 3 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyNeg (polyVar 2))) (polyNeg (coordinateFirstJet i 2))
      exact coordinate_neg_first_jet blocks i 2 (by decide)
  · rcases direction_cases j with rfl | rfl | rfl
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyNeg (polyVar 3))) (polyNeg (coordinateFirstJet i 3))
      exact coordinate_neg_first_jet blocks i 3 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyVar 0)) (coordinateFirstJet i 0)
      exact coordinate_first_jet blocks i 0 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyVar 1)) (coordinateFirstJet i 1)
      exact coordinate_first_jet blocks i 1 (by decide)
  · rcases direction_cases j with rfl | rfl | rfl
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyVar 2)) (coordinateFirstJet i 2)
      exact coordinate_first_jet blocks i 2 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyNeg (polyVar 1))) (polyNeg (coordinateFirstJet i 1))
      exact coordinate_neg_first_jet blocks i 1 (by decide)
    · change HaarCarrierEqv blocks
        (pairedDerivative i (polyVar 0)) (coordinateFirstJet i 0)
      exact coordinate_first_jet blocks i 0 (by decide)

private theorem coordinate_diagonal {blocks : Nat} (hb : 0 < blocks) (i : Fin 3)
    (k : Nat) (hk : k < 4) : HaarCarrierEqv blocks
      (pairedDerivative i (pairedDerivative i (polyVar k))) (polyNeg (polyVar k)) := by
  refine (pairedDerivative_carrier hb i (coordinate_first_jet blocks i k hk)).trans ?_
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases direction_cases i with rfl | rfl | rfl
  all_goals (apply carrier_of_canon_check; decide +kernel)

private theorem coordinate_mixed {blocks : Nat} (hb : 0 < blocks) (i j : Fin 3)
    (hij : i ≠ j) (k : Nat) (hk : k < 4) : HaarCarrierEqv blocks
      (polyAdd (pairedDerivative i (pairedDerivative j (polyVar k)))
        (pairedDerivative j (pairedDerivative i (polyVar k)))) polyZero := by
  refine (HaarCarrierEqv.add
    (pairedDerivative_carrier hb i (coordinate_first_jet blocks j k hk))
    (pairedDerivative_carrier hb j (coordinate_first_jet blocks i k hk))).trans ?_
  refine (HaarCarrierEqv.add
    (coordinate_second_jet blocks i j k hk)
    (coordinate_second_jet blocks j i k hk)).trans ?_
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases direction_cases i with rfl | rfl | rfl
  all_goals rcases direction_cases j with rfl | rfl | rfl
  all_goals first
    | exact False.elim (hij rfl)
    | apply carrier_of_canon_check; decide +kernel

private theorem euler_pin (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) :
    RatPolyCoeffEqv (headEuler p) p :=
  (headEuler_of_blockDegree 1 p hp).trans
    ((cap_mul_left 1 p).symm.trans (RatPolyCoeffEqv.one_mul p))

/-- Every literal paired direction has Hessian -p on a head-linear polynomial,
at full arbitrary-insertion Haar carrier strength. -/
theorem paired_linear_diagonal {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) (i : Fin 3) :
    HaarCarrierEqv blocks (pairedDerivative i (pairedDerivative i p)) (polyNeg p) := by
  have ht (k : Nat) (hk : k < 4) : HaarCarrierEqv blocks
      (pairedDerivative i (pairedDerivative i (polyMul (polyVar k) (ratDerivative k p))))
      (polyNeg (polyMul (polyVar k) (ratDerivative k p))) := by
    refine (second_factor hb i i _ _ (fun a b ha hb =>
      angular_partial_zero ha hb hk p hp)).trans ?_
    refine (HaarCarrierEqv.mul_right (ratDerivative k p)
      (coordinate_diagonal hb i k hk)).trans ?_
    exact RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => polyVar k | _ => ratDerivative k p))
  refine (pairedDerivative_carrier hb i (pairedDerivative_carrier hb i
    (RatPolyCoeffEqv.haarCarrier (euler_pin p hp).symm))).trans ?_
  refine (second_add hb i i _ _).trans ?_
  refine (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (second_add hb i i _ _)).trans ?_
  refine (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (second_add hb i i _ _))).trans ?_
  refine (HaarCarrierEqv.add (ht 0 (by decide)) (HaarCarrierEqv.add (ht 1 (by decide))
    (HaarCarrierEqv.add (ht 2 (by decide)) (ht 3 (by decide))))).trans ?_
  have hn : RatPolyCoeffEqv
      (polyAdd (polyNeg (polyMul (polyVar 0) (ratDerivative 0 p)))
        (polyAdd (polyNeg (polyMul (polyVar 1) (ratDerivative 1 p)))
          (polyAdd (polyNeg (polyMul (polyVar 2) (ratDerivative 2 p)))
            (polyNeg (polyMul (polyVar 3) (ratDerivative 3 p))))))
      (polyNeg (headEuler p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.neg (.var 0)) (.add (.neg (.var 1)) (.add (.neg (.var 2)) (.neg (.var 3)))))
      (.neg (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3)))))
      (by decide) (fun k => polyMul (polyVar k) (ratDerivative k p))
  exact (RatPolyCoeffEqv.haarCarrier hn).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.neg (euler_pin p hp)))

/-- Distinct paired directions have zero symmetrized mixed Hessian. Neither
ordered jet is discarded or replaced by a commuting-derivative assumption. -/
theorem paired_linear_mixed {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p)
    (i j : Fin 3) (hij : i ≠ j) : HaarCarrierEqv blocks
      (polyAdd (pairedDerivative i (pairedDerivative j p))
        (pairedDerivative j (pairedDerivative i p))) polyZero := by
  have ht (k : Nat) (hk : k < 4) : HaarCarrierEqv blocks
      (polyAdd (pairedDerivative i (pairedDerivative j (polyMul (polyVar k) (ratDerivative k p))))
        (pairedDerivative j (pairedDerivative i (polyMul (polyVar k) (ratDerivative k p)))))
      polyZero := by
    have hz (a b : Nat) (ha : a < 4) (hb : b < 4) :=
      angular_partial_zero ha hb hk p hp
    refine (HaarCarrierEqv.add (second_factor hb i j _ _ hz)
      (second_factor hb j i _ _ hz)).trans ?_
    have hdist : RatPolyCoeffEqv
        (polyAdd (polyMul (pairedDerivative i (pairedDerivative j (polyVar k))) (ratDerivative k p))
          (polyMul (pairedDerivative j (pairedDerivative i (polyVar k))) (ratDerivative k p)))
        (polyMul (polyAdd (pairedDerivative i (pairedDerivative j (polyVar k)))
          (pairedDerivative j (pairedDerivative i (polyVar k)))) (ratDerivative k p)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (.mul (.add (.var 0) (.var 1)) (.var 2)) (by decide)
        (fun
          | 0 => pairedDerivative i (pairedDerivative j (polyVar k))
          | 1 => pairedDerivative j (pairedDerivative i (polyVar k)) | _ => ratDerivative k p)
    exact (RatPolyCoeffEqv.haarCarrier hdist).trans
      ((HaarCarrierEqv.mul_right _ (coordinate_mixed hb i j hij k hk)).trans
        (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.mul_comm _ _).trans
          (RatPolyCoeffEqv.mul_zero_right _))))
  have he : HaarCarrierEqv blocks p (headEuler p) :=
    RatPolyCoeffEqv.haarCarrier (euler_pin p hp).symm
  refine (HaarCarrierEqv.add
    (pairedDerivative_carrier hb i (pairedDerivative_carrier hb j he))
    (pairedDerivative_carrier hb j (pairedDerivative_carrier hb i he))).trans ?_
  refine (mixed_add hb i j _ _).trans ?_
  refine (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (mixed_add hb i j _ _)).trans ?_
  refine (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (mixed_add hb i j _ _))).trans ?_
  exact HaarCarrierEqv.add (ht 0 (by decide)) (HaarCarrierEqv.add (ht 1 (by decide))
    (HaarCarrierEqv.add (ht 2 (by decide)) (ht 3 (by decide))))

private theorem frozen_grouped (u : Fin 3 → RatPoly) (f : Fin 3 → Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (threeSum (fun i => threeSum (fun j => polyMul (polyMul (u i) (u j)) (f i j))))
      (polyAdd (threeSum (fun i => polyMul (polyMul (u i) (u i)) (f i i)))
        (polyAdd (polyMul (polyMul (u 0) (u 1)) (polyAdd (f 0 1) (f 1 0)))
          (polyAdd (polyMul (polyMul (u 0) (u 2)) (polyAdd (f 0 2) (f 2 0)))
            (polyMul (polyMul (u 1) (u 2)) (polyAdd (f 1 2) (f 2 1)))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 4))
          (.mul (.mul (.var 0) (.var 2)) (.var 5))))
      (.add
        (.add (.mul (.mul (.var 1) (.var 0)) (.var 6))
          (.add (.mul (.mul (.var 1) (.var 1)) (.var 7))
            (.mul (.mul (.var 1) (.var 2)) (.var 8))))
        (.add (.mul (.mul (.var 2) (.var 0)) (.var 9))
          (.add (.mul (.mul (.var 2) (.var 1)) (.var 10))
            (.mul (.mul (.var 2) (.var 2)) (.var 11))))))
    (.add
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
        (.add (.mul (.mul (.var 1) (.var 1)) (.var 7))
          (.mul (.mul (.var 2) (.var 2)) (.var 11))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.add (.var 4) (.var 6)))
        (.add (.mul (.mul (.var 0) (.var 2)) (.add (.var 5) (.var 9)))
          (.mul (.mul (.var 1) (.var 2)) (.add (.var 8) (.var 10))))))
    (by decide) (fun
      | 0 => u 0 | 1 => u 1 | 2 => u 2
      | 3 => f 0 0 | 4 => f 0 1 | 5 => f 0 2
      | 6 => f 1 0 | 7 => f 1 1 | 8 => f 1 2
      | 9 => f 2 0 | 10 => f 2 1 | _ => f 2 2)

/-- Finite nine-entry Hessian contraction from actual diagonal and mixed
carrier pins. Applicable also after literal word transport; arbitrary u is
multiplied only after the jets and is never differentiated. -/
theorem frozen_hessian_of_diagonal_mixed {blocks : Nat}
    (p : RatPoly) (u : Fin 3 → RatPoly) (f : Fin 3 → Fin 3 → RatPoly)
    (hd : ∀ i, HaarCarrierEqv blocks (f i i) (polyNeg p))
    (hm : ∀ i j, i ≠ j → HaarCarrierEqv blocks (polyAdd (f i j) (f j i)) polyZero) :
    HaarCarrierEqv blocks
      (threeSum (fun i => threeSum (fun j => polyMul (polyMul (u i) (u j)) (f i j))))
      (polyNeg (polyMul (threeSquare u) p)) := by
  have hd' := HaarCarrierEqv.add (HaarCarrierEqv.mul_left (polyMul (u 0) (u 0)) (hd 0))
    (HaarCarrierEqv.add (HaarCarrierEqv.mul_left (polyMul (u 1) (u 1)) (hd 1))
      (HaarCarrierEqv.mul_left (polyMul (u 2) (u 2)) (hd 2)))
  have hz (i j : Fin 3) (hij : i ≠ j) : HaarCarrierEqv blocks
      (polyMul (polyMul (u i) (u j)) (polyAdd (f i j) (f j i))) polyZero :=
    (HaarCarrierEqv.mul_left (polyMul (u i) (u j)) (hm i j hij)).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _))
  refine (RatPolyCoeffEqv.haarCarrier (frozen_grouped u f)).trans
    ((HaarCarrierEqv.add hd' (HaarCarrierEqv.add (hz 0 1 (by decide))
      (HaarCarrierEqv.add (hz 0 2 (by decide)) (hz 1 2 (by decide))))).trans ?_)
  refine (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _)).trans ?_
  exact RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 0) (.var 0)) (.neg (.var 3)))
      (.add (.mul (.mul (.var 1) (.var 1)) (.neg (.var 3)))
        (.mul (.mul (.var 2) (.var 2)) (.neg (.var 3)))))
    (.neg (.mul (.add (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))) (.var 3)))
    (by decide) (fun | 0 => u 0 | 1 => u 1 | 2 => u 2 | _ => p))

/-- Frozen ALL-NINE paired Hessian of the original head-linear polynomial. -/
theorem paired_linear_frozen {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) (u : Fin 3 → RatPoly) :
    HaarCarrierEqv blocks (frozenSecondJet u p) (polyNeg (polyMul (threeSquare u) p)) :=
  frozen_hessian_of_diagonal_mixed p u
    (fun i j => pairedDerivative i (pairedDerivative j p))
    (paired_linear_diagonal hb p hp) (paired_linear_mixed hb p hp)

end YMGap.Continuum.QuaternionHaarPairedLinearHessian

#print axioms YMGap.Continuum.QuaternionHaarPairedLinearHessian.paired_linear_diagonal
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearHessian.paired_linear_mixed
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearHessian.frozen_hessian_of_diagonal_mixed
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearHessian.paired_linear_frozen
