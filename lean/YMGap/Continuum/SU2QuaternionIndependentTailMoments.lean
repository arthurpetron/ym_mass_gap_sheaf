/-
# Fundamental moments with an arbitrary independent quaternion tail

Only the exposed quaternion block is integrated. Its four coordinate
covariances remove cross terms exactly; all tail coefficients and the
arbitrary independent spectator remain in the original Haar functional.
The tail's Haar-unit norm then gives the fundamental second moment one.
The bilinear rule instead retains both arbitrary tails and fuses their
traces into the scalar conjugate product, without a tail-unit premise.
No positivity of the spectator, trace factorization, or scaling claim.
-/

import YMGap.Continuum.SU2QuaternionOriginalBlockCoordinateMoments
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.QuaternionHaarUnitScalarSquare

namespace YMGap.Continuum.SU2QuaternionIndependentTailMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOriginalBlockCoordinateMoments
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation "quarter" => SU2PeterWeylWilsonBlock.quarter

private def four (f : Fin 4 → RatPoly) : RatPoly :=
  polyAdd (f 0) (polyAdd (f 1) (polyAdd (f 2) (f 3)))

private def fourQ (f : Fin 4 → Q') : Q' := f 0 + (f 1 + (f 2 + f 3))

private theorem fourQ_congr {a b : Fin 4 → Q'} (h : ∀ i, a i ≈ b i) :
    fourQ a ≈ fourQ b :=
  Q'.add_eqv_congr' (h 0) (Q'.add_eqv_congr' (h 1) (Q'.add_eqv_congr' (h 2) (h 3)))

private theorem fourQ_scale (c : Q') (a : Fin 4 → Q') :
    fourQ (fun i => c * a i) ≈ c * fourQ a :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))))
    (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

private theorem haar_four (blocks : Nat) (r : RatPoly) (f : Fin 4 → RatPoly) :
    quaternionHaar blocks (polyMul (four f) r) ≈
      fourQ (fun i => quaternionHaar blocks (polyMul (f i) r)) := by
  unfold four fourQ
  rw [polyMul_add_left_exact, polyMul_add_left_exact, polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_append _ _ _))))

private theorem pair_add_right (blocks : Nat) (r a b c : RatPoly) :
    weightedPair blocks r a (polyAdd b c) ≈
      weightedPair blocks r a b + weightedPair blocks r a c :=
  Q'.eqv_trans _ _ _ (weighted_symm _ _ _ _)
    (Q'.eqv_trans _ _ _ (weighted_add_left _ _ _ _ _)
      (Q'.add_eqv_congr' (weighted_symm _ _ _ _) (weighted_symm _ _ _ _)))

private theorem pair_add_zero (blocks : Nat) (r a b c : RatPoly)
    (hb : weightedPair blocks r a b ≈ 0) (hc : weightedPair blocks r a c ≈ 0) :
    weightedPair blocks r a (polyAdd b c) ≈ 0 :=
  Q'.eqv_trans _ _ _ (pair_add_right _ _ _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hb hc) (by decide))

private theorem square_add_orthogonal (blocks : Nat) (r a b : RatPoly)
    (h : weightedPair blocks r a b ≈ 0) :
    weightedPair blocks r (polyAdd a b) (polyAdd a b) ≈
      weightedPair blocks r a a + weightedPair blocks r b b := by
  have hba := Q'.eqv_trans _ _ _ (weighted_symm blocks r b a) h
  refine Q'.eqv_trans _ _ _ (weighted_add_left _ _ _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (pair_add_right _ _ _ _ _) (pair_add_right _ _ _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _) h)
      (Q'.add_eqv_congr' hba (Q'.eqv_refl _))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.const 0)) (.add (.const 0) (.var 1)))
    (.add (.var 0) (.var 1)) (by decide)
    (fun | 0 => weightedPair blocks r a a | _ => weightedPair blocks r b b)

private theorem four_orthogonal (blocks : Nat) (r : RatPoly) (f : Fin 4 → RatPoly)
    (h : ∀ i j, i ≠ j → weightedPair blocks r (f i) (f j) ≈ 0) :
    weightedPair blocks r (four f) (four f) ≈
      fourQ (fun i => weightedPair blocks r (f i) (f i)) := by
  have h23 := square_add_orthogonal blocks r (f 2) (f 3) (h 2 3 (by decide))
  have h1 := square_add_orthogonal blocks r (f 1) (polyAdd (f 2) (f 3))
    (pair_add_zero _ _ _ _ _ (h 1 2 (by decide)) (h 1 3 (by decide)))
  have h0 := square_add_orthogonal blocks r (f 0) (polyAdd (f 1) (polyAdd (f 2) (f 3)))
    (pair_add_zero _ _ _ _ _ (h 0 1 (by decide))
      (pair_add_zero _ _ _ _ _ (h 0 2 (by decide)) (h 0 3 (by decide))))
  exact Q'.eqv_trans _ _ _ h0 (Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.eqv_trans _ _ _ h1 (Q'.add_eqv_congr' (Q'.eqv_refl _) h23)))

private def term (block : Nat) (c : Fin 4 → RatPoly) (i : Fin 4) : RatPoly :=
  polyMul (polyVar (4*block+i.val)) (c i)

private theorem term_pair (blocks block : Nat) (hb : block < blocks)
    (c : Fin 4 → RatPoly) (r : RatPoly)
    (hc : ∀ i, QuaternionBlockIndependent block (c i))
    (hr : QuaternionBlockIndependent block r) (i j : Fin 4) :
    weightedPair blocks r (term block c i) (term block c j) ≈
      (if i.val = j.val then quarter else 0) * weightedPair blocks r (c i) (c j) := by
  have he : RatPolyCoeffEqv
      (polyMul (polyMul (term block c i) (term block c j)) r)
      (polyMul (polyMul (polyVar (4*block+i.val)) (polyVar (4*block+j.val)))
        (polyMul (polyMul (c i) (c j)) r)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.var 4))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.mul (.var 1) (.var 3)) (.var 4)))
      (by decide) (fun
        | 0 => polyVar (4*block+i.val)
        | 1 => c i
        | 2 => polyVar (4*block+j.val)
        | 3 => c j
        | _ => r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (variable_pair_mul blocks block hb i j _
      (quaternionBlockIndependent_polyMul (quaternionBlockIndependent_polyMul (hc i) (hc j)) hr))

private theorem linear_square (blocks block : Nat) (hb : block < blocks)
    (c : Fin 4 → RatPoly) (r : RatPoly)
    (hc : ∀ i, QuaternionBlockIndependent block (c i))
    (hr : QuaternionBlockIndependent block r) :
    weightedPair blocks r (four (term block c)) (four (term block c)) ≈
      quarter * quaternionHaar blocks (polyMul (four (fun i => polyMul (c i) (c i))) r) := by
  have hz (i j : Fin 4) (hij : i ≠ j) : weightedPair blocks r (term block c i) (term block c j) ≈ 0 := by
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h := term_pair blocks block hb c r hc hr i j
    rw [if_neg hv] at h
    exact Q'.eqv_trans _ _ _ h (Q'.zero_mul_eqv _)
  refine Q'.eqv_trans _ _ _ (four_orthogonal blocks r (term block c) hz) ?_
  have hd (i : Fin 4) : weightedPair blocks r (term block c i) (term block c i) ≈
      quarter * weightedPair blocks r (c i) (c i) := by
    simpa only [if_pos rfl] using term_pair blocks block hb c r hc hr i i
  exact Q'.eqv_trans _ _ _ (fourQ_congr hd)
    (Q'.eqv_trans _ _ _ (fourQ_scale quarter _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haar_four blocks r _))))

private def coefficients (p : PolyQuaternion) (i : Fin 4) : RatPoly :=
  match i.val with
  | 0 => p.scalar | 1 => polyNeg p.iPart | 2 => polyNeg p.jPart | _ => polyNeg p.kPart

private theorem coefficients_independent {block : Nat} {p : PolyQuaternion}
    (hp : HasPolyQuaternionBlockDegree block 0 p) (i : Fin 4) :
    QuaternionBlockIndependent block (coefficients p i) := by
  unfold coefficients
  split
  · exact degree_zero_independent hp.scalar
  · exact degree_zero_independent hp.iPart.neg
  · exact degree_zero_independent hp.jPart.neg
  · exact degree_zero_independent hp.kPart.neg

private theorem scalar_eq_linear (block : Nat) (p : PolyQuaternion) :
    RatPolyCoeffEqv (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar
      (four (term block (coefficients p))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.add (.mul (.var 2) (.var 3))
      (.add (.mul (.var 4) (.var 5)) (.mul (.var 6) (.var 7))))))
    (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 2) (.neg (.var 3)))
      (.add (.mul (.var 4) (.neg (.var 5))) (.mul (.var 6) (.neg (.var 7))))))
    (by decide) (fun
      | 0 => polyVar (4*block)
      | 1 => p.scalar
      | 2 => polyVar (4*block+1)
      | 3 => p.iPart
      | 4 => polyVar (4*block+2)
      | 5 => p.jPart
      | 6 => polyVar (4*block+3)
      | _ => p.kPart)

private theorem coefficient_squares (p : PolyQuaternion) :
    RatPolyCoeffEqv (four (fun i => polyMul (coefficients p i) (coefficients p i)))
      (polyQuaternionNorm p) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 0)) (.add (.mul (.neg (.var 1)) (.neg (.var 1)))
      (.add (.mul (.neg (.var 2)) (.neg (.var 2))) (.mul (.neg (.var 3)) (.neg (.var 3))))))
    (.add (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 1))
      (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
    (by decide) (fun | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | _ => p.kPart)

/-- The fundamental first moment against the unchanged independent spectator. -/
theorem fundamental_first_moment (blocks block : Nat) (hb : block < blocks)
    (p : PolyQuaternion) (r : RatPoly) (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hr : QuaternionBlockIndependent block r) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1) r) ≈ 0 := by
  have hz (i : Fin 4) : quaternionHaar blocks (polyMul (term block (coefficients p) i) r) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
      (variable_mul blocks block hb i _
        (quaternionBlockIndependent_polyMul (coefficients_independent hp i) hr))
  have hlin := Q'.eqv_trans _ _ _ (haar_four blocks r (term block (coefficients p)))
    (Q'.eqv_trans _ _ _ (fourQ_congr hz) (by decide : fourQ (fun _ => 0) ≈ 0))
  have hscalar := Q'.eqv_trans _ _ _
    (haar_of_coeff ((scalar_eq_linear block p).mul_right r)) hlin
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left 2 _ r))
      (quaternionHaar_polySmul blocks 2 _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ hscalar) (Q'.mul_zero_eqv 2))

/-- The normalized second moment is the untouched spectator's Haar value.
Only the supplied tail's actual Haar-unit relation is used after integration. -/
theorem fundamental_second_moment (blocks block : Nat) (hb : block < blocks)
    (p : PolyQuaternion) (r : RatPoly) (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hr : QuaternionBlockIndependent block r)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    quaternionHaar blocks (polyMul
      (polyMul (characterPolynomial (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1)
        (characterPolynomial (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1)) r) ≈
      quaternionHaar blocks r := by
  let s := (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar
  have hs : weightedPair blocks r s s ≈ quarter * quaternionHaar blocks r := by
    refine Q'.eqv_trans _ _ _
      (haar_of_coeff (((scalar_eq_linear block p).mul (scalar_eq_linear block p)).mul_right r)) ?_
    refine Q'.eqv_trans _ _ _
      (linear_square blocks block hb (coefficients p) r (coefficients_independent hp) hr) ?_
    apply Q'.mul_eqv_congr_left
    exact Q'.eqv_trans _ _ _ (haar_of_coeff ((coefficient_squares p).mul_right r))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ r))
        (Q'.eqv_trans _ _ _ (hnorm r) (haar_of_coeff (RatPolyCoeffEqv.mul_one r))))
  have hright : weightedPair blocks r s (polySmul 2 s) ≈ 2 * weightedPair blocks r s s :=
    Q'.eqv_trans _ _ _ (weighted_symm _ _ _ _) (weighted_smul_left blocks r 2 s s)
  refine Q'.eqv_trans _ _ _ (weighted_smul_left blocks r 2 s (polySmul 2 s)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ hright) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ (Q'.mul_eqv_congr_left 2 _ _ hs)) ?_
  have hnum : (((2 : Q')*2)*quarter) ≈ 1 := by decide
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 2 _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (2*2) quarter _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hnum) (Q'.one_mul_eqv _)))

private theorem cross_term_pair (blocks block : Nat) (hb : block < blocks)
    (c d : Fin 4 → RatPoly) (r : RatPoly)
    (hc : ∀ i, QuaternionBlockIndependent block (c i))
    (hd : ∀ i, QuaternionBlockIndependent block (d i))
    (hr : QuaternionBlockIndependent block r) (i j : Fin 4) :
    weightedPair blocks r (term block c i) (term block d j) ≈
      (if i.val = j.val then quarter else 0) * weightedPair blocks r (c i) (d j) := by
  have he : RatPolyCoeffEqv
      (polyMul (polyMul (term block c i) (term block d j)) r)
      (polyMul (polyMul (polyVar (4*block+i.val)) (polyVar (4*block+j.val)))
        (polyMul (polyMul (c i) (d j)) r)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.var 4))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.mul (.var 1) (.var 3)) (.var 4)))
      (by decide) (fun
        | 0 => polyVar (4*block+i.val) | 1 => c i
        | 2 => polyVar (4*block+j.val) | 3 => d j | _ => r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (variable_pair_mul blocks block hb i j _
      (quaternionBlockIndependent_polyMul (quaternionBlockIndependent_polyMul (hc i) (hd j)) hr))

private theorem pair_four_right (blocks : Nat) (r a : RatPoly) (f : Fin 4 → RatPoly) :
    weightedPair blocks r a (four f) ≈ fourQ (fun i => weightedPair blocks r a (f i)) :=
  Q'.eqv_trans _ _ _ (pair_add_right _ _ _ _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (pair_add_right _ _ _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (pair_add_right _ _ _ _ _))))

private theorem fourQ_single (i : Fin 4) (x : Q') :
    fourQ (fun j => if i = j then x else 0) ≈ x := by
  rcases i with ⟨i,hi⟩
  match i with
  | 0 =>
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.const 0) (.add (.const 0) (.const 0)))) (.var 0)
        (by decide) (fun _ => x)
  | 1 =>
      exact poly_identity_of_normal_eq
        (.add (.const 0) (.add (.var 0) (.add (.const 0) (.const 0)))) (.var 0)
        (by decide) (fun _ => x)
  | 2 =>
      exact poly_identity_of_normal_eq
        (.add (.const 0) (.add (.const 0) (.add (.var 0) (.const 0)))) (.var 0)
        (by decide) (fun _ => x)
  | 3 =>
      exact poly_identity_of_normal_eq
        (.add (.const 0) (.add (.const 0) (.add (.const 0) (.var 0)))) (.var 0)
        (by decide) (fun _ => x)
  | n+4 => exact False.elim (by omega)

private theorem linear_cross_pair (blocks block : Nat) (hb : block < blocks)
    (c d : Fin 4 → RatPoly) (r : RatPoly)
    (hc : ∀ i, QuaternionBlockIndependent block (c i))
    (hd : ∀ i, QuaternionBlockIndependent block (d i))
    (hr : QuaternionBlockIndependent block r) :
    weightedPair blocks r (four (term block c)) (four (term block d)) ≈
      quarter * quaternionHaar blocks (polyMul (four (fun i => polyMul (c i) (d i))) r) := by
  have row (i : Fin 4) : weightedPair blocks r (term block c i) (four (term block d)) ≈
      quarter * weightedPair blocks r (c i) (d i) := by
    refine Q'.eqv_trans _ _ _ (pair_four_right _ _ _ _) ?_
    refine Q'.eqv_trans _ _ _ (fourQ_congr (fun j => ?_)) (fourQ_single i _)
    refine Q'.eqv_trans _ _ _ (cross_term_pair blocks block hb c d r hc hd hr i j) ?_
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, if_pos rfl]
      exact Q'.eqv_refl _
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rw [if_neg hv, if_neg hij]
      exact Q'.zero_mul_eqv _
  have left : weightedPair blocks r (four (term block c)) (four (term block d)) ≈
      fourQ (fun i => weightedPair blocks r (term block c i) (four (term block d))) := by
    exact Q'.eqv_trans _ _ _ (weighted_symm _ _ _ _)
      (Q'.eqv_trans _ _ _ (pair_four_right _ _ _ _)
        (fourQ_congr (fun i => weighted_symm _ _ _ _)))
  exact Q'.eqv_trans _ _ _ left (Q'.eqv_trans _ _ _ (fourQ_congr row)
    (Q'.eqv_trans _ _ _ (fourQ_scale quarter _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haar_four blocks r _)))))

private theorem coefficient_dot (p q : PolyQuaternion) :
    RatPolyCoeffEqv (four (fun i => polyMul (coefficients p i) (coefficients q i)))
      (PolyQuaternion.mul (PolyQuaternion.conj p) q).scalar :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 4)) (.add (.mul (.neg (.var 1)) (.neg (.var 5)))
      (.add (.mul (.neg (.var 2)) (.neg (.var 6))) (.mul (.neg (.var 3)) (.neg (.var 7))))))
    (PolyQuaternionExpr.mul (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))
      (PolyQuaternionExpr.coordinate 4)).scalar
    (by decide) (fun
      | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
      | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart)

/-- Exact shared-link trace fusion on the original carrier, with BOTH tails
and the unchanged spectator independent only of the integrated link.
No tail unit norm or independence between the two tails is assumed. -/
theorem fundamental_pair_moment (blocks block : Nat) (hb : block < blocks)
    (p q : PolyQuaternion) (r : RatPoly)
    (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hq : HasPolyQuaternionBlockDegree block 0 q)
    (hr : QuaternionBlockIndependent block r) :
    quaternionHaar blocks (polyMul
      (polyMul (characterPolynomial (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1)
        (characterPolynomial (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) q).scalar 1)) r) ≈
      quaternionHaar blocks (polyMul (PolyQuaternion.mul (PolyQuaternion.conj p) q).scalar r) := by
  let s := (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar
  let t := (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) q).scalar
  have hs : weightedPair blocks r s t ≈
      quarter * quaternionHaar blocks (polyMul (PolyQuaternion.mul (PolyQuaternion.conj p) q).scalar r) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (((scalar_eq_linear block p).mul (scalar_eq_linear block q)).mul_right r))
      (Q'.eqv_trans _ _ _
        (linear_cross_pair blocks block hb (coefficients p) (coefficients q) r
          (coefficients_independent hp) (coefficients_independent hq) hr)
        (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff ((coefficient_dot p q).mul_right r))))
  have hright : weightedPair blocks r s (polySmul 2 t) ≈ 2 * weightedPair blocks r s t :=
    Q'.eqv_trans _ _ _ (weighted_symm _ _ _ _)
      (Q'.eqv_trans _ _ _ (weighted_smul_left blocks r 2 t s)
        (Q'.mul_eqv_congr_left _ _ _ (weighted_symm _ _ _ _)))
  refine Q'.eqv_trans _ _ _ (weighted_smul_left blocks r 2 s (polySmul 2 t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ hright) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ (Q'.mul_eqv_congr_left 2 _ _ hs)) ?_
  have hnum : (((2 : Q')*2)*quarter) ≈ 1 := by decide
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 2 _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (2*2) quarter _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hnum) (Q'.one_mul_eqv _)))

#print axioms fundamental_first_moment
#print axioms fundamental_second_moment
#print axioms fundamental_pair_moment

end YMGap.Continuum.SU2QuaternionIndependentTailMoments
