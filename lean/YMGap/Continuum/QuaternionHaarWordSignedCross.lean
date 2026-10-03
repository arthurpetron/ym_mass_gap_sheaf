/-
# Exact signed cross cost of the ORIGINAL ordered quaternion telescope

All four coordinate squares are expanded before charging any diagonal.
The cross polynomial lists each positional pair once and retains every
literal ordered prefix/suffix. No sign, independence or source-order
assumption is made about the cross cost. This is finite polynomial/Haar
algebra, not a variance-relative or changing-family estimate.
-/

import YMGap.Continuum.QuaternionHaarWordComponents

namespace YMGap.Continuum.QuaternionHaarWordSignedCross

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (polyQuaternionNorm_one haarNorm_mul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarWordComponents
open YMGap.Continuum.QuaternionHaarFamilySquare

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private def coordSum (ts : List PolyQuaternion) (i : Nat) : RatPoly :=
  polySum (ts.map (component i))

private def coordDiag (ts : List PolyQuaternion) (i : Nat) : RatPoly :=
  polySum (ts.map (fun t => polyMul (component i t) (component i t)))

private def vectorSum (ts : List PolyQuaternion) : PolyQuaternion :=
  ⟨coordSum ts 0, coordSum ts 1, coordSum ts 2, coordSum ts 3⟩

/-- Actual signed pair sum in all four coordinates; positional repetitions
are preserved, even when two increments happen to be equal. -/
def termCrossPolynomial (ts : List PolyQuaternion) : RatPoly :=
  polyAdd (crossSum (component 0) ts)
    (polyAdd (crossSum (component 1) ts)
      (polyAdd (crossSum (component 2) ts) (crossSum (component 3) ts)))

def wordCrossPolynomial (left right : OrientedBF4Link → PolyQuaternion)
    (es : List OrientedBF4Link) : RatPoly :=
  termCrossPolynomial (terms left right PolyQuaternion.one es)

def wordDiagonalPolynomial (left right : OrientedBF4Link → PolyQuaternion)
    (es : List OrientedBF4Link) : RatPoly :=
  polySum ((terms left right PolyQuaternion.one es).map polyQuaternionNorm)

private theorem norm_congr {p q : PolyQuaternion} (h : PolyQuaternionCoeffEqv p q) :
    RatPolyCoeffEqv (polyQuaternionNorm p) (polyQuaternionNorm q) :=
  (h.scalar.mul h.scalar).add
    ((h.iPart.mul h.iPart).add ((h.jPart.mul h.jPart).add (h.kPart.mul h.kPart)))

private theorem difference_congr {p q r s : PolyQuaternion}
    (hp : PolyQuaternionCoeffEqv p q) (hr : PolyQuaternionCoeffEqv r s) :
    PolyQuaternionCoeffEqv (difference p r) (difference q s) :=
  ⟨hp.scalar.add (RatPolyCoeffEqv.neg hr.scalar),
    hp.iPart.add (RatPolyCoeffEqv.neg hr.iPart),
    hp.jPart.add (RatPolyCoeffEqv.neg hr.jPart),
    hp.kPart.add (RatPolyCoeffEqv.neg hr.kPart)⟩

private theorem diagonal_coordinates (ts : List PolyQuaternion) :
    RatPolyCoeffEqv (polySum (ts.map polyQuaternionNorm))
      (polyAdd (coordDiag ts 0) (polyAdd (coordDiag ts 1)
        (polyAdd (coordDiag ts 2) (coordDiag ts 3)))) := by
  induction ts with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons t ts ih =>
      have h := (RatPolyCoeffEqv.refl (polyQuaternionNorm t)).add ih
      exact h.trans (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
          (.add (.var 4) (.add (.var 5) (.add (.var 6) (.var 7)))))
        (.add (.add (.mul (.var 0) (.var 0)) (.var 4))
          (.add (.add (.mul (.var 1) (.var 1)) (.var 5))
            (.add (.add (.mul (.var 2) (.var 2)) (.var 6))
              (.add (.mul (.var 3) (.var 3)) (.var 7)))))
        (by decide) (fun
          | 0 => t.scalar | 1 => t.iPart | 2 => t.jPart | 3 => t.kPart
          | 4 => coordDiag ts 0 | 5 => coordDiag ts 1
          | 6 => coordDiag ts 2 | _ => coordDiag ts 3))

private theorem vector_expansion (ts : List PolyQuaternion) :
    RatPolyCoeffEqv (polyQuaternionNorm (vectorSum ts))
      (polyAdd (polySum (ts.map polyQuaternionNorm))
        (polyAdd (termCrossPolynomial ts) (termCrossPolynomial ts))) := by
  have h0 := sumSquare_expansion (component 0) ts
  have h1 := sumSquare_expansion (component 1) ts
  have h2 := sumSquare_expansion (component 2) ts
  have h3 := sumSquare_expansion (component 3) ts
  rw [diagonalSum_eq] at h0 h1 h2 h3
  have h := h0.add (h1.add (h2.add h3))
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.add (.var 4) (.var 4)))
      (.add (.add (.var 1) (.add (.var 5) (.var 5)))
        (.add (.add (.var 2) (.add (.var 6) (.var 6)))
          (.add (.var 3) (.add (.var 7) (.var 7))))))
    (.add (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3))))
      (.add (.add (.var 4) (.add (.var 5) (.add (.var 6) (.var 7))))
        (.add (.var 4) (.add (.var 5) (.add (.var 6) (.var 7))))))
    (by decide) (fun
      | 0 => coordDiag ts 0 | 1 => coordDiag ts 1
      | 2 => coordDiag ts 2 | 3 => coordDiag ts 3
      | 4 => crossSum (component 0) ts | 5 => crossSum (component 1) ts
      | 6 => crossSum (component 2) ts | _ => crossSum (component 3) ts)
  exact h.trans (hr.trans ((diagonal_coordinates ts).symm.add
    (RatPolyCoeffEqv.refl _)))

/-- Exact whole-word norm decomposition. No quaternion factor is commuted. -/
theorem word_norm_cross_expansion (left right : OrientedBF4Link → PolyQuaternion)
    (es : List OrientedBF4Link) :
    RatPolyCoeffEqv
      (polyQuaternionNorm (difference (wordWith left es) (wordWith right es)))
      (polyAdd (wordDiagonalPolynomial left right es)
        (polyAdd (wordCrossPolynomial left right es) (wordCrossPolynomial left right es))) := by
  have ht := terms_components left right PolyQuaternion.one es
  have hw := difference_congr (PolyQuaternionCoeffEqv.one_mul (wordWith left es))
    (PolyQuaternionCoeffEqv.one_mul (wordWith right es))
  exact (norm_congr (ht.trans hw)).symm.trans
    (vector_expansion (terms left right PolyQuaternion.one es))

/-- Haar integration retains the complete weight, including any overlapping
source variables. The signed cross is not replaced by an absolute cost. -/
theorem word_weighted_cross_identity (blocks : Nat) (W : RatPoly)
    (left right : OrientedBF4Link → PolyQuaternion) (es : List OrientedBF4Link) :
    quaternionHaar blocks (polyMul W
      (polyQuaternionNorm (difference (wordWith left es) (wordWith right es)))) ≈
      quaternionHaar blocks (polyMul W (wordDiagonalPolynomial left right es)) +
        2*quaternionHaar blocks (polyMul W (wordCrossPolynomial left right es)) := by
  have h := haar_of_coeff (blocks := blocks) ((word_norm_cross_expansion left right es).mul_left W)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (haar_weighted_add blocks W _ _) (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (haar_weighted_add blocks W _ _))
      (poly_identity_of_normal_eq (.add (.var 0) (.add (.var 1) (.var 1)))
        (.add (.var 0) (.mul (.const 2) (.var 1))) (by decide) (fun
          | 0 => quaternionHaar blocks (polyMul W (wordDiagonalPolynomial left right es))
          | _ => quaternionHaar blocks (polyMul W (wordCrossPolynomial left right es))))))

/-- The exact diagonal cancels unit prefixes and suffixes under arbitrary
insertions, but leaves every signed cross untouched. -/
theorem terms_diagonal_pin {n : Nat} (left right : OrientedBF4Link → PolyQuaternion) :
    ∀ (p : PolyQuaternion) (es : List OrientedBF4Link),
      HaarCarrierEqv n (polyQuaternionNorm p) polyOne →
      (∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne) →
      (∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne) →
      HaarCarrierEqv n (polySum ((terms left right p es).map polyQuaternionNorm))
        (polySum (es.map (fun e => polyQuaternionNorm (difference (left e) (right e)))))
  | _, [], _, _, _ => HaarCarrierEqv.refl n _
  | p, e::es, hp, hl, hr =>
      HaarCarrierEqv.add
        (unit_sandwich_norm hp
          (word_unit right es (fun f hf => hr f (List.mem_cons_of_mem e hf))) _)
        (terms_diagonal_pin left right (p ⋄ left e) es
          (haarNorm_mul hp (hl e List.mem_cons_self))
          (fun f hf => hl f (List.mem_cons_of_mem e hf))
          (fun f hf => hr f (List.mem_cons_of_mem e hf)))

private theorem sum_bound (B : Q') : ∀ xs : List Q',
    (∀ x, x ∈ xs → x ≤ B) → qListSum xs ≤ Q'.ofNat xs.length*B
  | [], _ => Q'.ge_of_eqv (Q'.zero_mul_eqv B)
  | x::xs, h => by
      have hs := Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ (h x List.mem_cons_self))
        (Q'.add_le_add_left _ _ _
          (sum_bound B xs (fun y hy => h y (List.mem_cons_of_mem x hy))))
      have he : Q'.ofNat (xs.length+1)*B ≈ B+Q'.ofNat xs.length*B :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv _ _))
          (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
            (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv B))
              (Q'.add_comm_eqv _ _)))
      exact Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv he)

/-- Only the diagonal pays length times the literal per-link bound. -/
theorem word_diagonal_bound {n : Nat} (W : RatPoly) (B : Q')
    (left right : OrientedBF4Link → PolyQuaternion) (es : List OrientedBF4Link)
    (hl : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne)
    (hr : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne)
    (hb : ∀ e, e ∈ es → quaternionHaar n
      (polyMul W (polyQuaternionNorm (difference (left e) (right e)))) ≤ B) :
    quaternionHaar n (polyMul W (wordDiagonalPolynomial left right es)) ≤
      Q'.ofNat es.length*B := by
  let ts := terms left right PolyQuaternion.one es
  have ht := terms_norm_bound W B left right PolyQuaternion.one es
    (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one) hl hr hb
  have he := haar_weighted_sum_indexed n W polyQuaternionNorm ts
  have hs := sum_bound B
    (ts.map (fun t => quaternionHaar n (polyMul W (polyQuaternionNorm t))))
    (by
      intro x hx
      obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hx
      exact ht t ht')
  simp only [List.length_map, ts, terms_length] at hs
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hs

#print axioms termCrossPolynomial
#print axioms wordCrossPolynomial
#print axioms wordDiagonalPolynomial
#print axioms word_norm_cross_expansion
#print axioms word_weighted_cross_identity
#print axioms terms_diagonal_pin
#print axioms word_diagonal_bound

end YMGap.Continuum.QuaternionHaarWordSignedCross
