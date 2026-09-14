/-
# Ignore only zero exponent padding, including under arbitrary insertions

The existing sparse checker records EVERY nonzero exponent, not merely the
coordinates of a chosen carrier. Its soundness therefore extends to Haar
with arbitrary insertions, including polynomials not syntactically supported
on that carrier. Nonzero out-of-carrier exponents are not dropped.
-/

import YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.SU2QuaternionHaarSparseEquality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

local infix:50 " ≈ " => Q'.eqv

private theorem allZero_iff : ∀ m : List Nat,
    allZero m = true ↔ ∀ i, exponentAt m i = 0
  | [] => by simp [allZero, exponentAt]
  | a::m => by
    simp only [allZero, Bool.and_eq_true, decide_eq_true_eq, allZero_iff m]
    constructor
    · rintro ⟨rfl,h⟩ i
      cases i with
      | zero => rfl
      | succ i => exact h i
    · intro h
      exact ⟨h 0,fun i => h (i+1)⟩

private theorem prefix_congr (blocks : Nat) (m n : List Nat)
    (h : ∀ i, exponentAt m i = exponentAt n i) :
    quaternionHaarPrefix blocks m = quaternionHaarPrefix blocks n := by
  induction blocks generalizing m n with
  | zero => rfl
  | succ blocks ih =>
    simp only [quaternionHaarPrefix, h]
    rw [ih (m.drop 4) (n.drop 4) (fun i => by rw [exponentAt_drop, exponentAt_drop]; exact h _)]

theorem haarMono_congr (blocks : Nat) (m n : List Nat)
    (h : ∀ i, exponentAt m i = exponentAt n i) :
    quaternionHaarMono blocks m = quaternionHaarMono blocks n := by
  have hd : allZero (m.drop (4*blocks)) = allZero (n.drop (4*blocks)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [allZero_iff, exponentAt_drop, h]
  unfold quaternionHaarMono
  rw [hd, prefix_congr blocks m n h]

/-- The bound argument of the old checker is intentionally irrelevant:
the sparse code compares all nonzero coordinate/exponent pairs. -/
theorem check_prefix (blocks : Nat) : ∀ {p q : RatPoly},
    quaternionPrefixPolynomialCheck 0 p q = true → QuaternionPrefixPolynomialEqv blocks p q
  | [], [], _ => .nil
  | [], _::_, h => by contradiction
  | _::_, [], h => by contradiction
  | s::p, t::q, h => by
    change (quaternionPrefixTermCheck 0 s t && quaternionPrefixPolynomialCheck 0 p q) = true at h
    rw [Bool.and_eq_true] at h
    exact .cons (quaternionPrefixTermCheck_sound (blocks := blocks) h.1) (check_prefix blocks h.2)

theorem haar_of_all_prefix (blocks : Nat) {p q : RatPoly}
    (h : ∀ b, QuaternionPrefixPolynomialEqv b p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  induction p generalizing q with
  | nil => cases h 0; exact Q'.eqv_refl _
  | cons s p ih =>
    cases q with
    | nil => cases h 0
    | cons t q =>
      have ht (b : Nat) : QuaternionPrefixTermEqv b s t := by cases h b with | cons ht _ => exact ht
      have hr (b : Nat) : QuaternionPrefixPolynomialEqv b p q := by cases h b with | cons _ hr => exact hr
      have hm := haarMono_congr blocks s.1 t.1 (fun i => (ht (i+1)).exponent i (by omega))
      change s.2 * quaternionHaarMono blocks s.1 + quaternionHaar blocks p ≈ _
      rw [hm]
      exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (ht 0).coefficient) (ih hr)

theorem carrier_of_check (blocks : Nat) {p q : RatPoly}
    (h : quaternionPrefixPolynomialCheck 0 p q = true) : HaarCarrierEqv blocks p q := by
  intro insertion
  exact haar_of_all_prefix blocks (fun b => (QuaternionPrefixPolynomialEqv.refl b insertion).mul (check_prefix b h))

theorem carrier_of_canon_check (blocks : Nat) {p q : RatPoly}
    (h : quaternionPrefixPolynomialCheck 0 (canonRat p) (canonRat q) = true) :
    HaarCarrierEqv blocks p q := by
  intro insertion
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm blocks insertion p)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_canonRat_mul blocks p insertion))
      (Q'.eqv_trans _ _ _ (haar_of_carrier (HaarCarrierEqv.mul_right insertion (carrier_of_check blocks h)))
        (Q'.eqv_trans _ _ _ (quaternionHaar_canonRat_mul blocks q insertion)
          (quaternionHaar_polyMul_comm blocks q insertion))))

end YMGap.Continuum.SU2QuaternionHaarSparseEquality

#print axioms YMGap.Continuum.SU2QuaternionHaarSparseEquality.haarMono_congr
#print axioms YMGap.Continuum.SU2QuaternionHaarSparseEquality.check_prefix
#print axioms YMGap.Continuum.SU2QuaternionHaarSparseEquality.haar_of_all_prefix
#print axioms YMGap.Continuum.SU2QuaternionHaarSparseEquality.carrier_of_check
#print axioms YMGap.Continuum.SU2QuaternionHaarSparseEquality.carrier_of_canon_check
