/-
# Push the corrected-slab support Gram to finite local fingerprints

The support-pushed Gram is indexed by complete lower-half occupied supports.
A local observable must not force every unqueried face to be empty.  We
therefore push the complete support-pair kernel through an arbitrary finite
Boolean support code.  Each target entry sums every full support in that
fingerprint fiber, and the local-fingerprint quadratic is exactly the original
normalized support quadratic with the coefficient pulled back along the code.
-/

import YMGap.Continuum.FiniteJointKernelPushforward
import YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw

namespace YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteJointKernelPushforward
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

local infix:50 " ≈ " => Q'.eqv

/-- The duplicate-free list of local Boolean fingerprints actually attained
by complete lower-half supports. -/
def centralLocalSupportFingerprintSpace
    (half : Nat) (code : List Nat → List Bool) : List (List Bool) :=
  ((centralHalfSupportSpace half).map code).eraseDups

private theorem filtered_eraseDups_nodup_local {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) :
    ∀ predicate : A → Bool, (xs.filter predicate).eraseDups.Nodup := by
  induction xs with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun item => (!(item == head)) && predicate item)⟩
        intro hmem
        have hmem' : head ∈ tail.filter
            (fun item => (!(item == head)) && predicate item) :=
          List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hmem').2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih predicate

private theorem filter_true_local {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => true) = xs
  | [] => rfl
  | head :: tail =>
      congrArg (List.cons head) (filter_true_local tail)

private theorem eraseDups_nodup_local {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) : xs.eraseDups.Nodup := by
  have h := filtered_eraseDups_nodup_local xs (fun _ => true)
  rw [filter_true_local] at h
  exact h

theorem centralLocalSupportFingerprintSpace_nodup
    (half : Nat) (code : List Nat → List Bool) :
    (centralLocalSupportFingerprintSpace half code).Nodup := by
  unfold centralLocalSupportFingerprintSpace
  exact eraseDups_nodup_local _

theorem centralLocalSupportFingerprint_mem
    (half : Nat) (code : List Nat → List Bool)
    {support : List Nat}
    (hsupport : support ∈ centralHalfSupportSpace half) :
    code support ∈ centralLocalSupportFingerprintSpace half code := by
  unfold centralLocalSupportFingerprintSpace
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨support, hsupport, rfl⟩

/-- Normalized corrected-slab joint law pushed from full supports to local
Boolean fingerprints. -/
def centralNormalizedLocalSupportPairLaw
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (code : List Nat → List Bool)
    (left right : List Bool) : Q' :=
  finiteJointKernelPushforward
    (centralHalfSupportSpace half)
    (centralNormalizedSupportPairLaw w hw K half)
    code left right

/-- Pull a coefficient on local fingerprints back to complete supports. -/
def centralLocalSupportCoefficient
    (code : List Nat → List Bool)
    (coefficient : List Bool → Q') (support : List Nat) : Q' :=
  coefficient (code support)

/-- Exact local-fingerprint reindexing of the complete normalized support
quadratic.  Every unqueried support coordinate has been summed in a fiber. -/
theorem centralNormalizedSupportReflectionQuadratic_eq_localJointLaw
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (code : List Nat → List Bool)
    (coefficient : List Bool → Q') :
    centralNormalizedSupportReflectionQuadratic w hw K half
        (centralLocalSupportCoefficient code coefficient) ≈
      finiteJointQuadratic
        (centralLocalSupportFingerprintSpace half code)
        coefficient
        (centralNormalizedLocalSupportPairLaw w hw K half code) := by
  have hsupport :=
    centralNormalizedSupportReflectionQuadratic_eq_jointLaw
      w hw K half (centralLocalSupportCoefficient code coefficient)
  have hpush := finiteJointQuadratic_pushforward_eqv_pullback
    (centralHalfSupportSpace half)
    (centralNormalizedSupportPairLaw w hw K half)
    code (centralLocalSupportFingerprintSpace half code)
    (centralLocalSupportFingerprintSpace_nodup half code)
    (fun support hsupport =>
      centralLocalSupportFingerprint_mem half code hsupport)
    coefficient
  exact Q'.eqv_trans _ _ _ hsupport (Q'.eqv_symm hpush)

theorem centralNormalizedLocalSupportQuadratic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (code : List Nat → List Bool)
    (coefficient : List Bool → Q') :
    (0 : Q') ≤
      finiteJointQuadratic
        (centralLocalSupportFingerprintSpace half code)
        coefficient
        (centralNormalizedLocalSupportPairLaw w hw K half code) := by
  exact Q'.le_trans' _ _ _
    (centralNormalizedSupportReflectionQuadratic_nonnegative
      w hw K half (centralLocalSupportCoefficient code coefficient))
    (Q'.le_of_eqv
      (centralNormalizedSupportReflectionQuadratic_eq_localJointLaw
        w hw K half code coefficient))

#print axioms centralLocalSupportFingerprintSpace_nodup
#print axioms centralLocalSupportFingerprint_mem
#print axioms centralNormalizedSupportReflectionQuadratic_eq_localJointLaw
#print axioms centralNormalizedLocalSupportQuadratic_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
