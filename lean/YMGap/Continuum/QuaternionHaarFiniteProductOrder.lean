/-
# Pointwise order for the original finite product quaternion Haar

A supported signed rational polynomial bounded below on every explicit
rational unit-quaternion assignment has the same lower bound under the
ORIGINAL `quaternionHaar`. The proof integrates one actual head block at a
time, using the proved one-block rational sphere cubature order theorem.
The zero-block case and negative scalar bounds are included.

This is scalar order for a finite polynomial functional. It constructs no
algebraic positivity Certificate, compact-group measure, entropy estimate,
interacting spectral estimate, or continuum theory.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid
import YMGap.Continuum.SU2QuaternionTailEvaluation
import YMGap.Continuum.RatPolySubstitution

namespace YMGap.Continuum.QuaternionHaarFiniteProductOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq qpow evalMonoFrom evalMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (evalRatPoly_neg)
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair (environmentOf)

local infix:50 " ≈ " => Q'.eqv

/-- Explicit unit quaternions populate successive groups of four coordinates.
Values beyond the supplied polynomial support do not affect evaluation. -/
def environment (qs : Nat → UnitNorm) (index : Nat) : Q' :=
  environmentOf (qs (index/4)).val (index%4)

/-- The environment uses each supplied quaternion's actual four coordinates. -/
theorem environment_coordinate (qs : Nat → UnitNorm) (block : Nat) (a : Fin 4) :
    environment qs (4*block+a.val) =
      YMGap.RepTheory.RationalQuaternionNormRepair.coordinate (qs block).val a := by
  have ha := a.isLt
  have hd : (4*block+a.val)/4=block := by omega
  have hm : (4*block+a.val)%4=a.val := by omega
  simp only [environment, hd, hm]
  exact QuaternionHaarTensorBernsteinRepair.environmentOf_coordinate _ a

private def prepend (head : UnitNorm) (tail : Nat → UnitNorm) : Nat → UnitNorm
  | 0 => head
  | n+1 => tail n

private def splice (keep : Nat) (head tail : Nat → Q') (i : Nat) : Q' :=
  if i < keep then head i else tail (i-keep)

private theorem environment_prepend (head : UnitNorm) (tail : Nat → UnitNorm) :
    environment (prepend head tail) = splice 4 (environmentOf head.val) (environment tail) := by
  funext i
  cases (inferInstance : Decidable (i < 4)) with
  | isTrue hi =>
      simp only [environment, splice, hi, if_true, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, prepend]
  | isFalse hi =>
      have hd : i/4=(i-4)/4+1 := by omega
      have hm : i%4=(i-4)%4 := by omega
      simp only [environment, splice, hi, if_false, hd, hm, prepend]

private theorem mono_shift (rho : Nat → Q') (s : Nat) : ∀ (m : List Nat) (i : Nat),
    evalMonoFrom rho (s+i) m = evalMonoFrom (fun j => rho (s+j)) i m
  | [], _ => rfl
  | _::m, i => by
      simp only [evalMonoFrom]
      rw [show s+i+1=s+(i+1) from Nat.add_assoc _ _ _, mono_shift rho s m (i+1)]

private theorem mono_cons (rho : Nat → Q') (e : Nat) (m : List Nat) :
    evalMono rho (e::m) = qpow (rho 0) e * evalMono (fun j => rho (j+1)) m := by
  unfold evalMono
  simp only [evalMonoFrom]
  congr 1
  simpa only [Nat.add_zero, Nat.add_comm] using mono_shift rho 1 m 0

private theorem mono_splice : ∀ (keep : Nat) (head tail : Nat → Q') (m : List Nat),
    evalMono (splice keep head tail) m ≈
      evalMono head (m.take keep) * evalMono tail (m.drop keep)
  | 0, head, tail, m => by
      simpa only [splice, Nat.not_lt_zero, if_false, Nat.sub_zero, List.take_zero,
        List.drop_zero, evalMono, evalMonoFrom] using
        Q'.eqv_symm (Q'.one_mul_eqv (evalMono tail m))
  | keep+1, head, tail, [] => by
      change (1 : Q') ≈ 1*1
      decide
  | keep+1, head, tail, e::m => by
      rw [mono_cons, List.take_succ_cons, List.drop_succ_cons, mono_cons]
      have hshift : (fun j => splice (keep+1) head tail (j+1)) =
          splice keep (fun j => head (j+1)) tail := by
        funext j
        unfold splice
        cases (inferInstance : Decidable (j < keep)) with
        | isTrue hj => simp only [hj, Nat.succ_lt_succ_iff, if_true]
        | isFalse hj =>
            simp only [hj, Nat.succ_lt_succ_iff, if_false, Nat.add_sub_add_right]
      rw [hshift]
      have hzero : splice (keep+1) head tail 0 = head 0 := by simp [splice]
      rw [hzero]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (mono_splice keep (fun j => head (j+1)) tail m))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem evaluate_eval (keep : Nat) (head tail : Nat → Q') : ∀ p : RatPoly,
    evalRatPoly head (evaluateTail keep tail p) ≈ evalRatPoly (splice keep head tail) p
  | [] => Q'.eqv_refl _
  | t::p => by
      refine Q'.add_eqv_congr' ?_ (evaluate_eval keep head tail p)
      change (t.2*evalMono tail (t.1.drop keep))*evalMono head (t.1.take keep) ≈ _
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.var 2) (.var 1)))
          (by decide) (fun | 0 => t.2 | 1 => evalMono tail (t.1.drop keep) | _ => evalMono head (t.1.take keep)))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (mono_splice keep head tail t.1)))

private theorem evaluated_supported (rho : Nat → Q') (p : RatPoly) :
    SupportedQuaternionBlocks 1 (evaluateTail 4 rho p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change (s.1.take 4).length ≤ 4
  rw [List.length_take]
  exact Nat.min_le_left _ _

private theorem partial_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks+1) p) :
    SupportedQuaternionBlocks blocks (partialHaarHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have h := hp s hs
  simp only [partialHaarHeadTerm, List.length_drop]
  omega

private theorem weighted_haar (blocks : Nat) : ∀ p : RatPoly,
    ratWeightedSum (quaternionHaarMono blocks) p = quaternionHaar blocks p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*quaternionHaarMono blocks t.1+z) (weighted_haar blocks p)

private theorem haar_congr (blocks : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  simpa only [weighted_haar] using h (quaternionHaarMono blocks)

private theorem haar_zero_evaluate (rho : Nat → Q') : ∀ p : RatPoly,
    quaternionHaar 0 (evaluateTail 0 rho p) ≈ evalRatPoly rho p
  | [] => Q'.eqv_refl _
  | t::p => by
      change (t.2*evalMono rho t.1)*1 + quaternionHaar 0 (evaluateTail 0 rho p) ≈ _
      exact Q'.add_eqv_congr' (Q'.mul_one_eqv _) (haar_zero_evaluate rho p)

private theorem fixed_head_integral (rho : Nat → Q') (p : RatPoly) :
    quaternionHaar 1 (evaluateTail 4 rho p) ≈ evalRatPoly rho (partialHaarHead p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead 0 _))
    (Q'.eqv_trans _ _ _ (haar_congr 0 (partialHaarHead_evaluate 0 rho p))
      (haar_zero_evaluate rho _))

private theorem zero_supported_eval (rho : Nat → Q') : ∀ p : RatPoly,
    SupportedQuaternionBlocks 0 p → evalRatPoly rho p ≈ quaternionHaar 0 p
  | [], _ => Q'.eqv_refl _
  | t::p, hp => by
      have hlen : t.1.length=0 := Nat.eq_zero_of_le_zero (hp t List.mem_cons_self)
      have hm : t.1=[] := List.length_eq_zero_iff.mp hlen
      change t.2*evalMono rho t.1 + evalRatPoly rho p ≈
        t.2*quaternionHaarMono 0 t.1 + quaternionHaar 0 p
      rw [hm]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (zero_supported_eval rho p (fun s hs => hp s (List.mem_cons_of_mem t hs)))

/-- ORIGINAL finite-product Haar preserves any rational pointwise lower bound
on explicit rational unit-quaternion assignments. Coefficients and c may be signed. -/
theorem haar_lower_bound : ∀ (blocks : Nat) (p : RatPoly),
    SupportedQuaternionBlocks blocks p → ∀ c : Q',
    (∀ qs : Nat → UnitNorm, c ≤ evalRatPoly (environment qs) p) →
    c ≤ quaternionHaar blocks p
  | 0, p, hp, c, hlow =>
      Q'.le_trans' _ _ _ (hlow (fun _ => unitOne))
        (Q'.le_of_eqv (zero_supported_eval _ p hp))
  | blocks+1, p, hp, c, hlow => by
      have hpartial : ∀ qs : Nat → UnitNorm,
          c ≤ evalRatPoly (environment qs) (partialHaarHead p) := by
        intro qs
        have hhead : c ≤ quaternionHaar 1 (evaluateTail 4 (environment qs) p) := by
          apply QuaternionHaarTensorBernsteinPolynomialGrid.haar_lower_bound _ (evaluated_supported _ _) c
          intro head
          have hpin := evaluate_eval 4 (environmentOf head.val) (environment qs) p
          rw [← environment_prepend head qs] at hpin
          exact Q'.le_trans' _ _ _ (hlow (prepend head qs)) (Q'.ge_of_eqv hpin)
        exact Q'.le_trans' _ _ _ hhead (Q'.le_of_eqv (fixed_head_integral _ _))
      exact Q'.le_trans' _ _ _
        (haar_lower_bound blocks (partialHaarHead p) (partial_supported hp) c hpartial)
        (Q'.le_of_eqv (quaternionHaar_partialHaarHead blocks p))

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks p)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- The corresponding upper bound, with no sign restriction on the bound. -/
theorem haar_upper_bound (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (c : Q')
    (hupp : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) p ≤ c) :
    quaternionHaar blocks p ≤ c := by
  have h : -c ≤ quaternionHaar blocks (polyNeg p) := haar_lower_bound blocks _ (supported_neg hp) (-c)
    (fun qs => Q'.le_trans' _ _ _ (Q'.neg_le_neg (hupp qs))
      (Q'.ge_of_eqv (evalRatPoly_neg (environment qs) p)))
  have hn := Q'.neg_le_neg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_neg blocks p)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv _))
    (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.neg_neg_eqv _)))

/-- Shared-carrier pointwise polynomial order passes to the same finite Haar. -/
theorem haar_mono (blocks : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (hle : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) p ≤ evalRatPoly (environment qs) q) :
    quaternionHaar blocks p ≤ quaternionHaar blocks q := by
  have hs : SupportedQuaternionBlocks blocks (polyAdd q (polyNeg p)) := by
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact hq t h
    · exact supported_neg hp t h
  have h := haar_lower_bound blocks (polyAdd q (polyNeg p)) hs 0 (fun qs =>
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le (hle qs))
      (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (evalRatPoly_add (environment qs) q (polyNeg p))
        (Q'.add_eqv_congr_left _ _ _ (evalRatPoly_neg (environment qs) p)))))
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (BF4CompactActionCPOrder.quaternionHaar_append blocks q (polyNeg p))
    (Q'.add_eqv_congr_left _ _ _ (haar_neg blocks p))))

end YMGap.Continuum.QuaternionHaarFiniteProductOrder

#print axioms YMGap.Continuum.QuaternionHaarFiniteProductOrder.environment
#print axioms YMGap.Continuum.QuaternionHaarFiniteProductOrder.environment_coordinate
#print axioms YMGap.Continuum.QuaternionHaarFiniteProductOrder.haar_lower_bound
#print axioms YMGap.Continuum.QuaternionHaarFiniteProductOrder.haar_upper_bound
#print axioms YMGap.Continuum.QuaternionHaarFiniteProductOrder.haar_mono
