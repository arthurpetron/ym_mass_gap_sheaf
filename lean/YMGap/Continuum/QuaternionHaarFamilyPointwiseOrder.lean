/-
# Pointwise order for original in-place quaternion Haar projections

Fix all spectator links at an explicit rational unit assignment. The four
selected exponents of each monomial give an actual one-block polynomial;
its original Haar integral is exactly the evaluation of `project`. Thus
the proved finite-product Haar order theorem supplies pointwise order for
the existing projection and every finite `familyProject` schedule.

Signed coefficients and scalar bounds are allowed. Schedules may repeat
indices or select indices beyond a polynomial's support: the explicit
one-block specialization still has support one. No positive Certificate,
conditional probability law, partition estimate, or uniform analytic
bound is assumed or constructed in this algebraic order lemma.
-/

import YMGap.Continuum.QuaternionHaarFiniteProductOrder
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection

namespace YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.RingNormaliser (evalMono evalMonoFrom qpow poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (exponentAt_drop)
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier (quaternionBlockMoment)
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
  (coordinateInQuaternionBlock clearQuaternionBlockFrom clearQuaternionBlock
   integrateQuaternionBlockTerm integrateQuaternionBlock)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment haar_lower_bound haar_mono)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem power_one : ∀ n : Nat, qpow (1 : Q') n ≈ 1
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (power_one n)

private theorem mono_one : ∀ (start : Nat) (m : List Nat),
    evalMonoFrom (fun _ => (1 : Q')) start m ≈ 1
  | _, [] => Q'.eqv_refl _
  | start, e::m => Q'.eqv_trans _ _ _ (mc (power_one e) (mono_one (start+1) m))
      (Q'.one_mul_eqv _)

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

private def window (start width : Nat) (head : Nat → Q') (k : Nat) : Q' :=
  if start ≤ k ∧ k < start+width then head (k-start) else 1

private theorem window_shift (start width : Nat) (head : Nat → Q') :
    (fun k => window (start+1) width head (k+1)) = window start width head := by
  funext k
  have he : start+1+width = start+width+1 := by omega
  simp only [window, he, Nat.succ_le_succ_iff, Nat.succ_lt_succ_iff,
    Nat.add_sub_add_right]

private theorem window_head_shift (width : Nat) (head : Nat → Q') :
    (fun k => window 0 (width+1) head (k+1)) =
      window 0 width (fun k => head (k+1)) := by
  funext k
  simp only [window, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and,
    Nat.succ_lt_succ_iff]

private theorem window_eval : ∀ (start width : Nat) (head : Nat → Q') (m : List Nat),
    evalMono (window start width head) m ≈ evalMono head ((m.drop start).take width)
  | 0, 0, head, m => by
      have he : window 0 0 head = fun _ => (1 : Q') := by
        funext k
        simp only [window, Nat.zero_add, Nat.not_lt_zero, and_false, if_false]
      rw [he, List.take_zero]
      exact mono_one 0 m
  | 0, width+1, _, [] => Q'.eqv_refl _
  | 0, width+1, head, e::m => by
      rw [mono_cons, List.drop_zero, List.take_succ_cons, mono_cons]
      have hz : window 0 (width+1) head 0 = head 0 := by
        simp only [window, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and,
          Nat.zero_lt_succ, if_true]
      rw [hz, window_head_shift]
      exact mc (Q'.eqv_refl _) (window_eval 0 width (fun j => head (j+1)) m)
  | start+1, _, _, [] => by
      simp only [List.drop_nil, List.take_nil]
      exact Q'.eqv_refl _
  | start+1, width, head, e::m => by
      rw [mono_cons, List.drop_succ_cons]
      have hz : window (start+1) width head 0 = 1 := by
        unfold window
        exact if_neg (fun h => Nat.not_succ_le_zero start h.1)
      rw [hz, window_shift]
      exact Q'.eqv_trans _ _ _ (mc (power_one e) (window_eval start width head m))
        (Q'.one_mul_eqv _)

private def replaceEnvironment (block : Nat) (head rho : Nat → Q') (k : Nat) : Q' :=
  if coordinateInQuaternionBlock block k then head (k-4*block) else rho k

private theorem mono_split (block : Nat) (head rho : Nat → Q') :
    ∀ (start : Nat) (m : List Nat),
    evalMonoFrom (replaceEnvironment block head rho) start m ≈
      evalMonoFrom (window (4*block) 4 head) start m *
        evalMonoFrom rho start (clearQuaternionBlockFrom block start m)
  | _, [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | start, e::m => by
      have hh : qpow (replaceEnvironment block head rho start) e ≈
          qpow (window (4*block) 4 head start) e *
            qpow (rho start) (if coordinateInQuaternionBlock block start then 0 else e) := by
        by_cases h : coordinateInQuaternionBlock block start
        · change 4*block ≤ start ∧ start < 4*block+4 at h
          simp only [replaceEnvironment, coordinateInQuaternionBlock, window, if_pos h]
          exact Q'.eqv_symm (Q'.mul_one_eqv _)
        · change ¬ (4*block ≤ start ∧ start < 4*block+4) at h
          simp only [replaceEnvironment, coordinateInQuaternionBlock, window, if_neg h]
          exact Q'.eqv_symm (Q'.eqv_trans _ _ _
            (mc (power_one e) (Q'.eqv_refl _)) (Q'.one_mul_eqv _))
      change _ * evalMonoFrom (replaceEnvironment block head rho) (start+1) m ≈
        (_ * evalMonoFrom (window (4*block) 4 head) (start+1) m) *
          (_ * evalMonoFrom rho (start+1) (clearQuaternionBlockFrom block (start+1) m))
      exact Q'.eqv_trans _ _ _ (mc hh (mono_split block head rho (start+1) m))
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
          (fun | 0 => qpow (window (4*block) 4 head start) e
               | 1 => qpow (rho start) (if coordinateInQuaternionBlock block start then 0 else e)
               | 2 => evalMonoFrom (window (4*block) 4 head) (start+1) m
               | _ => evalMonoFrom rho (start+1) (clearQuaternionBlockFrom block (start+1) m)))

private theorem selected_mono (block : Nat) (head rho : Nat → Q') (m : List Nat) :
    evalMono (replaceEnvironment block head rho) m ≈
      evalMono head ((m.drop (4*block)).take 4) * evalMono rho (clearQuaternionBlock block m) :=
  Q'.eqv_trans _ _ _ (mono_split block head rho 0 m)
    (mc (window_eval (4*block) 4 head m) (Q'.eqv_refl _))

/-- Evaluate every spectator and retain the selected four exponents as one
literal quaternion block. This is a finite polynomial, not a conditional law. -/
def fixedBlockPolynomial (block : Nat) (rho : Nat → Q') (p : RatPoly) : RatPoly :=
  p.map (fun t => ((t.1.drop (4*block)).take 4,
    t.2 * evalMono rho (clearQuaternionBlock block t.1)))

theorem fixedBlockPolynomial_supported (block : Nat) (rho : Nat → Q') (p : RatPoly) :
    SupportedQuaternionBlocks 1 (fixedBlockPolynomial block rho p) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  change ((s.1.drop (4*block)).take 4).length ≤ 4
  rw [List.length_take]
  exact Nat.min_le_left _ _

private theorem fixed_eval (block : Nat) (head rho : Nat → Q') : ∀ p : RatPoly,
    evalRatPoly head (fixedBlockPolynomial block rho p) ≈
      evalRatPoly (replaceEnvironment block head rho) p
  | [] => Q'.eqv_refl _
  | t::p => by
      refine Q'.add_eqv_congr' ?_ (fixed_eval block head rho p)
      change (t.2 * evalMono rho (clearQuaternionBlock block t.1)) *
          evalMono head ((t.1.drop (4*block)).take 4) ≈ _
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
          (fun | 0 => t.2 | 1 => evalMono rho (clearQuaternionBlock block t.1)
               | _ => evalMono head ((t.1.drop (4*block)).take 4)))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (selected_mono block head rho t.1)))

private theorem exponent_take (m : List Nat) : ∀ n i, i < n →
    exponentAt (m.take n) i = exponentAt m i
  | 0, _, hi => False.elim (Nat.not_lt_zero _ hi)
  | n+1, 0, _ => by cases m <;> rfl
  | n+1, i+1, hi => by
      cases m with
      | nil => rfl
      | cons _ m => exact exponent_take m n i (Nat.lt_of_succ_lt_succ hi)

private theorem selected_moment (block : Nat) (m : List Nat) :
    quaternionHaarMono 1 ((m.drop (4*block)).take 4) ≈ quaternionBlockMoment block m := by
  have hd : ((m.drop (4*block)).take 4).drop 4 = [] :=
    List.drop_eq_nil_iff.mpr (by rw [List.length_take]; exact Nat.min_le_left _ _)
  simp only [quaternionHaarMono, show 4*1=4 from rfl, hd, allZero, if_true,
    quaternionHaarPrefix]
  refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ?_
  unfold quaternionBlockMoment
  rw [exponent_take _ 4 0 (by decide), exponent_take _ 4 1 (by decide),
    exponent_take _ 4 2 (by decide), exponent_take _ 4 3 (by decide),
    exponentAt_drop, exponentAt_drop, exponentAt_drop, exponentAt_drop, Nat.add_zero]
  exact Q'.eqv_refl _

/-- The original one-block Haar of the explicit specialization equals
the original in-place projection evaluated at the fixed spectators. -/
theorem fixedBlockPolynomial_haar (block : Nat) (rho : Nat → Q') : ∀ p : RatPoly,
    quaternionHaar 1 (fixedBlockPolynomial block rho p) ≈
      evalRatPoly rho (project block p)
  | [] => Q'.eqv_refl _
  | t::p => by
      refine Q'.add_eqv_congr' ?_ (fixedBlockPolynomial_haar block rho p)
      change (t.2 * evalMono rho (clearQuaternionBlock block t.1)) *
          quaternionHaarMono 1 ((t.1.drop (4*block)).take 4) ≈
        (t.2 * quaternionBlockMoment block t.1) * evalMono rho (clearQuaternionBlock block t.1)
      exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (selected_moment block t.1))
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
          (fun | 0 => t.2 | 1 => evalMono rho (clearQuaternionBlock block t.1)
               | _ => quaternionBlockMoment block t.1))

/-- Keep every other original link, replacing exactly one supplied unit. -/
def updateAssignment (block : Nat) (head : UnitNorm) (qs : Nat → UnitNorm)
    (k : Nat) : UnitNorm := if k = block then head else qs k

private theorem environment_update (block : Nat) (heads qs : Nat → UnitNorm) :
    environment (updateAssignment block (heads 0) qs) =
      replaceEnvironment block (environment heads) (environment qs) := by
  funext k
  have hm := Nat.mod_lt k (by decide : 0 < 4)
  by_cases hb : k/4 = block
  · have hin : coordinateInQuaternionBlock block k := ⟨by omega, by omega⟩
    have hr : k-4*block = k%4 := by omega
    simp only [environment, updateAssignment, hb, if_true, replaceEnvironment,
      if_pos hin, hr, Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
  · have hout : ¬ coordinateInQuaternionBlock block k := by
      intro h
      apply hb
      have h0 := h.1
      have h1 := h.2
      omega
    simp only [environment, updateAssignment, if_neg hb, replaceEnvironment, if_neg hout]

/-- Exact original-assignment evaluation pin. Only the selected unit changes;
all coefficients and spectator variables of the original polynomial remain. -/
theorem fixedBlockPolynomial_evaluate (block : Nat) (heads qs : Nat → UnitNorm) (p : RatPoly) :
    evalRatPoly (environment heads) (fixedBlockPolynomial block (environment qs) p) ≈
      evalRatPoly (environment (updateAssignment block (heads 0) qs)) p := by
  rw [environment_update]
  exact fixed_eval block (environment heads) (environment qs) p

/-- In-place original Haar projection preserves a signed scalar lower bound
at EVERY fixed boundary assignment. No support or index restriction is needed. -/
theorem project_pointwise_lower_bound (block : Nat) (p : RatPoly) (c : Q')
    (h : ∀ qs : Nat → UnitNorm, c ≤ evalRatPoly (environment qs) p)
    (qs : Nat → UnitNorm) : c ≤ evalRatPoly (environment qs) (project block p) := by
  have hh := haar_lower_bound 1 (fixedBlockPolynomial block (environment qs) p)
    (fixedBlockPolynomial_supported block (environment qs) p) c (fun heads =>
      Q'.le_trans' _ _ _ (h (updateAssignment block (heads 0) qs))
        (Q'.ge_of_eqv (fixedBlockPolynomial_evaluate block heads qs p)))
  exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (fixedBlockPolynomial_haar block (environment qs) p))

/-- Original in-place projection preserves pointwise polynomial order on
explicit rational unit assignments, with arbitrary signed coefficients. -/
theorem project_pointwise_mono (block : Nat) (p q : RatPoly)
    (h : ∀ qs : Nat → UnitNorm,
      evalRatPoly (environment qs) p ≤ evalRatPoly (environment qs) q)
    (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs) (project block p) ≤
      evalRatPoly (environment qs) (project block q) := by
  have hh := haar_mono 1 (fixedBlockPolynomial block (environment qs) p)
    (fixedBlockPolynomial block (environment qs) q)
    (fixedBlockPolynomial_supported block (environment qs) p)
    (fixedBlockPolynomial_supported block (environment qs) q) (fun heads =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (fixedBlockPolynomial_evaluate block heads qs p))
        (Q'.le_trans' _ _ _ (h (updateAssignment block (heads 0) qs))
          (Q'.ge_of_eqv (fixedBlockPolynomial_evaluate block heads qs q))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (fixedBlockPolynomial_haar block (environment qs) p))
    (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (fixedBlockPolynomial_haar block (environment qs) q)))

/-- Every finite original integration schedule preserves pointwise order.
Repeated indices and an empty schedule are included. -/
theorem familyProject_pointwise_mono : ∀ (ids : List Nat) (p q : RatPoly),
    (∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) p ≤ evalRatPoly (environment qs) q) →
    ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) (familyProject ids p) ≤
      evalRatPoly (environment qs) (familyProject ids q)
  | [], _, _, h, qs => h qs
  | i::ids, p, q, h, qs => familyProject_pointwise_mono ids (project i p) (project i q)
      (project_pointwise_mono i p q h) qs

/-- A signed scalar lower bound survives every finite original schedule at
every retained boundary assignment. This is not a conditional partition floor. -/
theorem familyProject_pointwise_lower_bound : ∀ (ids : List Nat) (p : RatPoly) (c : Q'),
    (∀ qs : Nat → UnitNorm, c ≤ evalRatPoly (environment qs) p) →
    ∀ qs : Nat → UnitNorm, c ≤ evalRatPoly (environment qs) (familyProject ids p)
  | [], _, _, h, qs => h qs
  | i::ids, p, c, h, qs => familyProject_pointwise_lower_bound ids (project i p) c
      (project_pointwise_lower_bound i p c h) qs

end YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder

#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.fixedBlockPolynomial
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.fixedBlockPolynomial_supported
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.fixedBlockPolynomial_haar
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.updateAssignment
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.fixedBlockPolynomial_evaluate
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.project_pointwise_lower_bound
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.project_pointwise_mono
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.familyProject_pointwise_mono
#print axioms YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder.familyProject_pointwise_lower_bound
