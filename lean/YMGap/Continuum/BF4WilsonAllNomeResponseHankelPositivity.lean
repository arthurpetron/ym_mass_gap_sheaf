/-
# Hankel and Hausdorff positivity of the response (NECESSARY moment conditions)

Companion to `audits/AUDIT-RESPONSE-HANKEL-POSITIVITY-2026-10-06.md`. ADDITIVE.

On the completed all-nome carrier, take any vector `ψ` and set `R(n) = B(ψ, T^n ψ)`.
The time map `T` is self-adjoint and positive: `B(x, T x) ≥ 0`
(`completedInner_oneStep_nonnegative`), and `B(T^a x, T^b y) = B(x, T^(a+b) y)`.
It is also a contraction (`completedInner_time_contraction`). These facts already
give `mixedMoment_nonnegative`: `B(x, T^m (I-T)^l x) ≥ 0` for all `m, l`.

Applying that to `v = Σ_i c_i T^i ψ` (`orbitSum`, rational coefficients `c_i : Q'`, the
repo's scalar) and expanding bilinearly gives, in plain double-sum form:

* **Hankel positivity** (`hankelSum_nonneg`), for EVERY `m ≥ 0`, in particular `m ∈ {0,1}`:
  `Σ_i Σ_k c_i c_k R(i+k+m) ≥ 0`.
* **Hausdorff positivity** (`hausdorffSum_nonneg`), for every `m, l ≥ 0`:
  `Σ_i Σ_k c_i c_k (∇^l R)(i+k+m) ≥ 0`.
  Here `∇R(n) = R(n) - R(n+1)` and `∇^l = (-Δ)^l`, so
  `(∇^l R)(n) = Σ_{r ≤ l} (-1)^r C(l,r) R(n+r)`.
  For `l = 1` this is `Σ_i Σ_k c_i c_k (R(i+k+m) - R(i+k+m+1)) ≥ 0`
  (`hausdorffSum_first_nonneg`).

`hankelSum cs R m` is literally `Σ_{i<|cs|} Σ_{k<|cs|} c_i c_k R(i+k+m)`, built as
`responseSum` over the indexed list `[(c_0,0), (c_1,1), …]`. `hankelForm K R m` is the
same over an arbitrary lag list `K = [(c,lag)]`.

No `T^(1/2)` and no spectral measure is used. The `m` odd cases come from positivity of
`T` itself; the even shift uses self-adjointness.

Regressions:
* `mixedMoment_eq_hausdorffDiff`: `mixedMoment ψ m l = (∇^l R)(m)`.
* `mixedMoment_nonnegative_via_hankel`: the existing lemma is the 1×1 case.
* `hankelSum_pair`: the explicit 2×2 form
  `a²R(m) + 2ab R(m+1) + b²R(m+2) ≥ 0` (`hankel2_nonneg`).
* `hankel_logConvex_step`: `R(k+1)² ≤ R(k)R(k+2)`. This re-exports the existing
  Cauchy–Schwarz proof (`response_log_convex_step`). It is NOT re-derived here from the
  2×2 form, because the constructive discriminant argument was skipped.

HONEST SCOPE. These are NECESSARY conditions on the response sequence, testable on
measured data. They hold for EVERY vector on this carrier; they do not single out the
YM anchor and prove nothing about survival or a gap. The converse, Hausdorff's moment
theorem (a representing measure on `[0,1]`), is NOT formalized. Real (RC) coefficients
are not covered; only rational ones are, though the conditions are stable under limits
on paper.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen

namespace YMGap.Continuum.BF4WilsonAllNomeResponseHankelPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (defect defectPower defectPower_succ_right mixedMoment mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_log_convex_step)

/-! ## 0. Scalar helpers (local copies of standard private lemmas) -/

private theorem rh_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv _))

private theorem rh_scale_one (a : RC) : RCscale 1 a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.one_mul_eqv (A.approx n)))

private theorem rh_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv _))

private theorem rh_negative_one (a : RC) : RCscale (-1) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem rh_sub_scale_add (c : Q') (a b s t : RC) :
    RCsub (RCadd (RCscale c a) s) (RCadd (RCscale c b) t) =
      RCadd (RCscale c (RCsub a b)) (RCsub s t) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  refine Quotient.inductionOn₂ s t ?_
  intro S U
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
        (.neg (.add (.mul (.var 0) (.var 2)) (.var 4))))
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.var 3) (.neg (.var 4))))
      (by decide)
      (fun | 0 => c | 1 => A.approx n | 2 => B'.approx n | 3 => S.approx n
           | _ => U.approx n)))

private theorem rh_pair_expand (a b : Q') (x y z : RC) :
    RCadd (RCscale a (RCadd (RCscale a x) (RCscale b y)))
        (RCscale b (RCadd (RCscale a y) (RCscale b z))) =
      RCadd (RCadd (RCscale (a*a) x) (RCscale (a*b + a*b) y)) (RCscale (b*b) z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4)))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 3)))
        (.mul (.mul (.var 1) (.var 1)) (.var 4)))
      (by decide)
      (fun | 0 => a | 1 => b | 2 => X.approx n | 3 => Y.approx n | _ => Z.approx n)))

/-! ## 1. Plain finite sums -/

/-- `[(c_0,i), (c_1,i+1), …]`: coefficients indexed by consecutive lags. -/
def lagged : List Q' → Nat → List (Q' × Nat)
  | [], _ => []
  | c :: cs, i => (c, i) :: lagged cs (i+1)

/-- Hankel quadratic form over a lag list `K = [(c,lag)]`:
`Σ_{(c,i)∈K} Σ_{(d,k)∈K} c d R(i+k+m)`. -/
def hankelForm (K : List (Q' × Nat)) (R : Nat → RC) (m : Nat) : RC :=
  responseSum K (fun i => responseSum K (fun k => R (i+k+m)))

/-- **Plain form.** `hankelSum [c_0,…,c_{N-1}] R m = Σ_{i<N} Σ_{k<N} c_i c_k R(i+k+m)`. -/
def hankelSum (cs : List Q') (R : Nat → RC) (m : Nat) : RC :=
  hankelForm (lagged cs 0) R m

/-- Iterated backward difference `∇^l R`, with `∇R(n) = R(n) - R(n+1)`
(`= (-Δ)^l R`, i.e. `(∇^l R)(n) = Σ_{r≤l} (-1)^r C(l,r) R(n+r)`). -/
def hausdorffDiff : Nat → (Nat → RC) → Nat → RC
  | 0, R => R
  | l+1, R => hausdorffDiff l (fun n => RCsub (R n) (R (n+1)))

theorem hausdorffDiff_one (R : Nat → RC) (n : Nat) :
    hausdorffDiff 1 R n = RCsub (R n) (R (n+1)) := rfl

theorem responseSum_sub (K : List (Q' × Nat)) (f g : Nat → RC) :
    RCsub (responseSum K f) (responseSum K g) = responseSum K (fun i => RCsub (f i) (g i)) := by
  induction K with
  | nil => exact rh_sub_self RCzero
  | cons a K ih =>
      rcases a with ⟨c, n⟩
      show RCsub (RCadd (RCscale c (f n)) (responseSum K f))
          (RCadd (RCscale c (g n)) (responseSum K g)) =
        RCadd (RCscale c (RCsub (f n) (g n))) (responseSum K (fun i => RCsub (f i) (g i)))
      rw [rh_sub_scale_add, ih]

/-- `∇^l` commutes with a finite rational sum. -/
theorem hausdorffDiff_responseSum (K : List (Q' × Nat)) :
    ∀ (l : Nat) (F : Nat → Nat → RC) (m : Nat),
      hausdorffDiff l (fun n => responseSum K (fun i => F i n)) m =
        responseSum K (fun i => hausdorffDiff l (F i) m)
  | 0, _, _ => rfl
  | l+1, F, m => by
      show hausdorffDiff l (fun n => RCsub (responseSum K (fun i => F i n))
          (responseSum K (fun i => F i (n+1)))) m =
        responseSum K (fun i => hausdorffDiff l (fun n => RCsub (F i n) (F i (n+1))) m)
      have e : (fun n => RCsub (responseSum K (fun i => F i n))
          (responseSum K (fun i => F i (n+1)))) =
          (fun n => responseSum K (fun i => RCsub (F i n) (F i (n+1)))) :=
        funext (fun n => responseSum_sub K _ _)
      rw [e]
      exact hausdorffDiff_responseSum K l (fun i n => RCsub (F i n) (F i (n+1))) m

/-- Shift: `∇^l (n ↦ R(a+n)) (m) = (∇^l R)(a+m)`. -/
theorem hausdorffDiff_shift : ∀ (l : Nat) (R : Nat → RC) (a m : Nat),
    hausdorffDiff l (fun n => R (a+n)) m = hausdorffDiff l R (a+m)
  | 0, _, _, _ => rfl
  | l+1, R, a, m => hausdorffDiff_shift l (fun n => RCsub (R n) (R (n+1))) a m

/-! ## 2. The completed carrier -/

section Carrier

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

private theorem rh_inner_sub_left (x y z : V) :
    B (completedSub hw0 hw1 x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub completedNeg RCsub
  rw [completedInner_add_left, completedInner_smul_left, rh_negative_one]

private theorem rh_inner_sub_right (x y z : V) :
    B x (completedSub hw0 hw1 y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 x, rh_inner_sub_left,
    completedInner_symm hw0 hw1 y x, completedInner_symm hw0 hw1 z x]

/-- Vector-to-scalar pin: `B(x, T^n (I-T)^l y) = ∇^l (k ↦ B(x, T^k y)) (n)`. -/
theorem inner_time_defectPower (x : V) :
    ∀ (l : Nat) (y : V) (n : Nat),
      B x (T n (defectPower hw0 hw1 l y)) = hausdorffDiff l (fun k => B x (T k y)) n
  | 0, _, _ => rfl
  | l+1, y, n => by
      rw [defectPower_succ_right, inner_time_defectPower x l (defect hw0 hw1 y) n]
      show hausdorffDiff l (fun k => B x (T k (defect hw0 hw1 y))) n =
        hausdorffDiff l (fun k => RCsub (B x (T k y)) (B x (T (k+1) y))) n
      have e : (fun k => B x (T k (defect hw0 hw1 y))) =
          (fun k => RCsub (B x (T k y)) (B x (T (k+1) y))) := by
        funext k
        rw [defect, completedTime_sub, rh_inner_sub_right, completedTime_add]
      rw [e]

/-- The response of `v = Σ c_i T^i ψ` expands into the Hankel double sum. -/
theorem orbit_response_expand (ψ : V) (K : List (Q' × Nat)) (n : Nat) :
    B (orbitSum hw0 hw1 ψ K) (T n (orbitSum hw0 hw1 ψ K)) =
      responseSum K (fun i => responseSum K (fun k => B ψ (T (i+k+n) ψ))) := by
  rw [orbitSum_time hw0 hw1 ψ K n, orbitSum_pairing]
  apply congrArg (responseSum K)
  funext i
  apply congrArg (responseSum K)
  funext k
  rw [completedTime_add hw0 hw1 (i+k) n ψ]

/-- **Hausdorff–Hankel positivity, lag-list form.** For every `m, l ≥ 0`:
`Σ_{(c,i)} Σ_{(d,k)} c d (∇^l R)(i+k+m) ≥ 0`, `R(n) = B(ψ, T^n ψ)`. -/
theorem hausdorffHankel_nonneg (ψ : V) (K : List (Q' × Nat)) (m l : Nat) :
    RCnonneg (hankelForm K (hausdorffDiff l (fun n => B ψ (T n ψ))) m) := by
  have h : RCnonneg (B (orbitSum hw0 hw1 ψ K)
      (T m (defectPower hw0 hw1 l (orbitSum hw0 hw1 ψ K)))) :=
    mixedMoment_nonnegative hw0 hw1 (orbitSum hw0 hw1 ψ K) m l
  rw [inner_time_defectPower] at h
  have e1 : (fun n => B (orbitSum hw0 hw1 ψ K) (T n (orbitSum hw0 hw1 ψ K))) =
      (fun n => responseSum K (fun i => responseSum K (fun k => B ψ (T (i+k+n) ψ)))) :=
    funext (fun n => orbit_response_expand hw0 hw1 ψ K n)
  rw [e1] at h
  have e2 : hausdorffDiff l
        (fun n => responseSum K (fun i => responseSum K (fun k => B ψ (T (i+k+n) ψ)))) m =
      responseSum K (fun i => hausdorffDiff l
        (fun n => responseSum K (fun k => B ψ (T (i+k+n) ψ))) m) :=
    hausdorffDiff_responseSum K l (fun i n => responseSum K (fun k => B ψ (T (i+k+n) ψ))) m
  have e3 : responseSum K (fun i => hausdorffDiff l
        (fun n => responseSum K (fun k => B ψ (T (i+k+n) ψ))) m) =
      responseSum K (fun i => responseSum K (fun k =>
        hausdorffDiff l (fun n => B ψ (T n ψ)) (i+k+m))) := by
    apply congrArg (responseSum K)
    funext i
    rw [hausdorffDiff_responseSum K l (fun k n => B ψ (T (i+k+n) ψ)) m]
    apply congrArg (responseSum K)
    funext k
    exact hausdorffDiff_shift l (fun n => B ψ (T n ψ)) (i+k) m
  rw [e2, e3] at h
  exact h

/-- **Hankel positivity, lag-list form** (every `m`). -/
theorem hankelForm_nonneg (ψ : V) (K : List (Q' × Nat)) (m : Nat) :
    RCnonneg (hankelForm K (fun n => B ψ (T n ψ)) m) :=
  hausdorffHankel_nonneg hw0 hw1 ψ K m 0

/-- **Hankel positivity, plain form.** For any rational `c_0,…,c_{N-1}` and every `m`:
`Σ_i Σ_k c_i c_k R(i+k+m) ≥ 0`, `R(n) = B(ψ, T^n ψ)`. -/
theorem hankelSum_nonneg (ψ : V) (cs : List Q') (m : Nat) :
    RCnonneg (hankelSum cs (fun n => B ψ (T n ψ)) m) :=
  hankelForm_nonneg hw0 hw1 ψ (lagged cs 0) m

/-- `m = 0`: `Σ_i Σ_k c_i c_k R(i+k) ≥ 0` (`= ‖Σ c_i T^i ψ‖²`). -/
theorem hankelSum_nonneg_zero (ψ : V) (cs : List Q') :
    RCnonneg (hankelSum cs (fun n => B ψ (T n ψ)) 0) :=
  hankelSum_nonneg hw0 hw1 ψ cs 0

/-- `m = 1`: `Σ_i Σ_k c_i c_k R(i+k+1) ≥ 0` (`= B(v, T v)`, positivity of `T`). -/
theorem hankelSum_nonneg_one (ψ : V) (cs : List Q') :
    RCnonneg (hankelSum cs (fun n => B ψ (T n ψ)) 1) :=
  hankelSum_nonneg hw0 hw1 ψ cs 1

/-- **Hausdorff positivity, plain form.** For every `m, l`:
`Σ_i Σ_k c_i c_k (∇^l R)(i+k+m) ≥ 0`. -/
theorem hausdorffSum_nonneg (ψ : V) (cs : List Q') (m l : Nat) :
    RCnonneg (hankelSum cs (hausdorffDiff l (fun n => B ψ (T n ψ))) m) :=
  hausdorffHankel_nonneg hw0 hw1 ψ (lagged cs 0) m l

/-- **First Hausdorff condition, plain form.**
`Σ_i Σ_k c_i c_k (R(i+k+m) - R(i+k+m+1)) ≥ 0` (`= B(v, T^m (I-T) v)`). -/
theorem hausdorffSum_first_nonneg (ψ : V) (cs : List Q') (m : Nat) :
    RCnonneg (hankelSum cs (fun n => RCsub (B ψ (T n ψ)) (B ψ (T (n+1) ψ))) m) :=
  hausdorffSum_nonneg hw0 hw1 ψ cs m 1

/-! ## 3. Regressions -/

/-- The existing mixed moment IS the Hausdorff difference of the response. -/
theorem mixedMoment_eq_hausdorffDiff (ψ : V) (m l : Nat) :
    mixedMoment hw0 hw1 ψ m l = hausdorffDiff l (fun n => B ψ (T n ψ)) m :=
  inner_time_defectPower hw0 hw1 ψ l ψ m

theorem hankelSum_singleton (R : Nat → RC) (m : Nat) : hankelSum [1] R m = R m := by
  show RCadd (RCscale 1 (RCadd (RCscale 1 (R (0+0+m))) RCzero)) RCzero = R m
  rw [rh_add_zero, rh_add_zero, rh_scale_one, rh_scale_one, show 0+0+m = m by omega]

/-- `mixedMoment_nonnegative` recovered as the 1×1 Hausdorff–Hankel case. -/
theorem mixedMoment_nonnegative_via_hankel (ψ : V) (m l : Nat) :
    RCnonneg (mixedMoment hw0 hw1 ψ m l) := by
  rw [mixedMoment_eq_hausdorffDiff,
    ← hankelSum_singleton (hausdorffDiff l (fun n => B ψ (T n ψ))) m]
  exact hausdorffSum_nonneg hw0 hw1 ψ [1] m l

/-- The 2×2 plain form, multiplied out. -/
theorem hankelSum_pair (a b : Q') (R : Nat → RC) (m : Nat) :
    hankelSum [a, b] R m =
      RCadd (RCadd (RCscale (a*a) (R m)) (RCscale (a*b + a*b) (R (m+1))))
        (RCscale (b*b) (R (m+2))) := by
  show RCadd (RCscale a (RCadd (RCscale a (R (0+0+m)))
        (RCadd (RCscale b (R (0+1+m))) RCzero)))
      (RCadd (RCscale b (RCadd (RCscale a (R (1+0+m)))
        (RCadd (RCscale b (R (1+1+m))) RCzero))) RCzero) = _
  rw [rh_add_zero, rh_add_zero, rh_add_zero, show 0+0+m = m by omega,
    show 0+1+m = m+1 by omega, show 1+1+m = m+2 by omega]
  exact rh_pair_expand a b (R m) (R (m+1)) (R (m+2))

/-- **2×2 Hankel**: `a² R(m) + 2ab R(m+1) + b² R(m+2) ≥ 0` for all rational `a, b`. -/
theorem hankel2_nonneg (ψ : V) (a b : Q') (m : Nat) :
    RCnonneg (RCadd (RCadd (RCscale (a*a) (B ψ (T m ψ)))
        (RCscale (a*b + a*b) (B ψ (T (m+1) ψ)))) (RCscale (b*b) (B ψ (T (m+2) ψ)))) := by
  rw [← hankelSum_pair a b (fun n => B ψ (T n ψ)) m]
  exact hankelSum_nonneg hw0 hw1 ψ [a, b] m

/-- Log-convexity step `R(k+1)² ≤ R(k) R(k+2)`: the EXISTING Cauchy–Schwarz result,
re-exported for the same `R`. It is not re-derived from `hankel2_nonneg` (the
constructive discriminant step is skipped). -/
theorem hankel_logConvex_step (ψ : V) (k : Nat) :
    RCle (RCmul (B ψ (T (k+1) ψ)) (B ψ (T (k+1) ψ)))
      (RCmul (B ψ (T k ψ)) (B ψ (T (k+2) ψ))) :=
  response_log_convex_step hw0 hw1 width ψ k

end Carrier

#print axioms responseSum_sub
#print axioms hausdorffDiff_responseSum
#print axioms hausdorffDiff_shift
#print axioms inner_time_defectPower
#print axioms orbit_response_expand
#print axioms hausdorffHankel_nonneg
#print axioms hankelForm_nonneg
#print axioms hankelSum_nonneg
#print axioms hankelSum_nonneg_zero
#print axioms hankelSum_nonneg_one
#print axioms hausdorffSum_nonneg
#print axioms hausdorffSum_first_nonneg
#print axioms mixedMoment_eq_hausdorffDiff
#print axioms hankelSum_singleton
#print axioms mixedMoment_nonnegative_via_hankel
#print axioms hankelSum_pair
#print axioms hankel2_nonneg
#print axioms hankel_logConvex_step

end YMGap.Continuum.BF4WilsonAllNomeResponseHankelPositivity
