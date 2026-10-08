/-
# Positive orbit smoothing preserves the original response-ratio order

Every response on the SAME original Wilson completion has increasing cleared
block ratios. Positive rational time-orbit combinations therefore improve
these ratios, including at zero moments. The proof regularizes only scalar
responses, uses actual second-defect positivity, and removes the regularizer
by constructive order closure. No spectral measure, norm inverse, auxiliary
carrier, or source-overlap premise is introduced.

Raw retention is sufficient for positive smoothing, not necessary. None of
these unconditional inequalities supplies useful changing-family retention,
the original innovation ceiling, or a continuum/physical gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen

namespace YMGap.Continuum.BF4WilsonAllNomePositiveOrbitResponseOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
  (response_nonnegative response_log_convex_step)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)

local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem mul_zero (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem mul_assoc (a b c : RC) :
    RCmul (RCmul a b) c = RCmul a (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_assoc_eqv (A.approx n) (B.approx n) (C.approx n)))

private theorem mul_swap_last (a b c : RC) :
    RCmul (RCmul a b) c = RCmul (RCmul a c) b := by
  rw [mul_assoc, RCmul_comm b c, ← mul_assoc]

private theorem mul_mono_left {a b c : RC} (ha : RCnonneg a) (h : RCle b c) :
    RCle (RCmul a b) (RCmul a c) := by
  revert ha h
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C ha h => leEv_mul_nonneg_left ha h

private theorem mul_mono_right {a b c : RC} (hc : RCnonneg c) (h : RCle a b) :
    RCle (RCmul a c) (RCmul b c) := by
  rw [RCmul_comm a c, RCmul_comm b c]
  exact mul_mono_left hc h

private theorem rat_nonnegative (q : Q') (hq : (0 : Q') ≤ q) : RCnonneg (rat q) :=
  leEv_ofQ'_of_approx_ge (fun _ => hq)

private theorem cancel_floor {a b c : RC} (epsilon : Q')
    (he : (0 : Q') < epsilon) (hc : RCle (rat epsilon) c)
    (h : RCle (RCmul a c) (RCmul b c)) : RCle a b := by
  revert hc h
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C hc h => leEv_cancel_mul_right_posEv ⟨epsilon, he, hc⟩ h

private theorem sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B.approx n)))

private theorem le_of_sub_nonnegative {a b : RC} (h : RCnonneg (RCsub a b)) :
    RCle b a := by
  have hh := RCadd_le_add h (RCle_refl b)
  rwa [zero_add, sub_add_cancel] at hh

private theorem difference_of_split (a b c : RC) (h : a = RCadd b c) :
    RCsub a b = c := by
  rw [h]
  refine Quotient.inductionOn₂ b c ?_
  exact fun B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => B.approx n | _ => C.approx n)))

private theorem second_difference_regroup (a b c : RC) :
    RCsub (RCadd a c) (RCadd b b) = RCsub (RCsub a b) (RCsub b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 1))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem regularized_product (a b : RC) (epsilon : Q') :
    RCmul (RCadd a (rat epsilon)) (RCadd b (rat epsilon)) =
      RCadd (RCadd (RCmul a b) (RCscale epsilon (RCadd a b)))
        (rat (epsilon*epsilon)) := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2)))
      (.add (.add (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.add (.var 0) (.var 1)))) (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => epsilon)))

/-! Two finite inductions; all cancelled factors have the produced epsilon floor. -/

private theorem positive_chain_adjacent (E : Nat → RC) (epsilon : Q')
    (he : (0 : Q') < epsilon) (hf : ∀ n, RCle (rat epsilon) (E n))
    (hn : ∀ n, RCnonneg (E n))
    (hs : ∀ n, RCle (RCmul (E (n+1)) (E (n+1))) (RCmul (E n) (E (n+2))))
    (L : Nat) : ∀ j : Nat,
    RCle (RCmul (E (L+j)) (E (L+1))) (RCmul (E (L+j+1)) (E L))
  | 0 => by
      rw [Nat.add_zero, RCmul_comm (E L) (E (L+1))]
      exact RCle_refl _
  | j+1 => by
      have h1 := mul_mono_right (hn (L+j+1))
        (positive_chain_adjacent E epsilon he hf hn hs L j)
      have h2 := mul_mono_right (hn L) (hs (L+j))
      have hleft : RCmul (RCmul (E (L+j)) (E (L+1))) (E (L+j+1)) =
          RCmul (RCmul (E (L+j+1)) (E (L+1))) (E (L+j)) := by
        rw [RCmul_comm (E (L+j)) (E (L+1)), mul_swap_last,
          RCmul_comm (E (L+1)) (E (L+j+1))]
      have hmiddle : RCmul (RCmul (E (L+j+1)) (E L)) (E (L+j+1)) =
          RCmul (RCmul (E (L+j+1)) (E (L+j+1))) (E L) := mul_swap_last _ _ _
      have hright : RCmul (RCmul (E (L+j)) (E (L+j+2))) (E L) =
          RCmul (RCmul (E (L+j+2)) (E L)) (E (L+j)) := by
        rw [RCmul_comm (E (L+j)) (E (L+j+2)), mul_swap_last]
      rw [hleft, hmiddle] at h1
      rw [hright] at h2
      have hc := cancel_floor epsilon he (hf (L+j)) (RCle_trans h1 h2)
      simpa only [show L+(j+1)=L+j+1 by omega,
        show L+(j+1)+1=L+j+2 by omega] using hc

private theorem positive_chain_crossRatio (E : Nat → RC) (epsilon : Q')
    (he : (0 : Q') < epsilon) (hf : ∀ n, RCle (rat epsilon) (E n))
    (hn : ∀ n, RCnonneg (E n))
    (hs : ∀ n, RCle (RCmul (E (n+1)) (E (n+1))) (RCmul (E n) (E (n+2))))
    (L j : Nat) : ∀ h : Nat,
    RCle (RCmul (E (L+j)) (E (L+h))) (RCmul (E (L+j+h)) (E L))
  | 0 => by simp only [Nat.add_zero]; exact RCle_refl _
  | h+1 => by
      have h1 := mul_mono_right (hn (L+h+1))
        (positive_chain_crossRatio E epsilon he hf hn hs L j h)
      have h2 := mul_mono_right (hn L)
        (positive_chain_adjacent E epsilon he hf hn hs (L+h) j)
      have hleft : RCmul (RCmul (E (L+j)) (E (L+h))) (E (L+h+1)) =
          RCmul (RCmul (E (L+j)) (E (L+h+1))) (E (L+h)) := mul_swap_last _ _ _
      have hmiddle : RCmul (RCmul (E (L+j+h)) (E L)) (E (L+h+1)) =
          RCmul (RCmul (E (L+j+h)) (E (L+h+1))) (E L) := mul_swap_last _ _ _
      have hright : RCmul (RCmul (E (L+j+h+1)) (E L)) (E (L+h)) =
          RCmul (RCmul (E (L+j+h+1)) (E (L+h))) (E L) := mul_swap_last _ _ _
      rw [hleft, hmiddle] at h1
      simp only [show L+h+j=L+j+h by omega] at h2
      rw [← hright] at h2
      have hc := cancel_floor epsilon he (hf (L+h)) (RCle_trans h1 h2)
      simpa only [show L+(h+1)=L+h+1 by omega,
        show L+j+(h+1)=L+j+h+1 by omega] using hc

/-! The explicit null sequence removes scalar regularization at four endpoints. -/

private theorem invSucc_converges_zero :
    ConvergesTo (fun n => ofQ' (Q'.invSucc n)) czero := by
  intro epsilon he
  refine ⟨epsilon.den, fun n hn => ⟨0, fun _ _ => ?_⟩⟩
  change Q'.invSucc n ≤ 0+epsilon ∧ (0 : Q') ≤ Q'.invSucc n+epsilon
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
        (HalfPow.invSucc_den_le epsilon he))
      (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  · exact Q'.zero_le_add _ _ (Q'.le_of_lt (Q'.invSucc_pos n)) (Q'.le_of_lt he)

private theorem regularized_converges (A : CReal) :
    ConvergesTo (fun n => add A (ofQ' (Q'.invSucc n))) A :=
  convergesTo_limit_congr
    (TrigAddCReal.convergesTo_add (convergesTo_const A) invSucc_converges_zero)
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem remove_regularization (a b c d : RC)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (RCmul (RCadd a (rat epsilon)) (RCadd b (rat epsilon)))
        (RCmul (RCadd c (rat epsilon)) (RCadd d (rat epsilon)))) :
    RCle (RCmul a b) (RCmul c d) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D h
  exact leEv_of_convergesTo_le
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (regularized_converges A) (regularized_converges B))
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (regularized_converges C) (regularized_converges D))
    (fun n => h (Q'.invSucc n) (Q'.invSucc_pos n))

section Completed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation:max "R" x:arg n:arg => B x (T n x)
attribute [local irreducible] completedInner completedTime

private theorem first_defect_pin (x : V) (n : Nat) :
    RCsub (R x n) (R x (n+1)) = mixedMoment hw0 hw1 x n 1 := by
  exact difference_of_split _ _ _ (mixedMoment_split hw0 hw1 x n 0)

private theorem response_convex_step (x : V) (n : Nat) :
    RCle (RCadd (R x (n+1)) (R x (n+1))) (RCadd (R x n) (R x (n+2))) := by
  apply le_of_sub_nonnegative
  rw [second_difference_regroup, first_defect_pin hw0 hw1 x n,
    show n+2=(n+1)+1 by omega, first_defect_pin hw0 hw1 x (n+1)]
  rw [difference_of_split _ _ _ (mixedMoment_split hw0 hw1 x n 1)]
  exact mixedMoment_nonnegative hw0 hw1 x n 2

private theorem regularized_response_crossRatio (x : V) (epsilon : Q')
    (he : (0 : Q') < epsilon) (L j h : Nat) :
    RCle (RCmul (RCadd (R x (L+j)) (rat epsilon))
      (RCadd (R x (L+h)) (rat epsilon)))
      (RCmul (RCadd (R x (L+j+h)) (rat epsilon)) (RCadd (R x L) (rat epsilon))) := by
  let E : Nat → RC := fun n => RCadd (R x n) (rat epsilon)
  have hf : ∀ n, RCle (rat epsilon) (E n) := by
    intro n
    have hh := RCadd_le_add (response_nonnegative hw0 hw1 width x n)
      (RCle_refl (rat epsilon))
    simpa only [zero_add] using hh
  have hn : ∀ n, RCnonneg (E n) := fun n =>
    RCle_trans (rat_nonnegative epsilon (Q'.le_of_lt he)) (hf n)
  have hs : ∀ n, RCle (RCmul (E (n+1)) (E (n+1))) (RCmul (E n) (E (n+2))) := by
    intro n
    dsimp only [E]
    rw [regularized_product, regularized_product]
    exact RCadd_le_add
      (RCadd_le_add (response_log_convex_step hw0 hw1 width x n)
        (RCscale_mono (Q'.le_of_lt he) (response_convex_step hw0 hw1 x n)))
      (RCle_refl _)
  exact positive_chain_crossRatio E epsilon he hf hn hs L j h

/-- Every cleared block ratio increases along the actual original response.
All three lags are arbitrary and zero responses need no excluded case. -/
theorem response_crossRatio (x : V) (L j h : Nat) :
    RCle (RCmul (R x (L+j)) (R x (L+h)))
      (RCmul (R x (L+j+h)) (R x L)) :=
  remove_regularization _ _ _ _
    (fun epsilon he => regularized_response_crossRatio hw0 hw1 x epsilon he L j h)

private theorem mul_add (a b c : RC) :
    RCmul (RCadd a b) c = RCadd (RCmul a c) (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A0 B0 C0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv (A0.approx n) (B0.approx n) (C0.approx n)))

private theorem mul_scale (q : Q') (a b : RC) :
    RCmul (RCscale q a) b = RCscale q (RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A0 B0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_assoc_eqv q (A0.approx n) (B0.approx n)))

private theorem sum_mul_right (cs : List (Q' × Nat)) (f : Nat → RC) (a : RC) :
    RCmul (responseSum cs f) a = responseSum cs (fun n => RCmul (f n) a) := by
  induction cs with
  | nil => exact mul_zero a
  | cons c cs ih =>
      simp only [responseSum, mul_add, mul_scale, ih]

private theorem sum_mono (cs : List (Q' × Nat)) (f g : Nat → RC)
    (hc : ∀ c ∈ cs, (0 : Q') ≤ c.1) (hfg : ∀ n, RCle (f n) (g n)) :
    RCle (responseSum cs f) (responseSum cs g) := by
  revert hc
  induction cs with
  | nil => intro hc; exact RCle_refl _
  | cons c cs ih =>
      intro hc
      exact RCadd_le_add (RCscale_mono (hc c (List.mem_cons_self)) (hfg c.2))
        (ih (fun c hm => hc c (List.mem_cons_of_mem _ hm)))

private theorem orbit_response_expand (x : V) (cs : List (Q' × Nat)) (n : Nat) :
    R (orbitSum hw0 hw1 x cs) n = responseSum cs (fun j =>
      responseSum cs (fun k => R x (j+k+n))) := by
  rw [orbitSum_time, orbitSum_pairing]
  apply congrArg (responseSum cs)
  funext j
  apply congrArg (responseSum cs)
  funext k
  rw [← completedTime_add]

/-- Positive rational orbit weights improve the response ratio on the SAME
carrier. Repeated orbit entries and every double-orbit cross term remain. -/
theorem positiveOrbit_response_crossRatio (x : V) (cs : List (Q' × Nat))
    (hc : ∀ c ∈ cs, (0 : Q') ≤ c.1) (L h : Nat) :
    RCle (RCmul (R (orbitSum hw0 hw1 x cs) L) (R x (L+h)))
      (RCmul (R (orbitSum hw0 hw1 x cs) (L+h)) (R x L)) := by
  rw [orbit_response_expand hw0 hw1 x cs L,
    orbit_response_expand hw0 hw1 x cs (L+h), sum_mul_right, sum_mul_right]
  apply sum_mono cs _ _ hc
  intro j
  rw [sum_mul_right, sum_mul_right]
  apply sum_mono cs _ _ hc
  intro k
  have hh := response_crossRatio hw0 hw1 x L (j+k) h
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

private theorem scale_regularized (q epsilon : Q') (a : RC) :
    RCscale q (RCadd a (rat epsilon)) =
      RCadd (RCscale q a) (rat (q*epsilon)) := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_add_eqv q (A.approx n) epsilon))

private theorem scale_move (q : Q') (a b : RC) :
    RCmul a (RCscale q b) = RCmul (RCscale q a) b := by
  rw [RCmul_comm a (RCscale q b), mul_scale, RCmul_comm b a, ← mul_scale]

private theorem remove_scaled_regularization (q : Q') (a b : RC)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (RCscale q (RCadd a (rat epsilon))) (RCadd b (rat epsilon))) :
    RCle (RCscale q a) b := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A0 B0 h
  exact leEv_of_convergesTo_le
    (convergesTo_const_mul (ofQ' q) (regularized_converges A0))
    (regularized_converges B0) (fun n => h (Q'.invSucc n) (Q'.invSucc_pos n))

/-- A retained block fraction at L also holds at every later lag, without
cancelling a possibly zero original response. -/
theorem shifted_response_floor (x : V) (kappa : Q')
    (hk : kappa ≤ (1 : Q')) (L h j : Nat)
    (hf : RCle (RCscale kappa (R x L)) (R x (L+h))) :
    RCle (RCscale kappa (R x (L+j))) (R x (L+j+h)) := by
  apply remove_scaled_regularization
  intro epsilon he
  have hfloor (n : Nat) : RCle (rat epsilon) (RCadd (R x n) (rat epsilon)) := by
    have hh := RCadd_le_add (response_nonnegative hw0 hw1 width x n)
      (RCle_refl (rat epsilon))
    simpa only [zero_add] using hh
  have hnonneg (n : Nat) : RCnonneg (RCadd (R x n) (rat epsilon)) :=
    RCle_trans (rat_nonnegative epsilon (Q'.le_of_lt he)) (hfloor n)
  have hke : kappa*epsilon ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ epsilon hk (Q'.le_of_lt he))
      (Q'.le_of_eqv (Q'.one_mul_eqv epsilon))
  have hregular : RCle (RCscale kappa (RCadd (R x L) (rat epsilon)))
      (RCadd (R x (L+h)) (rat epsilon)) := by
    rw [scale_regularized]
    exact RCadd_le_add hf (leEv_ofQ'_of_approx_ge (fun _ => hke))
  have h1 := mul_mono_left (hnonneg (L+j)) hregular
  rw [scale_move] at h1
  exact cancel_floor epsilon he (hfloor L)
    (RCle_trans h1 (regularized_response_crossRatio hw0 hw1 x epsilon he L j h))

private theorem sum_scale (cs : List (Q' × Nat)) (f : Nat → RC) (q : Q') :
    RCscale q (responseSum cs f) = responseSum cs (fun n => RCscale q (f n)) := by
  induction cs with
  | nil => exact RCscale_RCzero q
  | cons c cs ih =>
      change RCscale q (RCadd (RCscale c.1 (f c.2)) (responseSum cs f)) = _
      have hadd (a b : RC) : RCscale q (RCadd a b) =
          RCadd (RCscale q a) (RCscale q b) := by
        refine Quotient.inductionOn₂ a b ?_
        exact fun A0 B0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
          (fun n => Q'.mul_add_eqv q (A0.approx n) (B0.approx n)))
      rw [hadd, ih, RCscale_RCscale]
      change RCadd (RCscale (q*c.1) (f c.2)) _ =
        RCadd (RCscale c.1 (RCscale q (f c.2))) _
      rw [RCscale_RCscale, RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv q c.1)]

/-- A raw retained fraction transfers to every positive smoothing without a
norm floor. This is sufficient, not necessary; the raw floor is not produced.
Neither a zero response nor an empty orbit is excluded. -/
theorem positiveOrbit_response_retention (x : V) (cs : List (Q' × Nat))
    (hc : ∀ c ∈ cs, (0 : Q') ≤ c.1) (kappa : Q')
    (_hk0 : (0 : Q') ≤ kappa) (hk1 : kappa ≤ (1 : Q')) (L h : Nat)
    (hf : RCle (RCscale kappa (R x L)) (R x (L+h))) :
    RCle (RCscale kappa (R (orbitSum hw0 hw1 x cs) L))
      (R (orbitSum hw0 hw1 x cs) (L+h)) := by
  rw [orbit_response_expand hw0 hw1 x cs L,
    orbit_response_expand hw0 hw1 x cs (L+h), sum_scale]
  apply sum_mono cs _ _ hc
  intro j
  rw [sum_scale]
  apply sum_mono cs _ _ hc
  intro k
  have hh := shifted_response_floor hw0 hw1 x kappa hk1 L h (j+k) hf
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

end Completed

#print axioms positive_chain_crossRatio
#print axioms invSucc_converges_zero
#print axioms remove_regularization
#print axioms response_convex_step
#print axioms response_crossRatio
#print axioms orbit_response_expand
#print axioms positiveOrbit_response_crossRatio
#print axioms shifted_response_floor
#print axioms positiveOrbit_response_retention

end YMGap.Continuum.BF4WilsonAllNomePositiveOrbitResponseOrder
