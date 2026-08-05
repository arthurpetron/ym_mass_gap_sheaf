/-
`FusionBoxShellReserve` -- central-shell endpoint closure and the exact
consumer seam for the all-cutoff physical prefix reserve.

The endpoint argument is independent of the still-open integer prefix
classification.  At `wH = 1/2`, the actual even/odd box ceilings are beaten
by explicit central terms already present in the middle box:

* for `s=2m`, the two central odd pairs give `2 c_m c_(m+1)`;
* for `s=2m+1`, the even centre and its two nearest shifted pairs give
  `c_(m+1)^2 + 2 c_m c_(m+2)`.

Together with the proved factor-four Newton inequality, these lower bounds
close every finite-triangle interlacing inequality at the endpoint.  The
second section records the exact constructive composition from the stronger
term-filtered prefix reserve to certificates at every cutoff and hence to the
existing interval `UniformBoxLogConcave` consumer.

Honest scope: this file does not pretend that endpoint positivity alone proves
the whole interval prefix reserve.  It exposes the exact even/odd integer seam;
that seam is now constructively discharged downstream in
`FusionBoxPostBoundaryClosure`.
-/

import YMGap.Continuum.FusionBoxPrefixReserve
import YMGap.Continuum.FusionBoxStrandCeilings
import YMGap.Continuum.AcNReserveAnalytic
import YMGap.Continuum.EigShiftOrder
import YMGap.Continuum.WHMarginTailClose

namespace YMGap.Continuum.FusionBoxShellReserve

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionWeightedBoxInterlacing
open YMGap.Continuum.FusionWeightedInterlacingCertificate
open YMGap.Continuum.FusionBoxBernsteinReconstruction
open YMGap.Continuum.FusionBoxPrefixReserve
open YMGap.Continuum.FusionBoxStrandCeilings
open YMGap.Continuum.AcNReserveAnalytic

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast_local,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-- A local unambiguous name for the physical endpoint `w = 1/2`. -/
private abbrev halfW : Q' := YMGap.Continuum.FusionCoreStepRoundA.wH

/-! ## 1. Small constructive finite-sum selectors -/

-- The two- and three-term selectors are the already axiom-gated
-- `EigShiftOrder.fsum_two_term_le` and
-- `WHMarginTailClose.fsum_three_term_le`.

private theorem mul_le_mul_nonneg {a b c d : Q'}
    (hab : a ≤ b) (hcd : c ≤ d) (hc : (0 : Q') ≤ c)
    (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

/-- Constructive binomial-square lower bound, kept local so the endpoint
argument does not depend on a private helper from another module. -/
private theorem sq_binomial_lower (S T : Q') (hT : (0 : Q') ≤ T) :
    S * S + Q'.ofNat 4 * (S * T) ≤
      (S + Q'.ofNat 2 * T) * (S + Q'.ofNat 2 * T) := by
  have hright :
      ((S + Q'.ofNat 2 * T) * (S + Q'.ofNat 2 * T)).eqv
        ((S + Q'.ofNat 2 * T) * S +
          (S + Q'.ofNat 2 * T) * (Q'.ofNat 2 * T)) :=
    Q'.mul_add_eqv (S + Q'.ofNat 2 * T) S (Q'.ofNat 2 * T)
  have hleftSquare :
      ((S + Q'.ofNat 2 * T) * S).eqv
        (S * S + (Q'.ofNat 2 * T) * S) :=
    Q'.add_mul_eqv S (Q'.ofNat 2 * T) S
  have hrightSquare :
      ((S + Q'.ofNat 2 * T) * (Q'.ofNat 2 * T)).eqv
        (S * (Q'.ofNat 2 * T) +
          (Q'.ofNat 2 * T) * (Q'.ofNat 2 * T)) :=
    Q'.add_mul_eqv S (Q'.ofNat 2 * T) (Q'.ofNat 2 * T)
  have h2T0 : (0 : Q') ≤ (Q'.ofNat 2 * T) * (Q'.ofNat 2 * T) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hT)
      (Q'.mul_nonneg _ _ (by decide) hT)
  have hfirst : S * S + (Q'.ofNat 2 * T) * S ≤
      (S + Q'.ofNat 2 * T) * S := Q'.ge_of_eqv hleftSquare
  have hsecond : S * (Q'.ofNat 2 * T) ≤
      (S + Q'.ofNat 2 * T) * (Q'.ofNat 2 * T) :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ h2T0)
      (Q'.ge_of_eqv hrightSquare)
  have hsum := Q'.add_le_add hfirst hsecond
  have hp1 : ((Q'.ofNat 2 * T) * S).eqv
      (Q'.ofNat 2 * (S * T)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 2) T S)
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) (T * S) (S * T)
        (Q'.mul_comm_eqv T S))
  have hp2 : (S * (Q'.ofNat 2 * T)).eqv
      (Q'.ofNat 2 * (S * T)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv S (Q'.ofNat 2) T))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (S * Q'.ofNat 2) (Q'.ofNat 2 * S) T
          (Q'.mul_comm_eqv S (Q'.ofNat 2)))
        (Q'.mul_assoc_eqv (Q'.ofNat 2) S T))
  have hcross :
      ((Q'.ofNat 2 * T) * S + S * (Q'.ofNat 2 * T)).eqv
        (Q'.ofNat 4 * (S * T)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp1 hp2) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv (Q'.ofNat 2) (Q'.ofNat 2) (S * T))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  have hregroup :
      ((S * S + (Q'.ofNat 2 * T) * S) + S * (Q'.ofNat 2 * T)).eqv
        (S * S + Q'.ofNat 4 * (S * T)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (S * S) ((Q'.ofNat 2 * T) * S)
        (S * (Q'.ofNat 2 * T)))
      (Q'.add_eqv_congr_left (S * S) _ _ hcross)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hregroup)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hright)))

private theorem boxTerm_nonneg (a b s : Nat) :
    (0 : Q') ≤ fusionInd a b s * (coeffW halfW a * coeffW halfW b) :=
  Q'.mul_nonneg _ _ (fusionInd_nonneg a b s)
    (Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) a)
      (coeffW_nonneg (by decide) b))

/-! ## 2. Central terms actually occur in the middle boxes -/

private theorem fusionInd_odd_central_left (m : Nat) :
    fusionInd m (m + 1) (2 * m + 1) = 1 := by
  unfold fusionInd
  have hok : fusionOK m (m + 1) (2 * m + 1) = true := by
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff]
    have hmax : Nat.max m (m + 1) = m + 1 := Nat.max_eq_right (by omega)
    have hmin : Nat.min m (m + 1) = m := Nat.min_eq_left (by omega)
    rw [hmax, hmin]
    refine ⟨by omega, by omega, ?_⟩
    have hpar : m + (m + 1) + (2 * m + 1) = 2 * (2 * m + 1) := by omega
    rw [hpar, Nat.mul_comm 2 (2 * m + 1), Nat.mul_mod_left]
  rw [hok]; rfl

private theorem fusionInd_odd_central_right (m : Nat) :
    fusionInd (m + 1) m (2 * m + 1) = 1 := by
  unfold fusionInd
  have hok : fusionOK (m + 1) m (2 * m + 1) = true := by
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff]
    have hmax : Nat.max (m + 1) m = m + 1 := Nat.max_eq_left (by omega)
    have hmin : Nat.min (m + 1) m = m := Nat.min_eq_right (by omega)
    rw [hmax, hmin]
    refine ⟨by omega, by omega, ?_⟩
    have hpar : m + 1 + m + (2 * m + 1) = 2 * (2 * m + 1) := by omega
    rw [hpar, Nat.mul_comm 2 (2 * m + 1), Nat.mul_mod_left]
  rw [hok]; rfl

private theorem fusionInd_even_central (m : Nat) :
    fusionInd (m + 1) (m + 1) (2 * m + 2) = 1 := by
  unfold fusionInd
  have hok : fusionOK (m + 1) (m + 1) (2 * m + 2) = true := by
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff]
    have hmax : Nat.max (m + 1) (m + 1) = m + 1 := Nat.max_self _
    have hmin : Nat.min (m + 1) (m + 1) = m + 1 := Nat.min_self _
    rw [hmax, hmin]
    refine ⟨by omega, by omega, ?_⟩
    have hpar : m + 1 + (m + 1) + (2 * m + 2) = 2 * (2 * m + 2) := by omega
    rw [hpar, Nat.mul_comm 2 (2 * m + 2), Nat.mul_mod_left]
  rw [hok]; rfl

private theorem fusionInd_even_shift_left (m : Nat) :
    fusionInd m (m + 2) (2 * m + 2) = 1 := by
  unfold fusionInd
  have hok : fusionOK m (m + 2) (2 * m + 2) = true := by
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff]
    have hmax : Nat.max m (m + 2) = m + 2 := Nat.max_eq_right (by omega)
    have hmin : Nat.min m (m + 2) = m := Nat.min_eq_left (by omega)
    rw [hmax, hmin]
    refine ⟨by omega, by omega, ?_⟩
    have hpar : m + (m + 2) + (2 * m + 2) = 2 * (2 * m + 2) := by omega
    rw [hpar, Nat.mul_comm 2 (2 * m + 2), Nat.mul_mod_left]
  rw [hok]; rfl

private theorem fusionInd_even_shift_right (m : Nat) :
    fusionInd (m + 2) m (2 * m + 2) = 1 := by
  unfold fusionInd
  have hok : fusionOK (m + 2) m (2 * m + 2) = true := by
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff]
    have hmax : Nat.max (m + 2) m = m + 2 := Nat.max_eq_left (by omega)
    have hmin : Nat.min (m + 2) m = m := Nat.min_eq_right (by omega)
    rw [hmax, hmin]
    refine ⟨by omega, by omega, ?_⟩
    have hpar : m + 2 + m + (2 * m + 2) = 2 * (2 * m + 2) := by omega
    rw [hpar, Nat.mul_comm 2 (2 * m + 2), Nat.mul_mod_left]
  rw [hok]; rfl

/-- The two central odd antidiagonal terms are present whenever the finite
triangle reaches `m+1`. -/
theorem boxSum_odd_central_lower (N m : Nat) (hm : m + 1 ≤ N) :
    coeffW halfW m * coeffW halfW (m + 1) +
        coeffW halfW m * coeffW halfW (m + 1) ≤
      boxSum halfW N (2 * m + 1) := by
  let F : Nat → Q' := fun a => fsum (fun b =>
    fusionInd a b (2 * m + 1) * (coeffW halfW a * coeffW halfW b)) (N + 1)
  have hF : ∀ a, (0 : Q') ≤ F a := fun a =>
    fsum_nonneg (fun b => boxTerm_nonneg a b (2 * m + 1)) (N + 1)
  have houter := YMGap.Continuum.EigShiftOrder.fsum_two_term_le
    hF m (m + 1) (by omega) (N + 1) (by omega)
  have hleft :
      fusionInd m (m + 1) (2 * m + 1) *
          (coeffW halfW m * coeffW halfW (m + 1)) ≤ F m :=
    fsum_term_le_of_nonneg (fun b => boxTerm_nonneg m b (2 * m + 1))
      (m + 1) (N + 1) (by omega)
  have hright :
      fusionInd (m + 1) m (2 * m + 1) *
          (coeffW halfW (m + 1) * coeffW halfW m) ≤ F (m + 1) :=
    fsum_term_le_of_nonneg
      (fun b => boxTerm_nonneg (m + 1) b (2 * m + 1))
      m (N + 1) (by omega)
  have hselected := Q'.add_le_add hleft hright
  unfold boxSum
  change _ ≤ fsum F (N + 1)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ hselected houter)
  rw [fusionInd_odd_central_left, fusionInd_odd_central_right]
  ring_qeqv

/-- The even centre and both nearest shifted pairs are present whenever the
finite triangle reaches `m+2`. -/
theorem boxSum_even_three_central_lower (N m : Nat) (hm : m + 2 ≤ N) :
    (coeffW halfW (m + 1) * coeffW halfW (m + 1)) +
        (coeffW halfW m * coeffW halfW (m + 2)) +
        (coeffW halfW m * coeffW halfW (m + 2)) ≤
      boxSum halfW N (2 * m + 2) := by
  let F : Nat → Q' := fun a => fsum (fun b =>
    fusionInd a b (2 * m + 2) * (coeffW halfW a * coeffW halfW b)) (N + 1)
  have hF : ∀ a, (0 : Q') ≤ F a := fun a =>
    fsum_nonneg (fun b => boxTerm_nonneg a b (2 * m + 2)) (N + 1)
  have houter := YMGap.Continuum.WHMarginTailClose.fsum_three_term_le
    hF m (m + 1) (m + 2) (by omega) (by omega) (N + 1) (by omega)
  have hc :
      fusionInd (m + 1) (m + 1) (2 * m + 2) *
          (coeffW halfW (m + 1) * coeffW halfW (m + 1)) ≤ F (m + 1) :=
    fsum_term_le_of_nonneg
      (fun b => boxTerm_nonneg (m + 1) b (2 * m + 2))
      (m + 1) (N + 1) (by omega)
  have hl :
      fusionInd m (m + 2) (2 * m + 2) *
          (coeffW halfW m * coeffW halfW (m + 2)) ≤ F m :=
    fsum_term_le_of_nonneg (fun b => boxTerm_nonneg m b (2 * m + 2))
      (m + 2) (N + 1) (by omega)
  have hr :
      fusionInd (m + 2) m (2 * m + 2) *
          (coeffW halfW (m + 2) * coeffW halfW m) ≤ F (m + 2) :=
    fsum_term_le_of_nonneg (fun b => boxTerm_nonneg (m + 2) b (2 * m + 2))
      m (N + 1) (by omega)
  have hselected := Q'.add_le_add (Q'.add_le_add hl hc) hr
  unfold boxSum
  change _ ≤ fsum F (N + 1)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ hselected houter)
  rw [fusionInd_even_central, fusionInd_even_shift_left,
    fusionInd_even_shift_right]
  ring_qeqv

/-! ## 3. Endpoint all-cutoff interlacing -/

theorem even_box_interlacing_at_half
    (N m : Nat) (hm : m + 1 ≤ N) :
    boxSum halfW N (2 * m) * boxSum halfW N (2 * m + 2) ≤
      boxSum halfW N (2 * m + 1) * boxSum halfW N (2 * m + 1) := by
  let A := coeffW halfW m * coeffW halfW (m + 1)
  have hA0 : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (coeffW_nonneg (by decide) m) (coeffW_nonneg (by decide) (m + 1))
  have hmid : A + A ≤ boxSum halfW N (2 * m + 1) := by
    simpa [A] using boxSum_odd_central_lower N m hm
  have hrightCeiling :
      boxSum halfW N (2 * m + 2) ≤ Q'.mkPos 13 8 (by decide) *
        (coeffW halfW (m + 1) * coeffW halfW (m + 1)) := by
    have hindex : 2 * (m + 1) = 2 * m + 2 := by omega
    simpa only [hindex] using boxSum_even_ceiling N (m + 1)
  have houter := even_first_shell_dominates_negative N m
    (boxSum_even_ceiling N m) hrightCeiling
  have houterA :
      boxSum halfW N (2 * m) * boxSum halfW N (2 * m + 2) ≤
        Q'.ofNat 3 * (A * A) :=
    Q'.le_trans' _ _ _ houter (Q'.le_of_eqv (by
      simp only [A]
      ring_qeqv))
  have h34 : Q'.ofNat 3 * (A * A) ≤ Q'.ofNat 4 * (A * A) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide)
      (Q'.mul_nonneg _ _ hA0 hA0)
  have hbase : Q'.ofNat 4 * (A * A) ≤ (A + A) * (A + A) :=
    Q'.le_of_eqv (Q'.eqv_symm
      (YMGap.Continuum.FusionCoreStepRoundG.two_two_mul_eqv A A))
  have hmid0 : (0 : Q') ≤ boxSum halfW N (2 * m + 1) :=
    YMGap.Continuum.FusionCoreInduction.boxSum_nonneg (by decide) _ _
  have hsquare := mul_le_mul_nonneg hmid hmid
    (Q'.zero_le_add A A hA0 hA0) hmid0
  exact Q'.le_trans' _ _ _ houterA
    (Q'.le_trans' _ _ _ h34 (Q'.le_trans' _ _ _ hbase hsquare))

/-- The quotient-ring scalar core of the odd-channel close.  Isolating it
keeps elaboration independent of the large coefficient expressions. -/
private theorem odd_scalar_close {A B C D q : Q'}
    (hC0 : (0 : Q') ≤ C) (hD0 : (0 : Q') ≤ D)
    (hCD0 : (0 : Q') ≤ C * D)
    (hconst : (q * q) * Q'.ofNat 4 ≤ Q'.ofNat 5)
    (hABCD : (A * B).eqv (C * D))
    (h4D : Q'.ofNat 4 * D ≤ C) :
    (q * (Q'.ofNat 2 * A)) * (q * (Q'.ofNat 2 * B)) ≤
      (C + D + D) * (C + D + D) := by
  have hfactor :
      ((q * (Q'.ofNat 2 * A)) * (q * (Q'.ofNat 2 * B))).eqv
        (((q * q) * Q'.ofNat 4) * (A * B)) := by
    ring_qeqv
  have hfactorCD :
      (((q * q) * Q'.ofNat 4) * (A * B)).eqv
        (((q * q) * Q'.ofNat 4) * (C * D)) :=
    Q'.mul_eqv_congr_left _ _ _ hABCD
  have hfive :
      (q * (Q'.ofNat 2 * A)) * (q * (Q'.ofNat 2 * B)) ≤
        Q'.ofNat 5 * (C * D) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfactor hfactorCD))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hconst hCD0)
  have h4CD : Q'.ofNat 4 * (C * D) ≤ C * C := by
    refine Q'.le_trans' _ (C * (Q'.ofNat 4 * D)) _ ?_ ?_
    · exact Q'.le_of_eqv (by ring_qeqv)
    · exact Q'.mul_le_mul_of_nonneg_left _ _ _ h4D hC0
  have hCDle4CD : C * D ≤ Q'.ofNat 4 * (C * D) := by
    refine Q'.le_trans' _ ((1 : Q') * (C * D)) _ ?_ ?_
    · exact Q'.ge_of_eqv (Q'.one_mul_eqv (C * D))
    · exact Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) hCD0
  have hfiveBase : Q'.ofNat 5 * (C * D) ≤
      C * C + Q'.ofNat 4 * (C * D) := by
    have hsplit : (Q'.ofNat 5 * (C * D)).eqv
        (Q'.ofNat 4 * (C * D) + C * D) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 5)
          (Q'.ofNat 4 + (1 : Q')) (C * D) (by decide)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv (Q'.ofNat 4) (1 : Q') (C * D)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (C * D))
    have hfirst := Q'.add_le_add h4CD (Q'.le_refl' (C * D))
    have hsecond := Q'.add_le_add (Q'.le_refl' (C * C)) hCDle4CD
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.le_trans' _ _ _ hfirst hsecond)
  have hbinomial := sq_binomial_lower C D hD0
  have hdouble : (C + Q'.ofNat 2 * D).eqv (C + D + D) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left C _ _
        (YMGap.Constructive.ExpNeg.two_mul_eqv D)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv C D D)
  have hsquareForm :
      ((C + Q'.ofNat 2 * D) * (C + Q'.ofNat 2 * D)).eqv
        ((C + D + D) * (C + D + D)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hdouble)
      (Q'.mul_eqv_congr_left _ _ _ hdouble)
  exact Q'.le_trans' _ _ _ hfive
    (Q'.le_trans' _ _ _ hfiveBase
      (Q'.le_trans' _ _ _ hbinomial (Q'.le_of_eqv hsquareForm)))

theorem odd_box_interlacing_at_half
    (N m : Nat) (hm : m + 2 ≤ N) :
    boxSum halfW N (2 * m + 1) * boxSum halfW N (2 * m + 3) ≤
      boxSum halfW N (2 * m + 2) * boxSum halfW N (2 * m + 2) := by
  let A := coeffW halfW m * coeffW halfW (m + 1)
  let B := coeffW halfW (m + 1) * coeffW halfW (m + 2)
  let C := coeffW halfW (m + 1) * coeffW halfW (m + 1)
  let D := coeffW halfW m * coeffW halfW (m + 2)
  let q := Q'.mkPos 35 32 (by decide)
  have hA0 : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (coeffW_nonneg (by decide) m) (coeffW_nonneg (by decide) (m + 1))
  have hC0 : (0 : Q') ≤ C := Q'.mul_nonneg _ _
    (coeffW_nonneg (by decide) (m + 1))
    (coeffW_nonneg (by decide) (m + 1))
  have hD0 : (0 : Q') ≤ D := Q'.mul_nonneg _ _
    (coeffW_nonneg (by decide) m) (coeffW_nonneg (by decide) (m + 2))
  have hleft := boxSum_odd_ceiling N m
  have hright : boxSum halfW N (2 * m + 3) ≤ q * (Q'.ofNat 2 * B) := by
    have hindex : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    have hcoeff : m + 1 + 1 = m + 2 := by omega
    simpa only [hindex, hcoeff] using boxSum_odd_ceiling N (m + 1)
  have hright0 : (0 : Q') ≤ boxSum halfW N (2 * m + 3) :=
    YMGap.Continuum.FusionCoreInduction.boxSum_nonneg (by decide) _ _
  have hleftBound0 : (0 : Q') ≤ q * (Q'.ofNat 2 * A) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (by decide) hA0)
  have hceilProduct := mul_le_mul_nonneg
    (by simpa [q, A] using hleft) hright hright0 hleftBound0
  have hCD0 : (0 : Q') ≤ C * D := Q'.mul_nonneg _ _ hC0 hD0
  have hconst : (q * q) * Q'.ofNat 4 ≤ Q'.ofNat 5 := by
    unfold q
    decide
  have h4D : Q'.ofNat 4 * D ≤ C := by
    simpa [C, D] using perDiagonal_newton (by decide) (by decide) m
  have hABCD : (A * B).eqv (C * D) := by
    change ((coeffW halfW m * coeffW halfW (m + 1)) *
      (coeffW halfW (m + 1) * coeffW halfW (m + 2))).eqv
      ((coeffW halfW (m + 1) * coeffW halfW (m + 1)) *
        (coeffW halfW m * coeffW halfW (m + 2)))
    ring_qeqv
  have hscalar := odd_scalar_close hC0 hD0 hCD0 hconst hABCD h4D
  have hmid : C + D + D ≤ boxSum halfW N (2 * m + 2) := by
    simpa [C, D] using boxSum_even_three_central_lower N m hm
  have hmid0 : (0 : Q') ≤ boxSum halfW N (2 * m + 2) :=
    YMGap.Continuum.FusionCoreInduction.boxSum_nonneg (by decide) _ _
  have hsquare := mul_le_mul_nonneg hmid hmid
    (Q'.zero_le_add _ D (Q'.zero_le_add C D hC0 hD0) hD0) hmid0
  exact Q'.le_trans' _ _ _ hceilProduct
    (Q'.le_trans' _ _ _ hscalar hsquare)

theorem finite_triangle_interlacing_at_half
    (N s : Nat) (hs : s + 2 ≤ 2 * N) :
    (0 : Q') ≤ YMGap.Continuum.FusionCoreStepRoundB.quadDiff halfW N s := by
  have hbox : boxSum halfW N s * boxSum halfW N (s + 2) ≤
      boxSum halfW N (s + 1) * boxSum halfW N (s + 1) := by
    by_cases heven : s % 2 = 0
    · let m := s / 2
      have hsform : s = 2 * m := by unfold m; omega
      rw [hsform]
      exact even_box_interlacing_at_half N m (by omega)
    · let m := s / 2
      have hsform : s = 2 * m + 1 := by unfold m; omega
      rw [hsform]
      exact odd_box_interlacing_at_half N m (by omega)
  have hdiff : (0 : Q') ≤
      boxSum halfW N (s + 1) * boxSum halfW N (s + 1) +
        -(boxSum halfW N s * boxSum halfW N (s + 2)) :=
    Q'.sub_nonneg_of_le hbox
  exact Q'.le_trans' _ _ _ hdiff
    (Q'.le_of_eqv
      (YMGap.Continuum.FusionCoreStepRoundB.boxDiff_eq_quadDiff halfW N s))

/-- Unconditional all-cutoff endpoint closure from the proved strand ceilings
and the explicit central-shell lower bounds. -/
def uniformBoxLogConcave_half :
    YMGap.Continuum.FusionCoreStepRoundA.UniformBoxLogConcave halfW :=
  uniformBoxLogConcave_of_finite_interlacing (by decide) (by decide)
    finite_triangle_interlacing_at_half

/-! ## 4. Exact interval consumer from the physical prefix reserve -/

def allCutoffBernsteinCertificatesOfPrefixReserve
    (reserve : AllCutoffPhysicalPrefixReserve) :
    ∀ N, FiniteTriangleBernsteinCertificate N := fun N =>
  finiteTriangleBernsteinCertificateOfClearedPrefixes N
    (fun s hs K _ => reserve N s K hs)

def uniformBoxLogConcave_of_physical_prefix_reserve
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ halfW)
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (reserve : AllCutoffPhysicalPrefixReserve) :
    YMGap.Continuum.FusionCoreStepRoundA.UniformBoxLogConcave w :=
  uniformBoxLogConcave_of_bernstein_certificates hw0 hwH hstrong
    (allCutoffBernsteinCertificatesOfPrefixReserve reserve)

/-! ## 5. Exact interval seam (discharged downstream)

The endpoint is unconditional.  Promotion to the whole physical interval
through the canonical Bernstein rows factors through the integer shell
statement below.  It is strictly narrower than the old all-coupling box
inequality: it mentions only the executable term-filtered prefix carrier
already connected exactly to the reconstruction.  The concrete witness is
`FusionBoxPostBoundaryClosure.postBoundaryEvenOddPrefixReserve`.
-/

def EvenOddShellPrefixReserve : Prop :=
  (∀ N m K, 2 * m + 2 ≤ 2 * N →
    0 ≤ boxClearedPowerPrefix N (2 * m) K) ∧
  (∀ N m K, 2 * m + 3 ≤ 2 * N →
    0 ≤ boxClearedPowerPrefix N (2 * m + 1) K)

theorem allCutoffPhysicalPrefixReserve_of_evenOdd
    (h : EvenOddShellPrefixReserve) : AllCutoffPhysicalPrefixReserve := by
  intro N s K hs
  by_cases heven : s % 2 = 0
  · let m := s / 2
    have hsform : s = 2 * m := by unfold m; omega
    have hs' : 2 * m + 2 ≤ 2 * N := by omega
    rw [hsform]
    exact h.1 N m K hs'
  · let m := s / 2
    have hsform : s = 2 * m + 1 := by unfold m; omega
    have hs' : 2 * m + 3 ≤ 2 * N := by omega
    rw [hsform]
    exact h.2 N m K hs'

#print axioms YMGap.Continuum.FusionBoxShellReserve.boxSum_odd_central_lower
#print axioms YMGap.Continuum.FusionBoxShellReserve.boxSum_even_three_central_lower
#print axioms YMGap.Continuum.FusionBoxShellReserve.even_box_interlacing_at_half
#print axioms YMGap.Continuum.FusionBoxShellReserve.odd_box_interlacing_at_half
#print axioms YMGap.Continuum.FusionBoxShellReserve.finite_triangle_interlacing_at_half
#print axioms YMGap.Continuum.FusionBoxShellReserve.uniformBoxLogConcave_half
#print axioms YMGap.Continuum.FusionBoxShellReserve.allCutoffBernsteinCertificatesOfPrefixReserve
#print axioms YMGap.Continuum.FusionBoxShellReserve.uniformBoxLogConcave_of_physical_prefix_reserve
#print axioms YMGap.Continuum.FusionBoxShellReserve.allCutoffPhysicalPrefixReserve_of_evenOdd

end YMGap.Continuum.FusionBoxShellReserve
