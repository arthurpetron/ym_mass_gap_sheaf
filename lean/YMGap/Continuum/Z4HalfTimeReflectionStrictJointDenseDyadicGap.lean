/-
# Removing the dense presentation prefactor by dyadic moments

The thermodynamic clustering theorem bounds the completed same-object moment

  m_n(v) <= P(v) * q^n,      q = 1/16,

where `P(v)` still depends on the chosen strict-cylinder presentation.  This
file supplies the constructive spectral-radius step which removes that fixed
prefactor.  The engine is stated first for one `CReal` moment sequence.  It
uses only eventual order, a rational strict-excess witness, dyadic
log-convexity, and rational geometric domination.

No spectral measure, choice principle, or decidable equality on completed
reals is used.  The strict-excess branch is detected at rational
approximations; if it existed, it would produce a rational rate `r > q` whose
dyadic powers are lower bounds for the same moments, contradicting the
presentation-level `P*q^n` upper envelope.
-/

import YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.MeanExpConvexProgress
import YMGap.Continuum.RCDistBridge
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem q_add_four_eighths_le_add_epsilon
    (x epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    x + ((Q'.mkPos 1 8 (by decide)) * epsilon +
      ((Q'.mkPos 1 8 (by decide)) * epsilon +
        ((Q'.mkPos 1 8 (by decide)) * epsilon +
          (Q'.mkPos 1 8 (by decide)) * epsilon))) ≤ x + epsilon := by
  apply Q'.add_le_add_left
  have hnonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  have hscale :
      ((Q'.mkPos 1 8 (by decide) +
        (Q'.mkPos 1 8 (by decide) +
          (Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 8 (by decide)))) * epsilon) ≤
        (1 : Q') * epsilon :=
    Q'.mul_le_mul_of_nonneg_right _ _ epsilon (by decide) hnonnegative
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv (Q'.one_mul_eqv epsilon)))

private theorem q_add_six_eighths_le_add_epsilon
    (x epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    x + ((Q'.mkPos 1 8 (by decide)) * epsilon +
      ((Q'.mkPos 1 8 (by decide)) * epsilon +
        ((Q'.mkPos 1 8 (by decide)) * epsilon +
          ((Q'.mkPos 1 8 (by decide)) * epsilon +
            ((Q'.mkPos 1 8 (by decide)) * epsilon +
              (Q'.mkPos 1 8 (by decide)) * epsilon))))) ≤ x + epsilon := by
  apply Q'.add_le_add_left
  have hnonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  have hscale :
      ((Q'.mkPos 1 8 (by decide) +
        (Q'.mkPos 1 8 (by decide) +
          (Q'.mkPos 1 8 (by decide) +
            (Q'.mkPos 1 8 (by decide) +
              (Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 8 (by decide)))))) * epsilon) ≤
        (1 : Q') * epsilon :=
    Q'.mul_le_mul_of_nonneg_right _ _ epsilon (by decide) hnonnegative
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv (Q'.one_mul_eqv epsilon)))

/-! ## 1. Located eventual order from exclusion of positive excess -/

/-- If the difference `A-B` cannot carry an eventual positive rational
witness, then `A <= B` in eventual order.  This is the constructive located
order step: at one common Cauchy stage, the rational comparison is decidable.
The negative branch would make `A-B` eventually at least `epsilon/8`. -/
theorem leEv_of_no_posEv_sub {A B : CReal}
    (hno : PosEv (CReal.sub A B) -> False) : CReal.leEv A B := by
  intro epsilon hepsilon
  let e : Q' := (Q'.mkPos 1 8 (by decide)) * epsilon
  have he : (0 : Q') < e := Q'.mul_pos (by decide) hepsilon
  obtain ⟨NA, hA⟩ := A.cauchy e he
  obtain ⟨NB, hB⟩ := B.cauchy e he
  let N : Nat := max NA NB
  have hNA : NA ≤ N := Nat.le_max_left _ _
  have hNB : NB ≤ N := Nat.le_max_right _ _
  by_cases hlocated :
      A.approx N ≤ B.approx N + (e + (e + (e + e)))
  · refine ⟨N, fun n hn => ?_⟩
    have hAn : A.approx n ≤ A.approx N + e := (hA N n hNA (Nat.le_trans hNA hn)).2
    have hBn : B.approx N ≤ B.approx n + e := (hB N n hNB (Nat.le_trans hNB hn)).1
    have hchain :
        A.approx n ≤
          B.approx n + (e + (e + (e + (e + (e + e))))) := by
      refine Q'.le_trans' _ _ _ hAn ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ e hlocated) ?_
      have hshift := Q'.add_le_add_right _ _
        (e + (e + (e + (e + e)))) hBn
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
        (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv (by ring_qeqv)))
    exact Q'.le_trans' _ _ _ hchain
      (q_add_six_eighths_le_add_epsilon (B.approx n) epsilon hepsilon)
  · exfalso
    apply hno
    refine posEv_of_eventually he ?_
    refine ⟨N, fun n hn => ?_⟩
    have hreverse :
        B.approx N + (e + (e + (e + e))) ≤ A.approx N :=
      Q'.le_of_not_le hlocated
    have hAN : A.approx N ≤ A.approx n + e :=
      (hA N n hNA (Nat.le_trans hNA hn)).1
    have hBN : B.approx n ≤ B.approx N + e :=
      (hB N n hNB (Nat.le_trans hNB hn)).2
    have hlarge : B.approx n + (e + e) ≤ A.approx n := by
      have h1 : B.approx N + (e + (e + (e + e))) ≤ A.approx n + e :=
        Q'.le_trans' _ _ _ hreverse hAN
      have h2 : B.approx N + (e + (e + e)) ≤ A.approx n := by
        exact le_of_add_le_add_right (c := e)
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv)) h1)
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ (e + e) hBN)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv)) h2)
    have hadd := Q'.add_le_add_right
      (B.approx n + (e + e)) (A.approx n) (-B.approx n) hlarge
    change e ≤ A.approx n + -B.approx n
    have hee : e ≤ e + e :=
      Q'.add_le_self_of_nonneg e e (Q'.le_of_lt he)
    have eleft :
        ((B.approx n + (e + e)) + -B.approx n).eqv (e + e) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (B.approx n) (e + e) (-B.approx n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (B.approx n) ((e + e) + -B.approx n)
          (-B.approx n + (e + e)) (Q'.add_comm_eqv (e + e) (-B.approx n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (B.approx n) (-B.approx n) (e + e))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (B.approx n + -B.approx n) 0 (e + e)
          (Q'.add_neg_self_eqv (B.approx n))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' (e + e))
    exact Q'.le_trans' _ _ _ hee
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv eleft) hadd)

#print axioms leEv_of_no_posEv_sub

/-! ## 2. Positive-factor cancellation in eventual order -/

/-- A strictly positive `CReal` factor can be cancelled on the right of an
eventual weak inequality.  The proof uses the explicit eventual rational lower
bound supplied by `PosEv`; it does not form a reciprocal real. -/
theorem leEv_cancel_mul_right_posEv {A B F : CReal}
    (hF : PosEv F)
    (hAB : CReal.leEv (CReal.mul A F) (CReal.mul B F)) :
    CReal.leEv A B := by
  obtain ⟨f, hf, Nf, hNf⟩ := eventually_ge_of_posEv hF
  intro epsilon hepsilon
  have hfepsilon : (0 : Q') < f * epsilon := Q'.mul_pos hf hepsilon
  obtain ⟨Nmul, hNmul⟩ := hAB (f * epsilon) hfepsilon
  refine ⟨max Nf Nmul, fun n hn => ?_⟩
  have hnF : Nf ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnMul : Nmul ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hfactor : f ≤ F.approx n := hNf n hnF
  have hproduct :
      A.approx n * F.approx n ≤
        B.approx n * F.approx n + f * epsilon :=
    hNmul n hnMul
  by_cases hdirect : A.approx n ≤ B.approx n
  · exact Q'.le_trans' _ _ _ hdirect
      (Q'.add_le_self_of_nonneg (B.approx n) epsilon (Q'.le_of_lt hepsilon))
  · have hBA : B.approx n ≤ A.approx n := Q'.le_of_not_le hdirect
    have hdiff0 : (0 : Q') ≤ A.approx n + -B.approx n :=
      Q'.sub_nonneg_of_le hBA
    have hdiffFactor :
        (A.approx n + -B.approx n) * F.approx n ≤ f * epsilon := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.sub_mul_eqv (A.approx n) (B.approx n) (F.approx n)))
        (Q'.sub_le_of_le_add hproduct)
    have hscaled :
        (A.approx n + -B.approx n) * f ≤ f * epsilon := by
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left f (F.approx n)
          (A.approx n + -B.approx n) hfactor hdiff0)
        hdiffFactor
    have hcancel : A.approx n + -B.approx n ≤ epsilon := by
      apply Q'.le_of_mul_le_mul_left
        (c := f)
      · exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_comm_eqv f (A.approx n + -B.approx n)))
          hscaled
      · exact hf
    exact Q'.le_add_of_sub_le hcancel

#print axioms leEv_cancel_mul_right_posEv

/-! ## 3. Rational and `CReal` plumbing for the dyadic engine -/

private theorem leEv_ofQ'_reflect {p q : Q'}
    (h : CReal.leEv (CReal.ofQ' p) (CReal.ofQ' q)) : p ≤ q := by
  refine Q'.le_of_forall_pos_add ?_
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact hN N (Nat.le_refl N)

private theorem posEv_mono {A B : CReal}
    (hA : PosEv A) (hAB : CReal.leEv A B) : PosEv B := by
  obtain ⟨d, hd, hdA⟩ := hA
  exact ⟨d, hd, CReal.leEv_trans hdA hAB⟩

/-- Rearrange a positive lower bound on `A-B` into the additive strict lower
bound `B+d <= A`, entirely in eventual order. -/
private theorem leEv_add_ofQ'_of_leEv_sub {A B : CReal} {d : Q'}
    (h : CReal.leEv (CReal.ofQ' d) (CReal.sub A B)) :
    CReal.leEv (CReal.add B (CReal.ofQ' d)) A := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  show B.approx n + d ≤ A.approx n + epsilon
  have hadd := Q'.add_le_add_left (B.approx n) d
    ((A.approx n + -B.approx n) + epsilon) hd
  have hcancel :
      (B.approx n + ((A.approx n + -B.approx n) + epsilon)).eqv
        (A.approx n + epsilon) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv (B.approx n) (A.approx n + -B.approx n) epsilon)) ?_
    refine Q'.add_eqv_congr_right _ _ epsilon ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (B.approx n) (A.approx n) (-B.approx n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (B.approx n + A.approx n)
        (A.approx n + B.approx n) (-B.approx n)
        (Q'.add_comm_eqv (B.approx n) (A.approx n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (A.approx n) (B.approx n) (-B.approx n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (A.approx n) _ _
        (Q'.add_neg_self_eqv (B.approx n))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (A.approx n))
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hcancel)

private theorem cadd_zero_left (A : CReal) :
    CReal.Equiv (CReal.add CReal.czero A) A :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A.approx n)))

private theorem cscale_add (a b : Q') (A : CReal) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' (a + b)) A)
      (CReal.add
        (CReal.mul (CReal.ofQ' a) A)
        (CReal.mul (CReal.ofQ' b) A)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_mul_eqv a b (A.approx n))

private theorem cscale_ofQ' (a b : Q') :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' a) (CReal.ofQ' b))
      (CReal.ofQ' (a * b)) :=
  CReal.Equiv.symm (ofQ'_mul a b)

private theorem cscale_zero (a : Q') :
    CReal.Equiv (CReal.mul (CReal.ofQ' a) CReal.czero) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => CRealLog.mul_zero_eqv a)

private theorem leEv_scale_nonneg {a : Q'} (ha : (0 : Q') ≤ a)
    {A : CReal} (hA : CReal.leEv CReal.czero A) :
    CReal.leEv CReal.czero (CReal.mul (CReal.ofQ' a) A) := by
  exact CReal.leEv_trans
    (CReal.leEv_of_equiv (CReal.Equiv.symm (cscale_zero a)))
    (CReal.leEv_smul_nonneg ha hA)

private def dyadic : Nat → Nat
  | 0 => 1
  | k + 1 => dyadic k + dyadic k

private theorem dyadic_pos : ∀ k : Nat, 0 < dyadic k
  | 0 => by decide
  | k + 1 => by
      have hk := dyadic_pos k
      simp only [dyadic]
      omega

private theorem self_le_dyadic : ∀ k : Nat, k ≤ dyadic k
  | 0 => Nat.zero_le 1
  | k + 1 => by
      have hk := self_le_dyadic k
      have hkpos := dyadic_pos k
      simp only [dyadic]
      omega

/-- Once the faster geometric term has overtaken the slower envelope, it
remains ahead at every larger exponent. -/
private theorem geometric_strict_persists
    {b P q r : Q'}
    (hb : (0 : Q') < b) (hq : (0 : Q') < q)
    (hqr : q ≤ r) {n N : Nat} (hnN : n ≤ N)
    (hstrict : P * q ^ n < b * r ^ n) :
    P * q ^ N < b * r ^ N := by
  let d := N - n
  have hnd : n + d = N := Nat.add_sub_of_le hnN
  have hqd : (0 : Q') < q ^ d := pow_pos hq d
  have hmul :
      (P * q ^ n) * q ^ d < (b * r ^ n) * q ^ d :=
    mul_lt_mul_of_pos_right hqd hstrict
  have hqd_le_rd : q ^ d ≤ r ^ d :=
    CRealLog.pow_le_pow_base q r (Q'.le_of_lt hq) hqr d
  have hbrn0 : (0 : Q') ≤ b * r ^ n := by
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt hb)
      (Q'.pow_nonneg r (Q'.le_trans' _ _ _ (Q'.le_of_lt hq) hqr) n)
  have hright : (b * r ^ n) * q ^ d ≤ (b * r ^ n) * r ^ d :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hqd_le_rd hbrn0
  have hleftEq :
      (P * q ^ N).eqv ((P * q ^ n) * q ^ d) := by
    rw [← hnd]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left P _ _ (Q'.pow_add_eqv q n d)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv P (q ^ n) (q ^ d))
  have hrightEq :
      ((b * r ^ n) * r ^ d).eqv (b * r ^ N) := by
    rw [← hnd]
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv b (r ^ n) (r ^ d)) ?_
    exact Q'.mul_eqv_congr_left b _ _ (Q'.eqv_symm (Q'.pow_add_eqv r n d))
  exact lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleftEq) hmul)
    (Q'.le_trans' _ _ _ hright (Q'.le_of_eqv hrightEq))

#print axioms geometric_strict_persists

/-! ## 4. Abstract constructive dyadic spectral-radius theorem -/

/-- A nonnegative contractive moment sequence with dyadic log-convexity and a
fixed geometric envelope at rate `q` already satisfies the sharp one-step
bound `m₁ <= q m₀`.  The envelope prefactor `P` disappears. -/
theorem dyadic_geometric_first_le
    (m : Nat → CReal) (q P : Q')
    (hq : (0 : Q') < q) (hP : (0 : Q') < P)
    (hnonnegative : ∀ n, CReal.leEv CReal.czero (m n))
    (hleZero : ∀ n, CReal.leEv (m n) (m 0))
    (hdyadic : ∀ n,
      CReal.leEv (CReal.mul (m n) (m n))
        (CReal.mul (m (n + n)) (m 0)))
    (henvelope : ∀ n,
      CReal.leEv (m n) (CReal.ofQ' (P * q ^ n))) :
    CReal.leEv (m 1) (CReal.mul (CReal.ofQ' q) (m 0)) := by
  apply leEv_of_no_posEv_sub
  intro hexcess
  obtain ⟨d, hd, hdifference⟩ := hexcess
  have hstrict :
      CReal.leEv
        (CReal.add (CReal.mul (CReal.ofQ' q) (m 0)) (CReal.ofQ' d))
        (m 1) :=
    leEv_add_ofQ'_of_leEv_sub hdifference
  have hqM0nonnegative :
      CReal.leEv CReal.czero (CReal.mul (CReal.ofQ' q) (m 0)) :=
    leEv_scale_nonneg (Q'.le_of_lt hq) (hnonnegative 0)
  have hdToStrictLeft :
      CReal.leEv (CReal.ofQ' d)
        (CReal.add (CReal.mul (CReal.ofQ' q) (m 0)) (CReal.ofQ' d)) := by
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv (CReal.Equiv.symm (cadd_zero_left (CReal.ofQ' d))))
      (CReal.leEv_add hqM0nonnegative (CReal.leEv_refl (CReal.ofQ' d)))
  have hdM0 : CReal.leEv (CReal.ofQ' d) (m 0) :=
    CReal.leEv_trans hdToStrictLeft
      (CReal.leEv_trans hstrict (hleZero 1))
  have hM0pos : PosEv (m 0) := ⟨d, hd, hdM0⟩
  have hM0P : CReal.leEv (m 0) (CReal.ofQ' P) := by
    refine CReal.leEv_trans (henvelope 0) (CReal.leEv_of_equiv ?_)
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left P _ _ (pow_zero_eqv q)) ?_
      exact Q'.mul_one_eqv P)
  let c : Q' := Q'.divPos d P hP
  have hc : (0 : Q') < c := Q'.divPos_pos d P hP hd
  let r : Q' := q + c
  have hr : (0 : Q') < r :=
    q_pos_add_nonneg hq (Q'.le_of_lt hc)
  have hqr : q ≤ r :=
    Q'.add_le_self_of_nonneg q c (Q'.le_of_lt hc)
  have hcM0d :
      CReal.leEv (CReal.mul (CReal.ofQ' c) (m 0)) (CReal.ofQ' d) := by
    have hscaled := CReal.leEv_smul_nonneg (Q'.le_of_lt hc) hM0P
    refine CReal.leEv_trans hscaled (CReal.leEv_of_equiv ?_)
    exact CReal.Equiv.trans (cscale_ofQ' c P)
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.divPos_mul_eqv d P hP))
  have hrM0M1 :
      CReal.leEv (CReal.mul (CReal.ofQ' r) (m 0)) (m 1) := by
    have hadd := CReal.leEv_add
      (CReal.leEv_refl (CReal.mul (CReal.ofQ' q) (m 0))) hcM0d
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv (cscale_add q c (m 0)))
      (CReal.leEv_trans hadd hstrict)
  have hlower : ∀ k : Nat,
      CReal.leEv
        (CReal.mul (CReal.ofQ' (r ^ dyadic k)) (m 0))
        (m (dyadic k)) := by
    intro k
    induction k with
    | zero =>
        refine CReal.leEv_trans (CReal.leEv_of_equiv ?_) hrM0M1
        exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
          Q'.mul_eqv_congr_right _ _ ((m 0).approx n) (pow_one_eqv r))
    | succ k ih =>
        have hlowerNonnegative :
            CReal.leEv CReal.czero
              (CReal.mul (CReal.ofQ' (r ^ dyadic k)) (m 0)) :=
          leEv_scale_nonneg
            (Q'.pow_nonneg r (Q'.le_of_lt hr) (dyadic k))
            (hnonnegative 0)
        have hsquareFirst :=
          CReal.leEv_mul_nonneg_left hlowerNonnegative ih
        have hsquareSecond :=
          CReal.leEv_mul_nonneg_left (hnonnegative (dyadic k)) ih
        have hsquare :
            CReal.leEv
              (CReal.mul
                (CReal.mul (CReal.ofQ' (r ^ dyadic k)) (m 0))
                (CReal.mul (CReal.ofQ' (r ^ dyadic k)) (m 0)))
              (CReal.mul (m (dyadic k)) (m (dyadic k))) := by
          exact CReal.leEv_trans hsquareFirst
            (CReal.leEv_trans
              (CReal.leEv_of_equiv
                (CRealAlg.cmul_comm
                  (CReal.mul (CReal.ofQ' (r ^ dyadic k)) (m 0))
                  (m (dyadic k))))
              hsquareSecond)
        have htoDouble := CReal.leEv_trans hsquare (hdyadic (dyadic k))
        have hleftEquiv :
            CReal.Equiv
              (CReal.mul
                (CReal.mul (CReal.ofQ' (r ^ dyadic k)) (m 0))
                (CReal.mul (CReal.ofQ' (r ^ dyadic k)) (m 0)))
              (CReal.mul
                (CReal.mul
                  (CReal.ofQ' (r ^ (dyadic k + dyadic k))) (m 0))
                (m 0)) :=
          SumOfSquares.Equiv_of_approx_eqv (fun n => by
            have hp := Q'.pow_add_eqv r (dyadic k) (dyadic k)
            change
              ((r ^ dyadic k * (m 0).approx n) *
                  (r ^ dyadic k * (m 0).approx n)).eqv
                ((r ^ (dyadic k + dyadic k) * (m 0).approx n) *
                  (m 0).approx n)
            refine Q'.eqv_trans _ _ _
              (YMGap.Continuum.FusionGenFunction.mul_swap4
                (r ^ dyadic k) ((m 0).approx n)
                (r ^ dyadic k) ((m 0).approx n)) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ ((m 0).approx n * (m 0).approx n)
                (Q'.eqv_symm hp)) ?_
            exact Q'.eqv_symm
              (Q'.mul_assoc_eqv (r ^ (dyadic k + dyadic k))
                ((m 0).approx n) ((m 0).approx n)))
        have hproduct :
            CReal.leEv
              (CReal.mul
                (CReal.mul
                  (CReal.ofQ' (r ^ (dyadic k + dyadic k))) (m 0))
                (m 0))
              (CReal.mul (m (dyadic k + dyadic k)) (m 0)) :=
          CReal.leEv_trans (CReal.leEv_of_equiv (CReal.Equiv.symm hleftEquiv))
            htoDouble
        exact leEv_cancel_mul_right_posEv hM0pos hproduct
  obtain ⟨n, hn⟩ := term_exceeds_envelope d P q c hd hP hq hc
  let N := dyadic n
  have hnN : n ≤ N := self_le_dyadic n
  have hfast : P * q ^ N < d * r ^ N :=
    geometric_strict_persists hd hq hqr hnN hn
  have hratLower :
      CReal.leEv (CReal.ofQ' (r ^ N * d))
        (CReal.mul (CReal.ofQ' (r ^ N)) (m 0)) := by
    refine CReal.leEv_trans (CReal.leEv_of_equiv (ofQ'_mul (r ^ N) d)) ?_
    exact CReal.leEv_smul_nonneg
      (Q'.pow_nonneg r (Q'.le_of_lt hr) N) hdM0
  have hconstant :
      CReal.leEv (CReal.ofQ' (r ^ N * d))
        (CReal.ofQ' (P * q ^ N)) :=
    CReal.leEv_trans hratLower
      (CReal.leEv_trans (hlower n) (henvelope N))
  have hslow : r ^ N * d ≤ P * q ^ N := leEv_ofQ'_reflect hconstant
  have hback : d * r ^ N ≤ P * q ^ N :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv d (r ^ N))) hslow
  have hcontr : P * q ^ N < P * q ^ N :=
    lt_of_lt_of_le hfast hback
  exact lt_irrefl' _ hcontr

#print axioms dyadic_geometric_first_le

/-! ## 5. Specialization to the thermodynamic strict-cylinder moments -/

/-- The explicit `CReal` representative of the dense same-object completed
two-step moment supplied by the thermodynamic connected-covariance bridge. -/
def strictJointDenseCentralMoment
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (n : Nat) : CReal :=
  orientedDoubledTimeCentralConnectedLimit
    coupling hcoupling hle n vector

/-- The presentation-dependent prefactor has disappeared: every dense
vacuum-orthogonal vector obeys the common one-step moment bound with the exact
rate `anchorDecoratedDoubledTimeRate = 1/16`. -/
theorem strictJointCylinderCompletedTwoStepAutocorrelation_embed_RC_le_rate
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedTwoStepAutocorrelation hcoupling hle
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
          (StrictJointCylinderStage.mk base vector)) 1)
      (CReal.RCscale anchorDecoratedDoubledTimeRate
        (strictJointCylinderCompletedTwoStepAutocorrelation hcoupling hle
          ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
            (StrictJointCylinderStage.mk base vector)) 0)) := by
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
      hcoupling hle 1 vector horthogonal,
    strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
      hcoupling hle 0 vector horthogonal]
  change CReal.leEv
    (strictJointDenseCentralMoment hcoupling hle vector 1)
    (CReal.mul (CReal.ofQ' anchorDecoratedDoubledTimeRate)
      (strictJointDenseCentralMoment hcoupling hle vector 0))
  apply dyadic_geometric_first_le
    (m := strictJointDenseCentralMoment hcoupling hle vector)
    (q := anchorDecoratedDoubledTimeRate)
    (P := couplingParametricStrictSignedPositivePrefactor vector.roots.length
      (strictJointFingerprintSpace vector.roots.length)
      (strictJointFingerprintSpace vector.roots.length)
      vector.coefficient vector.coefficient)
  · exact anchorDecoratedDoubledTimeRate_pos
  · exact couplingParametricStrictSignedPositivePrefactor_pos
      vector.roots.length
      (strictJointFingerprintSpace vector.roots.length)
      (strictJointFingerprintSpace vector.roots.length)
      vector.coefficient vector.coefficient
  · intro n
    have hn := strictJointCylinderCompletedTwoStepAutocorrelation_nonnegative
      hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (StrictJointCylinderStage.mk base vector)) n
    rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
      hcoupling hle n vector horthogonal] at hn
    exact hn
  · intro n
    have hn := strictJointCylinderCompletedTwoStepAutocorrelation_le_zero
      hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (StrictJointCylinderStage.mk base vector)) n
    rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle n vector horthogonal,
      strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle 0 vector horthogonal] at hn
    exact hn
  · intro n
    have hn := strictJointCylinderCompletedTwoStepAutocorrelation_dyadic
      hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (StrictJointCylinderStage.mk base vector)) n
    rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle n vector horthogonal,
      strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle (n + n) vector horthogonal,
      strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle 0 vector horthogonal] at hn
    exact hn
  · intro n
    have hn :=
      strictJointCylinderCompletedTwoStepAutocorrelation_embed_RC_le_geometric
        hcoupling hle n vector horthogonal
    rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
      hcoupling hle n vector horthogonal] at hn
    exact hn

/-- Uniform dense vacuum-complement form gap for the concrete completed
two-step transfer.  This is the direct operator-form rendering of the sharp
same-object moment estimate above. -/
theorem strictJointCylinderCompletedTwoStepTransfer_embed_form_gap
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle
          ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
            (StrictJointCylinderStage.mk base vector)))
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
          (StrictJointCylinderStage.mk base vector)))
      (CReal.RCscale anchorDecoratedDoubledTimeRate
        (strictJointCylinderCompletedInner hcoupling hle
          ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
            (StrictJointCylinderStage.mk base vector))
          ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
            (StrictJointCylinderStage.mk base vector)))) := by
  rw [← strictJointCylinderCompletedTwoStepAutocorrelation_one hcoupling hle,
    ← strictJointCylinderCompletedTwoStepAutocorrelation_zero hcoupling hle]
  exact strictJointCylinderCompletedTwoStepAutocorrelation_embed_RC_le_rate
    hcoupling hle vector horthogonal

/-- The common dense separator is genuinely strict and works for every stage
presentation of every dense vacuum-orthogonal vector. -/
theorem anchorDecoratedDoubledTimeRate_dense_vacuum_form_gap
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    (0 : Q') ≤ anchorDecoratedDoubledTimeRate ∧
    anchorDecoratedDoubledTimeRate < (1 : Q') ∧
    ∀ (base : Nat) (vector : StrictJointCylinderVector base),
      StrictJointVacuumOrthogonal hcoupling hle vector →
      CReal.RCle
        (strictJointCylinderCompletedInner hcoupling hle
          (strictJointCylinderCompletedTwoStepTransfer hcoupling hle
            ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
              (StrictJointCylinderStage.mk base vector)))
          ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
            (StrictJointCylinderStage.mk base vector)))
        (CReal.RCscale anchorDecoratedDoubledTimeRate
          (strictJointCylinderCompletedInner hcoupling hle
            ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
              (StrictJointCylinderStage.mk base vector))
            ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
              (StrictJointCylinderStage.mk base vector)))) := by
  exact ⟨anchorDecoratedDoubledTimeRate_nonnegative,
    anchorDecoratedDoubledTimeRate_lt_one,
    fun _ vector horthogonal =>
      strictJointCylinderCompletedTwoStepTransfer_embed_form_gap
        hcoupling hle vector horthogonal⟩

#print axioms strictJointCylinderCompletedTwoStepAutocorrelation_embed_RC_le_rate
#print axioms strictJointCylinderCompletedTwoStepTransfer_embed_form_gap
#print axioms anchorDecoratedDoubledTimeRate_dense_vacuum_form_gap

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
