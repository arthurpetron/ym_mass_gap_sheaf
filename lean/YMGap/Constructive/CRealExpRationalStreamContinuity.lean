/-
# Rational-stream continuity for the constructive negative exponential

`CRealExp.convergesTo_expNegCD` is the completed-argument continuity theorem,
but it requires `ExpNegCData`: an antitone Type-level modulus and pointwise
`[0,1]` bounds for every completed exponent.  Exact physical logarithms need
not lie in `[0,1]`, and their natural inner modulus is not value-antitone.

This file proves the complementary theorem needed by the dynamic Wilson path.
For nonnegative *rational* exponent streams, convergence to one common
constructive real is enough to transfer convergence of their exponential
streams.  The proof is global in the exponent and local only in the exponent
difference:

* `expNeg_antitone_sub_le_zero` derives monotonicity from the exponential
  addition law, positivity, and `e^{-c} <= 1`;
* `expNeg_twoSided_contraction` combines monotonicity with the existing
  one-sided contraction whenever the two rational exponents are within one;
* `convergesTo_expNeg_of_common_rational_exponent_limit` uses a capped
  quarter-tolerance, so eventual common-limit closeness always places the two
  exponents inside that unit corridor.

No logarithm/exponential inverse is asserted.  The theorem only says that an
evaluation proved for one rational approximation stream can be transported to
any other nonnegative rational stream with the same `CReal` exponent limit.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Constructive.CRealExp

namespace YMGap.Constructive.CRealExpRationalStreamContinuity

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive

namespace CReal

private theorem q_le_of_not_le {p q : Q'} (h : ¬ (p <= q)) : q <= p := by
  show q.num * (p.den : Int) <= p.num * (q.den : Int)
  have h' : ¬ (p.num * (q.den : Int) <= q.num * (p.den : Int)) := h
  exact Int.le_of_lt (Int.not_le.mp h')

private theorem geRat_of_equiv_local {A B : CReal} {d : Q'}
    (h : CReal.Equiv A B) (hB : ExpPos.geRat B d) :
    ExpPos.geRat A d := by
  intro epsilon hepsilon
  have hhalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨NEquiv, hEquiv⟩ := h (HalfPow.half * epsilon) hhalf
  obtain ⟨NBound, hBound⟩ := hB (HalfPow.half * epsilon) hhalf
  refine ⟨max NEquiv NBound, fun n hn => ?_⟩
  have hnEquiv : NEquiv <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnBound : NBound <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  refine Q'.le_trans' _ _ _ (hBound n hnBound) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ (HalfPow.half * epsilon)
      (hEquiv n hnEquiv).2) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (A.approx n)
      (HalfPow.half * epsilon) (HalfPow.half * epsilon)) ?_)
  exact Q'.add_eqv_congr_left (A.approx n)
    (HalfPow.half * epsilon + HalfPow.half * epsilon) epsilon
    (ExpNeg.two_halves epsilon)

private theorem leRat_neg_of_geRat_local {B : CReal} {d : Q'}
    (h : ExpPos.geRat B d) : CReal.leRat (CReal.neg B) (-d) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  show -(B.approx n) <= -d + epsilon
  have hlower := hN n hn
  have hshift : -(B.approx n + epsilon) + epsilon <= -d + epsilon :=
    Q'.add_le_add_right _ _ epsilon (Q'.neg_le_neg hlower)
  have hcancel : (-(B.approx n + epsilon) + epsilon).eqv
      (-(B.approx n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ epsilon
        (Q'.neg_add_eqv (B.approx n) epsilon)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (-(B.approx n)) (-epsilon) epsilon) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-(B.approx n)) _ _
        (Q'.neg_add_self_eqv epsilon)) ?_
    rw [Q'.add_zero']
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hshift

private theorem sub_swap_neg_equiv (A B : CReal) :
    CReal.Equiv (CReal.sub B A) (CReal.neg (CReal.sub A B)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show (B.approx n + -(A.approx n)).eqv
      (-(A.approx n + -(B.approx n)))
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (A.approx n) (-(B.approx n))) ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-(A.approx n))
        (-(-(B.approx n))) (B.approx n)
        (Q'.neg_neg_eqv (B.approx n))) ?_
    exact Q'.add_comm_eqv (-(A.approx n)) (B.approx n))

/-- The missing monotonic half of the global contraction argument.
If `0 <= a <= b`, then `e^{-b} - e^{-a} <= 0` in the sound `leRat` sense.

The proof does not compare alternating partial sums termwise.  It factors
`e^{-a} - e^{-b}` as `e^{-a} * (1 - e^{-(b-a)})`; both factors are
nonnegative, so the negative of that difference has upper bound zero. -/
theorem expNeg_antitone_sub_le_zero {a b : Q'}
    (ha : (0 : Q') <= a) (hb : (0 : Q') <= b) (hab : a <= b) :
    CReal.leRat
      (CReal.sub (ExpNeg.expNeg b hb) (ExpNeg.expNeg a ha)) 0 := by
  have hdiff0 : (0 : Q') <= b - a := Q'.sub_nonneg_of_le hab
  have hsum : (a + (b - a)).eqv b := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (b + -a) (-a + b)
        (Q'.add_comm_eqv b (-a))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv a (-a) b)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ b (Q'.add_neg_self_eqv a)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 b) ?_
    exact QPoly.q_add_zero_eqv b
  have hExpB : CReal.Equiv (ExpNeg.expNeg b hb)
      (CReal.mul (ExpNeg.expNeg a ha)
        (ExpNeg.expNeg (b - a) hdiff0)) :=
    (CReal.Equiv.trans
      (expNeg_add_equiv a (b - a) ha hdiff0)
      (expNeg_eqv_congr
        (Q'.zero_le_add a (b - a) ha hdiff0) hb hsum)).symm
  have hFactor : CReal.Equiv
      (CReal.sub (ExpNeg.expNeg a ha) (ExpNeg.expNeg b hb))
      (CReal.mul (ExpNeg.expNeg a ha)
        (CReal.sub CReal.cone
          (ExpNeg.expNeg (b - a) hdiff0))) := by
    have hReplace : CReal.Equiv
        (CReal.sub (ExpNeg.expNeg a ha) (ExpNeg.expNeg b hb))
        (CReal.sub (ExpNeg.expNeg a ha)
          (CReal.mul (ExpNeg.expNeg a ha)
            (ExpNeg.expNeg (b - a) hdiff0))) :=
      CReal.sub_congr_right hExpB
    have hDistribute : CReal.Equiv
        (CReal.sub (ExpNeg.expNeg a ha)
          (CReal.mul (ExpNeg.expNeg a ha)
            (ExpNeg.expNeg (b - a) hdiff0)))
        (CReal.mul (ExpNeg.expNeg a ha)
          (CReal.sub CReal.cone
            (ExpNeg.expNeg (b - a) hdiff0))) :=
      (CReal.Equiv.trans
        (CReal.mul_sub (ExpNeg.expNeg a ha) CReal.cone
          (ExpNeg.expNeg (b - a) hdiff0))
        (CReal.sub_congr_left
          (CRealAlg.cmul_cone (ExpNeg.expNeg a ha)))).symm
    exact CReal.Equiv.trans hReplace hDistribute
  have hPositive : ExpPos.geRat
      (CReal.sub (ExpNeg.expNeg a ha) (ExpNeg.expNeg b hb)) 0 :=
    geRat_of_equiv_local hFactor
      (CReal.mul_nonneg
        (expNeg_geRat_zero a ha)
        (CReal.geRat_sub_cone_expNeg hdiff0))
  exact CReal.leRat_of_equiv (sub_swap_neg_equiv (ExpNeg.expNeg a ha)
      (ExpNeg.expNeg b hb))
    (leRat_neg_of_geRat_local hPositive)

/-- Two nonnegative rational exponents within `delta <= 1` have exponential
values within `delta`, in both `leRat` difference directions. -/
theorem expNeg_twoSided_contraction {a b delta : Q'}
    (ha : (0 : Q') <= a) (hb : (0 : Q') <= b)
    (hdelta0 : (0 : Q') <= delta) (hdelta1 : delta <= 1)
    (hab : a <= b + delta) (hba : b <= a + delta) :
    CReal.leRat
        (CReal.sub (ExpNeg.expNeg a ha) (ExpNeg.expNeg b hb)) delta ∧
      CReal.leRat
        (CReal.sub (ExpNeg.expNeg b hb) (ExpNeg.expNeg a ha)) delta := by
  by_cases horder : a <= b
  · have hdiff : b - a <= delta := Q'.sub_le_of_le_add hba
    have hdiff1 : b - a <= 1 := Q'.le_trans' _ _ _ hdiff hdelta1
    exact
      ⟨CReal.leRat_mono
        (CReal.expNeg_contraction ha horder hdiff1) hdiff,
       CReal.leRat_mono
        (expNeg_antitone_sub_le_zero ha hb horder) hdelta0⟩
  · have hreverse : b <= a := q_le_of_not_le horder
    have hdiff : a - b <= delta := Q'.sub_le_of_le_add hab
    have hdiff1 : a - b <= 1 := Q'.le_trans' _ _ _ hdiff hdelta1
    exact
      ⟨CReal.leRat_mono
        (expNeg_antitone_sub_le_zero hb ha hreverse) hdelta0,
       CReal.leRat_mono
        (CReal.expNeg_contraction hb hreverse hdiff1) hdiff⟩

/-- **Rational-stream continuity of `expNeg`, in transport form.**

If two nonnegative rational exponent streams converge (after `ofQ'`) to the
same constructive real `W`, then convergence of the exponential of the second
stream to `L` transfers to the exponential of the first stream.  No boundedness
of `W`, no `ExpNegCData`, and no log/exp inverse theorem is required. -/
theorem convergesTo_expNeg_of_common_rational_exponent_limit
    {a b : Nat -> Q'} {W L : CReal}
    (ha0 : forall stage, (0 : Q') <= a stage)
    (hb0 : forall stage, (0 : Q') <= b stage)
    (ha : CReal.ConvergesTo (fun stage => CReal.ofQ' (a stage)) W)
    (hb : CReal.ConvergesTo (fun stage => CReal.ofQ' (b stage)) W)
    (hbExp : CReal.ConvergesTo
      (fun stage => ExpNeg.expNeg (b stage) (hb0 stage)) L) :
    CReal.ConvergesTo
      (fun stage => ExpNeg.expNeg (a stage) (ha0 stage)) L := by
  intro epsilon hepsilon
  have core : forall rho : Q', (0 : Q') < rho -> rho <= epsilon -> rho <= 1 ->
      exists Nstage : Nat, forall stage : Nat, Nstage <= stage ->
        exists Napx : Nat, forall n : Nat, Napx <= n ->
          (ExpNeg.expNeg (a stage) (ha0 stage)).approx n <=
              L.approx n + epsilon /\
            L.approx n <=
              (ExpNeg.expNeg (a stage) (ha0 stage)).approx n + epsilon := by
    intro rho hrho hrhoEpsilon hrhoOne
    let q : Q' := HalfPow.half * (HalfPow.half * rho)
    let delta : Q' := q + q
    have hq : (0 : Q') < q :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos rho hrho)
    have hdelta0 : (0 : Q') <= delta :=
      Q'.zero_le_add q q (Q'.le_of_lt hq) (Q'.le_of_lt hq)
    have hqq : delta.eqv (HalfPow.half * rho) :=
      ExpNeg.two_halves (HalfPow.half * rho)
    have hhalfRho : (0 : Q') <= HalfPow.half * rho :=
      Q'.le_of_lt (ExpNeg.half_mul_pos rho hrho)
    have hhalfRhoLe : HalfPow.half * rho <= rho :=
      Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg
          (HalfPow.half * rho) (HalfPow.half * rho) hhalfRho)
        (Q'.le_of_eqv (ExpNeg.two_halves rho))
    have hdelta1 : delta <= 1 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hqq)
        (Q'.le_trans' _ _ _ hhalfRhoLe hrhoOne)
    have hbudget : (q + (delta + q)).eqv rho := by
      have hregroup : (q + ((q + q) + q)).eqv
          ((q + q) + (q + q)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left q ((q + q) + q) (q + (q + q))
            (Q'.add_assoc_eqv q q q)) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv q q (q + q))
      refine Q'.eqv_trans _ _ _ hregroup ?_
      refine Q'.eqv_trans _ _ _
        (ExpNeg.add_eqv_congr2 hqq hqq) ?_
      exact ExpNeg.two_halves rho
    obtain ⟨NA, hA⟩ := ha q hq
    obtain ⟨NB, hB⟩ := hb q hq
    obtain ⟨NE, hE⟩ := hbExp q hq
    refine ⟨max (max NA NB) NE, fun stage hstage => ?_⟩
    have hstageA : NA <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hstage
    have hstageB : NB <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hstage
    have hstageE : NE <= stage :=
      Nat.le_trans (Nat.le_max_right _ _) hstage
    obtain ⟨PA, hPA⟩ := hA stage hstageA
    obtain ⟨PB, hPB⟩ := hB stage hstageB
    obtain ⟨PE, hPE⟩ := hE stage hstageE
    let inputIndex : Nat := max PA PB
    have hinputA : PA <= inputIndex := Nat.le_max_left _ _
    have hinputB : PB <= inputIndex := Nat.le_max_right _ _
    obtain ⟨haForward, haBackward⟩ := hPA inputIndex hinputA
    obtain ⟨hbForward, hbBackward⟩ := hPB inputIndex hinputB
    have hab : a stage <= b stage + delta := by
      have hchain : a stage <= (b stage + q) + q :=
        Q'.le_trans' _ _ _ haForward
          (Q'.add_le_add_right _ _ q hbBackward)
      refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (b stage) q q)
        (Q'.add_eqv_congr_left (b stage) (q + q) delta
          (Q'.eqv_refl delta))
    have hba : b stage <= a stage + delta := by
      have hchain : b stage <= (a stage + q) + q :=
        Q'.le_trans' _ _ _ hbForward
          (Q'.add_le_add_right _ _ q haBackward)
      refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (a stage) q q)
        (Q'.add_eqv_congr_left (a stage) (q + q) delta
          (Q'.eqv_refl delta))
    obtain ⟨hExpAB, hExpBA⟩ :=
      expNeg_twoSided_contraction
        (ha0 stage) (hb0 stage) hdelta0 hdelta1 hab hba
    obtain ⟨PAB, hPAB⟩ := hExpAB q hq
    obtain ⟨PBA, hPBA⟩ := hExpBA q hq
    refine ⟨max (max PAB PBA) PE, fun n hn => ?_⟩
    have hnAB : PAB <= n :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
    have hnBA : PBA <= n :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
    have hnE : PE <= n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hAB : (ExpNeg.expNeg (a stage) (ha0 stage)).approx n <=
        (ExpNeg.expNeg (b stage) (hb0 stage)).approx n + (delta + q) :=
      CReal.le_add_of_sub_le (hPAB n hnAB)
    have hBA : (ExpNeg.expNeg (b stage) (hb0 stage)).approx n <=
        (ExpNeg.expNeg (a stage) (ha0 stage)).approx n + (delta + q) :=
      CReal.le_add_of_sub_le (hPBA n hnBA)
    obtain ⟨hEL, hLE⟩ := hPE n hnE
    have closeBudget : forall x y z : Q',
        x <= y + (delta + q) -> y <= z + q -> x <= z + epsilon := by
      intro x y z hxy hyz
      have hchain : x <= (z + q) + (delta + q) :=
        Q'.le_trans' _ _ _ hxy
          (Q'.add_le_add_right _ _ (delta + q) hyz)
      refine Q'.le_trans' _ _ _ hchain ?_
      have hreassociate : ((z + q) + (delta + q)).eqv
          (z + (q + (delta + q))) :=
        Q'.add_assoc_eqv z q (delta + q)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassociate) ?_
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_left z (q + (delta + q)) rho hbudget)) ?_
      exact Q'.add_le_add_left z rho epsilon hrhoEpsilon
    have closeBudgetReverse : forall x y z : Q',
        x <= y + q -> y <= z + (delta + q) -> x <= z + epsilon := by
      intro x y z hxy hyz
      have hchain : x <= (z + (delta + q)) + q :=
        Q'.le_trans' _ _ _ hxy
          (Q'.add_le_add_right _ _ q hyz)
      refine Q'.le_trans' _ _ _ hchain ?_
      have hreassociate : ((z + (delta + q)) + q).eqv
          (z + ((delta + q) + q)) :=
        Q'.add_assoc_eqv z (delta + q) q
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassociate) ?_
      have hreverseBudget : ((delta + q) + q).eqv rho :=
        Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (delta + q) q) hbudget
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_left z ((delta + q) + q) rho
            hreverseBudget)) ?_
      exact Q'.add_le_add_left z rho epsilon hrhoEpsilon
    exact
      ⟨closeBudget _ _ _ hAB hEL,
       closeBudgetReverse _ _ _ hLE hBA⟩
  by_cases hepsilonOne : epsilon <= (1 : Q')
  · exact core epsilon hepsilon (Q'.le_refl' epsilon) hepsilonOne
  · exact core 1 (by decide) (q_le_of_not_le hepsilonOne)
      (Q'.le_refl' 1)

end CReal

end YMGap.Constructive.CRealExpRationalStreamContinuity

#print axioms YMGap.Constructive.CRealExpRationalStreamContinuity.CReal.expNeg_antitone_sub_le_zero
#print axioms YMGap.Constructive.CRealExpRationalStreamContinuity.CReal.expNeg_twoSided_contraction
#print axioms YMGap.Constructive.CRealExpRationalStreamContinuity.CReal.convergesTo_expNeg_of_common_rational_exponent_limit
