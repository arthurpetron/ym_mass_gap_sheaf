/-
# Binary-Gram factorization of ordered right-associated channels

The invariant Gram of a nested right SU(2) transvectant is the product of
the two binary transvectant Grams divided by the intermediate representation
dimension.  Everything is stated denominator-free over `Q'`:

`(f+1) * triRightChannelWeight = innerGram * outerGram`.

The proof expands one nested coefficient through the physical intermediate
monomial window, uses the exact one-shell support theorem, factors every
normalized output row, and only then sums the rows.  Thus the dimension
factor is derived from the checked coefficient model rather than inserted as
a normalization convention.
-/

import YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
import YMGap.Continuum.SU2TransvectantClosedBinaryGram

namespace YMGap.Continuum.SU2OrderedRightNestedGramFactorization

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantRowNormConstancy
open YMGap.Continuum.SU2TransvectantNormalizedRows
open YMGap.Continuum.SU2TransvectantClosedBinaryGram
open YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

def nestedConvolution {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat) : Q' :=
  finSum (fun t =>
    let H := transvect b c q.p (tprod (mono j) (mono l)) t
    let O := transvect a q.intermediate q.r
      (tprod (mono i) (mono t)) s
    (H * O) * (H * O)) (q.intermediate + 1)

theorem nestedConvolution_eq_triRight_sq {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (i j l s : Nat) (hj : j ≤ b) (hl : l ≤ c) :
    nestedConvolution q i j l s ≈
      triRight a b c d q.intermediate (mono i) (mono j) (mono l) s *
        triRight a b c d q.intermediate (mono i) (mono j) (mono l) s := by
  by_cases hbelow : j + l < q.p
  · have hzero := triRight_monomial_zero_below_inner_order q i j l s hbelow
    refine Q'.eqv_trans _ 0 _ ?_ ?_
    · unfold nestedConvolution
      apply finSum_zero_on
      intro t ht
      have hH := transvect_monomial_zero_offshell b c q.p j l t (by omega)
      let OT := transvect a q.intermediate q.r
        (tprod (mono i) (mono t)) s
      dsimp only
      refine Q'.eqv_trans _ ((0 * OT) * (0 * OT)) _ ?_ ?_
      · exact mul_eqv_congr
          (Q'.mul_eqv_congr_right _ _ _ hH)
          (Q'.mul_eqv_congr_right _ _ _ hH)
      · exact Q'.eqv_trans _ (0 * 0) _
          (mul_eqv_congr (Q'.zero_mul_eqv OT) (Q'.zero_mul_eqv OT))
          (Q'.zero_mul_eqv 0)
    · exact Q'.eqv_symm (Q'.eqv_trans _ (0 * 0) _
        (mul_eqv_congr hzero hzero) (Q'.zero_mul_eqv 0))
  · have hp : q.p ≤ j + l := by omega
    let t0 := j + l - q.p
    let H := hahnEntry b c (j + l) q.p j
    let O := transvect a q.intermediate q.r
      (tprod (mono i) (mono t0)) s
    by_cases htphys : t0 ≤ q.intermediate
    case neg =>
      have hsumZero : nestedConvolution q i j l s ≈ 0 := by
        unfold nestedConvolution
        apply finSum_zero_on
        intro t ht
        have hne : ¬ t + q.p = j + l := by
          intro heq
          have : t = t0 := by unfold t0; omega
          omega
        have hH := transvect_monomial_zero_offshell b c q.p j l t hne
        let OT := transvect a q.intermediate q.r
          (tprod (mono i) (mono t)) s
        dsimp only
        refine Q'.eqv_trans _ ((0 * OT) * (0 * OT)) _ ?_ ?_
        · exact mul_eqv_congr
            (Q'.mul_eqv_congr_right _ _ _ hH)
            (Q'.mul_eqv_congr_right _ _ _ hH)
        · exact Q'.eqv_trans _ (0 * 0) _
            (mul_eqv_congr (Q'.zero_mul_eqv OT) (Q'.zero_mul_eqv OT))
            (Q'.zero_mul_eqv 0)
      have hinnerZero : BFormEqv
          (transvect b c q.p (tprod (mono j) (mono l))) zeroF := by
        intro t
        by_cases htf : t ≤ q.intermediate
        · exact transvect_monomial_zero_offshell b c q.p j l t (by
            intro heq
            have : t = t0 := by unfold t0; omega
            omega)
        · have hpq := Nat.le_min.mp q.p_le
          have hz := YMGap.Continuum.SU2ProjectedRawSupportedBridge.transvect_zero_above_degree
            b c q.p (tprod (mono j) (mono l)) hpq.1 hpq.2
            (YMGap.Continuum.SU2TransvectantBinaryGramInvariant.tprod_mono_supported
              b c j l hj hl) t (by
                change b + c - 2 * q.p < t
                change ¬ t ≤ b + c - 2 * q.p at htf
                omega)
          simpa only [zeroF] using hz
      have htensorZero : BForm2Eqv
          (tprod (mono i) (transvect b c q.p (tprod (mono j) (mono l))))
          zeroForm2 := by
        intro x y
        unfold tprod zeroForm2
        exact Q'.eqv_trans _ (mono i x * 0) _
          (Q'.mul_eqv_congr_left _ _ _ (hinnerZero y))
          (Q'.mul_zero_eqv _)
      have houterZero := transvect_congr a q.intermediate q.r
        htensorZero s
      have hzeroForm := transvect_zeroForm2 a q.intermediate q.r s
      have htriZero : triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s ≈ 0 := by
        unfold triRight
        rw [fixedRight_inner_couplingOrder q,
          fixedRight_outer_couplingOrder q]
        exact Q'.eqv_trans _ _ _ houterZero hzeroForm
      exact Q'.eqv_trans _ 0 _ hsumZero
        (Q'.eqv_symm (Q'.eqv_trans _ (0 * 0) _
          (mul_eqv_congr htriZero htriZero) (Q'.zero_mul_eqv 0)))
    case pos =>
    have ht0 : t0 < q.intermediate + 1 := by omega
    have hterms : ∀ t, t < q.intermediate + 1 →
        (let IH := transvect b c q.p (tprod (mono j) (mono l)) t
         let OT := transvect a q.intermediate q.r
            (tprod (mono i) (mono t)) s
         (IH * OT) * (IH * OT)) ≈
          if t = t0 then (H * O) * (H * O) else 0 := by
      intro t ht
      by_cases htt : t = t0
      · subst t
        rw [if_pos rfl]
        have hinner := transvect_monomial_factorial_formula
          b c q.p j l t0
        have hshell : t0 + q.p = j + l := by unfold t0; omega
        have hH : transvect b c q.p (tprod (mono j) (mono l)) t0 ≈ H := by
          simpa only [H, hahnEntry, if_pos hshell,
            show j + l - j = l by omega] using hinner
        dsimp only
        exact mul_eqv_congr
          (Q'.mul_eqv_congr_right _ _ _ hH)
          (Q'.mul_eqv_congr_right _ _ _ hH)
      · rw [if_neg htt]
        have hshell : ¬ t + q.p = j + l := by
          intro heq
          have : t = t0 := by unfold t0; omega
          exact htt this
        have hH := transvect_monomial_zero_offshell b c q.p j l t hshell
        let OT := transvect a q.intermediate q.r
          (tprod (mono i) (mono t)) s
        dsimp only
        refine Q'.eqv_trans _ ((0 * OT) * (0 * OT)) _ ?_ ?_
        · exact mul_eqv_congr
            (Q'.mul_eqv_congr_right _ _ _ hH)
            (Q'.mul_eqv_congr_right _ _ _ hH)
        · exact Q'.eqv_trans _ (0 * 0) _
            (mul_eqv_congr (Q'.zero_mul_eqv OT) (Q'.zero_mul_eqv OT))
            (Q'.zero_mul_eqv 0)
    have hsum : nestedConvolution q i j l s ≈ (H * O) * (H * O) := by
      refine Q'.eqv_trans _
        (finSum (fun t => if t = t0 then (H * O) * (H * O) else 0)
          (q.intermediate + 1)) _ ?_ ?_
      · unfold nestedConvolution
        exact finSum_eqv_congr_lt _ _ _ hterms
      · exact finSum_onehot_value ((H * O) * (H * O))
          (q.intermediate + 1) t0 ht0
    have htri := triRight_monomial_factorization
      a b c d q.intermediate i j l s (by
        rw [fixedRight_inner_couplingOrder q]
        exact hp)
    have horders : couplingOrder b c q.intermediate = q.p :=
      fixedRight_inner_couplingOrder q
    have houter : couplingOrder a q.intermediate d = q.r :=
      fixedRight_outer_couplingOrder q
    rw [horders, houter] at htri
    have ht : j + l - q.p = t0 := rfl
    rw [ht] at htri
    change nestedConvolution q i j l s ≈ _
    exact Q'.eqv_trans _ _ _ hsum
      (Q'.eqv_symm (mul_eqv_congr htri htri))

def triRightNormalizedRowNorm {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun l =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s *
        (triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s *
          triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s))
    (c + 1)) (b + 1)) (a + 1)

def triRightConvolutionRowNorm {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun l =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s * nestedConvolution q i j l s)
    (c + 1)) (b + 1)) (a + 1)

theorem triRightNormalizedRowNorm_eq_convolution {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) :
    triRightNormalizedRowNorm q s ≈ triRightConvolutionRowNorm q s := by
  unfold triRightNormalizedRowNorm triRightConvolutionRowNorm
  refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
  refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
  exact Q'.mul_eqv_congr_left
    (tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s) _ _
    (Q'.eqv_symm (nestedConvolution_eq_triRight_sq q i j l s
      (by omega) (by omega)))

theorem triRightConvolutionRowNorm_factor {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) :
    triRightConvolutionRowNorm q s ≈
      binaryRowFactorialProduct b c q.p *
        binaryNormalizedRowNorm a q.intermediate q.r s := by
  let P := binaryRowFactorialProduct b c q.p
  let W := symMonomialNormSq d s
  let H : Nat → Nat → Nat → Q' := fun j l t =>
    transvect b c q.p (tprod (mono j) (mono l)) t
  let O : Nat → Nat → Q' := fun i t =>
    transvect a q.intermediate q.r (tprod (mono i) (mono t)) s
  let A : Nat → Nat → Nat → Nat → Q' := fun i j l t =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c l * W *
      ((H j l t * O i t) * (H j l t * O i t))
  have hexpand : triRightConvolutionRowNorm q s ≈
      finSum (fun i => finSum (fun j => finSum (fun l =>
        finSum (fun t => A i j l t) (q.intermediate + 1))
        (c + 1)) (b + 1)) (a + 1) := by
    unfold triRightConvolutionRowNorm nestedConvolution
    refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
    refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
    refine Q'.eqv_trans _
      (finSum (fun t =>
        (tvBinomQ a i * tvBinomQ b j * tvBinomQ c l * W) *
          ((H j l t * O i t) * (H j l t * O i t)))
        (q.intermediate + 1)) _ ?_ ?_
    · exact const_mul_finSum _ _ _
    · exact finSum_eqv_congr_lt _ _ _ (fun t ht => by
        unfold A
        exact Q'.eqv_refl _)
  have hswapL : ∀ i j,
      finSum (fun l => finSum (fun t => A i j l t)
          (q.intermediate + 1)) (c + 1) ≈
        finSum (fun t => finSum (fun l => A i j l t) (c + 1))
          (q.intermediate + 1) := by
    intro i j
    exact finSum_swap (fun l t => A i j l t) (c + 1)
      (q.intermediate + 1)
  have hswapJ : ∀ i,
      finSum (fun j => finSum (fun t => finSum (fun l => A i j l t)
          (c + 1)) (q.intermediate + 1)) (b + 1) ≈
        finSum (fun t => finSum (fun j => finSum (fun l => A i j l t)
          (c + 1)) (b + 1)) (q.intermediate + 1) := by
    intro i
    exact finSum_swap
      (fun j t => finSum (fun l => A i j l t) (c + 1))
      (b + 1) (q.intermediate + 1)
  have hreorder :
      finSum (fun i => finSum (fun j => finSum (fun l =>
        finSum (fun t => A i j l t) (q.intermediate + 1))
        (c + 1)) (b + 1)) (a + 1) ≈
      finSum (fun i => finSum (fun t => finSum (fun j =>
        finSum (fun l => A i j l t) (c + 1)) (b + 1))
        (q.intermediate + 1)) (a + 1) := by
    refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    refine Q'.eqv_trans _
      (finSum (fun j => finSum (fun t => finSum (fun l => A i j l t)
        (c + 1)) (q.intermediate + 1)) (b + 1)) _ ?_ (hswapJ i)
    exact finSum_eqv_congr_lt _ _ (b + 1)
      (fun j hj => hswapL i j)
  have hinner : ∀ i t, t < q.intermediate + 1 →
      finSum (fun j => finSum (fun l => A i j l t) (c + 1)) (b + 1) ≈
        P * (W * (tvBinomQ q.intermediate t *
          (tvBinomQ a i * (O i t * O i t)))) := by
    intro i t ht
    let K := tvBinomQ a i * W * (O i t * O i t)
    have hfactor :
        finSum (fun j => finSum (fun l => A i j l t) (c + 1)) (b + 1) ≈
          K * binaryRawRowNorm b c q.p t := by
      refine Q'.eqv_trans _
        (finSum (fun j => K * finSum (fun l =>
          tvBinomQ c l * (tvBinomQ b j * (H j l t * H j l t)))
          (c + 1)) (b + 1)) _ ?_ ?_
      · refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
        refine Q'.eqv_trans _
          (finSum (fun l => K *
            (tvBinomQ c l * (tvBinomQ b j * (H j l t * H j l t))))
            (c + 1)) _ ?_ ?_
        · exact finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => by
            unfold A K
            ring_qeqv)
        · exact Q'.eqv_symm (const_mul_finSum _ K (c + 1))
      · refine Q'.eqv_trans _
          (K * finSum (fun j => finSum (fun l =>
            tvBinomQ c l * (tvBinomQ b j * (H j l t * H j l t)))
            (c + 1)) (b + 1)) _
          (Q'.eqv_symm (const_mul_finSum _ K (b + 1))) ?_
        unfold binaryRawRowNorm tensorBinomPair H
        exact Q'.eqv_refl _
    have hpq := Nat.le_min.mp q.p_le
    have hraw := binaryRawRowNorm_factorial_product b c q.p t
      hpq.1 hpq.2 (by
        change t ≤ b + c - 2 * q.p
        change t < b + c - 2 * q.p + 1 at ht
        omega)
    refine Q'.eqv_trans _ (K * (tvBinomQ q.intermediate t * P)) _
      (Q'.eqv_trans _ _ _ hfactor
        (Q'.mul_eqv_congr_left K _ _ (by
          simpa only [FixedRightCGChannel.intermediate, P] using hraw))) ?_
    unfold K
    ring_qeqv
  refine Q'.eqv_trans _ _ _ hexpand ?_
  refine Q'.eqv_trans _ _ _ hreorder ?_
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun t =>
      P * (W * (tvBinomQ q.intermediate t *
        (tvBinomQ a i * (O i t * O i t)))))
      (q.intermediate + 1)) (a + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    exact finSum_eqv_congr_lt _ _ (q.intermediate + 1)
      (fun t ht => hinner i t ht)
  · refine Q'.eqv_trans _
      (finSum (fun i => P * finSum (fun t =>
        W * (tvBinomQ q.intermediate t *
          (tvBinomQ a i * (O i t * O i t))))
        (q.intermediate + 1)) (a + 1)) _ ?_ ?_
    · refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
      exact Q'.eqv_symm (const_mul_finSum _ P (q.intermediate + 1))
    refine Q'.eqv_trans _
      (P * finSum (fun i => finSum (fun t =>
        W * (tvBinomQ q.intermediate t *
          (tvBinomQ a i * (O i t * O i t))))
        (q.intermediate + 1)) (a + 1)) _ ?_ ?_
    · exact Q'.eqv_symm (const_mul_finSum _ P (a + 1))
    · apply Q'.mul_eqv_congr_left P
      refine Q'.eqv_trans _
        (finSum (fun i => W * finSum (fun t =>
          tvBinomQ q.intermediate t *
            (tvBinomQ a i * (O i t * O i t)))
          (q.intermediate + 1)) (a + 1)) _ ?_ ?_
      · refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
        exact Q'.eqv_symm (const_mul_finSum _ W (q.intermediate + 1))
      refine Q'.eqv_trans _
        (W * finSum (fun i => finSum (fun t =>
          tvBinomQ q.intermediate t *
            (tvBinomQ a i * (O i t * O i t)))
          (q.intermediate + 1)) (a + 1)) _ ?_ ?_
      · exact Q'.eqv_symm (const_mul_finSum _ W (a + 1))
      · unfold binaryNormalizedRowNorm binaryRawRowNorm tensorBinomPair O W
        rw [show a + q.intermediate - 2 * q.r = d by
          exact q.degree_eq]
        exact Q'.eqv_refl _

theorem triRightNormalizedRowNorm_factor {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) :
    triRightNormalizedRowNorm q s ≈
      binaryRowFactorialProduct b c q.p *
        binaryNormalizedRowNorm a q.intermediate q.r s := by
  exact Q'.eqv_trans _ _ _
    (triRightNormalizedRowNorm_eq_convolution q s)
    (triRightConvolutionRowNorm_factor q s)

theorem triRightChannelWeight_eq_rowSum {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    triRightChannelWeight a b c d q.intermediate ≈
      finSum (fun s => triRightNormalizedRowNorm q s) (d + 1) := by
  let A : Nat → Nat → Nat → Nat → Q' := fun i j l s =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s *
        (triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s *
          triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s)
  change finSum (fun i => finSum (fun j => finSum (fun l =>
    finSum (fun s => A i j l s) (d + 1)) (c + 1)) (b + 1)) (a + 1) ≈ _
  have hswapL : ∀ i j,
      finSum (fun l => finSum (fun s => A i j l s) (d + 1)) (c + 1) ≈
        finSum (fun s => finSum (fun l => A i j l s) (c + 1)) (d + 1) := by
    intro i j
    exact finSum_swap (fun l s => A i j l s) (c + 1) (d + 1)
  have hswapJ : ∀ i,
      finSum (fun j => finSum (fun s => finSum (fun l => A i j l s)
        (c + 1)) (d + 1)) (b + 1) ≈
        finSum (fun s => finSum (fun j => finSum (fun l => A i j l s)
          (c + 1)) (b + 1)) (d + 1) := by
    intro i
    exact finSum_swap
      (fun j s => finSum (fun l => A i j l s) (c + 1))
      (b + 1) (d + 1)
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun j => finSum (fun s =>
      finSum (fun l => A i j l s) (c + 1)) (d + 1))
      (b + 1)) (a + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    exact finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => hswapL i j)
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun s => finSum (fun j =>
      finSum (fun l => A i j l s) (c + 1)) (b + 1))
      (d + 1)) (a + 1)) _ ?_ ?_
  · exact finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => hswapJ i)
  refine Q'.eqv_trans _
    (finSum (fun s => finSum (fun i => finSum (fun j =>
      finSum (fun l => A i j l s) (c + 1)) (b + 1))
      (a + 1)) (d + 1)) _ ?_ ?_
  · exact finSum_swap
      (fun i s => finSum (fun j => finSum (fun l => A i j l s)
        (c + 1)) (b + 1)) (a + 1) (d + 1)
  · exact finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => by
      unfold triRightNormalizedRowNorm A
      exact Q'.eqv_refl _)

theorem triRightChannelWeight_binary_factor {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    triRightChannelWeight a b c d q.intermediate ≈
      binaryRowFactorialProduct b c q.p *
        binaryTransvectantGram a q.intermediate q.r := by
  refine Q'.eqv_trans _
    (finSum (fun s => triRightNormalizedRowNorm q s) (d + 1)) _
    (triRightChannelWeight_eq_rowSum q) ?_
  refine Q'.eqv_trans _
    (finSum (fun s => binaryRowFactorialProduct b c q.p *
      binaryNormalizedRowNorm a q.intermediate q.r s) (d + 1)) _ ?_ ?_
  · exact finSum_eqv_congr_lt _ _ (d + 1) (fun s hs =>
      triRightNormalizedRowNorm_factor q s)
  refine Q'.eqv_trans _
    (binaryRowFactorialProduct b c q.p *
      finSum (fun s => binaryNormalizedRowNorm a q.intermediate q.r s)
        (d + 1)) _
    (Q'.eqv_symm (const_mul_finSum _ _ _)) ?_
  unfold binaryTransvectantGram
  rw [show a + q.intermediate - 2 * q.r = d by exact q.degree_eq]
  exact Q'.eqv_refl _

/-- The concrete nested right-channel weight is the product of its two
binary transvectant Grams divided, in denominator-free form, by the
intermediate representation dimension. -/
theorem triRightChannelWeight_nested_binary_gram {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    Q'.ofNat (q.intermediate + 1) *
        triRightChannelWeight a b c d q.intermediate ≈
      binaryTransvectantGram b c q.p *
        binaryTransvectantGram a q.intermediate q.r := by
  have hp := Nat.le_min.mp q.p_le
  have hinner := binaryTransvectantGram_factorial_product
    b c q.p hp.1 hp.2
  refine Q'.eqv_trans _
    (Q'.ofNat (q.intermediate + 1) *
      (binaryRowFactorialProduct b c q.p *
        binaryTransvectantGram a q.intermediate q.r)) _
    (Q'.mul_eqv_congr_left _ _ _ (triRightChannelWeight_binary_factor q)) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (q.intermediate + 1) *
      binaryRowFactorialProduct b c q.p) *
        binaryTransvectantGram a q.intermediate q.r) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (by
    simpa only [FixedRightCGChannel.intermediate] using Q'.eqv_symm hinner)

end YMGap.Continuum.SU2OrderedRightNestedGramFactorization

#print axioms YMGap.Continuum.SU2OrderedRightNestedGramFactorization.nestedConvolution_eq_triRight_sq
#print axioms YMGap.Continuum.SU2OrderedRightNestedGramFactorization.triRightNormalizedRowNorm_factor
#print axioms YMGap.Continuum.SU2OrderedRightNestedGramFactorization.triRightChannelWeight_nested_binary_gram
