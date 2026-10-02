/-
# Strict margins for ORIGINAL inclusive heat prefixes

The original completed chord-quartic profile and the original spacing tails
give a rational inequality at one COMMON inclusive label cutoff K.  Both
tail offsets are K+1-spacingLabelCutoff, not K-spacingLabelCutoff.

The resulting polynomial is built from the actual heatPrefix, evaluated at
the same environment.  Its explicit positive margin is pointwise on the
closed class interval, including both endpoints.  No Haar Certificate is
inferred from pointwise positivity.  Certificate compilation, interacting
variance alignment and continuum survival are separate open obligations.
-/

import YMGap.Continuum.SU2HeatJacobiCompletedProfileBound
import YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
import YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor
import YMGap.Continuum.QuaternionHaarHeatCertificate

namespace YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.SU2HeatJacobiCompletedProfileBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor (eval_finitePolySum_range)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] pointwiseHeatCReal

private theorem mul_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c hab)
    (Q'.mul_eqv_congr_left b _ _ hcd)

/-- Tail after the actual inclusive label cutoff K. -/
def inclusivePrefixTail (q : Q') (K : Nat) : Q' :=
  spacingClosedTail q (K+1-spacingLabelCutoff q)

/-- The coefficient of the actual completed chord-quartic comparison. -/
def quarticProfileCoefficient (q : Q') : Q' :=
  40*(((24576 : Q')*24576)*((1-q)*(1-q)))

/-- Both original tails at the SAME inclusive K; the factor 16 bounds
the squared chord on the whole closed interval. -/
def quarticPrefixError (q : Q') (K : Nat) : Q' :=
  16*inclusivePrefixTail q K +
    quarticProfileCoefficient q*inclusivePrefixTail (q*q) K

/-- The K+1 offset is exact, not an asymptotic reindexing. -/
theorem inclusivePrefix_pin (q x : Q') (K : Nat)
    (hK : spacingLabelCutoff q ≤ K+1) :
    spacingPointwiseHeatPartial q x (K+1-spacingLabelCutoff q) =
      standardPointwiseHeatPartial q x (K+1) := by
  unfold spacingPointwiseHeatPartial
  rw [Nat.add_sub_of_le hK]

/-- Every later approximation lies in the actual inclusive-prefix corridor.
The approximation index can be shared with a different nome. -/
theorem inclusivePrefix_corridor {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (K n : Nat) (hK : spacingLabelCutoff q ≤ K+1)
    (hn : K+1-spacingLabelCutoff q ≤ n) :
    standardPointwiseHeatPartial q x (K+1) ≤
        spacingPointwiseHeatPartial q x n + inclusivePrefixTail q K ∧
      spacingPointwiseHeatPartial q x n ≤
        standardPointwiseHeatPartial q x (K+1) + inclusivePrefixTail q K := by
  obtain ⟨L,hL⟩ := Nat.exists_eq_add_of_le hn
  rw [hL]
  have hl := spacingPointwiseHeatPartial_block_lower hq0 hq1 hxlo hxhi
    (K+1-spacingLabelCutoff q) L
  have hu := spacingPointwiseHeatPartial_block_upper hq0 hq1 hxlo hxhi
    (K+1-spacingLabelCutoff q) L
  rw [inclusivePrefix_pin q x K hK] at hl hu
  exact ⟨hl,hu⟩

private theorem coefficient_nonnegative {q : Q'} (hq1 : q < (1 : Q')) :
    (0 : Q') ≤ quarticProfileCoefficient q := by
  have hg := Q'.sub_nonneg_of_le (Q'.le_of_lt hq1)
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hg hg))

private theorem chord_square_bounds {x : Q'}
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    (0 : Q') ≤ (2*(1-x))*(2*(1-x)) ∧
      (2*(1-x))*(2*(1-x)) ≤ (16 : Q') := by
  have hz0 := Q'.sub_nonneg_of_le hxhi
  have hz2 : 1-x ≤ (2 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hxlo))
      (Q'.le_of_eqv (by decide : (1 : Q') + -(-1) ≈ 2))
  have hr0 : (0 : Q') ≤ 2*(1-x) := Q'.mul_nonneg _ _ (by decide) hz0
  have hr4 : 2*(1-x) ≤ (4 : Q') :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 hz2 (by decide))
      (Q'.le_of_eqv (by decide : (2 : Q')*2 ≈ 4))
  exact ⟨Q'.mul_nonneg _ _ hr0 hr0,
    Q'.le_trans' _ _ _ (HKConv.mul_le_mul' hr0 (by decide) hr4 hr4)
      (Q'.le_of_eqv (by decide : (4 : Q')*4 ≈ 16))⟩

/-- The original rational chord-quartic bound, at a common inclusive K.
No independent cutoffs or replacement heat coefficients are used. -/
theorem inclusivePrefix_chord_quartic_bound {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (K : Nat) (hKq : spacingLabelCutoff q ≤ K+1)
    (hKqq : spacingLabelCutoff (q*q) ≤ K+1) :
    ((2*(1-x))*(2*(1-x)))*standardPointwiseHeatPartial q x (K+1) ≤
      quarticProfileCoefficient q*standardPointwiseHeatPartial (q*q) x (K+1) +
        quarticPrefixError q K := by
  let r := (2*(1-x))*(2*(1-x))
  let c := quarticProfileCoefficient q
  let P := standardPointwiseHeatPartial q x (K+1)
  let P2 := standardPointwiseHeatPartial (q*q) x (K+1)
  let T := inclusivePrefixTail q K
  let T2 := inclusivePrefixTail (q*q) K
  have hqq0 := HKPos.q_mul_pos hq0 hq0
  have hqq1 := FiniteJacobiCoefficients.square_base_lt_one hq0 hq1
  have hr := chord_square_bounds hxlo hxhi
  have hc : (0 : Q') ≤ c := coefficient_nonnegative hq1
  have hT : (0 : Q') ≤ T := spacingClosedTail_nonnegative hq0 _
  have hprofile := pointwiseHeat_chord_quartic_bound hq0 hq1 hq hxlo hxhi
  apply Q'.le_of_forall_pos_add
  intro epsilon hepsilon
  obtain ⟨base,hbase⟩ := hprofile epsilon hepsilon
  let n := max base (max (K+1-spacingLabelCutoff q) (K+1-spacingLabelCutoff (q*q)))
  have hnbase : base ≤ n := Nat.le_max_left _ _
  have hnq : K+1-spacingLabelCutoff q ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hnqq : K+1-spacingLabelCutoff (q*q) ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hp := hbase n hnbase
  change r*(pointwiseHeatCReal hq0 hq1 hxlo hxhi).approx n ≤
    c*(pointwiseHeatCReal hqq0 hqq1 hxlo hxhi).approx n + epsilon at hp
  rw [pointwiseHeatCReal_approx,pointwiseHeatCReal_approx] at hp
  have hl := (inclusivePrefix_corridor hq0 hq1 hxlo hxhi K n hKq hnq).1
  have hu := (inclusivePrefix_corridor hqq0 hqq1 hxlo hxhi K n hKqq hnqq).2
  have h1 : r*P ≤ r*(spacingPointwiseHeatPartial q x n+T) :=
    Q'.mul_le_mul_of_nonneg_left _ _ r hl hr.1
  have h2 : r*spacingPointwiseHeatPartial q x n+r*T ≤
      (c*spacingPointwiseHeatPartial (q*q) x n+epsilon)+r*T :=
    Q'.add_le_add_right _ _ _ hp
  have h3 : (c*spacingPointwiseHeatPartial (q*q) x n+epsilon)+r*T ≤
      (c*(P2+T2)+epsilon)+r*T :=
    Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ epsilon
      (Q'.mul_le_mul_of_nonneg_left _ _ c hu hc))
  have h4 : (c*(P2+T2)+epsilon)+r*T ≤
      (c*(P2+T2)+epsilon)+16*T :=
    Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ T hr.2 hT)
  have hresult := Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_add_eqv r _ T))
    (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ h3 h4)))
  exact Q'.le_trans' _ _ _ hresult (Q'.le_of_eqv (by
    change (c*(P2+T2)+epsilon)+16*T ≈ (c*P2+(16*T+c*T2))+epsilon
    exact poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
        (.mul (.const 16) (.var 4)))
      (.add (.add (.mul (.var 0) (.var 1))
        (.add (.mul (.const 16) (.var 4)) (.mul (.var 0) (.var 2)))) (.var 3))
      (by decide) (fun
        | 0 => c
        | 1 => P2
        | 2 => T2
        | 3 => epsilon
        | _ => T)))

/-- Evaluation commutes with the ACTUAL heatPrefix, with K+1 terms. -/
theorem eval_heatPrefix (q : Q') (K : Nat) (X : RatPoly) (rho : Nat → Q') :
    evalRatPoly rho (heatPrefix q K X) ≈
      standardPointwiseHeatPartial q (evalRatPoly rho X) (K+1) := by
  apply Q'.eqv_trans _ _ _ (eval_finitePolySum_range rho _ (K+1))
  apply finSum_eqv_congr
  intro spin
  exact Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
    (Q'.mul_eqv_congr_left _ _ _ (eval_characterPolynomial rho X spin))

private def chordPolynomial (X : RatPoly) : RatPoly :=
  polySmul 2 (polyAdd polyOne (polyNeg X))

/-- Actual original heat-prefix margin polynomial, not a sampled surrogate. -/
def quarticMarginPolynomial (q : Q') (K : Nat) (eta : Q') (X : RatPoly) : RatPoly :=
  polyAdd (polyAdd
    (polySmul (quarticProfileCoefficient q) (heatPrefix (q*q) K X))
    (cap (quarticPrefixError q K+eta)))
    (polyNeg (polyMul (polyMul (chordPolynomial X) (chordPolynomial X)) (heatPrefix q K X)))

private theorem eval_chord (X : RatPoly) (rho : Nat → Q') :
    evalRatPoly rho (chordPolynomial X) ≈ 2*(1-evalRatPoly rho X) :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul rho 2 _)
    (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr' (evalRatPoly_one rho) (evalRatPoly_neg rho X))))

private theorem eval_cap (a : Q') (rho : Nat → Q') : evalRatPoly rho (cap a) ≈ a :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul rho a polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (evalRatPoly_one rho))
      (Q'.mul_one_eqv a))

/-- Exact polynomial evaluation pin, retaining both original prefixes. -/
theorem quarticMarginPolynomial_eval (q : Q') (K : Nat) (eta : Q')
    (X : RatPoly) (rho : Nat → Q') :
    evalRatPoly rho (quarticMarginPolynomial q K eta X) ≈
      (quarticProfileCoefficient q*standardPointwiseHeatPartial (q*q) (evalRatPoly rho X) (K+1) +
        (quarticPrefixError q K+eta)) +
      -(((2*(1-evalRatPoly rho X))*(2*(1-evalRatPoly rho X)))*
        standardPointwiseHeatPartial q (evalRatPoly rho X) (K+1)) := by
  apply Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
  apply Q'.add_eqv_congr'
  · apply Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
    apply Q'.add_eqv_congr'
    · exact Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
        (Q'.mul_eqv_congr_left _ _ _ (eval_heatPrefix (q*q) K X rho))
    · exact eval_cap _ rho
  · apply Q'.eqv_trans _ _ _ (evalRatPoly_neg rho _)
    apply Q'.neg_eqv_congr
    apply Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
    apply mul_congr
    · exact Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
        (mul_congr (eval_chord X rho) (eval_chord X rho))
    · exact eval_heatPrefix q K X rho

/-- Strict pointwise polynomial margin on the entire closed class interval.
The explicit positive eta is NOT a Haar certificate premise. -/
theorem eta_le_quarticMarginPolynomial {q eta : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (heta : (0 : Q') < eta)
    (K : Nat) (hKq : spacingLabelCutoff q ≤ K+1)
    (hKqq : spacingLabelCutoff (q*q) ≤ K+1)
    (X : RatPoly) (rho : Nat → Q')
    (hxlo : (-1 : Q') ≤ evalRatPoly rho X)
    (hxhi : evalRatPoly rho X ≤ (1 : Q')) :
    eta ≤ evalRatPoly rho (quarticMarginPolynomial q K eta X) ∧
      (0 : Q') < evalRatPoly rho (quarticMarginPolynomial q K eta X) := by
  have h := inclusivePrefix_chord_quartic_bound hq0 hq1 hq hxlo hxhi K hKq hKqq
  have hn := Q'.sub_nonneg_of_le h
  have hh := Q'.add_le_add_left eta _ _ hn
  have he : eta+(0 : Q') ≈ eta := QPoly.q_add_zero_eqv eta
  have hr : eta+((quarticProfileCoefficient q*
      standardPointwiseHeatPartial (q*q) (evalRatPoly rho X) (K+1)+quarticPrefixError q K) +
      -(((2*(1-evalRatPoly rho X))*(2*(1-evalRatPoly rho X)))*
        standardPointwiseHeatPartial q (evalRatPoly rho X) (K+1))) ≈
      (quarticProfileCoefficient q*standardPointwiseHeatPartial (q*q) (evalRatPoly rho X) (K+1) +
        (quarticPrefixError q K+eta)) +
      -(((2*(1-evalRatPoly rho X))*(2*(1-evalRatPoly rho X)))*
        standardPointwiseHeatPartial q (evalRatPoly rho X) (K+1)) := by
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.add (.add (.var 1) (.var 2)) (.var 3)))
      (.add (.add (.var 1) (.add (.var 2) (.var 0))) (.var 3))
      (by decide) (fun
        | 0 => eta
        | 1 => quarticProfileCoefficient q*
            standardPointwiseHeatPartial (q*q) (evalRatPoly rho X) (K+1)
        | 2 => quarticPrefixError q K
        | _ => -(((2*(1-evalRatPoly rho X))*(2*(1-evalRatPoly rho X)))*
            standardPointwiseHeatPartial q (evalRatPoly rho X) (K+1)))
  have hmargin := Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ hh (Q'.le_trans' _ _ _ (Q'.le_of_eqv hr)
      (Q'.ge_of_eqv (quarticMarginPolynomial_eval q K eta X rho))))
  exact ⟨hmargin,Q'.pos_of_lt_of_le heta hmargin⟩

/-- Computed inclusive cutoff for one original spacing-tail tolerance. -/
def inclusiveTailCutoff (q epsilon : Q') : Nat :=
  spacingLabelCutoff q+spacingTailCauchyCutoff q epsilon

/-- Every later inclusive cutoff satisfies the computed tail tolerance.
No unspecified tail estimate or uncomputed existence premise is supplied. -/
theorem inclusivePrefixTail_small {q epsilon : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hepsilon : (0 : Q') < epsilon) (K : Nat)
    (hK : inclusiveTailCutoff q epsilon ≤ K) :
    inclusivePrefixTail q K ≤ epsilon := by
  let data := spacingTailRescaleData hq0 epsilon hepsilon
  let M := K+1-spacingLabelCutoff q
  have hM : spacingTailCauchyCutoff q epsilon ≤ M := by
    unfold inclusiveTailCutoff at hK
    dsimp [M]
    omega
  have hp := HKConvGen.pow_base_le_cutoff (spacingTailRatio_pos hq0)
    (spacingTailRatio_lt_one hq0 hq1) data.2.1
  have hpM : spacingTailRatio q ^ M ≤ data.1 :=
    Q'.le_trans' _ _ _ (HKConvGen.pow_base_antitone
      (Q'.le_of_lt (spacingTailRatio_pos hq0))
      (Q'.le_of_lt (spacingTailRatio_lt_one hq0 hq1)) hM) hp
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (spacingTailScale q) hpM
    (Q'.le_of_lt (spacingTailScale_pos hq0))
  have hpin : inclusivePrefixTail q K ≈ spacingTailScale q*(spacingTailRatio q ^ M) := by
    change ((spacingTailHead q*(spacingTailRatio q ^ M))*
      HKConv.divPos 1 (1 + -spacingTailRatio q)) ≈
      (spacingTailHead q*HKConv.divPos 1 (1 + -spacingTailRatio q))*(spacingTailRatio q ^ M)
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun
        | 0 => spacingTailHead q
        | 1 => spacingTailRatio q ^ M
        | _ => HKConv.divPos 1 (1 + -spacingTailRatio q))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ hscaled data.2.2)

#print axioms inclusivePrefixTail
#print axioms quarticProfileCoefficient
#print axioms quarticPrefixError
#print axioms inclusivePrefix_pin
#print axioms inclusivePrefix_corridor
#print axioms inclusivePrefix_chord_quartic_bound
#print axioms eval_heatPrefix
#print axioms quarticMarginPolynomial
#print axioms quarticMarginPolynomial_eval
#print axioms eta_le_quarticMarginPolynomial
#print axioms inclusiveTailCutoff
#print axioms inclusivePrefixTail_small

end YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin
