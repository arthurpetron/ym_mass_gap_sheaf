/-
# Structural right-channel Gram orthogonality and the stretched family

The canonical Schur bridge only needs off-diagonal orthogonality of distinct
right intermediate channels.  This file isolates that smallest exact residual,
proves that it supplies every canonical enumerated Gram row, and removes the
separate diagonal-normalization concern: the diagonal entry is definitionally
the already-derived channel weight.

For the infinite stretched family `d=a+b+c`, every admissible right channel is
the unique order-zero channel.  Hence the off-diagonal residual is vacuous for
a structural reason, while the diagonal weight is proved strictly positive by
exhibiting the exact unit summand at the all-zero monomial and bounding it by
the nonnegative finite Gram sum.

More generally, every physical right channel has strictly positive Gram
weight.  Coordinatewise transvectant surjectivity supplies a nonzero inner
monomial pivot at the slot needed by the outer extremal pivot; its coefficient
square is a strictly positive summand of the exact finite Gram expression.
-/

import YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
import YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.SU2OrderedRightGramOrthogonality

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantAdmissibleExtremal
open YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d := by
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b c hab)
    (Q'.mul_eqv_congr_left b c d hcd)

private theorem eqv_zero_iff_num_zero (x : Q') :
    x ≈ 0 ↔ x.num = 0 := by
  constructor
  · intro h
    have h' : x.num * (1 : Int) = (0 : Int) * (x.den : Int) := h
    simpa only [Int.mul_one, Int.zero_mul] using h'
  · intro h
    unfold Q'.eqv
    change x.num * (1 : Int) = (0 : Int) * (x.den : Int)
    rw [h]
    simp only [Int.zero_mul]

private theorem mul_not_eqv_zero {x y : Q'}
    (hx : ¬ x ≈ 0) (hy : ¬ y ≈ 0) : ¬ x * y ≈ 0 := by
  intro hxy
  have hnum : x.num * y.num = 0 :=
    (eqv_zero_iff_num_zero (x * y)).mp hxy
  rcases Int.mul_eq_zero.mp hnum with hx0 | hy0
  · exact hx ((eqv_zero_iff_num_zero x).mpr hx0)
  · exact hy ((eqv_zero_iff_num_zero y).mpr hy0)

private theorem self_mul_pos_of_not_eqv_zero (x : Q') (hx : ¬ x ≈ 0) :
    (0 : Q') < x * x := by
  apply CReal.pos_of_num_pos
  rw [Q'.mul_num_cast]
  have hn : x.num ≠ 0 := fun h => hx ((eqv_zero_iff_num_zero x).mpr h)
  rcases Int.lt_or_gt_of_ne hn with hneg | hpos
  · have hp : 0 < (-x.num) * (-x.num) :=
      Int.mul_pos (Int.neg_pos.mpr hneg) (Int.neg_pos.mpr hneg)
    simpa only [Int.neg_mul, Int.mul_neg, Int.neg_neg] using hp
  · exact Int.mul_pos hpos hpos

private theorem tvBinomQ_pos_of_le (n i : Nat) (hi : i ≤ n) :
    (0 : Q') < tvBinomQ n i := by
  unfold tvBinomQ
  rw [if_pos hi]
  apply CReal.pos_of_num_pos
  change (0 : Int) < Int.ofNat (tvFact n)
  exact Int.natCast_pos.mpr (tvFact_pos n)

private theorem symMonomialNormSq_pos_of_le (n i : Nat) (hi : i ≤ n) :
    (0 : Q') < symMonomialNormSq n i := by
  unfold symMonomialNormSq
  rw [if_pos hi]
  apply CReal.pos_of_num_pos
  change (0 : Int) < Int.ofNat (tvFact i * tvFact (n - i))
  exact Int.natCast_pos.mpr
    (Nat.mul_pos (tvFact_pos i) (tvFact_pos (n - i)))

private theorem swap_middle_mul (x a y : Q') :
    x * (a * y) ≈ a * (x * y) := by
  refine Q'.eqv_trans _ ((x * a) * y) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((a * x) * y) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.mul_assoc_eqv _ _ _

/-! ## 1. The exact all-label residual -/

/-- The genuinely nontrivial part of right-channel Gram orthogonality: distinct
intermediate contraction orders have zero invariant Hilbert--Schmidt pairing.
No diagonal normalization is included. -/
def RightChannelOffDiagonalOrthogonality (a b c d : Nat) : Prop :=
  ∀ (q u : FixedRightCGChannel a b c d), q.p ≠ u.p →
    triMapInner a b c d
      (triRight a b c d q.intermediate)
      (triRight a b c d u.intermediate) ≈ 0

/-- Once the off-diagonal residual is known, the complete Gram law follows:
equal inner orders give equal proof-carrying channels, and the diagonal is
exactly `triRightChannelWeight` by definition. -/
theorem rightChannel_gram_of_offDiagonal {a b c d : Nat}
    (horth : RightChannelOffDiagonalOrthogonality a b c d)
    (q u : FixedRightCGChannel a b c d) :
    triMapInner a b c d
        (triRight a b c d q.intermediate)
        (triRight a b c d u.intermediate) ≈
      if q.p = u.p then triRightChannelWeight a b c d u.intermediate else 0 := by
  by_cases hpu : q.p = u.p
  · rw [if_pos hpu]
    have hqu := fixedRightChannel_eq_of_p_eq q u hpu
    subst q
    exact Q'.eqv_refl _
  · rw [if_neg hpu]
    exact horth q u hpu

/-- Valid total lookup is literal list indexing, so the fallback is absent on
the canonical enumeration window. -/
theorem fixedRightChannelAt_eq_getElem {a b c d : Nat}
    (fallback : FixedRightCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c d)) (q : Nat)
    (hq : q < qs.length) :
    fixedRightChannelAt fallback qs q = qs[q] := by
  unfold fixedRightChannelAt
  rw [List.getElem?_eq_getElem hq]
  rfl

/-- On a duplicate-free channel list, valid total lookup is injective in its
index. -/
theorem fixedRightChannelAt_injective_of_nodup {a b c d : Nat}
    (fallback : FixedRightCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c d)) (hqs : qs.Nodup)
    (q r : Nat) (hq : q < qs.length) (hr : r < qs.length)
    (hqr : fixedRightChannelAt fallback qs q =
      fixedRightChannelAt fallback qs r) : q = r := by
  have hopt : qs[q]? = qs[r]? := by
    rw [List.getElem?_eq_getElem hq, List.getElem?_eq_getElem hr]
    exact congrArg some (by
      simpa only [fixedRightChannelAt_eq_getElem fallback qs q hq,
        fixedRightChannelAt_eq_getElem fallback qs r hr] using hqr)
  exact List.getElem?_inj hq hqs hopt

/-- The smallest off-diagonal predicate supplies the exact canonical Gram row
expected by the Schur bridge, for every left channel and every valid selected
target index. -/
theorem enumeratedRightGramOrthogonalAt_of_offDiagonal
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) (target : Nat)
    (htarget : target < (fixedRightChannels a b c d).length)
    (horth : RightChannelOffDiagonalOrthogonality a b c d) :
    EnumeratedRightGramOrthogonalAt qL target := by
  refine ⟨htarget, ?_⟩
  intro q hq
  by_cases hqt : q = target
  · subst q
    rw [if_pos rfl]
    exact Q'.eqv_refl _
  · rw [if_neg hqt]
    apply horth
    intro hp
    have hchannels : enumeratedRightChannel qL q =
        enumeratedRightChannel qL target :=
      fixedRightChannel_eq_of_p_eq _ _ hp
    exact hqt (fixedRightChannelAt_injective_of_nodup
      (fixedRightFallbackOfFixedLeft qL)
      (fixedRightChannels a b c d)
      (fixedRightChannels_nodup a b c d) q target hq htarget hchannels)

/-! ## 2. Every physical right channel has a nonzero monomial pivot -/

theorem fixedRight_inner_fusionOK {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    fusionOK b c q.intermediate = true := by
  apply (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
    b c q.intermediate).mpr
  have hp := Nat.le_min.mp q.p_le
  refine ⟨q.p, hp.1, hp.2, ?_⟩
  unfold FixedRightCGChannel.intermediate
  omega

theorem fixedRight_outer_fusionOK {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    fusionOK a q.intermediate d = true := by
  apply (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
    a q.intermediate d).mpr
  have hr := Nat.le_min.mp q.r_le
  refine ⟨q.r, hr.1, hr.2, ?_⟩
  have hd := q.degree_eq
  unfold FixedRightCGChannel.intermediate at hd ⊢
  omega

/-- A proof-carrying right channel has an explicit physical monomial triple
on which its nested transvectant coefficient is nonzero.  The inner pair is
chosen by coordinatewise surjectivity at output slot `f-r`; the first factor
then uses the positive outer extremal pivot. -/
theorem fixedRight_nonzero_monomial_pivot {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    ∃ j k, j ≤ b ∧ k ≤ c ∧
      ¬ triRight a b c d q.intermediate
        (mono a) (mono j) (mono k) d ≈ 0 := by
  have hr := Nat.le_min.mp q.r_le
  obtain ⟨j, k, alpha, hj, hk, halpha, hinner⟩ :=
    admissible_transvect_coordinate_pivot b c q.intermediate
      (q.intermediate - q.r) (fixedRight_inner_fusionOK q) (by omega)
  let carrier : BForm2 :=
    tprod (mono a) (mono (q.intermediate - q.r))
  have htprod : BForm2Eqv
      (tprod (mono a)
        (transvect b c (couplingOrder b c q.intermediate)
          (tprod (mono j) (mono k))))
      (bscale alpha carrier) := by
    intro x y
    have hin := hinner y
    refine Q'.eqv_trans _ (mono a x *
      (alpha * mono (q.intermediate - q.r) y)) _
      (Q'.mul_eqv_congr_left _ _ _ hin) ?_
    simpa only [bscale, carrier, tprod] using
      swap_middle_mul (mono a x) alpha
        (mono (q.intermediate - q.r) y)
  have hcongr := transvect_congr a q.intermediate q.r htprod d
  have hscale := transvect_scale a q.intermediate q.r alpha carrier d
  have hdegree : a + q.intermediate - 2 * q.r = d := by
    have hd := q.degree_eq
    unfold FixedRightCGChannel.intermediate at hd ⊢
    exact hd
  have hext : transvect a q.intermediate q.r carrier d ≈
      extremalCoeff a q.r := by
    let F : BForm := transvect a q.intermediate q.r carrier
    have hext0 : F (a + q.intermediate - 2 * q.r) ≈
        extremalCoeff a q.r := by
      simpa only [F, carrier] using
        transvect_extremal q.r a q.intermediate hr.1 hr.2
    have hvalue : F d = F (a + q.intermediate - 2 * q.r) :=
      congrArg F hdegree.symm
    change F d ≈ extremalCoeff a q.r
    rw [hvalue]
    exact hext0
  have hcoeff : triRight a b c d q.intermediate
      (mono a) (mono j) (mono k) d ≈
      alpha * extremalCoeff a q.r := by
    unfold triRight
    rw [fixedRight_outer_couplingOrder q]
    exact Q'.eqv_trans _ _ _ hcongr
      (Q'.eqv_trans _ _ _ hscale
        (Q'.mul_eqv_congr_left alpha _ _ hext))
  refine ⟨j, k, hj, hk, ?_⟩
  intro hzero
  have hproduct : alpha * extremalCoeff a q.r ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcoeff) hzero
  exact mul_not_eqv_zero halpha
    (extremalCoeff_not_eqv_zero a q.r hr.1) hproduct

/-! ## 3. The infinite stretched family -/

/-- The unique order-zero right channel at maximal final degree. -/
def stretchedRightChannel (a b c : Nat) :
    FixedRightCGChannel a b c (a + b + c) where
  p := 0
  p_le := Nat.zero_le _
  r := 0
  r_le := Nat.zero_le _
  degree_eq := by omega

/-- Every admissible right channel at maximal final degree has inner order
zero. -/
theorem stretched_right_channel_p_eq_zero (a b c : Nat)
    (q : FixedRightCGChannel a b c (a + b + c)) : q.p = 0 := by
  have hp := Nat.le_min.mp q.p_le
  have hr := Nat.le_min.mp q.r_le
  have hd := q.degree_eq
  unfold FixedRightCGChannel.intermediate at hr
  omega

/-- Consequently the stretched right channel is genuinely unique, including
its proof fields and outer contraction order. -/
theorem stretched_right_channel_unique (a b c : Nat)
    (q : FixedRightCGChannel a b c (a + b + c)) :
    q = stretchedRightChannel a b c := by
  apply fixedRightChannel_eq_of_p_eq
  exact stretched_right_channel_p_eq_zero a b c q

/-- Off-diagonal orthogonality holds on the entire infinite stretched family:
two distinct inner orders cannot exist. -/
theorem stretched_right_offDiagonal (a b c : Nat) :
    RightChannelOffDiagonalOrthogonality a b c (a + b + c) := by
  intro q u hne
  exact False.elim (hne (by
    rw [stretched_right_channel_p_eq_zero a b c q,
      stretched_right_channel_p_eq_zero a b c u]))

/-! ## 4. A sharper stretched lower bound from a visible unit summand -/

private theorem symMonomialNormSq_zero (n : Nat) :
    symMonomialNormSq n 0 ≈ 1 := by
  unfold symMonomialNormSq
  rw [if_pos (Nat.zero_le n), Nat.sub_zero]
  simp only [tvFact, Nat.one_mul]
  exact mkN_self_pred_eqv_one (tvFact n) (tvFact_pos n)

/-- At the all-zero input and output monomial, the stretched right channel has
coefficient exactly one. -/
theorem stretched_triRight_zero_coefficient (a b c : Nat) :
    triRight a b c (a + b + c) (b + c)
      (mono 0) (mono 0) (mono 0) 0 ≈ 1 := by
  have hin : couplingOrder b c (b + c) = 0 := by
    unfold couplingOrder
    omega
  have hout : couplingOrder a (b + c) (a + b + c) = 0 := by
    unfold couplingOrder
    omega
  have htprod : BForm2Eqv
      (tprod (mono 0)
        (transvect b c 0 (tprod (mono 0) (mono 0))))
      (tprod (mono 0) (mono 0)) := by
    intro x y
    exact Q'.mul_eqv_congr_left _ _ _
      (by simpa only [mono] using transvect_zero_monomial b c 0 0 y)
  unfold triRight
  rw [hin, hout]
  exact Q'.eqv_trans _ _ _ (transvect_congr a (b + c) 0 htprod 0)
    (by simpa using transvect_zero_monomial a (b + c) 0 0 0)

/-- The displayed all-zero diagonal Gram summand is exactly one. -/
theorem stretched_zero_diagonal_summand (a b c : Nat) :
    triDiagonalSummand a b c (a + b + c)
      (triRight a b c (a + b + c) (b + c)) 0 0 0 0 ≈ 1 := by
  unfold triDiagonalSummand
  have ha := tvBinomQ_zero a
  have hb := tvBinomQ_zero b
  have hc := tvBinomQ_zero c
  have hd := symMonomialNormSq_zero (a + b + c)
  have hcoeff := stretched_triRight_zero_coefficient a b c
  calc
    _ ≈ (1 : Q') * 1 * 1 * 1 * (1 * 1) := by
      exact mul_eqv_congr
        (mul_eqv_congr (mul_eqv_congr (mul_eqv_congr ha hb) hc) hd)
        (mul_eqv_congr hcoeff hcoeff)
    _ ≈ (1 : Q') := by decide

private theorem head_le_finSum (g : Nat → Q')
    (hg : ∀ i, (0 : Q') ≤ g i) :
    ∀ k, g 0 ≤ finSum g (k + 1)
  | 0 => by
      rw [finSum_succ, finSum_zero, Q'.zero_add']
      exact Q'.le_refl' _
  | k + 1 => by
      rw [finSum_succ]
      exact Q'.le_trans' _ _ _ (head_le_finSum g hg k)
        (Q'.add_le_self_of_nonneg _ _ (hg (k + 1)))

private theorem term_le_finSum (g : Nat → Q')
    (hg : ∀ i, (0 : Q') ≤ g i) :
    ∀ n k, k < n → g k ≤ finSum g n
  | 0, k, hk => by omega
  | n + 1, k, hk => by
      rw [finSum_succ]
      by_cases hkn : k = n
      · subst k
        have hsum : (0 : Q') ≤ finSum g n :=
          YMGap.RG.finSum_nonneg _ hg n
        exact Q'.le_trans' _ (g n + finSum g n) _
          (Q'.add_le_self_of_nonneg _ _ hsum)
          (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
      · exact Q'.le_trans' _ _ _ (term_le_finSum g hg n k (by omega))
          (Q'.add_le_self_of_nonneg _ _ (hg n))

private theorem nested_diagonal_term_le (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm)
    (i j k s : Nat) (hi : i < a + 1) (hj : j < b + 1)
    (hk : k < c + 1) (hs : s < d + 1) :
    triDiagonalSummand a b c d L i j k s ≤
      triMapInner a b c d L L := by
  let S := fun i j k s => triDiagonalSummand a b c d L i j k s
  have hS : ∀ i j k s, (0 : Q') ≤ S i j k s :=
    fun i j k s => triDiagonalSummand_nonneg a b c d L i j k s
  have h1 : S i j k s ≤ finSum (fun u => S i j k u) (d + 1) :=
    term_le_finSum _ (hS i j k) (d + 1) s hs
  have h2 : finSum (fun u => S i j k u) (d + 1) ≤
      finSum (fun v => finSum (fun u => S i j v u) (d + 1)) (c + 1) :=
    term_le_finSum _ (fun v => YMGap.RG.finSum_nonneg _
      (hS i j v) (d + 1)) (c + 1) k hk
  have h3 : finSum (fun v => finSum (fun u => S i j v u) (d + 1))
        (c + 1) ≤
      finSum (fun w => finSum (fun v => finSum (fun u => S i w v u)
        (d + 1)) (c + 1)) (b + 1) :=
    term_le_finSum _ (fun w => YMGap.RG.finSum_nonneg _ (fun v =>
      YMGap.RG.finSum_nonneg _ (hS i w v) (d + 1)) (c + 1))
      (b + 1) j hj
  have h4 : finSum (fun w => finSum (fun v => finSum (fun u => S i w v u)
        (d + 1)) (c + 1)) (b + 1) ≤
      finSum (fun x => finSum (fun w => finSum (fun v => finSum
        (fun u => S x w v u) (d + 1)) (c + 1)) (b + 1)) (a + 1) :=
    term_le_finSum _ (fun x => YMGap.RG.finSum_nonneg _ (fun w =>
      YMGap.RG.finSum_nonneg _ (fun v => YMGap.RG.finSum_nonneg _
        (hS x w v) (d + 1)) (c + 1)) (b + 1)) (a + 1) i hi
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2
    (Q'.le_trans' _ _ _ h3 (by simpa only [S, triMapInner] using h4)))

/-- Every proof-carrying physical right channel has strictly positive derived
Gram weight.  No normalization is assumed: a nonzero monomial coefficient is
exhibited and its positive diagonal square is bounded by the finite sum. -/
theorem right_channel_weight_pos_all {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    (0 : Q') < triRightChannelWeight a b c d q.intermediate := by
  obtain ⟨j, k, hj, hk, hcoeff⟩ := fixedRight_nonzero_monomial_pivot q
  let C : Q' := triRight a b c d q.intermediate
    (mono a) (mono j) (mono k) d
  have hC : ¬ C ≈ 0 := by simpa only [C] using hcoeff
  have hsq : (0 : Q') < C * C := self_mul_pos_of_not_eqv_zero C hC
  have ha : (0 : Q') < tvBinomQ a a := tvBinomQ_pos_of_le a a (Nat.le_refl a)
  have hb : (0 : Q') < tvBinomQ b j := tvBinomQ_pos_of_le b j hj
  have hc : (0 : Q') < tvBinomQ c k := tvBinomQ_pos_of_le c k hk
  have hd : (0 : Q') < symMonomialNormSq d d :=
    symMonomialNormSq_pos_of_le d d (Nat.le_refl d)
  have hsummand : (0 : Q') < triDiagonalSummand a b c d
      (triRight a b c d q.intermediate) a j k d := by
    unfold triDiagonalSummand
    exact Q'.mul_pos
      (Q'.mul_pos (Q'.mul_pos (Q'.mul_pos ha hb) hc) hd) hsq
  have hle := nested_diagonal_term_le a b c d
    (triRight a b c d q.intermediate) a j k d
    (by omega) (by omega) (by omega) (by omega)
  exact Q'.pos_of_lt_of_le hsummand (by
    simpa only [triRightChannelWeight] using hle)

private theorem nested_diagonal_head_le (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) :
    triDiagonalSummand a b c d L 0 0 0 0 ≤
      triMapInner a b c d L L := by
  let S := fun i j k s => triDiagonalSummand a b c d L i j k s
  have hs : S 0 0 0 0 ≤ finSum (fun s => S 0 0 0 s) (d + 1) :=
    head_le_finSum _ (fun s => triDiagonalSummand_nonneg a b c d L 0 0 0 s) d
  have hk : finSum (fun s => S 0 0 0 s) (d + 1) ≤
      finSum (fun k => finSum (fun s => S 0 0 k s) (d + 1)) (c + 1) :=
    head_le_finSum _ (fun k => YMGap.RG.finSum_nonneg _
      (fun s => triDiagonalSummand_nonneg a b c d L 0 0 k s) (d + 1)) c
  have hj : finSum (fun k => finSum (fun s => S 0 0 k s) (d + 1)) (c + 1) ≤
      finSum (fun j => finSum (fun k => finSum (fun s => S 0 j k s)
        (d + 1)) (c + 1)) (b + 1) :=
    head_le_finSum _ (fun j => YMGap.RG.finSum_nonneg _ (fun k =>
      YMGap.RG.finSum_nonneg _
        (fun s => triDiagonalSummand_nonneg a b c d L 0 j k s)
        (d + 1)) (c + 1)) b
  have hi : finSum (fun j => finSum (fun k => finSum (fun s => S 0 j k s)
        (d + 1)) (c + 1)) (b + 1) ≤
      finSum (fun i => finSum (fun j => finSum (fun k => finSum
        (fun s => S i j k s) (d + 1)) (c + 1)) (b + 1)) (a + 1) :=
    head_le_finSum _ (fun i => YMGap.RG.finSum_nonneg _ (fun j =>
      YMGap.RG.finSum_nonneg _ (fun k => YMGap.RG.finSum_nonneg _
        (fun s => triDiagonalSummand_nonneg a b c d L i j k s)
        (d + 1)) (c + 1)) (b + 1)) a
  exact Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ hk
    (Q'.le_trans' _ _ _ hj (by simpa only [S, triMapInner] using hi)))

/-- The stretched channel Gram weight is at least one, uniformly in all three
external labels. -/
theorem stretched_right_weight_ge_one (a b c : Nat) :
    (1 : Q') ≤ triRightChannelWeight a b c (a + b + c) (b + c) := by
  have hhead := nested_diagonal_head_le a b c (a + b + c)
    (triRight a b c (a + b + c) (b + c))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (stretched_zero_diagonal_summand a b c)) hhead

/-- In particular the stretched right Gram weight is strictly positive, with
the explicit rational lower witness `1`. -/
theorem stretched_right_weight_pos (a b c : Nat) :
    (0 : Q') < triRightChannelWeight a b c (a + b + c) (b + c) :=
  Q'.pos_of_lt_of_le (by decide) (stretched_right_weight_ge_one a b c)

/-- Complete Gram law for every pair of proof-carrying channels in the
infinite stretched family. -/
theorem stretched_right_gram (a b c : Nat)
    (q u : FixedRightCGChannel a b c (a + b + c)) :
    triMapInner a b c (a + b + c)
        (triRight a b c (a + b + c) q.intermediate)
        (triRight a b c (a + b + c) u.intermediate) ≈
      if q.p = u.p then
        triRightChannelWeight a b c (a + b + c) u.intermediate else 0 :=
  rightChannel_gram_of_offDiagonal (stretched_right_offDiagonal a b c) q u

end YMGap.Continuum.SU2OrderedRightGramOrthogonality

#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.rightChannel_gram_of_offDiagonal
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.fixedRightChannelAt_eq_getElem
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.fixedRightChannelAt_injective_of_nodup
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.enumeratedRightGramOrthogonalAt_of_offDiagonal
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.fixedRight_inner_fusionOK
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.fixedRight_outer_fusionOK
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.fixedRight_nonzero_monomial_pivot
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.right_channel_weight_pos_all
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_right_channel_p_eq_zero
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_right_channel_unique
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_right_offDiagonal
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_triRight_zero_coefficient
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_zero_diagonal_summand
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_right_weight_ge_one
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_right_weight_pos
#print axioms YMGap.Continuum.SU2OrderedRightGramOrthogonality.stretched_right_gram
