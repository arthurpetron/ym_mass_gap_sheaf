/-
# The arbitrary-label zero-first-leg Chu--Vandermonde family

For external labels `(0,b,c,d)` with physical contraction order `p`, the left
and right nested maps both reduce to the same binary order-`p` transvectant.
Their channel weights and cross Gram therefore have one common closed
factorial value.  The last equality uses the all-order rising
Chu--Vandermonde binary Gram theorem, not a finite label table.
-/

import YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
import YMGap.Continuum.SU2TransvectantClosedBinaryGram

namespace YMGap.Continuum.SU2OrderedRacahZeroLegFamily

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantRowNormConstancy
open YMGap.Continuum.SU2TransvectantNormalizedRows
open YMGap.Continuum.SU2TransvectantClosedBinaryGram
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## Canonical physical zero-leg channels -/

def zeroLeftFamily (b c p : Nat) (hp : p ≤ min b c) :
    FixedLeftCGChannel 0 b c (b + c - 2 * p) where
  k := 0
  k_le := by omega
  r := p
  r_le := by simpa using hp
  degree_eq := by omega

def zeroRightFamily (b c p : Nat) (hp : p ≤ min b c) :
    FixedRightCGChannel 0 b c (b + c - 2 * p) where
  p := p
  p_le := hp
  r := 0
  r_le := by omega
  degree_eq := by omega

theorem zero_family_intermediates (b c p : Nat) (hp : p ≤ min b c) :
    (zeroLeftFamily b c p hp).intermediate = b ∧
    (zeroRightFamily b c p hp).intermediate = b + c - 2 * p := by
  constructor
  · change 0 + b - 2 * 0 = b
    omega
  · unfold FixedRightCGChannel.intermediate zeroRightFamily
    rfl

/-! ## The degree-zero tensor unit -/

/-- Tensoring a form on the left with the degree-zero monomial and taking the
order-zero transvectant is exactly the original form. -/
theorem transvect_zero_left_unit (n : Nat) (f : BForm) (s : Nat) :
    transvect 0 n 0 (tprod (mono 0) f) s ≈ f s := by
  unfold transvect OmegaK diag tprod
  have hsum : finSum (fun i => mono 0 i * f (s - i)) (s + 1) ≈
      finSum (fun i => if i = 0 then f s else 0) (s + 1) := by
    refine finSum_eqv_congr _ _ (fun i => ?_) (s + 1)
    by_cases hi : i = 0
    · subst i
      simp only [mono, if_pos, Nat.sub_zero]
      exact Q'.one_mul_eqv _
    · simp only [mono, if_neg hi]
      exact Q'.zero_mul_eqv _
  exact Q'.eqv_trans _ _ _ hsum
    (YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (f s) (s + 1) 0 (by omega))

/-! ## Both nested coefficients reduce to one binary coefficient -/

theorem zeroLeftFamily_monomial_eq_binary (b c p : Nat)
    (hp : p ≤ min b c) (j l s : Nat) :
    triLeft 0 b c (b + c - 2 * p) b
        (mono 0) (mono j) (mono l) s ≈
      transvect b c p (tprod (mono j) (mono l)) s := by
  let q := zeroLeftFamily b c p hp
  have he : q.intermediate = b := by
    change 0 + b - 2 * 0 = b
    omega
  have hk := fixedLeft_inner_couplingOrder q
  have hr := fixedLeft_outer_couplingOrder q
  rw [he] at hk hr
  have hinner : BFormEqv
      (transvect 0 b q.k (tprod (mono 0) (mono j))) (mono j) := by
    intro t
    simpa only [q] using transvect_zero_left_unit b (mono j) t
  have htensor : BForm2Eqv
      (tprod (transvect 0 b q.k (tprod (mono 0) (mono j))) (mono l))
      (tprod (mono j) (mono l)) := by
    intro x y
    unfold tprod
    exact Q'.mul_eqv_congr_right _ _ _ (hinner x)
  have houter := transvect_congr b c q.r htensor s
  unfold triLeft
  rw [hk, hr]
  simpa only [q, zeroLeftFamily] using houter

theorem zeroRightFamily_monomial_eq_binary (b c p : Nat)
    (hp : p ≤ min b c) (j l s : Nat) :
    triRight 0 b c (b + c - 2 * p) (b + c - 2 * p)
        (mono 0) (mono j) (mono l) s ≈
      transvect b c p (tprod (mono j) (mono l)) s := by
  let q := zeroRightFamily b c p hp
  have he : q.intermediate = b + c - 2 * p := by
    unfold q FixedRightCGChannel.intermediate zeroRightFamily
    rfl
  have hpq := fixedRight_inner_couplingOrder q
  have hr := fixedRight_outer_couplingOrder q
  rw [he] at hpq hr
  unfold triRight
  rw [hpq, hr]
  simpa only [q, zeroRightFamily] using
    transvect_zero_left_unit (b + c - 2 * p)
      (transvect b c p (tprod (mono j) (mono l))) s

/-! ## Reordering the invariant binary Gram -/

def binaryGramTriOrder (b c p : Nat) : Q' :=
  finSum (fun j => finSum (fun l => finSum (fun s =>
    tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq (b + c - 2 * p) s *
        (transvect b c p (tprod (mono j) (mono l)) s *
          transvect b c p (tprod (mono j) (mono l)) s))
    (b + c - 2 * p + 1)) (c + 1)) (b + 1)

theorem binaryGramTriOrder_eq_binaryTransvectantGram (b c p : Nat) :
    binaryGramTriOrder b c p ≈ binaryTransvectantGram b c p := by
  let d := b + c - 2 * p
  let A : Nat → Nat → Nat → Q' := fun j l s =>
    tvBinomQ b j * tvBinomQ c l * symMonomialNormSq d s *
      (transvect b c p (tprod (mono j) (mono l)) s *
        transvect b c p (tprod (mono j) (mono l)) s)
  have hswap1 : finSum (fun j => finSum (fun l => finSum (fun s => A j l s)
        (d + 1)) (c + 1)) (b + 1) ≈
      finSum (fun j => finSum (fun s => finSum (fun l => A j l s)
        (c + 1)) (d + 1)) (b + 1) := by
    refine finSum_eqv_congr _ _ (fun j => ?_) (b + 1)
    exact finSum_swap (fun l s => A j l s) (c + 1) (d + 1)
  have hswap2 : finSum (fun j => finSum (fun s => finSum (fun l => A j l s)
        (c + 1)) (d + 1)) (b + 1) ≈
      finSum (fun s => finSum (fun j => finSum (fun l => A j l s)
        (c + 1)) (b + 1)) (d + 1) :=
    finSum_swap (fun j s => finSum (fun l => A j l s) (c + 1))
      (b + 1) (d + 1)
  have hrearrange : finSum (fun s => finSum (fun j => finSum (fun l =>
        A j l s) (c + 1)) (b + 1)) (d + 1) ≈
      finSum (fun s => symMonomialNormSq d s *
        finSum (fun j => finSum (fun l => tvBinomQ c l *
          (tvBinomQ b j *
            (transvect b c p (tprod (mono j) (mono l)) s *
              transvect b c p (tprod (mono j) (mono l)) s)))
          (c + 1)) (b + 1)) (d + 1) := by
    refine finSum_eqv_congr _ _ (fun s => ?_) (d + 1)
    refine Q'.eqv_trans _
      (finSum (fun j => finSum (fun l => symMonomialNormSq d s *
        (tvBinomQ c l * (tvBinomQ b j *
          (transvect b c p (tprod (mono j) (mono l)) s *
            transvect b c p (tprod (mono j) (mono l)) s))))
        (c + 1)) (b + 1)) _ ?_ ?_
    · refine finSum_eqv_congr _ _ (fun j => ?_) (b + 1)
      refine finSum_eqv_congr _ _ (fun l => ?_) (c + 1)
      unfold A
      ring_qeqv
    · refine Q'.eqv_trans _
        (finSum (fun j => symMonomialNormSq d s *
          finSum (fun l => tvBinomQ c l * (tvBinomQ b j *
            (transvect b c p (tprod (mono j) (mono l)) s *
              transvect b c p (tprod (mono j) (mono l)) s)))
            (c + 1)) (b + 1)) _ ?_ ?_
      · refine finSum_eqv_congr _ _ (fun j => ?_) (b + 1)
        exact Q'.eqv_symm (const_mul_finSum _ _ (c + 1))
      · exact Q'.eqv_symm (const_mul_finSum _ _ (b + 1))
  unfold binaryGramTriOrder
  change finSum (fun j => finSum (fun l => finSum (fun s => A j l s)
      (d + 1)) (c + 1)) (b + 1) ≈ _
  refine Q'.eqv_trans _ _ _ hswap1 ?_
  refine Q'.eqv_trans _ _ _ hswap2 ?_
  refine Q'.eqv_trans _ _ _ hrearrange ?_
  unfold binaryTransvectantGram binaryNormalizedRowNorm binaryRawRowNorm
    tensorBinomPair
  exact Q'.eqv_refl _

/-! ## Zero-leg three-map Gram collapse -/

private theorem zeroLegGramTerm_eq (B C N L R X : Q')
    (hL : L ≈ X) (hR : R ≈ X) :
    tvBinomQ 0 0 * B * C * N * (L * R) ≈
      B * C * N * (X * X) := by
  have hprod : L * R ≈ X * X := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right L X R hL)
      (Q'.mul_eqv_congr_left X R X hR)
  have h0 : tvBinomQ 0 0 ≈ 1 := by decide
  have hprefix : tvBinomQ 0 0 * B * C * N ≈ 1 * B * C * N := by
    exact Q'.mul_eqv_congr_right _ _ N
      (Q'.mul_eqv_congr_right _ _ C
        (Q'.mul_eqv_congr_right _ _ B h0))
  refine Q'.eqv_trans _ ((1 * B * C * N) * (X * X)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (L * R) hprefix)
      (Q'.mul_eqv_congr_left (1 * B * C * N) _ _ hprod)
  · ring_qeqv

theorem triMapInner_zero_leg_eq_binaryGramTriOrder (b c p : Nat)
    (L R : BForm → BForm → BForm → BForm)
    (hL : ∀ j l s, L (mono 0) (mono j) (mono l) s ≈
      transvect b c p (tprod (mono j) (mono l)) s)
    (hR : ∀ j l s, R (mono 0) (mono j) (mono l) s ≈
      transvect b c p (tprod (mono j) (mono l)) s) :
    triMapInner 0 b c (b + c - 2 * p) L R ≈
      binaryGramTriOrder b c p := by
  unfold triMapInner binaryGramTriOrder
  change (0 + finSum (fun j => finSum (fun l => finSum (fun s =>
    tvBinomQ 0 0 * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq (b + c - 2 * p) s *
        (L (mono 0) (mono j) (mono l) s *
          R (mono 0) (mono j) (mono l) s))
    (b + c - 2 * p + 1)) (c + 1)) (b + 1)) ≈ _
  refine Q'.eqv_trans _
    (finSum (fun j => finSum (fun l => finSum (fun s =>
      tvBinomQ 0 0 * tvBinomQ b j * tvBinomQ c l *
        symMonomialNormSq (b + c - 2 * p) s *
          (L (mono 0) (mono j) (mono l) s *
            R (mono 0) (mono j) (mono l) s))
      (b + c - 2 * p + 1)) (c + 1)) (b + 1)) _
    (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
  refine finSum_eqv_congr _ _ (fun j => ?_) (b + 1)
  refine finSum_eqv_congr _ _ (fun l => ?_) (c + 1)
  refine finSum_eqv_congr _ _ (fun s => ?_) (b + c - 2 * p + 1)
  exact zeroLegGramTerm_eq _ _ _ _ _ _ (hL j l s) (hR j l s)

/-! ## Closed zero-leg channel weights and cross -/

theorem zero_family_cross_eq_binaryGram (b c p : Nat)
    (hp : p ≤ min b c) :
    triCrossChannelWeight (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp) ≈
      binaryTransvectantGram b c p := by
  refine Q'.eqv_trans _ (binaryGramTriOrder b c p) _ ?_
    (binaryGramTriOrder_eq_binaryTransvectantGram b c p)
  unfold triCrossChannelWeight
  exact triMapInner_zero_leg_eq_binaryGramTriOrder b c p _ _
    (fun j l s => by
      simpa only [zeroLeftFamily, FixedLeftCGChannel.intermediate,
        Nat.zero_add, Nat.mul_zero, Nat.sub_zero] using
        zeroLeftFamily_monomial_eq_binary b c p hp j l s)
    (fun j l s => by
      simpa only [zeroRightFamily, FixedRightCGChannel.intermediate] using
        zeroRightFamily_monomial_eq_binary b c p hp j l s)

theorem zero_family_leftWeight_eq_binaryGram (b c p : Nat)
    (hp : p ≤ min b c) :
    triLeftChannelWeight 0 b c (b + c - 2 * p) b ≈
      binaryTransvectantGram b c p := by
  refine Q'.eqv_trans _ (binaryGramTriOrder b c p) _ ?_
    (binaryGramTriOrder_eq_binaryTransvectantGram b c p)
  unfold triLeftChannelWeight
  exact triMapInner_zero_leg_eq_binaryGramTriOrder b c p _ _
    (zeroLeftFamily_monomial_eq_binary b c p hp)
    (zeroLeftFamily_monomial_eq_binary b c p hp)

theorem zero_family_rightWeight_eq_binaryGram (b c p : Nat)
    (hp : p ≤ min b c) :
    triRightChannelWeight 0 b c (b + c - 2 * p) (b + c - 2 * p) ≈
      binaryTransvectantGram b c p := by
  refine Q'.eqv_trans _ (binaryGramTriOrder b c p) _ ?_
    (binaryGramTriOrder_eq_binaryTransvectantGram b c p)
  unfold triRightChannelWeight
  exact triMapInner_zero_leg_eq_binaryGramTriOrder b c p _ _
    (zeroRightFamily_monomial_eq_binary b c p hp)
    (zeroRightFamily_monomial_eq_binary b c p hp)

/-- **All-label zero-leg Chu--Vandermonde normalization.** -/
theorem zero_family_closed_factorial_normalization (b c p : Nat)
    (hp : p ≤ min b c) :
    triCrossChannelWeight (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp) ≈
      Q'.ofNat (b + c - 2 * p + 1) *
        binaryRowFactorialProduct b c p ∧
    triLeftChannelWeight 0 b c (b + c - 2 * p) b ≈
      Q'.ofNat (b + c - 2 * p + 1) *
        binaryRowFactorialProduct b c p ∧
    triRightChannelWeight 0 b c (b + c - 2 * p) (b + c - 2 * p) ≈
      Q'.ofNat (b + c - 2 * p + 1) *
        binaryRowFactorialProduct b c p := by
  have hb := Nat.le_min.mp hp
  have hclosed := binaryTransvectantGram_factorial_product b c p hb.1 hb.2
  exact ⟨Q'.eqv_trans _ _ _ (zero_family_cross_eq_binaryGram b c p hp) hclosed,
    Q'.eqv_trans _ _ _ (zero_family_leftWeight_eq_binaryGram b c p hp) hclosed,
    Q'.eqv_trans _ _ _ (zero_family_rightWeight_eq_binaryGram b c p hp) hclosed⟩

/-- The explicit threefold carrier inherits the same all-label closed value. -/
theorem zero_family_collapsedCross_closed (b c p : Nat)
    (hp : p ≤ min b c) :
    collapsedFactorialCrossSum (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp) ≈
      Q'.ofNat (b + c - 2 * p + 1) *
        binaryRowFactorialProduct b c p := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (triCrossChannelWeight_eq_collapsedFactorialCrossSum
        (zeroLeftFamily b c p hp) (zeroRightFamily b c p hp)))
    (zero_family_closed_factorial_normalization b c p hp).1

end YMGap.Continuum.SU2OrderedRacahZeroLegFamily

#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegFamily.transvect_zero_left_unit
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegFamily.zeroLeftFamily_monomial_eq_binary
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegFamily.zeroRightFamily_monomial_eq_binary
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegFamily.binaryGramTriOrder_eq_binaryTransvectantGram
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegFamily.triMapInner_zero_leg_eq_binaryGramTriOrder
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegFamily.zero_family_closed_factorial_normalization
#print axioms YMGap.Continuum.SU2OrderedRacahZeroLegFamily.zero_family_collapsedCross_closed
