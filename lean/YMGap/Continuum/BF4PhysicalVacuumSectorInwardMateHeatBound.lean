/-
# Six-face heat payment for the physical BF4 inward mate

At the physical strong-coupling nome `w = 1/2`, replace an even SU(2) label
by `1` at zero and by its predecessor away from zero.  On a non-vacuum
six-face even cube, at least one coordinate is positive.  That coordinate
pays the sharp consecutive-weight factor `1/16`; each of the other five
coordinates costs at most the vacuum-to-fundamental factor `4`.  Hence

    heat(source) <= 64 * heat(evenInwardMate(source)).

For an odd cube every coordinate is positive, and predecessor lowering gives
the stronger factor `(1/4)^6 = 1/4096`.

This is the load-bearing Casimir part of the proposed inward-mate transition.
It does not assert the still-open intertwiner/interface comparison, a raw-row
bound, a Poincare inequality, a completed gap, or a continuum/Clay result.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
import YMGap.Continuum.PlaquetteActivity

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

def oneSixteenth : Q' := Q'.mkPos 1 16 (by decide)
def oneQuarter : Q' := Q'.mkPos 1 4 (by decide)
def four : Q' := Q'.ofNat 4
def sixtyFour : Q' := Q'.ofNat 64
def oneOver4096 : Q' := Q'.mkPos 1 4096 (by decide)

/-- The parity-changing inward mate of an even label: `0 -> 1`, while every
positive label loses one unit. -/
def evenInwardMateLabel (spin : Nat) : Nat :=
  if spin = 0 then 1 else spin - 1

/-- The inward mate of a positive odd label is its predecessor. -/
def oddInwardMateLabel (spin : Nat) : Nat := spin - 1

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den, Q'.ofNat,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem mul_le_mul_both_local
    {a b A B : Q'}
    (ha : a <= A) (hb : b <= B)
    (hb0 : (0 : Q') <= b) (hA0 : (0 : Q') <= A) :
    a * b <= A * B :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ ha hb0)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hb hA0)

/-- At `w = 1/2`, every consecutive excited SU(2) heat coefficient loses at
least the factor `1/16`. -/
theorem coeffW_half_succ_le_sixteenth
    (spin : Nat) (hspin : 1 <= spin) :
    coeffW cutoffTwoHalfCoupling (spin + 1) <=
      oneSixteenth * coeffW cutoffTwoHalfCoupling spin := by
  have hratio := coeffW_succ_ratio
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) spin hspin
  have hrate :
      Q'.ofNat 2 * qpow cutoffTwoHalfCoupling 5 <= oneSixteenth := by
    unfold cutoffTwoHalfCoupling oneSixteenth
    decide
  exact Q'.le_trans' _ _ _ hratio
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
      (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) spin))

/-- Every positive label at `w = 1/2` is at most one quarter of its
predecessor's heat coefficient. -/
theorem coeffW_half_positive_le_quarter_pred
    (spin : Nat) (hspin : 0 < spin) :
    coeffW cutoffTwoHalfCoupling spin <=
      oneQuarter * coeffW cutoffTwoHalfCoupling (spin - 1) := by
  cases spin with
  | zero => omega
  | succ predecessor =>
      cases predecessor with
      | zero =>
          unfold cutoffTwoHalfCoupling oneQuarter coeffW dimQ c4 qpow
          decide
      | succ prior =>
          have hstep := coeffW_half_succ_le_sixteenth
            (prior + 1) (by omega)
          have hrate : oneSixteenth <= oneQuarter := by decide
          have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
            (coeffW_nonneg (w := cutoffTwoHalfCoupling)
              (by decide) (prior + 1))
          simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
            (Q'.le_trans' _ _ _ hstep hscale)

/-- A positive even label obtains the sharper `1/16` predecessor payment. -/
theorem coeffW_half_positive_even_le_sixteenth_mate
    (spin : Nat) (hspin : 0 < spin) (heven : spin % 2 = 0) :
    coeffW cutoffTwoHalfCoupling spin <=
      oneSixteenth *
        coeffW cutoffTwoHalfCoupling (evenInwardMateLabel spin) := by
  have htwo : 2 <= spin := by omega
  have hpred : 1 <= spin - 1 := by omega
  have hsplit : spin = (spin - 1) + 1 := by omega
  unfold evenInwardMateLabel
  rw [if_neg (Nat.ne_of_gt hspin)]
  rw [hsplit]
  exact coeffW_half_succ_le_sixteenth (spin - 1) hpred

/-- Every even label costs at most four times its inward mate; at zero this is
the exact vacuum/fundamental heat ratio, and away from zero the true bound is
much smaller. -/
theorem coeffW_half_even_le_four_mate
    (spin : Nat) (heven : spin % 2 = 0) :
    coeffW cutoffTwoHalfCoupling spin <=
      four * coeffW cutoffTwoHalfCoupling (evenInwardMateLabel spin) := by
  by_cases hzero : spin = 0
  · subst spin
    unfold cutoffTwoHalfCoupling four evenInwardMateLabel coeffW dimQ c4 qpow
    decide
  · have hpos : 0 < spin := Nat.pos_of_ne_zero hzero
    have hsharp := coeffW_half_positive_even_le_sixteenth_mate
      spin hpos heven
    have hrate : oneSixteenth <= four := by decide
    exact Q'.le_trans' _ _ _ hsharp
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
        (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide)
          (evenInwardMateLabel spin)))

/-- Every odd label is positive, so lowering it to its even predecessor costs
at most `1/4`. -/
theorem coeffW_half_odd_le_quarter_mate
    (spin : Nat) (hodd : spin % 2 = 1) :
    coeffW cutoffTwoHalfCoupling spin <=
      oneQuarter * coeffW cutoffTwoHalfCoupling (oddInwardMateLabel spin) := by
  have hpos : 0 < spin := by omega
  exact coeffW_half_positive_le_quarter_pred spin hpos

/-- Right-associated product of the six lower-cube face factors. -/
def sixHeatProduct (a b c d e f : Nat) : Q' :=
  coeffW cutoffTwoHalfCoupling a *
    (coeffW cutoffTwoHalfCoupling b *
      (coeffW cutoffTwoHalfCoupling c *
        (coeffW cutoffTwoHalfCoupling d *
          (coeffW cutoffTwoHalfCoupling e *
            coeffW cutoffTwoHalfCoupling f))))

private def sixQProduct (a b c d e f : Q') : Q' :=
  a * (b * (c * (d * (e * f))))

private theorem sixQProduct_pointwise_mul
    (a b c d e f A B C D E F : Q') :
    sixQProduct (a * A) (b * B) (c * C)
        (d * D) (e * E) (f * F) ≈
      sixQProduct a b c d e f * sixQProduct A B C D E F := by
  unfold sixQProduct
  q_ring

private theorem sixQProduct_nonnegative
    {a b c d e f : Q'}
    (ha : (0 : Q') <= a) (hb : (0 : Q') <= b)
    (hc : (0 : Q') <= c) (hd : (0 : Q') <= d)
    (he : (0 : Q') <= e) (hf : (0 : Q') <= f) :
    (0 : Q') <= sixQProduct a b c d e f := by
  unfold sixQProduct
  exact Q'.mul_nonneg _ _ ha
    (Q'.mul_nonneg _ _ hb
      (Q'.mul_nonneg _ _ hc
        (Q'.mul_nonneg _ _ hd (Q'.mul_nonneg _ _ he hf))))

private theorem sixQProduct_mono
    {a b c d e f A B C D E F : Q'}
    (ha : a <= A) (hb : b <= B) (hc : c <= C)
    (hd : d <= D) (he : e <= E) (hf : f <= F)
    (_ha0 : (0 : Q') <= a) (hb0 : (0 : Q') <= b)
    (hc0 : (0 : Q') <= c) (hd0 : (0 : Q') <= d)
    (he0 : (0 : Q') <= e) (hf0 : (0 : Q') <= f)
    (hA0 : (0 : Q') <= A) (hB0 : (0 : Q') <= B)
    (hC0 : (0 : Q') <= C) (hD0 : (0 : Q') <= D)
    (hE0 : (0 : Q') <= E) :
    sixQProduct a b c d e f <= sixQProduct A B C D E F := by
  unfold sixQProduct
  apply mul_le_mul_both_local ha
  · apply mul_le_mul_both_local hb
    · apply mul_le_mul_both_local hc
      · apply mul_le_mul_both_local hd
        · exact mul_le_mul_both_local he hf hf0 hE0
        · exact Q'.mul_nonneg _ _ he0 hf0
        · exact hD0
      · exact Q'.mul_nonneg _ _ hd0 (Q'.mul_nonneg _ _ he0 hf0)
      · exact hC0
    · exact Q'.mul_nonneg _ _ hc0
        (Q'.mul_nonneg _ _ hd0 (Q'.mul_nonneg _ _ he0 hf0))
    · exact hB0
  · exact Q'.mul_nonneg _ _ hb0
      (Q'.mul_nonneg _ _ hc0
        (Q'.mul_nonneg _ _ hd0 (Q'.mul_nonneg _ _ he0 hf0)))
  · exact hA0

private theorem sixQProduct_le_sixtyFour_of_one_sharp
    {a b c d e f A B C D E F : Q'}
    (ha : a <= four * A) (hb : b <= four * B)
    (hc : c <= four * C) (hd : d <= four * D)
    (he : e <= four * E) (hf : f <= four * F)
    (hsharp :
      a <= oneSixteenth * A ∨ b <= oneSixteenth * B ∨
      c <= oneSixteenth * C ∨ d <= oneSixteenth * D ∨
      e <= oneSixteenth * E ∨ f <= oneSixteenth * F)
    (ha0 : (0 : Q') <= a) (hb0 : (0 : Q') <= b)
    (hc0 : (0 : Q') <= c) (hd0 : (0 : Q') <= d)
    (he0 : (0 : Q') <= e) (hf0 : (0 : Q') <= f)
    (hA0 : (0 : Q') <= A) (hB0 : (0 : Q') <= B)
    (hC0 : (0 : Q') <= C) (hD0 : (0 : Q') <= D)
    (hE0 : (0 : Q') <= E) (_hF0 : (0 : Q') <= F) :
    sixQProduct a b c d e f <=
      sixtyFour * sixQProduct A B C D E F := by
  have hfour : (0 : Q') <= four := by decide
  have hsixteenth : (0 : Q') <= oneSixteenth := by decide
  rcases hsharp with hsa | hsb | hsc | hsd | hse | hsf
  · refine Q'.le_trans' _
      (sixQProduct (oneSixteenth * A) (four * B) (four * C)
        (four * D) (four * E) (four * F)) _ ?_ (Q'.le_of_eqv ?_)
    · exact sixQProduct_mono hsa hb hc hd he hf
        ha0 hb0 hc0 hd0 he0 hf0
        (Q'.mul_nonneg _ _ hsixteenth hA0)
        (Q'.mul_nonneg _ _ hfour hB0)
        (Q'.mul_nonneg _ _ hfour hC0)
        (Q'.mul_nonneg _ _ hfour hD0)
        (Q'.mul_nonneg _ _ hfour hE0)
    · exact Q'.eqv_trans _ _ _
        (sixQProduct_pointwise_mul
          oneSixteenth four four four four four A B C D E F)
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
  · refine Q'.le_trans' _
      (sixQProduct (four * A) (oneSixteenth * B) (four * C)
        (four * D) (four * E) (four * F)) _ ?_ (Q'.le_of_eqv ?_)
    · exact sixQProduct_mono ha hsb hc hd he hf
        ha0 hb0 hc0 hd0 he0 hf0
        (Q'.mul_nonneg _ _ hfour hA0)
        (Q'.mul_nonneg _ _ hsixteenth hB0)
        (Q'.mul_nonneg _ _ hfour hC0)
        (Q'.mul_nonneg _ _ hfour hD0)
        (Q'.mul_nonneg _ _ hfour hE0)
    · exact Q'.eqv_trans _ _ _
        (sixQProduct_pointwise_mul
          four oneSixteenth four four four four A B C D E F)
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
  · refine Q'.le_trans' _
      (sixQProduct (four * A) (four * B) (oneSixteenth * C)
        (four * D) (four * E) (four * F)) _ ?_ (Q'.le_of_eqv ?_)
    · exact sixQProduct_mono ha hb hsc hd he hf
        ha0 hb0 hc0 hd0 he0 hf0
        (Q'.mul_nonneg _ _ hfour hA0)
        (Q'.mul_nonneg _ _ hfour hB0)
        (Q'.mul_nonneg _ _ hsixteenth hC0)
        (Q'.mul_nonneg _ _ hfour hD0)
        (Q'.mul_nonneg _ _ hfour hE0)
    · exact Q'.eqv_trans _ _ _
        (sixQProduct_pointwise_mul
          four four oneSixteenth four four four A B C D E F)
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
  · refine Q'.le_trans' _
      (sixQProduct (four * A) (four * B) (four * C)
        (oneSixteenth * D) (four * E) (four * F)) _ ?_ (Q'.le_of_eqv ?_)
    · exact sixQProduct_mono ha hb hc hsd he hf
        ha0 hb0 hc0 hd0 he0 hf0
        (Q'.mul_nonneg _ _ hfour hA0)
        (Q'.mul_nonneg _ _ hfour hB0)
        (Q'.mul_nonneg _ _ hfour hC0)
        (Q'.mul_nonneg _ _ hsixteenth hD0)
        (Q'.mul_nonneg _ _ hfour hE0)
    · exact Q'.eqv_trans _ _ _
        (sixQProduct_pointwise_mul
          four four four oneSixteenth four four A B C D E F)
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
  · refine Q'.le_trans' _
      (sixQProduct (four * A) (four * B) (four * C)
        (four * D) (oneSixteenth * E) (four * F)) _ ?_ (Q'.le_of_eqv ?_)
    · exact sixQProduct_mono ha hb hc hd hse hf
        ha0 hb0 hc0 hd0 he0 hf0
        (Q'.mul_nonneg _ _ hfour hA0)
        (Q'.mul_nonneg _ _ hfour hB0)
        (Q'.mul_nonneg _ _ hfour hC0)
        (Q'.mul_nonneg _ _ hfour hD0)
        (Q'.mul_nonneg _ _ hsixteenth hE0)
    · exact Q'.eqv_trans _ _ _
        (sixQProduct_pointwise_mul
          four four four four oneSixteenth four A B C D E F)
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
  · refine Q'.le_trans' _
      (sixQProduct (four * A) (four * B) (four * C)
        (four * D) (four * E) (oneSixteenth * F)) _ ?_ (Q'.le_of_eqv ?_)
    · exact sixQProduct_mono ha hb hc hd he hsf
        ha0 hb0 hc0 hd0 he0 hf0
        (Q'.mul_nonneg _ _ hfour hA0)
        (Q'.mul_nonneg _ _ hfour hB0)
        (Q'.mul_nonneg _ _ hfour hC0)
        (Q'.mul_nonneg _ _ hfour hD0)
        (Q'.mul_nonneg _ _ hfour hE0)
    · exact Q'.eqv_trans _ _ _
        (sixQProduct_pointwise_mul
          four four four four four oneSixteenth A B C D E F)
        (Q'.mul_eqv_congr_right _ _ _ (by decide))

/-- **Non-vacuum even six-face heat payment.**  If all six cube labels are
even and at least one is positive, their physical `w = 1/2` heat product is
at most `64` times the heat product of the parity-changing inward mate. -/
theorem sixHeatProduct_evenInwardMate_le_sixtyFour
    (a b c d e f : Nat)
    (haEven : a % 2 = 0) (hbEven : b % 2 = 0)
    (hcEven : c % 2 = 0) (hdEven : d % 2 = 0)
    (heEven : e % 2 = 0) (hfEven : f % 2 = 0)
    (hnonvacuum : 0 < a ∨ 0 < b ∨ 0 < c ∨
      0 < d ∨ 0 < e ∨ 0 < f) :
    sixHeatProduct a b c d e f <=
      sixtyFour *
        sixHeatProduct
          (evenInwardMateLabel a) (evenInwardMateLabel b)
          (evenInwardMateLabel c) (evenInwardMateLabel d)
          (evenInwardMateLabel e) (evenInwardMateLabel f) := by
  unfold sixHeatProduct
  apply sixQProduct_le_sixtyFour_of_one_sharp
  · exact coeffW_half_even_le_four_mate a haEven
  · exact coeffW_half_even_le_four_mate b hbEven
  · exact coeffW_half_even_le_four_mate c hcEven
  · exact coeffW_half_even_le_four_mate d hdEven
  · exact coeffW_half_even_le_four_mate e heEven
  · exact coeffW_half_even_le_four_mate f hfEven
  · rcases hnonvacuum with ha | hb | hc | hd | he | hf
    · exact Or.inl (coeffW_half_positive_even_le_sixteenth_mate a ha haEven)
    · exact Or.inr (Or.inl
        (coeffW_half_positive_even_le_sixteenth_mate b hb hbEven))
    · exact Or.inr (Or.inr (Or.inl
        (coeffW_half_positive_even_le_sixteenth_mate c hc hcEven)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (coeffW_half_positive_even_le_sixteenth_mate d hd hdEven))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (coeffW_half_positive_even_le_sixteenth_mate e he heEven)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (coeffW_half_positive_even_le_sixteenth_mate f hf hfEven)))))
  all_goals exact coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) _

/-- **Odd six-face heat payment.**  If all six labels are odd, simultaneous
predecessor lowering gains the explicit factor `1/4096`. -/
theorem sixHeatProduct_oddInwardMate_le_oneOver4096
    (a b c d e f : Nat)
    (haOdd : a % 2 = 1) (hbOdd : b % 2 = 1)
    (hcOdd : c % 2 = 1) (hdOdd : d % 2 = 1)
    (heOdd : e % 2 = 1) (hfOdd : f % 2 = 1) :
    sixHeatProduct a b c d e f <=
      oneOver4096 *
        sixHeatProduct
          (oddInwardMateLabel a) (oddInwardMateLabel b)
          (oddInwardMateLabel c) (oddInwardMateLabel d)
          (oddInwardMateLabel e) (oddInwardMateLabel f) := by
  have hproduct := sixQProduct_mono
    (coeffW_half_odd_le_quarter_mate a haOdd)
    (coeffW_half_odd_le_quarter_mate b hbOdd)
    (coeffW_half_odd_le_quarter_mate c hcOdd)
    (coeffW_half_odd_le_quarter_mate d hdOdd)
    (coeffW_half_odd_le_quarter_mate e heOdd)
    (coeffW_half_odd_le_quarter_mate f hfOdd)
    (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) a)
    (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) b)
    (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) c)
    (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) d)
    (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) e)
    (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide) f)
    (Q'.mul_nonneg _ _ (by decide)
      (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide)
        (oddInwardMateLabel a)))
    (Q'.mul_nonneg _ _ (by decide)
      (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide)
        (oddInwardMateLabel b)))
    (Q'.mul_nonneg _ _ (by decide)
      (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide)
        (oddInwardMateLabel c)))
    (Q'.mul_nonneg _ _ (by decide)
      (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide)
        (oddInwardMateLabel d)))
    (Q'.mul_nonneg _ _ (by decide)
      (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide)
        (oddInwardMateLabel e)))
  unfold sixHeatProduct at hproduct ⊢
  refine Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv ?_)
  exact Q'.eqv_trans _ _ _
    (sixQProduct_pointwise_mul
      oneQuarter oneQuarter oneQuarter oneQuarter oneQuarter oneQuarter
      (coeffW cutoffTwoHalfCoupling (oddInwardMateLabel a))
      (coeffW cutoffTwoHalfCoupling (oddInwardMateLabel b))
      (coeffW cutoffTwoHalfCoupling (oddInwardMateLabel c))
      (coeffW cutoffTwoHalfCoupling (oddInwardMateLabel d))
      (coeffW cutoffTwoHalfCoupling (oddInwardMateLabel e))
      (coeffW cutoffTwoHalfCoupling (oddInwardMateLabel f)))
    (Q'.mul_eqv_congr_right _ _ _ (by decide))

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound.coeffW_half_succ_le_sixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound.sixHeatProduct_evenInwardMate_le_sixtyFour
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound.sixHeatProduct_oddInwardMate_le_oneOver4096
