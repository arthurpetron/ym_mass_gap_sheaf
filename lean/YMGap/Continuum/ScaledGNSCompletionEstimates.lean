/-
# Quantitative norm estimates on the existing normalized GNS completion

Cauchy--Schwarz, the quadratic triangle inequality, and the original dense
approximation modulus survive the same positive normalization. Norm ceilings
are computed from supplied Cauchy representatives, not selected from quotient
points. These estimates are for the existing completion and pairing.
-/

import YMGap.Continuum.ScaledGNSCompletion
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.ScaledGNSCompletionEstimates

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletion

variable (D : GNSData) (N : Normalization)

local notation "S" => scaledSeminorm D N
local notation "B" => scaledCompletedInner D N
local notation "lambda" => Quotient.mk CReal.crealSetoid N.value

def scaledSub (x y : (S).Completion) : (S).Completion :=
  toScaledCompletion D N (D.cSub (toRawCompletion D N x) (toRawCompletion D N y))

theorem mul_mono_left {f a b : RC} (hf : RCnonneg f) (h : RCle a b) :
    RCle (RCmul f a) (RCmul f b) := by
  refine Quotient.inductionOn₃ f a b ?_ hf h
  intro repF repA repB hF hAB
  exact CReal.leEv_mul_nonneg_left hF hAB

theorem mul_mono_right {f a b : RC} (hf : RCnonneg f) (h : RCle a b) :
    RCle (RCmul a f) (RCmul b f) := by
  rw [RCmul_comm a f, RCmul_comm b f]
  exact mul_mono_left hf h

theorem mul_add (a b c : RC) :
    RCmul (RCadd a b) c = RCadd (RCmul a c) (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro repA repB repC
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.add_mul_eqv _ _ _))

theorem product_shuffle (a b c : RC) :
    RCmul (RCmul a c) (RCmul b c) = RCmul (RCmul c c) (RCmul a b) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro repA repB repC
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv ((repA.approx n * repC.approx n) * (repB.approx n * repC.approx n))
    ((repC.approx n * repC.approx n) * (repA.approx n * repB.approx n))
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

theorem square_nonnegative (a : RC) : RCnonneg (RCmul a a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact CReal.leEv_ofQ'_of_approx_ge (fun n => SumOfSquares.q_mul_self_nonneg (A.approx n))

theorem normalization_nonnegative : RCnonneg lambda :=
  CReal.leEv_ofQ'_of_approx_ge (fun n => Q'.le_trans' _ _ _ (Q'.le_of_lt N.floor_pos) (N.lower n))

theorem scaledInner_nonnegative (x : (S).Completion) : RCnonneg (B x x) := by
  have hmul (a b : RC) (ha : RCnonneg a) (hb : RCnonneg b) : RCnonneg (RCmul a b) := by
    refine Quotient.inductionOn₂ a b ?_ ha hb
    intro repA repB hA hB
    exact CReal.mul_nonneg hA hB
  exact hmul _ _ (D.cinner_self_nonneg (toRawCompletion D N x)) (normalization_nonnegative N)

theorem scaledInner_cauchySchwarz (x y : (S).Completion) :
    RCle (RCmul (B x y) (B x y)) (RCmul (B x x) (B y y)) := by
  unfold scaledCompletedInner
  rw [product_shuffle, product_shuffle]
  exact mul_mono_left (square_nonnegative lambda)
    (D.RC_cauchy_schwarz (toRawCompletion D N x) (toRawCompletion D N y))

private theorem raw_triangle (x y z : GNSCompletionSpace D) :
    RCle (D.cinnerCompl (D.cSub x z) (D.cSub x z))
      (RCadd
        (RCadd (D.cinnerCompl (D.cSub x y) (D.cSub x y)) (D.cinnerCompl (D.cSub x y) (D.cSub x y)))
        (RCadd (D.cinnerCompl (D.cSub y z) (D.cSub y z)) (D.cinnerCompl (D.cSub y z) (D.cSub y z)))) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Z))
    (CReal.convergesTo_add
      (CReal.convergesTo_add (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y))
        (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y)))
      (CReal.convergesTo_add (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy Y Z))
        (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy Y Z))))
    (fun n => CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (D.distSqQ_triangle (X.seq n) (Y.seq n) (Z.seq n))))

theorem scaledInner_triangle (x y z : (S).Completion) :
    RCle (B (scaledSub D N x z) (scaledSub D N x z))
      (RCadd
        (RCadd (B (scaledSub D N x y) (scaledSub D N x y)) (B (scaledSub D N x y) (scaledSub D N x y)))
        (RCadd (B (scaledSub D N y z) (scaledSub D N y z)) (B (scaledSub D N y z) (scaledSub D N y z)))) := by
  unfold scaledCompletedInner scaledSub
  simp only [raw_scaled_inverse]
  have h := mul_mono_right (normalization_nonnegative N)
    (raw_triangle D (toRawCompletion D N x) (toRawCompletion D N y) (toRawCompletion D N z))
  rw [mul_add, mul_add, mul_add] at h
  exact h

/-- The bound is computed from this supplied representative, not its quotient. -/
theorem scaledInner_normCeil (X : CauchyGNS D) :
    RCle (B (toScaledCompletion D N (Quotient.mk (cauchySetoid D) X))
      (toScaledCompletion D N (Quotient.mk (cauchySetoid D) X)))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' (Q'.ofNat (D.normCeil X)))) := by
  rw [scaledCompletedInner_comparison]
  intro epsilon hepsilon
  refine ⟨D.normBase X, fun n hn => ?_⟩
  let i := CReal.QMhat (D.cInnerSeq X X) (D.cInnerQCauchy X X) n
  have hb := D.normCeil_bound X i (Nat.le_trans hn (CReal.self_le_QMhat _ _ n))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (D.B (X.seq i) (X.seq i))
    (N.upper n) (D.self_nonneg _)
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ hb (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))))

/-- Original squared-distance modulus, with no normalization loss. -/
theorem scaledInner_approximation (X : CauchyGNS D) (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : X.modulus epsilon ≤ n) :
    RCle (B (scaledSub D N ((S).embedRep (X.seq n)) (toScaledCompletion D N (Quotient.mk (cauchySetoid D) X)))
      (scaledSub D N ((S).embedRep (X.seq n)) (toScaledCompletion D N (Quotient.mk (cauchySetoid D) X))))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' epsilon)) := by
  unfold scaledCompletedInner scaledSub
  rw [raw_scaled_inverse, toRawCompletion_embed, raw_scaled_inverse]
  intro delta hdelta
  refine ⟨X.modulus epsilon, fun k hk => ?_⟩
  let U := constCauchy D (X.seq n)
  let i := CReal.QMhat (fun m => D.distSqQ (U.seq m) (X.seq m)) (D.distSqSeqCauchy U X) k
  have hb := X.isCauchy epsilon hepsilon n i hn (Nat.le_trans hk (CReal.self_le_QMhat _ _ k))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (D.distSqQ (X.seq n) (X.seq i))
    (N.upper k) (D.self_nonneg _)
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ hb (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hdelta))))

end YMGap.Continuum.ScaledGNSCompletionEstimates

#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.scaledSub
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.mul_mono_left
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.mul_mono_right
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.mul_add
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.product_shuffle
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.square_nonnegative
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.normalization_nonnegative
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.scaledInner_nonnegative
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.scaledInner_cauchySchwarz
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.scaledInner_triangle
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.scaledInner_normCeil
#print axioms YMGap.Continuum.ScaledGNSCompletionEstimates.scaledInner_approximation
