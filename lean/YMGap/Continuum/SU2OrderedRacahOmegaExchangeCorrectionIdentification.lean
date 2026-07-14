/-
# Specializing the one-Omega commutator to a right channel

The boundary-aware polynomial commutator is now substituted into the actual
positive-inner-order `triRight` recurrence.  This produces the exact raw
induction step: first-pair exchange of the original channel is reduced to
first-pair exchange at labels `(b-1,c-1)` plus the concrete four-term
commutator correction.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution

namespace YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_mul_eqv (u v : Nat) :
    Q'.ofNat (u * v) ≈ Q'.ofNat u * Q'.ofNat v := by
  show (u * v : Int) *
      ((Q'.ofNat u * Q'.ofNat v).den : Int) =
    (Q'.ofNat u * Q'.ofNat v).num * (1 : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one]

/-- Coefficient array of the channel obtained by peeling one positive inner
contraction. -/
def peeledRightCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) :
    Nat → Nat → Nat → Q' := fun i j l =>
  triRight a (b - 1) (c - 1) d q.intermediate
    (mono i) (mono j) (mono l) s

/-- The split one-Omega lift is exactly the original positive-inner-order
right channel, including all truncated-natural source coordinates. -/
theorem peeled_omegaLiftSplit_eq_triRight {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l s : Nat) :
    omegaLiftSplit b c (peeledRightCoefficient q s) i j l ≈
      triRight a b c d q.intermediate
        (mono i) (mono j) (mono l) s := by
  have hred := triRight_positive_inner_reduction q hp i j l s
  have h0 := ofNat_mul_eqv j (c - l)
  have h1 := ofNat_mul_eqv (b - j) l
  let X := peeledRightCoefficient q s i j (l - 1)
  have hneg :
      (-(Q'.ofNat ((b - j) * l))) * X ≈
        -((Q'.ofNat (b - j) * Q'.ofNat l) * X) := by
    refine Q'.eqv_trans _ (-(Q'.ofNat ((b - j) * l) * X)) _
      (Q'.neg_mul_eqv _ _) ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ X h1)
  have hsplit :
      Q'.ofNat (j * (c - l)) *
            peeledRightCoefficient q s i (j - 1) l +
          (-(Q'.ofNat ((b - j) * l))) *
            peeledRightCoefficient q s i j (l - 1) ≈
        omegaLiftSplit b c (peeledRightCoefficient q s) i j l := by
    unfold omegaLiftSplit
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ h0)
      (by simpa only [X] using hneg)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsplit)
    (Q'.eqv_symm (by
      simpa only [peeledRightCoefficient] using hred))

private theorem firstPairExchange3_congr (a b : Nat)
    (x y : Nat → Nat → Nat → Q')
    (hxy : ∀ i j l, x i j l ≈ y i j l) (i j l : Nat) :
    firstPairExchange3 a b x i j l ≈
      firstPairExchange3 a b y i j l := by
  unfold firstPairExchange3 pairExchange
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (hxy (i + 1) (j - 1) l)
        (Q'.neg_eqv_congr _ _ (hxy i j l))))
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (hxy (i - 1) (j + 1) l)
        (Q'.neg_eqv_congr _ _ (hxy i j l))))

/-- The four-term correction specialized to the peeled right channel. -/
def triRightOmegaCorrection {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat) : Q' :=
  omegaExchangeCorrection a b c (peeledRightCoefficient q s) i j l

/-- **Exact positive-order raw induction step.**  The raw first-pair
exchange of a right channel is the Omega lift of the reduced-label exchange,
plus the specialized four-term correction.  This statement is valid on the
entire physical second-coordinate interval, including both faces. -/
theorem triRight_firstPairExchange_induction_step {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l s : Nat) (hj : j ≤ b) :
    firstPairExchange3 a b
        (fun u v w => triRight a b c d q.intermediate
          (mono u) (mono v) (mono w) s) i j l ≈
      omegaLiftSplit b c
          (firstPairExchange3 a (b - 1)
            (peeledRightCoefficient q s)) i j l +
        triRightOmegaCorrection q i j l s := by
  let lifted := omegaLiftSplit b c (peeledRightCoefficient q s)
  let original : Nat → Nat → Nat → Q' := fun u v w =>
    triRight a b c d q.intermediate (mono u) (mono v) (mono w) s
  have hlift : ∀ u v w, lifted u v w ≈ original u v w := by
    intro u v w
    simpa only [lifted, original] using
      peeled_omegaLiftSplit_eq_triRight q hp u v w s
  have hleft := firstPairExchange3_congr a b original lifted
    (fun u v w => Q'.eqv_symm (hlift u v w)) i j l
  have hcomm := firstPairExchange3_omegaLiftSplit
    (a := a) (b := b) (c := c) (i := i) (j := j) (l := l)
    (peeledRightCoefficient q s) hj
  exact Q'.eqv_trans _ _ _
    (by simpa only [original, lifted] using hleft)
    (by simpa only [lifted, triRightOmegaCorrection] using hcomm)

/-! ## A normalization fence for the correction carrier -/

/-- The middle channel in the smallest three-channel block. -/
def correctionFenceMiddle : FixedRightCGChannel 2 2 2 2 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

/-- Its lower adjacent channel. -/
def correctionFenceLower : FixedRightCGChannel 2 2 2 2 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

/-- Its upper adjacent channel. -/
def correctionFenceUpper : FixedRightCGChannel 2 2 2 2 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

/-- In the smallest interior block, the correction has a nonzero coordinate
where the upper adjacent carrier vanishes. -/
theorem correctionFence_value :
    triRightOmegaCorrection correctionFenceMiddle 0 2 1 1 ≈
      Q'.ofNat 16 := by
  decide

theorem correctionFence_upper_value :
    triRight 2 2 2 2 correctionFenceUpper.intermediate
        (mono 0) (mono 2) (mono 1) 1 ≈ 0 := by
  decide

/-- **Single-carrier normalization fence.**  The four-term correction is not
a scalar multiple of the upper adjacent channel, even in the smallest
interior block.  Thus a claimed direct identification with only that carrier
is false; a correct general theorem must retain the full tridiagonal
combination. -/
theorem correction_not_scalar_upper_adjacent (z : Q') :
    ¬ (triRightOmegaCorrection correctionFenceMiddle 0 2 1 1 ≈
      z * triRight 2 2 2 2 correctionFenceUpper.intermediate
        (mono 0) (mono 2) (mono 1) 1) := by
  intro h
  have hz :
      z * triRight 2 2 2 2 correctionFenceUpper.intermediate
          (mono 0) (mono 2) (mono 1) 1 ≈ 0 :=
    Q'.eqv_trans _ (z * 0) _
      (Q'.mul_eqv_congr_left z _ _ correctionFence_upper_value)
      (Q'.mul_zero_eqv z)
  have hc0 : triRightOmegaCorrection correctionFenceMiddle 0 2 1 1 ≈ 0 :=
    Q'.eqv_trans _ _ _ h hz
  have h160 : Q'.ofNat 16 ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm correctionFence_value) hc0
  exact (by decide : ¬ (Q'.ofNat 16 ≈ 0)) h160

/-- The same block exposes the correct mechanism: the correction has all
three right-channel components.  This finite exact identity is a
normalization fence and scouting datum, not the still-required all-label
contiguous theorem. -/
theorem correctionFence_three_channel_identity :
    ∀ i, i < 3 → ∀ j, j < 3 → ∀ l, l < 3 → ∀ s, s < 3 →
      Q'.ofNat 3 * triRightOmegaCorrection correctionFenceMiddle i j l s ≈
        Q'.ofNat 2 *
            triRight 2 2 2 2 correctionFenceLower.intermediate
              (mono i) (mono j) (mono l) s +
          (-(Q'.ofNat 3 *
            triRight 2 2 2 2 correctionFenceMiddle.intermediate
              (mono i) (mono j) (mono l) s)) +
          Q'.ofNat 4 *
            triRight 2 2 2 2 correctionFenceUpper.intermediate
              (mono i) (mono j) (mono l) s := by
  decide

end YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification.peeled_omegaLiftSplit_eq_triRight
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification.triRight_firstPairExchange_induction_step
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification.correction_not_scalar_upper_adjacent
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification.correctionFence_three_channel_identity
