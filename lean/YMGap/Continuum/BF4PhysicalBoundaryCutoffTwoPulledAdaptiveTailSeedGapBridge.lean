/-
# An adaptive strict-gap tail seed for the cutoff-two physical carrier

The fixed `49/50` tail-seed bridge reserves the fixed relative error `1/200`.
That is useful when the finite seed already has the cutoff-two rate, but it is
unnecessarily rigid for a fresh finite seed found farther out in the cutoff
tail.  This module instead starts with any common finite seed rate

    0 <= q < 1

and spends one quarter of its actual slack:

    error(q) = (1/4) * (1 - q).

The moving-form perturbation then has rate

    q * (1 + error(q)) + error(q) < 1.

The proof is entirely order-theoretic over `Q'`: because `q <= 1`, the new
rate is at most `q + 2*error(q) = q + (1/2)*(1-q)`, which is strictly below
one.  Thus no summability from cutoff two to the tail is required.  The only
remaining analytic input is a strict finite gap at a cutoff already returned
by the verified moving-form tail modulus.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Spend one quarter of the actual finite-seed slack -/

/-- One quarter of `1-q`, represented using the already verified constructive
half.  This definition carries no proof argument, so its value is independent
of proof witnesses. -/
def cutoffTwoAdaptiveTailSeedRelativeError (q : Q') : Q' :=
  half * (half * ((1 : Q') + (-q)))

/-- The rate obtained after both the seed diagonal and matrix are perturbed by
the adaptive relative error. -/
def cutoffTwoAdaptiveTailSeedRate (q : Q') : Q' :=
  q * ((1 : Q') + cutoffTwoAdaptiveTailSeedRelativeError q) +
    cutoffTwoAdaptiveTailSeedRelativeError q

/-- Strict addition by a positive rational, proved directly from the stored
integer numerator and positive denominator. -/
private theorem lt_add_of_pos_right (a b : Q') (hb : (0 : Q') < b) :
    a < a + b := by
  show a.num * ((a + b).den : Int) < (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int)
      < (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  omega

private theorem add_neg_self_eqv (q : Q') : (q + (-q)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv q (-q)) (Q'.neg_add_self_eqv q)

private theorem add_slack_eqv_one (q : Q') :
    (q + ((1 : Q') + (-q))) ≈ 1 := by
  refine Q'.eqv_trans _ (q + ((-q) + 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left q _ _ (Q'.add_comm_eqv (1 : Q') (-q))
  refine Q'.eqv_trans _ ((q + (-q)) + 1) _
    (Q'.eqv_symm (Q'.add_assoc_eqv q (-q) 1)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + 1) _
    (Q'.add_eqv_congr_right _ _ 1 (add_neg_self_eqv q)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' 1)

theorem cutoffTwoAdaptiveTailSeedRelativeError_pos
    {q : Q'} (hq1 : q < (1 : Q')) :
    (0 : Q') < cutoffTwoAdaptiveTailSeedRelativeError q := by
  have hslack : (0 : Q') < (1 : Q') + (-q) :=
    YMGap.Continuum.ClusteringImpliesGap.sub_pos_of_lt hq1
  unfold cutoffTwoAdaptiveTailSeedRelativeError
  exact ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ hslack)

theorem cutoffTwoAdaptiveTailSeedRate_nonnegative
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) :
    (0 : Q') ≤ cutoffTwoAdaptiveTailSeedRate q := by
  have he0 : (0 : Q') ≤ cutoffTwoAdaptiveTailSeedRelativeError q :=
    Q'.le_of_lt (cutoffTwoAdaptiveTailSeedRelativeError_pos hq1)
  unfold cutoffTwoAdaptiveTailSeedRate
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ hq0 (Q'.zero_le_add _ _ (by decide) he0)) he0

/-- The central adaptive arithmetic: spending one quarter of the seed slack
leaves at least half of that slack after both perturbation contributions. -/
theorem cutoffTwoAdaptiveTailSeedRate_lt_one
    {q : Q'} (hq1 : q < (1 : Q')) :
    cutoffTwoAdaptiveTailSeedRate q < (1 : Q') := by
  let slack : Q' := (1 : Q') + (-q)
  let halfSlack : Q' := half * slack
  let error : Q' := cutoffTwoAdaptiveTailSeedRelativeError q
  have hslack : (0 : Q') < slack :=
    YMGap.Continuum.ClusteringImpliesGap.sub_pos_of_lt hq1
  have hhalfSlack : (0 : Q') < halfSlack := ExpNeg.half_mul_pos _ hslack
  have herror : (0 : Q') < error :=
    cutoffTwoAdaptiveTailSeedRelativeError_pos hq1
  have herror0 : (0 : Q') ≤ error := Q'.le_of_lt herror
  have hqle : q ≤ (1 : Q') := Q'.le_of_lt hq1
  have hqError : q * error ≤ error :=
    Q'.le_trans' _ ((1 : Q') * error) _
      (Q'.mul_le_mul_of_nonneg_right _ _ error hqle herror0)
      (Q'.le_of_eqv (Q'.one_mul_eqv error))
  have hinflation : q * ((1 : Q') + error) ≤ q + error := by
    refine Q'.le_trans' _ (q * 1 + q * error) _
      (Q'.le_of_eqv (Q'.mul_add_eqv q 1 error)) ?_
    refine Q'.le_trans' _ (q + q * error) _
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_right _ _ (q * error) (Q'.mul_one_eqv q))) ?_
    exact Q'.add_le_add_left q (q * error) error hqError
  have hrateLe : cutoffTwoAdaptiveTailSeedRate q ≤
      (q + error) + error := by
    unfold cutoffTwoAdaptiveTailSeedRate
    exact Q'.add_le_add_right _ _ error hinflation
  have herrorPair : (error + error) ≈ halfSlack := by
    unfold error cutoffTwoAdaptiveTailSeedRelativeError halfSlack
    exact ExpNeg.two_halves (half * slack)
  have hupperEqv : ((q + error) + error) ≈ q + halfSlack := by
    refine Q'.eqv_trans _ (q + (error + error)) _
      (Q'.add_assoc_eqv q error error) ?_
    exact Q'.add_eqv_congr_left q _ _ herrorPair
  have hhalfLtSlack : q + halfSlack < q + slack := by
    have hgrow : q + halfSlack < (q + halfSlack) + halfSlack :=
      lt_add_of_pos_right _ _ hhalfSlack
    have hdoubleEqv : ((q + halfSlack) + halfSlack) ≈ q + slack := by
      refine Q'.eqv_trans _ (q + (halfSlack + halfSlack)) _
        (Q'.add_assoc_eqv q halfSlack halfSlack) ?_
      exact Q'.add_eqv_congr_left q _ _ (ExpNeg.two_halves slack)
    exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      hgrow (Q'.le_of_eqv hdoubleEqv)
  have htoOne : q + halfSlack < (1 : Q') :=
    YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hhalfLtSlack
      (Q'.le_of_eqv (add_slack_eqv_one q))
  exact Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hrateLe (Q'.le_of_eqv hupperEqv)) htoOne

/-! ## 2. A finite strict seed aligned with its adaptive tail modulus -/

/-- At one coefficient, a finite strict gap with common rate `q` is located at
a start of the moving-form tail for the error determined by `q` itself. -/
structure CutoffTwoPulledAdaptiveTailSeedGapAt
    (q : Q') (coefficient : Nat → Q') : Type 1 where
  seed : Nat
  seed_ge_floor : cutoffTwoPulledRowFloorAnchor ≤ seed
  seed_gap :
    Q'.abs (cutoffTwoActualMovingMatrixAt seed coefficient) ≤
      q * cutoffTwoActualMovingDiagonalAt seed coefficient
  stability : ∀ later : Nat, seed ≤ later →
    Q'.abs
        (cutoffTwoActualMovingMatrixAt seed coefficient +
          (-cutoffTwoActualMovingMatrixAt later coefficient)) ≤
        cutoffTwoAdaptiveTailSeedRelativeError q *
          cutoffTwoActualMovingDiagonalAt later coefficient ∧
      Q'.abs
        (cutoffTwoActualMovingDiagonalAt seed coefficient +
          (-cutoffTwoActualMovingDiagonalAt later coefficient)) ≤
        cutoffTwoAdaptiveTailSeedRelativeError q *
          cutoffTwoActualMovingDiagonalAt later coefficient

/-- For every strict seed rate, the stability half of the adaptive seed
certificate has a constructive start.  The finite gap at that same start is
the remaining field. -/
theorem exists_cutoffTwoPulledAdaptiveTailStabilityStart
    (coefficient : Nat → Q') (q : Q') (hq1 : q < (1 : Q')) :
    ∃ seed : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ seed ∧
      ∀ later : Nat, seed ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt seed
                (cutoffTwoPulledMovingCenteredCoefficientAt seed coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            cutoffTwoAdaptiveTailSeedRelativeError q *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt seed
                (cutoffTwoPulledMovingCenteredCoefficientAt seed coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            cutoffTwoAdaptiveTailSeedRelativeError q *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  obtain ⟨seed, hfloor, htail⟩ :=
    movingForm_relative_errors_for_every_positive coefficient
      (cutoffTwoAdaptiveTailSeedRelativeError q)
      (cutoffTwoAdaptiveTailSeedRelativeError_pos hq1)
  exact ⟨seed, hfloor, fun later hlater =>
    htail seed later (Nat.le_refl _) hlater⟩

namespace CutoffTwoPulledAdaptiveTailSeedGapAt

private theorem diagonal_inflation
    {q : Q'} {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledAdaptiveTailSeedGapAt q coefficient)
    {later : Nat} (hlater : certificate.seed ≤ later) :
    cutoffTwoActualMovingDiagonalAt certificate.seed coefficient ≤
      ((1 : Q') + cutoffTwoAdaptiveTailSeedRelativeError q) *
        cutoffTwoActualMovingDiagonalAt later coefficient := by
  have herror := (certificate.stability later hlater).2
  have hadd := ExpNeg.le_add_of_abs_sub_le herror
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((1 : Q') * cutoffTwoActualMovingDiagonalAt later coefficient +
          cutoffTwoAdaptiveTailSeedRelativeError q *
            cutoffTwoActualMovingDiagonalAt later coefficient) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.one_mul_eqv _)))
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))))

/-- The finite seed gap propagates to every later cutoff at the strict rate
computed from its own slack. -/
theorem later_abs_gap
    {q : Q'} {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledAdaptiveTailSeedGapAt q coefficient)
    (hq0 : (0 : Q') ≤ q)
    (later : Nat) (hlater : certificate.seed ≤ later) :
    Q'.abs (cutoffTwoActualMovingMatrixAt later coefficient) ≤
      cutoffTwoAdaptiveTailSeedRate q *
        cutoffTwoActualMovingDiagonalAt later coefficient := by
  let seedMatrix := cutoffTwoActualMovingMatrixAt certificate.seed coefficient
  let laterMatrix := cutoffTwoActualMovingMatrixAt later coefficient
  let laterDiagonal := cutoffTwoActualMovingDiagonalAt later coefficient
  have hreverseTriangle := Q'.abs_le_abs_add_abs_sub
    laterMatrix seedMatrix
  have hcommuted : Q'.abs (laterMatrix + (-seedMatrix)) ≤
      cutoffTwoAdaptiveTailSeedRelativeError q * laterDiagonal := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          laterMatrix seedMatrix))
      (certificate.stability later hlater).1
  have hseedScaled : q *
      cutoffTwoActualMovingDiagonalAt certificate.seed coefficient ≤
      q * (((1 : Q') + cutoffTwoAdaptiveTailSeedRelativeError q) *
        laterDiagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (certificate.diagonal_inflation hlater) hq0
  have hsum : Q'.abs seedMatrix +
        Q'.abs (laterMatrix + (-seedMatrix)) ≤
      q * (((1 : Q') + cutoffTwoAdaptiveTailSeedRelativeError q) *
          laterDiagonal) +
        cutoffTwoAdaptiveTailSeedRelativeError q * laterDiagonal :=
    Q'.add_le_add
      (Q'.le_trans' _ _ _ certificate.seed_gap hseedScaled)
      hcommuted
  refine Q'.le_trans' _ _ _ hreverseTriangle
    (Q'.le_trans' _ _ _ hsum ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      ((q * ((1 : Q') + cutoffTwoAdaptiveTailSeedRelativeError q)) *
          laterDiagonal +
        cutoffTwoAdaptiveTailSeedRelativeError q * laterDiagonal) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv q
            ((1 : Q') + cutoffTwoAdaptiveTailSeedRelativeError q)
            laterDiagonal)))
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (q * ((1 : Q') + cutoffTwoAdaptiveTailSeedRelativeError q))
          (cutoffTwoAdaptiveTailSeedRelativeError q) laterDiagonal)))

/-! ## 3. Contraction to the same-object Bishop-real limit -/

/-- One adaptive tail seed is sufficient for the same coefficient's literal
moving matrix and diagonal Bishop-real limits to satisfy a strict rate. -/
theorem centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal
    {q : Q'} {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledAdaptiveTailSeedGapAt q coefficient)
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ' (cutoffTwoAdaptiveTailSeedRate q))
        (cutoffTwoMovingDiagonalLimit coefficient)) := by
  let matrix := cutoffTwoMovingMatrixLimit coefficient
  let diagonal := cutoffTwoMovingDiagonalLimit coefficient
  intro tolerance htolerance
  let delta := half * tolerance
  have hdelta : (0 : Q') < delta :=
    ExpNeg.half_mul_pos tolerance htolerance
  obtain ⟨matrixCutoff, hmatrix⟩ := matrix.cauchy delta hdelta
  obtain ⟨diagonalCutoff, hdiagonal⟩ := diagonal.cauchy delta hdelta
  let threshold := max matrixCutoff diagonalCutoff
  let anchor := max certificate.seed threshold
  have hseedAnchor : certificate.seed ≤ anchor := Nat.le_max_left _ _
  have hthresholdAnchor : threshold ≤ anchor := Nat.le_max_right _ _
  have hmatrixAnchor : matrixCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_left _ _) hthresholdAnchor
  have hdiagonalAnchor : diagonalCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_right _ _) hthresholdAnchor
  refine ⟨threshold, ?_⟩
  intro later hlater
  have hmatrixLater : matrixCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hdiagonalLater : diagonalCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  have hmatrixToAnchor : matrix.approx later ≤
      matrix.approx anchor + delta :=
    (hmatrix later anchor hmatrixLater hmatrixAnchor).1
  have hdiagonalFromAnchor : diagonal.approx anchor ≤
      diagonal.approx later + delta :=
    (hdiagonal anchor later hdiagonalAnchor hdiagonalLater).1
  have hanchorGap : matrix.approx anchor ≤
      cutoffTwoAdaptiveTailSeedRate q * diagonal.approx anchor := by
    refine Q'.le_trans' _ (Q'.abs (matrix.approx anchor)) _
      (Q'.le_abs_self _) ?_
    exact certificate.later_abs_gap hq0 anchor hseedAnchor
  have hrate0 : (0 : Q') ≤ cutoffTwoAdaptiveTailSeedRate q :=
    cutoffTwoAdaptiveTailSeedRate_nonnegative hq0 hq1
  have hrate1 : cutoffTwoAdaptiveTailSeedRate q < (1 : Q') :=
    cutoffTwoAdaptiveTailSeedRate_lt_one hq1
  have hscaledDiagonal :
      cutoffTwoAdaptiveTailSeedRate q * diagonal.approx anchor ≤
        cutoffTwoAdaptiveTailSeedRate q * (diagonal.approx later + delta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalFromAnchor hrate0
  have hscaleDelta : cutoffTwoAdaptiveTailSeedRate q * delta ≤ delta :=
    Q'.le_trans' _ ((1 : Q') * delta) _
      (Q'.mul_le_mul_of_nonneg_right _ _ delta
        (Q'.le_of_lt hrate1) (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  have herror : cutoffTwoAdaptiveTailSeedRate q * delta + delta ≤
      tolerance :=
    Q'.le_trans' _ (delta + delta) _
      (Q'.add_le_add_right _ _ delta hscaleDelta)
      (Q'.le_of_eqv (ExpNeg.two_halves tolerance))
  refine Q'.le_trans' _ _ _ hmatrixToAnchor ?_
  refine Q'.le_trans' _
    (cutoffTwoAdaptiveTailSeedRate q * diagonal.approx anchor + delta) _
    (Q'.add_le_add_right _ _ delta hanchorGap) ?_
  refine Q'.le_trans' _
    (cutoffTwoAdaptiveTailSeedRate q * (diagonal.approx later + delta) +
      delta) _
    (Q'.add_le_add_right _ _ delta hscaledDiagonal) ?_
  refine Q'.le_trans' _
    (cutoffTwoAdaptiveTailSeedRate q * diagonal.approx later +
      (cutoffTwoAdaptiveTailSeedRate q * delta + delta)) _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((cutoffTwoAdaptiveTailSeedRate q * diagonal.approx later +
            cutoffTwoAdaptiveTailSeedRate q * delta) + delta) _
        (Q'.add_eqv_congr_right _ _ delta
          (Q'.mul_add_eqv (cutoffTwoAdaptiveTailSeedRate q)
            (diagonal.approx later) delta))
        (Q'.add_assoc_eqv
          (cutoffTwoAdaptiveTailSeedRate q * diagonal.approx later)
          (cutoffTwoAdaptiveTailSeedRate q * delta) delta))) ?_
  exact Q'.add_le_add_left
    (cutoffTwoAdaptiveTailSeedRate q * diagonal.approx later)
    (cutoffTwoAdaptiveTailSeedRate q * delta + delta) tolerance herror

end CutoffTwoPulledAdaptiveTailSeedGapAt

/-! ## 4. The uniform finite-seed frontier -/

/-- A common strict finite rate `q` for every coefficient, with a possibly
coefficient-dependent seed cutoff already aligned to the adaptive tail. -/
structure CutoffTwoCoefficientwiseAdaptiveTailSeedGap (q : Q') : Type 1 where
  q_nonnegative : (0 : Q') ≤ q
  q_lt_one : q < (1 : Q')
  seedGapAt : ∀ coefficient : Nat → Q',
    CutoffTwoPulledAdaptiveTailSeedGapAt q coefficient

namespace CutoffTwoCoefficientwiseAdaptiveTailSeedGap

/-- The uniform finite adaptive seed family contracts to a uniform strict
same-object CReal form gap. -/
theorem centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal
    {q : Q'} (family : CutoffTwoCoefficientwiseAdaptiveTailSeedGap q)
    (coefficient : Nat → Q') :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ' (cutoffTwoAdaptiveTailSeedRate q))
        (cutoffTwoMovingDiagonalLimit coefficient)) :=
  CutoffTwoPulledAdaptiveTailSeedGapAt.centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal
    (family.seedGapAt coefficient) family.q_nonnegative family.q_lt_one

theorem adaptiveTailSeedRate_lt_one
    {q : Q'} (family : CutoffTwoCoefficientwiseAdaptiveTailSeedGap q) :
    cutoffTwoAdaptiveTailSeedRate q < (1 : Q') :=
  cutoffTwoAdaptiveTailSeedRate_lt_one
    family.q_lt_one

end CutoffTwoCoefficientwiseAdaptiveTailSeedGap

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.cutoffTwoAdaptiveTailSeedRelativeError_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.cutoffTwoAdaptiveTailSeedRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.cutoffTwoAdaptiveTailSeedRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.exists_cutoffTwoPulledAdaptiveTailStabilityStart
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.CutoffTwoPulledAdaptiveTailSeedGapAt.later_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.CutoffTwoPulledAdaptiveTailSeedGapAt.centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.CutoffTwoCoefficientwiseAdaptiveTailSeedGap.centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.CutoffTwoCoefficientwiseAdaptiveTailSeedGap.adaptiveTailSeedRate_lt_one
