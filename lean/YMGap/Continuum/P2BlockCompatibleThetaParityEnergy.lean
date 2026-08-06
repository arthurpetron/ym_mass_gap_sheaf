/-
Track 11.7-fusion / R3k -- deficit-energy normal form for dyadic parity
transport.

# Result

The two debt-corrected parity atoms are put into cancellation-preserving
deficit coordinates.  At the coarse cutoff, the fourth-power comparison is
equivalent to transporting the theta deficit.  At the fine cutoff, the
bipartite subdivision is equivalent to paying the full theta deficit from
the even-subsequence path energy.  The resulting atoms contain only positive
finite theta masses and additive deficits, so their next reduction can use
finite Abel prefixes and sums of squares without forming normalized
quotients.

# Constructivity

Exact `Q'` algebra and the proved finite-theta AM--GM inequality.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaParityTransport

namespace YMGap.Continuum.P2BlockCompatibleThetaParityEnergy

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaCross
open YMGap.Continuum.P2BlockCompatibleThetaDeficit
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private def scaleDeficitL : RingNormaliser.PolyExpr :=
  .add (.mul (.const 4) (.var 0)) (.neg (.mul (.const 4) (.var 1)))

private def scaleDeficitR : RingNormaliser.PolyExpr :=
  .mul (.const 4) (.add (.var 0) (.neg (.var 1)))

private theorem scaleDeficit_normal :
    RingNormaliser.normalize scaleDeficitL =
      RingNormaliser.normalize scaleDeficitR := by decide

private theorem scale_deficit_algebra (J K : Q') :
    Q'.ofNat 4 * J + -(Q'.ofNat 4 * K) ≈
      Q'.ofNat 4 * (J + -K) := by
  simpa [scaleDeficitL, scaleDeficitR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      scaleDeficitL scaleDeficitR scaleDeficit_normal
      (fun | 0 => J | _ => K))

private def coarseShift : RingNormaliser.PolyExpr :=
  .add
    (.add (.mul (.var 0) (.var 2))
      (.neg (.mul (.var 1) (.var 2))))
    (.mul (.var 1) (.var 3))

private def coarseShiftLeftL : RingNormaliser.PolyExpr :=
  .add coarseShift
    (.mul (.var 1) (.add (.var 2) (.neg (.var 3))))

private def coarseShiftLeftR : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.var 2)

private theorem coarseShiftLeft_normal :
    RingNormaliser.normalize coarseShiftLeftL =
      RingNormaliser.normalize coarseShiftLeftR := by decide

private theorem coarse_shift_left_algebra (A I J K : Q') :
    (((A * J + -(I * J)) + I * K) + I * (J + -K)) ≈ A * J := by
  simpa [coarseShift, coarseShiftLeftL, coarseShiftLeftR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      coarseShiftLeftL coarseShiftLeftR coarseShiftLeft_normal
      (fun | 0 => A | 1 => I | 2 => J | _ => K))

private def coarseShiftRightL : RingNormaliser.PolyExpr :=
  .add coarseShift
    (.add
      (.mul (.add (.var 1) (.neg (.var 0))) (.var 2))
      (.mul (.var 4) (.mul (.var 1) (.var 2))))

private def coarseShiftRightR : RingNormaliser.PolyExpr :=
  .mul (.var 1)
    (.add (.var 3) (.mul (.var 4) (.var 2)))

private theorem coarseShiftRight_normal :
    RingNormaliser.normalize coarseShiftRightL =
      RingNormaliser.normalize coarseShiftRightR := by decide

private theorem coarse_shift_right_algebra (A I J K delta : Q') :
    ((A * J + -(I * J)) + I * K) +
        ((I + -A) * J + delta * (I * J)) ≈
      I * (K + delta * J) := by
  simpa [coarseShift, coarseShiftRightL, coarseShiftRightR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      coarseShiftRightL coarseShiftRightR coarseShiftRight_normal
      (fun | 0 => A | 1 => I | 2 => J | 3 => K | _ => delta))

private def fineShift : RingNormaliser.PolyExpr :=
  .add
    (.add
      (.mul (.const 2) (.mul (.var 2) (.var 1)))
      (.neg (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.var 3))

private def fineShiftLeftL : RingNormaliser.PolyExpr :=
  .add fineShift
    (.add
      (.mul (.const 2)
        (.mul (.var 2) (.add (.var 0) (.neg (.var 1)))))
      (.mul (.var 4) (.mul (.var 0) (.var 2))))

private def fineShiftLeftR : RingNormaliser.PolyExpr :=
  .mul (.var 0)
    (.add (.var 2)
      (.add (.var 3) (.mul (.var 4) (.var 2))))

private theorem fineShiftLeft_normal :
    RingNormaliser.normalize fineShiftLeftL =
      RingNormaliser.normalize fineShiftLeftR := by decide

private theorem fine_shift_left_algebra (I S E C delta : Q') :
    ((Q'.ofNat 2 * (E * S) + -(I * E)) + I * C) +
        (Q'.ofNat 2 * (E * (I + -S)) + delta * (I * E)) ≈
      I * (E + (C + delta * E)) := by
  simpa [fineShift, fineShiftLeftL, fineShiftLeftR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      fineShiftLeftL fineShiftLeftR fineShiftLeft_normal
      (fun | 0 => I | 1 => S | 2 => E | 3 => C | _ => delta))

private def fineShiftRightL : RingNormaliser.PolyExpr :=
  .add fineShift
    (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))

private def fineShiftRightR : RingNormaliser.PolyExpr :=
  .mul (.const 2) (.mul (.var 2) (.var 1))

private theorem fineShiftRight_normal :
    RingNormaliser.normalize fineShiftRightL =
      RingNormaliser.normalize fineShiftRightR := by decide

private theorem fine_shift_right_algebra (I S E C : Q') :
    ((Q'.ofNat 2 * (E * S) + -(I * E)) + I * C) + I * (E + -C) ≈
      Q'.ofNat 2 * (E * S) := by
  simpa [fineShift, fineShiftRightL, fineShiftRightR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      fineShiftRightL fineShiftRightR fineShiftRight_normal
      (fun | 0 => I | 1 => S | 2 => E | _ => C))

/-- Theta deficit at the coarse cutoff but at the fourth power of the fine
weight. -/
def blockFourthThetaDeficit (k : Nat) : Q' :=
  let w4 := qpow (blockWeight (k + 1)) 4
  integerThetaSum w4 (blockNcut k) +
    -(w4 * halfThetaSum w4 (blockNcut k))

/-- Additive path energy of the fine even subsequence. -/
def blockFineEvenDeficit (k : Nat) : Q' :=
  blockFineEvenTheta k + -blockFineEvenCross k

theorem blockFourthThetaDeficit_nonneg (k : Nat) :
    (0 : Q') <= blockFourthThetaDeficit k := by
  let w4 := qpow (blockWeight (k + 1)) 4
  have hw4 : (0 : Q') <= w4 :=
    qpow_nonneg (blockWeight (k + 1)) (blockWeight_nonneg (k + 1)) 4
  unfold blockFourthThetaDeficit
  dsimp only [w4]
  exact Q'.sub_nonneg_of_le
    (halfTheta_le_integerTheta hw4 (blockNcut k))

/-- Exact rescaling of the even path energy to the fourth-power theta
deficit. -/
theorem blockFineEvenDeficit_eqv_four_fourthThetaDeficit (k : Nat) :
    blockFineEvenDeficit k ≈
      Q'.ofNat 4 * blockFourthThetaDeficit k := by
  let w4 := qpow (blockWeight (k + 1)) 4
  let J := integerThetaSum w4 (blockNcut k)
  let K := w4 * halfThetaSum w4 (blockNcut k)
  have hE : blockFineEvenTheta k ≈ Q'.ofNat 4 * J := by
    simpa only [J, w4] using
      blockFineEvenTheta_eqv_four_integerTheta k
  have hC : blockFineEvenCross k ≈ Q'.ofNat 4 * K := by
    dsimp only [K, w4]
    unfold blockFineEvenCross
    exact Q'.eqv_refl _
  unfold blockFineEvenDeficit blockFourthThetaDeficit
  dsimp only [w4, J, K]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hE (Q'.neg_eqv_congr _ _ hC)) ?_
  exact scale_deficit_algebra J K

theorem blockFineEvenDeficit_nonneg (k : Nat) :
    (0 : Q') <= blockFineEvenDeficit k := by
  have hscaled : (0 : Q') <=
      Q'.ofNat 4 * blockFourthThetaDeficit k :=
    Q'.mul_nonneg _ _ (by decide) (blockFourthThetaDeficit_nonneg k)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.ge_of_eqv (blockFineEvenDeficit_eqv_four_fourthThetaDeficit k))

/-- Deficit/energy form of the two local dyadic parity atoms.  No normalized
theta quotient occurs in either premise. -/
structure BlockCompatibleP2DyadicParityEnergyTransport : Type where
  /-- The fourth-power theta deficit is bounded by the physical coarse
  deficit plus the explicit geometric debt. -/
  coarseDeficitWithDebt : forall k, 4 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    blockIntegerTheta k * blockFourthThetaDeficit k <=
      blockThetaDeficit k * integerThetaSum w4 (blockNcut k) +
        blockParityDebt k *
          (blockIntegerTheta k * integerThetaSum w4 (blockNcut k))
  /-- The even-subsequence path energy pays twice the full fine deficit and
  the same debt. -/
  fineEvenEnergyReserve : forall k, 4 <= k ->
    Q'.ofNat 2 *
          (blockFineEvenTheta k * blockThetaDeficit (k + 1)) +
        blockParityDebt k *
          (blockIntegerTheta (k + 1) * blockFineEvenTheta k) <=
      blockIntegerTheta (k + 1) * blockFineEvenDeficit k

/-- Exact additive cancellation compiles the deficit/energy atoms back to
the debt-corrected correlation transport. -/
def BlockCompatibleP2DyadicParityEnergyTransport.toDyadicParityTransport
    (P : BlockCompatibleP2DyadicParityEnergyTransport) :
    BlockCompatibleP2DyadicParityTransport where
  coarseFourthPowerWithDebt := fun k hk => by
    let A := blockWeight k * blockHalfTheta k
    let I := blockIntegerTheta k
    let w4 := qpow (blockWeight (k + 1)) 4
    let J := integerThetaSum w4 (blockNcut k)
    let K := w4 * halfThetaSum w4 (blockNcut k)
    let delta := blockParityDebt k
    have hbase : I * (J + -K) <=
        (I + -A) * J + delta * (I * J) := by
      simpa only [I, A, J, K, w4, delta, blockFourthThetaDeficit,
        blockThetaDeficit] using P.coarseDeficitWithDebt k hk
    let X := (A * J + -(I * J)) + I * K
    have hshift := Q'.add_le_add_left X _ _ hbase
    have hleft : X + I * (J + -K) ≈ A * J := by
      dsimp only [X]
      exact coarse_shift_left_algebra A I J K
    have hright :
        X + ((I + -A) * J + delta * (I * J)) ≈
          I * (K + delta * J) := by
      dsimp only [X]
      exact coarse_shift_right_algebra A I J K delta
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
      (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))
  fineSubdivision := fun k hk => by
    let I := blockIntegerTheta (k + 1)
    let S := blockWeight (k + 1) * blockHalfTheta (k + 1)
    let E := blockFineEvenTheta k
    let C := blockFineEvenCross k
    let delta := blockParityDebt k
    have hbase :
        Q'.ofNat 2 * (E * (I + -S)) + delta * (I * E) <=
          I * (E + -C) := by
      simpa only [I, S, E, C, delta, blockThetaDeficit,
        blockFineEvenDeficit] using P.fineEvenEnergyReserve k hk
    let X := (Q'.ofNat 2 * (E * S) + -(I * E)) + I * C
    have hshift := Q'.add_le_add_left X _ _ hbase
    have hleft :
        X + (Q'.ofNat 2 * (E * (I + -S)) + delta * (I * E)) ≈
          I * (E + (C + delta * E)) := by
      dsimp only [X]
      exact fine_shift_left_algebra I S E C delta
    have hright : X + I * (E + -C) ≈ Q'.ofNat 2 * (E * S) := by
      dsimp only [X]
      exact fine_shift_right_algebra I S E C
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
      (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

#print axioms blockFourthThetaDeficit_nonneg
#print axioms blockFineEvenDeficit_eqv_four_fourthThetaDeficit
#print axioms blockFineEvenDeficit_nonneg
#print axioms BlockCompatibleP2DyadicParityEnergyTransport.toDyadicParityTransport

end YMGap.Continuum.P2BlockCompatibleThetaParityEnergy
