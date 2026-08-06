/-
Track 11.7-fusion / R3k -- exact sum-of-squares normal form for the
block-compatible theta deficits.

# Result

Every finite theta deficit is exactly one half of a positive path energy:
the two endpoint squares plus the finite sum of adjacent difference squares.
The proof reuses the cutoff-uniform Dirichlet identity instead of expanding a
growing theta polynomial.  It then specializes the identity to the physical
coarse, fine, and fourth-power-even schedules.

# Constructivity

Finite sums, the existing constructive sum-of-squares theorem, and exact
`Q'` transport.  No `Classical`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.AllWindowCorrDirichlet
import YMGap.Continuum.P2BlockCompatibleThetaParityEnergy

namespace YMGap.Continuum.P2BlockCompatibleThetaPathEnergy

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaCross
open YMGap.Continuum.P2BlockCompatibleThetaDeficit
open YMGap.Continuum.P2BlockCompatibleThetaParityEnergy
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem qpow_two_eqv_mul (w : Q') :
    qpow w 2 ≈ w * w := by
  change ((1 : Q') * w) * w ≈ w * w
  exact Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)

/-- Positive endpoint-plus-Dirichlet carrier for a finite theta deficit. -/
def thetaPathEnergy (w : Q') (N : Nat) : Q' :=
  qpow w 2 *
    (coeffW w 0 * coeffW w 0 +
      coeffW w N * coeffW w N + dirichletEnergy w N)

theorem thetaPathEnergy_nonneg {w : Q'} (hw : (0 : Q') <= w) (N : Nat) :
    (0 : Q') <= thetaPathEnergy w N := by
  have hq : (0 : Q') <= qpow w 2 := qpow_nonneg w hw 2
  have h0 : (0 : Q') <= coeffW w 0 * coeffW w 0 :=
    q_mul_self_nonneg (coeffW w 0)
  have hN : (0 : Q') <= coeffW w N * coeffW w N :=
    q_mul_self_nonneg (coeffW w N)
  have hE : (0 : Q') <= dirichletEnergy w N :=
    dirichletEnergy_nonneg w N
  unfold thetaPathEnergy
  exact Q'.mul_nonneg _ _ hq
    (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ h0 hN) hE)

private theorem scaled_adjCorr_eqv_thetaSignal (w : Q') (N : Nat) :
    qpow w 2 * adjCorr w N ≈ w * halfThetaSum w N := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (adjCorr w N) (qpow_two_eqv_mul w)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv w w (adjCorr w N)) ?_
  exact Q'.mul_eqv_congr_left w _ _ (adjCorr_theta_eqv w N)

private theorem scaled_difference_eqv (q D A : Q') :
    q * D + -(q * A) ≈ q * (D + -A) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (q * D) _ _
      (Q'.eqv_symm (Q'.mul_neg_eqv q A))) ?_
  exact Q'.eqv_symm (Q'.mul_add_eqv q D (-A))

private theorem twice_scaled_eqv (q X : Q') :
    Q'.ofNat 2 * (q * X) ≈ q * (Q'.ofNat 2 * X) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) q X)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ X (Q'.mul_comm_eqv (Q'.ofNat 2) q)) ?_
  exact Q'.mul_assoc_eqv q (Q'.ofNat 2) X

/-- Exact proof-about-computation identity: the theta deficit is a finite
sum of squares with both moving-cutoff endpoint squares retained. -/
theorem twice_thetaDeficit_eqv_pathEnergy (w : Q') (N : Nat) :
    Q'.ofNat 2 *
        (integerThetaSum w N + -(w * halfThetaSum w N)) ≈
      thetaPathEnergy w N := by
  let q := qpow w 2
  let D := coordNormSq w N
  let A := adjCorr w N
  let I := integerThetaSum w N
  let S := w * halfThetaSum w N
  have hI : q * D ≈ I := by
    simpa only [q, D, I] using coordNormSq_theta_eqv w N
  have hS : q * A ≈ S := by
    simpa only [q, A, S] using scaled_adjCorr_eqv_thetaSignal w N
  have hinside : I + -S ≈ q * (D + -A) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_symm hI)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hS))) ?_
    exact scaled_difference_eqv q D A
  have hdir : Q'.ofNat 2 * (D + -A) ≈
      coeffW w 0 * coeffW w 0 +
        coeffW w N * coeffW w N + dirichletEnergy w N := by
    simpa only [D, A] using
      twice_norm_sub_corr_eq_boundary_dirichlet w N
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hinside) ?_
  refine Q'.eqv_trans _ _ _ (twice_scaled_eqv q (D + -A)) ?_
  unfold thetaPathEnergy
  dsimp only [q]
  exact Q'.mul_eqv_congr_left (qpow w 2) _ _ hdir

theorem twice_blockThetaDeficit_eqv_pathEnergy (k : Nat) :
    Q'.ofNat 2 * blockThetaDeficit k ≈
      thetaPathEnergy (blockWeight k) (blockNcut k) := by
  simpa only [blockThetaDeficit] using
    twice_thetaDeficit_eqv_pathEnergy (blockWeight k) (blockNcut k)

theorem twice_blockFourthThetaDeficit_eqv_pathEnergy (k : Nat) :
    let w4 := qpow (blockWeight (k + 1)) 4
    Q'.ofNat 2 * blockFourthThetaDeficit k ≈
      thetaPathEnergy w4 (blockNcut k) := by
  let w4 := qpow (blockWeight (k + 1)) 4
  simpa only [w4, blockFourthThetaDeficit] using
    twice_thetaDeficit_eqv_pathEnergy w4 (blockNcut k)

/-- The even-subsequence energy is exactly four copies of the
fourth-power path energy. -/
theorem twice_blockFineEvenDeficit_eqv_pathEnergy (k : Nat) :
    let w4 := qpow (blockWeight (k + 1)) 4
    Q'.ofNat 2 * blockFineEvenDeficit k ≈
      Q'.ofNat 4 * thetaPathEnergy w4 (blockNcut k) := by
  let w4 := qpow (blockWeight (k + 1)) 4
  have hscale := blockFineEvenDeficit_eqv_four_fourthThetaDeficit k
  have hpath := twice_blockFourthThetaDeficit_eqv_pathEnergy k
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hscale) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * (Q'.ofNat 2 * blockFourthThetaDeficit k)) _ ?_ ?_
  · exact twice_scaled_eqv (Q'.ofNat 4) (blockFourthThetaDeficit k)
  · exact Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _
      (by simpa only [w4] using hpath)

private def fineSandwichScaleL : RingNormaliser.PolyExpr :=
  .mul (.const 4)
    (.add
      (.mul (.const 2) (.mul (.var 1) (.var 2)))
      (.mul (.const 2) (.mul (.var 3) (.mul (.var 0) (.var 1)))))

private def fineSandwichScaleR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 2) (.mul (.mul (.const 4) (.var 1)) (.var 2)))
    (.mul (.const 2)
      (.mul (.var 3) (.mul (.var 0) (.mul (.const 4) (.var 1)))))

private theorem fineSandwichScale_normal :
    RingNormaliser.normalize fineSandwichScaleL =
      RingNormaliser.normalize fineSandwichScaleR := by decide

private theorem fine_sandwich_scale_algebra (I J P delta : Q') :
    Q'.ofNat 4 *
        (Q'.ofNat 2 * (J * P) +
          Q'.ofNat 2 * (delta * (I * J))) ≈
      Q'.ofNat 2 * ((Q'.ofNat 4 * J) * P) +
        Q'.ofNat 2 * (delta * (I * (Q'.ofNat 4 * J))) := by
  simpa [fineSandwichScaleL, fineSandwichScaleR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      fineSandwichScaleL fineSandwichScaleR fineSandwichScale_normal
      (fun | 0 => I | 1 => J | 2 => P | _ => delta))

private theorem four_mul_product_eqv_product_four (I P : Q') :
    Q'.ofNat 4 * (I * P) ≈ I * (Q'.ofNat 4 * P) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) I P)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ P (Q'.mul_comm_eqv (Q'.ofNat 4) I)) ?_
  exact Q'.mul_assoc_eqv I (Q'.ofNat 4) P

/-- Common-cutoff normalized-energy sandwich, stated division-free.  The
coarse side is the sharp debt comparison; the fine side has a much larger
bipartite reserve. -/
structure BlockCompatibleP2ThetaPathEnergySandwich : Type where
  coarseEnergyUpper : forall k, 4 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    blockIntegerTheta k * thetaPathEnergy w4 (blockNcut k) <=
      thetaPathEnergy (blockWeight k) (blockNcut k) *
          integerThetaSum w4 (blockNcut k) +
        Q'.ofNat 2 *
          (blockParityDebt k *
            (blockIntegerTheta k * integerThetaSum w4 (blockNcut k)))
  fineEnergyLower : forall k, 4 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    Q'.ofNat 2 *
          (integerThetaSum w4 (blockNcut k) *
            thetaPathEnergy (blockWeight (k + 1)) (blockNcut (k + 1))) +
        Q'.ofNat 2 *
          (blockParityDebt k *
            (blockIntegerTheta (k + 1) *
              integerThetaSum w4 (blockNcut k))) <=
      blockIntegerTheta (k + 1) * thetaPathEnergy w4 (blockNcut k)

/-- Fully explicit sum-of-squares frontier for the parity transport.  Both
premises compare positive finite path energies and positive theta masses;
there are no normalized correlations or hidden subtractions. -/
structure BlockCompatibleP2DyadicParityPathEnergyTransport : Type where
  coarsePathEnergyWithDebt : forall k, 4 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    blockIntegerTheta k * thetaPathEnergy w4 (blockNcut k) <=
      thetaPathEnergy (blockWeight k) (blockNcut k) *
          integerThetaSum w4 (blockNcut k) +
        Q'.ofNat 2 *
          (blockParityDebt k *
            (blockIntegerTheta k * integerThetaSum w4 (blockNcut k)))
  finePathEnergyReserve : forall k, 4 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    Q'.ofNat 2 *
          (blockFineEvenTheta k *
            thetaPathEnergy (blockWeight (k + 1)) (blockNcut (k + 1))) +
        Q'.ofNat 2 *
          (blockParityDebt k *
            (blockIntegerTheta (k + 1) * blockFineEvenTheta k)) <=
      blockIntegerTheta (k + 1) *
        (Q'.ofNat 4 * thetaPathEnergy w4 (blockNcut k))

/-- Exact even-node rescaling turns the common-cutoff energy sandwich into
the physical even-subsequence path-energy transport. -/
def BlockCompatibleP2ThetaPathEnergySandwich.toPathEnergyTransport
    (P : BlockCompatibleP2ThetaPathEnergySandwich) :
    BlockCompatibleP2DyadicParityPathEnergyTransport where
  coarsePathEnergyWithDebt := fun k hk => P.coarseEnergyUpper k hk
  finePathEnergyReserve := fun k hk => by
    let I := blockIntegerTheta (k + 1)
    let E := blockFineEvenTheta k
    let w4 := qpow (blockWeight (k + 1)) 4
    let J := integerThetaSum w4 (blockNcut k)
    let P1 := thetaPathEnergy
      (blockWeight (k + 1)) (blockNcut (k + 1))
    let P4 := thetaPathEnergy w4 (blockNcut k)
    let delta := blockParityDebt k
    have hE : E ≈ Q'.ofNat 4 * J := by
      simpa only [E, J, w4] using
        blockFineEvenTheta_eqv_four_integerTheta k
    have hbase :
        Q'.ofNat 2 * (J * P1) + Q'.ofNat 2 * (delta * (I * J)) <=
          I * P4 := by
      simpa only [I, J, P1, P4, delta, w4] using P.fineEnergyLower k hk
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4)
      hbase (by decide)
    have htargetLeft :
        Q'.ofNat 2 * (E * P1) + Q'.ofNat 2 * (delta * (I * E)) ≈
          Q'.ofNat 4 *
            (Q'.ofNat 2 * (J * P1) +
              Q'.ofNat 2 * (delta * (I * J))) := by
      refine Q'.eqv_trans _
        (Q'.ofNat 2 * ((Q'.ofNat 4 * J) * P1) +
          Q'.ofNat 2 * (delta * (I * (Q'.ofNat 4 * J)))) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
            (Q'.mul_eqv_congr_right _ _ P1 hE))
          (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
            (Q'.mul_eqv_congr_left delta _ _
              (Q'.mul_eqv_congr_left I _ _ hE)))
      · exact Q'.eqv_symm (fine_sandwich_scale_algebra I J P1 delta)
    have htargetRight : Q'.ofNat 4 * (I * P4) ≈
        I * (Q'.ofNat 4 * P4) :=
      four_mul_product_eqv_product_four I P4
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htargetLeft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv htargetRight))

/-- Scaling both additive deficit inequalities by two and substituting the
exact SOS identities compiles the path-energy frontier to the deficit-energy
frontier. -/
def BlockCompatibleP2DyadicParityPathEnergyTransport.toEnergyTransport
    (P : BlockCompatibleP2DyadicParityPathEnergyTransport) :
    BlockCompatibleP2DyadicParityEnergyTransport where
  coarseDeficitWithDebt := fun k hk => by
    let I := blockIntegerTheta k
    let J := integerThetaSum
      (qpow (blockWeight (k + 1)) 4) (blockNcut k)
    let T0 := blockThetaDeficit k
    let T4 := blockFourthThetaDeficit k
    let P0 := thetaPathEnergy (blockWeight k) (blockNcut k)
    let P4 := thetaPathEnergy
      (qpow (blockWeight (k + 1)) 4) (blockNcut k)
    let D := blockParityDebt k * (I * J)
    have hT0 : Q'.ofNat 2 * T0 ≈ P0 := by
      simpa only [T0, P0] using twice_blockThetaDeficit_eqv_pathEnergy k
    have hT4 : Q'.ofNat 2 * T4 ≈ P4 := by
      simpa only [T4, P4] using
        twice_blockFourthThetaDeficit_eqv_pathEnergy k
    have hpath : I * P4 <= P0 * J + Q'.ofNat 2 * D := by
      simpa only [I, J, P0, P4, D] using P.coarsePathEnergyWithDebt k hk
    have hleft : Q'.ofNat 2 * (I * T4) ≈ I * P4 := by
      refine Q'.eqv_trans _ _ _ (twice_scaled_eqv I T4) ?_
      exact Q'.mul_eqv_congr_left I _ _ hT4
    have hP0J : P0 * J ≈ Q'.ofNat 2 * (T0 * J) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ J (Q'.eqv_symm hT0)) ?_
      exact Q'.mul_assoc_eqv (Q'.ofNat 2) T0 J
    have hright : P0 * J + Q'.ofNat 2 * D ≈
        Q'.ofNat 2 * (T0 * J + D) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hP0J (Q'.eqv_refl _)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat 2) (T0 * J) D)
    have hscaled : Q'.ofNat 2 * (I * T4) <=
        Q'.ofNat 2 * (T0 * J + D) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hpath (Q'.le_of_eqv hright))
    exact Q'.le_of_mul_le_mul_left hscaled (by decide)
  fineEvenEnergyReserve := fun k hk => by
    let I := blockIntegerTheta (k + 1)
    let E := blockFineEvenTheta k
    let T1 := blockThetaDeficit (k + 1)
    let TE := blockFineEvenDeficit k
    let P1 := thetaPathEnergy
      (blockWeight (k + 1)) (blockNcut (k + 1))
    let P4 := thetaPathEnergy
      (qpow (blockWeight (k + 1)) 4) (blockNcut k)
    let D := blockParityDebt k * (I * E)
    have hT1 : Q'.ofNat 2 * T1 ≈ P1 := by
      simpa only [T1, P1] using
        twice_blockThetaDeficit_eqv_pathEnergy (k + 1)
    have hTE : Q'.ofNat 2 * TE ≈ Q'.ofNat 4 * P4 := by
      simpa only [TE, P4] using
        twice_blockFineEvenDeficit_eqv_pathEnergy k
    have hpath :
        Q'.ofNat 2 * (E * P1) + Q'.ofNat 2 * D <=
          I * (Q'.ofNat 4 * P4) := by
      simpa only [I, E, P1, P4, D] using P.finePathEnergyReserve k hk
    have hET : Q'.ofNat 2 * (E * T1) ≈ E * P1 := by
      refine Q'.eqv_trans _ _ _ (twice_scaled_eqv E T1) ?_
      exact Q'.mul_eqv_congr_left E _ _ hT1
    have hleft :
        Q'.ofNat 2 * (Q'.ofNat 2 * (E * T1) + D) ≈
          Q'.ofNat 2 * (E * P1) + Q'.ofNat 2 * D := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (Q'.ofNat 2) (Q'.ofNat 2 * (E * T1)) D) ?_
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hET)
        (Q'.eqv_refl _)
    have hright : Q'.ofNat 2 * (I * TE) ≈
        I * (Q'.ofNat 4 * P4) := by
      refine Q'.eqv_trans _ _ _ (twice_scaled_eqv I TE) ?_
      exact Q'.mul_eqv_congr_left I _ _ hTE
    have hscaled :
        Q'.ofNat 2 * (Q'.ofNat 2 * (E * T1) + D) <=
          Q'.ofNat 2 * (I * TE) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hpath (Q'.le_of_eqv (Q'.eqv_symm hright)))
    exact Q'.le_of_mul_le_mul_left hscaled (by decide)

#print axioms thetaPathEnergy_nonneg
#print axioms twice_thetaDeficit_eqv_pathEnergy
#print axioms twice_blockThetaDeficit_eqv_pathEnergy
#print axioms twice_blockFourthThetaDeficit_eqv_pathEnergy
#print axioms twice_blockFineEvenDeficit_eqv_pathEnergy
#print axioms BlockCompatibleP2ThetaPathEnergySandwich.toPathEnergyTransport
#print axioms BlockCompatibleP2DyadicParityPathEnergyTransport.toEnergyTransport

end YMGap.Continuum.P2BlockCompatibleThetaPathEnergy
