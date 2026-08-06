/-
Track 11.7-fusion / R3k -- dyadic parity transport for the physical theta
half-contraction.

# Result

At the fine cutoff `N_(k+1)=2*N_k+1`, split the integer theta norm into its
even and odd nodes.  Let `E_k` be the even mass and let `C_k` be the adjacent
correlation inside that even subsequence.  Two local comparisons suffice:

    (w_k H_k) E_k <= I_k (C_k + delta_k E_k),
    I_(k+1) (E_k + C_k + delta_k E_k)
      <= 2 E_k (w_(k+1) H_(k+1)).

Here `delta_k=(1/360)8^(-k)` is an explicit shared debt.  It is essential:
the debt-free coarse comparison is false on the physical schedule.  The
first inequality bounds that small coarse-to-fourth-power correlation debt;
the second pays the same buffer from the fine bipartite-path reserve.  Exact
finite-sum pairing and positive cancellation compile them to

    2 I_k T_(k+1) <= T_k I_(k+1),

the existing normalized theta-deficit half-contraction.  Thus the remaining
global residual atom is replaced by two one-dimensional dyadic transport
atoms suitable for an Abel-prefix proof about computation.

# Constructivity

Primitive finite sums, exact `Q'` algebra, and positive-factor cancellation.
No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaDyadic

namespace YMGap.Continuum.P2BlockCompatibleThetaParityTransport

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaCross
open YMGap.Continuum.P2BlockCompatibleThetaDeficit
open YMGap.Continuum.P2BlockCompatibleThetaDyadic
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem parity_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "parity_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, parity_neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.neg_zero,
               Int.zero_add, Int.add_zero];
             ac_rfl))

private def twiceShiftL : RingNormaliser.PolyExpr :=
  .mul (.const 2) (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))

private def twiceShiftR : RingNormaliser.PolyExpr :=
  .add
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.neg (.mul (.const 2) (.mul (.var 0) (.var 2))))

private theorem twiceShift_normal :
    RingNormaliser.normalize twiceShiftL =
      RingNormaliser.normalize twiceShiftR := by decide

private theorem twice_shift_algebra (I0 I1 S1 : Q') :
    Q'.ofNat 2 * (I0 * (I1 + -S1)) ≈
      (I0 * I1 + I0 * I1) + -(Q'.ofNat 2 * (I0 * S1)) := by
  simpa [twiceShiftL, twiceShiftR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      twiceShiftL twiceShiftR twiceShift_normal
      (fun | 0 => I0 | 1 => I1 | _ => S1))

private def cancelShiftL : RingNormaliser.PolyExpr :=
  .add
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.neg
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 1))))

private def cancelShiftR : RingNormaliser.PolyExpr :=
  .mul (.add (.var 0) (.neg (.var 2))) (.var 1)

private theorem cancelShift_normal :
    RingNormaliser.normalize cancelShiftL =
      RingNormaliser.normalize cancelShiftR := by decide

private theorem cancel_shift_algebra (I0 I1 A0 : Q') :
    (I0 * I1 + I0 * I1) + -(I0 * I1 + A0 * I1) ≈
      (I0 + -A0) * I1 := by
  simpa [cancelShiftL, cancelShiftR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      cancelShiftL cancelShiftR cancelShift_normal
      (fun | 0 => I0 | 1 => I1 | _ => A0))

private theorem ofNat_pos_of_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact Q'.ofNat_succ_pos m

private theorem integerThetaTerm_pos_local {w : Q'}
    (hw : (0 : Q') < w) {n : Nat} (hn : 0 < n) :
    (0 : Q') < integerThetaTerm w n := by
  unfold integerThetaTerm
  exact Q'.mul_pos
    (ofNat_pos_of_pos_local (Nat.mul_pos hn hn))
    (qpow_pos (Q'.mul_pos hw hw) (n * n))

/-- Fine integer-theta mass on even nodes `2,4,...,2(N_k+1)`. -/
def blockFineEvenTheta (k : Nat) : Q' :=
  finSum
    (fun p => integerThetaTerm (blockWeight (k + 1)) (2 * p + 2))
    (blockNcut k + 1)

/-- Fine integer-theta mass on odd nodes `1,3,...,2N_k+1`. -/
def blockFineOddTheta (k : Nat) : Q' :=
  finSum
    (fun p => integerThetaTerm (blockWeight (k + 1)) (2 * p + 1))
    (blockNcut k + 1)

/-- Adjacent correlation internal to the even fine subsequence.  Under
`m=2n`, its exact rescaling is four times the theta correlation at weight
`w_(k+1)^4` and coarse cutoff `N_k`. -/
def blockFineEvenCross (k : Nat) : Q' :=
  let w4 := qpow (blockWeight (k + 1)) 4
  Q'.ofNat 4 * (w4 * halfThetaSum w4 (blockNcut k))

/-- Explicit schedule-sized buffer for the small coarse-to-fourth-power
correlation debt.  It is `(1/360) * 8^(-k)` because
`blockMargin k = (1/12) * 4^(-k)`. -/
def blockParityDebt (k : Nat) : Q' :=
  Q'.mkPos 1 30 (by decide) *
    (qpow YMGap.Constructive.HalfPow.half k * blockMargin k)

theorem blockParityDebt_nonneg (k : Nat) :
    (0 : Q') <= blockParityDebt k := by
  unfold blockParityDebt
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _
      (qpow_nonneg YMGap.Constructive.HalfPow.half (by decide) k)
      (blockMargin_nonneg k))

/-- The explicit debt buffer decays by exactly one eighth per block step. -/
theorem blockParityDebt_succ_eqv (k : Nat) :
    blockParityDebt (k + 1) ≈
      blockParityDebt k * Q'.mkPos 1 8 (by decide) := by
  let c := Q'.mkPos 1 30 (by decide)
  let h := YMGap.Constructive.HalfPow.half
  let e := Q'.mkPos 1 8 (by decide)
  have hm := blockMargin_succ_eqv k
  have hhe : h * blockQuarter ≈ e := by decide
  unfold blockParityDebt
  dsimp only [c, h, e] at hm hhe ⊢
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.mkPos 1 30 (by decide)) _ _
      (Q'.mul_eqv_congr_left
        (qpow YMGap.Constructive.HalfPow.half k *
          YMGap.Constructive.HalfPow.half) _ _ hm)) ?_
  refine Q'.eqv_trans _
    ((Q'.mkPos 1 30 (by decide) *
        (qpow YMGap.Constructive.HalfPow.half k * blockMargin k)) *
      (YMGap.Constructive.HalfPow.half * blockQuarter)) _
    (by parity_ring) ?_
  exact Q'.mul_eqv_congr_left _ _ _ hhe

private theorem evenThetaPower_eqv (w : Q') (n : Nat) :
    qpow (w * w) ((2 * n) * (2 * n)) ≈
      qpow ((qpow w 4) * (qpow w 4)) (n * n) := by
  let e := (2 * n) * (2 * n)
  let d := 4 * (n * n)
  have hed : e = d := by
    dsimp only [e, d]
    rw [show 4 = 2 * 2 by decide]
    ac_rfl
  have hleft : qpow (w * w) e ≈ qpow w (d + d) := by
    refine Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self w e) ?_
    rw [hed]
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_add w d d)
  have hright : qpow ((qpow w 4) * (qpow w 4)) (n * n) ≈
      qpow w (d + d) := by
    refine Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self (qpow w 4) (n * n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow (qpow w 4) (n * n))
        (HeatKernelRGStep.qpow_qpow w 4 (n * n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (qpow w (4 * (n * n))) _ _
        (HeatKernelRGStep.qpow_qpow w 4 (n * n))) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_add w d d)
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

/-- Even fine nodes are exactly four times the integer-theta summands at the
fourth-power fine weight. -/
theorem integerThetaTerm_even_eqv (w : Q') (n : Nat) :
    integerThetaTerm w (2 * n) ≈
      Q'.ofNat 4 * integerThetaTerm (qpow w 4) n := by
  unfold integerThetaTerm
  have hsq : (2 * n) * (2 * n) = 4 * (n * n) := by
    rw [show 4 = 2 * 2 by decide]
    ac_rfl
  have hcoeff : Q'.ofNat ((2 * n) * (2 * n)) ≈
      Q'.ofNat 4 * Q'.ofNat (n * n) := by
    rw [hsq]
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 4 (n * n))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hcoeff) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 4 * Q'.ofNat (n * n)) _ _
      (evenThetaPower_eqv w n)) ?_
  exact Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat (n * n)) _

/-- Exact coarse-cutoff reconstruction of the even fine mass. -/
theorem blockFineEvenTheta_eqv_four_integerTheta (k : Nat) :
    blockFineEvenTheta k ≈
      Q'.ofNat 4 *
        integerThetaSum (qpow (blockWeight (k + 1)) 4) (blockNcut k) := by
  unfold blockFineEvenTheta integerThetaSum
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun p => integerThetaTerm (blockWeight (k + 1)) (2 * p + 2))
      (fun p => Q'.ofNat 4 *
        integerThetaTerm (qpow (blockWeight (k + 1)) 4) (p + 1))
      (fun p => by
        simpa only [Nat.mul_add, Nat.mul_one] using
          (integerThetaTerm_even_eqv (blockWeight (k + 1)) (p + 1)))
      (blockNcut k + 1)) ?_
  exact Q'.eqv_symm
    (const_mul_finSum
      (fun p => integerThetaTerm
        (qpow (blockWeight (k + 1)) 4) (p + 1))
      (Q'.ofNat 4) (blockNcut k + 1))

private theorem evenFinSum_nonneg (w : Q') (hw : (0 : Q') < w) :
    forall L : Nat,
      (0 : Q') <=
        finSum (fun p => integerThetaTerm w (2 * p + 2)) L
  | 0 => Q'.le_refl' 0
  | L + 1 =>
      Q'.zero_le_add _ _ (evenFinSum_nonneg w hw L)
        (Q'.le_of_lt (integerThetaTerm_pos_local hw (by omega)))

/-- The even fine mass is a legitimate positive cancellation factor. -/
theorem blockFineEvenTheta_pos (k : Nat) :
    (0 : Q') < blockFineEvenTheta k := by
  unfold blockFineEvenTheta
  show (0 : Q') <
    finSum
        (fun p => integerThetaTerm (blockWeight (k + 1)) (2 * p + 2))
        (blockNcut k) +
      integerThetaTerm (blockWeight (k + 1)) (2 * blockNcut k + 2)
  have hprefix := evenFinSum_nonneg
    (blockWeight (k + 1)) (blockWeight_pos (k + 1)) (blockNcut k)
  have hterm : (0 : Q') <
      integerThetaTerm (blockWeight (k + 1)) (2 * blockNcut k + 2) :=
    integerThetaTerm_pos_local (blockWeight_pos (k + 1)) (by omega)
  exact Q'.pos_of_lt_of_le (Q'.pos_add_nonneg hterm hprefix)
    (Q'.ge_of_eqv (Q'.add_comm_eqv _ _))

/-- The fine theta norm is exactly its even-plus-odd parity partition. -/
theorem blockIntegerTheta_succ_eqv_even_add_odd (k : Nat) :
    blockIntegerTheta (k + 1) ≈
      blockFineEvenTheta k + blockFineOddTheta k := by
  unfold blockIntegerTheta
  rw [blockNcut_succ]
  refine Q'.eqv_trans _
    (finSum (integerThetaPair (blockWeight (k + 1)))
      (blockNcut k + 1)) _
    (integerThetaSum_doubleSucc_eqv
      (blockWeight (k + 1)) (blockNcut k)) ?_
  refine Q'.eqv_trans _
    (blockFineOddTheta k + blockFineEvenTheta k) _ ?_
    (Q'.add_comm_eqv _ _)
  simpa [integerThetaPair, blockFineEvenTheta, blockFineOddTheta] using
    (finSum_add
      (fun p => integerThetaTerm (blockWeight (k + 1)) (2 * p + 1))
      (fun p => integerThetaTerm (blockWeight (k + 1)) (2 * p + 2))
      (blockNcut k + 1))

/-- The two strictly local dyadic atoms replacing the global Pascal-residual
half-contraction. -/
structure BlockCompatibleP2DyadicParityTransport : Type where
  /-- At the same coarse cutoff, the physical coarse theta pair is bounded by
  the pair at the fourth power of the fine weight plus the explicit dyadic
  debt buffer.  Exact even-node rescaling below reconstructs the factor-four
  fine subsequence. -/
  coarseFourthPowerWithDebt : forall k, 4 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    (blockWeight k * blockHalfTheta k) *
        integerThetaSum w4 (blockNcut k) <=
      blockIntegerTheta k *
        (w4 * halfThetaSum w4 (blockNcut k) +
          blockParityDebt k * integerThetaSum w4 (blockNcut k))
  /-- The even/odd fine path subdivides with a factor-two reserve after paying
  the same explicit coarse-correlation debt. -/
  fineSubdivision : forall k, 4 <= k ->
    blockIntegerTheta (k + 1) *
        (blockFineEvenTheta k +
          (blockFineEvenCross k +
            blockParityDebt k * blockFineEvenTheta k)) <=
      Q'.ofNat 2 *
        (blockFineEvenTheta k *
          (blockWeight (k + 1) * blockHalfTheta (k + 1)))

/-- The same-cutoff fourth-power atom reconstructs coarse-to-even transport
with its explicit debt; the factor four is derived rather than left in the
frontier. -/
theorem BlockCompatibleP2DyadicParityTransport.coarseToEvenWithDebt
    (P : BlockCompatibleP2DyadicParityTransport) (k : Nat) (hk : 4 <= k) :
    (blockWeight k * blockHalfTheta k) * blockFineEvenTheta k <=
      blockIntegerTheta k *
        (blockFineEvenCross k +
          blockParityDebt k * blockFineEvenTheta k) := by
  let A0 := blockWeight k * blockHalfTheta k
  let I0 := blockIntegerTheta k
  let w4 := qpow (blockWeight (k + 1)) 4
  let J := integerThetaSum w4 (blockNcut k)
  let K := w4 * halfThetaSum w4 (blockNcut k)
  let E := blockFineEvenTheta k
  let C := blockFineEvenCross k
  let delta := blockParityDebt k
  let D := C + delta * E
  have hbase : A0 * J <= I0 * (K + delta * J) := by
    simpa only [A0, I0, w4, J, K, delta] using
      P.coarseFourthPowerWithDebt k hk
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (A0 * J) (I0 * (K + delta * J)) (Q'.ofNat 4) hbase (by decide)
  have hE : E ≈ Q'.ofNat 4 * J := by
    simpa only [E, J, w4] using
      blockFineEvenTheta_eqv_four_integerTheta k
  have hC : C ≈ Q'.ofNat 4 * K := by
    dsimp only [C, K, w4]
    unfold blockFineEvenCross
    exact Q'.eqv_refl _
  have hD : D ≈ Q'.ofNat 4 * (K + delta * J) := by
    dsimp only [D]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hC
        (Q'.mul_eqv_congr_left delta _ _ hE)) ?_
    parity_ring
  have hleft : A0 * E ≈ Q'.ofNat 4 * (A0 * J) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left A0 _ _ hE) ?_
    parity_ring
  have hright : Q'.ofNat 4 * (I0 * (K + delta * J)) ≈ I0 * D := by
    refine Q'.eqv_trans _ _ _ (by parity_ring :
      Q'.ofNat 4 * (I0 * (K + delta * J)) ≈
        I0 * (Q'.ofNat 4 * (K + delta * J))) ?_
    exact Q'.mul_eqv_congr_left I0 _ _ (Q'.eqv_symm hD)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- The dyadic parity atoms compile, without division, to the exact theta
half-contraction consumed by the physical `BlockingStep.Phi` bridge. -/
def BlockCompatibleP2DyadicParityTransport.toThetaDeficitHalfContraction
    (P : BlockCompatibleP2DyadicParityTransport) :
    BlockCompatibleP2ThetaDeficitHalfContraction where
  contraction := fun k hk => by
    let I0 := blockIntegerTheta k
    let I1 := blockIntegerTheta (k + 1)
    let A0 := blockWeight k * blockHalfTheta k
    let S1 := blockWeight (k + 1) * blockHalfTheta (k + 1)
    let E := blockFineEvenTheta k
    let C := blockFineEvenCross k
    let delta := blockParityDebt k
    let D := C + delta * E
    have hI0 : (0 : Q') <= I0 := by
      simpa only [I0] using blockIntegerTheta_nonneg k
    have hI1 : (0 : Q') <= I1 := by
      simpa only [I1] using blockIntegerTheta_nonneg (k + 1)
    have hE : (0 : Q') < E := by
      simpa only [E] using blockFineEvenTheta_pos k
    have hcoarse : A0 * E <= I0 * D := by
      simpa only [A0, E, I0, C, delta, D] using
        P.coarseToEvenWithDebt k hk
    have hfine : I1 * (E + D) <= Q'.ofNat 2 * (E * S1) := by
      simpa only [I1, E, C, delta, D, S1] using P.fineSubdivision k hk
    have hcoarseScaled := Q'.mul_le_mul_of_nonneg_right
      (A0 * E) (I0 * D) I1 hcoarse hI1
    have hadd := Q'.add_le_add_left (I0 * (E * I1)) _ _ hcoarseScaled
    have hfirst :
        E * (I0 * I1 + A0 * I1) <= I0 * (I1 * (E + D)) := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (by parity_ring :
          E * (I0 * I1 + A0 * I1) ≈
            I0 * (E * I1) + (A0 * E) * I1))
        (Q'.le_trans' _ _ _ hadd
          (Q'.le_of_eqv (by parity_ring :
            I0 * (E * I1) + (I0 * D) * I1 ≈
              I0 * (I1 * (E + D)))))
    have hfineScaled := Q'.mul_le_mul_of_nonneg_left
      (I1 * (E + D)) (Q'.ofNat 2 * (E * S1)) I0 hfine hI0
    have hfull :
        E * (I0 * I1 + A0 * I1) <= E * (Q'.ofNat 2 * (I0 * S1)) := by
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hfineScaled
          (Q'.le_of_eqv (by parity_ring :
            I0 * (Q'.ofNat 2 * (E * S1)) ≈
              E * (Q'.ofNat 2 * (I0 * S1)))))
    have hcore : I0 * I1 + A0 * I1 <= Q'.ofNat 2 * (I0 * S1) :=
      Q'.le_of_mul_le_mul_left hfull hE
    have hneg := Q'.neg_le_neg hcore
    have hshift := Q'.add_le_add_left (I0 * I1 + I0 * I1) _ _ hneg
    have hfinal :
        Q'.ofNat 2 * (I0 * (I1 + -S1)) <= (I0 + -A0) * I1 := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (twice_shift_algebra I0 I1 S1))
        (Q'.le_trans' _ _ _ hshift
          (Q'.le_of_eqv (cancel_shift_algebra I0 I1 A0)))
    simpa only [I0, I1, A0, S1, blockThetaDeficit] using hfinal

#print axioms blockFineEvenTheta_pos
#print axioms blockParityDebt_succ_eqv
#print axioms integerThetaTerm_even_eqv
#print axioms blockFineEvenTheta_eqv_four_integerTheta
#print axioms blockIntegerTheta_succ_eqv_even_add_odd
#print axioms BlockCompatibleP2DyadicParityTransport.coarseToEvenWithDebt
#print axioms BlockCompatibleP2DyadicParityTransport.toThetaDeficitHalfContraction

end YMGap.Continuum.P2BlockCompatibleThetaParityTransport
