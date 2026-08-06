/-
Track 11.7-fusion / R3k -- sharp trapezoid/terminal compiler for the
block-compatible common-cutoff theta drift.

# Result

The cancellation-preserving covariance from
`P2BlockCompatibleThetaDriftCross` is reduced to two exact one-dimensional
crosses:

* the trapezoid exchange, equal to `2 * squareCore + terminalBoundary`;
* the terminal cross, equal to the unmatched boundary column.

Consequently the pair of inequalities

    trapezoidCross <= 0,
    terminalCross <= 2 * normalizedBudget

implies the desired covariance bound.  The proof keeps the negative square
core until the final positive factor-two cancellation.  The independent fine
even/odd reserve is passed through unchanged.

The new tail structure is honest: no inhabitant is asserted.

# Constructivity

Primitive finite sums, exact `Q'` setoid algebra, and reflected polynomial
normalization only.  No `Classical`, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaDriftCross

namespace YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaDriftCross
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Diagonal norm with the terminal mode omitted. -/
def fixedCutoffDiagPrefix (w : Q') (N : Nat) : Q' :=
  fsum (fixedCutoffDiagTerm w) N

/-- Common-cutoff covariance using only the square prefix. -/
def fixedCutoffPrefixCross (low high : Q') (N : Nat) : Q' :=
  adjCorr low N * fixedCutoffDiagPrefix high N +
    -(adjCorr high N * fixedCutoffDiagPrefix low N)

/-- Trapezoidal diagonal mass: the full norm plus the terminal-deleted norm,
equivalently twice the square prefix plus one terminal square. -/
def fixedCutoffTrapezoidNorm (w : Q') (N : Nat) : Q' :=
  coordNormSq w N + fixedCutoffDiagPrefix w N

/-- One-dimensional trapezoid cross. -/
def fixedCutoffTrapezoidCross (low high : Q') (N : Nat) : Q' :=
  adjCorr low N * fixedCutoffTrapezoidNorm high N +
    -(adjCorr high N * fixedCutoffTrapezoidNorm low N)

/-- One-dimensional terminal cross. -/
def fixedCutoffTerminalCross (low high : Q') (N : Nat) : Q' :=
  adjCorr low N * fixedCutoffDiagTerm high N +
    -(adjCorr high N * fixedCutoffDiagTerm low N)

private theorem rect_sub_eq_local
    (F G : Nat → Nat → Q') (m n : Nat) :
    fsum (fun i => fsum (F i) n) m +
        -(fsum (fun i => fsum (G i) n) m) ≈
      fsum (fun i => fsum (fun j => F i j + -(G i j)) n) m := by
  have hneg : -(fsum (fun i => fsum (G i) n) m) ≈
      fsum (fun i => fsum (fun j => -(G i j)) n) m := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (CubeRatioBounds.fsum_neg (fun i => fsum (G i) n) m)) ?_
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
      Q'.eqv_symm (CubeRatioBounds.fsum_neg (G i) n)) m
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hneg) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (CubeRatioBounds.fsum_add
      (fun i => fsum (F i) n)
      (fun i => fsum (fun j => -(G i j)) n) m)) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
    Q'.eqv_symm (CubeRatioBounds.fsum_add
      (F i) (fun j => -(G i j)) n)) m

/-- The square double sum is exactly the one-dimensional prefix cross. -/
theorem fixedCutoffDriftCore_eq_prefixCross
    (low high : Q') (N : Nat) :
    fixedCutoffDriftCore low high N ≈
      fixedCutoffPrefixCross low high N := by
  let AL := fun i => fixedCutoffAdjTerm low i
  let AH := fun i => fixedCutoffAdjTerm high i
  let DL := fun j => fixedCutoffDiagTerm low j
  let DH := fun j => fixedCutoffDiagTerm high j
  have hleft := FusionCoreStepRoundB.fsum_mul_fsum AL DH N N
  have hright := FusionCoreStepRoundB.fsum_mul_fsum AH DL N N
  have hprod :
      fsum AL N * fsum DH N + -(fsum AH N * fsum DL N) ≈
        fsum (fun i =>
          fsum (fun j => AL i * DH j + -(AH i * DL j)) N) N := by
    refine Q'.eqv_trans _
      (fsum (fun i => fsum (fun j => AL i * DH j) N) N +
        -(fsum (fun i => fsum (fun j => AH i * DL j) N) N)) _
      (Q'.add_eqv_congr' hleft (Q'.neg_eqv_congr _ _ hright)) ?_
    exact rect_sub_eq_local
      (fun i j => AL i * DH j)
      (fun i j => AH i * DL j) N N
  have hkernel :
      fsum (fun i =>
        fsum (fun j => AL i * DH j + -(AH i * DL j)) N) N ≈
      fixedCutoffDriftCore low high N := by
    unfold fixedCutoffDriftCore
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
      CubeRatioBounds.fsum_eqv_congr _ _ (fun j => by
        unfold AL AH DL DH fixedCutoffDriftKernel
        exact Q'.eqv_refl _) N) N
  have hprefix : fixedCutoffPrefixCross low high N ≈
      fsum AL N * fsum DH N + -(fsum AH N * fsum DL N) := by
    unfold fixedCutoffPrefixCross fixedCutoffDiagPrefix adjCorr AL AH DL DH
    exact Q'.eqv_refl _
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hprefix (Q'.eqv_trans _ _ _ hprod hkernel))

private def trapezoidExpandL : RingNormaliser.PolyExpr :=
  let A0 := RingNormaliser.PolyExpr.var 0
  let A4 := RingNormaliser.PolyExpr.var 1
  let D0 := RingNormaliser.PolyExpr.var 2
  let D4 := RingNormaliser.PolyExpr.var 3
  let P0 := RingNormaliser.PolyExpr.var 4
  let P4 := RingNormaliser.PolyExpr.var 5
  .add (.mul A0 (.add D4 P4)) (.neg (.mul A4 (.add D0 P0)))

private def trapezoidExpandR : RingNormaliser.PolyExpr :=
  let A0 := RingNormaliser.PolyExpr.var 0
  let A4 := RingNormaliser.PolyExpr.var 1
  let D0 := RingNormaliser.PolyExpr.var 2
  let D4 := RingNormaliser.PolyExpr.var 3
  let P0 := RingNormaliser.PolyExpr.var 4
  let P4 := RingNormaliser.PolyExpr.var 5
  .add
    (.add (.mul A0 D4) (.neg (.mul A4 D0)))
    (.add (.mul A0 P4) (.neg (.mul A4 P0)))

private theorem trapezoidExpand_normal :
    RingNormaliser.normalize trapezoidExpandL =
      RingNormaliser.normalize trapezoidExpandR := by decide

private theorem trapezoid_expand_algebra
    (A0 A4 D0 D4 P0 P4 : Q') :
    A0 * (D4 + P4) + -(A4 * (D0 + P0)) ≈
      (A0 * D4 + -(A4 * D0)) +
        (A0 * P4 + -(A4 * P0)) := by
  simpa [trapezoidExpandL, trapezoidExpandR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      trapezoidExpandL trapezoidExpandR trapezoidExpand_normal
      (fun | 0 => A0 | 1 => A4 | 2 => D0 | 3 => D4 |
        4 => P0 | _ => P4))

/-- The trapezoid cross is the full covariance plus its square-prefix cross. -/
theorem fixedCutoffTrapezoidCross_eq_deficit_add_prefix
    (low high : Q') (N : Nat) :
    fixedCutoffTrapezoidCross low high N ≈
      fixedCutoffDeficitDriftCross low high N +
        fixedCutoffPrefixCross low high N := by
  unfold fixedCutoffTrapezoidCross fixedCutoffTrapezoidNorm
    fixedCutoffDeficitDriftCross fixedCutoffPrefixCross
  exact trapezoid_expand_algebra _ _ _ _ _ _

/-- Exact sharp identity behind the half-boundary refund: the one-dimensional
trapezoid cross is two square cores plus the unmatched terminal column. -/
theorem fixedCutoffTrapezoidCross_eq_two_core_add_boundary
    (low high : Q') (N : Nat) :
    fixedCutoffTrapezoidCross low high N ≈
      (fixedCutoffDriftCore low high N +
        fixedCutoffDriftCore low high N) +
          fixedCutoffDriftBoundary low high N := by
  let C := fixedCutoffDriftCore low high N
  let E := fixedCutoffDriftBoundary low high N
  refine Q'.eqv_trans _ _ _
    (fixedCutoffTrapezoidCross_eq_deficit_add_prefix low high N) ?_
  refine Q'.eqv_trans _
    ((C + E) + C) _
    (Q'.add_eqv_congr'
      (fixedCutoffDeficitDriftCross_eq_core_add_boundary low high N)
      (fixedCutoffDriftCore_eq_prefixCross low high N |> Q'.eqv_symm)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv C E C) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left C _ _ (Q'.add_comm_eqv E C)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv C C E)

/-- The unmatched boundary column is exactly one terminal cross. -/
theorem fixedCutoffDriftBoundary_eq_terminalCross
    (low high : Q') (N : Nat) :
    fixedCutoffDriftBoundary low high N ≈
      fixedCutoffTerminalCross low high N := by
  let AL := fun i => fixedCutoffAdjTerm low i
  let AH := fun i => fixedCutoffAdjTerm high i
  let dL := fixedCutoffDiagTerm low N
  let dH := fixedCutoffDiagTerm high N
  have hsplit := CubeRatioBounds.fsum_add
    (fun i => AL i * dH) (fun i => -(AH i * dL)) N
  have hleft := CubeRatioBounds.fsum_mul_const AL dH N
  have hright0 := CubeRatioBounds.fsum_neg (fun i => AH i * dL) N
  have hright1 := CubeRatioBounds.fsum_mul_const AH dL N
  have hright : fsum (fun i => -(AH i * dL)) N ≈
      -(fsum AH N * dL) :=
    Q'.eqv_trans _ _ _ hright0
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hright1))
  unfold fixedCutoffDriftBoundary
  refine Q'.eqv_trans _
    (fsum (fun i => AL i * dH + -(AH i * dL)) N) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i => by
      unfold AL AH dL dH fixedCutoffDriftKernel
      exact Q'.eqv_refl _) N
  · refine Q'.eqv_trans _ _ _ hsplit ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_symm hleft) hright) ?_
    unfold fixedCutoffTerminalCross adjCorr AL AH dL dH
    exact Q'.eqv_refl _

private def doubleCoreBoundaryL : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let E := RingNormaliser.PolyExpr.var 1
  .add (.add C E) (.add C E)

private def doubleCoreBoundaryR : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let E := RingNormaliser.PolyExpr.var 1
  .add (.add (.add C C) E) E

private theorem doubleCoreBoundary_normal :
    RingNormaliser.normalize doubleCoreBoundaryL =
      RingNormaliser.normalize doubleCoreBoundaryR := by decide

private theorem double_core_boundary_algebra (C E : Q') :
    (C + E) + (C + E) ≈ ((C + C) + E) + E := by
  simpa [doubleCoreBoundaryL, doubleCoreBoundaryR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      doubleCoreBoundaryL doubleCoreBoundaryR doubleCoreBoundary_normal
      (fun | 0 => C | _ => E))

/-- The fixed normalized covariance budget at physical scale `k`. -/
def blockDriftCrossBudget (k : Nat) : Q' :=
  let w0 := blockWeight k
  let w4 := qpow (blockWeight (k + 1)) 4
  let D0 := coordNormSq w0 (blockNcut k)
  let D4 := coordNormSq w4 (blockNcut k)
  (blockNormalizedSlopeCoeff *
    (blockQuadraticDrift k * blockLength k)) * (D0 * D4)

/-- Honest sharp tail after the three checked cells.  The coarse covariance is
split into the nonpositive trapezoid exchange and a factor-two terminal
budget; the independent fine even/odd reserve is unchanged. -/
structure BlockCompatibleP2TrapezoidExchangeTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalBudget : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTerminalCross w0 w4 (blockNcut k) <=
      Q'.ofNat 2 * blockDriftCrossBudget k
  fineReserve : forall k, 7 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <=
      D1 * T4

/-- The trapezoid refund and factor-two terminal budget compile to the exact
dimensionless covariance tail. -/
def BlockCompatibleP2TrapezoidExchangeTailFromSeven.toDriftCrossTail
    (T : BlockCompatibleP2TrapezoidExchangeTailFromSeven) :
    BlockCompatibleP2DimensionlessDriftCrossTailFromSeven where
  coarseCross := fun k hk => by
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    let C := fixedCutoffDriftCore w0 w4 N
    let E := fixedCutoffDriftBoundary w0 w4 N
    let X := C + E
    let B := blockDriftCrossBudget k
    have htrap : fixedCutoffTrapezoidCross w0 w4 N <= (0 : Q') := by
      simpa only [w0, w4, N] using T.trapezoidExchange k hk
    have hrefund : (C + C) + E <= (0 : Q') :=
      Q'.le_trans' _ _ _
        (Q'.ge_of_eqv
          (by simpa only [C, E] using
            fixedCutoffTrapezoidCross_eq_two_core_add_boundary w0 w4 N))
        htrap
    have hterminal : fixedCutoffTerminalCross w0 w4 N <=
        Q'.ofNat 2 * B := by
      simpa only [w0, w4, N, B] using T.terminalBudget k hk
    have hboundary : E <= Q'.ofNat 2 * B :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (by simpa only [E] using
            fixedCutoffDriftBoundary_eq_terminalCross w0 w4 N))
        hterminal
    have hadd := Q'.add_le_add_right ((C + C) + E) (0 : Q') E hrefund
    have hdoubleToBoundary : X + X <= E := by
      have hleft : X + X ≈ ((C + C) + E) + E := by
        simpa only [X] using double_core_boundary_algebra C E
      have hright : (0 : Q') + E ≈ E := QPoly.q_zero_add_eqv E
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))
    have hdouble : X + X <= B + B :=
      Q'.le_trans' _ _ _ hdoubleToBoundary
        (Q'.le_trans' _ _ _ hboundary
          (Q'.le_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv B)))
    have hscaled : Q'.ofNat 2 * X <= Q'.ofNat 2 * B :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv X))
        (Q'.le_trans' _ _ _ hdouble
          (Q'.ge_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv B)))
    have hXB : X <= B := Q'.le_of_mul_le_mul_left hscaled (by decide)
    have hcross : fixedCutoffDeficitDriftCross w0 w4 N <= X :=
      Q'.le_of_eqv
        (by simpa only [C, E, X] using
          fixedCutoffDeficitDriftCross_eq_core_add_boundary w0 w4 N)
    exact Q'.le_trans' _ _ _ hcross hXB
  fineReserve := fun k hk => T.fineReserve k hk

/-- Direct landing in the division-free coefficient sandwich consumed by the
checked prefix and the physical `BlockingStep.Phi` bridge. -/
def BlockCompatibleP2TrapezoidExchangeTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TrapezoidExchangeTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toDriftCrossTail.toCoefficientSandwich

#print axioms fixedCutoffDriftCore_eq_prefixCross
#print axioms fixedCutoffTrapezoidCross_eq_deficit_add_prefix
#print axioms fixedCutoffTrapezoidCross_eq_two_core_add_boundary
#print axioms fixedCutoffDriftBoundary_eq_terminalCross
#print axioms BlockCompatibleP2TrapezoidExchangeTailFromSeven.toDriftCrossTail
#print axioms BlockCompatibleP2TrapezoidExchangeTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
