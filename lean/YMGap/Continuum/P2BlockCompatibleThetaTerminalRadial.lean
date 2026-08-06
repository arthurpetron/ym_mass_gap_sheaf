/-
Track 11.7-fusion / R3l -- exact radial reindex of the terminal diagonal moment.

# Result

The diagonal gap envelope is reindexed without an inequality or a growing
normalization certificate.  For a cutoff `N=n+1` it is exactly the sum of

* the head diagonal with weight `2*(N+1)^2-5`;
* the interior diagonal at `i+1` with weight
  `4*(N+1)^2-4*(i+2)^2-2`;
* the terminal diagonal with weight `2*N+1`.

This is the sharp radial form needed by the remaining theta-moment estimate;
no analytic bound or tail inhabitant is asserted here.

# Constructivity

Primitive finite-sum recursion, exact `Q'` setoid algebra, and Presburger
reasoning after two explicit Casimir identities.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalMoment

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaDriftCross
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalChord
open YMGap.Continuum.P2BlockCompatibleThetaTerminalMoment
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem c4_charge_sq_local (s : Nat) :
    c4 s + 1 = (s + 1) * (s + 1) := by
  show s * (s + 2) + 1 = (s + 1) * (s + 1)
  have e1 : (s + 1) * (s + 1) = s * s + (2 * s + 1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have e2 : s * (s + 2) = s * s + 2 * s := by
    rw [Nat.mul_add]
    omega
  rw [e1, e2]
  omega

private theorem c4_second_diff_local (s : Nat) :
    c4 s + c4 (s + 2) = 2 * c4 (s + 1) + 2 := by
  show s * (s + 2) + (s + 2) * ((s + 2) + 2) =
    2 * ((s + 1) * ((s + 1) + 2)) + 2
  have h0 : s * (s + 2) = s * s + 2 * s := by
    rw [Nat.mul_add, Nat.mul_comm s 2]
  have h2 : (s + 2) * ((s + 2) + 2) = s * s + 6 * s + 8 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have h1 : (s + 1) * ((s + 1) + 2) = s * s + 4 * s + 3 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  rw [h0, h2, h1]
  omega

private def adjacentBaseL : RingNormaliser.PolyExpr :=
  let g := RingNormaliser.PolyExpr.var 0
  let t0 := RingNormaliser.PolyExpr.var 1
  let t1 := RingNormaliser.PolyExpr.var 2
  .add (.const 0) (.mul g (.add t0 t1))

private def adjacentBaseR : RingNormaliser.PolyExpr :=
  let g := RingNormaliser.PolyExpr.var 0
  let t0 := RingNormaliser.PolyExpr.var 1
  let t1 := RingNormaliser.PolyExpr.var 2
  .add (.add (.mul g t0) (.const 0)) (.mul g t1)

private theorem adjacentBase_normal :
    RingNormaliser.normalize adjacentBaseL =
      RingNormaliser.normalize adjacentBaseR := by decide

private theorem adjacent_base_eqv (g t0 t1 : Q') :
    (0 : Q') + g * (t0 + t1) ≈ (g * t0 + 0) + g * t1 := by
  simpa [adjacentBaseL, adjacentBaseR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      adjacentBaseL adjacentBaseR adjacentBase_normal
      (fun | 0 => g | 1 => t0 | _ => t1))

private def adjacentStepL : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let g0 := RingNormaliser.PolyExpr.var 2
  let g1 := RingNormaliser.PolyExpr.var 3
  let t1 := RingNormaliser.PolyExpr.var 4
  let t2 := RingNormaliser.PolyExpr.var 5
  .add (.add (.add A S) (.mul g0 t1))
    (.mul g1 (.add t1 t2))

private def adjacentStepR : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let g0 := RingNormaliser.PolyExpr.var 2
  let g1 := RingNormaliser.PolyExpr.var 3
  let t1 := RingNormaliser.PolyExpr.var 4
  let t2 := RingNormaliser.PolyExpr.var 5
  .add (.add A (.add S (.mul (.add g0 g1) t1))) (.mul g1 t2)

private theorem adjacentStep_normal :
    RingNormaliser.normalize adjacentStepL =
      RingNormaliser.normalize adjacentStepR := by decide

private theorem adjacent_step_eqv
    (A S g0 g1 t1 t2 : Q') :
    ((A + S) + g0 * t1) + g1 * (t1 + t2) ≈
      (A + (S + (g0 + g1) * t1)) + g1 * t2 := by
  simpa [adjacentStepL, adjacentStepR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      adjacentStepL adjacentStepR adjacentStep_normal
      (fun | 0 => A | 1 => S | 2 => g0 | 3 => g1 | 4 => t1 | _ => t2))

/-- Generic exact reindex of a sum of adjacent diagonal pairs. -/
private theorem fsum_adjacent_diag_reindex
    (g t : Nat -> Q') : forall n,
    fsum (fun i => g i * (t i + t (i + 1))) (n + 1) ≈
      (g 0 * t 0 +
        fsum (fun i => (g i + g (i + 1)) * t (i + 1)) n) +
          g n * t (n + 1)
  | 0 => by
      change (0 : Q') + g 0 * (t 0 + t 1) ≈
        (g 0 * t 0 + 0) + g 0 * t 1
      exact adjacent_base_eqv _ _ _
  | n + 1 => by
      have ih := fsum_adjacent_diag_reindex g t n
      change
        fsum (fun i => g i * (t i + t (i + 1))) (n + 1) +
            g (n + 1) * (t (n + 1) + t (n + 1 + 1)) ≈
          (g 0 * t 0 +
              (fsum (fun i => (g i + g (i + 1)) * t (i + 1)) n +
                (g n + g (n + 1)) * t (n + 1))) +
            g (n + 1) * t (n + 1 + 1)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact adjacent_step_eqv _ _ _ _ _ _

/-- The head radial coefficient at a positive cutoff. -/
theorem fixedCutoffTerminalExponentGap_head (N : Nat) :
    fixedCutoffTerminalExponentGap 0 N =
      2 * ((N + 1) * (N + 1)) - 5 := by
  have hsq := c4_charge_sq_local N
  unfold fixedCutoffTerminalExponentGap fixedCutoffDiagExponent
    fixedCutoffAdjExponent
  have hc0 : c4 0 = 0 := by decide
  have hc1 : c4 1 = 3 := by decide
  rw [hc0, hc1]
  omega

/-- The exact combined radial coefficient on an interior diagonal. -/
theorem fixedCutoffTerminalExponentGap_pair
    {i N : Nat} (hiN : i + 1 < N) :
    fixedCutoffTerminalExponentGap i N +
        fixedCutoffTerminalExponentGap (i + 1) N =
      4 * ((N + 1) * (N + 1)) -
          4 * ((i + 2) * (i + 2)) - 2 := by
  have hgap0 := fixedCutoffTerminalExponentGap_pos
    (show i < N by omega)
  have hgap1 := fixedCutoffTerminalExponentGap_pos hiN
  have hcurv := c4_second_diff_local i
  have hsqN := c4_charge_sq_local N
  have hsqi := c4_charge_sq_local (i + 1)
  have hidx : i + 1 + 1 = i + 2 := by omega
  rw [hidx] at hsqi
  unfold fixedCutoffTerminalExponentGap fixedCutoffDiagExponent
    fixedCutoffAdjExponent at hgap0 hgap1 ⊢
  rw [hidx] at hgap1 ⊢
  omega

/-- The exact radial coefficient on the unmatched terminal diagonal. -/
theorem fixedCutoffTerminalExponentGap_terminal (n : Nat) :
    fixedCutoffTerminalExponentGap n (n + 1) = 2 * n + 3 := by
  unfold fixedCutoffTerminalExponentGap fixedCutoffDiagExponent
    fixedCutoffAdjExponent
  rw [BondMovingScaledNorm.c4_succ]
  omega

/-- Sharp head/interior/terminal radial form of the diagonal gap envelope. -/
def fixedCutoffTerminalRadialDiagEnvelope (low : Q') : Nat -> Q'
  | 0 => 0
  | n + 1 =>
      (Q'.ofNat (2 * ((n + 2) * (n + 2)) - 5) *
          fixedCutoffDiagTerm low 0 +
        fsum (fun i =>
          Q'.ofNat
              (4 * ((n + 2) * (n + 2)) -
                4 * ((i + 2) * (i + 2)) - 2) *
            fixedCutoffDiagTerm low (i + 1)) n) +
        Q'.ofNat (2 * n + 3) * fixedCutoffDiagTerm low (n + 1)

private theorem ofNat_mul_eqv_of_eq
    {a b : Nat} (h : a = b) (x : Q') :
    Q'.ofNat a * x ≈ Q'.ofNat b * x := by
  rw [h]
  exact Q'.eqv_refl _

/-- Exact, cutoff-uniform radialization of the diagonal terminal envelope. -/
theorem fixedCutoffTerminalDiagGapEnvelope_eq_radial
    (low : Q') (N : Nat) :
    fixedCutoffTerminalDiagGapEnvelope low N ≈
      fixedCutoffTerminalRadialDiagEnvelope low N := by
  cases N with
  | zero =>
      unfold fixedCutoffTerminalDiagGapEnvelope
        fixedCutoffTerminalRadialDiagEnvelope
      exact Q'.eqv_refl 0
  | succ n =>
      let g := fun i => Q'.ofNat
        (fixedCutoffTerminalExponentGap i (n + 1))
      let t := fun i => fixedCutoffDiagTerm low i
      have hreindex := fsum_adjacent_diag_reindex g t n
      have hhead : g 0 * t 0 ≈
          Q'.ofNat (2 * ((n + 2) * (n + 2)) - 5) * t 0 := by
        apply ofNat_mul_eqv_of_eq
        simpa only [g] using fixedCutoffTerminalExponentGap_head (n + 1)
      have hinterior :
          fsum (fun i => (g i + g (i + 1)) * t (i + 1)) n ≈
            fsum (fun i =>
              Q'.ofNat
                  (4 * ((n + 2) * (n + 2)) -
                    4 * ((i + 2) * (i + 2)) - 2) *
                t (i + 1)) n := by
        refine CubeRatioBounds.fsum_eqv_congr_lt _ _ n ?_
        intro i hi
        have hp := fixedCutoffTerminalExponentGap_pair
          (i := i) (N := n + 1) (show i + 1 < n + 1 by omega)
        have hweight : g i + g (i + 1) ≈
            Q'.ofNat
              (4 * ((n + 2) * (n + 2)) -
                4 * ((i + 2) * (i + 2)) - 2) := by
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.ofNat_add_eqv _ _)) ?_
          exact Q'.eqv_of_eq (congrArg Q'.ofNat hp)
        exact Q'.mul_eqv_congr_right _ _ _ hweight
      have hterminal : g n * t (n + 1) ≈
          Q'.ofNat (2 * n + 3) * t (n + 1) := by
        apply ofNat_mul_eqv_of_eq
        simpa only [g] using fixedCutoffTerminalExponentGap_terminal n
      unfold fixedCutoffTerminalDiagGapEnvelope
        fixedCutoffTerminalRadialDiagEnvelope
      change fsum (fun i => g i * (t i + t (i + 1))) (n + 1) ≈ _
      refine Q'.eqv_trans _ _ _ hreindex ?_
      exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hhead hinterior) hterminal

/-- The radial envelope is nonnegative at every nonnegative heat weight. -/
theorem fixedCutoffTerminalRadialDiagEnvelope_nonneg
    {low : Q'} (hlow : (0 : Q') <= low) : forall N,
    (0 : Q') <= fixedCutoffTerminalRadialDiagEnvelope low N
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      have hdiag : forall i, (0 : Q') <= fixedCutoffDiagTerm low i :=
        fun i => Q'.mul_nonneg _ _
          (coeffW_nonneg hlow i) (coeffW_nonneg hlow i)
      have hhead : (0 : Q') <=
          Q'.ofNat (2 * ((n + 2) * (n + 2)) - 5) *
            fixedCutoffDiagTerm low 0 :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) (hdiag 0)
      have hmid : (0 : Q') <=
          fsum (fun i =>
            Q'.ofNat
                (4 * ((n + 2) * (n + 2)) -
                  4 * ((i + 2) * (i + 2)) - 2) *
              fixedCutoffDiagTerm low (i + 1)) n :=
        fsum_nonneg (fun i => Q'.mul_nonneg _ _
          (HeatKernelRGStep.zero_le_ofNat _) (hdiag (i + 1))) n
      have hend : (0 : Q') <=
          Q'.ofNat (2 * n + 3) * fixedCutoffDiagTerm low (n + 1) :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) (hdiag (n + 1))
      unfold fixedCutoffTerminalRadialDiagEnvelope
      exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hhead hmid) hend

/-! ## Rational separation of the remaining endpoint/radial product -/

/-- Endpoint share chosen to retain a simple rational all-cutoff target. -/
def terminalOuterSplitCoeff : Q' := Q'.mkPos 5 16 (by decide)

/-- Radial-moment share paired with `terminalOuterSplitCoeff`. -/
def terminalRadialSplitCoeff : Q' := Q'.mkPos 341 125 (by decide)

theorem terminalSplitCoeff_product_le_budget :
    terminalOuterSplitCoeff * terminalRadialSplitCoeff <=
      Q'.ofNat 4 * blockNormalizedSlopeCoeff := by
  unfold terminalOuterSplitCoeff terminalRadialSplitCoeff
    blockNormalizedSlopeCoeff
  decide

private def splitProductL : RingNormaliser.PolyExpr :=
  let cO := RingNormaliser.PolyExpr.var 0
  let D4 := RingNormaliser.PolyExpr.var 1
  let cR := RingNormaliser.PolyExpr.var 2
  let L := RingNormaliser.PolyExpr.var 3
  let D0 := RingNormaliser.PolyExpr.var 4
  .mul (.mul cO D4) (.mul cR (.mul (.mul L L) D0))

private def splitProductR : RingNormaliser.PolyExpr :=
  let cO := RingNormaliser.PolyExpr.var 0
  let D4 := RingNormaliser.PolyExpr.var 1
  let cR := RingNormaliser.PolyExpr.var 2
  let L := RingNormaliser.PolyExpr.var 3
  let D0 := RingNormaliser.PolyExpr.var 4
  .mul L (.mul (.mul cO cR) (.mul L (.mul D0 D4)))

private theorem splitProduct_normal :
    RingNormaliser.normalize splitProductL =
      RingNormaliser.normalize splitProductR := by decide

private theorem split_product_eqv (cO D4 cR L D0 : Q') :
    (cO * D4) * (cR * ((L * L) * D0)) ≈
      L * ((cO * cR) * (L * (D0 * D4))) := by
  simpa [splitProductL, splitProductR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      splitProductL splitProductR splitProduct_normal
      (fun | 0 => cO | 1 => D4 | 2 => cR | 3 => L | _ => D0))

private theorem factorized_terminal_product_le
    (L O R D0 D4 cO cR B : Q')
    (hLpos : (0 : Q') < L)
    (hD00 : (0 : Q') <= D0) (hD40 : (0 : Q') <= D4)
    (hR0 : (0 : Q') <= R) (hcO0 : (0 : Q') <= cO)
    (hOuter : L * O <= cO * D4)
    (hRadial : R <= cR * ((L * L) * D0))
    (hcoeff : cO * cR <= B) :
    O * R <= B * (L * (D0 * D4)) := by
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ R hOuter hR0
  have hcOD40 : (0 : Q') <= cO * D4 :=
    Q'.mul_nonneg _ _ hcO0 hD40
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ (cO * D4)
    hRadial hcOD40
  have hraw : (L * O) * R <=
      (cO * D4) * (cR * ((L * L) * D0)) :=
    Q'.le_trans' _ _ _ hfirst hsecond
  have hleft : (L * O) * R ≈ L * (O * R) :=
    Q'.mul_assoc_eqv L O R
  have hright := split_product_eqv cO D4 cR L D0
  have hL0 : (0 : Q') <= L := Q'.le_of_lt hLpos
  have hscale0 : (0 : Q') <= L * (D0 * D4) :=
    Q'.mul_nonneg _ _ hL0 (Q'.mul_nonneg _ _ hD00 hD40)
  have hcoeffScaled := Q'.mul_le_mul_of_nonneg_right _ _
    (L * (D0 * D4)) hcoeff hscale0
  have htargetScaled := Q'.mul_le_mul_of_nonneg_left _ _ L
    hcoeffScaled hL0
  have hscaled : L * (O * R) <=
      L * (B * (L * (D0 * D4))) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hraw
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) htargetScaled))
  exact Q'.le_of_mul_le_mul_left hscaled hLpos

/-- Honest radial terminal frontier.  The exact reindex theorem compiles this
field back to the diagonal-envelope carrier without spending any budget. -/
structure BlockCompatibleP2TerminalRadialTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalRadialEnvelope : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let D0 := coordNormSq w0 (blockNcut k)
    let D4 := coordNormSq w4 (blockNcut k)
    fixedCutoffTerminalOuterFactor w4 (blockNcut k) *
        fixedCutoffTerminalRadialDiagEnvelope w0 (blockNcut k) <=
      (Q'.ofNat 4 * blockNormalizedSlopeCoeff) *
        (blockLength k * (D0 * D4))
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

def BlockCompatibleP2TerminalRadialTailFromSeven.toDiagEnvelopeTail
    (T : BlockCompatibleP2TerminalRadialTailFromSeven) :
    BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalDiagEnvelope := fun k hk => by
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    let O := fixedCutoffTerminalOuterFactor w4 N
    let E := fixedCutoffTerminalDiagGapEnvelope w0 N
    let R := fixedCutoffTerminalRadialDiagEnvelope w0 N
    let D0 := coordNormSq w0 N
    let D4 := coordNormSq w4 N
    have hER : E ≈ R := by
      simpa only [E, R] using
        fixedCutoffTerminalDiagGapEnvelope_eq_radial w0 N
    have hmul : O * E ≈ O * R :=
      Q'.mul_eqv_congr_left O _ _ hER
    have hradial : O * R <=
        (Q'.ofNat 4 * blockNormalizedSlopeCoeff) *
          (blockLength k * (D0 * D4)) := by
      simpa only [w0, w4, N, O, R, D0, D4] using
        T.terminalRadialEnvelope k hk
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hmul) hradial
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalRadialTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalRadialTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toDiagEnvelopeTail.toCoefficientSandwich

/-- Factorized all-cutoff terminal frontier.  Both fields are division-free:
the endpoint field is scaled by one cutoff length and the radial field by two. -/
structure BlockCompatibleP2TerminalFactorizedTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalOuter : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    blockLength k * fixedCutoffTerminalOuterFactor w4 (blockNcut k) <=
      terminalOuterSplitCoeff * coordNormSq w4 (blockNcut k)
  terminalRadial : forall k, 7 <= k ->
    let w0 := blockWeight k
    fixedCutoffTerminalRadialDiagEnvelope w0 (blockNcut k) <=
      terminalRadialSplitCoeff *
        ((blockLength k * blockLength k) *
          coordNormSq w0 (blockNcut k))
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

def BlockCompatibleP2TerminalFactorizedTailFromSeven.toRadialTail
    (T : BlockCompatibleP2TerminalFactorizedTailFromSeven) :
    BlockCompatibleP2TerminalRadialTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalRadialEnvelope := fun k hk => by
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    let N := blockNcut k
    let L := blockLength k
    let O := fixedCutoffTerminalOuterFactor w4 N
    let R := fixedCutoffTerminalRadialDiagEnvelope w0 N
    let D0 := coordNormSq w0 N
    let D4 := coordNormSq w4 N
    have hw00 : (0 : Q') <= w0 := by
      simpa only [w0] using blockWeight_nonneg k
    have hw40 : (0 : Q') <= w4 := by
      unfold w4
      exact qpow_nonneg (blockWeight (k + 1))
        (blockWeight_nonneg (k + 1)) 4
    have houter : L * O <= terminalOuterSplitCoeff * D4 := by
      simpa only [w4, N, L, O, D4] using T.terminalOuter k hk
    have hradial : R <= terminalRadialSplitCoeff * ((L * L) * D0) := by
      simpa only [w0, N, L, R, D0] using T.terminalRadial k hk
    have hproduct := factorized_terminal_product_le
      L O R D0 D4 terminalOuterSplitCoeff terminalRadialSplitCoeff
      (Q'.ofNat 4 * blockNormalizedSlopeCoeff)
      (blockLength_pos k)
      (coordNormSq_nonneg hw00 N) (coordNormSq_nonneg hw40 N)
      (fixedCutoffTerminalRadialDiagEnvelope_nonneg hw00 N)
      (by unfold terminalOuterSplitCoeff; decide)
      houter hradial terminalSplitCoeff_product_le_budget
    simpa only [w0, w4, N, L, O, R, D0, D4] using hproduct
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalFactorizedTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalFactorizedTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toRadialTail.toCoefficientSandwich

#print axioms fixedCutoffTerminalExponentGap_head
#print axioms fixedCutoffTerminalExponentGap_pair
#print axioms fixedCutoffTerminalExponentGap_terminal
#print axioms fixedCutoffTerminalDiagGapEnvelope_eq_radial
#print axioms fixedCutoffTerminalRadialDiagEnvelope_nonneg
#print axioms terminalSplitCoeff_product_le_budget
#print axioms BlockCompatibleP2TerminalRadialTailFromSeven.toDiagEnvelopeTail
#print axioms BlockCompatibleP2TerminalRadialTailFromSeven.toCoefficientSandwich
#print axioms BlockCompatibleP2TerminalFactorizedTailFromSeven.toRadialTail
#print axioms BlockCompatibleP2TerminalFactorizedTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial
