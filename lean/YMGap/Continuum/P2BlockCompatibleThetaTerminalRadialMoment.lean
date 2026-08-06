/-
Track 11.7-fusion / R3s -- exact fourth-moment balance for the terminal radial field.

# Result

The remaining radial envelope is not an opaque weighted theta sum.  If

    D  = sum_(s<=N) diag(s),
    M4 = sum_(s<=N) 4*(s+1)^2*diag(s),
    L  = N+1,

then its exact head/interior/terminal weights satisfy

    radial + M4 + (2*L^2-1)*diag(0)
      = (4*L^2-2)*D + (2*L+1)*diag(N).

Consequently the sharp radial upper bound with coefficient `341/125` follows
from the positive lower-moment inequality with complementary coefficient
`159/125`.  The compiler installs the already-proved physical terminal-theta
endpoint field, so the honest remaining carrier consists only of this moment
lower bound, the trapezoid exchange, and the independent fine reserve.

No inhabitant of those three analytic fields is asserted.

# Constructivity

Primitive finite-sum reindexing, natural-number coefficient identities, and
the reflected `Q'` polynomial normalizer only.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialMoment

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaDriftCross
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial
open YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Four times the fourth radial heat moment.  `fixedCutoffDiagTerm` already
contains `(s+1)^2`, so the displayed multiplier produces the fourth moment in
the integer-theta coordinate. -/
def fixedCutoffTerminalFourFourthMoment (w : Q') (N : Nat) : Q' :=
  fsum (fun s =>
    Q'.ofNat (4 * ((s + 1) * (s + 1))) * fixedCutoffDiagTerm w s) (N + 1)

/-- Complement of `terminalRadialSplitCoeff = 341/125` inside the leading
radial coefficient four. -/
def terminalRadialMomentCoeff : Q' := Q'.mkPos 159 125 (by decide)

theorem terminalRadialCoeff_balance :
    terminalRadialMomentCoeff + terminalRadialSplitCoeff ≈ Q'.ofNat 4 := by
  unfold terminalRadialMomentCoeff terminalRadialSplitCoeff
  decide

private theorem weightedNatAdd_eqv
    {a b c : Nat} (h : a + b = c) (x : Q') :
    Q'.ofNat a * x + Q'.ofNat b * x ≈ Q'.ofNat c * x := by
  refine Q'.eqv_trans _ ((Q'.ofNat a + Q'.ofNat b) * x) _
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
  rw [← h]
  exact Q'.mul_eqv_congr_right _ _ x
    (Q'.eqv_symm (Q'.ofNat_add_eqv a b))

private theorem weightedNatAddThree_eqv
    {a b c d : Nat} (h : a + b + c = d) (x : Q') :
    (Q'.ofNat a * x + Q'.ofNat b * x) + Q'.ofNat c * x ≈
      Q'.ofNat d * x := by
  have hab := weightedNatAdd_eqv (a := a) (b := b) (c := a + b) rfl x
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hab)
    (weightedNatAdd_eqv h x)

private theorem le_of_add_le_add_right_local
    {a b c : Q'} (h : a + c <= b + c) : a <= b := by
  have hscaled := Q'.add_le_add_right _ _ (-c) h
  have ha : (a + c) + -c ≈ a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a c (-c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  have hb : (b + c) + -c ≈ b := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b c (-c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' b)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv ha)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hb))

/-- Constant-size algebraic regrouping used to keep the reflected normalizer
away from reducible finite sums. -/
private theorem radialBalance_regroup
    (h r t m j u x : Q') :
    ((((h + r) + t) + ((m + j) + u)) + x) ≈
      (((h + m) + x) + (r + j)) + (t + u) := by
  ring_qeqv

/-- Factor a common coefficient after the three radial sectors have been
balanced. -/
private theorem radialCommon_regroup
    (c d0 interior terminal extra : Q') :
    (c * d0 + c * interior) + (c * terminal + extra) ≈
      c * ((d0 + interior) + terminal) + extra := by
  ring_qeqv

/-- Abstract compiler for the head/interior/terminal coefficient balance.
Keeping this theorem independent of finite-sum definitions prevents Lean's
definitional equality checker from unfolding a symbolic `fsum` while it is
only trying to reassociate seven scalar terms. -/
private theorem radialBalance_of_parts
    (radial moment D h r t m j u x c d0 interior terminal extra : Q')
    (hRadial : radial ≈ (h + r) + t)
    (hMoment : moment ≈ (m + j) + u)
    (hD : D ≈ (d0 + interior) + terminal)
    (hHead : (h + m) + x ≈ c * d0)
    (hInterior : r + j ≈ c * interior)
    (hTerminal : t + u ≈ c * terminal + extra) :
    radial + moment + x ≈ c * D + extra := by
  refine Q'.eqv_trans _
    ((((h + r) + t) + ((m + j) + u)) + x) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hRadial hMoment) (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    ((((h + m) + x) + (r + j)) + (t + u)) _
    (radialBalance_regroup _ _ _ _ _ _ _) ?_
  refine Q'.eqv_trans _
    ((c * d0 + c * interior) + (c * terminal + extra)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hHead hInterior) hTerminal
  refine Q'.eqv_trans _
    (c * ((d0 + interior) + terminal) + extra) _
    (radialCommon_regroup _ _ _ _ _) ?_
  exact Q'.add_eqv_congr_right _ _ extra
    (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm hD))

private theorem interiorCoeff_add_fourSquare
    {i n : Nat} (hi : i < n) :
    (4 * ((n + 2) * (n + 2)) -
          4 * ((i + 2) * (i + 2)) - 2) +
        4 * ((i + 2) * (i + 2)) =
      4 * ((n + 2) * (n + 2)) - 2 := by
  have hir : i + 2 <= n + 1 := by omega
  have hsq : (i + 2) * (i + 2) <= (n + 1) * (n + 1) :=
    Nat.mul_le_mul hir hir
  have hnext : (n + 1) * (n + 1) + 1 <= (n + 2) * (n + 2) := by
    have hexpand :
        (n + 2) * (n + 2) =
          (n + 1) * (n + 1) + (n + 1) + (n + 2) := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.add_mul, Nat.mul_add]
      omega
    rw [hexpand]
    omega
  have hgap : (i + 2) * (i + 2) + 1 <= (n + 2) * (n + 2) :=
    Nat.le_trans (Nat.add_le_add_right hsq 1) hnext
  have hscaled := Nat.mul_le_mul_left 4 hgap
  omega

private theorem radialInteriorMoment_balance
    (w : Q') (n : Nat) :
    fsum (fun i =>
        Q'.ofNat
            (4 * ((n + 2) * (n + 2)) -
              4 * ((i + 2) * (i + 2)) - 2) *
          fixedCutoffDiagTerm w (i + 1)) n +
      fsum (fun i =>
        Q'.ofNat (4 * ((i + 2) * (i + 2))) *
          fixedCutoffDiagTerm w (i + 1)) n ≈
      Q'.ofNat (4 * ((n + 2) * (n + 2)) - 2) *
        fsum (fun i => fixedCutoffDiagTerm w (i + 1)) n := by
  let r := fun i =>
    Q'.ofNat
        (4 * ((n + 2) * (n + 2)) -
          4 * ((i + 2) * (i + 2)) - 2) *
      fixedCutoffDiagTerm w (i + 1)
  let m := fun i =>
    Q'.ofNat (4 * ((i + 2) * (i + 2))) *
      fixedCutoffDiagTerm w (i + 1)
  let d := fun i => fixedCutoffDiagTerm w (i + 1)
  refine Q'.eqv_trans _ (fsum (fun i => r i + m i) n) _
    (Q'.eqv_symm (CubeRatioBounds.fsum_add r m n)) ?_
  refine Q'.eqv_trans _ (fsum (fun i =>
      Q'.ofNat (4 * ((n + 2) * (n + 2)) - 2) * d i) n) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr_lt _ _ n (fun i hi => by
      dsimp only [r, m, d]
      exact weightedNatAdd_eqv (interiorCoeff_add_fourSquare hi) _)
  · exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul
        (Q'.ofNat (4 * ((n + 2) * (n + 2)) - 2)) d n)

/-- Exact coefficient balance behind the terminal radial field. -/
theorem fixedCutoffTerminalRadial_fourthMoment_balance
    (w : Q') (N : Nat) :
    let L := N + 1
    fixedCutoffTerminalRadialDiagEnvelope w N +
          fixedCutoffTerminalFourFourthMoment w N +
          Q'.ofNat (2 * (L * L) - 1) * fixedCutoffDiagTerm w 0 ≈
      Q'.ofNat (4 * (L * L) - 2) * coordNormSq w N +
        Q'.ofNat (2 * L + 1) * fixedCutoffDiagTerm w N := by
  cases N with
  | zero =>
      unfold fixedCutoffTerminalRadialDiagEnvelope
        fixedCutoffTerminalFourFourthMoment coordNormSq
      ring_qeqv
  | succ n =>
      let d := fun s => fixedCutoffDiagTerm w s
      let I := fsum (fun i => d (i + 1)) n
      let J := fsum (fun i =>
        Q'.ofNat (4 * ((i + 2) * (i + 2))) * d (i + 1)) n
      let R := fsum (fun i =>
        Q'.ofNat
            (4 * ((n + 2) * (n + 2)) -
              4 * ((i + 2) * (i + 2)) - 2) * d (i + 1)) n
      let L2 := (n + 2) * (n + 2)
      let common := 4 * L2 - 2
      have hLsq : 4 <= L2 := by
        dsimp only [L2]
        exact Nat.mul_le_mul
          (show 2 <= n + 2 by omega) (show 2 <= n + 2 by omega)
      have hD : coordNormSq w (n + 1) ≈ (d 0 + I) + d (n + 1) := by
        have h := AFRateCalibration.fsum_shift_cons d (n + 1)
        change fsum d (n + 2) ≈
          d 0 + (fsum (fun i => d (i + 1)) n + d (n + 1)) at h
        unfold coordNormSq
        exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      have hM : fixedCutoffTerminalFourFourthMoment w (n + 1) ≈
          (Q'.ofNat 4 * d 0 + J) + Q'.ofNat (4 * L2) * d (n + 1) := by
        let m := fun s =>
          Q'.ofNat (4 * ((s + 1) * (s + 1))) * d s
        have h := AFRateCalibration.fsum_shift_cons m (n + 1)
        change fsum m (n + 2) ≈
          m 0 + (fsum (fun i => m (i + 1)) n + m (n + 1)) at h
        have hm0 : m 0 ≈ Q'.ofNat 4 * d 0 := by
          unfold m
          change Q'.ofNat 4 * d 0 ≈ Q'.ofNat 4 * d 0
          exact Q'.eqv_refl _
        have hmN : m (n + 1) ≈ Q'.ofNat (4 * L2) * d (n + 1) := by
          unfold m L2
          rw [show n + 1 + 1 = n + 2 by omega]
          exact Q'.eqv_refl _
        have hmJ : fsum (fun i => m (i + 1)) n ≈ J := by
          unfold J
          exact CubeRatioBounds.fsum_eqv_congr_lt _ _ n (fun i _ => by
            unfold m
            rw [show i + 1 + 1 = i + 2 by omega]
            exact Q'.eqv_refl _)
        unfold fixedCutoffTerminalFourFourthMoment
        change fsum m (n + 2) ≈ _
        refine Q'.eqv_trans _ _ _ h ?_
        refine Q'.eqv_trans _
          (Q'.ofNat 4 * d 0 +
            (J + Q'.ofNat (4 * L2) * d (n + 1))) _ ?_ ?_
        · exact Q'.add_eqv_congr' hm0 (Q'.add_eqv_congr' hmJ hmN)
        · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      have hmid : R + J ≈ Q'.ofNat common * I := by
        simpa only [R, J, common, I, d] using
          radialInteriorMoment_balance w n
      have hheadNat :
          (2 * L2 - 5) + 4 + (2 * L2 - 1) = common := by
        dsimp only [common]
        omega
      have hhead :
          (Q'.ofNat (2 * L2 - 5) * d 0 + Q'.ofNat 4 * d 0) +
              Q'.ofNat (2 * L2 - 1) * d 0 ≈
            Q'.ofNat common * d 0 :=
        weightedNatAddThree_eqv hheadNat _
      have hterminalNat :
          (2 * n + 3) + 4 * L2 = common + (2 * (n + 2) + 1) := by
        dsimp only [common]
        omega
      have hterminal :
          Q'.ofNat (2 * n + 3) * d (n + 1) +
              Q'.ofNat (4 * L2) * d (n + 1) ≈
            Q'.ofNat common * d (n + 1) +
              Q'.ofNat (2 * (n + 2) + 1) * d (n + 1) :=
        Q'.eqv_trans _ _ _
          (weightedNatAdd_eqv hterminalNat _)
          (Q'.eqv_symm (weightedNatAdd_eqv rfl _))
      have hradial : fixedCutoffTerminalRadialDiagEnvelope w (n + 1) ≈
          (Q'.ofNat (2 * L2 - 5) * d 0 + R) +
            Q'.ofNat (2 * n + 3) * d (n + 1) := by
        unfold fixedCutoffTerminalRadialDiagEnvelope
        exact Q'.eqv_refl _
      exact radialBalance_of_parts
        (fixedCutoffTerminalRadialDiagEnvelope w (n + 1))
        (fixedCutoffTerminalFourFourthMoment w (n + 1))
        (coordNormSq w (n + 1))
        (Q'.ofNat (2 * L2 - 5) * d 0) R
        (Q'.ofNat (2 * n + 3) * d (n + 1))
        (Q'.ofNat 4 * d 0) J
        (Q'.ofNat (4 * L2) * d (n + 1))
        (Q'.ofNat (2 * L2 - 1) * d 0)
        (Q'.ofNat common) (d 0) I (d (n + 1))
        (Q'.ofNat (2 * (n + 2) + 1) * d (n + 1))
        hradial hM hD hhead hmid hterminal

/-- A positive fourth-moment lower bound implies the original sharp radial
upper bound, with no division and no loss of the `341/125` coefficient. -/
theorem terminalRadial_le_of_fourthMoment
    (w : Q') (N : Nat)
    (hMoment :
      let L := Q'.ofNat (N + 1)
      let D := coordNormSq w N
      terminalRadialMomentCoeff * ((L * L) * D) +
          Q'.ofNat (2 * (N + 1) + 1) * fixedCutoffDiagTerm w N <=
        fixedCutoffTerminalFourFourthMoment w N +
          Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
            fixedCutoffDiagTerm w 0 + Q'.ofNat 2 * D) :
    fixedCutoffTerminalRadialDiagEnvelope w N <=
      terminalRadialSplitCoeff *
        ((Q'.ofNat (N + 1) * Q'.ofNat (N + 1)) * coordNormSq w N) := by
  let L := Q'.ofNat (N + 1)
  let D := coordNormSq w N
  let R := fixedCutoffTerminalRadialDiagEnvelope w N
  let M := fixedCutoffTerminalFourFourthMoment w N
  let H := Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
    fixedCutoffDiagTerm w 0
  let T := Q'.ofNat (2 * (N + 1) + 1) * fixedCutoffDiagTerm w N
  let A := terminalRadialMomentCoeff * ((L * L) * D)
  let B := terminalRadialSplitCoeff * ((L * L) * D)
  have hbal := fixedCutoffTerminalRadial_fourthMoment_balance w N
  have hLsq : L * L ≈ Q'.ofNat ((N + 1) * (N + 1)) := by
    dsimp only [L]
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _)
  have hbalance : R + M + H ≈
      Q'.ofNat (4 * ((N + 1) * (N + 1)) - 2) * D + T := by
    dsimp only [R, M, H, T, D]
    exact hbal
  have hm : A + T <= M + H + Q'.ofNat 2 * D := by
    simpa only [A, T, M, H, L, D] using hMoment
  have hwithR := Q'.add_le_add_left R _ _ hm
  have hleft : R + (A + T) ≈ (R + A) + T := by ring_qeqv
  have hright : R + (M + H + Q'.ofNat 2 * D) ≈
      ((Q'.ofNat 4 * (L * L)) * D + T) := by
    refine Q'.eqv_trans _
      ((R + M + H) + Q'.ofNat 2 * D) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat (4 * ((N + 1) * (N + 1)) - 2) * D + T) +
        Q'.ofNat 2 * D) _
      (Q'.add_eqv_congr_right _ _ _ hbalance) ?_
    have hsq : 1 <= (N + 1) * (N + 1) :=
      Nat.mul_le_mul (show 1 <= N + 1 by omega) (show 1 <= N + 1 by omega)
    have hnat :
        (4 * ((N + 1) * (N + 1)) - 2) + 2 =
          4 * ((N + 1) * (N + 1)) := by omega
    have hcoeff := weightedNatAdd_eqv hnat D
    refine Q'.eqv_trans _
      ((Q'.ofNat (4 * ((N + 1) * (N + 1)) - 2) * D +
          Q'.ofNat 2 * D) + T) _ (by ring_qeqv) ?_
    exact Q'.add_eqv_congr_right _ _ T hcoeff
  have hcancelT : R + A <=
      Q'.ofNat (4 * ((N + 1) * (N + 1))) * D :=
    le_of_add_le_add_right_local
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ _ _ hwithR (Q'.le_of_eqv hright)))
  have hfour : Q'.ofNat (4 * ((N + 1) * (N + 1))) * D ≈ A + B := by
    dsimp only [A, B]
    have hc := terminalRadialCoeff_balance
    refine Q'.eqv_trans _
      ((Q'.ofNat 4) * ((L * L) * D)) _
      ?_ ?_
    · refine Q'.eqv_trans _
        ((Q'.ofNat 4 * (L * L)) * D) _ ?_ (Q'.mul_assoc_eqv _ _ _)
      have hnat := HeatKernelRGStep.ofNat_mul_eqv
        4 ((N + 1) * (N + 1))
      have hscale := Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _
        (Q'.eqv_symm hLsq)
      exact Q'.mul_eqv_congr_right _ _ D
        (Q'.eqv_trans _ _ _ hnat hscale)
    refine Q'.eqv_trans _
      ((terminalRadialMomentCoeff + terminalRadialSplitCoeff) *
        ((L * L) * D)) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hc)) ?_
    exact Q'.add_mul_eqv _ _ _
  have hAB : R + A <= B + A := by
    exact Q'.le_trans' _ _ _ hcancelT
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hfour (Q'.add_comm_eqv A B)))
  have hR : R <= B := le_of_add_le_add_right_local hAB
  simpa only [R, B, L, D] using hR

/-! ## Exact integer-theta form for fixed-block certification -/

/-- Fourfold fourth moment written directly in the integer-theta coordinate. -/
def fixedCutoffTerminalIntegerFourFourthSum (w : Q') (N : Nat) : Q' :=
  fsum (fun s =>
    Q'.ofNat (4 * ((s + 1) * (s + 1))) * integerThetaTerm w (s + 1))
    (N + 1)

private theorem scaleWeightedDiag_eqv
    (q a d theta : Q') (hd : q * d ≈ theta) :
    q * (a * d) ≈ a * theta := by
  refine Q'.eqv_trans _ (a * (q * d)) _ (by ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left a _ _ hd

/-- Multiplication by the vacuum power converts the diagonal fourth moment
exactly to the integer-theta fourth sum. -/
theorem terminalFourFourthMoment_theta_eqv (w : Q') (N : Nat) :
    qpow w 2 * fixedCutoffTerminalFourFourthMoment w N ≈
      fixedCutoffTerminalIntegerFourFourthSum w N := by
  unfold fixedCutoffTerminalFourFourthMoment
    fixedCutoffTerminalIntegerFourFourthSum
  refine Q'.eqv_trans _
    (fsum (fun s => qpow w 2 *
      (Q'.ofNat (4 * ((s + 1) * (s + 1))) *
        fixedCutoffDiagTerm w s)) (N + 1)) _ ?_ ?_
  · exact CubeRatioBounds.fsum_const_mul (qpow w 2)
      (fun s => Q'.ofNat (4 * ((s + 1) * (s + 1))) *
        fixedCutoffDiagTerm w s) (N + 1)
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      scaleWeightedDiag_eqv _ _ _ _
        (diagonal_term_theta_eqv w s)) (N + 1)

private theorem scaleMomentLeft_regroup
    (q alpha L D terminalCoeff terminalDiag : Q') :
    q * (alpha * ((L * L) * D) + terminalCoeff * terminalDiag) ≈
      alpha * ((L * L) * (q * D)) + terminalCoeff * (q * terminalDiag) := by
  ring_qeqv

private theorem scaleMomentRight_regroup
    (q moment headCoeff headDiag D : Q') :
    q * (moment + headCoeff * headDiag + Q'.ofNat 2 * D) ≈
      q * moment + headCoeff * (q * headDiag) + Q'.ofNat 2 * (q * D) := by
  ring_qeqv

/-- The integer-theta fourth-moment inequality implies the diagonal-moment
field, hence the original radial upper bound.  Positivity is supplied by the
physical block weight, so the final cancellation remains constructive. -/
theorem terminalRadial_le_of_integerFourFourthMoment
    (k : Nat)
    (hTheta :
      let w := blockWeight k
      let N := blockNcut k
      let L := Q'.ofNat (N + 1)
      let Theta := integerThetaSum w N
      terminalRadialMomentCoeff * ((L * L) * Theta) +
          Q'.ofNat (2 * (N + 1) + 1) * integerThetaTerm w (N + 1) <=
        fixedCutoffTerminalIntegerFourFourthSum w N +
          Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
            integerThetaTerm w 1 + Q'.ofNat 2 * Theta) :
    fixedCutoffTerminalRadialDiagEnvelope (blockWeight k) (blockNcut k) <=
      terminalRadialSplitCoeff *
        ((Q'.ofNat (blockNcut k + 1) * Q'.ofNat (blockNcut k + 1)) *
          coordNormSq (blockWeight k) (blockNcut k)) := by
  let w := blockWeight k
  let N := blockNcut k
  let q := qpow w 2
  let L := Q'.ofNat (N + 1)
  let D := coordNormSq w N
  let Theta := integerThetaSum w N
  let M := fixedCutoffTerminalFourFourthMoment w N
  let Theta4 := fixedCutoffTerminalIntegerFourFourthSum w N
  let d0 := fixedCutoffDiagTerm w 0
  let dN := fixedCutoffDiagTerm w N
  let theta0 := integerThetaTerm w 1
  let thetaN := integerThetaTerm w (N + 1)
  let hCoeff := Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1)
  let tCoeff := Q'.ofNat (2 * (N + 1) + 1)
  have hD : q * D ≈ Theta := by
    simpa only [q, D, Theta] using coordNormSq_theta_eqv w N
  have hM : q * M ≈ Theta4 := by
    simpa only [q, M, Theta4] using terminalFourFourthMoment_theta_eqv w N
  have hd0 : q * d0 ≈ theta0 := by
    simpa only [q, d0, theta0] using diagonal_term_theta_eqv w 0
  have hdN : q * dN ≈ thetaN := by
    simpa only [q, dN, thetaN] using diagonal_term_theta_eqv w N
  have hleft :
      q * (terminalRadialMomentCoeff * ((L * L) * D) + tCoeff * dN) ≈
        terminalRadialMomentCoeff * ((L * L) * Theta) + tCoeff * thetaN := by
    refine Q'.eqv_trans _
      (terminalRadialMomentCoeff * ((L * L) * (q * D)) +
        tCoeff * (q * dN)) _
      (scaleMomentLeft_regroup _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left terminalRadialMomentCoeff _ _
        (Q'.mul_eqv_congr_left (L * L) _ _ hD))
      (Q'.mul_eqv_congr_left tCoeff _ _ hdN)
  have hright : q * (M + hCoeff * d0 + Q'.ofNat 2 * D) ≈
      Theta4 + hCoeff * theta0 + Q'.ofNat 2 * Theta := by
    refine Q'.eqv_trans _
      (q * M + hCoeff * (q * d0) + Q'.ofNat 2 * (q * D)) _
      (scaleMomentRight_regroup _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hM
        (Q'.mul_eqv_congr_left hCoeff _ _ hd0))
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hD)
  have htheta :
      terminalRadialMomentCoeff * ((L * L) * Theta) + tCoeff * thetaN <=
        Theta4 + hCoeff * theta0 + Q'.ofNat 2 * Theta := by
    simpa only [w, N, L, Theta, Theta4, theta0, thetaN, hCoeff, tCoeff]
      using hTheta
  have hscaled :
      q * (terminalRadialMomentCoeff * ((L * L) * D) + tCoeff * dN) <=
        q * (M + hCoeff * d0 + Q'.ofNat 2 * D) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ htheta (Q'.ge_of_eqv hright))
  have hqpos : (0 : Q') < q := by
    dsimp only [q, w]
    exact BondMovingScaledNorm.qpow_pos (blockWeight_pos k) 2
  have hMoment :
      terminalRadialMomentCoeff * ((L * L) * D) + tCoeff * dN <=
        M + hCoeff * d0 + Q'.ofNat 2 * D :=
    Q'.le_of_mul_le_mul_left hscaled hqpos
  simpa only [w, N, L, D, M, d0, dN, hCoeff, tCoeff] using
    terminalRadial_le_of_fourthMoment w N hMoment

/-- Fixed-block-ready post-endpoint frontier in the integer-theta coordinate. -/
structure BlockCompatibleP2TerminalIntegerFourthTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalIntegerFourth : forall k, 7 <= k ->
    let w := blockWeight k
    let N := blockNcut k
    let L := Q'.ofNat (N + 1)
    let Theta := integerThetaSum w N
    terminalRadialMomentCoeff * ((L * L) * Theta) +
        Q'.ofNat (2 * (N + 1) + 1) * integerThetaTerm w (N + 1) <=
      fixedCutoffTerminalIntegerFourFourthSum w N +
        Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
          integerThetaTerm w 1 + Q'.ofNat 2 * Theta
  fineReserve : forall k, 7 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <= D1 * T4

/-- Honest post-endpoint frontier: only the radial lower moment, trapezoid
exchange, and fine reserve remain. -/
structure BlockCompatibleP2TerminalRadialMomentTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalRadialMoment : forall k, 7 <= k ->
    let w0 := blockWeight k
    let N := blockNcut k
    let L := Q'.ofNat (N + 1)
    let D := coordNormSq w0 N
    terminalRadialMomentCoeff * ((L * L) * D) +
        Q'.ofNat (2 * (N + 1) + 1) * fixedCutoffDiagTerm w0 N <=
      fixedCutoffTerminalFourFourthMoment w0 N +
        Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
          fixedCutoffDiagTerm w0 0 + Q'.ofNat 2 * D
  fineReserve : forall k, 7 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <= D1 * T4

/-- Install the proved 640-step endpoint certificate and compile the new
fourth-moment field to the exact physical theta carrier. -/
def BlockCompatibleP2TerminalRadialMomentTailFromSeven.toThetaFactorizedTail
    (T : BlockCompatibleP2TerminalRadialMomentTailFromSeven) :
    BlockCompatibleP2TerminalThetaFactorizedTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalTheta := terminalTheta_fromSeven
  terminalRadial := fun k hk => by
    simpa only [blockLength] using
      terminalRadial_le_of_fourthMoment
        (blockWeight k) (blockNcut k) (T.terminalRadialMoment k hk)
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalRadialMomentTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalRadialMomentTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toThetaFactorizedTail.toCoefficientSandwich

def BlockCompatibleP2TerminalIntegerFourthTailFromSeven.toThetaFactorizedTail
    (T : BlockCompatibleP2TerminalIntegerFourthTailFromSeven) :
    BlockCompatibleP2TerminalThetaFactorizedTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalTheta := terminalTheta_fromSeven
  terminalRadial := fun k hk => by
    simpa only [blockLength] using
      terminalRadial_le_of_integerFourFourthMoment k
        (T.terminalIntegerFourth k hk)
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalIntegerFourthTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalIntegerFourthTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toThetaFactorizedTail.toCoefficientSandwich

#print axioms terminalRadialCoeff_balance
#print axioms fixedCutoffTerminalRadial_fourthMoment_balance
#print axioms terminalRadial_le_of_fourthMoment
#print axioms terminalFourFourthMoment_theta_eqv
#print axioms terminalRadial_le_of_integerFourFourthMoment
#print axioms BlockCompatibleP2TerminalRadialMomentTailFromSeven.toThetaFactorizedTail
#print axioms BlockCompatibleP2TerminalRadialMomentTailFromSeven.toCoefficientSandwich
#print axioms BlockCompatibleP2TerminalIntegerFourthTailFromSeven.toThetaFactorizedTail
#print axioms BlockCompatibleP2TerminalIntegerFourthTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialMoment
