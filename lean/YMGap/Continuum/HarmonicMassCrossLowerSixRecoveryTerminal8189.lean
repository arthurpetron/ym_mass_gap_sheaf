/-
Isolated exact terminal check for the finite lower-six recovery bridge.

The closed rational decision is deliberately kept out of the generic
finite-difference module.  Its sole numerical inputs are the derived exact
endpoint `k=8189`, denominator `D=8191`, and square-root center `c=127`.
-/

import YMGap.Constructive.FinSumAlg
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189

set_option maxHeartbeats 24000000
set_option maxRecDepth 200000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Exact endpoint center: `2*(8189+2)+1 = 16383` lies between
`127^2=16129` and `128^2=16384`. -/
theorem thetaWindowCenter_8189 : thetaWindowCenter 8189 = 127 := by
  unfold thetaWindowCenter thetaWindowLength
  decide

/-! ## Replay-bounded endpoint certificate

The direct decision for the public endpoint statement expands both 254-term
theta masses in one kernel reduction.  Split at mode 202, which balances the
cubic cumulative cost of the strict-fold powers, check two conservative
rational lower bounds independently, and reassemble them by `Q'.eqv`.  This
changes no mathematical statement and keeps every numerical fact inside the
ordinary kernel rather than a native evaluator. -/

/- The largest exponent below is `255^2 = 65025`.  Reducing the strict-fold
`qpow` at that exponent is both stack-linear and allocation-quadratic in the
growing exact integers.  The certificate evaluates powers in base-256 blocks:
at most 254 multiplications of `w^256`, followed by at most 255 residual
multiplications.  The public strict-fold power is retained and connected by
the proved semigroup laws. -/
private def terminalBlockedQpow (w : Q') (n : Nat) : Q' :=
  qpow (qpow w 256) (n / 256) * qpow w (n % 256)

private theorem qpow_eqv_terminalBlockedQpow (w : Q') (n : Nat) :
    qpow w n ≈ terminalBlockedQpow w n := by
  have hdecomp : 256 * (n / 256) + n % 256 = n := Nat.div_add_mod n 256
  have hsplit :
      qpow w n ≈
        qpow w (256 * (n / 256)) * qpow w (n % 256) := by
    simpa only [hdecomp] using
      (YMGap.Continuum.HeatKernelRGStep.qpow_add
        w (256 * (n / 256)) (n % 256))
  have hiter := YMGap.Continuum.HeatKernelRGStep.qpow_qpow
    w 256 (n / 256)
  unfold terminalBlockedQpow
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hiter))

private def terminalIntegerThetaTerm (n : Nat) : Q' :=
  Q'.ofNat (n * n) *
    terminalBlockedQpow (harmW 8189 * harmW 8189) (n * n)

private def terminalHalfThetaTerm (n : Nat) : Q' :=
  Q'.ofNat (n * (n + 1)) *
    terminalBlockedQpow (harmW 8189 * harmW 8189) (n * (n + 1))

private theorem integerThetaTerm_eqv_terminal (n : Nat) :
    integerThetaTerm (harmW 8189) n ≈ terminalIntegerThetaTerm n := by
  unfold integerThetaTerm terminalIntegerThetaTerm
  exact Q'.mul_eqv_congr_left _ _ _
    (qpow_eqv_terminalBlockedQpow
      (harmW 8189 * harmW 8189) (n * n))

private theorem halfThetaTerm_eqv_terminal (n : Nat) :
    halfThetaTerm (harmW 8189) n ≈ terminalHalfThetaTerm n := by
  unfold halfThetaTerm terminalHalfThetaTerm
  exact Q'.mul_eqv_congr_left _ _ _
    (qpow_eqv_terminalBlockedQpow
      (harmW 8189 * harmW 8189) (n * (n + 1)))

private theorem integerThetaFinSum_eqv_terminal (start count : Nat) :
    finSum (fun j => integerThetaTerm (harmW 8189) (j + start)) count ≈
      finSum (fun j => terminalIntegerThetaTerm (j + start)) count :=
  RationalTail.finSum_eqv_congr _ _
    (fun j => integerThetaTerm_eqv_terminal (j + start)) count

private theorem halfThetaFinSum_eqv_terminal (start count : Nat) :
    finSum (fun j => halfThetaTerm (harmW 8189) (j + start)) count ≈
      finSum (fun j => terminalHalfThetaTerm (j + start)) count :=
  RationalTail.finSum_eqv_congr _ _
    (fun j => halfThetaTerm_eqv_terminal (j + start)) count

private def terminalChunkSum
    (f : Nat → Q') (start : Nat) : List Nat → Q'
  | [] => 0
  | count :: counts =>
      finSum (fun j => f (j + start)) count +
        terminalChunkSum f (start + count) counts

private theorem finSum_eqv_terminalChunkSum
    (f : Nat → Q') (start : Nat) : ∀ counts : List Nat,
    finSum (fun j => f (j + start)) counts.sum ≈
      terminalChunkSum f start counts
  | [] => Q'.eqv_refl 0
  | count :: counts => by
      refine Q'.eqv_trans _
        (finSum (fun j => f (j + start)) count +
          finSum (fun j => f (j + (start + count))) counts.sum) _ ?_ ?_
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (YMGap.Constructive.finSum_split
            (fun j => f (j + start)) count counts.sum)
      · exact Q'.add_eqv_congr_left _ _ _
          (finSum_eqv_terminalChunkSum f (start + count) counts)

private def terminalSparseCoefficient : Q' :=
  qpow ((1 : Q') + harmW 8189) 3 +
    -(Q'.ofNat 6 * (harmU 8189 * harmU 8189))

private def terminalHalfCoefficient : Q' :=
  -(Q'.ofNat 8 * harmW 8189)

/- These schedules approximately equalize `Σ n²`, the dominant exact-rational
cost of each block.  Consequently the late, large-exponent blocks contain far
fewer modes than the early blocks. -/
private def terminalHeadWidths : List Nat :=
  [94, 24, 18, 14, 12, 11, 10, 10, 9]

private def terminalTailWidths : List Nat :=
  [8, 7, 7, 6, 6, 6, 5, 5, 2]

private theorem terminalHeadWidths_sum : terminalHeadWidths.sum = 202 := by decide
private theorem terminalTailWidths_sum : terminalTailWidths.sum = 52 := by decide

private def terminalIntegerBlock (start count : Nat) : Q' :=
  finSum (fun j => terminalIntegerThetaTerm (j + start)) count

private def terminalHalfBlock (start count : Nat) : Q' :=
  finSum (fun j => terminalHalfThetaTerm (j + start)) count

private def terminalBlockSlice (start count : Nat) : Q' :=
  terminalSparseCoefficient * terminalIntegerBlock start count +
    terminalHalfCoefficient * terminalHalfBlock start count

private def terminalSliceChunks (start : Nat) : List Nat → Q'
  | [] => 0
  | count :: counts =>
      terminalBlockSlice start count +
        terminalSliceChunks (start + count) counts

private theorem terminal_scaled_zero (S H : Q') :
    S * (0 : Q') + H * (0 : Q') ≈ 0 := by
  refine Q'.eqv_trans _ ((0 : Q') + H * 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_zero_eqv S)
  refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv H)
  · exact QPoly.q_zero_add_eqv 0

private theorem terminal_scaled_add_rearrange
    (S H I Irest J Jrest : Q') :
    S * (I + Irest) + H * (J + Jrest) ≈
      (S * I + H * J) + (S * Irest + H * Jrest) := by
  refine Q'.eqv_trans _
    ((S * I + S * Irest) + H * (J + Jrest)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv S I Irest)
  refine Q'.eqv_trans _
    ((S * I + S * Irest) + (H * J + H * Jrest)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv H J Jrest)
  · exact Q'.add_swap_inner (S * I) (S * Irest) (H * J) (H * Jrest)

private theorem scaled_terminalChunkSums_eqv_slices
    (start : Nat) : ∀ counts : List Nat,
    terminalSparseCoefficient *
          terminalChunkSum terminalIntegerThetaTerm start counts +
        terminalHalfCoefficient *
          terminalChunkSum terminalHalfThetaTerm start counts ≈
      terminalSliceChunks start counts
  | [] => terminal_scaled_zero _ _
  | count :: counts => by
      refine Q'.eqv_trans _
        (terminalBlockSlice start count +
          (terminalSparseCoefficient *
              terminalChunkSum terminalIntegerThetaTerm (start + count) counts +
            terminalHalfCoefficient *
              terminalChunkSum terminalHalfThetaTerm (start + count) counts)) _ ?_ ?_
      · exact terminal_scaled_add_rearrange _ _ _ _ _ _
      · exact Q'.add_eqv_congr_left _ _ _
          (scaled_terminalChunkSums_eqv_slices (start + count) counts)

private def terminalFirstBlockAssembly : Q' :=
  terminalSliceChunks 1 terminalHeadWidths

private def terminalIntegerHead : Q' :=
  finSum (fun j => terminalIntegerThetaTerm (j + 1)) 202

private def terminalIntegerTail : Q' :=
  finSum (fun j => terminalIntegerThetaTerm (j + 203)) 52

private def terminalHalfHead : Q' :=
  finSum (fun j => terminalHalfThetaTerm (j + 1)) 202

private def terminalHalfTail : Q' :=
  finSum (fun j => terminalHalfThetaTerm (j + 203)) 52

private def terminalEndpoint : Q' :=
  Q'.ofNat 4 * terminalIntegerThetaTerm 255

private def terminalSecondBlockAssembly : Q' :=
  terminalSliceChunks 203 terminalTailWidths + terminalEndpoint

private def terminalOriginalEndpoint : Q' :=
  Q'.ofNat 4 * integerThetaTerm (harmW 8189) 255

private theorem terminalOriginalEndpoint_eqv :
    terminalOriginalEndpoint ≈ terminalEndpoint := by
  unfold terminalOriginalEndpoint terminalEndpoint
  exact Q'.mul_eqv_congr_left _ _ _ (integerThetaTerm_eqv_terminal 255)

private def terminalFirstSlice : Q' :=
  terminalSparseCoefficient * terminalIntegerHead +
    terminalHalfCoefficient * terminalHalfHead

private def terminalSecondSlice : Q' :=
  terminalSparseCoefficient * terminalIntegerTail +
      terminalHalfCoefficient * terminalHalfTail +
    terminalEndpoint

private theorem terminalIntegerHead_eqv_chunks :
    terminalIntegerHead ≈
      terminalChunkSum terminalIntegerThetaTerm 1 terminalHeadWidths := by
  unfold terminalIntegerHead
  simpa only [terminalHeadWidths_sum] using
    (finSum_eqv_terminalChunkSum
      terminalIntegerThetaTerm 1 terminalHeadWidths)

private theorem terminalHalfHead_eqv_chunks :
    terminalHalfHead ≈
      terminalChunkSum terminalHalfThetaTerm 1 terminalHeadWidths := by
  unfold terminalHalfHead
  simpa only [terminalHeadWidths_sum] using
    (finSum_eqv_terminalChunkSum
      terminalHalfThetaTerm 1 terminalHeadWidths)

private theorem terminalIntegerTail_eqv_chunks :
    terminalIntegerTail ≈
      terminalChunkSum terminalIntegerThetaTerm 203 terminalTailWidths := by
  unfold terminalIntegerTail
  simpa only [terminalTailWidths_sum] using
    (finSum_eqv_terminalChunkSum
      terminalIntegerThetaTerm 203 terminalTailWidths)

private theorem terminalHalfTail_eqv_chunks :
    terminalHalfTail ≈
      terminalChunkSum terminalHalfThetaTerm 203 terminalTailWidths := by
  unfold terminalHalfTail
  simpa only [terminalTailWidths_sum] using
    (finSum_eqv_terminalChunkSum
      terminalHalfThetaTerm 203 terminalTailWidths)

private theorem terminalFirstSlice_eqv_blocks :
    terminalFirstSlice ≈ terminalFirstBlockAssembly := by
  have hInteger :
      terminalSparseCoefficient * terminalIntegerHead ≈
        terminalSparseCoefficient *
          terminalChunkSum terminalIntegerThetaTerm 1 terminalHeadWidths :=
    Q'.mul_eqv_congr_left _ _ _ terminalIntegerHead_eqv_chunks
  have hHalf :
      terminalHalfCoefficient * terminalHalfHead ≈
        terminalHalfCoefficient *
          terminalChunkSum terminalHalfThetaTerm 1 terminalHeadWidths :=
    Q'.mul_eqv_congr_left _ _ _ terminalHalfHead_eqv_chunks
  have hScaled :
      terminalFirstSlice ≈
        terminalSparseCoefficient *
            terminalChunkSum terminalIntegerThetaTerm 1 terminalHeadWidths +
          terminalHalfCoefficient *
            terminalChunkSum terminalHalfThetaTerm 1 terminalHeadWidths := by
    unfold terminalFirstSlice
    exact Q'.eqv_trans _
      (terminalSparseCoefficient *
          terminalChunkSum terminalIntegerThetaTerm 1 terminalHeadWidths +
        terminalHalfCoefficient * terminalHalfHead) _
      (Q'.add_eqv_congr_right _ _ _ hInteger)
      (Q'.add_eqv_congr_left _ _ _ hHalf)
  exact Q'.eqv_trans _ _ _ hScaled
    (scaled_terminalChunkSums_eqv_slices 1 terminalHeadWidths)

private theorem terminalSecondSlice_eqv_blocks :
    terminalSecondSlice ≈ terminalSecondBlockAssembly := by
  have hInteger :
      terminalSparseCoefficient * terminalIntegerTail ≈
        terminalSparseCoefficient *
          terminalChunkSum terminalIntegerThetaTerm 203 terminalTailWidths :=
    Q'.mul_eqv_congr_left _ _ _ terminalIntegerTail_eqv_chunks
  have hHalf :
      terminalHalfCoefficient * terminalHalfTail ≈
        terminalHalfCoefficient *
          terminalChunkSum terminalHalfThetaTerm 203 terminalTailWidths :=
    Q'.mul_eqv_congr_left _ _ _ terminalHalfTail_eqv_chunks
  have hScaled :
      terminalSparseCoefficient * terminalIntegerTail +
          terminalHalfCoefficient * terminalHalfTail ≈
        terminalSparseCoefficient *
            terminalChunkSum terminalIntegerThetaTerm 203 terminalTailWidths +
          terminalHalfCoefficient *
            terminalChunkSum terminalHalfThetaTerm 203 terminalTailWidths := by
    exact Q'.eqv_trans _
      (terminalSparseCoefficient *
          terminalChunkSum terminalIntegerThetaTerm 203 terminalTailWidths +
        terminalHalfCoefficient * terminalHalfTail) _
      (Q'.add_eqv_congr_right _ _ _ hInteger)
      (Q'.add_eqv_congr_left _ _ _ hHalf)
  unfold terminalSecondSlice terminalSecondBlockAssembly
  exact Q'.eqv_trans _
    ((terminalSparseCoefficient *
          terminalChunkSum terminalIntegerThetaTerm 203 terminalTailWidths +
        terminalHalfCoefficient *
          terminalChunkSum terminalHalfThetaTerm 203 terminalTailWidths) +
      terminalEndpoint) _
    (Q'.add_eqv_congr_right _ _ _ hScaled)
    (Q'.add_eqv_congr_right _ _ _
      (scaled_terminalChunkSums_eqv_slices 203 terminalTailWidths))

/-! ### Cost-balanced closed block checks -/

private theorem terminalBlock_1_94_lower :
    Q'.mkPos (-3988472632) 1000000 (by decide) ≤
      terminalBlockSlice 1 94 := by decide

private theorem terminalBlock_95_24_lower :
    Q'.mkPos 2193840017 1000000 (by decide) ≤
      terminalBlockSlice 95 24 := by decide

private theorem terminalBlock_119_18_lower :
    Q'.mkPos 1020038372 1000000 (by decide) ≤
      terminalBlockSlice 119 18 := by decide

private theorem terminalBlock_137_14_lower :
    Q'.mkPos 422203735 1000000 (by decide) ≤
      terminalBlockSlice 137 14 := by decide

private theorem terminalBlock_151_12_lower :
    Q'.mkPos 188448556 1000000 (by decide) ≤
      terminalBlockSlice 151 12 := by decide

private theorem terminalBlock_163_11_lower :
    Q'.mkPos 88253860 1000000 (by decide) ≤
      terminalBlockSlice 163 11 := by decide

private theorem terminalBlock_174_10_lower :
    Q'.mkPos 40324579 1000000 (by decide) ≤
      terminalBlockSlice 174 10 := by decide

private theorem terminalBlock_184_10_lower :
    Q'.mkPos 19722169 1000000 (by decide) ≤
      terminalBlockSlice 184 10 := by decide

private theorem terminalBlock_194_9_lower :
    Q'.mkPos 8475610 1000000 (by decide) ≤
      terminalBlockSlice 194 9 := by decide

private theorem terminalBlock_203_8_lower :
    Q'.mkPos 3714425 1000000 (by decide) ≤
      terminalBlockSlice 203 8 := by decide

private theorem terminalBlock_211_7_lower :
    Q'.mkPos 1680831 1000000 (by decide) ≤
      terminalBlockSlice 211 7 := by decide

private theorem terminalBlock_218_7_lower :
    Q'.mkPos 886001 1000000 (by decide) ≤
      terminalBlockSlice 218 7 := by decide

private theorem terminalBlock_225_6_lower :
    Q'.mkPos 406907 1000000 (by decide) ≤
      terminalBlockSlice 225 6 := by decide

private theorem terminalBlock_231_6_lower :
    Q'.mkPos 224935 1000000 (by decide) ≤
      terminalBlockSlice 231 6 := by decide

private theorem terminalBlock_237_6_lower :
    Q'.mkPos 121895 1000000 (by decide) ≤
      terminalBlockSlice 237 6 := by decide

private theorem terminalBlock_243_5_lower :
    Q'.mkPos 56653 1000000 (by decide) ≤
      terminalBlockSlice 243 5 := by decide

private theorem terminalBlock_248_5_lower :
    Q'.mkPos 32984 1000000 (by decide) ≤
      terminalBlockSlice 248 5 := by decide

private theorem terminalBlock_253_2_lower :
    Q'.mkPos 8870 1000000 (by decide) ≤
      terminalBlockSlice 253 2 := by decide

private theorem terminalEndpoint_lower :
    Q'.mkPos 33063 1000000 (by decide) ≤ terminalEndpoint := by decide

private def terminalFirstLowerAssembly : Q' :=
  Q'.mkPos (-3988472632) 1000000 (by decide) +
    (Q'.mkPos 2193840017 1000000 (by decide) +
      (Q'.mkPos 1020038372 1000000 (by decide) +
        (Q'.mkPos 422203735 1000000 (by decide) +
          (Q'.mkPos 188448556 1000000 (by decide) +
            (Q'.mkPos 88253860 1000000 (by decide) +
              (Q'.mkPos 40324579 1000000 (by decide) +
                (Q'.mkPos 19722169 1000000 (by decide) +
                  (Q'.mkPos 8475610 1000000 (by decide) + 0))))))))

private theorem terminalFirstLowerAssembly_le_blocks :
    terminalFirstLowerAssembly ≤ terminalFirstBlockAssembly := by
  unfold terminalFirstLowerAssembly terminalFirstBlockAssembly
  simpa only [terminalHeadWidths, terminalSliceChunks] using
    (Q'.add_le_add terminalBlock_1_94_lower
      (Q'.add_le_add terminalBlock_95_24_lower
        (Q'.add_le_add terminalBlock_119_18_lower
          (Q'.add_le_add terminalBlock_137_14_lower
            (Q'.add_le_add terminalBlock_151_12_lower
              (Q'.add_le_add terminalBlock_163_11_lower
                (Q'.add_le_add terminalBlock_174_10_lower
                  (Q'.add_le_add terminalBlock_184_10_lower
                    (Q'.add_le_add terminalBlock_194_9_lower
                      (Q'.le_refl' 0))))))))))

private theorem terminalFirstRounded_lower :
    Q'.mkPos (-7165734) 1000000 (by decide) ≤
      terminalFirstLowerAssembly := by decide

/-- Summing the independently checked head blocks loses only four millionths
against the earlier monolithic enclosure. -/
private theorem terminalFirstSlice_lower :
    Q'.mkPos (-7165734) 1000000 (by decide) ≤
      terminalFirstSlice :=
  Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ terminalFirstRounded_lower
      terminalFirstLowerAssembly_le_blocks)
    (Q'.le_of_eqv (Q'.eqv_symm terminalFirstSlice_eqv_blocks))

private def terminalSecondLowerAssembly : Q' :=
  (Q'.mkPos 3714425 1000000 (by decide) +
    (Q'.mkPos 1680831 1000000 (by decide) +
      (Q'.mkPos 886001 1000000 (by decide) +
        (Q'.mkPos 406907 1000000 (by decide) +
          (Q'.mkPos 224935 1000000 (by decide) +
            (Q'.mkPos 121895 1000000 (by decide) +
              (Q'.mkPos 56653 1000000 (by decide) +
                (Q'.mkPos 32984 1000000 (by decide) +
                  (Q'.mkPos 8870 1000000 (by decide) + 0))))))))) +
    Q'.mkPos 33063 1000000 (by decide)

private theorem terminalSecondLowerAssembly_le_blocks :
    terminalSecondLowerAssembly ≤ terminalSecondBlockAssembly := by
  unfold terminalSecondLowerAssembly terminalSecondBlockAssembly
  simpa only [terminalTailWidths, terminalSliceChunks] using
    (Q'.add_le_add
      (Q'.add_le_add terminalBlock_203_8_lower
        (Q'.add_le_add terminalBlock_211_7_lower
          (Q'.add_le_add terminalBlock_218_7_lower
            (Q'.add_le_add terminalBlock_225_6_lower
              (Q'.add_le_add terminalBlock_231_6_lower
                (Q'.add_le_add terminalBlock_237_6_lower
                  (Q'.add_le_add terminalBlock_243_5_lower
                    (Q'.add_le_add terminalBlock_248_5_lower
                      (Q'.add_le_add terminalBlock_253_2_lower
                        (Q'.le_refl' 0))))))))))
      terminalEndpoint_lower)

private theorem terminalSecondRounded_lower :
    Q'.mkPos 7166564 1000000 (by decide) ≤
      terminalSecondLowerAssembly := by decide

/-- The independently checked tail blocks and endpoint retain a positive
six-decimal enclosure strong enough for the terminal payment. -/
private theorem terminalSecondSlice_lower :
    Q'.mkPos 7166564 1000000 (by decide) ≤
      terminalSecondSlice :=
  Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ terminalSecondRounded_lower
      terminalSecondLowerAssembly_le_blocks)
    (Q'.le_of_eqv (Q'.eqv_symm terminalSecondSlice_eqv_blocks))

private theorem terminalIntegerHead_eqv_original :
    finSum (fun j => integerThetaTerm (harmW 8189) (j + 1)) 202 ≈
      terminalIntegerHead := by
  unfold terminalIntegerHead
  exact integerThetaFinSum_eqv_terminal 1 202

private theorem terminalIntegerTail_eqv_original :
    finSum
        (fun j => integerThetaTerm (harmW 8189) (202 + j + 1)) 52 ≈
      terminalIntegerTail := by
  unfold terminalIntegerTail
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (integerThetaFinSum_eqv_terminal 203 52)

private theorem terminalHalfHead_eqv_original :
    finSum (fun j => halfThetaTerm (harmW 8189) (j + 1)) 202 ≈
      terminalHalfHead := by
  unfold terminalHalfHead
  exact halfThetaFinSum_eqv_terminal 1 202

private theorem terminalHalfTail_eqv_original :
    finSum
        (fun j => halfThetaTerm (harmW 8189) (202 + j + 1)) 52 ≈
      terminalHalfTail := by
  unfold terminalHalfTail
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (halfThetaFinSum_eqv_terminal 203 52)

private theorem lowerSixFixedIntegerMass_8189_127_eqv_terminal :
    lowerSixFixedIntegerMass 8189 127 ≈
      terminalIntegerHead + terminalIntegerTail := by
  have hSplit :
      lowerSixFixedIntegerMass 8189 127 ≈
        finSum (fun j => integerThetaTerm (harmW 8189) (j + 1)) 202 +
          finSum
            (fun j => integerThetaTerm (harmW 8189) (202 + j + 1)) 52 := by
    unfold lowerSixFixedIntegerMass
    simpa only using
      (YMGap.Constructive.finSum_split
        (fun j => integerThetaTerm (harmW 8189) (j + 1)) 202 52)
  have hTransport :
      finSum (fun j => integerThetaTerm (harmW 8189) (j + 1)) 202 +
          finSum
            (fun j => integerThetaTerm (harmW 8189) (202 + j + 1)) 52 ≈
        terminalIntegerHead + terminalIntegerTail := by
    exact Q'.eqv_trans _
      (terminalIntegerHead +
        finSum
          (fun j => integerThetaTerm (harmW 8189) (202 + j + 1)) 52) _
      (Q'.add_eqv_congr_right _ _ _ terminalIntegerHead_eqv_original)
      (Q'.add_eqv_congr_left _ _ _ terminalIntegerTail_eqv_original)
  exact Q'.eqv_trans _ _ _ hSplit hTransport

private theorem lowerSixFixedHalfMass_8189_127_eqv_terminal :
    lowerSixFixedHalfMass 8189 127 ≈
      terminalHalfHead + terminalHalfTail := by
  have hSplit :
      lowerSixFixedHalfMass 8189 127 ≈
        finSum (fun j => halfThetaTerm (harmW 8189) (j + 1)) 202 +
          finSum
            (fun j => halfThetaTerm (harmW 8189) (202 + j + 1)) 52 := by
    unfold lowerSixFixedHalfMass
    simpa only using
      (YMGap.Constructive.finSum_split
        (fun j => halfThetaTerm (harmW 8189) (j + 1)) 202 52)
  have hTransport :
      finSum (fun j => halfThetaTerm (harmW 8189) (j + 1)) 202 +
          finSum
            (fun j => halfThetaTerm (harmW 8189) (202 + j + 1)) 52 ≈
        terminalHalfHead + terminalHalfTail := by
    exact Q'.eqv_trans _
      (terminalHalfHead +
        finSum
          (fun j => halfThetaTerm (harmW 8189) (202 + j + 1)) 52) _
      (Q'.add_eqv_congr_right _ _ _ terminalHalfHead_eqv_original)
      (Q'.add_eqv_congr_left _ _ _ terminalHalfTail_eqv_original)
  exact Q'.eqv_trans _ _ _ hSplit hTransport

private theorem terminalHalfMass_form (H : Q') :
    -(Q'.ofNat 8 * (harmW 8189 * H)) ≈ terminalHalfCoefficient * H := by
  unfold terminalHalfCoefficient
  refine Q'.eqv_trans _ (-((Q'.ofNat 8 * harmW 8189) * H)) _ ?_ ?_
  · exact Q'.neg_eqv_congr _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 8) (harmW 8189) H))
  · exact Q'.eqv_symm (Q'.neg_mul_eqv (Q'.ofNat 8 * harmW 8189) H)

private theorem lowerSixFixedCenterSparseSlack_8189_127_eqv_mass_endpoint :
    lowerSixFixedCenterSparseSlack 8189 127 ≈
      (terminalSparseCoefficient * lowerSixFixedIntegerMass 8189 127 +
          terminalHalfCoefficient * lowerSixFixedHalfMass 8189 127) +
        terminalOriginalEndpoint := by
  unfold lowerSixFixedCenterSparseSlack terminalSparseCoefficient
    terminalOriginalEndpoint
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (terminalHalfMass_form (lowerSixFixedHalfMass 8189 127)))

private theorem terminalScaledMass_eqv_chunks :
    terminalSparseCoefficient * lowerSixFixedIntegerMass 8189 127 +
        terminalHalfCoefficient * lowerSixFixedHalfMass 8189 127 ≈
      terminalSparseCoefficient *
          (terminalIntegerHead + terminalIntegerTail) +
        terminalHalfCoefficient *
          (terminalHalfHead + terminalHalfTail) := by
  have hInteger :
      terminalSparseCoefficient * lowerSixFixedIntegerMass 8189 127 ≈
        terminalSparseCoefficient *
          (terminalIntegerHead + terminalIntegerTail) :=
    Q'.mul_eqv_congr_left _ _ _
      lowerSixFixedIntegerMass_8189_127_eqv_terminal
  have hHalf :
      terminalHalfCoefficient * lowerSixFixedHalfMass 8189 127 ≈
        terminalHalfCoefficient *
          (terminalHalfHead + terminalHalfTail) :=
    Q'.mul_eqv_congr_left _ _ _
      lowerSixFixedHalfMass_8189_127_eqv_terminal
  exact Q'.eqv_trans _
    (terminalSparseCoefficient *
        (terminalIntegerHead + terminalIntegerTail) +
      terminalHalfCoefficient * lowerSixFixedHalfMass 8189 127) _
    (Q'.add_eqv_congr_right _ _ _ hInteger)
    (Q'.add_eqv_congr_left _ _ _ hHalf)

private theorem terminalChunkedMassEndpoint_eqv_slices :
    (terminalSparseCoefficient *
          (terminalIntegerHead + terminalIntegerTail) +
        terminalHalfCoefficient *
          (terminalHalfHead + terminalHalfTail)) +
      terminalEndpoint ≈
        terminalFirstSlice + terminalSecondSlice := by
  have hrearrange := terminal_scaled_add_rearrange
    terminalSparseCoefficient terminalHalfCoefficient
    terminalIntegerHead terminalIntegerTail terminalHalfHead terminalHalfTail
  unfold terminalFirstSlice terminalSecondSlice
  exact Q'.eqv_trans _
    ((terminalSparseCoefficient * terminalIntegerHead +
        terminalHalfCoefficient * terminalHalfHead) +
      (terminalSparseCoefficient * terminalIntegerTail +
        terminalHalfCoefficient * terminalHalfTail) + terminalEndpoint) _
    (Q'.add_eqv_congr_right _ _ _ hrearrange)
    (Q'.add_assoc_eqv _ _ _)

private theorem lowerSixFixedCenterSparseSlack_8189_127_eqv_slices :
    lowerSixFixedCenterSparseSlack 8189 127 ≈
      terminalFirstSlice + terminalSecondSlice := by
  exact Q'.eqv_trans _
    ((terminalSparseCoefficient * lowerSixFixedIntegerMass 8189 127 +
        terminalHalfCoefficient * lowerSixFixedHalfMass 8189 127) +
      terminalOriginalEndpoint) _
    lowerSixFixedCenterSparseSlack_8189_127_eqv_mass_endpoint
    (Q'.eqv_trans _
      ((terminalSparseCoefficient *
            (terminalIntegerHead + terminalIntegerTail) +
          terminalHalfCoefficient *
            (terminalHalfHead + terminalHalfTail)) +
        terminalOriginalEndpoint) _
      (Q'.add_eqv_congr_right _ _ _ terminalScaledMass_eqv_chunks)
      (Q'.eqv_trans _
        ((terminalSparseCoefficient *
              (terminalIntegerHead + terminalIntegerTail) +
            terminalHalfCoefficient *
              (terminalHalfHead + terminalHalfTail)) +
          terminalEndpoint) _
        (Q'.add_eqv_congr_left _ _ _ terminalOriginalEndpoint_eqv)
        terminalChunkedMassEndpoint_eqv_slices))

/-- The load-bearing closed-rational endpoint check.  No measured value is
present in the statement or proof. -/
theorem lowerSixFixedCenterSparseSlack_8189_127_nonnegative :
    (0 : Q') ≤ lowerSixFixedCenterSparseSlack 8189 127 := by
  let lowerHead := Q'.mkPos (-7165734) 1000000 (by decide)
  let lowerTail := Q'.mkPos 7166564 1000000 (by decide)
  have hFloor : (0 : Q') ≤ lowerHead + lowerTail := by
    decide
  have hSlices : lowerHead + lowerTail ≤
      terminalFirstSlice + terminalSecondSlice := by
    exact Q'.le_trans' _ (terminalFirstSlice + lowerTail) _
      (Q'.add_le_add_right _ _ _ terminalFirstSlice_lower)
      (Q'.add_le_add_left _ _ _ terminalSecondSlice_lower)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ hFloor hSlices)
    (Q'.le_of_eqv
      (Q'.eqv_symm lowerSixFixedCenterSparseSlack_8189_127_eqv_slices))

theorem lowerSixCenterSlack_8189_nonnegative :
    (0 : Q') ≤ lowerSixCenterSlack 8189 := by
  have hfixedEq := lowerSixCenterSlack_eqv_fixed 8189
  rw [thetaWindowCenter_8189] at hfixedEq
  have hsparseEq := lowerSixFixedCenterSlack_eqv_sparse 8189 127
  have hfixed : (0 : Q') ≤ lowerSixFixedCenterSlack 8189 127 :=
    Q'.le_trans' _ _ _
      lowerSixFixedCenterSparseSlack_8189_127_nonnegative
      (Q'.le_of_eqv (Q'.eqv_symm hsparseEq))
  exact Q'.le_trans' _ _ _ hfixed
    (Q'.le_of_eqv (Q'.eqv_symm hfixedEq))

theorem lowerSixRecoverySlack_8189_nonnegative :
    (0 : Q') ≤ lowerSixRecoverySlack 8189 := by
  exact Q'.le_trans' _ _ _ lowerSixCenterSlack_8189_nonnegative
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixRecoverySlack_eqv_centerSlack 8189)))

private theorem recovery_slack_as_subtraction (k : Nat) :
    lowerSixRecoverySlack k ≈
      lowerSixRecoveryReserve k + -(-lowerSixWindowPrefix k) := by
  unfold lowerSixRecoverySlack
  refine Q'.eqv_trans _
    (lowerSixRecoveryReserve k + lowerSixWindowPrefix k) _
    (Q'.add_comm_eqv _ _) ?_
  exact Q'.add_eqv_congr_left (lowerSixRecoveryReserve k) _ _
    (Q'.eqv_symm (Q'.neg_neg_eqv (lowerSixWindowPrefix k)))

/-- Exact recovery payment at the terminal finite scale. -/
theorem lowerSixRecoveryPayment_8189 :
    -lowerSixWindowPrefix 8189 ≤ lowerSixRecoveryReserve 8189 := by
  have hsub : (0 : Q') ≤
      lowerSixRecoveryReserve 8189 + -(-lowerSixWindowPrefix 8189) :=
    Q'.le_trans' _ _ _ lowerSixRecoverySlack_8189_nonnegative
      (Q'.le_of_eqv (recovery_slack_as_subtraction 8189))
  exact Q'.le_of_sub_nonneg hsub

/-- The exact physical anchor required by the production tail theorem. -/
theorem lowerSixInteriorPayment_8189_nonnegative :
    (0 : Q') ≤ lowerSixInteriorPayment 8189 := by
  unfold lowerSixInteriorPayment
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual
    (by decide) lowerSixRecoveryPayment_8189

#print axioms thetaWindowCenter_8189
#print axioms lowerSixFixedCenterSparseSlack_8189_127_nonnegative
#print axioms lowerSixCenterSlack_8189_nonnegative
#print axioms lowerSixRecoveryPayment_8189
#print axioms lowerSixInteriorPayment_8189_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189
