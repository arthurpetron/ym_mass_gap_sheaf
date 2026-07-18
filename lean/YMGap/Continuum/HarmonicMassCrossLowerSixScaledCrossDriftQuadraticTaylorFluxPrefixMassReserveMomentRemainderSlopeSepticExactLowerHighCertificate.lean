import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk0
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk1
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk2
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk3
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk4
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk5
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk6
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk7
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk8

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

open YMGap.Constructive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

private theorem all_of_take_five_and_drop {xs : List PE}
    (hhead : (xs.take 5).all highRowPred = true)
    (htail : (xs.drop 5).all highRowPred = true) :
    xs.all highRowPred = true := by
  rw [← List.take_append_drop 5 xs, List.all_append, hhead, htail]
  rfl

private theorem all_tail (n : Nat)
    (hhead : ((highRowsTail n).take 5).all highRowPred = true)
    (htail : (highRowsTail (n + 1)).all highRowPred = true) :
    (highRowsTail n).all highRowPred = true :=
  all_of_take_five_and_drop hhead (by
    simpa [highRowsTail] using htail)

/-- Kernel-checked row certificate: every coefficient in every univariate
`M` row is nonnegative. -/
theorem pExactLowerHigh_rows_coefficients_nonnegative :
    highRows.all highRowPred = true := by
  simpa [highRowsTail] using
    all_tail 0 highRows_chunk0
      (all_tail 1 highRows_chunk1
        (all_tail 2 highRows_chunk2
          (all_tail 3 highRows_chunk3
            (all_tail 4 highRows_chunk4
              (all_tail 5 highRows_chunk5
                (all_tail 6 highRows_chunk6
                  (all_tail 7 highRows_chunk7 highRows_chunk8)))))))

/-- The independently cached row certificates imply nonnegativity of the
cleared high-mode numerator at every nonnegative pair `(M,Z)`. -/
theorem pExactLowerHigh_eval_nonnegative (M Z : Q')
    (hM : (0 : Q') ≤ M) (hZ : (0 : Q') ≤ Z) :
    (0 : Q') ≤ RingNormaliser.eval (highEnvironment M Z) pExactLowerHigh :=
  pExactLowerHigh_eval_nonnegative_of_rows
    pExactLowerHigh_rows_coefficients_nonnegative M Z hM hZ

#print axioms pExactLowerHigh_rows_coefficients_nonnegative
#print axioms pExactLowerHigh_eval_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
