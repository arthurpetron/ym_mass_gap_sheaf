import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row0
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row1
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row2
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row3
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row4

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

private theorem all_of_take_one_and_drop {xs : List PE}
    (hhead : (xs.take 1).all highRowPred = true)
    (htail : (xs.drop 1).all highRowPred = true) :
    xs.all highRowPred = true := by
  rw [← List.take_append_drop 1 xs, List.all_append, hhead, htail]
  rfl

private theorem all_block_tail (n : Nat)
    (hhead : ((highRowsBlockTail 3 n).take 1).all highRowPred = true)
    (htail : (highRowsBlockTail 3 (n + 1)).all highRowPred = true) :
    (highRowsBlockTail 3 n).all highRowPred = true :=
  all_of_take_one_and_drop hhead (by
    simpa [highRowsBlockTail] using htail)

private theorem highRows_block3_empty :
    (highRowsBlockTail 3 5).all highRowPred = true := by decide

theorem highRows_chunk3 :
    ((highRowsTail 3).take 5).all highRowPred = true := by
  simpa [highRowsBlock, highRowsBlockTail] using
    all_block_tail 0 highRows_block3_row0
      (all_block_tail 1 highRows_block3_row1
        (all_block_tail 2 highRows_block3_row2
          (all_block_tail 3 highRows_block3_row3
            (all_block_tail 4 highRows_block3_row4 highRows_block3_empty))))

#print axioms highRows_chunk3

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
