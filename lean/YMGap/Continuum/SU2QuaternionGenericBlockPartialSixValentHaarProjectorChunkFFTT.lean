/- One serially compiled 256-case fiber with the first four selectors `0011`. -/

import YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjectorChunkFFTF

namespace YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem genericBlock_partial_sixValent_chunk_fftt
    (block : Nat)
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    GenericBlockPartialSixValentProjectorStatement block
      false false true true
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  solve_generic_block_partial_six_valent_fiber
    thirdForwardRow, thirdForwardColumn,
    firstReverseRow, firstReverseColumn,
    secondReverseRow, secondReverseColumn,
    thirdReverseRow, thirdReverseColumn

#print axioms genericBlock_partial_sixValent_chunk_fftt

end YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector
