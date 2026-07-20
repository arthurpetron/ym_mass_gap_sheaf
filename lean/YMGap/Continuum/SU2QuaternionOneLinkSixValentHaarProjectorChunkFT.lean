/- Four serially compiled 256-case fibers with first forward index pair `01`. -/

import YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjectorChunkFF

namespace YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem oneLink_sixValent_chunk_ftff
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false true false false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_ftft
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false true false true
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_fttf
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false true true false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_fttt
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false true true true
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

end YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
