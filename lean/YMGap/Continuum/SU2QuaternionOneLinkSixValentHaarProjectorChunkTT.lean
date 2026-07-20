/- Four serially compiled 256-case fibers with first forward index pair `11`. -/

import YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjectorChunkTF

namespace YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem oneLink_sixValent_chunk_ttff
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true true false false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_ttft
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true true false true
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_tttf
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true true true false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_tttt
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true true true true
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
