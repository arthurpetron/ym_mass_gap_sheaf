/- Four serially compiled 256-case fibers with first forward index pair `10`. -/

import YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjectorChunkFT

namespace YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem oneLink_sixValent_chunk_tfff
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true false false false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_tfft
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true false false true
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_tftf
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true false true false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_tftt
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      true false true true
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
