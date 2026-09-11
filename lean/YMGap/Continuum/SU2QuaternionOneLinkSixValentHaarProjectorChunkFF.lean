/- Four serially compiled 256-case fibers with first forward index pair `00`. -/

import YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjectorCore

namespace YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem oneLink_sixValent_chunk_ffff
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false false false false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_ffft
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false false false true
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_fftf
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false false true false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  cases thirdForwardRow <;> cases thirdForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    cases thirdReverseRow <;> cases thirdReverseColumn <;>
    constructor <;> decide

theorem oneLink_sixValent_chunk_fftt
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    OneLinkSixValentProjectorStatement
      false false true true
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
