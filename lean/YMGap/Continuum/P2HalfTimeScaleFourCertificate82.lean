import YMGap.Continuum.P2HalfTimeScaleFourCertificate

namespace YMGap.Continuum.P2HalfTimeScaleFourCertificate

set_option maxHeartbeats 12000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 300000

theorem physicalHalfTimeScaleFourCheck_82_97 :
    halfTimeIntegralTailBlockCheck 3071 3072 79 82 16 = true := by
  decide

end YMGap.Continuum.P2HalfTimeScaleFourCertificate

#print axioms YMGap.Continuum.P2HalfTimeScaleFourCertificate.physicalHalfTimeScaleFourCheck_82_97
