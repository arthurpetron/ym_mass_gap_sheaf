import YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns

namespace ScratchOutwardProjection

open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns

set_option maxHeartbeats 20000
set_option maxRecDepth 100000

abbrev localQueries : ComponentSubsupportQueryTriple :=
  (outwardXQuery,
    YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns.outwardYQuery,
    YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns.outwardZQuery)

theorem test :
    outwardCoarseQueries =
      (outwardXQuery,
        YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns.outwardYQuery,
        YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns.outwardZQuery) := by
  unfold outwardCoarseQueries
  exact Eq.refl _

end ScratchOutwardProjection
