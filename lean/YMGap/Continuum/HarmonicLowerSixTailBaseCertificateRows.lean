/-
# Aggregated exact Bernstein rows for the high-branch Base certificate

The six imported shards contain the 42 by 23 dense nonnegative table emitted
by `computations/HarmonicLowerSixTailBaseCertificate_generate.py`.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows0
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows1
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows2
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows3
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows4
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows5

namespace YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows

def tailBaseTableScale : Int :=
  758404417999238467456280659047188707220682937435270598745023227240282112518189216053787618463871928960335841894697497059426926278392542874606665272032610464054948118539746738202266095860000

def tailBaseChartQuotient : Int :=
  4246266442704506970444728081784881202769703745333392675149202022565337546643090708847947249314811617593773085270275171800492294607612009040097787139400411321379290157273014407224132000

def tailBaseBernsteinRows : List (List Int) :=
  tailBaseBernsteinRows0 ++ tailBaseBernsteinRows1 ++
    tailBaseBernsteinRows2 ++ tailBaseBernsteinRows3 ++
      tailBaseBernsteinRows4 ++ tailBaseBernsteinRows5

end YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows
