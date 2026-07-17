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

def tailBaseChartBase : Nat :=
  392

def tailBaseTableScale : Int :=
  22821784381319623030372961946148450127886102071075625082347942135934891824794025997391167262758930737305500070552215954799984640000

def tailBaseChartQuotient : Int :=
  127777970276977817140466179256731055277769950847264214788768187541977502448386248970584066866879038869603314971877696339968000

def tailBaseBernsteinRows : List (List Int) :=
  tailBaseBernsteinRows0 ++ tailBaseBernsteinRows1 ++
    tailBaseBernsteinRows2 ++ tailBaseBernsteinRows3 ++
      tailBaseBernsteinRows4 ++ tailBaseBernsteinRows5

end YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows
