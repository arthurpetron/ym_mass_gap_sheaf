/-
# Aggregated power terms for `178605 * BASE_FULL_NUM`

The seven imported shards are the 691 nonzero integer power terms emitted by
the authoritative exact generator.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms0
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms1
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms2
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms3
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms4
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms5
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms6

namespace YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms

def tailBaseClearedTerms : List (Nat × Nat × Int) :=
  tailBaseClearedTerms0 ++ tailBaseClearedTerms1 ++
    tailBaseClearedTerms2 ++ tailBaseClearedTerms3 ++
      tailBaseClearedTerms4 ++ tailBaseClearedTerms5 ++
        tailBaseClearedTerms6

end YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms
