/- Shared-DAG bucket certificates 0 through 23. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoSharedDAGBucket0000 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [12, 25, 36, 36, 36]

def cutoffTwoSharedDAGBucket0000Certificate : CheckedBucketResult 2
    38 cutoffTwoSharedDAGBucket0000 where
  result := cutoffTwoSharedDAGFactor 81
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0001 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [7, 26, 32, 32, 32]

def cutoffTwoSharedDAGBucket0001Certificate : CheckedBucketResult 2
    22 cutoffTwoSharedDAGBucket0001 where
  result := cutoffTwoSharedDAGFactor 82
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0002 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [5, 27, 30, 30, 30]

def cutoffTwoSharedDAGBucket0002Certificate : CheckedBucketResult 2
    14 cutoffTwoSharedDAGBucket0002 where
  result := cutoffTwoSharedDAGFactor 83
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0003 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [2, 24, 48, 48, 83]

def cutoffTwoSharedDAGBucket0003Certificate : CheckedBucketResult 2
    5 cutoffTwoSharedDAGBucket0003 where
  result := cutoffTwoSharedDAGFactor 84
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0004 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [10, 29, 34, 34, 34]

def cutoffTwoSharedDAGBucket0004Certificate : CheckedBucketResult 2
    31 cutoffTwoSharedDAGBucket0004 where
  result := cutoffTwoSharedDAGFactor 85
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0005 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [11, 35, 35, 35, 85]

def cutoffTwoSharedDAGBucket0005Certificate : CheckedBucketResult 2
    32 cutoffTwoSharedDAGBucket0005 where
  result := cutoffTwoSharedDAGFactor 86
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0006 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [18, 31, 39, 39, 39]

def cutoffTwoSharedDAGBucket0006Certificate : CheckedBucketResult 2
    56 cutoffTwoSharedDAGBucket0006 where
  result := cutoffTwoSharedDAGFactor 87
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0007 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [19, 40, 40, 40, 87]

def cutoffTwoSharedDAGBucket0007Certificate : CheckedBucketResult 2
    58 cutoffTwoSharedDAGBucket0007 where
  result := cutoffTwoSharedDAGFactor 88
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0008 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [8, 52, 52, 82, 86]

def cutoffTwoSharedDAGBucket0008Certificate : CheckedBucketResult 2
    23 cutoffTwoSharedDAGBucket0008 where
  result := cutoffTwoSharedDAGFactor 89
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0009 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [13, 47, 47, 81, 88]

def cutoffTwoSharedDAGBucket0009Certificate : CheckedBucketResult 2
    40 cutoffTwoSharedDAGBucket0009 where
  result := cutoffTwoSharedDAGFactor 90
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0010 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [15, 28, 37, 37, 37]

def cutoffTwoSharedDAGBucket0010Certificate : CheckedBucketResult 2
    47 cutoffTwoSharedDAGBucket0010 where
  result := cutoffTwoSharedDAGFactor 91
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0011 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [17, 38, 38, 38, 91]

def cutoffTwoSharedDAGBucket0011Certificate : CheckedBucketResult 2
    50 cutoffTwoSharedDAGBucket0011 where
  result := cutoffTwoSharedDAGFactor 92
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0012 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [4, 51, 51, 84, 89]

def cutoffTwoSharedDAGBucket0012Certificate : CheckedBucketResult 2
    13 cutoffTwoSharedDAGBucket0012 where
  result := cutoffTwoSharedDAGFactor 93
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0013 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [1, 45, 45, 93]

def cutoffTwoSharedDAGBucket0013Certificate : CheckedBucketResult 2
    4 cutoffTwoSharedDAGBucket0013 where
  result := cutoffTwoSharedDAGFactor 94
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0014 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [14, 50, 50, 90, 92]

def cutoffTwoSharedDAGBucket0014Certificate : CheckedBucketResult 2
    41 cutoffTwoSharedDAGBucket0014 where
  result := cutoffTwoSharedDAGFactor 95
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0015 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 44, 44, 94, 95]

def cutoffTwoSharedDAGBucket0015Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket0015 where
  result := cutoffTwoSharedDAGFactor 96
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0016 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 49, 96]

def cutoffTwoSharedDAGBucket0016Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket0016 where
  result := cutoffTwoSharedDAGFactor 97
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0017 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 46, 97]

def cutoffTwoSharedDAGBucket0017Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket0017 where
  result := cutoffTwoSharedDAGFactor 98
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0018 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [21, 33, 41, 41, 41]

def cutoffTwoSharedDAGBucket0018Certificate : CheckedBucketResult 2
    65 cutoffTwoSharedDAGBucket0018 where
  result := cutoffTwoSharedDAGFactor 99
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0019 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 53, 98, 99]

def cutoffTwoSharedDAGBucket0019Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket0019 where
  result := cutoffTwoSharedDAGFactor 100
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0020 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 56, 100]

def cutoffTwoSharedDAGBucket0020Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket0020 where
  result := cutoffTwoSharedDAGFactor 101
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0021 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 54, 54, 101]

def cutoffTwoSharedDAGBucket0021Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket0021 where
  result := cutoffTwoSharedDAGFactor 102
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0022 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [23, 43, 43, 43, 102]

def cutoffTwoSharedDAGBucket0022Certificate : CheckedBucketResult 2
    68 cutoffTwoSharedDAGBucket0022 where
  result := cutoffTwoSharedDAGFactor 103
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket0023 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [22, 42, 42, 42, 103]

def cutoffTwoSharedDAGBucket0023Certificate : CheckedBucketResult 2
    67 cutoffTwoSharedDAGBucket0023 where
  result := cutoffTwoSharedDAGFactor 104
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

theorem cutoffTwoSharedDAGBucketShard000_checked :
    boundedLocalEquationCheck 2
        cutoffTwoSharedDAGBucket0023Certificate.result.scope
        cutoffTwoSharedDAGBucket0023Certificate.result.value
        (eliminatedBucketValue 2
          67
          cutoffTwoSharedDAGBucket0023) = true :=
  cutoffTwoSharedDAGBucket0023Certificate.table_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.cutoffTwoSharedDAGBucketShard000_checked
