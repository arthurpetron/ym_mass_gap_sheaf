/- Shared-DAG bucket certificates 1080 through 1103. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoSharedDAGBucket1080 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [1, 78, 78, 128]

def cutoffTwoSharedDAGBucket1080Certificate : CheckedBucketResult 2
    4 cutoffTwoSharedDAGBucket1080 where
  result := cutoffTwoSharedDAGFactor 351
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1081 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 80, 80, 234, 351]

def cutoffTwoSharedDAGBucket1081Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1081 where
  result := cutoffTwoSharedDAGFactor 750
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1082 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 62, 750]

def cutoffTwoSharedDAGBucket1082Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1082 where
  result := cutoffTwoSharedDAGFactor 546
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1083 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 666]

def cutoffTwoSharedDAGBucket1083Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1083 where
  result := cutoffTwoSharedDAGFactor 667
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1084 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 668]

def cutoffTwoSharedDAGBucket1084Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1084 where
  result := cutoffTwoSharedDAGFactor 751
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1085 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 68, 751]

def cutoffTwoSharedDAGBucket1085Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1085 where
  result := cutoffTwoSharedDAGFactor 508
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1086 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 62, 670]

def cutoffTwoSharedDAGBucket1086Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1086 where
  result := cutoffTwoSharedDAGFactor 752
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1087 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 752]

def cutoffTwoSharedDAGBucket1087Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1087 where
  result := cutoffTwoSharedDAGFactor 753
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1088 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 75, 75, 99, 753]

def cutoffTwoSharedDAGBucket1088Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1088 where
  result := cutoffTwoSharedDAGFactor 754
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1089 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 68, 754]

def cutoffTwoSharedDAGBucket1089Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1089 where
  result := cutoffTwoSharedDAGFactor 182
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1090 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 80, 80, 204, 234]

def cutoffTwoSharedDAGBucket1090Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1090 where
  result := cutoffTwoSharedDAGFactor 755
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1091 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 755]

def cutoffTwoSharedDAGBucket1091Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1091 where
  result := cutoffTwoSharedDAGFactor 756
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1092 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 756]

def cutoffTwoSharedDAGBucket1092Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1092 where
  result := cutoffTwoSharedDAGFactor 757
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1093 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 757]

def cutoffTwoSharedDAGBucket1093Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1093 where
  result := cutoffTwoSharedDAGFactor 758
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1094 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 68, 758]

def cutoffTwoSharedDAGBucket1094Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1094 where
  result := cutoffTwoSharedDAGFactor 759
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1095 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 54, 71, 759]

def cutoffTwoSharedDAGBucket1095Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket1095 where
  result := cutoffTwoSharedDAGFactor 760
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1096 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [23, 43, 43, 43, 760]

def cutoffTwoSharedDAGBucket1096Certificate : CheckedBucketResult 2
    68 cutoffTwoSharedDAGBucket1096 where
  result := cutoffTwoSharedDAGFactor 761
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1097 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [22, 42, 42, 42, 761]

def cutoffTwoSharedDAGBucket1097Certificate : CheckedBucketResult 2
    67 cutoffTwoSharedDAGBucket1097 where
  result := cutoffTwoSharedDAGFactor 513
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1098 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 44, 80, 234, 427]

def cutoffTwoSharedDAGBucket1098Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1098 where
  result := cutoffTwoSharedDAGFactor 762
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1099 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 762]

def cutoffTwoSharedDAGBucket1099Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1099 where
  result := cutoffTwoSharedDAGFactor 763
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1100 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 763]

def cutoffTwoSharedDAGBucket1100Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1100 where
  result := cutoffTwoSharedDAGFactor 764
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1101 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 75, 75, 99, 764]

def cutoffTwoSharedDAGBucket1101Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1101 where
  result := cutoffTwoSharedDAGFactor 751
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1102 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 71, 71, 508]

def cutoffTwoSharedDAGBucket1102Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket1102 where
  result := cutoffTwoSharedDAGFactor 183
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1103 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 49, 670]

def cutoffTwoSharedDAGBucket1103Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1103 where
  result := cutoffTwoSharedDAGFactor 765
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

theorem cutoffTwoSharedDAGBucketShard045_checked :
    boundedLocalEquationCheck 2
        cutoffTwoSharedDAGBucket1103Certificate.result.scope
        cutoffTwoSharedDAGBucket1103Certificate.result.value
        (eliminatedBucketValue 2
          11
          cutoffTwoSharedDAGBucket1103) = true :=
  cutoffTwoSharedDAGBucket1103Certificate.table_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.cutoffTwoSharedDAGBucketShard045_checked
