/- Shared-DAG bucket certificates 1128 through 1151. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoSharedDAGBucket1128 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 80, 80, 204, 341]

def cutoffTwoSharedDAGBucket1128Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1128 where
  result := cutoffTwoSharedDAGFactor 775
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1129 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 775]

def cutoffTwoSharedDAGBucket1129Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1129 where
  result := cutoffTwoSharedDAGFactor 776
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1130 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 776]

def cutoffTwoSharedDAGBucket1130Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1130 where
  result := cutoffTwoSharedDAGFactor 777
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1131 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 777]

def cutoffTwoSharedDAGBucket1131Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1131 where
  result := cutoffTwoSharedDAGFactor 778
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1132 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 72, 72, 778]

def cutoffTwoSharedDAGBucket1132Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1132 where
  result := cutoffTwoSharedDAGFactor 542
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1133 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 54, 71, 542]

def cutoffTwoSharedDAGBucket1133Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket1133 where
  result := cutoffTwoSharedDAGFactor 543
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1134 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 80, 80, 118, 204]

def cutoffTwoSharedDAGBucket1134Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1134 where
  result := cutoffTwoSharedDAGFactor 779
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1135 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 779]

def cutoffTwoSharedDAGBucket1135Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1135 where
  result := cutoffTwoSharedDAGFactor 780
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1136 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 780]

def cutoffTwoSharedDAGBucket1136Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1136 where
  result := cutoffTwoSharedDAGFactor 697
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1137 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 44, 80, 118, 427]

def cutoffTwoSharedDAGBucket1137Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1137 where
  result := cutoffTwoSharedDAGFactor 781
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1138 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 781]

def cutoffTwoSharedDAGBucket1138Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1138 where
  result := cutoffTwoSharedDAGFactor 782
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1139 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 782]

def cutoffTwoSharedDAGBucket1139Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1139 where
  result := cutoffTwoSharedDAGFactor 701
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1140 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 44, 80, 240, 427]

def cutoffTwoSharedDAGBucket1140Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1140 where
  result := cutoffTwoSharedDAGFactor 783
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1141 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 783]

def cutoffTwoSharedDAGBucket1141Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1141 where
  result := cutoffTwoSharedDAGFactor 784
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1142 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 784]

def cutoffTwoSharedDAGBucket1142Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1142 where
  result := cutoffTwoSharedDAGFactor 785
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1143 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 75, 75, 99, 785]

def cutoffTwoSharedDAGBucket1143Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1143 where
  result := cutoffTwoSharedDAGFactor 642
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1144 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 642]

def cutoffTwoSharedDAGBucket1144Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1144 where
  result := cutoffTwoSharedDAGFactor 623
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1145 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 49, 682]

def cutoffTwoSharedDAGBucket1145Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1145 where
  result := cutoffTwoSharedDAGFactor 687
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1146 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 688]

def cutoffTwoSharedDAGBucket1146Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1146 where
  result := cutoffTwoSharedDAGFactor 786
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1147 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 72, 72, 786]

def cutoffTwoSharedDAGBucket1147Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1147 where
  result := cutoffTwoSharedDAGFactor 732
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1148 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 49, 686]

def cutoffTwoSharedDAGBucket1148Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1148 where
  result := cutoffTwoSharedDAGFactor 787
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1149 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 59, 787]

def cutoffTwoSharedDAGBucket1149Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1149 where
  result := cutoffTwoSharedDAGFactor 788
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1150 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 788]

def cutoffTwoSharedDAGBucket1150Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1150 where
  result := cutoffTwoSharedDAGFactor 789
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1151 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 789]

def cutoffTwoSharedDAGBucket1151Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1151 where
  result := cutoffTwoSharedDAGFactor 664
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

theorem cutoffTwoSharedDAGBucketShard047_checked :
    boundedLocalEquationCheck 2
        cutoffTwoSharedDAGBucket1151Certificate.result.scope
        cutoffTwoSharedDAGBucket1151Certificate.result.value
        (eliminatedBucketValue 2
          59
          cutoffTwoSharedDAGBucket1151) = true :=
  cutoffTwoSharedDAGBucket1151Certificate.table_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.cutoffTwoSharedDAGBucketShard047_checked
