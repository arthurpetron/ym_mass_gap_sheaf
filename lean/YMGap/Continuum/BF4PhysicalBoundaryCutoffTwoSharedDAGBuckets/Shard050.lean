/- Shared-DAG bucket certificates 1200 through 1223. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoSharedDAGBucket1200 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 73, 73, 333]

def cutoffTwoSharedDAGBucket1200Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1200 where
  result := cutoffTwoSharedDAGFactor 334
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1201 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 80, 80, 340, 341]

def cutoffTwoSharedDAGBucket1201Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1201 where
  result := cutoffTwoSharedDAGFactor 342
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1202 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 73, 73, 343]

def cutoffTwoSharedDAGBucket1202Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1202 where
  result := cutoffTwoSharedDAGFactor 344
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1203 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 80, 80, 118, 340]

def cutoffTwoSharedDAGBucket1203Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1203 where
  result := cutoffTwoSharedDAGFactor 813
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1204 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 62, 813]

def cutoffTwoSharedDAGBucket1204Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1204 where
  result := cutoffTwoSharedDAGFactor 814
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1205 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 73, 73, 814]

def cutoffTwoSharedDAGBucket1205Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1205 where
  result := cutoffTwoSharedDAGFactor 815
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1206 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 66, 99, 815]

def cutoffTwoSharedDAGBucket1206Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1206 where
  result := cutoffTwoSharedDAGFactor 816
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1207 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 816]

def cutoffTwoSharedDAGBucket1207Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1207 where
  result := cutoffTwoSharedDAGFactor 552
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1208 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 353]

def cutoffTwoSharedDAGBucket1208Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1208 where
  result := cutoffTwoSharedDAGFactor 817
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1209 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 817]

def cutoffTwoSharedDAGBucket1209Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1209 where
  result := cutoffTwoSharedDAGFactor 818
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1210 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 818]

def cutoffTwoSharedDAGBucket1210Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1210 where
  result := cutoffTwoSharedDAGFactor 521
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1211 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 770]

def cutoffTwoSharedDAGBucket1211Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1211 where
  result := cutoffTwoSharedDAGFactor 362
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1212 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 56, 363]

def cutoffTwoSharedDAGBucket1212Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1212 where
  result := cutoffTwoSharedDAGFactor 569
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1213 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 73, 73, 771]

def cutoffTwoSharedDAGBucket1213Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1213 where
  result := cutoffTwoSharedDAGFactor 819
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1214 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 66, 99, 819]

def cutoffTwoSharedDAGBucket1214Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1214 where
  result := cutoffTwoSharedDAGFactor 820
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1215 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 68, 820]

def cutoffTwoSharedDAGBucket1215Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1215 where
  result := cutoffTwoSharedDAGFactor 821
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1216 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 54, 67, 821]

def cutoffTwoSharedDAGBucket1216Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket1216 where
  result := cutoffTwoSharedDAGFactor 675
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1217 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 66, 99, 702]

def cutoffTwoSharedDAGBucket1217Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1217 where
  result := cutoffTwoSharedDAGFactor 822
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1218 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 822]

def cutoffTwoSharedDAGBucket1218Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1218 where
  result := cutoffTwoSharedDAGFactor 704
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1219 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 54, 71, 704]

def cutoffTwoSharedDAGBucket1219Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket1219 where
  result := cutoffTwoSharedDAGFactor 599
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1220 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 62, 711]

def cutoffTwoSharedDAGBucket1220Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1220 where
  result := cutoffTwoSharedDAGFactor 823
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1221 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 823]

def cutoffTwoSharedDAGBucket1221Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1221 where
  result := cutoffTwoSharedDAGFactor 824
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1222 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 824]

def cutoffTwoSharedDAGBucket1222Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1222 where
  result := cutoffTwoSharedDAGFactor 825
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1223 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 825]

def cutoffTwoSharedDAGBucket1223Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1223 where
  result := cutoffTwoSharedDAGFactor 826
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

theorem cutoffTwoSharedDAGBucketShard050_checked :
    boundedLocalEquationCheck 2
        cutoffTwoSharedDAGBucket1223Certificate.result.scope
        cutoffTwoSharedDAGBucket1223Certificate.result.value
        (eliminatedBucketValue 2
          59
          cutoffTwoSharedDAGBucket1223) = true :=
  cutoffTwoSharedDAGBucket1223Certificate.table_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.cutoffTwoSharedDAGBucketShard050_checked
