/- Shared-DAG bucket certificates 1440 through 1463. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoSharedDAGBucket1440 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 44, 80, 346, 427]

def cutoffTwoSharedDAGBucket1440Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1440 where
  result := cutoffTwoSharedDAGFactor 918
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1441 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 76, 76, 918]

def cutoffTwoSharedDAGBucket1441Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1441 where
  result := cutoffTwoSharedDAGFactor 919
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1442 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 919]

def cutoffTwoSharedDAGBucket1442Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1442 where
  result := cutoffTwoSharedDAGFactor 920
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1443 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 75, 75, 99, 920]

def cutoffTwoSharedDAGBucket1443Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1443 where
  result := cutoffTwoSharedDAGFactor 885
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1444 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 72, 72, 706]

def cutoffTwoSharedDAGBucket1444Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1444 where
  result := cutoffTwoSharedDAGFactor 707
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1445 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 888]

def cutoffTwoSharedDAGBucket1445Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1445 where
  result := cutoffTwoSharedDAGFactor 921
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1446 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 921]

def cutoffTwoSharedDAGBucket1446Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1446 where
  result := cutoffTwoSharedDAGFactor 922
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1447 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 53, 75, 99, 922]

def cutoffTwoSharedDAGBucket1447Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1447 where
  result := cutoffTwoSharedDAGFactor 923
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1448 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 923]

def cutoffTwoSharedDAGBucket1448Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1448 where
  result := cutoffTwoSharedDAGFactor 829
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1449 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 76, 76, 892]

def cutoffTwoSharedDAGBucket1449Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1449 where
  result := cutoffTwoSharedDAGFactor 924
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1450 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 924]

def cutoffTwoSharedDAGBucket1450Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1450 where
  result := cutoffTwoSharedDAGFactor 736
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1451 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 72, 72, 721]

def cutoffTwoSharedDAGBucket1451Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1451 where
  result := cutoffTwoSharedDAGFactor 829
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1452 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 54, 67, 829]

def cutoffTwoSharedDAGBucket1452Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket1452 where
  result := cutoffTwoSharedDAGFactor 738
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1453 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 76, 76, 382]

def cutoffTwoSharedDAGBucket1453Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1453 where
  result := cutoffTwoSharedDAGFactor 925
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1454 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 925]

def cutoffTwoSharedDAGBucket1454Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1454 where
  result := cutoffTwoSharedDAGFactor 926
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1455 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [9, 75, 75, 99, 926]

def cutoffTwoSharedDAGBucket1455Certificate : CheckedBucketResult 2
    29 cutoffTwoSharedDAGBucket1455 where
  result := cutoffTwoSharedDAGFactor 927
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1456 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 56, 72, 927]

def cutoffTwoSharedDAGBucket1456Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1456 where
  result := cutoffTwoSharedDAGFactor 749
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1457 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [16, 54, 71, 749]

def cutoffTwoSharedDAGBucket1457Certificate : CheckedBucketResult 2
    49 cutoffTwoSharedDAGBucket1457 where
  result := cutoffTwoSharedDAGFactor 743
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1458 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 44, 80, 118, 398]

def cutoffTwoSharedDAGBucket1458Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1458 where
  result := cutoffTwoSharedDAGFactor 928
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1459 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 49, 76, 928]

def cutoffTwoSharedDAGBucket1459Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1459 where
  result := cutoffTwoSharedDAGFactor 929
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1460 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [6, 46, 73, 929]

def cutoffTwoSharedDAGBucket1460Certificate : CheckedBucketResult 2
    20 cutoffTwoSharedDAGBucket1460 where
  result := cutoffTwoSharedDAGFactor 747
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1461 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [20, 72, 72, 748]

def cutoffTwoSharedDAGBucket1461Certificate : CheckedBucketResult 2
    59 cutoffTwoSharedDAGBucket1461 where
  result := cutoffTwoSharedDAGFactor 749
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1462 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [0, 80, 80, 341, 408]

def cutoffTwoSharedDAGBucket1462Certificate : CheckedBucketResult 2
    2 cutoffTwoSharedDAGBucket1462 where
  result := cutoffTwoSharedDAGFactor 409
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

def cutoffTwoSharedDAGBucket1463 : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList [3, 76, 76, 409]

def cutoffTwoSharedDAGBucket1463Certificate : CheckedBucketResult 2
    11 cutoffTwoSharedDAGBucket1463 where
  result := cutoffTwoSharedDAGFactor 410
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide

theorem cutoffTwoSharedDAGBucketShard060_checked :
    boundedLocalEquationCheck 2
        cutoffTwoSharedDAGBucket1463Certificate.result.scope
        cutoffTwoSharedDAGBucket1463Certificate.result.value
        (eliminatedBucketValue 2
          11
          cutoffTwoSharedDAGBucket1463) = true :=
  cutoffTwoSharedDAGBucket1463Certificate.table_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.cutoffTwoSharedDAGBucketShard060_checked
