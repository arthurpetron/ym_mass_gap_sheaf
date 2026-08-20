/- Composed exact certificate for the widest cutoff-two elimination step 13. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk15
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk16
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk17
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk18
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk19
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk20
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk21
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk22
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk23
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk24
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk25
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Chunk26

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step13ChunkCertificate81 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 81) :=
  .done step13_tail_81_empty

def step13ChunkCertificate80 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 80) :=
  .step step13_chunk_80 step13ChunkCertificate81

def step13ChunkCertificate79 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 79) :=
  .step step13_chunk_79 step13ChunkCertificate80

def step13ChunkCertificate78 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 78) :=
  .step step13_chunk_78 step13ChunkCertificate79

def step13ChunkCertificate77 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 77) :=
  .step step13_chunk_77 step13ChunkCertificate78

def step13ChunkCertificate76 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 76) :=
  .step step13_chunk_76 step13ChunkCertificate77

def step13ChunkCertificate75 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 75) :=
  .step step13_chunk_75 step13ChunkCertificate76

def step13ChunkCertificate74 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 74) :=
  .step step13_chunk_74 step13ChunkCertificate75

def step13ChunkCertificate73 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 73) :=
  .step step13_chunk_73 step13ChunkCertificate74

def step13ChunkCertificate72 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 72) :=
  .step step13_chunk_72 step13ChunkCertificate73

def step13ChunkCertificate71 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 71) :=
  .step step13_chunk_71 step13ChunkCertificate72

def step13ChunkCertificate70 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 70) :=
  .step step13_chunk_70 step13ChunkCertificate71

def step13ChunkCertificate69 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 69) :=
  .step step13_chunk_69 step13ChunkCertificate70

def step13ChunkCertificate68 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 68) :=
  .step step13_chunk_68 step13ChunkCertificate69

def step13ChunkCertificate67 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 67) :=
  .step step13_chunk_67 step13ChunkCertificate68

def step13ChunkCertificate66 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 66) :=
  .step step13_chunk_66 step13ChunkCertificate67

def step13ChunkCertificate65 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 65) :=
  .step step13_chunk_65 step13ChunkCertificate66

def step13ChunkCertificate64 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 64) :=
  .step step13_chunk_64 step13ChunkCertificate65

def step13ChunkCertificate63 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 63) :=
  .step step13_chunk_63 step13ChunkCertificate64

def step13ChunkCertificate62 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 62) :=
  .step step13_chunk_62 step13ChunkCertificate63

def step13ChunkCertificate61 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 61) :=
  .step step13_chunk_61 step13ChunkCertificate62

def step13ChunkCertificate60 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 60) :=
  .step step13_chunk_60 step13ChunkCertificate61

def step13ChunkCertificate59 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 59) :=
  .step step13_chunk_59 step13ChunkCertificate60

def step13ChunkCertificate58 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 58) :=
  .step step13_chunk_58 step13ChunkCertificate59

def step13ChunkCertificate57 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 57) :=
  .step step13_chunk_57 step13ChunkCertificate58

def step13ChunkCertificate56 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 56) :=
  .step step13_chunk_56 step13ChunkCertificate57

def step13ChunkCertificate55 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 55) :=
  .step step13_chunk_55 step13ChunkCertificate56

def step13ChunkCertificate54 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 54) :=
  .step step13_chunk_54 step13ChunkCertificate55

def step13ChunkCertificate53 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 53) :=
  .step step13_chunk_53 step13ChunkCertificate54

def step13ChunkCertificate52 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 52) :=
  .step step13_chunk_52 step13ChunkCertificate53

def step13ChunkCertificate51 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 51) :=
  .step step13_chunk_51 step13ChunkCertificate52

def step13ChunkCertificate50 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 50) :=
  .step step13_chunk_50 step13ChunkCertificate51

def step13ChunkCertificate49 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 49) :=
  .step step13_chunk_49 step13ChunkCertificate50

def step13ChunkCertificate48 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 48) :=
  .step step13_chunk_48 step13ChunkCertificate49

def step13ChunkCertificate47 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 47) :=
  .step step13_chunk_47 step13ChunkCertificate48

def step13ChunkCertificate46 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 46) :=
  .step step13_chunk_46 step13ChunkCertificate47

def step13ChunkCertificate45 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 45) :=
  .step step13_chunk_45 step13ChunkCertificate46

def step13ChunkCertificate44 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 44) :=
  .step step13_chunk_44 step13ChunkCertificate45

def step13ChunkCertificate43 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 43) :=
  .step step13_chunk_43 step13ChunkCertificate44

def step13ChunkCertificate42 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 42) :=
  .step step13_chunk_42 step13ChunkCertificate43

def step13ChunkCertificate41 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 41) :=
  .step step13_chunk_41 step13ChunkCertificate42

def step13ChunkCertificate40 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 40) :=
  .step step13_chunk_40 step13ChunkCertificate41

def step13ChunkCertificate39 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 39) :=
  .step step13_chunk_39 step13ChunkCertificate40

def step13ChunkCertificate38 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 38) :=
  .step step13_chunk_38 step13ChunkCertificate39

def step13ChunkCertificate37 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 37) :=
  .step step13_chunk_37 step13ChunkCertificate38

def step13ChunkCertificate36 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 36) :=
  .step step13_chunk_36 step13ChunkCertificate37

def step13ChunkCertificate35 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 35) :=
  .step step13_chunk_35 step13ChunkCertificate36

def step13ChunkCertificate34 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 34) :=
  .step step13_chunk_34 step13ChunkCertificate35

def step13ChunkCertificate33 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 33) :=
  .step step13_chunk_33 step13ChunkCertificate34

def step13ChunkCertificate32 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 32) :=
  .step step13_chunk_32 step13ChunkCertificate33

def step13ChunkCertificate31 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 31) :=
  .step step13_chunk_31 step13ChunkCertificate32

def step13ChunkCertificate30 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 30) :=
  .step step13_chunk_30 step13ChunkCertificate31

def step13ChunkCertificate29 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 29) :=
  .step step13_chunk_29 step13ChunkCertificate30

def step13ChunkCertificate28 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 28) :=
  .step step13_chunk_28 step13ChunkCertificate29

def step13ChunkCertificate27 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 27) :=
  .step step13_chunk_27 step13ChunkCertificate28

def step13ChunkCertificate26 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 26) :=
  .step step13_chunk_26 step13ChunkCertificate27

def step13ChunkCertificate25 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 25) :=
  .step step13_chunk_25 step13ChunkCertificate26

def step13ChunkCertificate24 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 24) :=
  .step step13_chunk_24 step13ChunkCertificate25

def step13ChunkCertificate23 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 23) :=
  .step step13_chunk_23 step13ChunkCertificate24

def step13ChunkCertificate22 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 22) :=
  .step step13_chunk_22 step13ChunkCertificate23

def step13ChunkCertificate21 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 21) :=
  .step step13_chunk_21 step13ChunkCertificate22

def step13ChunkCertificate20 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 20) :=
  .step step13_chunk_20 step13ChunkCertificate21

def step13ChunkCertificate19 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 19) :=
  .step step13_chunk_19 step13ChunkCertificate20

def step13ChunkCertificate18 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 18) :=
  .step step13_chunk_18 step13ChunkCertificate19

def step13ChunkCertificate17 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 17) :=
  .step step13_chunk_17 step13ChunkCertificate18

def step13ChunkCertificate16 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 16) :=
  .step step13_chunk_16 step13ChunkCertificate17

def step13ChunkCertificate15 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 15) :=
  .step step13_chunk_15 step13ChunkCertificate16

def step13ChunkCertificate14 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 14) :=
  .step step13_chunk_14 step13ChunkCertificate15

def step13ChunkCertificate13 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 13) :=
  .step step13_chunk_13 step13ChunkCertificate14

def step13ChunkCertificate12 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 12) :=
  .step step13_chunk_12 step13ChunkCertificate13

def step13ChunkCertificate11 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 11) :=
  .step step13_chunk_11 step13ChunkCertificate12

def step13ChunkCertificate10 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 10) :=
  .step step13_chunk_10 step13ChunkCertificate11

def step13ChunkCertificate09 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 9) :=
  .step step13_chunk_09 step13ChunkCertificate10

def step13ChunkCertificate08 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 8) :=
  .step step13_chunk_08 step13ChunkCertificate09

def step13ChunkCertificate07 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 7) :=
  .step step13_chunk_07 step13ChunkCertificate08

def step13ChunkCertificate06 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 6) :=
  .step step13_chunk_06 step13ChunkCertificate07

def step13ChunkCertificate05 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 5) :=
  .step step13_chunk_05 step13ChunkCertificate06

def step13ChunkCertificate04 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 4) :=
  .step step13_chunk_04 step13ChunkCertificate05

def step13ChunkCertificate03 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 3) :=
  .step step13_chunk_03 step13ChunkCertificate04

def step13ChunkCertificate02 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 2) :=
  .step step13_chunk_02 step13ChunkCertificate03

def step13ChunkCertificate01 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 1) :=
  .step step13_chunk_01 step13ChunkCertificate02

def step13ChunkCertificate00 :
    ChunkedListAll step13ChunkSize step13Predicate (step13Tail 0) :=
  .step step13_chunk_00 step13ChunkCertificate01

theorem step13_table_checked :
    boundedLocalEquationCheck 2 step13Result.scope step13Result.value
      (eliminatedBucketValue 2 21 step13Bucket) = true :=
  step13ChunkCertificate00.all_eq_true

theorem step13_scope_nodup : step13Result.scope.Nodup := by decide
theorem step13_coordinate_not_scope : 21 ∉ step13Result.scope := by decide

theorem step13_scope_cover_checked :
    step13Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 21 ∨ id ∈ step13Result.scope)) = true := by
  decide

theorem step13_result_scope_remaining_checked :
    step13Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 14)) = true := by
  decide

def step13 : CheckedScopedEliminationStep 2 21
    (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors13 where
  bucketResult :=
    { result := step13Result
      scope_nodup := step13_scope_nodup
      coordinate_not_scope := step13_coordinate_not_scope
      scope_cover_checked := step13_scope_cover_checked
      table_checked := step13_table_checked }
  result_scope_remaining_checked := step13_result_scope_remaining_checked

def factors14 : List ScopedQFactor := step13.afterFactors

theorem step13_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 13) factors13 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors14 :=
  step13.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13.step13_partitionSum_eqv

