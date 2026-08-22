/-
# The 127 nonzero cutoff-two unordered spatial-S3 representatives

This literal carrier is generated from the stored raw table, but its length,
uniqueness, upper-triangularity, and nonzeroness are checked below by Lean.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSpatialS3NonzeroRepresentatives : List CutoffTwoSectorPair :=
[
  ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 4⟩, ⟨0, 8⟩, ⟨0, 9⟩,
  ⟨0, 10⟩, ⟨0, 11⟩, ⟨0, 12⟩, ⟨0, 15⟩, ⟨0, 16⟩, ⟨0, 25⟩,
  ⟨0, 26⟩, ⟨0, 28⟩, ⟨0, 29⟩, ⟨0, 30⟩, ⟨0, 32⟩, ⟨0, 57⟩,
  ⟨0, 58⟩, ⟨0, 60⟩, ⟨0, 64⟩, ⟨1, 1⟩, ⟨1, 64⟩, ⟨2, 2⟩,
  ⟨2, 63⟩, ⟨2, 64⟩, ⟨4, 4⟩, ⟨4, 61⟩, ⟨4, 62⟩, ⟨4, 64⟩,
  ⟨8, 8⟩, ⟨8, 57⟩, ⟨8, 58⟩, ⟨8, 60⟩, ⟨8, 64⟩, ⟨9, 9⟩,
  ⟨9, 56⟩, ⟨9, 64⟩, ⟨10, 10⟩, ⟨10, 55⟩, ⟨10, 56⟩, ⟨10, 63⟩,
  ⟨10, 64⟩, ⟨11, 11⟩, ⟨11, 54⟩, ⟨11, 56⟩, ⟨11, 62⟩, ⟨11, 64⟩,
  ⟨12, 12⟩, ⟨12, 53⟩, ⟨12, 54⟩, ⟨12, 55⟩, ⟨12, 56⟩, ⟨12, 61⟩,
  ⟨12, 62⟩, ⟨12, 63⟩, ⟨12, 64⟩, ⟨15, 15⟩, ⟨15, 50⟩, ⟨15, 52⟩,
  ⟨15, 56⟩, ⟨15, 58⟩, ⟨15, 60⟩, ⟨15, 64⟩, ⟨16, 16⟩, ⟨16, 49⟩,
  ⟨16, 50⟩, ⟨16, 51⟩, ⟨16, 52⟩, ⟨16, 55⟩, ⟨16, 56⟩, ⟨16, 57⟩,
  ⟨16, 58⟩, ⟨16, 59⟩, ⟨16, 60⟩, ⟨16, 63⟩, ⟨16, 64⟩, ⟨25, 25⟩,
  ⟨25, 48⟩, ⟨25, 64⟩, ⟨26, 26⟩, ⟨26, 47⟩, ⟨26, 48⟩, ⟨26, 55⟩,
  ⟨26, 56⟩, ⟨26, 63⟩, ⟨26, 64⟩, ⟨28, 28⟩, ⟨28, 32⟩, ⟨28, 46⟩,
  ⟨28, 47⟩, ⟨28, 48⟩, ⟨28, 60⟩, ⟨28, 61⟩, ⟨28, 62⟩, ⟨28, 64⟩,
  ⟨29, 29⟩, ⟨29, 44⟩, ⟨29, 48⟩, ⟨29, 60⟩, ⟨29, 64⟩, ⟨30, 30⟩,
  ⟨30, 44⟩, ⟨30, 47⟩, ⟨30, 48⟩, ⟨30, 56⟩, ⟨30, 59⟩, ⟨30, 60⟩,
  ⟨30, 63⟩, ⟨30, 64⟩, ⟨32, 32⟩, ⟨32, 48⟩, ⟨32, 57⟩, ⟨32, 58⟩,
  ⟨32, 60⟩, ⟨32, 61⟩, ⟨32, 62⟩, ⟨32, 64⟩, ⟨57, 57⟩, ⟨57, 64⟩,
  ⟨58, 58⟩, ⟨58, 63⟩, ⟨58, 64⟩, ⟨60, 60⟩, ⟨60, 62⟩, ⟨60, 64⟩,
  ⟨64, 64⟩
]

def cutoffTwoSpatialS3NonzeroRepresentativeCodes : List Nat :=
[
  0, 1, 2, 4, 8, 9, 10, 11, 12, 15, 16, 25,
  26, 28, 29, 30, 32, 57, 58, 60, 64, 66, 129, 132,
  193, 194, 264, 321, 322, 324, 528, 577, 578, 580, 584, 594,
  641, 649, 660, 705, 706, 713, 714, 726, 769, 771, 777, 779,
  792, 833, 834, 835, 836, 841, 842, 843, 844, 990, 1025, 1027,
  1031, 1033, 1035, 1039, 1056, 1089, 1090, 1091, 1092, 1095, 1096, 1097,
  1098, 1099, 1100, 1103, 1104, 1650, 1673, 1689, 1716, 1737, 1738, 1745,
  1746, 1753, 1754, 1848, 1852, 1866, 1867, 1868, 1880, 1881, 1882, 1884,
  1914, 1929, 1933, 1945, 1949, 1980, 1994, 1997, 1998, 2006, 2009, 2010,
  2013, 2014, 2112, 2128, 2137, 2138, 2140, 2141, 2142, 2144, 3762, 3769,
  3828, 3833, 3834, 3960, 3962, 3964, 4224
]

/-- A compact recognizer for the same 127 literal representative codes.
Unlike list membership, this stays compact in proofs with a variable code. -/
def cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 9 => true
  | 10 => true
  | 11 => true
  | 12 => true
  | 15 => true
  | 16 => true
  | 25 => true
  | 26 => true
  | 28 => true
  | 29 => true
  | 30 => true
  | 32 => true
  | 57 => true
  | 58 => true
  | 60 => true
  | 64 => true
  | 66 => true
  | 129 => true
  | 132 => true
  | 193 => true
  | 194 => true
  | 264 => true
  | 321 => true
  | 322 => true
  | 324 => true
  | 528 => true
  | 577 => true
  | 578 => true
  | 580 => true
  | 584 => true
  | 594 => true
  | 641 => true
  | 649 => true
  | 660 => true
  | 705 => true
  | 706 => true
  | 713 => true
  | 714 => true
  | 726 => true
  | 769 => true
  | 771 => true
  | 777 => true
  | 779 => true
  | 792 => true
  | 833 => true
  | 834 => true
  | 835 => true
  | 836 => true
  | 841 => true
  | 842 => true
  | 843 => true
  | 844 => true
  | 990 => true
  | 1025 => true
  | 1027 => true
  | 1031 => true
  | 1033 => true
  | 1035 => true
  | 1039 => true
  | 1056 => true
  | 1089 => true
  | 1090 => true
  | 1091 => true
  | 1092 => true
  | 1095 => true
  | 1096 => true
  | 1097 => true
  | 1098 => true
  | 1099 => true
  | 1100 => true
  | 1103 => true
  | 1104 => true
  | 1650 => true
  | 1673 => true
  | 1689 => true
  | 1716 => true
  | 1737 => true
  | 1738 => true
  | 1745 => true
  | 1746 => true
  | 1753 => true
  | 1754 => true
  | 1848 => true
  | 1852 => true
  | 1866 => true
  | 1867 => true
  | 1868 => true
  | 1880 => true
  | 1881 => true
  | 1882 => true
  | 1884 => true
  | 1914 => true
  | 1929 => true
  | 1933 => true
  | 1945 => true
  | 1949 => true
  | 1980 => true
  | 1994 => true
  | 1997 => true
  | 1998 => true
  | 2006 => true
  | 2009 => true
  | 2010 => true
  | 2013 => true
  | 2014 => true
  | 2112 => true
  | 2128 => true
  | 2137 => true
  | 2138 => true
  | 2140 => true
  | 2141 => true
  | 2142 => true
  | 2144 => true
  | 3762 => true
  | 3769 => true
  | 3828 => true
  | 3833 => true
  | 3834 => true
  | 3960 => true
  | 3962 => true
  | 3964 => true
  | 4224 => true
  | _ => false

def cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes : List Nat :=
  (List.range 4225).filter
    cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck

theorem cutoffTwoSpatialS3NonzeroRepresentatives_length :
    cutoffTwoSpatialS3NonzeroRepresentatives.length = 127 := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentatives_nodup :
    cutoffTwoSpatialS3NonzeroRepresentatives.Nodup := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeCodes_length :
    cutoffTwoSpatialS3NonzeroRepresentativeCodes.length = 127 := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeCodes_nodup :
    cutoffTwoSpatialS3NonzeroRepresentativeCodes.Nodup := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes_eq :
    cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes =
      cutoffTwoSpatialS3NonzeroRepresentativeCodes := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck_iff_mem_of_lt
    {code : Nat} (hcode : code < 4225) :
    cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck code = true ↔
      code ∈ cutoffTwoSpatialS3NonzeroRepresentativeCodes := by
  rw [← cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes_eq]
  constructor
  · intro hcheck
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hcode, hcheck⟩
  · intro hmem
    exact (List.mem_filter.mp hmem).2

theorem cutoffTwoSectorPairCode_lt (pair : CutoffTwoSectorPair) :
    cutoffTwoSectorPairCode pair < 4225 := by
  unfold cutoffTwoSectorPairCode
  omega

def cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck : Bool :=
  cutoffTwoSpatialS3NonzeroRepresentatives.all fun pair =>
    decide (pair.row.val ≤ pair.column.val)

def cutoffTwoSpatialS3NonzeroRepresentativesRawCheck : Bool :=
  cutoffTwoSpatialS3NonzeroRepresentatives.all fun pair =>
    decide (¬ cutoffTwoSectorRawKernel pair.row.val pair.column.val ≈ 0)

theorem cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck_true :
    cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck = true := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativesRawCheck_true :
    cutoffTwoSpatialS3NonzeroRepresentativesRawCheck = true := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentative_upper
    {pair : CutoffTwoSectorPair}
    (hpair : pair ∈ cutoffTwoSpatialS3NonzeroRepresentatives) :
    pair.row.val ≤ pair.column.val := by
  exact of_decide_eq_true
    (List.all_eq_true.mp
      cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck_true pair hpair)

theorem cutoffTwoSpatialS3NonzeroRepresentative_raw
    {pair : CutoffTwoSectorPair}
    (hpair : pair ∈ cutoffTwoSpatialS3NonzeroRepresentatives) :
    ¬ cutoffTwoSectorRawKernel pair.row.val pair.column.val ≈ 0 := by
  exact of_decide_eq_true
    (List.all_eq_true.mp
      cutoffTwoSpatialS3NonzeroRepresentativesRawCheck_true pair hpair)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentatives_length
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentatives_nodup
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentativeCodes_length
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentativeCodes_nodup
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes_eq
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck_iff_mem_of_lt
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSectorPairCode_lt
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentative_upper
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.cutoffTwoSpatialS3NonzeroRepresentative_raw
