/-
# Exact cutoff-two vacuum-column elimination trace

This file instantiates the generic scoped-factor checker with the 24 lower
faces, 24 heat factors, and 48 production lower-link factors of the genuine
BF4 half-extent-zero vacuum column at cutoff two and coupling one half.

The elimination order was proposed by a strict 16-process exact-arithmetic
search.  Lean reconstructs every intermediate table, checks every local
bucket equation, and applies the generic trace-soundness theorem.  The
external program is therefore a certificate producer, not part of the
trusted proof.

This is one finite positive-cutoff contraction.  It makes no cutoff-uniform,
volume-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
import YMGap.Continuum.FiniteScopedFactorTableCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationTrace

local infix:50 " ≈ " => Q'.eqv

/-- The width-ten search order, mapped from variable indices to production
lower-face identifiers. -/
def cutoffTwoVacuumEliminationFaceOrder : List Nat :=
  [30, 46, 54, 63, 3, 10, 36, 18, 64, 66, 0, 28,
   27, 21, 19, 57, 55, 9, 39, 1, 45, 12, 37, 48]

/-- Kernel check that the proposed order is exactly a permutation of the
24-variable production carrier. -/
theorem cutoffTwoVacuumEliminationFaceOrder_perm :
    cutoffTwoVacuumEliminationFaceOrder.Perm
      cutoffTwoExpectedLowerFaceIds := by
  unfold cutoffTwoVacuumEliminationFaceOrder
    cutoffTwoExpectedLowerFaceIds
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 3, 10, 36, 18, 64, 66])
    (a := 0) (l₂ := [28, 27, 21, 19, 57, 55, 9, 39, 1, 45, 12, 37, 48])) ?_
  refine List.Perm.cons 0 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 3, 10, 36, 18, 64, 66, 28, 27, 21, 19, 57, 55, 9, 39])
    (a := 1) (l₂ := [45, 12, 37, 48])) ?_
  refine List.Perm.cons 1 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63]) (a := 3)
    (l₂ := [10, 36, 18, 64, 66, 28, 27, 21, 19, 57, 55, 9, 39, 45, 12, 37, 48])) ?_
  refine List.Perm.cons 3 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 10, 36, 18, 64, 66, 28, 27, 21, 19, 57, 55])
    (a := 9) (l₂ := [39, 45, 12, 37, 48])) ?_
  refine List.Perm.cons 9 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63]) (a := 10)
    (l₂ := [36, 18, 64, 66, 28, 27, 21, 19, 57, 55, 39, 45, 12, 37, 48])) ?_
  refine List.Perm.cons 10 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 36, 18, 64, 66, 28, 27, 21, 19, 57, 55, 39, 45])
    (a := 12) (l₂ := [37, 48])) ?_
  refine List.Perm.cons 12 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 36]) (a := 18)
    (l₂ := [64, 66, 28, 27, 21, 19, 57, 55, 39, 45, 37, 48])) ?_
  refine List.Perm.cons 18 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 36, 64, 66, 28, 27, 21])
    (a := 19) (l₂ := [57, 55, 39, 45, 37, 48])) ?_
  refine List.Perm.cons 19 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 36, 64, 66, 28, 27])
    (a := 21) (l₂ := [57, 55, 39, 45, 37, 48])) ?_
  refine List.Perm.cons 21 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 36, 64, 66, 28])
    (a := 27) (l₂ := [57, 55, 39, 45, 37, 48])) ?_
  refine List.Perm.cons 27 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [30, 46, 54, 63, 36, 64, 66])
    (a := 28) (l₂ := [57, 55, 39, 45, 37, 48])) ?_
  refine List.Perm.cons 28 ?_
  refine List.Perm.cons 30 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [46, 54, 63]) (a := 36)
    (l₂ := [64, 66, 57, 55, 39, 45, 37, 48])) ?_
  refine List.Perm.cons 36 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [46, 54, 63, 64, 66, 57, 55, 39, 45])
    (a := 37) (l₂ := [48])) ?_
  refine List.Perm.cons 37 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [46, 54, 63, 64, 66, 57, 55])
    (a := 39) (l₂ := [45, 48])) ?_
  refine List.Perm.cons 39 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [46, 54, 63, 64, 66, 57, 55])
    (a := 45) (l₂ := [48])) ?_
  refine List.Perm.cons 45 ?_
  refine List.Perm.cons 46 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [54, 63, 64, 66, 57, 55]) (a := 48) (l₂ := [])) ?_
  refine List.Perm.cons 48 ?_
  refine List.Perm.cons 54 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [63, 64, 66, 57]) (a := 55) (l₂ := [])) ?_
  refine List.Perm.cons 55 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [63, 64, 66]) (a := 57) (l₂ := [])) ?_
  refine List.Perm.cons 57 ?_
  refine List.Perm.cons 63 ?_
  refine List.Perm.cons 64 ?_
  refine List.Perm.cons 66 ?_
  exact List.Perm.refl []

/-- Rational local multiplicity table of a given active arity. -/
def cutoffTwoMultiplicityQTable (arity : Nat) : List Q' :=
  (cutoffTwoExpectedMultiplicityTables.getD arity []).map Q'.ofNat

/-- One checked table factor for every lower-face heat coefficient. -/
def cutoffTwoVacuumHeatFactors : List ScopedQFactor :=
  cutoffTwoExpectedLowerFaceIds.map fun faceId =>
    scopedTableFactor 3 [faceId] cutoffTwoExpectedHeatTable

/-- One checked table factor for every production lower-link scope. -/
def cutoffTwoVacuumLinkFactors : List ScopedQFactor :=
  cutoffTwoExpectedActiveLinkFaceIds.map fun scope =>
    scopedTableFactor 3 scope
      (cutoffTwoMultiplicityQTable scope.length)

/-- Complete 72-factor sparse presentation supplied to the trace checker. -/
def cutoffTwoVacuumInitialFactors : List ScopedQFactor :=
  cutoffTwoVacuumHeatFactors ++ cutoffTwoVacuumLinkFactors

theorem cutoffTwoVacuumInitialFactor_count :
    cutoffTwoVacuumInitialFactors.length = 72 := by
  decide

/-- Compact sparse datum constructor used at the wide stages. -/
def cutoffTwoSparseDatum
    (scope : List Nat) (entries : List (Nat × Q')) :
    SparseEliminationDatum :=
  { scope := scope, nonzeroEntries := entries }

/-- A sparse table whose listed entries all have value one. -/
def cutoffTwoUnitSparseDatum
    (scope indices : List Nat) : SparseEliminationDatum :=
  cutoffTwoSparseDatum scope
    (indices.map fun index => (index, (1 : Q')))

def cutoffTwoSparseEntries
    (value : Q') (indices : List Nat) : List (Nat × Q') :=
  indices.map fun index => (index, value)

/-- The first ten result tables have at most 2,187 entries and are computed
inside Lean.  The remaining wide tables are represented by only their exact
nonzero entries, severing recursive table expansion and bounding memory. -/
def cutoffTwoVacuumEliminationTableData : List SparseEliminationDatum :=
  [cutoffTwoUnitSparseDatum [12, 21, 27, 28]
    [0, 12, 24, 28, 40, 52, 56, 68, 80],
   cutoffTwoUnitSparseDatum [10, 37, 45, 48]
    [0, 12, 24, 28, 40, 52, 56, 68, 80],
   cutoffTwoUnitSparseDatum [18, 36, 55, 57]
    [0, 12, 24, 28, 40, 52, 56, 68, 80],
   cutoffTwoUnitSparseDatum [27, 45, 55, 57, 64, 66]
    [0, 10, 20, 30, 40, 50, 60, 70, 80, 84, 94, 104,
     108, 114, 118, 124, 128, 134, 138, 148, 158, 168, 178,
     188, 192, 202, 212, 216, 222, 226, 232, 236, 242, 244,
     252, 254, 262, 274, 282, 284, 292, 304, 312, 314, 322,
     328, 336, 338, 346, 352, 358, 360, 362, 366, 368, 370,
     376, 382, 390, 392, 400, 412, 420, 422, 430, 436, 444,
     446, 454, 460, 466, 468, 470, 474, 476, 478, 484, 488,
     496, 504, 506, 518, 526, 534, 536, 548, 556, 564, 566,
     572, 580, 588, 590, 596, 602, 604, 610, 612, 614, 618,
     620, 626, 634, 642, 644, 656, 664, 672, 674, 680, 688,
     696, 698, 704, 710, 712, 718, 720, 722, 726, 728],
   cutoffTwoSparseDatum [0, 1, 9, 12, 19, 21]
    (cutoffTwoSparseEntries 1
        [0, 4, 8, 36, 40, 44, 72, 76, 80] ++
      cutoffTwoSparseEntries (⟨1, 3⟩ : Q')
        [334, 336, 338, 340, 352, 354, 356, 358,
         370, 372, 374, 376, 388, 390, 392, 394] ++
      cutoffTwoSparseEntries (⟨3, 255⟩ : Q')
        [668, 670, 672, 674, 686, 688, 690, 692,
         704, 706, 708, 710, 722, 724, 726, 728]),
   cutoffTwoUnitSparseDatum [1, 9, 12, 37, 45, 48]
    [0, 12, 24, 324, 336, 348, 648, 660, 672],
   cutoffTwoUnitSparseDatum [0, 18, 37, 39, 55, 57]
    [0, 82, 164, 252, 334, 416, 504, 586, 668],
   cutoffTwoUnitSparseDatum [0, 19, 21, 37, 39, 55, 57]
    [0, 981, 1962],
   cutoffTwoUnitSparseDatum [27, 28, 45, 48, 55, 57, 66]
    [0, 31, 62, 90, 121, 152, 180, 211, 242, 247, 270, 278,
     301, 337, 360, 368, 391, 427, 450, 458, 481, 494, 517,
     540, 548, 584, 607, 630, 638, 674, 697, 720, 728, 732,
     757, 763, 788, 822, 847, 853, 878, 912, 937, 943, 968,
     973, 979, 1002, 1004, 1027, 1033, 1063, 1069, 1092,
     1094, 1117, 1123, 1153, 1159, 1182, 1184, 1207, 1213,
     1220, 1243, 1249, 1272, 1274, 1310, 1333, 1339, 1362,
     1364, 1400, 1423, 1429, 1452, 1454, 1464, 1489, 1514,
     1520, 1554, 1579, 1604, 1610, 1644, 1669, 1694, 1700,
     1705, 1730, 1734, 1736, 1759, 1795, 1820, 1824, 1826,
     1849, 1885, 1910, 1914, 1916, 1939, 1946, 1952, 1975,
     2000, 2004, 2006, 2036, 2042, 2065, 2090, 2094, 2096,
     2126, 2132, 2155, 2180, 2184, 2186],
   cutoffTwoUnitSparseDatum [27, 28, 45, 48, 55, 57]
    [0, 30, 60, 90, 120, 150, 180, 210, 240, 244, 274, 304,
     334, 364, 394, 424, 454, 484, 488, 518, 548, 578, 608,
     638, 668, 698, 728],
   cutoffTwoSparseDatum
    [1, 9, 12, 19, 21, 37, 39, 55, 57]
    [(0, (1 : Q')), (2916, (1 : Q')), (5832, (1 : Q')),
     (7542, ⟨1, 15⟩), (9000, ⟨1, 15⟩),
     (10458, ⟨1, 15⟩), (11916, ⟨1, 15⟩),
     (15084, ⟨9, 65535⟩), (16542, ⟨9, 65535⟩),
     (18000, ⟨9, 65535⟩), (19458, ⟨9, 65535⟩)],
   cutoffTwoUnitSparseDatum
    [9, 12, 19, 21, 27, 45, 48, 55, 57]
    [0, 30, 60, 1054, 1084, 1114, 2108, 2138, 2168,
     6886, 6916, 6946, 7290, 7320, 7350, 7940, 7970, 8000,
     8344, 8374, 8404, 13772, 13802, 13832, 14176, 14206,
     14236, 14580, 14610, 14640, 15230, 15260, 15290],
   cutoffTwoUnitSparseDatum
    [9, 12, 19, 21, 45, 48, 55, 57]
    [0, 30, 60, 2430, 2460, 2490, 4860, 4890, 4920],
   cutoffTwoSparseDatum
    [1, 9, 12, 19, 37, 39, 45, 48, 55, 57]
    [(0, (1 : Q')), (27054, ⟨1, 15⟩), (54108, ⟨9, 65535⟩)],
   cutoffTwoSparseDatum
    [1, 9, 12, 37, 39, 45, 48, 55, 57]
    [(0, (1 : Q')), (8829, ⟨1, 63⟩),
     (17658, ⟨27, 16777215⟩)],
   cutoffTwoSparseDatum
    [1, 9, 12, 37, 39, 45, 48, 55]
    [(0, (1 : Q')), (2943, ⟨1, 63⟩),
     (5886, ⟨27, 16777215⟩)],
   cutoffTwoSparseDatum
    [1, 9, 12, 37, 39, 45, 48]
    [(0, (1 : Q')), (981, ⟨1, 63⟩),
     (1962, ⟨27, 16777215⟩)],
   cutoffTwoSparseDatum
    [1, 12, 37, 39, 45, 48]
    [(0, (1 : Q')), (252, ⟨1, 255⟩),
     (504, ⟨81, 4294967295⟩)],
   cutoffTwoSparseDatum
    [1, 12, 37, 45, 48]
    [(0, (1 : Q')), (81, ⟨1, 1023⟩),
     (162, ⟨243, 1099511627775⟩)],
   cutoffTwoSparseDatum [12, 37, 45, 48]
    [(0, ⟨281543696188121, 281474976710655⟩)],
   cutoffTwoSparseDatum [12, 37, 48]
    [(0, ⟨281543696188121, 281474976710655⟩)],
   cutoffTwoSparseDatum [37, 48]
    [(0, ⟨281543696188121, 281474976710655⟩)],
   cutoffTwoSparseDatum [48]
    [(0, ⟨281543696188121, 281474976710655⟩)],
   cutoffTwoSparseDatum []
    [(0, ⟨281543696188121, 281474976710655⟩)]]

theorem cutoffTwoVacuumEliminationTableData_count :
    cutoffTwoVacuumEliminationTableData.length = 24 := by
  decide

/-- Total lookup used by the independently compiled step shards. -/
def cutoffTwoVacuumEliminationDatum (index : Nat) :
    SparseEliminationDatum :=
  cutoffTwoVacuumEliminationTableData.getD index
    { scope := [], nonzeroEntries := [] }

/-- The exact scalar proposed by the external 16-core contraction. -/
def cutoffTwoVacuumExpectedScalar : Q' :=
  Q'.mkPos 281543696188121 281474976710656 (by decide)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace.cutoffTwoVacuumEliminationFaceOrder_perm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace.cutoffTwoVacuumEliminationTableData_count
