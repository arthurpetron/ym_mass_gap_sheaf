/-
# Parallel finite checker for exact corrected-slab reflection

This file contains only the executable side of the 72-face covariance
certificate.  Six small importing modules check disjoint twelve-face slices,
allowing Lake to evaluate them in parallel.  The analytic consumer remains
in `BF4ExactSlabVacuumReflection`.
-/

import YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
import YMGap.Continuum.BF4GroupedGramChoiKernel
import YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
import YMGap.Continuum.SU2QuaternionHaarRingNormalizer

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev SlabLink :=
  YMGap.Continuum.ClusterCount4DProgress.Z4Link

private abbrev SlabFace :=
  YMGap.Continuum.ClusterCount4DProgress.Z4Plaq

def fallbackLink : SlabLink :=
  ((0, 0, 0, 0),
    YMGap.Continuum.ClusterCount4DProgress.Dir4.x0)

def linkAt (extent block : Nat) : SlabLink :=
  (boundaryCompleteSlabLinks extent).getD block fallbackLink

def reflectBlock (extent block : Nat) : Nat :=
  listIndexOf
    (timeReflectLink extent (linkAt extent block))
    (boundaryCompleteSlabLinks extent)

def reindexExponents (extent : Nat)
    (monomial : List Nat) : List Nat :=
  List.ofFn fun coordinate :
      Fin (4 * (boundaryCompleteSlabLinks extent).length) =>
    exponentAt monomial
      (4 * reflectBlock extent (coordinate.val / 4) +
        coordinate.val % 4)

def reindexPolynomial (extent : Nat) (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun term =>
    (reindexExponents extent term.1, term.2)

def timeVectorCoordinate (extent coordinate : Nat) : Bool :=
  decide
    ((linkAt extent (coordinate / 4)).2 =
        YMGap.Continuum.ClusterCount4DProgress.Dir4.x3 ∧
      coordinate % 4 ≠ 0)

def reflectPolynomial (extent : Nat) (polynomial : RatPoly) : RatPoly :=
  signSelectedPolynomial
    (4 * (boundaryCompleteSlabLinks extent).length)
    (timeVectorCoordinate extent)
    (reindexPolynomial extent polynomial)

def sparseCodeAux : Nat → List Nat → List Nat
  | _, [] => []
  | coordinate, exponent :: rest =>
      if exponent = 0 then sparseCodeAux (coordinate + 1) rest
      else coordinate :: exponent :: sparseCodeAux (coordinate + 1) rest

def sparseCode (monomial : List Nat) : List Nat :=
  sparseCodeAux 0 monomial

def sparseRaw (polynomial : RatPoly) : RawPoly :=
  polynomial.map fun term => (sparseCode term.1, term.2.num)

def integralCoefficients (polynomial : RatPoly) : Bool :=
  polynomial.all fun term => term.2.denPred == 0

def normalCheck (face : SlabFace) : Bool :=
  let left := reflectPolynomial 1
    (correctedSlabPlaquettePolynomial 1 face).scalar
  let right := canonicalQuaternionPolynomial
    (boundaryCompleteSlabLinks 1).length
    (correctedSlabPlaquettePolynomial 1
      (timeReflectPlaquette 1 face)).scalar
  integralCoefficients left && integralCoefficients right &&
    (canon (sparseRaw left) == canon (sparseRaw right))

/-! ## Compact executable reflection

The dense checker above first materializes a 464-coordinate exponent vector
for every plaquette monomial.  The following equivalent executable path scans
those coordinates but emits only the nonzero coordinate/exponent pairs.  Its
normal forms therefore remain quartic-sized throughout kernel reduction. -/

def compactReindexSparseAux (extent : Nat) (monomial : List Nat) :
    Nat → Nat → List Nat
  | _, 0 => []
  | coordinate, remaining + 1 =>
      let exponent := exponentAt monomial
        (4 * reflectBlock extent (coordinate / 4) + coordinate % 4)
      if exponent = 0 then
        compactReindexSparseAux extent monomial (coordinate + 1) remaining
      else
        coordinate :: exponent ::
          compactReindexSparseAux extent monomial (coordinate + 1) remaining

def compactReindexSparse (extent : Nat) (monomial : List Nat) : List Nat :=
  compactReindexSparseAux extent monomial 0
    (4 * (boundaryCompleteSlabLinks extent).length)

private def denseReindexAux (extent : Nat) (monomial : List Nat) :
    Nat → Nat → List Nat
  | _, 0 => []
  | coordinate, remaining + 1 =>
      exponentAt monomial
          (4 * reflectBlock extent (coordinate / 4) + coordinate % 4) ::
        denseReindexAux extent monomial (coordinate + 1) remaining

private theorem denseReindexAux_length
    (extent : Nat) (monomial : List Nat) :
    ∀ coordinate remaining,
      (denseReindexAux extent monomial coordinate remaining).length =
        remaining
  | _, 0 => rfl
  | coordinate, remaining + 1 => by
      simp only [denseReindexAux, List.length_cons]
      rw [denseReindexAux_length extent monomial (coordinate + 1) remaining]

private theorem exponentAt_denseReindexAux
    (extent : Nat) (monomial : List Nat) :
    ∀ remaining coordinate target,
      exponentAt
          (denseReindexAux extent monomial coordinate remaining) target =
        if target < remaining then
          exponentAt monomial
            (4 * reflectBlock extent ((coordinate + target) / 4) +
              (coordinate + target) % 4)
        else 0
  | 0, _, target => by
      simp [denseReindexAux, exponentAt]
  | remaining + 1, coordinate, 0 => by
      simp [denseReindexAux, exponentAt]
  | remaining + 1, coordinate, target + 1 => by
      simp only [denseReindexAux, exponentAt, List.getD_cons_succ,
        Nat.succ_lt_succ_iff]
      change
        exponentAt
            (denseReindexAux extent monomial (coordinate + 1) remaining)
            target =
          if target < remaining then
            exponentAt monomial
              (4 * reflectBlock extent ((coordinate + (target + 1)) / 4) +
                (coordinate + (target + 1)) % 4)
          else 0
      rw [exponentAt_denseReindexAux extent monomial remaining
        (coordinate + 1) target]
      have hcoordinate : coordinate + 1 + target = coordinate + (target + 1) := by
        omega
      rw [hcoordinate]

private theorem compactReindexSparseAux_eq_sparse_dense
    (extent : Nat) (monomial : List Nat) :
    ∀ coordinate remaining,
      compactReindexSparseAux extent monomial coordinate remaining =
        sparseCodeAux coordinate
          (denseReindexAux extent monomial coordinate remaining)
  | _, 0 => rfl
  | coordinate, remaining + 1 => by
      simp only [compactReindexSparseAux, denseReindexAux, sparseCodeAux]
      by_cases hzero :
          exponentAt monomial
              (4 * reflectBlock extent (coordinate / 4) + coordinate % 4) = 0
      · rw [if_pos hzero, if_pos hzero]
        exact compactReindexSparseAux_eq_sparse_dense extent monomial
          (coordinate + 1) remaining
      · rw [if_neg hzero, if_neg hzero]
        exact congrArg
          (fun tail =>
            coordinate ::
              exponentAt monomial
                (4 * reflectBlock extent (coordinate / 4) +
                  coordinate % 4) :: tail)
          (compactReindexSparseAux_eq_sparse_dense extent monomial
            (coordinate + 1) remaining)

private theorem exponentAt_reindexExponents
    (extent : Nat) (monomial : List Nat) {coordinate : Nat}
    (hcoordinate :
      coordinate < 4 * (boundaryCompleteSlabLinks extent).length) :
    exponentAt (reindexExponents extent monomial) coordinate =
      exponentAt monomial
        (4 * reflectBlock extent (coordinate / 4) + coordinate % 4) := by
  unfold exponentAt
  rw [← List.getElem_eq_getD
    (l := reindexExponents extent monomial)
    (i := coordinate)
    (h := by
      change coordinate < (List.ofFn _).length
      rw [List.length_ofFn]
      exact hcoordinate)
    0]
  exact List.getElem_ofFn
    (h := by
      change coordinate < (List.ofFn _).length
      rw [List.length_ofFn]
      exact hcoordinate)

private theorem denseReindexAux_eq_reindexExponents
    (extent : Nat) (monomial : List Nat) :
    denseReindexAux extent monomial 0
        (4 * (boundaryCompleteSlabLinks extent).length) =
      reindexExponents extent monomial := by
  apply natList_eq_of_length_getD
  · rw [denseReindexAux_length]
    exact List.length_ofFn.symm
  · intro coordinate hcoordinate
    change
      exponentAt
          (denseReindexAux extent monomial 0
            (4 * (boundaryCompleteSlabLinks extent).length)) coordinate =
        exponentAt (reindexExponents extent monomial) coordinate
    rw [exponentAt_denseReindexAux, if_pos (by
      simpa only [denseReindexAux_length] using hcoordinate)]
    simp only [Nat.zero_add]
    exact (exponentAt_reindexExponents extent monomial
      (by simpa only [denseReindexAux_length] using hcoordinate)).symm

theorem compactReindexSparse_eq_sparse_reindex
    (extent : Nat) (monomial : List Nat) :
    compactReindexSparse extent monomial =
      sparseCode (reindexExponents extent monomial) := by
  unfold compactReindexSparse sparseCode
  rw [compactReindexSparseAux_eq_sparse_dense,
    denseReindexAux_eq_reindexExponents]

def compactSelectedParity (extent : Nat) (monomial : List Nat) : Bool :=
  (List.range (4 * (boundaryCompleteSlabLinks extent).length)).foldl
    (fun parity coordinate =>
      if timeVectorCoordinate extent coordinate then
        xor parity
          (decide
            (exponentAt monomial
              (4 * reflectBlock extent (coordinate / 4) +
                coordinate % 4) % 2 = 1))
      else parity)
    false

private theorem foldl_congr_on
    {State Entry : Type}
    (left right : State → Entry → State) :
    ∀ (entries : List Entry) (initial : State),
      (∀ entry, entry ∈ entries →
        ∀ state, left state entry = right state entry) →
      entries.foldl left initial = entries.foldl right initial
  | [], _, _ => rfl
  | entry :: rest, initial, hsteps => by
      simp only [List.foldl_cons]
      rw [hsteps entry List.mem_cons_self initial]
      exact foldl_congr_on left right rest _
        (fun next hnext =>
          hsteps next (List.mem_cons_of_mem entry hnext))

theorem compactSelectedParity_eq_selected_reindex
    (extent : Nat) (monomial : List Nat) :
    compactSelectedParity extent monomial =
      selectedExponentParity
        (4 * (boundaryCompleteSlabLinks extent).length)
        (timeVectorCoordinate extent)
        (reindexExponents extent monomial) := by
  unfold compactSelectedParity selectedExponentParity
  apply foldl_congr_on
  intro coordinate hcoordinate parity
  have hlt : coordinate <
      4 * (boundaryCompleteSlabLinks extent).length :=
    List.mem_range.mp hcoordinate
  rw [exponentAt_reindexExponents extent monomial hlt]

def compactReflectRawTerm (extent : Nat) (term : RatTerm) :
    List Nat × Int :=
  let code := compactReindexSparse extent term.1
  (code,
    if compactSelectedParity extent term.1 then -term.2.num else term.2.num)

def compactReflectRaw (extent : Nat) (polynomial : RatPoly) : RawPoly :=
  polynomial.map (compactReflectRawTerm extent)

theorem compactReflectRaw_eq_sparse_reflect
    (extent : Nat) : ∀ polynomial : RatPoly,
    compactReflectRaw extent polynomial =
      sparseRaw (reflectPolynomial extent polynomial)
  | [] => rfl
  | term :: rest => by
      change
        compactReflectRawTerm extent term ::
            compactReflectRaw extent rest =
          (sparseCode (reindexExponents extent term.1),
              (if selectedExponentParity
                    (4 * (boundaryCompleteSlabLinks extent).length)
                    (timeVectorCoordinate extent)
                    (reindexExponents extent term.1)
                then -term.2 else term.2).num) ::
            sparseRaw (reflectPolynomial extent rest)
      rw [compactReflectRaw_eq_sparse_reflect extent rest]
      unfold compactReflectRawTerm
      rw [compactReindexSparse_eq_sparse_reindex,
        compactSelectedParity_eq_selected_reindex]
      split <;> rfl

theorem integralCoefficients_reflectPolynomial
    (extent : Nat) : ∀ polynomial : RatPoly,
    integralCoefficients (reflectPolynomial extent polynomial) =
      integralCoefficients polynomial
  | [] => rfl
  | term :: rest => by
      change
        ((if selectedExponentParity
              (4 * (boundaryCompleteSlabLinks extent).length)
              (timeVectorCoordinate extent)
              (reindexExponents extent term.1)
            then -term.2 else term.2).denPred == 0 &&
          integralCoefficients (reflectPolynomial extent rest)) =
        (term.2.denPred == 0 && integralCoefficients rest)
      rw [integralCoefficients_reflectPolynomial extent rest]
      split <;> rfl

def supportedCoordinates (coordinates : Nat) (polynomial : RatPoly) : Bool :=
  polynomial.all fun term => decide (term.1.length ≤ coordinates)

def compactNormalCheck (face : SlabFace) : Bool :=
  let source := (correctedSlabPlaquettePolynomial 1 face).scalar
  let target :=
    (correctedSlabPlaquettePolynomial 1
      (timeReflectPlaquette 1 face)).scalar
  integralCoefficients source && integralCoefficients target &&
    supportedCoordinates
      (4 * (boundaryCompleteSlabLinks 1).length) source &&
    supportedCoordinates
      (4 * (boundaryCompleteSlabLinks 1).length) target &&
    (canon (compactReflectRaw 1 source) == canon (sparseRaw target))

/-- The covariance equality separated from the inexpensive coefficient and
support checks.  Keeping this Boolean independent prevents the kernel from
retaining several copies of the expanded quartic plaquette while reducing a
single face certificate. -/
def compactCovarianceCheck (face : SlabFace) : Bool :=
  let source := (correctedSlabPlaquettePolynomial 1 face).scalar
  let target :=
    (correctedSlabPlaquettePolynomial 1
      (timeReflectPlaquette 1 face)).scalar
  canon (compactReflectRaw 1 source) == canon (sparseRaw target)

/-- The compiler side conditions, evaluated independently of covariance. -/
def compactSideCheck (face : SlabFace) : Bool :=
  let source := (correctedSlabPlaquettePolynomial 1 face).scalar
  let target :=
    (correctedSlabPlaquettePolynomial 1
      (timeReflectPlaquette 1 face)).scalar
  integralCoefficients source && integralCoefficients target &&
    supportedCoordinates
      (4 * (boundaryCompleteSlabLinks 1).length) source &&
    supportedCoordinates
      (4 * (boundaryCompleteSlabLinks 1).length) target

/-! ## Extent-one executable acceleration

The proof-facing checker above is generic in the slab extent.  At the literal
extent-one slab, however, repeatedly searching the 116-link list for every
one of 464 coordinates dominates kernel reduction.  The following array is
the exact reflected-block permutation.  Its agreement with `reflectBlock` is
itself checked by the kernel on the complete physical range; all subsequent
fast definitions are proved extensionally equal to the generic ones. -/

def reflectBlockTableOne : Array Nat :=
  #[8, 12, 16, 17, 14, 18, 19, 7, 0, 9, 20, 21, 1, 13, 4, 15, 2, 3, 5, 6,
    10, 11, 33, 34, 31, 35, 36, 27, 37, 38, 30, 24, 32, 22, 23, 25, 26, 28,
    29, 46, 48, 49, 50, 43, 51, 52, 39, 47, 40, 41, 42, 44, 45, 62, 63, 64,
    65, 57, 66, 67, 60, 61, 53, 54, 55, 56, 58, 59, 73, 75, 76, 77, 78, 68,
    74, 69, 70, 71, 72, 86, 87, 88, 89, 83, 90, 85, 79, 80, 81, 82, 84, 97,
    98, 99, 94, 100, 96, 91, 92, 93, 95, 110, 111, 112, 113, 105, 114, 115,
    108, 109, 101, 102, 103, 104, 106, 107]

def fastReflectBlockOne (block : Nat) : Nat :=
  reflectBlockTableOne.getD block 0

private theorem reflectBlockTableOne_check :
    (List.range (boundaryCompleteSlabLinks 1).length).all
      (fun block => decide (fastReflectBlockOne block = reflectBlock 1 block)) =
        true := by
  decide

theorem fastReflectBlockOne_eq_reflectBlock
    {block : Nat} (hblock : block < (boundaryCompleteSlabLinks 1).length) :
    fastReflectBlockOne block = reflectBlock 1 block := by
  have hentry := List.all_eq_true.mp reflectBlockTableOne_check block
    (List.mem_range.mpr hblock)
  exact of_decide_eq_true hentry

def fastCompactReindexSparseAux (monomial : List Nat) :
    Nat → Nat → List Nat
  | _, 0 => []
  | coordinate, remaining + 1 =>
      let exponent := exponentAt monomial
        (4 * fastReflectBlockOne (coordinate / 4) + coordinate % 4)
      if exponent = 0 then
        fastCompactReindexSparseAux monomial (coordinate + 1) remaining
      else
        coordinate :: exponent ::
          fastCompactReindexSparseAux monomial (coordinate + 1) remaining

private theorem fastCompactReindexSparseAux_eq :
    ∀ (monomial : List Nat) (coordinate remaining : Nat),
      coordinate + remaining ≤
          4 * (boundaryCompleteSlabLinks 1).length →
      fastCompactReindexSparseAux monomial coordinate remaining =
        compactReindexSparseAux 1 monomial coordinate remaining
  | _, _, 0, _ => rfl
  | monomial, coordinate, remaining + 1, hbound => by
      have hcoordinate :
          coordinate / 4 < (boundaryCompleteSlabLinks 1).length := by
        omega
      simp only [fastCompactReindexSparseAux, compactReindexSparseAux,
        fastReflectBlockOne_eq_reflectBlock hcoordinate]
      by_cases hzero :
          exponentAt monomial
              (4 * reflectBlock 1 (coordinate / 4) + coordinate % 4) = 0
      · rw [if_pos hzero, if_pos hzero]
        exact fastCompactReindexSparseAux_eq monomial
          (coordinate + 1) remaining (by omega)
      · rw [if_neg hzero, if_neg hzero,
          fastCompactReindexSparseAux_eq monomial
            (coordinate + 1) remaining (by omega)]

def fastCompactReindexSparse (monomial : List Nat) : List Nat :=
  fastCompactReindexSparseAux monomial 0
    (4 * (boundaryCompleteSlabLinks 1).length)

theorem fastCompactReindexSparse_eq (monomial : List Nat) :
    fastCompactReindexSparse monomial = compactReindexSparse 1 monomial := by
  exact fastCompactReindexSparseAux_eq monomial 0 _ (Nat.le_refl _)

def fastCompactSelectedParity (monomial : List Nat) : Bool :=
  (List.range (4 * (boundaryCompleteSlabLinks 1).length)).foldl
    (fun parity coordinate =>
      if timeVectorCoordinate 1 coordinate then
        xor parity
          (decide
            (exponentAt monomial
              (4 * fastReflectBlockOne (coordinate / 4) +
                coordinate % 4) % 2 = 1))
      else parity)
    false

theorem fastCompactSelectedParity_eq (monomial : List Nat) :
    fastCompactSelectedParity monomial = compactSelectedParity 1 monomial := by
  unfold fastCompactSelectedParity compactSelectedParity
  apply foldl_congr_on
  intro coordinate hcoordinate parity
  have hlt : coordinate <
      4 * (boundaryCompleteSlabLinks 1).length :=
    List.mem_range.mp hcoordinate
  rw [fastReflectBlockOne_eq_reflectBlock (by omega)]

def fastCompactReflectRawTerm (term : RatTerm) : List Nat × Int :=
  let code := fastCompactReindexSparse term.1
  (code,
    if fastCompactSelectedParity term.1 then -term.2.num else term.2.num)

def fastCompactReflectRaw (polynomial : RatPoly) : RawPoly :=
  polynomial.map fastCompactReflectRawTerm

private theorem fastCompactReflectRawTerm_eq (term : RatTerm) :
    fastCompactReflectRawTerm term = compactReflectRawTerm 1 term := by
  unfold fastCompactReflectRawTerm compactReflectRawTerm
  rw [fastCompactReindexSparse_eq, fastCompactSelectedParity_eq]

theorem fastCompactReflectRaw_eq (polynomial : RatPoly) :
    fastCompactReflectRaw polynomial = compactReflectRaw 1 polynomial := by
  unfold fastCompactReflectRaw compactReflectRaw
  apply List.map_congr_left
  intro term hterm
  exact fastCompactReflectRawTerm_eq term

def fastCompactNormalCheck (face : SlabFace) : Bool :=
  let source := (correctedSlabPlaquettePolynomial 1 face).scalar
  let target :=
    (correctedSlabPlaquettePolynomial 1
      (timeReflectPlaquette 1 face)).scalar
  integralCoefficients source && integralCoefficients target &&
    supportedCoordinates
      (4 * (boundaryCompleteSlabLinks 1).length) source &&
    supportedCoordinates
      (4 * (boundaryCompleteSlabLinks 1).length) target &&
    (canon (fastCompactReflectRaw source) == canon (sparseRaw target))

/-- The expensive covariance equality alone.  The four inexpensive compiler
side conditions can be certified independently, avoiding repeated expansion
of the same plaquette polynomial inside one kernel decision. -/
def fastCompactCovarianceCheck (face : SlabFace) : Bool :=
  let source := (correctedSlabPlaquettePolynomial 1 face).scalar
  let target :=
    (correctedSlabPlaquettePolynomial 1
      (timeReflectPlaquette 1 face)).scalar
  canon (fastCompactReflectRaw source) == canon (sparseRaw target)

theorem fastCompactCovarianceCheck_eq (face : SlabFace) :
    fastCompactCovarianceCheck face = compactCovarianceCheck face := by
  unfold fastCompactCovarianceCheck compactCovarianceCheck
  simp only [fastCompactReflectRaw_eq]

theorem fastCompactNormalCheck_eq (face : SlabFace) :
    fastCompactNormalCheck face = compactNormalCheck face := by
  unfold fastCompactNormalCheck compactNormalCheck
  simp only [fastCompactReflectRaw_eq]

def faceSlice (slice : Nat) : List SlabFace :=
  (boundaryCompleteSlabPlaquettes 1).drop (12 * slice) |>.take 12

/-- One face inside a twelve-face checker slice.  Keeping each expensive
normal-form decision in its own declaration prevents the kernel evaluator
from retaining the entire twelve-face reduction at once. -/
def faceSliceEntry (slice offset : Nat) : SlabFace :=
  (faceSlice slice).getD offset fallbackPlaquette

/-- Cheap assembly of twelve already-checked face certificates. -/
theorem allTwelveNormal (check : SlabFace → Bool)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : SlabFace)
    (h0 : check a0 = true) (h1 : check a1 = true)
    (h2 : check a2 = true) (h3 : check a3 = true)
    (h4 : check a4 = true) (h5 : check a5 = true)
    (h6 : check a6 = true) (h7 : check a7 = true)
    (h8 : check a8 = true) (h9 : check a9 = true)
    (h10 : check a10 = true) (h11 : check a11 = true) :
    ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11].all
      check) = true := by
  simp only [List.all_cons, List.all_nil, h0, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, Bool.and_self]

theorem faceSlices_cover :
    boundaryCompleteSlabPlaquettes 1 =
      faceSlice 0 ++ faceSlice 1 ++ faceSlice 2 ++
      faceSlice 3 ++ faceSlice 4 ++ faceSlice 5 := by
  decide

/-- All compiler side conditions for the literal 72 faces.  This reduction
is deliberately separate from the commutative normal-form calculation. -/
theorem allFacesSideCheck :
    (boundaryCompleteSlabPlaquettes 1).all compactSideCheck = true := by
  decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlices_cover
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.fastReflectBlockOne_eq_reflectBlock
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.fastCompactNormalCheck_eq
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.allFacesSideCheck
