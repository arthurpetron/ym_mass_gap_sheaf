/-
# Exact rooted BF4 tree paths and based cycle holonomies

The 23 variables in the BF4 tree-gauge boundary polynomial were previously
called chord holonomies because the 25 displayed tree links are set to the
identity.  This module supplies the missing finite geometry behind that name.

* the 25-link tree is equipped with an explicit rooted path to each of its 26
  vertices;
* every chord is completed by those paths to a closed loop based at the root;
* the corresponding raw 116-link polynomial quaternion is defined; and
* after tree gauge fixing, the based holonomy of chord `c` is proved
  prefix-equivalent to quaternion coordinate block `c`.

The five retained blocks therefore have the genuine based-cycle order
`{0,4,5,6,10}`.  This is the geometric half of the bridge.  Haar preservation
for the triangular, vertex-dependent change of link variables remains a
separate algebraic theorem and is not asserted here.

## Axiom gate

Finite lists, closed lattice geometry, exact rational polynomials, and
constructive prefix equivalence only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal

namespace YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

/-! ## 1. Explicit rooted paths in the displayed 25-link tree -/

def bf4SpatialTreeRoot : Z4Vertex := (0, 0, 0, 0)

/-- The root followed by the endpoint of each breadth-first tree link. -/
def bf4SpatialTreeVertices : List Z4Vertex :=
  bf4SpatialTreeRoot ::
    bf4SpatialTreeLinks.map fun link => addE link.1 link.2

theorem bf4SpatialTreeVertices_length :
    bf4SpatialTreeVertices.length = 26 := by
  decide

theorem bf4SpatialTreeVertices_nodup :
    bf4SpatialTreeVertices.Nodup := by
  decide

/-- For the vertex in the matching position of `bf4SpatialTreeVertices`, the
list of zero-based tree-link indices along the path from the root. -/
def bf4SpatialTreePathIndexTable : List (List Nat) :=
  [[],
   [0], [1], [2],
   [0, 3], [0, 4], [0, 5], [1, 6], [1, 7], [2, 8],
   [0, 3, 9], [0, 3, 10], [0, 4, 11], [0, 4, 12],
   [0, 5, 13], [1, 6, 14], [1, 7, 15],
   [0, 3, 9, 16], [0, 3, 9, 17], [0, 3, 10, 18],
   [0, 4, 11, 19], [0, 4, 12, 20], [1, 6, 14, 21],
   [0, 3, 9, 17, 22], [0, 3, 9, 17, 23],
   [0, 4, 11, 19, 24]]

theorem bf4SpatialTreePathIndexTable_length :
    bf4SpatialTreePathIndexTable.length = 26 := by
  decide

/-- Totalized rooted path lookup.  All physical chord endpoints occur in the
vertex table, so the fallback is never used by the based-cycle construction. -/
def bf4SpatialTreePathIndices (vertex : Z4Vertex) : List Nat :=
  bf4SpatialTreePathIndexTable.getD
    (bf4SpatialTreeVertices.idxOf vertex) []

private def bf4SpatialTreeFallbackLink : Z4Link :=
  ((0, 0, 0, 0), .x0)

def bf4SpatialTreePath (vertex : Z4Vertex) : List Z4Link :=
  (bf4SpatialTreePathIndices vertex).map fun index =>
    bf4SpatialTreeLinks.getD index bf4SpatialTreeFallbackLink

/-- Boolean composability check for a positively oriented link path. -/
def forwardLinkPathValid : Z4Vertex → List Z4Link → Bool
  | _, [] => true
  | vertex, link :: rest =>
      decide (link.1 = vertex) &&
        forwardLinkPathValid (addE link.1 link.2) rest

def forwardLinkPathEnd : Z4Vertex → List Z4Link → Z4Vertex
  | vertex, [] => vertex
  | _, link :: rest =>
      forwardLinkPathEnd (addE link.1 link.2) rest

def pathUsesOnlySpatialTree (path : List Z4Link) : Bool :=
  path.all fun link => decide (link ∈ bf4SpatialTreeLinks)

/-- Every one of the 46 chord endpoints has the displayed valid rooted tree
path, ending at that literal endpoint and using only tree links. -/
theorem bf4SpatialChordEndpointPaths_valid :
    ∀ cycle : BF4SpatialCycle,
      forwardLinkPathValid bf4SpatialTreeRoot
          (bf4SpatialTreePath (bf4SpatialChord cycle).1) = true ∧
      forwardLinkPathEnd bf4SpatialTreeRoot
          (bf4SpatialTreePath (bf4SpatialChord cycle).1) =
        (bf4SpatialChord cycle).1 ∧
      pathUsesOnlySpatialTree
          (bf4SpatialTreePath (bf4SpatialChord cycle).1) = true ∧
      forwardLinkPathValid bf4SpatialTreeRoot
          (bf4SpatialTreePath
            (addE (bf4SpatialChord cycle).1
              (bf4SpatialChord cycle).2)) = true ∧
      forwardLinkPathEnd bf4SpatialTreeRoot
          (bf4SpatialTreePath
            (addE (bf4SpatialChord cycle).1
              (bf4SpatialChord cycle).2)) =
        addE (bf4SpatialChord cycle).1
          (bf4SpatialChord cycle).2 ∧
      pathUsesOnlySpatialTree
          (bf4SpatialTreePath
            (addE (bf4SpatialChord cycle).1
              (bf4SpatialChord cycle).2)) = true := by
  decide

/-! ## 2. Closed loops based at the root -/

def forwardOrientedLink (link : Z4Link) : OrientedBF4Link :=
  { link := link, reverse := false }

def reverseOrientedLink (link : Z4Link) : OrientedBF4Link :=
  { link := link, reverse := true }

/-- The based loop `P(start) · chord · P(end)⁻¹` as a literal oriented word. -/
def bf4BasedCycleWord (cycle : BF4SpatialCycle) : List OrientedBF4Link :=
  (bf4SpatialTreePath (bf4SpatialChord cycle).1).map
      forwardOrientedLink ++
    [forwardOrientedLink (bf4SpatialChord cycle)] ++
      (bf4SpatialTreePath
          (addE (bf4SpatialChord cycle).1
            (bf4SpatialChord cycle).2)).reverse.map
        reverseOrientedLink

def orientedLinkStart (entry : OrientedBF4Link) : Z4Vertex :=
  if entry.reverse then addE entry.link.1 entry.link.2
  else entry.link.1

def orientedLinkEnd (entry : OrientedBF4Link) : Z4Vertex :=
  if entry.reverse then entry.link.1
  else addE entry.link.1 entry.link.2

def orientedLinkPathValid : Z4Vertex → List OrientedBF4Link → Bool
  | _, [] => true
  | vertex, entry :: rest =>
      decide (orientedLinkStart entry = vertex) &&
        orientedLinkPathValid (orientedLinkEnd entry) rest

def orientedLinkPathEnd : Z4Vertex → List OrientedBF4Link → Z4Vertex
  | vertex, [] => vertex
  | _, entry :: rest =>
      orientedLinkPathEnd (orientedLinkEnd entry) rest

/-- Each of the 23 displayed words is a composable loop from the fixed root
back to that root. -/
theorem bf4BasedCycleWord_closed :
    ∀ cycle : BF4SpatialCycle,
      orientedLinkPathValid bf4SpatialTreeRoot
          (bf4BasedCycleWord cycle) = true ∧
      orientedLinkPathEnd bf4SpatialTreeRoot
          (bf4BasedCycleWord cycle) = bf4SpatialTreeRoot := by
  decide

/-! ## 3. Raw and tree-gauge polynomial holonomies -/

def assignedTreePathHolonomy
    (assignment : Z4Link → PolyQuaternion) :
    List Z4Link → PolyQuaternion
  | [] => PolyQuaternion.one
  | link :: rest =>
      PolyQuaternion.mul (assignment link)
        (assignedTreePathHolonomy assignment rest)

/-- `P(start) · U_chord · P(end)⁻¹` for an arbitrary link assignment. -/
def assignedBasedCycleHolonomy
    (assignment : Z4Link → PolyQuaternion)
    (cycle : BF4SpatialCycle) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (assignedTreePathHolonomy assignment
        (bf4SpatialTreePath (bf4SpatialChord cycle).1))
      (assignment (bf4SpatialChord cycle)))
    (PolyQuaternion.conj
      (assignedTreePathHolonomy assignment
        (bf4SpatialTreePath
          (addE (bf4SpatialChord cycle).1
            (bf4SpatialChord cycle).2))))

/-- The genuine based-cycle polynomial in the literal raw 116-link carrier. -/
def exactRawBasedCycleHolonomy
    (cycle : BF4SpatialCycle) : PolyQuaternion :=
  assignedBasedCycleHolonomy
    (correctedSlabLinkPolynomial 1) cycle

/-- The same based-cycle construction after the displayed tree gauge is
applied: tree links are identity and chords are the 23 coordinate blocks. -/
def exactTreeGaugeBasedCycleHolonomy
    (cycle : BF4SpatialCycle) : PolyQuaternion :=
  assignedBasedCycleHolonomy treeGaugeLinkPolynomial cycle

theorem bf4SpatialTreeLink_not_chord
    {link : Z4Link} (hlink : link ∈ bf4SpatialTreeLinks) :
    link ∉ bf4SpatialChordLinks := by
  have hscan :
      bf4SpatialTreeLinks.all
        (fun treeLink => decide (treeLink ∉ bf4SpatialChordLinks)) = true := by
    decide
  exact of_decide_eq_true
    (List.all_eq_true.mp hscan link hlink)

theorem treeGaugeLinkPolynomial_tree
    {link : Z4Link} (hlink : link ∈ bf4SpatialTreeLinks) :
    treeGaugeLinkPolynomial link = PolyQuaternion.one := by
  unfold treeGaugeLinkPolynomial
  rw [if_neg (bf4SpatialTreeLink_not_chord hlink)]

private theorem polyOne_mul_prefix
    {blocks : Nat} : ∀ polynomial : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (polyMul polyOne polynomial) polynomial
  | [] => .nil
  | term :: rest => by
      unfold polyMul List.flatMap
      simp only [polyOne, List.map_cons, List.map_nil,
        List.flatten_cons]
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact Q'.one_mul_eqv term.2
        · intro coordinate _
          simp [RingNormaliser.monoMul, exponentAt]
      · simpa [polyMul, polyOne] using
          (polyOne_mul_prefix (blocks := blocks) rest)

private theorem polyMul_one_prefix
    {blocks : Nat} : ∀ polynomial : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (polyMul polynomial polyOne) polynomial
  | [] => .nil
  | term :: rest => by
      unfold polyMul List.flatMap
      simp only [polyOne, List.map_cons, List.map_nil,
        List.flatten_cons]
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact Q'.mul_one_eqv term.2
        · intro coordinate _
          cases term.1 <;> rfl
      · exact polyMul_one_prefix rest

private theorem polyMul_nil_right (polynomial : RatPoly) :
    polyMul polynomial [] = [] := by
  simp [polyMul]

private theorem polyQuaternion_one_mul_prefix
    {blocks : Nat} (quaternion : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (PolyQuaternion.mul PolyQuaternion.one quaternion) quaternion := by
  constructor
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.scalar)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.iPart)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.jPart)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.kPart)

private theorem polyQuaternion_mul_one_prefix
    {blocks : Nat} (quaternion : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (PolyQuaternion.mul quaternion PolyQuaternion.one) quaternion := by
  constructor
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyNeg, polyMul_nil_right] using
      (polyMul_one_prefix (blocks := blocks) quaternion.scalar)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyNeg, polyMul_nil_right] using
      (polyMul_one_prefix (blocks := blocks) quaternion.iPart)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyNeg, polyMul_nil_right] using
      (polyMul_one_prefix (blocks := blocks) quaternion.jPart)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyNeg, polyMul_nil_right] using
      (polyMul_one_prefix (blocks := blocks) quaternion.kPart)

private theorem assignedTreePathHolonomy_treeGauge_prefix_one
    {path : List Z4Link}
    (hpath : pathUsesOnlySpatialTree path = true) :
    QuaternionPrefixPolyQuaternionEqv 23
      (assignedTreePathHolonomy treeGaugeLinkPolynomial path)
      PolyQuaternion.one := by
  induction path with
  | nil => exact QuaternionPrefixPolyQuaternionEqv.refl 23 _
  | cons link rest induction =>
      have hparts := List.all_eq_true.mp hpath
      have hlink : link ∈ bf4SpatialTreeLinks :=
        of_decide_eq_true (hparts link List.mem_cons_self)
      have hrest : pathUsesOnlySpatialTree rest = true := by
        exact List.all_eq_true.mpr fun other hother =>
          hparts other (List.mem_cons_of_mem link hother)
      unfold assignedTreePathHolonomy
      rw [treeGaugeLinkPolynomial_tree hlink]
      exact QuaternionPrefixPolyQuaternionEqv.trans
        (QuaternionPrefixPolyQuaternionEqv.mul
          (QuaternionPrefixPolyQuaternionEqv.refl 23 PolyQuaternion.one)
          (induction hrest))
        (polyQuaternion_one_mul_prefix PolyQuaternion.one)

/-- **Based-cycle coordinate theorem.**  Once the displayed tree links are
identity, the rooted loop holonomy of chord `cycle` is exactly its polynomial
quaternion coordinate, up to harmless zero padding on the 23-block prefix. -/
theorem exactTreeGaugeBasedCycleHolonomy_prefix_coordinate
    (cycle : BF4SpatialCycle) :
    QuaternionPrefixPolyQuaternionEqv 23
      (exactTreeGaugeBasedCycleHolonomy cycle)
      (PolyQuaternion.coordinateVariable cycle.val) := by
  have hpaths := bf4SpatialChordEndpointPaths_valid cycle
  have hstart :=
    assignedTreePathHolonomy_treeGauge_prefix_one hpaths.2.2.1
  have hend :=
    assignedTreePathHolonomy_treeGauge_prefix_one hpaths.2.2.2.2.2
  have hchord :
      QuaternionPrefixPolyQuaternionEqv 23
        (treeGaugeLinkPolynomial (bf4SpatialChord cycle))
        (PolyQuaternion.coordinateVariable cycle.val) := by
    rw [treeGaugeLinkPolynomial_chord cycle]
    exact QuaternionPrefixPolyQuaternionEqv.refl 23 _
  have hendConj :
      QuaternionPrefixPolyQuaternionEqv 23
        (PolyQuaternion.conj
          (assignedTreePathHolonomy treeGaugeLinkPolynomial
            (bf4SpatialTreePath
              (addE (bf4SpatialChord cycle).1
                (bf4SpatialChord cycle).2))))
        PolyQuaternion.one := by
    simpa [PolyQuaternion.conj, PolyQuaternion.one, polyNeg, polyZero] using
      QuaternionPrefixPolyQuaternionEqv.conj hend
  unfold exactTreeGaugeBasedCycleHolonomy assignedBasedCycleHolonomy
  refine QuaternionPrefixPolyQuaternionEqv.trans
    (QuaternionPrefixPolyQuaternionEqv.mul
      (QuaternionPrefixPolyQuaternionEqv.mul hstart hchord)
      hendConj) ?_
  refine QuaternionPrefixPolyQuaternionEqv.trans
    (QuaternionPrefixPolyQuaternionEqv.mul
      (polyQuaternion_one_mul_prefix
        (PolyQuaternion.coordinateVariable cycle.val))
      (QuaternionPrefixPolyQuaternionEqv.refl 23 PolyQuaternion.one)) ?_
  exact polyQuaternion_mul_one_prefix
    (PolyQuaternion.coordinateVariable cycle.val)

/-! ## 4. The five retained based cycles -/

theorem bf4TransmittedBasedCycleIndices :
    bf4TransmittedCycleTable.map (fun cycle => cycle.val) =
      [0, 4, 5, 6, 10] := by
  rfl

def bf4TransmittedBasedCycleWords : List (List OrientedBF4Link) :=
  bf4TransmittedCycleTable.map bf4BasedCycleWord

theorem bf4TransmittedBasedCycleWords_length :
    bf4TransmittedBasedCycleWords.length = 5 := by
  simp [bf4TransmittedBasedCycleWords,
    bf4TransmittedCycleTable_length]

theorem bf4TransmittedBasedCycleWords_closed
    {word : List OrientedBF4Link}
    (hword : word ∈ bf4TransmittedBasedCycleWords) :
    orientedLinkPathValid bf4SpatialTreeRoot word = true ∧
      orientedLinkPathEnd bf4SpatialTreeRoot word =
        bf4SpatialTreeRoot := by
  rcases List.mem_map.mp hword with ⟨cycle, _, rfl⟩
  exact bf4BasedCycleWord_closed cycle

/-- The five genuine raw based-cycle polynomials, before tree gauge fixing,
in canonical transmitted order. -/
def exactRawTransmittedBasedCycleHolonomies : List PolyQuaternion :=
  bf4TransmittedCycleTable.map exactRawBasedCycleHolonomy

/-- The same five based-cycle polynomials after the explicit tree gauge. -/
def exactTreeGaugeTransmittedBasedCycleHolonomies : List PolyQuaternion :=
  bf4TransmittedCycleTable.map exactTreeGaugeBasedCycleHolonomy

theorem exactRawTransmittedBasedCycleHolonomies_length :
    exactRawTransmittedBasedCycleHolonomies.length = 5 := by
  simp [exactRawTransmittedBasedCycleHolonomies,
    bf4TransmittedCycleTable_length]

theorem exactTreeGaugeTransmittedBasedCycleHolonomies_length :
    exactTreeGaugeTransmittedBasedCycleHolonomies.length = 5 := by
  simp [exactTreeGaugeTransmittedBasedCycleHolonomies,
    bf4TransmittedCycleTable_length]

def transmittedBasedCycleMonomial (monomial : List Nat) : List Nat :=
  bf4TransmittedCycleTable.flatMap fun cycle =>
    [exponentAt monomial (4 * cycle.val),
     exponentAt monomial (4 * cycle.val + 1),
     exponentAt monomial (4 * cycle.val + 2),
     exponentAt monomial (4 * cycle.val + 3)]

/-- The existing five-coordinate contraction order is exactly the order of
the five rooted based cycles constructed above. -/
theorem retainedFiveMonomial_eq_transmittedBasedCycleMonomial
    (monomial : List Nat) :
    retainedFiveMonomial monomial =
      transmittedBasedCycleMonomial monomial := by
  simp [retainedFiveMonomial, transmittedBasedCycleMonomial,
    bf4TransmittedCycleTable]

/-- Each retained coordinate has the based-loop interpretation supplied by
the general 23-cycle theorem. -/
theorem transmittedTreeGaugeBasedCycleHolonomy_prefix_coordinate
    (coordinate : BF4TemporalHolonomy) :
    QuaternionPrefixPolyQuaternionEqv 23
      (exactTreeGaugeBasedCycleHolonomy
        (transmittedSpatialCycle coordinate))
      (PolyQuaternion.coordinateVariable
        (transmittedSpatialCycle coordinate).val) :=
  exactTreeGaugeBasedCycleHolonomy_prefix_coordinate _

end YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles

#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles.bf4SpatialChordEndpointPaths_valid
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles.bf4BasedCycleWord_closed
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles.bf4TransmittedBasedCycleWords_closed
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles.exactTreeGaugeBasedCycleHolonomy_prefix_coordinate
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles.retainedFiveMonomial_eq_transmittedBasedCycleMonomial
#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles.transmittedTreeGaugeBasedCycleHolonomy_prefix_coordinate
