/-
# Symbolic Boolean resolution of the paired elementary-cube network

This leaf keeps the twenty-four matrix indices as a recursive symbolic sum.
It extracts the twelve fundamental Schur factors structurally, identifies
their Boolean matching graph with eight independent vertex triangles, and
reduces only the generic three-index local problem.  The depth-twenty-four
sum is never unfolded, simplified, evaluated, or printed.

The resulting polynomial is the deliberately paired Haar-facing network.
No equality with the six-face production representative is claimed here;
that still requires an explicit raw-representative or Haar-level bridge.

# Axiom and resource gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
Only the one-link sixteen-case delta and the one-vertex eight-case sum may be
reduced concretely.
-/

import YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
import YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction

namespace YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
open YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-! ## 1. Opaque paired trace network and abstract Haar reduction -/

/-- The honest paired cube network.  This definition must remain opaque at
depth twenty four. -/
def radiusZeroElementaryCubePairedTraceNetwork : ComplexRatPoly :=
  complexRatPolyBoolSum 24 radiusZeroElementaryCubePairedSummand

/-- Haar linearity and the fixed-assignment twelve-link theorem reduce the
opaque polynomial network to the equally opaque symbolic delta sum. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubePairedTraceNetwork :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubePairedTraceNetwork)
      (rationalComplexBoolSum 24
        radiusZeroElementaryCubeSchurDeltaValue) := by
  exact rationalComplexEqv_trans
    (finiteProductHaarComplex_boolSum
      (adjacentEvenActiveLinks 0).length 24
      radiusZeroElementaryCubePairedSummand)
    (rationalComplexBoolSum_congr 24 (fun assignment =>
      finiteProductHaarComplex_radiusZeroElementaryCubePairedSummand
        assignment))

/-! ## 2. Exact tag graph certificates -/

/-- The two crossed equality edges imposed by one oriented link pair. -/
def TaggedCubeLinkPair.crossedTagEqualityPairs
    (pair : TaggedCubeLinkPair) : List (Nat × Nat) :=
  [(pair.forwardRowTag, pair.reverseColumnTag),
   (pair.forwardColumnTag, pair.reverseRowTag)]

/-- All twenty-four equality edges, in physical-link schedule order. -/
def radiusZeroElementaryCubeCrossedTagEqualityPairs : List (Nat × Nat) :=
  radiusZeroElementaryCubeTaggedLinkPairs.flatMap
    TaggedCubeLinkPair.crossedTagEqualityPairs

theorem radiusZeroElementaryCubeCrossedTagEqualityPairs_exact :
    radiusZeroElementaryCubeCrossedTagEqualityPairs =
      [(1,0), (4,3), (0,2), (9,10), (9,11), (6,7),
       (5,3), (8,6), (2,1), (13,12), (14,12), (16,15),
       (4,5), (15,17), (13,14), (21,22), (11,10), (23,21),
       (23,22), (19,18), (16,17), (18,20), (8,7), (20,19)] := by
  decide

/-- A vertex-triangle presentation of the intended equality constraints.
The universal Boolean theorem below proves that this presentation has exactly
the same solutions as the literal twelve-link graph.  A literal edge-list
permutation is not claimed here. -/
def radiusZeroElementaryCubeVertexTriangleEqualityPairs : List (Nat × Nat) :=
  [(1,0), (0,2), (2,1),
   (4,3), (5,3), (4,5),
   (6,7), (8,6), (8,7),
   (9,10), (9,11), (11,10),
   (13,12), (14,12), (13,14),
   (16,15), (15,17), (16,17),
   (19,18), (18,20), (20,19),
   (21,22), (23,21), (23,22)]

theorem radiusZeroElementaryCubeCrossedTagEqualityPairs_length :
    radiusZeroElementaryCubeCrossedTagEqualityPairs.length = 24 := by
  decide

/-- The eight vertex-major triples covered by the tag numbering. -/
def radiusZeroElementaryCubeVertexTagTriples : List (List Nat) :=
  [[0,1,2], [3,4,5], [6,7,8], [9,10,11],
   [12,13,14], [15,16,17], [18,19,20], [21,22,23]]

theorem radiusZeroElementaryCubeVertexTagTriples_length :
    radiusZeroElementaryCubeVertexTagTriples.length = 8 := by
  decide

theorem radiusZeroElementaryCubeVertexTagTriples_flatten :
    radiusZeroElementaryCubeVertexTagTriples.flatten = List.range 24 := by
  decide

theorem radiusZeroElementaryCubeVertexTriangleEqualityPairs_length :
    radiusZeroElementaryCubeVertexTriangleEqualityPairs.length = 24 := by
  decide

theorem radiusZeroElementaryCubeVertexTriangleEqualityPairs_nodup :
    radiusZeroElementaryCubeVertexTriangleEqualityPairs.Nodup := by
  decide

/-! ## 3. Pure-real Schur fold normal form -/

/-- Embed one constructive rational as a real rational-complex value. -/
def pureReal (value : Q') : RationalComplex := (value, 0)

/-- The rational zero/one indicator of a decidable Boolean condition. -/
def qBoolIndicator (condition : Bool) : Q' :=
  if condition then 1 else 0

theorem qBoolIndicator_and (left right : Bool) :
    qBoolIndicator (left && right) ≈
      qBoolIndicator left * qBoolIndicator right := by
  cases left <;> cases right <;> decide

/-- Whether the two matrix-index strands cross correctly at one link. -/
def contractionMatchBool
    (step : OrientedFundamentalContraction) : Bool :=
  decide (step.forwardRow = step.reverseColumn ∧
    step.forwardColumn = step.reverseRow)

/-- Product of the Boolean match indicators, in the same tail-first order as
the Schur delta fold. -/
def contractionMatchProduct :
    List OrientedFundamentalContraction → Q'
  | [] => 1
  | step :: steps =>
      contractionMatchProduct steps * qBoolIndicator (contractionMatchBool step)

/-- Boolean conjunction of every crossed-index condition in a schedule. -/
def contractionAllMatchBool :
    List OrientedFundamentalContraction → Bool
  | [] => true
  | step :: steps =>
      contractionMatchBool step && contractionAllMatchBool steps

theorem contractionMatchProduct_eqv_indicator :
    ∀ schedule : List OrientedFundamentalContraction,
      contractionMatchProduct schedule ≈
        qBoolIndicator (contractionAllMatchBool schedule)
  | [] => by decide
  | step :: steps => by
      change
        contractionMatchProduct steps *
            qBoolIndicator (contractionMatchBool step) ≈
          qBoolIndicator
            (contractionMatchBool step && contractionAllMatchBool steps)
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (contractionMatchProduct_eqv_indicator steps))
        (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv
            (qBoolIndicator (contractionAllMatchBool steps))
            (qBoolIndicator (contractionMatchBool step)))
          (Q'.eqv_symm
            (qBoolIndicator_and
              (contractionMatchBool step)
              (contractionAllMatchBool steps))))

theorem pureReal_congr {left right : Q'} (h : left ≈ right) :
    RationalComplexEqv (pureReal left) (pureReal right) :=
  ⟨h, Q'.eqv_refl 0⟩

theorem rationalComplexMul_pureReal (left right : Q') :
    RationalComplexEqv
      (rationalComplexMul (pureReal left) (pureReal right))
      (pureReal (left * right)) := by
  unfold rationalComplexMul pureReal RationalComplexEqv
  constructor <;> ring_qeqv

theorem contraction_delta_eqv_pureReal
    (step : OrientedFundamentalContraction) :
    RationalComplexEqv step.delta
      (pureReal (Q'.invSucc 1 *
        qBoolIndicator (contractionMatchBool step))) := by
  rcases step with ⟨block, forwardRow, forwardColumn,
    reverseRow, reverseColumn⟩
  change RationalComplexEqv
    (orientedFundamentalSchurDelta
      forwardRow forwardColumn reverseRow reverseColumn)
    (pureReal (Q'.invSucc 1 * qBoolIndicator
      (decide (forwardRow = reverseColumn ∧
        forwardColumn = reverseRow))))
  clear block
  cases forwardRow <;> cases forwardColumn <;>
    cases reverseRow <;> cases reverseColumn <;>
    unfold qBoolIndicator pureReal orientedFundamentalSchurDelta <;>
    constructor <;> decide

/-- A whole fixed schedule is twelve half-factors times its Boolean matching
indicator product.  The induction is over links, never assignments. -/
theorem schurDeltaProductFrom_eqv_pureReal (initial : Q') :
    ∀ schedule : List OrientedFundamentalContraction,
      RationalComplexEqv
        (schurDeltaProductFrom (pureReal initial) schedule)
        (pureReal
          ((initial * qpow (Q'.invSucc 1) schedule.length) *
            contractionMatchProduct schedule))
  | [] => by
      change RationalComplexEqv
        (pureReal initial) (pureReal ((initial * 1) * 1))
      exact pureReal_congr (by ring_qeqv)
  | step :: steps => by
      change RationalComplexEqv
        (rationalComplexMul
          (schurDeltaProductFrom (pureReal initial) steps) step.delta)
        (pureReal
          ((initial * qpow (Q'.invSucc 1) (steps.length + 1)) *
            (contractionMatchProduct steps *
              qBoolIndicator (contractionMatchBool step))))
      refine rationalComplexEqv_trans
        (rationalComplexMul_congr
          (schurDeltaProductFrom_eqv_pureReal initial steps)
          (contraction_delta_eqv_pureReal step)) ?_
      refine rationalComplexEqv_trans
        (rationalComplexMul_pureReal _ _) ?_
      apply pureReal_congr
      simp only [qpow_succ]
      ring_qeqv

theorem schurDeltaProduct_eqv_pureReal
    (schedule : List OrientedFundamentalContraction) :
    RationalComplexEqv
      (schurDeltaProduct schedule)
      (pureReal
        (qpow (Q'.invSucc 1) schedule.length *
          contractionMatchProduct schedule)) := by
  refine rationalComplexEqv_trans
    (schurDeltaProductFrom_eqv_pureReal 1 schedule) ?_
  apply pureReal_congr
  ring_qeqv

/-! ## 4. Generic three-index structural sum -/

def rationalComplexThreeBoolBind
    (family : Bool → Bool → Bool → RationalComplex) : RationalComplex :=
  rationalComplexBoolBind (fun first =>
    rationalComplexBoolBind (fun second =>
      rationalComplexBoolBind (fun third => family first second third)))

theorem rationalComplexThreeBoolBind_congr
    {left right : Bool → Bool → Bool → RationalComplex}
    (hpointwise : ∀ first second third,
      RationalComplexEqv
        (left first second third) (right first second third)) :
    RationalComplexEqv
      (rationalComplexThreeBoolBind left)
      (rationalComplexThreeBoolBind right) := by
  unfold rationalComplexThreeBoolBind
  exact rationalComplexBoolBind_congr (fun first =>
    rationalComplexBoolBind_congr (fun second =>
      rationalComplexBoolBind_congr (fun third =>
        hpointwise first second third)))

theorem rationalComplexThreeBoolBind_mul
    (family : Bool → Bool → Bool → RationalComplex)
    (factor : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul (rationalComplexThreeBoolBind family) factor)
      (rationalComplexThreeBoolBind
        (fun first second third =>
          rationalComplexMul (family first second third) factor)) := by
  unfold rationalComplexThreeBoolBind
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_mul _ factor) ?_
  apply rationalComplexBoolBind_congr
  intro first
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_mul _ factor) ?_
  apply rationalComplexBoolBind_congr
  intro second
  exact rationalComplexBoolBind_mul
    (fun third => family first second third) factor

/-- This equation opens exactly three leading binders, independently of the
symbolic tail depth. -/
theorem rationalComplexBoolSum_add_three
    (depth : Nat) (family : List Bool → RationalComplex) :
    rationalComplexBoolSum (depth + 3) family =
      rationalComplexThreeBoolBind (fun first second third =>
        rationalComplexBoolSum depth (fun rest =>
          family (first :: second :: third :: rest))) := rfl

def rationalComplexPower (base : RationalComplex) : Nat → RationalComplex
  | 0 => rationalComplexOne
  | exponent + 1 =>
      rationalComplexMul base (rationalComplexPower base exponent)

/-- Default-safe product of consecutive three-index local factors. -/
def threeChunkProduct
    (localFactor : Bool → Bool → Bool → RationalComplex) :
    Nat → List Bool → RationalComplex
  | 0, _ => rationalComplexOne
  | count + 1, assignment =>
      rationalComplexMul
        (localFactor (assignment.getD 0 false)
          (assignment.getD 1 false)
          (assignment.getD 2 false))
        (threeChunkProduct localFactor count (assignment.drop 3))

/-- Boolean form of the local equality triangle. -/
def equalityTriangleMatchBool
    (first second third : Bool) : Bool :=
  decide (first = second ∧ second = third)

/-- Tail-first scalar product of consecutive triangle indicators. -/
def triangleMatchProduct : Nat → List Bool → Q'
  | 0, _ => 1
  | count + 1, assignment =>
      triangleMatchProduct count (assignment.drop 3) *
        qBoolIndicator
          (equalityTriangleMatchBool
            (cubeTagValue assignment 0)
            (cubeTagValue assignment 1)
            (cubeTagValue assignment 2))

/-- Boolean conjunction of the same consecutive equality triangles. -/
def triangleAllMatchBool : Nat → List Bool → Bool
  | 0, _ => true
  | count + 1, assignment =>
      equalityTriangleMatchBool
          (cubeTagValue assignment 0)
          (cubeTagValue assignment 1)
          (cubeTagValue assignment 2) &&
        triangleAllMatchBool count (assignment.drop 3)

theorem triangleMatchProduct_eqv_indicator :
    ∀ count assignment,
      triangleMatchProduct count assignment ≈
        qBoolIndicator (triangleAllMatchBool count assignment)
  | 0, _ => by
      change (1 : Q') ≈ qBoolIndicator true
      decide
  | count + 1, assignment => by
      change
        triangleMatchProduct count (assignment.drop 3) *
            qBoolIndicator
              (equalityTriangleMatchBool
                (cubeTagValue assignment 0)
                (cubeTagValue assignment 1)
                (cubeTagValue assignment 2)) ≈
          qBoolIndicator
            (equalityTriangleMatchBool
                (cubeTagValue assignment 0)
                (cubeTagValue assignment 1)
                (cubeTagValue assignment 2) &&
              triangleAllMatchBool count (assignment.drop 3))
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (triangleMatchProduct_eqv_indicator count (assignment.drop 3)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv _ _)
          (Q'.eqv_symm (qBoolIndicator_and _ _)))

theorem cubeTagValue_drop
    (assignment : List Bool) (offset tag : Nat) :
    cubeTagValue (assignment.drop offset) tag =
      cubeTagValue assignment (offset + tag) := by
  unfold cubeTagValue
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The literal twelve-link Schur graph is exactly the conjunction of the
eight consecutive vertex triangles.  This holds even on short lists because
both sides use the same false default. -/
theorem radiusZeroElementaryCubeContractionAllMatchBool_eq_triangles
    (assignment : List Bool) :
    contractionAllMatchBool
        (radiusZeroElementaryCubeContractionSchedule assignment) =
      triangleAllMatchBool 8 assignment := by
  rw [Bool.eq_iff_iff]
  simp only [radiusZeroElementaryCubeContractionSchedule,
    radiusZeroElementaryCubeTaggedLinkPairs, List.map,
    TaggedCubeLinkPair.contraction, contractionAllMatchBool,
    contractionMatchBool, triangleAllMatchBool,
    equalityTriangleMatchBool, cubeTagValue_drop,
    Bool.and_eq_true, decide_eq_true_eq, Nat.reduceAdd]
  constructor
  · intro h
    rcases h with
      ⟨⟨h10, h43⟩, ⟨h02, h910⟩, ⟨h911, h67⟩,
       ⟨h53, h86⟩, ⟨h21, h1312⟩, ⟨h1412, h1615⟩,
       ⟨h45, h1517⟩, ⟨h1314, h2122⟩, ⟨h1110, h2321⟩,
       ⟨h2322, h1918⟩, ⟨h1617, h1820⟩, ⟨h87, h2019⟩, _⟩
    simp_all
  · intro h
    rcases h with
      ⟨⟨h01, h12⟩, ⟨h34, h45⟩, ⟨h67, h78⟩,
       ⟨h910, h1011⟩, ⟨h1213, h1314⟩, ⟨h1516, h1617⟩,
       ⟨h1819, h1920⟩, ⟨h2122, h2223⟩, _⟩
    simp_all

theorem rationalComplexBoolSum_threeChunkProduct
    (localFactor : Bool → Bool → Bool → RationalComplex) :
    ∀ count : Nat,
      RationalComplexEqv
        (rationalComplexBoolSum (3 * count)
          (threeChunkProduct localFactor count))
        (rationalComplexPower
          (rationalComplexThreeBoolBind localFactor) count)
  | 0 => by
      change RationalComplexEqv rationalComplexOne rationalComplexOne
      exact rationalComplexEqv_refl _
  | count + 1 => by
      rw [show 3 * (count + 1) = 3 * count + 3 by omega]
      rw [rationalComplexBoolSum_add_three]
      simp only [threeChunkProduct, List.getD_cons_zero,
        List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
      change RationalComplexEqv
        (rationalComplexThreeBoolBind (fun first second third =>
          rationalComplexBoolSum (3 * count) (fun rest =>
            rationalComplexMul (localFactor first second third)
              (threeChunkProduct localFactor count rest))))
        (rationalComplexMul
          (rationalComplexThreeBoolBind localFactor)
          (rationalComplexPower
            (rationalComplexThreeBoolBind localFactor) count))
      refine rationalComplexEqv_trans
        (rationalComplexThreeBoolBind_congr (fun first second third =>
          rationalComplexEqv_trans
            (rationalComplexEqv_symm
              (rationalComplexMul_boolSum
                (localFactor first second third) (3 * count)
                (threeChunkProduct localFactor count)))
            (rationalComplexMul_congr_right (localFactor first second third)
              (rationalComplexBoolSum_threeChunkProduct
                localFactor count)))) ?_
      exact rationalComplexEqv_symm
        (rationalComplexThreeBoolBind_mul localFactor
          (rationalComplexPower
            (rationalComplexThreeBoolBind localFactor) count))

theorem rationalComplexPower_congr
    {left right : RationalComplex}
    (h : RationalComplexEqv left right) :
    ∀ exponent,
      RationalComplexEqv
        (rationalComplexPower left exponent)
        (rationalComplexPower right exponent)
  | 0 => rationalComplexEqv_refl _
  | exponent + 1 =>
      rationalComplexMul_congr h
        (rationalComplexPower_congr h exponent)

theorem rationalComplexPower_pureReal (value : Q') :
    ∀ exponent,
      RationalComplexEqv
        (rationalComplexPower (pureReal value) exponent)
        (pureReal (qpow value exponent))
  | 0 => by
      unfold rationalComplexPower rationalComplexOne pureReal
      exact rationalComplexEqv_refl _
  | exponent + 1 => by
      change RationalComplexEqv
        (rationalComplexMul (pureReal value)
          (rationalComplexPower (pureReal value) exponent))
        (pureReal (qpow value exponent * value))
      refine rationalComplexEqv_trans
        (rationalComplexMul_congr (rationalComplexEqv_refl _)
          (rationalComplexPower_pureReal value exponent)) ?_
      refine rationalComplexEqv_trans
        (rationalComplexMul_pureReal value (qpow value exponent)) ?_
      exact pureReal_congr (Q'.mul_comm_eqv value (qpow value exponent))

/-! ## 5. One safe vertex computation -/

/-- A single equality triangle: only the two constant Boolean triples
survive. -/
def equalityTriangleLocal
    (first second third : Bool) : RationalComplex :=
  pureReal (qBoolIndicator
    (equalityTriangleMatchBool first second third))

theorem threeChunkProduct_equalityTriangleLocal_eqv :
    ∀ count assignment,
      RationalComplexEqv
        (threeChunkProduct equalityTriangleLocal count assignment)
        (pureReal (triangleMatchProduct count assignment))
  | 0, _ => by
      unfold threeChunkProduct triangleMatchProduct
        rationalComplexOne pureReal
      exact rationalComplexEqv_refl _
  | count + 1, assignment => by
      change RationalComplexEqv
        (rationalComplexMul
          (pureReal (qBoolIndicator
            (equalityTriangleMatchBool
              (assignment.getD 0 false)
              (assignment.getD 1 false)
              (assignment.getD 2 false))))
          (threeChunkProduct equalityTriangleLocal count
            (assignment.drop 3)))
        (pureReal
          (triangleMatchProduct count (assignment.drop 3) *
            qBoolIndicator
              (equalityTriangleMatchBool
                (assignment.getD 0 false)
                (assignment.getD 1 false)
                (assignment.getD 2 false))))
      refine rationalComplexEqv_trans
        (rationalComplexMul_congr (rationalComplexEqv_refl _)
          (threeChunkProduct_equalityTriangleLocal_eqv
            count (assignment.drop 3))) ?_
      refine rationalComplexEqv_trans
        (rationalComplexMul_pureReal _ _) ?_
      exact pureReal_congr (Q'.mul_comm_eqv _ _)

theorem radiusZeroElementaryCubeContractionMatchProduct_eqv_triangles
    (assignment : List Bool) :
    contractionMatchProduct
        (radiusZeroElementaryCubeContractionSchedule assignment) ≈
      triangleMatchProduct 8 assignment := by
  exact Q'.eqv_trans _ _ _
    (contractionMatchProduct_eqv_indicator
      (radiusZeroElementaryCubeContractionSchedule assignment))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg qBoolIndicator
        (radiusZeroElementaryCubeContractionAllMatchBool_eq_triangles
          assignment)))
      (Q'.eqv_symm
        (triangleMatchProduct_eqv_indicator 8 assignment)))

theorem rationalComplexThreeBoolBind_equalityTriangleLocal :
    RationalComplexEqv
      (rationalComplexThreeBoolBind equalityTriangleLocal)
      (pureReal (Q'.ofNat 2)) := by
  unfold rationalComplexThreeBoolBind rationalComplexBoolBind
    equalityTriangleLocal qBoolIndicator pureReal rationalComplexAdd
    RationalComplexEqv
  constructor <;> decide

theorem rationalComplexBoolSum_eight_equalityTriangles :
    RationalComplexEqv
      (rationalComplexBoolSum 24
        (threeChunkProduct equalityTriangleLocal 8))
      (pureReal (qpow (Q'.ofNat 2) 8)) := by
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_threeChunkProduct equalityTriangleLocal 8) ?_
  refine rationalComplexEqv_trans
    (rationalComplexPower_congr
      rationalComplexThreeBoolBind_equalityTriangleLocal 8) ?_
  exact rationalComplexPower_pureReal (Q'.ofNat 2) 8

/-! ## 6. Exact symbolic delta sum and paired-network Haar value -/

/-- The fully resolved value of one symbolic Boolean assignment: twelve
fundamental Schur half-factors times eight consecutive vertex-triangle
indicators. -/
def radiusZeroElementaryCubeResolvedDeltaValue
    (assignment : List Bool) : RationalComplex :=
  rationalComplexMul
    (pureReal (qpow (Q'.invSucc 1) 12))
    (threeChunkProduct equalityTriangleLocal 8 assignment)

/-- The rational indicator product of the literal twelve-link schedule is
the same pure-real value as the product of the eight vertex-local factors. -/
theorem pureReal_radiusZeroElementaryCubeContractionMatchProduct_eqv_threeChunk
    (assignment : List Bool) :
    RationalComplexEqv
      (pureReal (contractionMatchProduct
        (radiusZeroElementaryCubeContractionSchedule assignment)))
      (threeChunkProduct equalityTriangleLocal 8 assignment) := by
  exact rationalComplexEqv_trans
    (pureReal_congr
      (radiusZeroElementaryCubeContractionMatchProduct_eqv_triangles
        assignment))
    (rationalComplexEqv_symm
      (threeChunkProduct_equalityTriangleLocal_eqv 8 assignment))

/-- Pointwise Schur resolution, without enumerating any of the twenty-four
Boolean indices. -/
theorem radiusZeroElementaryCubeSchurDeltaValue_eqv_resolved
    (assignment : List Bool) :
    RationalComplexEqv
      (radiusZeroElementaryCubeSchurDeltaValue assignment)
      (radiusZeroElementaryCubeResolvedDeltaValue assignment) := by
  unfold radiusZeroElementaryCubeSchurDeltaValue
    radiusZeroElementaryCubeResolvedDeltaValue
  refine rationalComplexEqv_trans
    (schurDeltaProduct_eqv_pureReal
      (radiusZeroElementaryCubeContractionSchedule assignment)) ?_
  rw [radiusZeroElementaryCubeContractionSchedule_length assignment]
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexMul_pureReal
        (qpow (Q'.invSucc 1) 12)
        (contractionMatchProduct
          (radiusZeroElementaryCubeContractionSchedule assignment)))) ?_
  exact rationalComplexMul_congr_right _
    (pureReal_radiusZeroElementaryCubeContractionMatchProduct_eqv_threeChunk
      assignment)

/-- The opaque depth-twenty-four delta sum is evaluated by congruence,
linearity, and the generic three-index structural theorem.  In particular,
this proof never unfolds the recursive sum at depth twenty four. -/
theorem rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue :
    RationalComplexEqv
      (rationalComplexBoolSum 24
        radiusZeroElementaryCubeSchurDeltaValue)
      (pureReal
        (qpow (Q'.invSucc 1) 12 * qpow (Q'.ofNat 2) 8)) := by
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr 24 (fun assignment =>
      radiusZeroElementaryCubeSchurDeltaValue_eqv_resolved assignment)) ?_
  unfold radiusZeroElementaryCubeResolvedDeltaValue
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexMul_boolSum
        (pureReal (qpow (Q'.invSucc 1) 12)) 24
        (threeChunkProduct equalityTriangleLocal 8))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_congr_right _
      rationalComplexBoolSum_eight_equalityTriangles) ?_
  exact rationalComplexMul_pureReal _ _

/-- The symbolic delta sum agrees with the geometry-derived post-Schur
factor: eight tag-triangle sums and twelve fundamental link contractions give
the same scalar as the independently counted eight vertices and twelve links.
Tag-to-geometric-endpoint incidence remains part of the production bridge. -/
theorem rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue_eqv_postSchur :
    RationalComplexEqv
      (rationalComplexBoolSum 24
        radiusZeroElementaryCubeSchurDeltaValue)
      (pureReal radiusZeroElementaryCubePostSchurResolvedFactor) := by
  refine rationalComplexEqv_trans
    rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue ?_
  apply pureReal_congr
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  change elementaryCubeEulerSchurFactor ≈
    radiusZeroElementaryCubePostSchurResolvedFactor
  exact Q'.eqv_of_eq
    radiusZeroElementaryCubePostSchurResolvedFactor_eq_euler.symm

/-- Exact value of the fully resolved symbolic delta sum. -/
theorem rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue_exact :
    RationalComplexEqv
      (rationalComplexBoolSum 24
        radiusZeroElementaryCubeSchurDeltaValue)
      (Q'.mkPos 1 16 (by decide), 0) := by
  exact rationalComplexEqv_trans
    rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue_eqv_postSchur
    (pureReal_congr radiusZeroElementaryCubePostSchurResolvedFactor_exact)

/-- **Exact Haar value of the paired elementary-cube trace network.**

This closes the deliberately paired polynomial network at `1/16`.  It does
not identify that network with the six-face production representative; that
separate raw-polynomial or Haar-level bridge remains the next wiring task. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubePairedTraceNetwork_exact :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubePairedTraceNetwork)
      (Q'.mkPos 1 16 (by decide), 0) := by
  exact rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroElementaryCubePairedTraceNetwork
    rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue_exact

#print axioms finiteProductHaarComplex_radiusZeroElementaryCubePairedTraceNetwork
#print axioms radiusZeroElementaryCubeCrossedTagEqualityPairs_length
#print axioms schurDeltaProduct_eqv_pureReal
#print axioms rationalComplexBoolSum_threeChunkProduct
#print axioms radiusZeroElementaryCubeContractionAllMatchBool_eq_triangles
#print axioms radiusZeroElementaryCubeSchurDeltaValue_eqv_resolved
#print axioms rationalComplexThreeBoolBind_equalityTriangleLocal
#print axioms rationalComplexBoolSum_eight_equalityTriangles
#print axioms rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue_exact
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubePairedTraceNetwork_exact

end YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution
