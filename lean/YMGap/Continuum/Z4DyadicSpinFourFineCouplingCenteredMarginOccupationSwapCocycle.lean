/-
# The geometric occupation skew is a component-exchange cocycle

The exact occupation transport theorem shows that a target-rooted support
swap exchanges the two replicas' occupations inside one component and leaves
their outside occupations fixed.  This module proves the corresponding exact
identity for the geometric-sum skew which carries the cutoff-one centered
mass determinant.

Writing

  K_w(a,b) = geomSum(w,a) * w^b - w^a * geomSum(w,b),

the division-free cocycle law is

  K_w(u+p,v+q)
    = K_w(u+q,v+p) + (w^u+w^v) * K_w(p,q).

Here `u,v` are outside exponents and `p,q` are component exponents.  The
canonical paired-support specialization therefore says that the change in
the full occupation cofactor is exactly an outside heat multiplier times the
component's own skew.  This is the algebraic telescoping interface needed by
a subsequent connected-component cancellation or estimate.

No summation over components, cancellation, or bound is asserted here.  In
particular this proves no uniform covariance estimate, continuum measure,
OS/GNS reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: exact rational setoid algebra and the already proved
finite occupation transport only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈
      factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _
    (Q'.mul_add_eqv factor left (-right)) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

private theorem add_mul_sub_expand_local
    (left right positive negative : Q') :
    (left + right) * (positive - negative) ≈
      (left * positive - left * negative) +
        (right * positive - right * negative) := by
  refine Q'.eqv_trans _
    (left * (positive - negative) +
      right * (positive - negative)) _ ?_ ?_
  · exact Q'.add_mul_eqv left right (positive - negative)
  exact Q'.add_eqv_congr'
    (mul_sub_expand_local left positive negative)
    (mul_sub_expand_local right positive negative)

private theorem add_neg_self_eqv_local (value : Q') :
    value + (-value) ≈ 0 :=
  Q'.eqv_trans _ (-value + value) _
    (Q'.add_comm_eqv value (-value))
    (Q'.neg_add_self_eqv value)

private theorem pair_sub_eqv_sub_add_sub_local
    (a x b y : Q') :
    (a + x) - (b + y) ≈
      (a - b) + (x - y) := by
  change (a + x) + (-(b + y)) ≈
    (a + (-b)) + (x + (-y))
  refine Q'.eqv_trans _
    ((a + x) + ((-b) + (-y))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (a + x) _ _
      (Q'.neg_add_eqv b y)
  · exact Q'.add_swap_inner a x (-b) (-y)

private theorem add_sub_cancel_middle_local (x y z : Q') :
    (x - y) + (y - z) ≈ x - z := by
  change (x + (-y)) + (y + (-z)) ≈ x + (-z)
  refine Q'.eqv_trans _ (x + ((-y) + (y + (-z)))) _ ?_ ?_
  · exact Q'.add_assoc_eqv x (-y) (y + (-z))
  refine Q'.eqv_trans _ (x + (((-y) + y) + (-z))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left x _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-y) y (-z)))
  refine Q'.eqv_trans _ (x + (0 + (-z))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left x _ _
      (Q'.add_eqv_congr_right _ _ (-z)
        (Q'.neg_add_self_eqv y))
  · exact Q'.add_eqv_congr_left x _ _
      (Q'.eqv_of_eq (Q'.zero_add' (-z)))

private theorem four_point_telescope_local (a b c d : Q') :
    a - d ≈
      (b - c) + ((a - b) + (c - d)) := by
  have hfirst : (a - b) + (b - c) ≈ a - c :=
    add_sub_cancel_middle_local a b c
  have hsecond : (a - c) + (c - d) ≈ a - d :=
    add_sub_cancel_middle_local a c d
  have hchain :
      ((a - b) + (b - c)) + (c - d) ≈ a - d :=
    Q'.eqv_trans _ ((a - c) + (c - d)) _
      (Q'.add_eqv_congr_right _ _ (c - d) hfirst)
      hsecond
  refine Q'.eqv_trans _
    (((a - b) + (b - c)) + (c - d)) _
    (Q'.eqv_symm hchain) ?_
  refine Q'.eqv_trans _
    ((a - b) + ((b - c) + (c - d))) _
    (Q'.add_assoc_eqv (a - b) (b - c) (c - d)) ?_
  refine Q'.eqv_trans _
    ((a - b) + ((c - d) + (b - c))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (a - b) _ _
      (Q'.add_comm_eqv (b - c) (c - d))
  refine Q'.eqv_trans _
    (((a - b) + (c - d)) + (b - c)) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_assoc_eqv (a - b) (c - d) (b - c))
  · exact Q'.add_comm_eqv ((a - b) + (c - d)) (b - c)

private theorem add_balance_to_cross_sub_local
    (a b c d : Q') (h : a + b ≈ c + d) :
    d - b ≈ a - c := by
  have hadded :
      (a + b) + ((-b) + (-c)) ≈
        (c + d) + ((-b) + (-c)) :=
    Q'.add_eqv_congr_right _ _ ((-b) + (-c)) h
  have hleft :
      (a + b) + ((-b) + (-c)) ≈ a - c := by
    change (a + b) + ((-b) + (-c)) ≈ a + (-c)
    refine Q'.eqv_trans _
      (a + (b + ((-b) + (-c)))) _
      (Q'.add_assoc_eqv a b ((-b) + (-c))) ?_
    refine Q'.eqv_trans _
      (a + ((b + (-b)) + (-c))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left a _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv b (-b) (-c)))
    refine Q'.eqv_trans _ (a + (0 + (-c))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left a _ _
        (Q'.add_eqv_congr_right _ _ (-c)
          (add_neg_self_eqv_local b))
    · exact Q'.add_eqv_congr_left a _ _
        (Q'.eqv_of_eq (Q'.zero_add' (-c)))
  have hright :
      (c + d) + ((-b) + (-c)) ≈ d - b := by
    change (c + d) + ((-b) + (-c)) ≈ d + (-b)
    refine Q'.eqv_trans _
      (c + (d + ((-b) + (-c)))) _
      (Q'.add_assoc_eqv c d ((-b) + (-c))) ?_
    refine Q'.eqv_trans _
      (c + ((d + (-b)) + (-c))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left c _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv d (-b) (-c)))
    refine Q'.eqv_trans _
      ((c + (d + (-b))) + (-c)) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.add_assoc_eqv c (d + (-b)) (-c))
    refine Q'.eqv_trans _
      (((d + (-b)) + c) + (-c)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ (-c)
        (Q'.add_comm_eqv c (d + (-b)))
    refine Q'.eqv_trans _
      ((d + (-b)) + (c + (-c))) _
      (Q'.add_assoc_eqv (d + (-b)) c (-c)) ?_
    refine Q'.eqv_trans _ ((d + (-b)) + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (d + (-b)) _ _
        (add_neg_self_eqv_local c)
    · exact Q'.eqv_of_eq (Q'.add_zero' (d + (-b)))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hright)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hadded) hleft)

/-! ## 1. A generic division-free cocycle -/

/-- The geometric/power skew at two natural exponents. -/
def geomSumQpowSkew (w : Q') (left right : Nat) : Q' :=
  geomSum w left * qpow w right -
    qpow w left * geomSum w right

/-- The skew has the simpler universal normal form `geomSum(left) -
geomSum(right)`.  The proof is division-free: it compares the two additive
expansions of `geomSum(left+right)`. -/
theorem geomSumQpowSkew_eqv_geomSum_sub
    (w : Q') (left right : Nat) :
    geomSumQpowSkew w left right ≈
      geomSum w left - geomSum w right := by
  have hsum :
      geomSum w left + qpow w left * geomSum w right ≈
        geomSum w right + qpow w right * geomSum w left := by
    refine Q'.eqv_trans _ (geomSum w (left + right)) _ ?_ ?_
    · exact Q'.eqv_symm (geomSum_add_eqv w left right)
    · rw [Nat.add_comm left right]
      exact geomSum_add_eqv w right left
  unfold geomSumQpowSkew
  refine Q'.eqv_trans _
    (qpow w right * geomSum w left -
      qpow w left * geomSum w right) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_comm_eqv _ _) (Q'.eqv_refl _)
  · exact add_balance_to_cross_sub_local
      (geomSum w left)
      (qpow w left * geomSum w right)
      (geomSum w right)
      (qpow w right * geomSum w left)
      hsum

/-- Exchanging the two inside exponents changes the complete skew by an
outside heat multiplier times the inside skew. -/
theorem geomSumQpowSkew_componentSwap_cocycle
    (w : Q') (leftOutside leftInside rightOutside rightInside : Nat) :
    geomSumQpowSkew w
        (leftOutside + leftInside) (rightOutside + rightInside) ≈
      geomSumQpowSkew w
          (leftOutside + rightInside) (rightOutside + leftInside) +
        (qpow w leftOutside + qpow w rightOutside) *
          geomSumQpowSkew w leftInside rightInside := by
  have horiginal := geomSumQpowSkew_eqv_geomSum_sub w
    (leftOutside + leftInside) (rightOutside + rightInside)
  have hswappedSub := geomSumQpowSkew_eqv_geomSum_sub w
    (leftOutside + rightInside) (rightOutside + leftInside)
  have hinside := geomSumQpowSkew_eqv_geomSum_sub w
    leftInside rightInside
  let leftOutsideGeom := geomSum w leftOutside
  let rightOutsideGeom := geomSum w rightOutside
  let leftInsideGeom := geomSum w leftInside
  let rightInsideGeom := geomSum w rightInside
  let leftOutsidePower := qpow w leftOutside
  let rightOutsidePower := qpow w rightOutside
  let leftInsideTerm := leftOutsidePower * leftInsideGeom
  let rightInsideTerm := rightOutsidePower * rightInsideGeom
  let leftCrossTerm := leftOutsidePower * rightInsideGeom
  let rightCrossTerm := rightOutsidePower * leftInsideGeom
  refine Q'.eqv_trans _
    (geomSum w (leftOutside + leftInside) -
      geomSum w (rightOutside + rightInside)) _ horiginal ?_
  refine Q'.eqv_trans _
    ((leftOutsideGeom + leftInsideTerm) -
      (rightOutsideGeom + rightInsideTerm)) _ ?_ ?_
  · exact sub_eqv_both_local
      (geomSum_add_eqv w leftOutside leftInside)
      (geomSum_add_eqv w rightOutside rightInside)
  refine Q'.eqv_trans _
    ((leftOutsideGeom - rightOutsideGeom) +
      (leftInsideTerm - rightInsideTerm)) _ ?_ ?_
  · exact pair_sub_eqv_sub_add_sub_local
      leftOutsideGeom leftInsideTerm
      rightOutsideGeom rightInsideTerm
  refine Q'.eqv_trans _
    ((leftOutsideGeom - rightOutsideGeom) +
      ((leftCrossTerm - rightCrossTerm) +
        ((leftInsideTerm - leftCrossTerm) +
          (rightCrossTerm - rightInsideTerm)))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left
      (leftOutsideGeom - rightOutsideGeom) _ _
      (four_point_telescope_local
        leftInsideTerm leftCrossTerm rightCrossTerm rightInsideTerm)
  refine Q'.eqv_trans _
    (((leftOutsideGeom - rightOutsideGeom) +
        (leftCrossTerm - rightCrossTerm)) +
      ((leftInsideTerm - leftCrossTerm) +
        (rightCrossTerm - rightInsideTerm))) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_assoc_eqv
        (leftOutsideGeom - rightOutsideGeom)
        (leftCrossTerm - rightCrossTerm)
        ((leftInsideTerm - leftCrossTerm) +
          (rightCrossTerm - rightInsideTerm)))
  refine Q'.eqv_trans _
    (((leftOutsideGeom + leftCrossTerm) -
        (rightOutsideGeom + rightCrossTerm)) +
      ((leftOutsidePower + rightOutsidePower) *
        (leftInsideGeom - rightInsideGeom))) _ ?_ ?_
  · apply Q'.add_eqv_congr'
    · exact Q'.eqv_symm
        (pair_sub_eqv_sub_add_sub_local
          leftOutsideGeom leftCrossTerm
          rightOutsideGeom rightCrossTerm)
    · exact Q'.eqv_symm
        (add_mul_sub_expand_local
          leftOutsidePower rightOutsidePower
          leftInsideGeom rightInsideGeom)
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_symm
      (Q'.eqv_trans _
        (geomSum w (leftOutside + rightInside) -
          geomSum w (rightOutside + leftInside)) _
        hswappedSub
        (sub_eqv_both_local
          (geomSum_add_eqv w leftOutside rightInside)
          (geomSum_add_eqv w rightOutside leftInside)))
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm hinside)

/-! ## 2. Canonical paired-support specialization -/

/-- Occupation of one source outside the canonical target-rooted support
component. -/
def fineCouplingPhysicalOutsideOccupiedFaceCount
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (source : EdgeLabelling) : Nat :=
  slabCutoffOneMaskedOccupiedCount
    (fun faceId =>
      !(fineCouplingPhysicalSupportSwapMask
        S targetFaceId pair faceId))
    source (slabPhysicalFaceEdges S.fine.extent)

/-- The skew carried only by occupations inside the canonical support
component. -/
def fineCouplingPhysicalComponentOccupationSkewCoefficient
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) : Q' :=
  geomSumQpowSkew S.fine.coupling
    (3 * fineCouplingPhysicalComponentOccupiedFaceCount
      S targetFaceId pair pair.1)
    (3 * fineCouplingPhysicalComponentOccupiedFaceCount
      S targetFaceId pair pair.2)

/-- The complete left occupation splits into component and outside pieces. -/
theorem fineCouplingPhysicalOccupiedFaceCount_eq_component_add_outside_left
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    fineCouplingPhysicalOccupiedFaceCount S pair.1 =
      fineCouplingPhysicalComponentOccupiedFaceCount
          S targetFaceId pair pair.1 +
        fineCouplingPhysicalOutsideOccupiedFaceCount
          S targetFaceId pair pair.1 := by
  unfold fineCouplingPhysicalOccupiedFaceCount
    fineCouplingPhysicalComponentOccupiedFaceCount
    fineCouplingPhysicalOutsideOccupiedFaceCount
  exact slabCutoffOneOccupiedCount_eq_masked_add_complement
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    pair.1 (slabPhysicalFaceEdges S.fine.extent)

/-- The complete right occupation splits into component and outside pieces. -/
theorem fineCouplingPhysicalOccupiedFaceCount_eq_component_add_outside_right
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    fineCouplingPhysicalOccupiedFaceCount S pair.2 =
      fineCouplingPhysicalComponentOccupiedFaceCount
          S targetFaceId pair pair.2 +
        fineCouplingPhysicalOutsideOccupiedFaceCount
          S targetFaceId pair pair.2 := by
  unfold fineCouplingPhysicalOccupiedFaceCount
    fineCouplingPhysicalComponentOccupiedFaceCount
    fineCouplingPhysicalOutsideOccupiedFaceCount
  exact slabCutoffOneOccupiedCount_eq_masked_add_complement
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    pair.2 (slabPhysicalFaceEdges S.fine.extent)

/-- The full occupation skew before the support swap is the skew after the
swap plus one exact component term.  This is the division-free telescoping
law exposed by the support-component involution. -/
theorem fineCouplingPhysicalOccupationSkewCoefficient_componentSwap_cocycle
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    fineCouplingPhysicalOccupationSkewCoefficient S pair ≈
      fineCouplingPhysicalOccupationSkewCoefficient S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair) +
        (qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.1) +
          qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.2)) *
          fineCouplingPhysicalComponentOccupationSkewCoefficient
            S targetFaceId pair := by
  let leftComponent := fineCouplingPhysicalComponentOccupiedFaceCount
    S targetFaceId pair pair.1
  let rightComponent := fineCouplingPhysicalComponentOccupiedFaceCount
    S targetFaceId pair pair.2
  let leftOutside := fineCouplingPhysicalOutsideOccupiedFaceCount
    S targetFaceId pair pair.1
  let rightOutside := fineCouplingPhysicalOutsideOccupiedFaceCount
    S targetFaceId pair pair.2
  have hleft :=
    fineCouplingPhysicalOccupiedFaceCount_eq_component_add_outside_left
      S targetFaceId pair
  have hright :=
    fineCouplingPhysicalOccupiedFaceCount_eq_component_add_outside_right
      S targetFaceId pair
  have hswappedLeft :=
    fineCouplingPhysicalSupportSwappedPair_left_count
      S targetFaceId pair
  have hswappedRight :=
    fineCouplingPhysicalSupportSwappedPair_right_count
      S targetFaceId pair
  have hleftExponent :
      3 * fineCouplingPhysicalOccupiedFaceCount S pair.1 =
        3 * leftOutside + 3 * leftComponent := by
    dsimp only [leftOutside, leftComponent]
    omega
  have hrightExponent :
      3 * fineCouplingPhysicalOccupiedFaceCount S pair.2 =
        3 * rightOutside + 3 * rightComponent := by
    dsimp only [rightOutside, rightComponent]
    omega
  have hswappedLeftExponent :
      3 * fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).1 =
        3 * leftOutside + 3 * rightComponent := by
    dsimp only [leftOutside, rightComponent]
    unfold fineCouplingPhysicalOutsideOccupiedFaceCount
    omega
  have hswappedRightExponent :
      3 * fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).2 =
        3 * rightOutside + 3 * leftComponent := by
    dsimp only [rightOutside, leftComponent]
    unfold fineCouplingPhysicalOutsideOccupiedFaceCount
    omega
  unfold fineCouplingPhysicalOccupationSkewCoefficient
    fineCouplingPhysicalComponentOccupationSkewCoefficient
  dsimp only
  rw [hleftExponent, hrightExponent,
    hswappedLeftExponent, hswappedRightExponent]
  exact geomSumQpowSkew_componentSwap_cocycle
    S.fine.coupling
    (3 * leftOutside) (3 * leftComponent)
    (3 * rightOutside) (3 * rightComponent)

#print axioms geomSumQpowSkew
#print axioms geomSumQpowSkew_eqv_geomSum_sub
#print axioms geomSumQpowSkew_componentSwap_cocycle
#print axioms fineCouplingPhysicalOutsideOccupiedFaceCount
#print axioms fineCouplingPhysicalComponentOccupationSkewCoefficient
#print axioms fineCouplingPhysicalOccupiedFaceCount_eq_component_add_outside_left
#print axioms fineCouplingPhysicalOccupiedFaceCount_eq_component_add_outside_right
#print axioms fineCouplingPhysicalOccupationSkewCoefficient_componentSwap_cocycle

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle
