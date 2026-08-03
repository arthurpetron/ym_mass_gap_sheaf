/-
# Exact block-reflection invariance of arbitrary quaternion product Haar

The corrected BF4 slab numbers every link by one quaternion block.  Euclidean
time reflection permutes those blocks and inverts the positive time-link
variables.  Before applying that geometry, this module proves the exact
algebraic change-of-variables theorem for the repository's rational moment
functional:

* an explicit involution of the quaternion blocks preserves every monomial
  Haar moment;
* changing the signs of any selected real quaternion coordinates preserves
  the Haar moment after the matching coefficient sign is included; and
* both operations lift termwise to arbitrary finite rational polynomials.

Nothing is imported from a pre-existing measure.  The proof unfolds the
normalized `S^3` monomial formula, reindexes its finite block product, and
uses the defining odd-moment cancellation for the sign part.

## Axiom gate

Finite lists and exact rational moments only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A head-first enumeration of quaternion blocks -/

/-- The block order compatible with the recursive definition of
`quaternionHaarPrefix`: zero first, followed by the recursively shifted
remaining blocks. -/
def quaternionBlockOrder : Nat → List Nat
  | 0 => []
  | blocks + 1 => 0 :: (quaternionBlockOrder blocks).map Nat.succ

theorem mem_quaternionBlockOrder_iff (block blocks : Nat) :
    block ∈ quaternionBlockOrder blocks ↔ block < blocks := by
  induction blocks generalizing block with
  | zero => simp [quaternionBlockOrder]
  | succ blocks induction =>
      cases block with
      | zero => simp [quaternionBlockOrder]
      | succ block =>
          simp [quaternionBlockOrder, induction]

theorem quaternionBlockOrder_nodup (blocks : Nat) :
    (quaternionBlockOrder blocks).Nodup := by
  induction blocks with
  | zero => exact List.nodup_nil
  | succ blocks induction =>
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨source, _, hsource⟩ := List.mem_map.mp hmem
        omega
      · exact
          YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
            Nat.succ (quaternionBlockOrder blocks) induction
            (fun left _ right _ heq => Nat.succ.inj heq)

/-! ## 2. Block moments and the prefix product -/

/-- The `S^3` moment attached to one numbered quaternion block. -/
def quaternionBlockMoment
    (monomial : List Nat) (block : Nat) : Q' :=
  sphereMoment4
    (exponentAt monomial (4 * block))
    (exponentAt monomial (4 * block + 1))
    (exponentAt monomial (4 * block + 2))
    (exponentAt monomial (4 * block + 3))

theorem exponentAt_drop
    (monomial : List Nat) :
    ∀ (offset index : Nat),
      exponentAt (monomial.drop offset) index =
        exponentAt monomial (offset + index)
  | 0, index => by simp [exponentAt]
  | offset + 1, index => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons exponent rest =>
          have hindex :
              offset + 1 + index = (offset + index) + 1 := by
            omega
          rw [hindex]
          simp only [List.drop_succ_cons]
          unfold exponentAt
          simp only [List.getD_cons_succ]
          exact exponentAt_drop rest offset index

private theorem quaternionBlockMoment_drop_four
    (monomial : List Nat) (block : Nat) :
    quaternionBlockMoment (monomial.drop 4) block =
      quaternionBlockMoment monomial (block + 1) := by
  unfold quaternionBlockMoment
  rw [exponentAt_drop monomial 4,
    exponentAt_drop monomial 4,
    exponentAt_drop monomial 4,
    exponentAt_drop monomial 4]
  have h0 : 4 + 4 * block = 4 * (block + 1) := by omega
  have h1 : 4 + (4 * block + 1) = 4 * (block + 1) + 1 := by omega
  have h2 : 4 + (4 * block + 2) = 4 * (block + 1) + 2 := by omega
  have h3 : 4 + (4 * block + 3) = 4 * (block + 1) + 3 := by omega
  rw [h0, h1, h2, h3]

/-- The recursive Haar prefix is exactly the commutative finite product of
its numbered block moments. -/
theorem quaternionHaarPrefix_eq_block_product
    (blocks : Nat) (monomial : List Nat) :
    quaternionHaarPrefix blocks monomial ≈
      listQProduct
        (quaternionBlockMoment monomial)
        (quaternionBlockOrder blocks) := by
  induction blocks generalizing monomial with
  | zero => exact Q'.eqv_refl 1
  | succ blocks induction =>
      change
        quaternionBlockMoment monomial 0 *
            quaternionHaarPrefix blocks (monomial.drop 4) ≈
          quaternionBlockMoment monomial 0 *
            listQProduct
              (quaternionBlockMoment monomial)
              ((quaternionBlockOrder blocks).map Nat.succ)
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _
        (listQProduct
          (quaternionBlockMoment (monomial.drop 4))
          (quaternionBlockOrder blocks)) _
        (induction (monomial.drop 4)) ?_
      rw [listQProduct_map]
      exact listQProduct_congr_eqv _ _ _
        (fun block _ =>
          Q'.eqv_of_eq
            (quaternionBlockMoment_drop_four monomial block))

/-! ## 3. Explicit involutive block permutations -/

/-- Constructive data for an involution of the first `blocks` quaternion
blocks.  The image bound and involution are data later instantiated by the
literal reflected slab link list. -/
structure QuaternionBlockInvolution
    (blocks : Nat) : Type where
  map : Nat → Nat
  map_lt : ∀ block, block < blocks → map block < blocks
  involutive : ∀ block, block < blocks → map (map block) = block

namespace QuaternionBlockInvolution

theorem injective_on
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    {left right : Nat}
    (hleft : left < blocks) (hright : right < blocks)
    (heq : permutation.map left = permutation.map right) :
    left = right := by
  have h := congrArg permutation.map heq
  rw [permutation.involutive left hleft,
    permutation.involutive right hright] at h
  exact h

theorem order_map_perm
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    ((quaternionBlockOrder blocks).map permutation.map).Perm
      (quaternionBlockOrder blocks) := by
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
      permutation.map
      (quaternionBlockOrder blocks)
      (quaternionBlockOrder_nodup blocks)
    intro left hleft right hright
    exact permutation.injective_on
      ((mem_quaternionBlockOrder_iff left blocks).mp hleft)
      ((mem_quaternionBlockOrder_iff right blocks).mp hright)
  · exact quaternionBlockOrder_nodup blocks
  · intro block
    constructor
    · intro hmem
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hmem
      rw [← hsourceEq]
      exact (mem_quaternionBlockOrder_iff _ _).mpr
        (permutation.map_lt source
          ((mem_quaternionBlockOrder_iff _ _).mp hsource))
    · intro hmem
      have hblock := (mem_quaternionBlockOrder_iff _ _).mp hmem
      let source := permutation.map block
      have hsource : source < blocks :=
        permutation.map_lt block hblock
      apply List.mem_map.mpr
      refine ⟨source,
        (mem_quaternionBlockOrder_iff _ _).mpr hsource, ?_⟩
      exact permutation.involutive block hblock

end QuaternionBlockInvolution

/-- Reindex an exponent vector by a quaternion-block involution, leaving the
four real coordinates inside every block in their original order. -/
def reindexQuaternionExponents
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (monomial : List Nat) : List Nat :=
  List.ofFn (fun coordinate : Fin (4 * blocks) =>
    let block := coordinate.val / 4
    let component := coordinate.val % 4
    exponentAt monomial
      (4 * permutation.map block + component))

theorem reindexQuaternionExponents_length
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (monomial : List Nat) :
    (reindexQuaternionExponents permutation monomial).length =
      4 * blocks := by
  exact List.length_ofFn

theorem exponentAt_reindexQuaternionExponents
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (monomial : List Nat) {coordinate : Nat}
    (hcoordinate : coordinate < 4 * blocks) :
    exponentAt
        (reindexQuaternionExponents permutation monomial)
        coordinate =
      exponentAt monomial
        (4 * permutation.map (coordinate / 4) + coordinate % 4) := by
  unfold exponentAt
  rw [← List.getElem_eq_getD
    (l := reindexQuaternionExponents permutation monomial)
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

theorem quaternionBlockMoment_reindex
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (monomial : List Nat) {block : Nat}
    (hblock : block < blocks) :
    quaternionBlockMoment
        (reindexQuaternionExponents permutation monomial) block =
      quaternionBlockMoment monomial (permutation.map block) := by
  unfold quaternionBlockMoment
  rw [exponentAt_reindexQuaternionExponents permutation monomial
        (by omega),
    exponentAt_reindexQuaternionExponents permutation monomial
        (by omega),
    exponentAt_reindexQuaternionExponents permutation monomial
        (by omega),
    exponentAt_reindexQuaternionExponents permutation monomial
        (by omega)]
  have hd0 : (4 * block) / 4 = block := by omega
  have hm0 : (4 * block) % 4 = 0 := by omega
  have hd1 : (4 * block + 1) / 4 = block := by omega
  have hm1 : (4 * block + 1) % 4 = 1 := by omega
  have hd2 : (4 * block + 2) / 4 = block := by omega
  have hm2 : (4 * block + 2) % 4 = 2 := by omega
  have hd3 : (4 * block + 3) / 4 = block := by omega
  have hm3 : (4 * block + 3) % 4 = 3 := by omega
  rw [hd0, hm0, hd1, hm1, hd2, hm2, hd3, hm3]
  simp only [Nat.add_zero]

private theorem allZero_drop_of_length_le
    (values : List Nat) (coordinates : Nat)
    (hvalues : values.length ≤ coordinates) :
    allZero (values.drop coordinates) = true := by
  rw [List.drop_eq_nil_of_le hvalues]
  rfl

/-- Exact monomial Haar invariance under an explicit involution of all
quaternion blocks. -/
theorem quaternionHaarMono_reindex
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (monomial : List Nat)
    (hsupport : monomial.length ≤ 4 * blocks) :
    quaternionHaarMono blocks
        (reindexQuaternionExponents permutation monomial) ≈
      quaternionHaarMono blocks monomial := by
  unfold quaternionHaarMono
  have hreindexedTail :
      allZero
          ((reindexQuaternionExponents permutation monomial).drop
            (4 * blocks)) = true :=
    allZero_drop_of_length_le _ _
      (Nat.le_of_eq
        (reindexQuaternionExponents_length permutation monomial))
  have hsourceTail :
      allZero (monomial.drop (4 * blocks)) = true :=
    allZero_drop_of_length_le _ _ hsupport
  rw [if_pos hreindexedTail, if_pos hsourceTail]
  refine Q'.eqv_trans _
    (listQProduct
      (quaternionBlockMoment
        (reindexQuaternionExponents permutation monomial))
      (quaternionBlockOrder blocks)) _
    (quaternionHaarPrefix_eq_block_product _ _) ?_
  refine Q'.eqv_trans _
    (listQProduct
      (quaternionBlockMoment monomial)
      ((quaternionBlockOrder blocks).map permutation.map)) _ ?_ ?_
  · rw [listQProduct_map]
    exact listQProduct_congr_eqv _ _ _
      (fun block hblock =>
        Q'.eqv_of_eq
          (quaternionBlockMoment_reindex
            permutation monomial
            ((mem_quaternionBlockOrder_iff _ _).mp hblock)))
  · exact Q'.eqv_trans _ _ _
      (listQProduct_perm
        (quaternionBlockMoment monomial)
        permutation.order_map_perm)
      (Q'.eqv_symm
        (quaternionHaarPrefix_eq_block_product
          blocks monomial))

/-- Termwise polynomial reindexing by a quaternion-block involution. -/
def reindexQuaternionPolynomial
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    RatPoly → RatPoly :=
  List.map (fun term =>
    (reindexQuaternionExponents permutation term.1, term.2))

theorem exponentAt_monoMul
    (left right : List Nat) (coordinate : Nat) :
    exponentAt (monoMul left right) coordinate =
      exponentAt left coordinate + exponentAt right coordinate := by
  induction left generalizing right coordinate with
  | nil => simp [monoMul, exponentAt]
  | cons head tail induction =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons other rest =>
          cases coordinate with
          | zero => simp [monoMul, exponentAt]
          | succ coordinate =>
              change exponentAt (monoMul tail rest) coordinate =
                exponentAt tail coordinate + exponentAt rest coordinate
              exact induction rest coordinate

theorem monoMul_length_of_equal
    : ∀ {left right : List Nat},
      left.length = right.length →
      (monoMul left right).length = left.length
  | [], right, hlength => by
      change right.length = 0
      exact hlength.symm
  | _ :: _, [], hlength => by
      exact False.elim (Nat.noConfusion hlength)
  | _ :: left, _ :: right, hlength => by
      change Nat.succ (monoMul left right).length =
        Nat.succ left.length
      exact congrArg Nat.succ
        (monoMul_length_of_equal (Nat.succ.inj hlength))

/-- Constructive list extensionality through `getD`; unlike `List.ext_getElem`
this proof does not introduce a choice dependency. -/
theorem natList_eq_of_length_getD
    {left right : List Nat}
    (hlength : left.length = right.length)
    (hget : ∀ coordinate, coordinate < left.length →
      left.getD coordinate 0 = right.getD coordinate 0) :
    left = right := by
  apply List.ext_getElem?
  intro coordinate
  by_cases hcoordinate : coordinate < left.length
  · have hright : coordinate < right.length := by
      rw [← hlength]
      exact hcoordinate
    rw [List.getElem?_eq_getElem hcoordinate,
      List.getElem?_eq_getElem hright]
    congr 1
    rw [List.getElem_eq_getD
        (l := left) (i := coordinate) (h := hcoordinate) 0,
      List.getElem_eq_getD
        (l := right) (i := coordinate) (h := hright) 0]
    exact hget coordinate hcoordinate
  · have hleftLe : left.length ≤ coordinate := Nat.le_of_not_gt hcoordinate
    have hrightLe : right.length ≤ coordinate := by
      rw [← hlength]
      exact hleftLe
    rw [List.getElem?_eq_none hleftLe,
      List.getElem?_eq_none hrightLe]

/-- Block reindexing is multiplicative on exponent vectors.  Both sides use
the same fixed `4 * blocks` padding, so this is literal list equality. -/
theorem reindexQuaternionExponents_monoMul
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (left right : List Nat) :
    reindexQuaternionExponents permutation (monoMul left right) =
      monoMul
        (reindexQuaternionExponents permutation left)
        (reindexQuaternionExponents permutation right) := by
  apply natList_eq_of_length_getD
  · rw [reindexQuaternionExponents_length]
    have hlength :
        (reindexQuaternionExponents permutation left).length =
          (reindexQuaternionExponents permutation right).length := by
      rw [reindexQuaternionExponents_length,
        reindexQuaternionExponents_length]
    rw [monoMul_length_of_equal hlength,
      reindexQuaternionExponents_length]
  · intro coordinate hleft
    change
      exponentAt
          (reindexQuaternionExponents permutation (monoMul left right))
          coordinate =
        exponentAt
          (monoMul
            (reindexQuaternionExponents permutation left)
            (reindexQuaternionExponents permutation right))
          coordinate
    have hcoordinate : coordinate < 4 * blocks := by
      rw [reindexQuaternionExponents_length] at hleft
      exact hleft
    rw [exponentAt_reindexQuaternionExponents
        permutation (monoMul left right) hcoordinate,
      exponentAt_monoMul,
      exponentAt_monoMul,
      exponentAt_reindexQuaternionExponents
        permutation left hcoordinate,
      exponentAt_reindexQuaternionExponents
        permutation right hcoordinate]

theorem reindexQuaternionPolynomial_add
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (left right : RatPoly) :
    reindexQuaternionPolynomial permutation (polyAdd left right) =
      polyAdd
        (reindexQuaternionPolynomial permutation left)
        (reindexQuaternionPolynomial permutation right) := by
  exact List.map_append

private theorem reindexQuaternionPolynomial_mul_single
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (term : RatTerm) (right : RatPoly) :
    reindexQuaternionPolynomial permutation (polyMul [term] right) =
      polyMul
        (reindexQuaternionPolynomial permutation [term])
        (reindexQuaternionPolynomial permutation right) := by
  simp only [polyMul, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, reindexQuaternionPolynomial, List.map_map,
    List.map_cons, List.map_nil]
  apply congrArg (fun f : RatTerm → RatTerm => right.map f)
  funext target
  simp only [Function.comp_apply]
  rcases term with ⟨termMono, termCoeff⟩
  rcases target with ⟨targetMono, targetCoeff⟩
  change
    (reindexQuaternionExponents permutation
        (monoMul termMono targetMono),
      termCoeff * targetCoeff) =
    (monoMul
        (reindexQuaternionExponents permutation termMono)
        (reindexQuaternionExponents permutation targetMono),
      termCoeff * targetCoeff)
  rw [reindexQuaternionExponents_monoMul]

/-- The block change of variables commutes literally with polynomial
multiplication. -/
theorem reindexQuaternionPolynomial_mul
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    ∀ left right : RatPoly,
      reindexQuaternionPolynomial permutation (polyMul left right) =
        polyMul
          (reindexQuaternionPolynomial permutation left)
          (reindexQuaternionPolynomial permutation right)
  | [], right => rfl
  | term :: rest, right => by
      have hsource :
          polyMul (term :: rest) right =
            polyAdd (polyMul [term] right) (polyMul rest right) := by
        simp [polyMul, polyAdd]
      have htarget :
          polyMul
              (reindexQuaternionPolynomial permutation (term :: rest))
              (reindexQuaternionPolynomial permutation right) =
            polyAdd
              (polyMul
                (reindexQuaternionPolynomial permutation [term])
                (reindexQuaternionPolynomial permutation right))
              (polyMul
                (reindexQuaternionPolynomial permutation rest)
                (reindexQuaternionPolynomial permutation right)) := by
        simp [polyMul, polyAdd, reindexQuaternionPolynomial]
      rw [hsource, htarget,
        reindexQuaternionPolynomial_add,
        reindexQuaternionPolynomial_mul_single,
        reindexQuaternionPolynomial_mul permutation rest right]

theorem reindexQuaternionPolynomial_smul
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (scale : Q') (polynomial : RatPoly) :
    reindexQuaternionPolynomial permutation
        (polySmul scale polynomial) =
      polySmul scale
        (reindexQuaternionPolynomial permutation polynomial) := by
  unfold reindexQuaternionPolynomial polySmul
  rw [List.map_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatTerm => polynomial.map f)
  funext term
  rfl

theorem reindexQuaternionPolynomial_neg
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (polynomial : RatPoly) :
    reindexQuaternionPolynomial permutation
        (polyNeg polynomial) =
      polyNeg
        (reindexQuaternionPolynomial permutation polynomial) := by
  unfold reindexQuaternionPolynomial polyNeg
  rw [List.map_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatTerm => polynomial.map f)
  funext term
  rfl

/-- Exact polynomial Haar invariance under block reindexing. -/
theorem quaternionHaar_reindex
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    ∀ polynomial : RatPoly,
      SupportedQuaternionBlocks blocks polynomial →
      quaternionHaar blocks
          (reindexQuaternionPolynomial permutation polynomial) ≈
        quaternionHaar blocks polynomial
  | [], _ => Q'.eqv_refl 0
  | term :: rest, hsupport => by
      unfold reindexQuaternionPolynomial List.map
      change
        term.2 * quaternionHaarMono blocks
              (reindexQuaternionExponents permutation term.1) +
            quaternionHaar blocks
              (reindexQuaternionPolynomial permutation rest) ≈
          term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks rest
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left term.2 _ _
          (quaternionHaarMono_reindex permutation term.1
            (hsupport term (by simp))))
        (quaternionHaar_reindex permutation rest
          (fun other hother =>
            hsupport other (by simp [hother])))

/-! ## 4. Prefix equivalence and harmless zero padding -/

/-- Two polynomial terms agree on the declared quaternion prefix.  Their
exponent lists may have different amounts of trailing zero padding. -/
structure QuaternionPrefixTermEqv
    (blocks : Nat) (left right : RatTerm) : Prop where
  coefficient : left.2 ≈ right.2
  exponent : ∀ coordinate, coordinate < 4 * blocks →
    exponentAt left.1 coordinate = exponentAt right.1 coordinate

/-- Term-order-preserving prefix equivalence of finite polynomials.  This is
the exact relation needed because block reindexing pads even the constant
monomial to `4 * blocks` coordinates. -/
inductive QuaternionPrefixPolynomialEqv
    (blocks : Nat) : RatPoly → RatPoly → Prop
  | nil : QuaternionPrefixPolynomialEqv blocks [] []
  | cons {leftTerm rightTerm : RatTerm} {leftRest rightRest : RatPoly} :
      QuaternionPrefixTermEqv blocks leftTerm rightTerm →
      QuaternionPrefixPolynomialEqv blocks leftRest rightRest →
      QuaternionPrefixPolynomialEqv blocks
        (leftTerm :: leftRest) (rightTerm :: rightRest)

namespace QuaternionPrefixPolynomialEqv

theorem refl (blocks : Nat) : ∀ polynomial : RatPoly,
    QuaternionPrefixPolynomialEqv blocks polynomial polynomial
  | [] => .nil
  | term :: rest =>
      .cons
        ⟨Q'.eqv_refl _, fun _ _ => rfl⟩
        (refl blocks rest)

theorem append {blocks : Nat}
    {left left' right right' : RatPoly}
    (hleft : QuaternionPrefixPolynomialEqv blocks left left')
    (hright : QuaternionPrefixPolynomialEqv blocks right right') :
    QuaternionPrefixPolynomialEqv blocks
      (left ++ right) (left' ++ right') := by
  induction hleft with
  | nil => exact hright
  | cons hterm hrest induction =>
      exact .cons hterm induction

theorem trans {blocks : Nat} {left middle right : RatPoly}
    (hleft : QuaternionPrefixPolynomialEqv blocks left middle)
    (hright : QuaternionPrefixPolynomialEqv blocks middle right) :
    QuaternionPrefixPolynomialEqv blocks left right := by
  induction hleft generalizing right with
  | nil =>
      cases hright
      exact .nil
  | cons hterm hrest induction =>
      cases hright with
      | cons hterm' hrest' =>
          apply QuaternionPrefixPolynomialEqv.cons
          · exact
              ⟨Q'.eqv_trans _ _ _
                  hterm.coefficient hterm'.coefficient,
                fun coordinate hcoordinate =>
                  (hterm.exponent coordinate hcoordinate).trans
                    (hterm'.exponent coordinate hcoordinate)⟩
          · exact induction hrest'

theorem neg {blocks : Nat} {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks
      (polyNeg left) (polyNeg right) := by
  induction heqv with
  | nil => exact .nil
  | cons hterm hrest induction =>
      exact .cons
        ⟨Q'.neg_eqv_congr _ _ hterm.coefficient,
          hterm.exponent⟩
        induction

theorem smul {blocks : Nat} (scale : Q')
    {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks
      (polySmul scale left) (polySmul scale right) := by
  induction heqv with
  | nil => exact .nil
  | cons hterm hrest induction =>
      exact .cons
        ⟨Q'.mul_eqv_congr_left scale _ _ hterm.coefficient,
          hterm.exponent⟩
        induction

private theorem term_mul
    {blocks : Nat} {left left' right right' : RatTerm}
    (hleft : QuaternionPrefixTermEqv blocks left left')
    (hright : QuaternionPrefixTermEqv blocks right right') :
    QuaternionPrefixTermEqv blocks
      (monoMul left.1 right.1, left.2 * right.2)
      (monoMul left'.1 right'.1, left'.2 * right'.2) := by
  constructor
  · exact Q'.eqv_trans _ (left'.2 * right.2) _
      (Q'.mul_eqv_congr_right _ _ _ hleft.coefficient)
      (Q'.mul_eqv_congr_left _ _ _ hright.coefficient)
  · intro coordinate hcoordinate
    rw [exponentAt_monoMul, exponentAt_monoMul,
      hleft.exponent coordinate hcoordinate,
      hright.exponent coordinate hcoordinate]

private theorem mulRow
    {blocks : Nat} {source source' : RatTerm}
    (hsource : QuaternionPrefixTermEqv blocks source source')
    {left right : RatPoly}
    (htargets : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks
      (left.map fun target =>
        (monoMul source.1 target.1, source.2 * target.2))
      (right.map fun target =>
        (monoMul source'.1 target.1, source'.2 * target.2)) := by
  induction htargets with
  | nil => exact .nil
  | cons hterm hrest induction =>
      exact .cons (term_mul hsource hterm) induction

theorem mul {blocks : Nat} {left left' right right' : RatPoly}
    (hleft : QuaternionPrefixPolynomialEqv blocks left left')
    (hright : QuaternionPrefixPolynomialEqv blocks right right') :
    QuaternionPrefixPolynomialEqv blocks
      (polyMul left right) (polyMul left' right') := by
  induction hleft with
  | nil => exact .nil
  | cons hterm hrest induction =>
      exact append (mulRow hterm hright) induction

/-- The all-spin Chebyshev recursion respects prefix equivalence. -/
theorem character {blocks : Nat} {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    ∀ spin,
      QuaternionPrefixPolynomialEqv blocks
        (characterPolynomial left spin)
        (characterPolynomial right spin)
  | 0 => refl blocks polyOne
  | 1 => smul 2 heqv
  | spin + 2 =>
      append
        (mul (smul 2 heqv) (character heqv (spin + 1)))
        (smul (-1) (character heqv spin))

end QuaternionPrefixPolynomialEqv

private theorem reindexQuaternionPolynomial_one_prefix
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial permutation polyOne) polyOne := by
  change QuaternionPrefixPolynomialEqv blocks
    [(reindexQuaternionExponents permutation [], 1)] [([], 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents
        permutation [] hcoordinate]
      simp [exponentAt]
  · exact .nil

/-- Block reindexing commutes with every all-spin character modulo only
harmless trailing-zero padding of its constant monomials. -/
theorem reindexQuaternionPolynomial_character_prefix
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (scalar : RatPoly) : ∀ spin,
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial permutation
        (characterPolynomial scalar spin))
      (characterPolynomial
        (reindexQuaternionPolynomial permutation scalar) spin)
  | 0 => reindexQuaternionPolynomial_one_prefix permutation
  | 1 => by
      change QuaternionPrefixPolynomialEqv blocks
        (reindexQuaternionPolynomial permutation
          (polySmul 2 scalar))
        (polySmul 2
          (reindexQuaternionPolynomial permutation scalar))
      rw [reindexQuaternionPolynomial_smul]
      exact QuaternionPrefixPolynomialEqv.refl _ _
  | spin + 2 => by
      change QuaternionPrefixPolynomialEqv blocks
        (reindexQuaternionPolynomial permutation
          (polyAdd
            (polyMul (polySmul 2 scalar)
              (characterPolynomial scalar (spin + 1)))
            (polySmul (-1)
              (characterPolynomial scalar spin))))
        (polyAdd
          (polyMul
            (polySmul 2
              (reindexQuaternionPolynomial permutation scalar))
            (characterPolynomial
              (reindexQuaternionPolynomial permutation scalar)
              (spin + 1)))
          (polySmul (-1)
            (characterPolynomial
              (reindexQuaternionPolynomial permutation scalar) spin)))
      rw [reindexQuaternionPolynomial_add,
        reindexQuaternionPolynomial_mul,
        reindexQuaternionPolynomial_smul,
        reindexQuaternionPolynomial_smul]
      exact QuaternionPrefixPolynomialEqv.append
        (QuaternionPrefixPolynomialEqv.mul
          (QuaternionPrefixPolynomialEqv.refl _ _)
          (reindexQuaternionPolynomial_character_prefix
            permutation scalar (spin + 1)))
        (QuaternionPrefixPolynomialEqv.smul (-1)
          (reindexQuaternionPolynomial_character_prefix
            permutation scalar spin))

private theorem quaternionBlockMoment_prefix_congr
    {blocks : Nat} {left right : RatTerm}
    (heqv : QuaternionPrefixTermEqv blocks left right)
    {block : Nat} (hblock : block < blocks) :
    quaternionBlockMoment left.1 block =
      quaternionBlockMoment right.1 block := by
  unfold quaternionBlockMoment
  rw [heqv.exponent (4 * block) (by omega),
    heqv.exponent (4 * block + 1) (by omega),
    heqv.exponent (4 * block + 2) (by omega),
    heqv.exponent (4 * block + 3) (by omega)]

private theorem quaternionHaarPrefix_prefix_congr
    {blocks : Nat} {left right : RatTerm}
    (heqv : QuaternionPrefixTermEqv blocks left right) :
    quaternionHaarPrefix blocks left.1 ≈
      quaternionHaarPrefix blocks right.1 := by
  refine Q'.eqv_trans _
    (listQProduct
      (quaternionBlockMoment left.1)
      (quaternionBlockOrder blocks)) _
    (quaternionHaarPrefix_eq_block_product blocks left.1) ?_
  refine Q'.eqv_trans _
    (listQProduct
      (quaternionBlockMoment right.1)
      (quaternionBlockOrder blocks)) _ ?_ ?_
  · exact listQProduct_congr_eqv _ _ _
      (fun block hblock => Q'.eqv_of_eq
        (quaternionBlockMoment_prefix_congr heqv
          ((mem_quaternionBlockOrder_iff block blocks).mp hblock)))
  · exact Q'.eqv_symm
      (quaternionHaarPrefix_eq_block_product blocks right.1)

private theorem quaternionHaarMono_prefix_congr
    {blocks : Nat} {left right : RatTerm}
    (heqv : QuaternionPrefixTermEqv blocks left right)
    (hleft : left.1.length ≤ 4 * blocks)
    (hright : right.1.length ≤ 4 * blocks) :
    quaternionHaarMono blocks left.1 ≈
      quaternionHaarMono blocks right.1 := by
  unfold quaternionHaarMono
  rw [if_pos (allZero_drop_of_length_le left.1 (4 * blocks) hleft),
    if_pos (allZero_drop_of_length_le right.1 (4 * blocks) hright)]
  exact quaternionHaarPrefix_prefix_congr heqv

/-- Prefix-equivalent supported polynomials have exactly the same normalized
product-Haar integral.  In particular all trailing-zero padding introduced
by a block permutation is analytically invisible. -/
theorem quaternionHaar_prefixPolynomialEqv
    (blocks : Nat) {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right)
    (hleft : SupportedQuaternionBlocks blocks left)
    (hright : SupportedQuaternionBlocks blocks right) :
    quaternionHaar blocks left ≈ quaternionHaar blocks right := by
  induction heqv with
  | nil => exact Q'.eqv_refl 0
  | @cons leftTerm rightTerm leftRest rightRest hterm hrest induction =>
      change
        leftTerm.2 * quaternionHaarMono blocks leftTerm.1 +
              quaternionHaar blocks leftRest ≈
          rightTerm.2 * quaternionHaarMono blocks rightTerm.1 +
              quaternionHaar blocks rightRest
      apply Q'.add_eqv_congr'
      · refine Q'.eqv_trans _
          (rightTerm.2 * quaternionHaarMono blocks leftTerm.1) _
          (Q'.mul_eqv_congr_right _ _ _ hterm.coefficient) ?_
        exact Q'.mul_eqv_congr_left _ _ _
          (quaternionHaarMono_prefix_congr hterm
            (hleft leftTerm (by simp))
            (hright rightTerm (by simp)))
      · exact induction
          (fun term hmem => hleft term (by simp [hmem]))
          (fun term hmem => hright term (by simp [hmem]))

/-! ## 5. Coordinate-sign invariance (quaternion inversion) -/

/-- Parity of the total exponent on a selected finite coordinate prefix. -/
def selectedExponentParity
    (coordinates : Nat) (selected : Nat → Bool)
    (monomial : List Nat) : Bool :=
  (List.range coordinates).foldl
    (fun parity coordinate =>
      if selected coordinate then
        xor parity (decide (exponentAt monomial coordinate % 2 = 1))
      else parity)
    false

/-- Apply the coefficient sign generated by changing the sign of every
selected coordinate. -/
def signSelectedTerm
    (coordinates : Nat) (selected : Nat → Bool)
    (term : RatTerm) : RatTerm :=
  (term.1,
    if selectedExponentParity coordinates selected term.1
    then -term.2 else term.2)

def signSelectedPolynomial
    (coordinates : Nat) (selected : Nat → Bool)
    (polynomial : RatPoly) : RatPoly :=
  polynomial.map (signSelectedTerm coordinates selected)

private theorem selectedExponentParity_false_of_even
    (coordinates : Nat) (selected : Nat → Bool)
    (monomial : List Nat)
    (heven : ∀ coordinate, coordinate < coordinates →
      selected coordinate = true →
      exponentAt monomial coordinate % 2 = 0) :
    selectedExponentParity coordinates selected monomial = false := by
  unfold selectedExponentParity
  have hfold : ∀ entries : List Nat,
      (∀ coordinate, coordinate ∈ entries →
        selected coordinate = true →
        exponentAt monomial coordinate % 2 = 0) →
      entries.foldl
          (fun parity coordinate =>
            if selected coordinate then
              xor parity
                (decide (exponentAt monomial coordinate % 2 = 1))
            else parity)
          false = false := by
    intro entries hentries
    induction entries with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.foldl_cons]
        by_cases hselected : selected head = true
        · rw [if_pos hselected]
          have hzero := hentries head List.mem_cons_self hselected
          have hone : exponentAt monomial head % 2 ≠ 1 := by omega
          simp only [hone]
          exact induction
            (fun coordinate hcoordinate =>
              hentries coordinate
                (List.mem_cons_of_mem head hcoordinate))
        · rw [if_neg hselected]
          exact induction
            (fun coordinate hcoordinate =>
              hentries coordinate
                (List.mem_cons_of_mem head hcoordinate))
  apply hfold (List.range coordinates)
  intro coordinate hcoordinate
  exact heven coordinate (List.mem_range.mp hcoordinate)

private theorem selectedExponentParity_true_has_odd
    (coordinates : Nat) (selected : Nat → Bool)
    (monomial : List Nat)
    (hparity :
      selectedExponentParity coordinates selected monomial = true) :
    ∃ coordinate,
      coordinate < coordinates ∧
      selected coordinate = true ∧
      exponentAt monomial coordinate % 2 = 1 := by
  by_cases hodd : ∃ coordinate,
      coordinate < coordinates ∧
      selected coordinate = true ∧
      exponentAt monomial coordinate % 2 = 1
  · exact hodd
  · have heven : ∀ coordinate, coordinate < coordinates →
        selected coordinate = true →
        exponentAt monomial coordinate % 2 = 0 := by
      intro coordinate hcoordinate hselected
      have hnotOne : exponentAt monomial coordinate % 2 ≠ 1 := by
        intro hone
        exact hodd ⟨coordinate, hcoordinate, hselected, hone⟩
      omega
    rw [selectedExponentParity_false_of_even
      coordinates selected monomial heven] at hparity
    contradiction

private theorem decide_exponentParity_add
    (left right : Nat) :
    decide ((left + right) % 2 = 1) =
      xor (decide (left % 2 = 1))
        (decide (right % 2 = 1)) := by
  have hleft : left % 2 = 0 ∨ left % 2 = 1 := by omega
  have hright : right % 2 = 0 ∨ right % 2 = 1 := by omega
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright <;>
    rw [Nat.add_mod, hleft, hright] <;> decide

private theorem selectedExponentParity_monoMul
    (coordinates : Nat) (selected : Nat → Bool)
    (left right : List Nat) :
    selectedExponentParity coordinates selected
        (monoMul left right) =
      xor
        (selectedExponentParity coordinates selected left)
        (selectedExponentParity coordinates selected right) := by
  unfold selectedExponentParity
  have hfold : ∀ (entries : List Nat) (leftParity rightParity : Bool),
      entries.foldl
          (fun parity coordinate =>
            if selected coordinate then
              xor parity
                (decide
                  (exponentAt (monoMul left right) coordinate % 2 = 1))
            else parity)
          (xor leftParity rightParity) =
        xor
          (entries.foldl
            (fun parity coordinate =>
              if selected coordinate then
                xor parity
                  (decide (exponentAt left coordinate % 2 = 1))
              else parity)
            leftParity)
          (entries.foldl
            (fun parity coordinate =>
              if selected coordinate then
                xor parity
                  (decide (exponentAt right coordinate % 2 = 1))
              else parity)
            rightParity) := by
    intro entries leftParity rightParity
    induction entries generalizing leftParity rightParity with
    | nil => rfl
    | cons coordinate rest induction =>
        simp only [List.foldl_cons]
        by_cases hselected : selected coordinate = true
        · rw [if_pos hselected, if_pos hselected, if_pos hselected,
            exponentAt_monoMul,
            decide_exponentParity_add]
          have hxor : ∀ leftBit rightBit : Bool,
              xor (xor leftParity rightParity)
                  (xor leftBit rightBit) =
                xor (xor leftParity leftBit)
                  (xor rightParity rightBit) := by
            intro leftBit rightBit
            cases leftParity <;> cases rightParity <;>
              cases leftBit <;> cases rightBit <;> rfl
          rw [hxor]
          exact induction _ _
        · rw [if_neg hselected, if_neg hselected, if_neg hselected]
          exact induction _ _
  simpa only [Bool.false_xor] using
    hfold (List.range coordinates) false false

private theorem selectedExponentParity_prefix_congr
    {blocks : Nat} (selected : Nat → Bool)
    {left right : RatTerm}
    (heqv : QuaternionPrefixTermEqv blocks left right) :
    selectedExponentParity (4 * blocks) selected left.1 =
      selectedExponentParity (4 * blocks) selected right.1 := by
  unfold selectedExponentParity
  have hfold : ∀ (entries : List Nat) (parity : Bool),
      (∀ coordinate, coordinate ∈ entries → coordinate < 4 * blocks) →
      entries.foldl
          (fun current coordinate =>
            if selected coordinate then
              xor current
                (decide (exponentAt left.1 coordinate % 2 = 1))
            else current)
          parity =
        entries.foldl
          (fun current coordinate =>
            if selected coordinate then
              xor current
                (decide (exponentAt right.1 coordinate % 2 = 1))
            else current)
          parity := by
    intro entries parity hentries
    induction entries generalizing parity with
    | nil => rfl
    | cons coordinate rest induction =>
        simp only [List.foldl_cons]
        by_cases hselected : selected coordinate = true
        · rw [if_pos hselected, if_pos hselected,
            heqv.exponent coordinate
              (hentries coordinate List.mem_cons_self)]
          exact induction _
            (fun entry hentry =>
              hentries entry (List.mem_cons_of_mem coordinate hentry))
        · rw [if_neg hselected, if_neg hselected]
          exact induction _
            (fun entry hentry =>
              hentries entry (List.mem_cons_of_mem coordinate hentry))
  exact hfold (List.range (4 * blocks)) false
    (fun coordinate hcoordinate => List.mem_range.mp hcoordinate)

namespace QuaternionPrefixPolynomialEqv

/-- Coordinate-sign substitution respects prefix equivalence. -/
theorem signSelected {blocks : Nat} (selected : Nat → Bool)
    {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks
      (signSelectedPolynomial (4 * blocks) selected left)
      (signSelectedPolynomial (4 * blocks) selected right) := by
  induction heqv with
  | nil => exact .nil
  | cons hterm hrest induction =>
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · unfold signSelectedTerm
          rw [selectedExponentParity_prefix_congr selected hterm]
          split
          · exact Q'.neg_eqv_congr _ _ hterm.coefficient
          · exact hterm.coefficient
        · exact hterm.exponent
      · exact induction

end QuaternionPrefixPolynomialEqv

private theorem sphereMoment4_zero_of_component_odd
    {e0 e1 e2 e3 : Nat}
    (hodd : e0 % 2 = 1 ∨ e1 % 2 = 1 ∨
      e2 % 2 = 1 ∨ e3 % 2 = 1) :
    sphereMoment4 e0 e1 e2 e3 = 0 := by
  unfold sphereMoment4
  rw [dif_neg]
  intro heven
  rcases hodd with hodd | hodd | hodd | hodd <;> omega

private theorem quaternionHaarPrefix_zero_of_odd_coordinate
    (blocks : Nat) (monomial : List Nat)
    {coordinate : Nat}
    (hcoordinate : coordinate < 4 * blocks)
    (hodd : exponentAt monomial coordinate % 2 = 1) :
    quaternionHaarPrefix blocks monomial ≈ 0 := by
  refine Q'.eqv_trans _
    (listQProduct
      (quaternionBlockMoment monomial)
      (quaternionBlockOrder blocks)) _
    (quaternionHaarPrefix_eq_block_product _ _) ?_
  let block := coordinate / 4
  have hblock : block < blocks := by omega
  have hblockMem : block ∈ quaternionBlockOrder blocks :=
    (mem_quaternionBlockOrder_iff block blocks).mpr hblock
  have hzero : quaternionBlockMoment monomial block = 0 := by
    unfold quaternionBlockMoment block
    have hcomponent : coordinate % 4 < 4 := Nat.mod_lt _ (by decide)
    have hcoordinateEq :
        coordinate = 4 * (coordinate / 4) + coordinate % 4 := by
      omega
    rw [hcoordinateEq] at hodd
    have hcases :
        coordinate % 4 = 0 ∨ coordinate % 4 = 1 ∨
          coordinate % 4 = 2 ∨ coordinate % 4 = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · rw [h0] at hodd
      exact sphereMoment4_zero_of_component_odd (Or.inl hodd)
    · rw [h1] at hodd
      exact sphereMoment4_zero_of_component_odd (Or.inr (Or.inl hodd))
    · rw [h2] at hodd
      exact sphereMoment4_zero_of_component_odd
        (Or.inr (Or.inr (Or.inl hodd)))
    · rw [h3] at hodd
      exact sphereMoment4_zero_of_component_odd
        (Or.inr (Or.inr (Or.inr hodd)))
  have product_zero_of_mem : ∀ entries : List Nat,
      block ∈ entries →
      listQProduct (quaternionBlockMoment monomial) entries ≈ 0 := by
    intro entries hmem
    induction entries with
    | nil => cases hmem
    | cons head tail induction =>
        simp only [listQProduct]
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst head
          rw [hzero]
          exact Q'.zero_mul_eqv _
        · refine Q'.eqv_trans _
              (quaternionBlockMoment monomial head * 0) _
              (Q'.mul_eqv_congr_left _ _ _ (induction htail)) ?_
          exact Q'.mul_zero_eqv _
  exact product_zero_of_mem _ hblockMem

private theorem quaternionHaarMono_zero_of_odd_coordinate
    (blocks : Nat) (monomial : List Nat)
    {coordinate : Nat}
    (hcoordinate : coordinate < 4 * blocks)
    (hodd : exponentAt monomial coordinate % 2 = 1) :
    quaternionHaarMono blocks monomial ≈ 0 := by
  unfold quaternionHaarMono
  split
  · exact quaternionHaarPrefix_zero_of_odd_coordinate
      blocks monomial hcoordinate hodd
  · exact Q'.eqv_refl 0

private theorem quaternionHaar_signSelectedTerm
    (blocks : Nat) (selected : Nat → Bool)
    (term : RatTerm) :
    (signSelectedTerm (4 * blocks) selected term).2 *
        quaternionHaarMono blocks
          (signSelectedTerm (4 * blocks) selected term).1 ≈
      term.2 * quaternionHaarMono blocks term.1 := by
  unfold signSelectedTerm
  by_cases hparity :
      selectedExponentParity (4 * blocks) selected term.1 = true
  · rw [if_pos hparity]
    obtain ⟨coordinate, hcoordinate, _, hodd⟩ :=
      selectedExponentParity_true_has_odd
        (4 * blocks) selected term.1 hparity
    have hzero := quaternionHaarMono_zero_of_odd_coordinate
      blocks term.1 hcoordinate hodd
    refine Q'.eqv_trans _ ((-term.2) * 0) _
      (Q'.mul_eqv_congr_left _ _ _ hzero) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) ?_
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (term.2 * 0) _
        (Q'.mul_eqv_congr_left _ _ _ hzero)
        (Q'.mul_zero_eqv _))
  · rw [if_neg hparity]
    exact Q'.eqv_refl _

/-- Exact product Haar is invariant under independent sign changes of any
selected real quaternion coordinates.  Quaternion inversion is obtained by
selecting the three vector coordinates of a block. -/
theorem quaternionHaar_signSelected
    (blocks : Nat) (selected : Nat → Bool) :
    ∀ polynomial : RatPoly,
      quaternionHaar blocks
          (signSelectedPolynomial (4 * blocks) selected polynomial) ≈
        quaternionHaar blocks polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (signSelectedTerm (4 * blocks) selected term).2 *
              quaternionHaarMono blocks
                (signSelectedTerm (4 * blocks) selected term).1 +
            quaternionHaar blocks
              (signSelectedPolynomial (4 * blocks) selected rest) ≈
          term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks rest
      exact Q'.add_eqv_congr'
        (quaternionHaar_signSelectedTerm blocks selected term)
        (quaternionHaar_signSelected blocks selected rest)

/-! ## 6. Coordinate-sign substitution as a polynomial homomorphism -/

theorem signSelectedPolynomial_add
    (coordinates : Nat) (selected : Nat → Bool)
    (left right : RatPoly) :
    signSelectedPolynomial coordinates selected (polyAdd left right) =
      polyAdd
        (signSelectedPolynomial coordinates selected left)
        (signSelectedPolynomial coordinates selected right) := by
  exact List.map_append

theorem signSelectedPolynomial_neg
    (coordinates : Nat) (selected : Nat → Bool)
    (polynomial : RatPoly) :
    signSelectedPolynomial coordinates selected (polyNeg polynomial) =
      polyNeg
        (signSelectedPolynomial coordinates selected polynomial) := by
  unfold signSelectedPolynomial polyNeg
  rw [List.map_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatTerm => polynomial.map f)
  funext term
  simp only [Function.comp_apply, signSelectedTerm]
  by_cases hparity :
      selectedExponentParity coordinates selected term.1 = true
  · rw [if_pos hparity, if_pos hparity]
  · rw [if_neg hparity, if_neg hparity]

private theorem signSelectedTerm_monoMul_prefix
    (blocks : Nat) (selected : Nat → Bool)
    (left right : RatTerm) :
    QuaternionPrefixTermEqv blocks
      (signSelectedTerm (4 * blocks) selected
        (monoMul left.1 right.1, left.2 * right.2))
      (monoMul left.1 right.1,
        (signSelectedTerm (4 * blocks) selected left).2 *
          (signSelectedTerm (4 * blocks) selected right).2) := by
  constructor
  · unfold signSelectedTerm
    rw [selectedExponentParity_monoMul]
    generalize hleft :
      selectedExponentParity (4 * blocks) selected left.1 = leftParity
    generalize hright :
      selectedExponentParity (4 * blocks) selected right.1 = rightParity
    cases leftParity <;> cases rightParity
    · simp only [hleft, hright, Bool.false_xor, if_false, Prod.snd]
      exact Q'.eqv_refl _
    · simp only [hleft, hright, Bool.false_xor, if_false, if_true,
        Prod.snd]
      exact Q'.eqv_symm (Q'.mul_neg_eqv left.2 right.2)
    · simp only [hleft, hright, Bool.true_xor, Bool.not_false,
        if_false, if_true, Prod.snd]
      exact Q'.eqv_symm (Q'.neg_mul_eqv left.2 right.2)
    · simp only [hleft, hright, Bool.true_xor, Bool.not_true,
        if_false, if_true, Prod.snd]
      exact Q'.eqv_symm
        (Q'.eqv_trans _ (-(left.2 * (-right.2))) _
          (Q'.neg_mul_eqv left.2 (-right.2))
          (Q'.eqv_trans _ (-(-(left.2 * right.2))) _
            (Q'.neg_eqv_congr _ _
              (Q'.mul_neg_eqv left.2 right.2))
            (Q'.neg_neg_eqv (left.2 * right.2))))
  · intro coordinate hcoordinate
    rfl

private theorem signSelectedPolynomial_mulRow_prefix
    (blocks : Nat) (selected : Nat → Bool)
    (source : RatTerm) : ∀ right : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (signSelectedPolynomial (4 * blocks) selected
        (right.map fun target =>
          (monoMul source.1 target.1,
            source.2 * target.2)))
      ((signSelectedPolynomial (4 * blocks) selected right).map
        fun target =>
          (monoMul
              (signSelectedTerm (4 * blocks) selected source).1
              target.1,
            (signSelectedTerm (4 * blocks) selected source).2 *
              target.2))
  | [] => .nil
  | target :: rest => by
      exact QuaternionPrefixPolynomialEqv.cons
        (signSelectedTerm_monoMul_prefix
          blocks selected source target)
        (signSelectedPolynomial_mulRow_prefix
          blocks selected source rest)

/-- Independent coordinate sign substitution is multiplicative modulo the
prefix relation (coefficients are compared by exact rational equivalence). -/
theorem signSelectedPolynomial_mul_prefix
    (blocks : Nat) (selected : Nat → Bool) :
    ∀ left right : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (signSelectedPolynomial (4 * blocks) selected
        (polyMul left right))
      (polyMul
        (signSelectedPolynomial (4 * blocks) selected left)
        (signSelectedPolynomial (4 * blocks) selected right))
  | [], right => .nil
  | source :: rest, right => by
      simpa only [polyMul, List.flatMap_cons,
        signSelectedPolynomial, List.map_append, List.map_cons] using
        (QuaternionPrefixPolynomialEqv.append
          (signSelectedPolynomial_mulRow_prefix
            blocks selected source right)
          (signSelectedPolynomial_mul_prefix
            blocks selected rest right))

/-- Coordinate-sign substitution commutes with scalar multiplication modulo
exact rational coefficient equivalence. -/
theorem signSelectedPolynomial_smul_prefix
    (blocks : Nat) (selected : Nat → Bool) (scale : Q') :
    ∀ polynomial : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (signSelectedPolynomial (4 * blocks) selected
        (polySmul scale polynomial))
      (polySmul scale
        (signSelectedPolynomial (4 * blocks) selected polynomial))
  | [] => .nil
  | term :: rest => by
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · unfold signSelectedTerm
          generalize hparity :
            selectedExponentParity (4 * blocks) selected term.1 = parity
          cases parity
          · simp only [hparity, Prod.snd, if_false]
            exact Q'.eqv_refl _
          · simp only [hparity, Prod.snd, if_true]
            exact Q'.eqv_symm (Q'.mul_neg_eqv scale term.2)
        · intro coordinate hcoordinate
          rfl
      · exact signSelectedPolynomial_smul_prefix
          blocks selected scale rest

private theorem selectedExponentParity_nil
    (coordinates : Nat) (selected : Nat → Bool) :
    selectedExponentParity coordinates selected [] = false := by
  apply selectedExponentParity_false_of_even
  intro coordinate hcoordinate hselected
  simp [exponentAt]

private theorem signSelectedPolynomial_one
    (coordinates : Nat) (selected : Nat → Bool) :
    signSelectedPolynomial coordinates selected polyOne = polyOne := by
  simp [signSelectedPolynomial, signSelectedTerm, polyOne,
    selectedExponentParity_nil coordinates selected]

/-- Every all-spin character is covariant under coordinate-sign
substitution, modulo exact rational coefficient equivalence. -/
theorem signSelectedPolynomial_character_prefix
    (blocks : Nat) (selected : Nat → Bool)
    (scalar : RatPoly) : ∀ spin,
    QuaternionPrefixPolynomialEqv blocks
      (signSelectedPolynomial (4 * blocks) selected
        (characterPolynomial scalar spin))
      (characterPolynomial
        (signSelectedPolynomial (4 * blocks) selected scalar) spin)
  | 0 => by
      change QuaternionPrefixPolynomialEqv blocks
        (signSelectedPolynomial (4 * blocks) selected polyOne)
        polyOne
      rw [signSelectedPolynomial_one]
      exact QuaternionPrefixPolynomialEqv.refl _ _
  | 1 => by
      change QuaternionPrefixPolynomialEqv blocks
        (signSelectedPolynomial (4 * blocks) selected
          (polySmul 2 scalar))
        (polySmul 2
          (signSelectedPolynomial (4 * blocks) selected scalar))
      exact signSelectedPolynomial_smul_prefix
        blocks selected 2 scalar
  | spin + 2 => by
      change QuaternionPrefixPolynomialEqv blocks
        (signSelectedPolynomial (4 * blocks) selected
          (polyAdd
            (polyMul (polySmul 2 scalar)
              (characterPolynomial scalar (spin + 1)))
            (polySmul (-1)
              (characterPolynomial scalar spin))))
        (polyAdd
          (polyMul
            (polySmul 2
              (signSelectedPolynomial (4 * blocks) selected scalar))
            (characterPolynomial
              (signSelectedPolynomial (4 * blocks) selected scalar)
              (spin + 1)))
          (polySmul (-1)
            (characterPolynomial
              (signSelectedPolynomial (4 * blocks) selected scalar) spin)))
      rw [signSelectedPolynomial_add]
      exact QuaternionPrefixPolynomialEqv.append
        (QuaternionPrefixPolynomialEqv.trans
          (signSelectedPolynomial_mul_prefix blocks selected
            (polySmul 2 scalar)
            (characterPolynomial scalar (spin + 1)))
          (QuaternionPrefixPolynomialEqv.mul
            (signSelectedPolynomial_smul_prefix
              blocks selected 2 scalar)
            (signSelectedPolynomial_character_prefix
              blocks selected scalar (spin + 1))))
        (QuaternionPrefixPolynomialEqv.trans
          (signSelectedPolynomial_smul_prefix
            blocks selected (-1)
            (characterPolynomial scalar spin))
          (QuaternionPrefixPolynomialEqv.smul (-1)
            (signSelectedPolynomial_character_prefix
              blocks selected scalar spin)))

end YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaarPrefix_eq_block_product
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.QuaternionBlockInvolution.order_map_perm
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaarMono_reindex
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaar_reindex
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaar_prefixPolynomialEqv
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.reindexQuaternionPolynomial_character_prefix
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.signSelectedPolynomial_character_prefix
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaar_signSelected
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.natList_eq_of_length_getD
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.monoMul_length_of_equal
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.exponentAt_monoMul
