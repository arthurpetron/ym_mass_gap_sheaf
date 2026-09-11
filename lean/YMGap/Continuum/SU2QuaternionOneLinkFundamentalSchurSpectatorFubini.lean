/-
# Spectator-stable Fubini reduction for one-link fundamental Schur contraction

The one-link fundamental Schur theorem computes a fully integrated complex
matrix-coefficient pair in block zero.  A production link contraction needs a
stronger interface: polynomial factors which do not depend on the selected
link must survive its partial integration and remain available for the later
finite-product integrations.

This leaf supplies that interface without expanding any face or lattice
product.  A polynomial is independent of a quaternion block when clearing
that block fixes every one of its raw monomials.  This predicate is closed
under the raw polynomial operations.  At monomial level, such a left factor
commutes exactly with the exponent mask and contributes zero exponent to the
selected block moment.  Consequently

    H(integrate_b (spectator * local))
      ~= H(spectator * integrate_b local),

and, for `b < blockCount`, finite-product Fubini gives

    H(spectator * local)
      ~= H(spectator * integrate_b local).

The result is lifted componentwise to the honest complex-pair carrier and
specialized to the forward/reverse fundamental coefficient product.  This is
the exact spectator-stability reduction needed before sequential link
contractions.

Honest remaining boundary: the existing theorem
`oneLink_oriented_fundamental_schur` identifies the *fully integrated*
block-zero scalar.  It does not state that partial integration of the
arbitrary block fundamental pair is the corresponding constant polynomial.
No theorem below infers that stronger statement from extensional polynomial
equality, because `finiteProductHaar` currently has no congruence theorem for
`RatPolyEqv`.  Thus this file reduces the spectator problem to the explicit
generic-block partial Schur identity; it does not claim that identity or any
closed-loop spin/fusion comparison.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
import YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur

namespace YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-! ## 1. Raw monomial independence of one quaternion block -/

/-- A raw polynomial is independent of `block` when clearing that block is
the identity on every monomial occurrence.  Coefficients and duplicate
monomials are deliberately irrelevant to this syntactic locality predicate. -/
def QuaternionBlockIndependent
    (block : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    clearQuaternionBlock block term.1 = term.1

/-- Clearing a block twice is the same as clearing it once. -/
private theorem clearQuaternionBlockFrom_idempotent
    (block start : Nat) : ∀ monomial : List Nat,
    clearQuaternionBlockFrom block start
        (clearQuaternionBlockFrom block start monomial) =
      clearQuaternionBlockFrom block start monomial
  | [] => rfl
  | exponent :: tail => by
      simp only [clearQuaternionBlockFrom]
      by_cases hcoordinate : coordinateInQuaternionBlock block start
      · simp only [hcoordinate, if_true]
        rw [clearQuaternionBlockFrom_idempotent block (start + 1) tail]
      · simp only [hcoordinate, if_false]
        rw [clearQuaternionBlockFrom_idempotent block (start + 1) tail]

theorem clearQuaternionBlock_idempotent
    (block : Nat) (monomial : List Nat) :
    clearQuaternionBlock block (clearQuaternionBlock block monomial) =
      clearQuaternionBlock block monomial := by
  exact clearQuaternionBlockFrom_idempotent block 0 monomial

/-- Every partially integrated polynomial is independent of the block that
was integrated. -/
theorem integrateQuaternionBlock_independent
    (block : Nat) (polynomial : RatPoly) :
    QuaternionBlockIndependent block
      (integrateQuaternionBlock block polynomial) := by
  intro term hterm
  unfold integrateQuaternionBlock at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  unfold integrateQuaternionBlockTerm
  exact clearQuaternionBlock_idempotent block source.1

/-- If the left monomial is fixed by the block mask, clearing a product
clears only the right monomial. -/
private theorem clearQuaternionBlockFrom_monoMul_of_left_fixed
    (block start : Nat) : ∀ (left right : List Nat),
    clearQuaternionBlockFrom block start left = left →
      clearQuaternionBlockFrom block start (monoMul left right) =
        monoMul left (clearQuaternionBlockFrom block start right)
  | [], right, _ => rfl
  | leftHead :: leftTail, [], hleft => hleft
  | leftHead :: leftTail, rightHead :: rightTail, hleft => by
      simp only [monoMul, clearQuaternionBlockFrom] at hleft ⊢
      by_cases hcoordinate : coordinateInQuaternionBlock block start
      · simp only [hcoordinate, if_true] at hleft ⊢
        have hhead : leftHead = 0 := (List.cons.inj hleft).1.symm
        have htail :
            clearQuaternionBlockFrom block (start + 1) leftTail =
              leftTail := (List.cons.inj hleft).2
        subst leftHead
        simp only [Nat.zero_add]
        rw [clearQuaternionBlockFrom_monoMul_of_left_fixed
          block (start + 1) leftTail rightTail htail]
      · simp only [hcoordinate, if_false] at hleft ⊢
        have htail :
            clearQuaternionBlockFrom block (start + 1) leftTail =
              leftTail := (List.cons.inj hleft).2
        rw [clearQuaternionBlockFrom_monoMul_of_left_fixed
          block (start + 1) leftTail rightTail htail]

theorem clearQuaternionBlock_monoMul_of_left_fixed
    (block : Nat) (left right : List Nat)
    (hleft : clearQuaternionBlock block left = left) :
    clearQuaternionBlock block (monoMul left right) =
      monoMul left (clearQuaternionBlock block right) := by
  exact clearQuaternionBlockFrom_monoMul_of_left_fixed
    block 0 left right hleft

/-- An independent left monomial contributes zero exponent to the selected
block, so that block's moment is exactly the right monomial's moment. -/
theorem quaternionBlockMoment_monoMul_of_left_fixed
    (block : Nat) (left right : List Nat)
    (hleft : clearQuaternionBlock block left = left) :
    quaternionBlockMoment block (monoMul left right) =
      quaternionBlockMoment block right := by
  have hzero : ∀ component, component < 4 →
      exponentAt left (4 * block + component) = 0 := by
    intro component hcomponent
    have hclear := exponentAt_clearQuaternionBlock_self
      left block component hcomponent
    rw [hleft] at hclear
    exact hclear
  have hzero0 : exponentAt left (4 * block) = 0 := by
    simpa only [Nat.add_zero] using hzero 0 (by omega)
  unfold quaternionBlockMoment
  rw [exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_monoMul, exponentAt_monoMul,
    hzero0, hzero 1 (by omega),
    hzero 2 (by omega), hzero 3 (by omega)]
  simp only [Nat.zero_add]

/-! ## 2. Independence constructors -/

theorem quaternionBlockIndependent_polyZero (block : Nat) :
    QuaternionBlockIndependent block polyZero := by
  intro term hterm
  exact False.elim (List.not_mem_nil hterm)

theorem quaternionBlockIndependent_polyOne (block : Nat) :
    QuaternionBlockIndependent block polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_singleton] at hterm
  subst term
  rfl

theorem quaternionBlockIndependent_polyConst
    (block : Nat) (coefficient : Q') :
    QuaternionBlockIndependent block (polyConst coefficient) := by
  intro term hterm
  simp only [polyConst, List.mem_singleton] at hterm
  subst term
  rfl

theorem quaternionBlockIndependent_polyAdd
    {block : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockIndependent block left)
    (hright : QuaternionBlockIndependent block right) :
    QuaternionBlockIndependent block (polyAdd left right) := by
  intro term hterm
  simp only [polyAdd, List.mem_append] at hterm
  cases hterm with
  | inl hterm => exact hleft term hterm
  | inr hterm => exact hright term hterm

theorem quaternionBlockIndependent_polyNeg
    {block : Nat} {polynomial : RatPoly}
    (hindependent : QuaternionBlockIndependent block polynomial) :
    QuaternionBlockIndependent block (polyNeg polynomial) := by
  intro term hterm
  unfold polyNeg at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hindependent source hsource

theorem quaternionBlockIndependent_polySmul
    (coefficient : Q') {block : Nat} {polynomial : RatPoly}
    (hindependent : QuaternionBlockIndependent block polynomial) :
    QuaternionBlockIndependent block (polySmul coefficient polynomial) := by
  intro term hterm
  unfold polySmul at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hindependent source hsource

private theorem mem_polyMul_local
    {left right : RatPoly} {term : RatTerm}
    (hterm : term ∈ polyMul left right) :
    ∃ leftTerm, leftTerm ∈ left ∧
      ∃ rightTerm, rightTerm ∈ right ∧
        term =
          (monoMul leftTerm.1 rightTerm.1,
            leftTerm.2 * rightTerm.2) := by
  unfold polyMul at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨leftTerm, hleftTerm, hterm⟩ := hterm
  rw [List.mem_map] at hterm
  obtain ⟨rightTerm, hrightTerm, rfl⟩ := hterm
  exact ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩

theorem quaternionBlockIndependent_polyMul
    {block : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockIndependent block left)
    (hright : QuaternionBlockIndependent block right) :
    QuaternionBlockIndependent block (polyMul left right) := by
  intro term hterm
  obtain ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul_local hterm
  rw [clearQuaternionBlock_monoMul_of_left_fixed
    block leftTerm.1 rightTerm.1 (hleft leftTerm hleftTerm)]
  rw [hright rightTerm hrightTerm]

/-! ## 2a. Componentwise complex independence and link-block constructors -/

/-- Both real components of an honest complex polynomial are independent of
the selected quaternion block. -/
def ComplexQuaternionBlockIndependent
    (block : Nat) (value : ComplexRatPoly) : Prop :=
  QuaternionBlockIndependent block value.1 ∧
    QuaternionBlockIndependent block value.2

theorem complexQuaternionBlockIndependent_conj
    {block : Nat} {value : ComplexRatPoly}
    (hindependent : ComplexQuaternionBlockIndependent block value) :
    ComplexQuaternionBlockIndependent block
      (complexRatPolyConj value) := by
  exact ⟨hindependent.1,
    quaternionBlockIndependent_polyNeg hindependent.2⟩

theorem complexQuaternionBlockIndependent_mul
    {block : Nat} {left right : ComplexRatPoly}
    (hleft : ComplexQuaternionBlockIndependent block left)
    (hright : ComplexQuaternionBlockIndependent block right) :
    ComplexQuaternionBlockIndependent block
      (complexRatPolyMul left right) := by
  constructor
  · exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hleft.1 hright.1)
      (quaternionBlockIndependent_polyNeg
        (quaternionBlockIndependent_polyMul hleft.2 hright.2))
  · exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polyMul hleft.1 hright.2)
      (quaternionBlockIndependent_polyMul hleft.2 hright.1)

/-- A variable monomial is fixed by a block mask whenever its unique
nonzero coordinate lies outside that block. -/
private theorem clearQuaternionBlockFrom_varMono_of_outside
    (block start : Nat) : ∀ coordinate : Nat,
    ¬ coordinateInQuaternionBlock block (start + coordinate) →
      clearQuaternionBlockFrom block start (varMono coordinate) =
        varMono coordinate
  | 0, hout => by
      have hout0 : ¬ coordinateInQuaternionBlock block start := by
        simpa only [Nat.add_zero] using hout
      simp [varMono, clearQuaternionBlockFrom, hout0]
  | coordinate + 1, hout => by
      have hout' :
          ¬ coordinateInQuaternionBlock block
            ((start + 1) + coordinate) := by
        have hcoordinate : (start + 1) + coordinate =
            start + (coordinate + 1) := by omega
        rw [hcoordinate]
        exact hout
      change
        (if coordinateInQuaternionBlock block start then 0 else 0) ::
              clearQuaternionBlockFrom block (start + 1)
                (varMono coordinate) =
          0 :: varMono coordinate
      simp only [ite_self]
      rw [clearQuaternionBlockFrom_varMono_of_outside
        block (start + 1) coordinate hout']

theorem clearQuaternionBlock_varMono_of_outside
    (block coordinate : Nat)
    (hout : ¬ coordinateInQuaternionBlock block coordinate) :
    clearQuaternionBlock block (varMono coordinate) =
      varMono coordinate := by
  unfold clearQuaternionBlock
  exact clearQuaternionBlockFrom_varMono_of_outside
    block 0 coordinate (by simpa only [Nat.zero_add] using hout)

theorem quaternionBlockIndependent_polyVar_of_outside
    (block coordinate : Nat)
    (hout : ¬ coordinateInQuaternionBlock block coordinate) :
    QuaternionBlockIndependent block (polyVar coordinate) := by
  intro term hterm
  simp only [polyVar, List.mem_singleton] at hterm
  subst term
  exact clearQuaternionBlock_varMono_of_outside block coordinate hout

/-- A coordinate of one quaternion link lies outside every distinct link
block. -/
theorem quaternionBlockIndependent_polyVar_of_distinctBlock
    {source target component : Nat}
    (hne : source ≠ target) (hcomponent : component < 4) :
    QuaternionBlockIndependent target
      (polyVar (4 * source + component)) := by
  apply quaternionBlockIndependent_polyVar_of_outside
  unfold coordinateInQuaternionBlock
  intro hinside
  omega

/-- Every fundamental matrix coefficient on `source` is independent of a
distinct quaternion link block `target`. -/
theorem complexQuaternionBlockIndependent_forwardFundamentalCoefficient
    {source target : Nat} (hne : source ≠ target)
    (row column : Bool) :
    ComplexQuaternionBlockIndependent target
      (forwardFundamentalCoefficient source row column) := by
  have h0 : QuaternionBlockIndependent target
      (polyVar (4 * source)) := by
    simpa using
      (quaternionBlockIndependent_polyVar_of_distinctBlock
        (source := source) (target := target) (component := 0)
        hne (by omega))
  have h1 : QuaternionBlockIndependent target
      (polyVar (4 * source + 1)) :=
    quaternionBlockIndependent_polyVar_of_distinctBlock
      (source := source) (target := target) (component := 1)
      hne (by omega)
  have h2 : QuaternionBlockIndependent target
      (polyVar (4 * source + 2)) :=
    quaternionBlockIndependent_polyVar_of_distinctBlock
      (source := source) (target := target) (component := 2)
      hne (by omega)
  have h3 : QuaternionBlockIndependent target
      (polyVar (4 * source + 3)) :=
    quaternionBlockIndependent_polyVar_of_distinctBlock
      (source := source) (target := target) (component := 3)
      hne (by omega)
  cases row <;> cases column
  · exact ⟨h0, h1⟩
  · exact ⟨h2, h3⟩
  · exact ⟨quaternionBlockIndependent_polyNeg h2, h3⟩
  · exact ⟨h0, quaternionBlockIndependent_polyNeg h1⟩

/-- The reverse-oriented coefficient has the same distinct-block locality as
the forward coefficient from which it is obtained by transpose-conjugation. -/
theorem complexQuaternionBlockIndependent_reverseFundamentalCoefficient
    {source target : Nat} (hne : source ≠ target)
    (row column : Bool) :
    ComplexQuaternionBlockIndependent target
      (reverseFundamentalCoefficient source row column) := by
  exact complexQuaternionBlockIndependent_conj
    (complexQuaternionBlockIndependent_forwardFundamentalCoefficient
      hne column row)

/-! ## 3. Factoring a spectator through partial integration -/

private def leftTermProduct
    (left : RatTerm) (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun right =>
    (monoMul left.1 right.1, left.2 * right.2)

private theorem polyMul_cons
    (left : RatTerm) (tail right : RatPoly) :
    polyMul (left :: tail) right =
      leftTermProduct left right ++ polyMul tail right := rfl

private theorem integrateQuaternionBlock_append
    (block : Nat) (left right : RatPoly) :
    integrateQuaternionBlock block (left ++ right) =
      integrateQuaternionBlock block left ++
        integrateQuaternionBlock block right := by
  unfold integrateQuaternionBlock
  exact List.map_append

private theorem finiteProductHaar_integrate_leftTermProduct
    (blockCount block : Nat) (left : RatTerm)
    (hleft : clearQuaternionBlock block left.1 = left.1) :
    ∀ right : RatPoly,
      finiteProductHaar blockCount
          (integrateQuaternionBlock block
            (leftTermProduct left right)) ≈
        finiteProductHaar blockCount
          (leftTermProduct left
            (integrateQuaternionBlock block right))
  | [] => Q'.eqv_refl 0
  | rightTerm :: tail => by
      change
        ((left.2 * rightTerm.2) *
              quaternionBlockMoment block
                (monoMul left.1 rightTerm.1)) *
              finiteProductHaarMono blockCount
                (clearQuaternionBlock block
                  (monoMul left.1 rightTerm.1)) +
            finiteProductHaar blockCount
              (integrateQuaternionBlock block
                (leftTermProduct left tail)) ≈
          (left.2 *
              (rightTerm.2 *
                quaternionBlockMoment block rightTerm.1)) *
              finiteProductHaarMono blockCount
                (monoMul left.1
                  (clearQuaternionBlock block rightTerm.1)) +
            finiteProductHaar blockCount
              (leftTermProduct left
                (integrateQuaternionBlock block tail))
      rw [quaternionBlockMoment_monoMul_of_left_fixed
          block left.1 rightTerm.1 hleft,
        clearQuaternionBlock_monoMul_of_left_fixed
          block left.1 rightTerm.1 hleft]
      exact q_add_congr
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_assoc_eqv left.2 rightTerm.2
            (quaternionBlockMoment block rightTerm.1)))
        (finiteProductHaar_integrate_leftTermProduct
          blockCount block left hleft tail)

/-- Partial integration factors through multiplication by a polynomial which
is independent of the selected block, at the exact finite-product functional
level.  No support or in-range hypothesis is required for this algebraic
identity. -/
theorem finiteProductHaar_integrateQuaternionBlock_polyMul_of_independent
    (blockCount block : Nat) : ∀ (spectator factor : RatPoly),
    QuaternionBlockIndependent block spectator →
      finiteProductHaar blockCount
          (integrateQuaternionBlock block
            (polyMul spectator factor)) ≈
        finiteProductHaar blockCount
          (polyMul spectator
            (integrateQuaternionBlock block factor))
  | [], factor, _ => Q'.eqv_refl 0
  | left :: tail, factor, hindependent => by
      have hleft : clearQuaternionBlock block left.1 = left.1 :=
        hindependent left List.mem_cons_self
      have htail : QuaternionBlockIndependent block tail := by
        intro term hterm
        exact hindependent term (List.mem_cons_of_mem left hterm)
      rw [polyMul_cons,
        integrateQuaternionBlock_append,
        polyMul_cons]
      refine Q'.eqv_trans _
          (finiteProductHaar blockCount
            (integrateQuaternionBlock block
              (leftTermProduct left factor)) +
          finiteProductHaar blockCount
            (integrateQuaternionBlock block
              (polyMul tail factor))) _ ?_ ?_
      · exact finiteProductHaar_append blockCount _ _
      · refine Q'.eqv_trans _
            (finiteProductHaar blockCount
              (leftTermProduct left
                (integrateQuaternionBlock block factor)) +
            finiteProductHaar blockCount
              (polyMul tail
                (integrateQuaternionBlock block factor))) _ ?_ ?_
        · exact q_add_congr
            (finiteProductHaar_integrate_leftTermProduct
              blockCount block left hleft factor)
            (finiteProductHaar_integrateQuaternionBlock_polyMul_of_independent
              blockCount block tail factor htail)
        · exact Q'.eqv_symm
            (finiteProductHaar_append blockCount _ _)

/-- In-range finite-product Fubini now removes the selected block while
leaving an independent spectator factor in place. -/
theorem finiteProductHaar_polyMul_eq_after_integrating_right
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator factor : RatPoly)
    (hindependent : QuaternionBlockIndependent block spectator) :
    finiteProductHaar blockCount (polyMul spectator factor) ≈
      finiteProductHaar blockCount
        (polyMul spectator
          (integrateQuaternionBlock block factor)) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finiteProductHaar_integrateQuaternionBlock
        blockCount block hblock (polyMul spectator factor)))
    (finiteProductHaar_integrateQuaternionBlock_polyMul_of_independent
      blockCount block spectator factor hindependent)

/-- Congruence of the finite-product functional through raw polynomial
addition, derived only from its established setoid linearity. -/
private theorem finiteProductHaar_polyAdd_congr
    (blockCount : Nat) {left left' right right' : RatPoly}
    (hleft : finiteProductHaar blockCount left ≈
      finiteProductHaar blockCount left')
    (hright : finiteProductHaar blockCount right ≈
      finiteProductHaar blockCount right') :
    finiteProductHaar blockCount (polyAdd left right) ≈
      finiteProductHaar blockCount (polyAdd left' right') :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_add blockCount left right)
    (Q'.eqv_trans _ _ _
      (q_add_congr hleft hright)
      (Q'.eqv_symm
        (finiteProductHaar_add blockCount left' right')))

/-- Congruence of the finite-product functional through raw polynomial
negation, again without asserting a global `RatPolyEqv` congruence API. -/
private theorem finiteProductHaar_polyNeg_congr
    (blockCount : Nat) {left right : RatPoly}
    (hvalue : finiteProductHaar blockCount left ≈
      finiteProductHaar blockCount right) :
    finiteProductHaar blockCount (polyNeg left) ≈
      finiteProductHaar blockCount (polyNeg right) :=
  Q'.eqv_trans _ _ _
    (finiteProductHaar_neg blockCount left)
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hvalue)
      (Q'.eqv_symm (finiteProductHaar_neg blockCount right)))

/-! ## 4. Honest complex-pair lift and fundamental specialization -/

/-- Partial integration on the two real components of an honest complex
rational polynomial. -/
def integrateQuaternionBlockComplex
    (block : Nat) (value : ComplexRatPoly) : ComplexRatPoly :=
  (integrateQuaternionBlock block value.1,
    integrateQuaternionBlock block value.2)

/-- Componentwise partial integration removes dependence on the integrated
block from both honest real components. -/
theorem integrateQuaternionBlockComplex_independent
    (block : Nat) (value : ComplexRatPoly) :
    ComplexQuaternionBlockIndependent block
      (integrateQuaternionBlockComplex block value) := by
  exact ⟨integrateQuaternionBlock_independent block value.1,
    integrateQuaternionBlock_independent block value.2⟩

/-- Multiply both real components of an honest complex polynomial by one
real spectator polynomial on the left. -/
def realSpectatorComplexMul
    (spectator : RatPoly) (value : ComplexRatPoly) : ComplexRatPoly :=
  (polyMul spectator value.1, polyMul spectator value.2)

/-- The forward/reverse oriented fundamental coefficient product on an
arbitrary base-four quaternion block. -/
def orientedFundamentalLinkContraction
    (block : Nat)
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    ComplexRatPoly :=
  complexRatPolyMul
    (forwardFundamentalCoefficient block forwardRow forwardColumn)
    (reverseFundamentalCoefficient block reverseRow reverseColumn)

/-- A local fundamental contraction on `source` is a valid complex spectator
for partial integration of every distinct link `target`. -/
theorem complexQuaternionBlockIndependent_orientedFundamentalLinkContraction
    {source target : Nat} (hne : source ≠ target)
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    ComplexQuaternionBlockIndependent target
      (orientedFundamentalLinkContraction source
        forwardRow forwardColumn reverseRow reverseColumn) := by
  exact complexQuaternionBlockIndependent_mul
    (complexQuaternionBlockIndependent_forwardFundamentalCoefficient
      hne forwardRow forwardColumn)
    (complexQuaternionBlockIndependent_reverseFundamentalCoefficient
      hne reverseRow reverseColumn)

/-- Complex-pair version of spectator-stable one-block Fubini. -/
theorem finiteProductHaarComplex_spectator_eq_after_integrating_right
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : RatPoly) (factor : ComplexRatPoly)
    (hindependent : QuaternionBlockIndependent block spectator) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (realSpectatorComplexMul spectator factor))
      (finiteProductHaarComplex blockCount
        (realSpectatorComplexMul spectator
          (integrateQuaternionBlockComplex block factor))) := by
  constructor
  · exact finiteProductHaar_polyMul_eq_after_integrating_right
      blockCount block hblock spectator factor.1 hindependent
  · exact finiteProductHaar_polyMul_eq_after_integrating_right
      blockCount block hblock spectator factor.2 hindependent

/-- Full honest-complex spectator law.  Each of the four scalar products in
complex multiplication is reduced by the scalar spectator theorem, and raw
addition/negation are transported only through the established linearity of
`finiteProductHaar`. -/
theorem finiteProductHaarComplex_complexSpectator_eq_after_integrating_right
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator factor : ComplexRatPoly)
    (hindependent :
      ComplexQuaternionBlockIndependent block spectator) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator factor))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (integrateQuaternionBlockComplex block factor))) := by
  constructor
  · exact finiteProductHaar_polyAdd_congr blockCount
      (finiteProductHaar_polyMul_eq_after_integrating_right
        blockCount block hblock spectator.1 factor.1 hindependent.1)
      (finiteProductHaar_polyNeg_congr blockCount
        (finiteProductHaar_polyMul_eq_after_integrating_right
          blockCount block hblock spectator.2 factor.2 hindependent.2))
  · exact finiteProductHaar_polyAdd_congr blockCount
      (finiteProductHaar_polyMul_eq_after_integrating_right
        blockCount block hblock spectator.1 factor.2 hindependent.1)
      (finiteProductHaar_polyMul_eq_after_integrating_right
        blockCount block hblock spectator.2 factor.1 hindependent.2)

/-- **Spectator-stable fundamental-link reduction.**  A forward/reverse
fundamental pair may be partially integrated inside any finite quaternion
product without disturbing a polynomial spectator independent of that link.

The right-hand partial integral is intentionally not rewritten to the Schur
delta: that is the separate generic-block partial Schur theorem still needed
to complete sequential closed-link contraction. -/
theorem orientedFundamentalLinkContraction_spectator_fubini
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : RatPoly)
    (hindependent : QuaternionBlockIndependent block spectator)
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (realSpectatorComplexMul spectator
          (orientedFundamentalLinkContraction block
            forwardRow forwardColumn reverseRow reverseColumn)))
      (finiteProductHaarComplex blockCount
        (realSpectatorComplexMul spectator
          (integrateQuaternionBlockComplex block
            (orientedFundamentalLinkContraction block
              forwardRow forwardColumn reverseRow reverseColumn)))) := by
  exact finiteProductHaarComplex_spectator_eq_after_integrating_right
    blockCount block hblock spectator
    (orientedFundamentalLinkContraction block
      forwardRow forwardColumn reverseRow reverseColumn)
    hindependent

/-- Complex-spectator form used by raw trace-network summands: an arbitrary
complex factor independent of the selected link remains in place while the
local forward/reverse fundamental contraction is partially integrated. -/
theorem orientedFundamentalLinkContraction_complexSpectator_fubini
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent :
      ComplexQuaternionBlockIndependent block spectator)
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedFundamentalLinkContraction block
            forwardRow forwardColumn reverseRow reverseColumn)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (integrateQuaternionBlockComplex block
            (orientedFundamentalLinkContraction block
              forwardRow forwardColumn reverseRow reverseColumn)))) := by
  exact
    finiteProductHaarComplex_complexSpectator_eq_after_integrating_right
      blockCount block hblock spectator
      (orientedFundamentalLinkContraction block
        forwardRow forwardColumn reverseRow reverseColumn)
      hindependent

/-- At block zero with no spectator, the local contraction used above is
exactly the polynomial appearing in the established one-link Schur theorem.
This records compatibility of the interfaces without strengthening the old
fully integrated conclusion. -/
theorem oneLink_oriented_fundamental_schur_as_linkContraction
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (orientedFundamentalLinkContraction 0
          forwardRow forwardColumn reverseRow reverseColumn))
      (orientedFundamentalSchurDelta
        forwardRow forwardColumn reverseRow reverseColumn) := by
  exact oneLink_oriented_fundamental_schur
    forwardRow forwardColumn reverseRow reverseColumn

#print axioms clearQuaternionBlock_idempotent
#print axioms integrateQuaternionBlock_independent
#print axioms clearQuaternionBlock_monoMul_of_left_fixed
#print axioms quaternionBlockMoment_monoMul_of_left_fixed
#print axioms quaternionBlockIndependent_polyMul
#print axioms complexQuaternionBlockIndependent_forwardFundamentalCoefficient
#print axioms complexQuaternionBlockIndependent_reverseFundamentalCoefficient
#print axioms complexQuaternionBlockIndependent_orientedFundamentalLinkContraction
#print axioms finiteProductHaar_integrateQuaternionBlock_polyMul_of_independent
#print axioms finiteProductHaar_polyMul_eq_after_integrating_right
#print axioms finiteProductHaarComplex_spectator_eq_after_integrating_right
#print axioms finiteProductHaarComplex_complexSpectator_eq_after_integrating_right
#print axioms orientedFundamentalLinkContraction_spectator_fubini
#print axioms orientedFundamentalLinkContraction_complexSpectator_fubini
#print axioms oneLink_oriented_fundamental_schur_as_linkContraction

end YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
