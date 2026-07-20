/-
# Generic-block partial fundamental Schur contraction

The established one-link theorem computes the fundamental Schur contraction
in block zero after a one-block Haar evaluation.  Closed trace networks need
the genuinely local statement: inside an arbitrary finite quaternion product,
one may replace a forward/reverse pair on an in-range block by the crossed
`1/2` delta while retaining an arbitrary honest complex spectator which is
independent of that block.

There is a small raw-carrier trap.  Partial integration clears four exponents
without shortening their exponent lists.  Consequently the partial integral
of a local pair is generally a sum of trailing-zero aliases, not literally a
`polyConst`.  This leaf treats that representation honestly.  It proves that
an arbitrary polynomial made only of all-zero exponent aliases acts, under
`finiteProductHaar`, by its coefficient sum.  The generic Schur theorem is
then stated only at the exact finite-product functional level.

No face polynomial, density product, bounded labelling family, or lattice
trajectory is unfolded or materialized here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

namespace YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- Exchange the second and third factors of a three-factor product. -/
private theorem q_mul_right_swap (a b c : Q') :
    (a * b) * c ≈ (a * c) * b :=
  Q'.eqv_trans _ (a * (b * c)) _
    (Q'.mul_assoc_eqv a b c)
    (Q'.eqv_trans _ (a * (c * b)) _
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b c))
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c b)))

/-! ## 1. The trailing-zero alias functional -/

/-- Sum the raw coefficients without identifying duplicate monomials. -/
def coefficientSum : RatPoly → Q'
  | [] => 0
  | term :: polynomial => term.2 + coefficientSum polynomial

/-- Every term is a constant *alias*: its complete exponent list consists of
zeros, although the list need not be empty. -/
def AllZeroExponentTerms (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → allZero term.1 = true

private theorem monoMul_drop (left right : List Nat) : ∀ count : Nat,
    (monoMul left right).drop count =
      monoMul (left.drop count) (right.drop count)
  | 0 => rfl
  | count + 1 => by
      cases left <;> cases right <;> simp [monoMul, monoMul_drop]
      next tail => cases tail.drop count <;> rfl

private theorem allZero_monoMul (left right : List Nat) :
    allZero (monoMul left right) =
      (allZero left && allZero right) := by
  induction left generalizing right with
  | nil => simp [monoMul, allZero]
  | cons head tail ih =>
      cases right with
      | nil => simp [monoMul, allZero]
      | cons other rest =>
          simp [monoMul, allZero, ih rest, Nat.add_eq_zero_iff,
            Bool.and_assoc, Bool.and_left_comm]

private theorem allZero_drop_of_true
    (monomial : List Nat) (hzero : allZero monomial = true) :
    ∀ count : Nat, allZero (monomial.drop count) = true
  | 0 => hzero
  | count + 1 => by
      cases monomial with
      | nil => rfl
      | cons head tail =>
          change allZero (tail.drop count) = true
          apply allZero_drop_of_true tail
          change (decide (head = 0) && allZero tail) = true at hzero
          exact ((Bool.and_eq_true _ _).mp hzero).2

private theorem exponentAt_eq_zero_of_allZero
    (monomial : List Nat) (hzero : allZero monomial = true) :
    ∀ coordinate : Nat, exponentAt monomial coordinate = 0 := by
  intro coordinate
  induction monomial generalizing coordinate with
  | nil => simp [exponentAt]
  | cons head tail ih =>
      change (decide (head = 0) && allZero tail) = true at hzero
      have hparts := (Bool.and_eq_true _ _).mp hzero
      have hhead : head = 0 := by simpa using hparts.1
      cases coordinate with
      | zero => simpa [exponentAt] using hhead
      | succ coordinate =>
          simpa [exponentAt] using ih hparts.2 coordinate

private theorem quaternionBlockMoment_monoMul_right_allZero
    (block : Nat) (left right : List Nat)
    (hright : allZero right = true) :
    quaternionBlockMoment block (monoMul left right) =
      quaternionBlockMoment block left := by
  unfold quaternionBlockMoment
  rw [exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_eq_zero_of_allZero right hright (4 * block),
    exponentAt_eq_zero_of_allZero right hright (4 * block + 1),
    exponentAt_eq_zero_of_allZero right hright (4 * block + 2),
    exponentAt_eq_zero_of_allZero right hright (4 * block + 3)]
  simp only [Nat.add_zero]

private theorem quaternionBlockMomentProduct_monoMul_right_allZero
    (left right : List Nat) (hright : allZero right = true) :
    ∀ blocks : List Nat,
      quaternionBlockMomentProduct (monoMul left right) blocks =
        quaternionBlockMomentProduct left blocks
  | [] => rfl
  | block :: blocks => by
      change
        quaternionBlockMoment block (monoMul left right) *
            quaternionBlockMomentProduct (monoMul left right) blocks =
          quaternionBlockMoment block left *
            quaternionBlockMomentProduct left blocks
      rw [quaternionBlockMoment_monoMul_right_allZero
          block left right hright,
        quaternionBlockMomentProduct_monoMul_right_allZero
          left right hright blocks]

/-- Appending any number of trailing zero exponents to a monomial does not
change its finite-product moment.  More generally the right factor may be an
arbitrary all-zero exponent list. -/
theorem finiteProductHaarMono_monoMul_right_allZero
    (blockCount : Nat) (left right : List Nat)
    (hright : allZero right = true) :
    finiteProductHaarMono blockCount (monoMul left right) =
      finiteProductHaarMono blockCount left := by
  unfold finiteProductHaarMono
  rw [monoMul_drop, allZero_monoMul,
    allZero_drop_of_true right hright (4 * blockCount)]
  simp only [Bool.and_true]
  by_cases htail : allZero (left.drop (4 * blockCount)) = true
  · simp only [htail, if_true]
    exact quaternionBlockMomentProduct_monoMul_right_allZero
      left right hright (List.range blockCount)
  · have hfalse : allZero (left.drop (4 * blockCount)) = false := by
      cases hvalue : allZero (left.drop (4 * blockCount)) with
      | false => rfl
      | true => exact (htail hvalue).elim
    simp only [hfalse, Bool.false_eq_true, if_false]

private def leftTermProduct
    (left : RatTerm) (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun right =>
    (monoMul left.1 right.1, left.2 * right.2)

private theorem finiteProductHaar_leftTermProduct_allZero
    (blockCount : Nat) (left : RatTerm) : ∀ aliases : RatPoly,
    AllZeroExponentTerms aliases →
      finiteProductHaar blockCount (leftTermProduct left aliases) ≈
        (left.2 * finiteProductHaarMono blockCount left.1) *
          coefficientSum aliases
  | [], _ => Q'.eqv_symm
      (Q'.mul_zero_eqv
        (left.2 * finiteProductHaarMono blockCount left.1))
  | alias :: aliases, hall => by
      have halias : allZero alias.1 = true :=
        hall alias List.mem_cons_self
      have htail : AllZeroExponentTerms aliases := by
        intro term hterm
        exact hall term (List.mem_cons_of_mem alias hterm)
      change
        (left.2 * alias.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 alias.1) +
            finiteProductHaar blockCount
              (leftTermProduct left aliases) ≈
          (left.2 * finiteProductHaarMono blockCount left.1) *
            (alias.2 + coefficientSum aliases)
      rw [finiteProductHaarMono_monoMul_right_allZero
        blockCount left.1 alias.1 halias]
      refine Q'.eqv_trans _
        ((left.2 * finiteProductHaarMono blockCount left.1) * alias.2 +
          (left.2 * finiteProductHaarMono blockCount left.1) *
            coefficientSum aliases) _ ?_ ?_
      · exact q_add_congr
          (q_mul_right_swap left.2 alias.2
            (finiteProductHaarMono blockCount left.1))
          (finiteProductHaar_leftTermProduct_allZero
            blockCount left aliases htail)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv
            (left.2 * finiteProductHaarMono blockCount left.1)
            alias.2 (coefficientSum aliases))

/-- **Functional constant-alias theorem.**  At finite-product Haar level, a
right polynomial all of whose exponent lists are zero acts by its raw
coefficient sum.  No raw equality with `polyConst` is asserted. -/
theorem finiteProductHaar_polyMul_allZero_right
    (blockCount : Nat) : ∀ (factor aliases : RatPoly),
    AllZeroExponentTerms aliases →
      finiteProductHaar blockCount (polyMul factor aliases) ≈
        finiteProductHaar blockCount factor * coefficientSum aliases
  | [], aliases, _ => Q'.eqv_symm
      (Q'.zero_mul_eqv (coefficientSum aliases))
  | left :: tail, aliases, hall => by
      change
        finiteProductHaar blockCount
              (leftTermProduct left aliases ++ polyMul tail aliases) ≈
          (left.2 * finiteProductHaarMono blockCount left.1 +
              finiteProductHaar blockCount tail) *
            coefficientSum aliases
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount (leftTermProduct left aliases) +
          finiteProductHaar blockCount (polyMul tail aliases)) _ ?_ ?_
      · exact finiteProductHaar_append blockCount _ _
      · refine Q'.eqv_trans _
          ((left.2 * finiteProductHaarMono blockCount left.1) *
                coefficientSum aliases +
            finiteProductHaar blockCount tail * coefficientSum aliases) _
          (q_add_congr
            (finiteProductHaar_leftTermProduct_allZero
              blockCount left aliases hall)
            (finiteProductHaar_polyMul_allZero_right
              blockCount tail aliases hall)) ?_
        exact Q'.eqv_symm
          (Q'.add_mul_eqv
            (left.2 * finiteProductHaarMono blockCount left.1)
            (finiteProductHaar blockCount tail)
            (coefficientSum aliases))

/-! ## 2. Polynomials supported on one selected quaternion block -/

private theorem exponentAt_varMono (source coordinate : Nat) :
    exponentAt (varMono source) coordinate =
      if coordinate = source then 1 else 0 := by
  induction source generalizing coordinate with
  | zero =>
      cases coordinate <;> rfl
  | succ source ih =>
      have hvar : varMono (source + 1) = 0 :: varMono source := by
        unfold varMono
        rw [List.replicate_succ]
        rfl
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          rw [hvar]
          simpa only [exponentAt, List.getD,
            List.getElem?_cons_succ, Nat.add_one_inj]
            using ih coordinate

private theorem allZero_of_exponentAt_eq_zero
    (monomial : List Nat)
    (hzero : ∀ coordinate, exponentAt monomial coordinate = 0) :
    allZero monomial = true := by
  induction monomial with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head = 0 := by
        simpa [exponentAt] using hzero 0
      have htail : ∀ coordinate, exponentAt tail coordinate = 0 := by
        intro coordinate
        simpa [exponentAt] using hzero (coordinate + 1)
      simpa [hhead] using ih htail

/-- Every monomial occurrence is supported on the four coordinates belonging
to `block`.  Trailing zero entries are allowed. -/
def QuaternionBlockLocal
    (block : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → ∀ coordinate,
    ¬ coordinateInQuaternionBlock block coordinate →
      exponentAt term.1 coordinate = 0

def ComplexQuaternionBlockLocal
    (block : Nat) (value : ComplexRatPoly) : Prop :=
  QuaternionBlockLocal block value.1 ∧
    QuaternionBlockLocal block value.2

private theorem mem_polyMul
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

private theorem quaternionBlockLocal_polyVar
    (block : Nat) (component : Fin 4) :
    QuaternionBlockLocal block
      (polyVar (4 * block + component.val)) := by
  intro term hterm coordinate hout
  simp only [polyVar, List.mem_singleton] at hterm
  subst term
  rw [exponentAt_varMono]
  have hne : coordinate ≠ 4 * block + component.val := by
    intro heq
    apply hout
    rw [heq]
    unfold coordinateInQuaternionBlock
    exact ⟨by omega, by omega⟩
  simp only [hne, if_false]

private theorem quaternionBlockLocal_polyAdd
    {block : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockLocal block left)
    (hright : QuaternionBlockLocal block right) :
    QuaternionBlockLocal block (polyAdd left right) := by
  intro term hterm coordinate hout
  simp only [polyAdd, List.mem_append] at hterm
  cases hterm with
  | inl hterm => exact hleft term hterm coordinate hout
  | inr hterm => exact hright term hterm coordinate hout

private theorem quaternionBlockLocal_polyNeg
    {block : Nat} {polynomial : RatPoly}
    (hlocal : QuaternionBlockLocal block polynomial) :
    QuaternionBlockLocal block (polyNeg polynomial) := by
  intro term hterm coordinate hout
  unfold polyNeg at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hlocal source hsource coordinate hout

private theorem quaternionBlockLocal_polyMul
    {block : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockLocal block left)
    (hright : QuaternionBlockLocal block right) :
    QuaternionBlockLocal block (polyMul left right) := by
  intro term hterm coordinate hout
  obtain ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, rfl⟩ :=
    mem_polyMul hterm
  rw [exponentAt_monoMul,
    hleft leftTerm hleftTerm coordinate hout,
    hright rightTerm hrightTerm coordinate hout]

private theorem complexQuaternionBlockLocal_conj
    {block : Nat} {value : ComplexRatPoly}
    (hlocal : ComplexQuaternionBlockLocal block value) :
    ComplexQuaternionBlockLocal block (complexRatPolyConj value) := by
  exact ⟨hlocal.1, quaternionBlockLocal_polyNeg hlocal.2⟩

/-- Block-local honest complex polynomials are closed under raw complex
multiplication.  This public closure is the locality API used by higher-valent
link factors assembled from already-local contractions. -/
theorem complexQuaternionBlockLocal_mul
    {block : Nat} {left right : ComplexRatPoly}
    (hleft : ComplexQuaternionBlockLocal block left)
    (hright : ComplexQuaternionBlockLocal block right) :
    ComplexQuaternionBlockLocal block (complexRatPolyMul left right) := by
  constructor
  · exact quaternionBlockLocal_polyAdd
      (quaternionBlockLocal_polyMul hleft.1 hright.1)
      (quaternionBlockLocal_polyNeg
        (quaternionBlockLocal_polyMul hleft.2 hright.2))
  · exact quaternionBlockLocal_polyAdd
      (quaternionBlockLocal_polyMul hleft.1 hright.2)
      (quaternionBlockLocal_polyMul hleft.2 hright.1)

private theorem complexQuaternionBlockLocal_forwardFundamentalCoefficient
    (block : Nat) (row column : Bool) :
    ComplexQuaternionBlockLocal block
      (forwardFundamentalCoefficient block row column) := by
  have h0 : QuaternionBlockLocal block (polyVar (4 * block)) := by
    simpa using quaternionBlockLocal_polyVar block (⟨0, by omega⟩ : Fin 4)
  have h1 : QuaternionBlockLocal block (polyVar (4 * block + 1)) :=
    quaternionBlockLocal_polyVar block (⟨1, by omega⟩ : Fin 4)
  have h2 : QuaternionBlockLocal block (polyVar (4 * block + 2)) :=
    quaternionBlockLocal_polyVar block (⟨2, by omega⟩ : Fin 4)
  have h3 : QuaternionBlockLocal block (polyVar (4 * block + 3)) :=
    quaternionBlockLocal_polyVar block (⟨3, by omega⟩ : Fin 4)
  cases row <;> cases column
  · exact ⟨h0, h1⟩
  · exact ⟨h2, h3⟩
  · exact ⟨quaternionBlockLocal_polyNeg h2, h3⟩
  · exact ⟨h0, quaternionBlockLocal_polyNeg h1⟩

private theorem complexQuaternionBlockLocal_reverseFundamentalCoefficient
    (block : Nat) (row column : Bool) :
    ComplexQuaternionBlockLocal block
      (reverseFundamentalCoefficient block row column) := by
  exact complexQuaternionBlockLocal_conj
    (complexQuaternionBlockLocal_forwardFundamentalCoefficient
      block column row)

theorem complexQuaternionBlockLocal_orientedFundamentalLinkContraction
    (block : Nat)
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    ComplexQuaternionBlockLocal block
      (orientedFundamentalLinkContraction block
        forwardRow forwardColumn reverseRow reverseColumn) := by
  exact complexQuaternionBlockLocal_mul
    (complexQuaternionBlockLocal_forwardFundamentalCoefficient
      block forwardRow forwardColumn)
    (complexQuaternionBlockLocal_reverseFundamentalCoefficient
      block reverseRow reverseColumn)

/-- Clearing the selected block turns a block-local polynomial into a
collection of honest all-zero exponent aliases. -/
theorem integrateQuaternionBlock_allZero_of_local
    (block : Nat) {polynomial : RatPoly}
    (hlocal : QuaternionBlockLocal block polynomial) :
    AllZeroExponentTerms
      (integrateQuaternionBlock block polynomial) := by
  intro term hterm
  unfold integrateQuaternionBlock at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  unfold integrateQuaternionBlockTerm
  apply allZero_of_exponentAt_eq_zero
  intro coordinate
  rw [exponentAt_clearQuaternionBlock]
  by_cases hins : coordinateInQuaternionBlock block coordinate
  · simp only [hins, if_true]
  · simp only [hins, if_false]
    exact hlocal source hsource coordinate hins

theorem integrateQuaternionBlockComplex_allZero_of_local
    (block : Nat) {value : ComplexRatPoly}
    (hlocal : ComplexQuaternionBlockLocal block value) :
    AllZeroExponentTerms
        (integrateQuaternionBlockComplex block value).1 ∧
      AllZeroExponentTerms
        (integrateQuaternionBlockComplex block value).2 := by
  exact ⟨integrateQuaternionBlock_allZero_of_local block hlocal.1,
    integrateQuaternionBlock_allZero_of_local block hlocal.2⟩

/-! ## 3. Arbitrary-block covariance and partial Schur value -/

private theorem exponentAt_blockVariable
    (block : Nat) (component query : Fin 4) :
    exponentAt (varMono (4 * block + component.val))
        (4 * block + query.val) =
      if component.val = query.val then 1 else 0 := by
  rw [exponentAt_varMono]
  by_cases hval : component.val = query.val
  · have hcoordinate :
        4 * block + query.val = 4 * block + component.val := by omega
    simp only [hcoordinate, hval, if_true]
  · have hcoordinate :
        4 * block + query.val ≠ 4 * block + component.val := by omega
    simp only [hcoordinate, hval, if_false]

/-- The closed four-by-four coordinate covariance calculation, stated only
with natural component codes.  Keeping bound proofs out of the conclusion is
what makes the finite decision proof independent of `Fin` proof fields. -/
theorem sphereMoment4_blockCoordinateCovarianceNat
    (left right : Nat) (hleftBound : left < 4) (hrightBound : right < 4) :
    sphereMoment4
        ((if left = 0 then 1 else 0) +
          (if right = 0 then 1 else 0))
        ((if left = 1 then 1 else 0) +
          (if right = 1 then 1 else 0))
        ((if left = 2 then 1 else 0) +
          (if right = 2 then 1 else 0))
        ((if left = 3 then 1 else 0) +
          (if right = 3 then 1 else 0)) ≈
      (if left = right then
        YMGap.Continuum.SU2PeterWeylWilsonBlock.quarter else 0) := by
  have hleft : left = 0 ∨ left = 1 ∨ left = 2 ∨ left = 3 := by omega
  have hright : right = 0 ∨ right = 1 ∨ right = 2 ∨ right = 3 := by omega
  rcases hleft with hleft | hleft | hleft | hleft <;>
    rcases hright with hright | hright | hright | hright <;>
      subst left <;> subst right <;> clear hleftBound hrightBound <;> decide

/-- The covariance of two coordinate variables in any selected quaternion
block is the standard normalized `S^3` covariance. -/
theorem quaternionBlockMoment_blockVariablePair
    (block : Nat) (left right : Fin 4) :
    quaternionBlockMoment block
        (monoMul
          (varMono (4 * block + left.val))
          (varMono (4 * block + right.val))) ≈
      (if left.val = right.val then
        YMGap.Continuum.SU2PeterWeylWilsonBlock.quarter else 0) := by
  unfold quaternionBlockMoment
  have hl0 := exponentAt_blockVariable block left (⟨0, by omega⟩ : Fin 4)
  have hl1 := exponentAt_blockVariable block left (⟨1, by omega⟩ : Fin 4)
  have hl2 := exponentAt_blockVariable block left (⟨2, by omega⟩ : Fin 4)
  have hl3 := exponentAt_blockVariable block left (⟨3, by omega⟩ : Fin 4)
  have hr0 := exponentAt_blockVariable block right (⟨0, by omega⟩ : Fin 4)
  have hr1 := exponentAt_blockVariable block right (⟨1, by omega⟩ : Fin 4)
  have hr2 := exponentAt_blockVariable block right (⟨2, by omega⟩ : Fin 4)
  have hr3 := exponentAt_blockVariable block right (⟨3, by omega⟩ : Fin 4)
  have hl0' :
      exponentAt (varMono (4 * block + left.val)) (4 * block) =
        if left.val = 0 then 1 else 0 := by
    simpa only [Nat.add_zero] using hl0
  have hr0' :
      exponentAt (varMono (4 * block + right.val)) (4 * block) =
        if right.val = 0 then 1 else 0 := by
    simpa only [Nat.add_zero] using hr0
  simp only [exponentAt_monoMul,
    hl0', hl1, hl2, hl3, hr0', hr1, hr2, hr3]
  exact sphereMoment4_blockCoordinateCovarianceNat
    left.val right.val left.isLt right.isLt

/-- The scalar supplied by the selected block after constructive partial
integration, still computed from the raw list with all aliases retained. -/
def blockIntegratedCoefficientSum
    (block : Nat) (polynomial : RatPoly) : Q' :=
  coefficientSum (integrateQuaternionBlock block polynomial)

/-- The two-component coefficient sum of a partially integrated honest
complex polynomial. -/
def integratedComplexCoefficientSum
    (block : Nat) (value : ComplexRatPoly) : RationalComplex :=
  (blockIntegratedCoefficientSum block value.1,
    blockIntegratedCoefficientSum block value.2)

private theorem coefficientSum_append : ∀ left right : RatPoly,
    coefficientSum (left ++ right) ≈
      coefficientSum left + coefficientSum right
  | [], right => Q'.eqv_symm
      (YMGap.Constructive.QPoly.q_zero_add_eqv (coefficientSum right))
  | term :: tail, right => by
      change
        term.2 + coefficientSum (tail ++ right) ≈
          (term.2 + coefficientSum tail) + coefficientSum right
      exact Q'.eqv_trans _
        (term.2 + (coefficientSum tail + coefficientSum right)) _
        (Q'.add_eqv_congr_left _ _ _
          (coefficientSum_append tail right))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv term.2
            (coefficientSum tail) (coefficientSum right)))

private theorem blockIntegratedCoefficientSum_add
    (block : Nat) (left right : RatPoly) :
    blockIntegratedCoefficientSum block (polyAdd left right) ≈
      blockIntegratedCoefficientSum block left +
        blockIntegratedCoefficientSum block right := by
  change
    coefficientSum
        ((left ++ right).map (integrateQuaternionBlockTerm block)) ≈
      coefficientSum
          (left.map (integrateQuaternionBlockTerm block)) +
        coefficientSum
          (right.map (integrateQuaternionBlockTerm block))
  rw [List.map_append]
  exact coefficientSum_append _ _

private theorem blockIntegratedCoefficientSum_neg
    (block : Nat) : ∀ polynomial : RatPoly,
    blockIntegratedCoefficientSum block (polyNeg polynomial) ≈
      -(blockIntegratedCoefficientSum block polynomial)
  | [] => by
      change (0 : Q') ≈ -0
      decide
  | term :: tail => by
      change
        ((-term.2) * quaternionBlockMoment block term.1) +
              blockIntegratedCoefficientSum block (polyNeg tail) ≈
          -(term.2 * quaternionBlockMoment block term.1 +
            blockIntegratedCoefficientSum block tail)
      exact Q'.eqv_trans _
        (-(term.2 * quaternionBlockMoment block term.1) +
          -(blockIntegratedCoefficientSum block tail)) _
        (q_add_congr
          (Q'.neg_mul_eqv term.2
            (quaternionBlockMoment block term.1))
          (blockIntegratedCoefficientSum_neg block tail))
        (Q'.eqv_symm
          (Q'.neg_add_eqv
            (term.2 * quaternionBlockMoment block term.1)
            (blockIntegratedCoefficientSum block tail)))

/-- One selected-block coordinate with an explicit rational coefficient. -/
def signedBlockVariable
    (block : Nat) (component : Fin 4) (coefficient : Q') : RatPoly :=
  [(varMono (4 * block + component.val), coefficient)]

def blockCoordinateCovariance (left right : Fin 4) : Q' :=
  if left.val = right.val then
    YMGap.Continuum.SU2PeterWeylWilsonBlock.quarter else 0

private theorem blockIntegratedCoefficientSum_signedVariablePair
    (block : Nat) (left right : Fin 4)
    (leftCoefficient rightCoefficient : Q') :
    blockIntegratedCoefficientSum block
        (polyMul
          (signedBlockVariable block left leftCoefficient)
          (signedBlockVariable block right rightCoefficient)) ≈
      (leftCoefficient * rightCoefficient) *
        blockCoordinateCovariance left right := by
  change
    (leftCoefficient * rightCoefficient) *
          quaternionBlockMoment block
            (monoMul
              (varMono (4 * block + left.val))
              (varMono (4 * block + right.val))) + 0 ≈
      (leftCoefficient * rightCoefficient) *
        blockCoordinateCovariance left right
  exact Q'.eqv_trans _
    ((leftCoefficient * rightCoefficient) *
      quaternionBlockMoment block
        (monoMul
          (varMono (4 * block + left.val))
          (varMono (4 * block + right.val)))) _
    (YMGap.Constructive.QPoly.q_add_zero_eqv _)
    (Q'.mul_eqv_congr_left (leftCoefficient * rightCoefficient) _ _
      (quaternionBlockMoment_blockVariablePair block left right))

/-- Coordinate/sign data for one complex fundamental matrix coefficient. -/
structure FundamentalCoefficientDescriptor where
  realComponent : Fin 4
  realCoefficient : Q'
  imaginaryComponent : Fin 4
  imaginaryCoefficient : Q'

def fundamentalCoefficientDescriptor :
    Bool → Bool → FundamentalCoefficientDescriptor
  | false, false => ⟨⟨0, by omega⟩, 1, ⟨1, by omega⟩, 1⟩
  | false, true => ⟨⟨2, by omega⟩, 1, ⟨3, by omega⟩, 1⟩
  | true, false => ⟨⟨2, by omega⟩, -1, ⟨3, by omega⟩, 1⟩
  | true, true => ⟨⟨0, by omega⟩, 1, ⟨1, by omega⟩, -1⟩

def conjugateFundamentalCoefficientDescriptor
    (descriptor : FundamentalCoefficientDescriptor) :
    FundamentalCoefficientDescriptor :=
  ⟨descriptor.realComponent, descriptor.realCoefficient,
    descriptor.imaginaryComponent, -descriptor.imaginaryCoefficient⟩

def descriptorComplexPolynomial
    (block : Nat) (descriptor : FundamentalCoefficientDescriptor) :
    ComplexRatPoly :=
  (signedBlockVariable block descriptor.realComponent
      descriptor.realCoefficient,
    signedBlockVariable block descriptor.imaginaryComponent
      descriptor.imaginaryCoefficient)

private theorem forwardFundamentalCoefficient_eq_descriptor
    (block : Nat) (row column : Bool) :
    forwardFundamentalCoefficient block row column =
      descriptorComplexPolynomial block
        (fundamentalCoefficientDescriptor row column) := by
  cases row <;> cases column <;> rfl

private theorem reverseFundamentalCoefficient_eq_descriptor
    (block : Nat) (row column : Bool) :
    reverseFundamentalCoefficient block row column =
      descriptorComplexPolynomial block
        (conjugateFundamentalCoefficientDescriptor
          (fundamentalCoefficientDescriptor column row)) := by
  cases row <;> cases column <;> rfl

def descriptorContractionValue
    (left right : FundamentalCoefficientDescriptor) : RationalComplex :=
  ((left.realCoefficient * right.realCoefficient) *
        blockCoordinateCovariance
          left.realComponent right.realComponent +
      -((left.imaginaryCoefficient * right.imaginaryCoefficient) *
        blockCoordinateCovariance
          left.imaginaryComponent right.imaginaryComponent),
    ((left.realCoefficient * right.imaginaryCoefficient) *
        blockCoordinateCovariance
          left.realComponent right.imaginaryComponent) +
      ((left.imaginaryCoefficient * right.realCoefficient) *
        blockCoordinateCovariance
          left.imaginaryComponent right.realComponent))

private theorem integrated_descriptorContraction_coefficientSum
    (block : Nat) (left right : FundamentalCoefficientDescriptor) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (complexRatPolyMul
          (descriptorComplexPolynomial block left)
          (descriptorComplexPolynomial block right)))
      (descriptorContractionValue left right) := by
  constructor
  · refine Q'.eqv_trans _
      (blockIntegratedCoefficientSum block
          (polyMul
            (signedBlockVariable block left.realComponent
              left.realCoefficient)
            (signedBlockVariable block right.realComponent
              right.realCoefficient)) +
        blockIntegratedCoefficientSum block
          (polyNeg
            (polyMul
              (signedBlockVariable block left.imaginaryComponent
                left.imaginaryCoefficient)
              (signedBlockVariable block right.imaginaryComponent
                right.imaginaryCoefficient)))) _ ?_ ?_
    · exact blockIntegratedCoefficientSum_add block _ _
    · exact q_add_congr
        (blockIntegratedCoefficientSum_signedVariablePair
          block left.realComponent right.realComponent
          left.realCoefficient right.realCoefficient)
        (Q'.eqv_trans _
          (-(blockIntegratedCoefficientSum block
            (polyMul
              (signedBlockVariable block left.imaginaryComponent
                left.imaginaryCoefficient)
              (signedBlockVariable block right.imaginaryComponent
                right.imaginaryCoefficient)))) _
          (blockIntegratedCoefficientSum_neg block _)
          (Q'.neg_eqv_congr _ _
            (blockIntegratedCoefficientSum_signedVariablePair
              block left.imaginaryComponent right.imaginaryComponent
              left.imaginaryCoefficient right.imaginaryCoefficient)))
  · refine Q'.eqv_trans _
      (blockIntegratedCoefficientSum block
          (polyMul
            (signedBlockVariable block left.realComponent
              left.realCoefficient)
            (signedBlockVariable block right.imaginaryComponent
              right.imaginaryCoefficient)) +
        blockIntegratedCoefficientSum block
          (polyMul
            (signedBlockVariable block left.imaginaryComponent
              left.imaginaryCoefficient)
            (signedBlockVariable block right.realComponent
              right.realCoefficient))) _ ?_ ?_
    · exact blockIntegratedCoefficientSum_add block _ _
    · exact q_add_congr
        (blockIntegratedCoefficientSum_signedVariablePair
          block left.realComponent right.imaginaryComponent
          left.realCoefficient right.imaginaryCoefficient)
        (blockIntegratedCoefficientSum_signedVariablePair
          block left.imaginaryComponent right.realComponent
          left.imaginaryCoefficient right.realCoefficient)

/-- The generic-block local calculation.  It deliberately computes the
coefficient sum of the trailing-zero aliases, rather than claiming that the
partial integral is a literal constant polynomial. -/
theorem integrated_orientedFundamentalLinkContraction_coefficientSum
    (block : Nat)
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFundamentalLinkContraction block
          forwardRow forwardColumn reverseRow reverseColumn))
      (orientedFundamentalSchurDelta
        forwardRow forwardColumn reverseRow reverseColumn) := by
  let forwardDescriptor :=
    fundamentalCoefficientDescriptor forwardRow forwardColumn
  let reverseDescriptor :=
    conjugateFundamentalCoefficientDescriptor
      (fundamentalCoefficientDescriptor reverseColumn reverseRow)
  have hdescriptor : RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFundamentalLinkContraction block
          forwardRow forwardColumn reverseRow reverseColumn))
      (descriptorContractionValue forwardDescriptor reverseDescriptor) := by
    unfold orientedFundamentalLinkContraction
    rw [forwardFundamentalCoefficient_eq_descriptor,
      reverseFundamentalCoefficient_eq_descriptor]
    exact integrated_descriptorContraction_coefficientSum
      block forwardDescriptor reverseDescriptor
  have harithmetic : RationalComplexEqv
      (descriptorContractionValue forwardDescriptor reverseDescriptor)
      (orientedFundamentalSchurDelta
        forwardRow forwardColumn reverseRow reverseColumn) := by
    cases forwardRow <;> cases forwardColumn <;>
      cases reverseRow <;> cases reverseColumn <;>
        constructor <;> decide
  exact ⟨Q'.eqv_trans _ _ _ hdescriptor.1 harithmetic.1,
    Q'.eqv_trans _ _ _ hdescriptor.2 harithmetic.2⟩

/-! ## 4. Complex alias multiplication and the partial Schur theorem -/

/-- Multiplication of exact rational-complex values. -/
def rationalComplexMul
    (left right : RationalComplex) : RationalComplex :=
  (left.1 * right.1 + -(left.2 * right.2),
    left.1 * right.2 + left.2 * right.1)

private theorem rationalComplexMul_congr_right
    (left : RationalComplex) {right right' : RationalComplex}
    (hright : RationalComplexEqv right right') :
    RationalComplexEqv
      (rationalComplexMul left right)
      (rationalComplexMul left right') := by
  constructor
  · exact q_add_congr
      (q_mul_congr (Q'.eqv_refl left.1) hright.1)
      (Q'.neg_eqv_congr _ _
        (q_mul_congr (Q'.eqv_refl left.2) hright.2))
  · exact q_add_congr
      (q_mul_congr (Q'.eqv_refl left.1) hright.2)
      (q_mul_congr (Q'.eqv_refl left.2) hright.1)

/-- A complex polynomial whose two components consist only of zero-exponent
aliases multiplies, under finite-product Haar, by the rational-complex pair
of coefficient sums. -/
theorem finiteProductHaarComplex_mul_allZero_right
    (blockCount : Nat) (factor aliases : ComplexRatPoly)
    (hall : AllZeroExponentTerms aliases.1 ∧
      AllZeroExponentTerms aliases.2) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul factor aliases))
      (rationalComplexMul
        (finiteProductHaarComplex blockCount factor)
        (coefficientSum aliases.1, coefficientSum aliases.2)) := by
  constructor
  · refine Q'.eqv_trans _
      (finiteProductHaar blockCount (polyMul factor.1 aliases.1) +
        finiteProductHaar blockCount
          (polyNeg (polyMul factor.2 aliases.2))) _ ?_ ?_
    · exact finiteProductHaar_add blockCount _ _
    · refine q_add_congr
        (finiteProductHaar_polyMul_allZero_right
          blockCount factor.1 aliases.1 hall.1) ?_
      exact Q'.eqv_trans _
        (-(finiteProductHaar blockCount
          (polyMul factor.2 aliases.2))) _
        (finiteProductHaar_neg blockCount _)
        (Q'.neg_eqv_congr _ _
          (finiteProductHaar_polyMul_allZero_right
            blockCount factor.2 aliases.2 hall.2))
  · refine Q'.eqv_trans _
      (finiteProductHaar blockCount (polyMul factor.1 aliases.2) +
        finiteProductHaar blockCount (polyMul factor.2 aliases.1)) _ ?_ ?_
    · exact finiteProductHaar_add blockCount _ _
    · exact q_add_congr
        (finiteProductHaar_polyMul_allZero_right
          blockCount factor.1 aliases.2 hall.2)
        (finiteProductHaar_polyMul_allZero_right
          blockCount factor.2 aliases.1 hall.1)

/-- **Generic block-local factor reduction with a complex spectator.**  If a
factor is local to an in-range quaternion block and its exact partially
integrated coefficient sum is `value`, then an arbitrary complex spectator
independent of that block factors through the full finite-product Haar
functional.  The conclusion is setoid-level because partial integration
retains trailing-zero monomial aliases rather than a literal constant
polynomial. -/
theorem genericBlock_localFactor_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator factor : ComplexRatPoly)
    (hindependent :
      ComplexQuaternionBlockIndependent block spectator)
    (hlocal : ComplexQuaternionBlockLocal block factor)
    (value : RationalComplex)
    (hvalue : RationalComplexEqv
      (integratedComplexCoefficientSum block factor) value) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator factor))
      (rationalComplexMul
        (finiteProductHaarComplex blockCount spectator) value) := by
  let aliases := integrateQuaternionBlockComplex block factor
  have hfubini : RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator factor))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator aliases)) := by
    exact
      finiteProductHaarComplex_complexSpectator_eq_after_integrating_right
        blockCount block hblock spectator factor hindependent
  have hall : AllZeroExponentTerms aliases.1 ∧
      AllZeroExponentTerms aliases.2 := by
    exact integrateQuaternionBlockComplex_allZero_of_local block hlocal
  have halias : RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator aliases))
      (rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (coefficientSum aliases.1, coefficientSum aliases.2)) := by
    exact finiteProductHaarComplex_mul_allZero_right
      blockCount spectator aliases hall
  have hcoefficient : RationalComplexEqv
      (coefficientSum aliases.1, coefficientSum aliases.2) value := by
    simpa [aliases, integratedComplexCoefficientSum,
      blockIntegratedCoefficientSum, integrateQuaternionBlockComplex]
      using hvalue
  constructor
  · exact Q'.eqv_trans _ _ _ hfubini.1
      (Q'.eqv_trans _ _ _ halias.1
        (rationalComplexMul_congr_right
          (finiteProductHaarComplex blockCount spectator)
          hcoefficient).1)
  · exact Q'.eqv_trans _ _ _ hfubini.2
      (Q'.eqv_trans _ _ _ halias.2
        (rationalComplexMul_congr_right
          (finiteProductHaarComplex blockCount spectator)
          hcoefficient).2)

/-- **Generic-block partial fundamental Schur theorem with a complex
spectator.**  For any in-range quaternion block and any componentwise
block-independent complex spectator, the local oppositely oriented
fundamental pair may be replaced under the full finite-product Haar
functional by the exact crossed `1/2` delta.

This is the linkwise contraction API required by a finite trace network.  Its
conclusion is functional/setoid-level precisely because raw partial
integration retains trailing-zero monomial aliases. -/
theorem genericBlock_oriented_fundamental_schur_with_complex_spectator
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
      (rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedFundamentalSchurDelta
          forwardRow forwardColumn reverseRow reverseColumn)) := by
  let contraction := orientedFundamentalLinkContraction block
    forwardRow forwardColumn reverseRow reverseColumn
  let aliases := integrateQuaternionBlockComplex block contraction
  have hfubini : RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator contraction))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator aliases)) := by
    exact orientedFundamentalLinkContraction_complexSpectator_fubini
      blockCount block hblock spectator hindependent
      forwardRow forwardColumn reverseRow reverseColumn
  have hlocal : ComplexQuaternionBlockLocal block contraction := by
    exact complexQuaternionBlockLocal_orientedFundamentalLinkContraction
      block forwardRow forwardColumn reverseRow reverseColumn
  have hall : AllZeroExponentTerms aliases.1 ∧
      AllZeroExponentTerms aliases.2 := by
    exact integrateQuaternionBlockComplex_allZero_of_local block hlocal
  have halias : RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator aliases))
      (rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (coefficientSum aliases.1, coefficientSum aliases.2)) := by
    exact finiteProductHaarComplex_mul_allZero_right
      blockCount spectator aliases hall
  have hvalue : RationalComplexEqv
      (coefficientSum aliases.1, coefficientSum aliases.2)
      (orientedFundamentalSchurDelta
        forwardRow forwardColumn reverseRow reverseColumn) := by
    exact integrated_orientedFundamentalLinkContraction_coefficientSum
      block forwardRow forwardColumn reverseRow reverseColumn
  constructor
  · exact Q'.eqv_trans _ _ _ hfubini.1
      (Q'.eqv_trans _ _ _ halias.1
        (rationalComplexMul_congr_right
          (finiteProductHaarComplex blockCount spectator) hvalue).1)
  · exact Q'.eqv_trans _ _ _ hfubini.2
      (Q'.eqv_trans _ _ _ halias.2
        (rationalComplexMul_congr_right
          (finiteProductHaarComplex blockCount spectator) hvalue).2)

#print axioms finiteProductHaarMono_monoMul_right_allZero
#print axioms finiteProductHaar_polyMul_allZero_right
#print axioms exponentAt_varMono
#print axioms exponentAt_blockVariable
#print axioms sphereMoment4_blockCoordinateCovarianceNat
#print axioms quaternionBlockMoment_blockVariablePair
#print axioms integrated_orientedFundamentalLinkContraction_coefficientSum
#print axioms finiteProductHaarComplex_mul_allZero_right
#print axioms complexQuaternionBlockLocal_mul
#print axioms genericBlock_localFactor_with_complex_spectator
#print axioms genericBlock_oriented_fundamental_schur_with_complex_spectator

end YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
