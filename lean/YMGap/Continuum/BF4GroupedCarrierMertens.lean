/-
# Finite all-label regrouping for the grouped BF4 carrier

The joint positive BF4 endpoint is indexed by ordered kinetic-feature words,
whereas the compact physical endpoint is indexed by ordinary powers of one
coupled polynomial.  This file establishes the finite algebra behind their
comparison.

The key relation identifies two polynomials when every arbitrary
ten-holonomy insertion gives the same normalized Haar moment.  We prove that
this relation is a constructive commutative-semiring congruence.  It then
regroups every reflected source/target feature word into the corresponding
product of the fifteen weighted Choi atoms.

This is still the finite Mertens layer.  The cofinal located-limit theorem
identifying the full grouped packet endpoint with the abstract exponential
is the remaining analytic step.

## Axiom gate

Finite lists, exact `Q'` setoid algebra, and exact quaternion-Haar identities
only.  No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedPhysicalActionShift

namespace YMGap.Continuum.BF4GroupedCarrierMertens

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.BF4GroupedPhysicalActionShift
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Q'.invSucc_num, Q'.invSucc_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. A same-carrier Haar quotient -/

/-- Two carrier polynomials are equivalent when no arbitrary
ten-holonomy polynomial insertion distinguishes them. -/
def TenHaarCarrierEqv (left right : RatPoly) : Prop :=
  ∀ insertion : RatPoly,
    quaternionHaar 10 (polyMul insertion left) ≈
      quaternionHaar 10 (polyMul insertion right)

theorem TenHaarCarrierEqv.refl
    (polynomial : RatPoly) :
    TenHaarCarrierEqv polynomial polynomial := by
  intro insertion
  exact Q'.eqv_refl _

theorem TenHaarCarrierEqv.symm
    {left right : RatPoly}
    (h : TenHaarCarrierEqv left right) :
    TenHaarCarrierEqv right left := by
  intro insertion
  exact Q'.eqv_symm (h insertion)

theorem TenHaarCarrierEqv.trans
    {first middle last : RatPoly}
    (hfirst : TenHaarCarrierEqv first middle)
    (hlast : TenHaarCarrierEqv middle last) :
    TenHaarCarrierEqv first last := by
  intro insertion
  exact Q'.eqv_trans _ _ _
    (hfirst insertion) (hlast insertion)

/-- Coefficientwise polynomial equivalence is stronger than the carrier
Haar quotient. -/
theorem tenHaarCarrierEqv_of_termwise
    {left right : RatPoly}
    (h : RatPolyTermwiseEqv left right) :
    TenHaarCarrierEqv left right := by
  intro insertion
  exact quaternionHaar_polyMul_termwise_eqv
    10 insertion h

/-- Multiplying equivalent right factors by one common left factor remains
equivalent. -/
theorem TenHaarCarrierEqv.mul_left
    (factor : RatPoly) {left right : RatPoly}
    (h : TenHaarCarrierEqv left right) :
    TenHaarCarrierEqv
      (polyMul factor left)
      (polyMul factor right) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul (polyMul insertion factor) left)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        10 insertion factor left)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul (polyMul insertion factor) right)) _
    (h (polyMul insertion factor)) ?_
  exact quaternionHaar_polyMul_assoc
    10 insertion factor right

/-- Multiplying equivalent left factors by one common right factor remains
equivalent. -/
theorem TenHaarCarrierEqv.mul_right
    {left right : RatPoly}
    (h : TenHaarCarrierEqv left right)
    (factor : RatPoly) :
    TenHaarCarrierEqv
      (polyMul left factor)
      (polyMul right factor) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul insertion (polyMul factor left))) _
    (quaternionHaar_polyMul_middle_comm
      10 insertion left factor) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul (polyMul insertion factor) left)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        10 insertion factor left)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul (polyMul insertion factor) right)) _
    (h (polyMul insertion factor)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul insertion (polyMul factor right))) _
    (quaternionHaar_polyMul_assoc
      10 insertion factor right) ?_
  exact quaternionHaar_polyMul_middle_comm
    10 insertion factor right

theorem TenHaarCarrierEqv.mul_congr
    {left left' right right' : RatPoly}
    (hleft : TenHaarCarrierEqv left left')
    (hright : TenHaarCarrierEqv right right') :
    TenHaarCarrierEqv
      (polyMul left right)
      (polyMul left' right') :=
  TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_right hleft right)
    (TenHaarCarrierEqv.mul_left left' hright)

/-- Adding one common right summand preserves carrier equivalence. -/
theorem TenHaarCarrierEqv.add_right
    {left right : RatPoly}
    (h : TenHaarCarrierEqv left right)
    (factor : RatPoly) :
    TenHaarCarrierEqv
      (polyAdd left factor)
      (polyAdd right factor) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar 10
          (polyMul insertion left) +
        quaternionHaar 10
          (polyMul insertion factor)) _
    (quaternionHaar_polyMul_add_right
      10 insertion left factor) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
          (polyMul insertion right) +
        quaternionHaar 10
          (polyMul insertion factor)) _
    (Q'.add_eqv_congr_right _ _ _
      (h insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_add_right
      10 insertion right factor)

/-- Adding one common left summand preserves carrier equivalence. -/
theorem TenHaarCarrierEqv.add_left
    (factor : RatPoly) {left right : RatPoly}
    (h : TenHaarCarrierEqv left right) :
    TenHaarCarrierEqv
      (polyAdd factor left)
      (polyAdd factor right) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar 10
          (polyMul insertion factor) +
        quaternionHaar 10
          (polyMul insertion left)) _
    (quaternionHaar_polyMul_add_right
      10 insertion factor left) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
          (polyMul insertion factor) +
        quaternionHaar 10
          (polyMul insertion right)) _
    (Q'.add_eqv_congr_left _ _ _
      (h insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_add_right
      10 insertion factor right)

theorem TenHaarCarrierEqv.add_congr
    {left left' right right' : RatPoly}
    (hleft : TenHaarCarrierEqv left left')
    (hright : TenHaarCarrierEqv right right') :
    TenHaarCarrierEqv
      (polyAdd left right)
      (polyAdd left' right') :=
  TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.add_right hleft right)
    (TenHaarCarrierEqv.add_left left' hright)

/-- Commutativity in the arbitrary-insertion Haar quotient. -/
theorem tenHaarCarrierEqv_mul_comm
    (left right : RatPoly) :
    TenHaarCarrierEqv
      (polyMul left right)
      (polyMul right left) := by
  intro insertion
  exact quaternionHaar_polyMul_middle_comm
    10 insertion left right

/-! ## 2. Termwise associativity and scalar multiplication -/

private theorem polyMul_cons_left_exact
    (first : RatTerm) (rest right : RatPoly) :
    polyMul (first :: rest) right =
      polyAdd (polyMul [first] right)
        (polyMul rest right) := by
  simp [polyMul, polyAdd]

private theorem polyMul_add_left_exact
    (left right third : RatPoly) :
    polyMul (polyAdd left right) third =
      polyAdd (polyMul left third)
        (polyMul right third) := by
  simp [polyMul, polyAdd]

private theorem polyMul_zero_right_exact :
    ∀ polynomial : RatPoly,
      polyMul polynomial polyZero = polyZero
  | [] => rfl
  | _ :: rest => by
      rw [polyMul_cons_left_exact]
      simp [polyMul, polyAdd, polyZero]

private theorem polyMul_single_cons_right_exact
    (first second : RatTerm) (rest : RatPoly) :
    polyMul [first] (second :: rest) =
      polyAdd (polyMul [first] [second])
        (polyMul [first] rest) := by
  simp [polyMul, polyAdd]

private theorem polyMul_single_add_right_exact
    (first : RatTerm) (left right : RatPoly) :
    polyMul [first] (polyAdd left right) =
      polyAdd (polyMul [first] left)
        (polyMul [first] right) := by
  simp [polyMul, polyAdd]

private theorem polySmul_add_exact
    (scale : Q') (left right : RatPoly) :
    polySmul scale (polyAdd left right) =
      polyAdd (polySmul scale left)
        (polySmul scale right) := by
  simp [polySmul, polyAdd]

private theorem termwise_assoc_row
    (first second : RatTerm) :
    ∀ rest : RatPoly,
      RatPolyTermwiseEqv
        (rest.map fun third =>
          (monoMul (monoMul first.1 second.1) third.1,
            (first.2 * second.2) * third.2))
        (rest.map fun third =>
          (monoMul first.1
              (monoMul second.1 third.1),
            first.2 * (second.2 * third.2)))
  | [] => True.intro
  | third :: rest => by
      exact
        ⟨monoMul_assoc first.1 second.1 third.1,
         Q'.mul_assoc_eqv first.2 second.2 third.2,
         termwise_assoc_row first second rest⟩

private theorem termwise_polyMul_assoc_single
    (first : RatTerm) :
    ∀ middle right : RatPoly,
      RatPolyTermwiseEqv
        (polyMul (polyMul [first] middle) right)
        (polyMul [first] (polyMul middle right))
  | [], _ => True.intro
  | second :: rest, right => by
      rw [polyMul_single_cons_right_exact
          first second rest,
        polyMul_add_left_exact
          (polyMul [first] [second])
          (polyMul [first] rest) right,
        polyMul_cons_left_exact second rest right,
        polyMul_single_add_right_exact
          first (polyMul [second] right)
          (polyMul rest right)]
      exact RatPolyTermwiseEqv.append
        (by
          simpa [polyMul, polyAdd, Function.comp_def]
            using termwise_assoc_row first second right)
        (termwise_polyMul_assoc_single first rest right)

/-- Literal multiplication is associative coefficientwise, in the exact
list order used by the carrier. -/
theorem ratPolyTermwiseEqv_polyMul_assoc :
    ∀ first second third : RatPoly,
      RatPolyTermwiseEqv
        (polyMul (polyMul first second) third)
        (polyMul first (polyMul second third))
  | [], _, _ => True.intro
  | first :: rest, second, third => by
      rw [polyMul_cons_left_exact first rest second,
        polyMul_add_left_exact
          (polyMul [first] second)
          (polyMul rest second) third,
        polyMul_cons_left_exact
          first rest (polyMul second third)]
      exact RatPolyTermwiseEqv.append
        (termwise_polyMul_assoc_single first second third)
        (ratPolyTermwiseEqv_polyMul_assoc
          rest second third)

/-- Associativity in the arbitrary-insertion Haar quotient. -/
theorem tenHaarCarrierEqv_mul_assoc
    (first second third : RatPoly) :
    TenHaarCarrierEqv
      (polyMul (polyMul first second) third)
      (polyMul first (polyMul second third)) :=
  tenHaarCarrierEqv_of_termwise
    (ratPolyTermwiseEqv_polyMul_assoc
      first second third)

private theorem termwise_smul_mul_row
    (first : RatTerm) (leftScale rightScale : Q') :
    ∀ right : RatPoly,
      RatPolyTermwiseEqv
        (right.map fun second =>
          (monoMul first.1 second.1,
            (leftScale * first.2) *
              (rightScale * second.2)))
        (right.map fun second =>
          (monoMul first.1 second.1,
            (leftScale * rightScale) *
              (first.2 * second.2)))
  | [] => True.intro
  | second :: rest => by
      exact
        ⟨rfl, by q_ring,
         termwise_smul_mul_row
          first leftScale rightScale rest⟩

/-- Two scalar polynomial factors combine coefficientwise. -/
theorem ratPolyTermwiseEqv_polyMul_smul
    (leftScale rightScale : Q') :
    ∀ left right : RatPoly,
      RatPolyTermwiseEqv
        (polyMul
          (polySmul leftScale left)
          (polySmul rightScale right))
        (polySmul (leftScale * rightScale)
          (polyMul left right))
  | [], _ => True.intro
  | first :: rest, right => by
      change
        RatPolyTermwiseEqv
          (polyMul
            ((first.1, leftScale * first.2) ::
              polySmul leftScale rest)
            (polySmul rightScale right))
          (polySmul (leftScale * rightScale)
            (polyMul (first :: rest) right))
      rw [polyMul_cons_left_exact,
        polyMul_cons_left_exact first rest right,
        polySmul_add_exact]
      exact RatPolyTermwiseEqv.append
        (by
          simpa [polyMul, polySmul, polyAdd,
            Function.comp_def]
            using termwise_smul_mul_row
              first leftScale rightScale right)
        (ratPolyTermwiseEqv_polyMul_smul
          leftScale rightScale rest right)

/-- Scalar multiplication respects exact-rational coefficient equivalence. -/
theorem tenHaarCarrierEqv_smul_coefficient
    {leftScale rightScale : Q'}
    (hscale : leftScale ≈ rightScale)
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polySmul leftScale polynomial)
      (polySmul rightScale polynomial) := by
  intro insertion
  refine Q'.eqv_trans _
    (leftScale *
      quaternionHaar 10
        (polyMul insertion polynomial)) _
    (quaternionHaar_polyMul_smul_right
      10 leftScale insertion polynomial) ?_
  refine Q'.eqv_trans _
    (rightScale *
      quaternionHaar 10
        (polyMul insertion polynomial)) _
    (Q'.mul_eqv_congr_right
      leftScale rightScale _ hscale) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_smul_right
      10 rightScale insertion polynomial)

/-- Scalar multiplication preserves carrier equivalence. -/
theorem TenHaarCarrierEqv.smul
    (scale : Q') {left right : RatPoly}
    (h : TenHaarCarrierEqv left right) :
    TenHaarCarrierEqv
      (polySmul scale left)
      (polySmul scale right) := by
  intro insertion
  refine Q'.eqv_trans _
    (scale *
      quaternionHaar 10
        (polyMul insertion left)) _
    (quaternionHaar_polyMul_smul_right
      10 scale insertion left) ?_
  refine Q'.eqv_trans _
    (scale *
      quaternionHaar 10
        (polyMul insertion right)) _
    (Q'.mul_eqv_congr_left scale _ _
      (h insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_smul_right
      10 scale insertion right)

private theorem termwise_smul_assoc :
    ∀ (firstScale secondScale : Q')
      (polynomial : RatPoly),
      RatPolyTermwiseEqv
        (polySmul firstScale
          (polySmul secondScale polynomial))
        (polySmul (firstScale * secondScale)
          polynomial)
  | _, _, [] => True.intro
  | firstScale, secondScale, term :: rest => by
      exact
        ⟨rfl,
         Q'.eqv_symm
          (Q'.mul_assoc_eqv
            firstScale secondScale term.2),
         termwise_smul_assoc
          firstScale secondScale rest⟩

theorem tenHaarCarrierEqv_smul_assoc
    (firstScale secondScale : Q')
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polySmul firstScale
        (polySmul secondScale polynomial))
      (polySmul (firstScale * secondScale)
        polynomial) :=
  tenHaarCarrierEqv_of_termwise
    (termwise_smul_assoc
      firstScale secondScale polynomial)

theorem tenHaarCarrierEqv_smul_one
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polySmul 1 polynomial) polynomial := by
  intro insertion
  refine Q'.eqv_trans _
    ((1 : Q') *
      quaternionHaar 10
        (polyMul insertion polynomial)) _
    (quaternionHaar_polyMul_smul_right
      10 1 insertion polynomial) ?_
  exact Q'.one_mul_eqv _

/-- A scalar on a left polynomial factor may be pulled onto the complete
product in the carrier quotient. -/
theorem tenHaarCarrierEqv_polyMul_smul_left
    (scale : Q') (left right : RatPoly) :
    TenHaarCarrierEqv
      (polyMul (polySmul scale left) right)
      (polySmul scale (polyMul left right)) := by
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_left
      (polySmul scale left)
      (TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_smul_one right))) ?_
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_of_termwise
      (ratPolyTermwiseEqv_polyMul_smul
        scale 1 left right)) ?_
  exact tenHaarCarrierEqv_smul_coefficient
    (Q'.mul_one_eqv scale)
    (polyMul left right)

/-- A scalar on a right polynomial factor may likewise be pulled onto the
complete product in the commutative ten-Haar carrier. -/
theorem tenHaarCarrierEqv_polyMul_smul_right
    (scale : Q') (left right : RatPoly) :
    TenHaarCarrierEqv
      (polyMul left (polySmul scale right))
      (polySmul scale (polyMul left right)) :=
  TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_mul_comm
      left (polySmul scale right))
    (TenHaarCarrierEqv.trans
      (tenHaarCarrierEqv_polyMul_smul_left
        scale right left)
      (TenHaarCarrierEqv.smul scale
        (tenHaarCarrierEqv_mul_comm right left)))

/-- Right distributivity in the commutative ten-Haar carrier. -/
theorem tenHaarCarrierEqv_polyMul_add_right
    (factor left right : RatPoly) :
    TenHaarCarrierEqv
      (polyMul factor (polyAdd left right))
      (polyAdd
        (polyMul factor left)
        (polyMul factor right)) := by
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_mul_comm
      factor (polyAdd left right)) ?_
  rw [polyMul_add_left_exact]
  exact TenHaarCarrierEqv.add_congr
    (tenHaarCarrierEqv_mul_comm left factor)
    (tenHaarCarrierEqv_mul_comm right factor)

theorem tenHaarCarrierEqv_mul_one
    (polynomial : RatPoly) :
    TenHaarCarrierEqv
      (polyMul polynomial polyOne)
      polynomial := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul
        (polyMul insertion polynomial)
        polyOne)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        10 insertion polynomial polyOne)) ?_
  exact quaternionHaar_polyMul_one_right
    10 (polyMul insertion polynomial)

/-- Four-factor Fubini regrouping inside every arbitrary insertion. -/
theorem tenHaarCarrierEqv_four_swap
    (first second third fourth : RatPoly) :
    TenHaarCarrierEqv
      (polyMul (polyMul first second)
        (polyMul third fourth))
      (polyMul (polyMul first third)
        (polyMul second fourth)) := by
  refine TenHaarCarrierEqv.trans
    (tenHaarCarrierEqv_mul_assoc
      first second (polyMul third fourth)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_left first
      (TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_mul_assoc
          second third fourth))) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_left first
      (TenHaarCarrierEqv.mul_right
        (tenHaarCarrierEqv_mul_comm
          second third)
        fourth)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.mul_left first
      (tenHaarCarrierEqv_mul_assoc
        third second fourth)) ?_
  exact TenHaarCarrierEqv.symm
    (tenHaarCarrierEqv_mul_assoc
      first third (polyMul second fourth))

/-! ## 3. Reflected source/target feature words -/

/-- One unweighted reflected feature pair. -/
def groupedKineticCrossUnweightedAtom
    (feature : BF4KineticFeature) : RatPoly :=
  polyMul
    (sourceKineticFeaturePolynomial feature)
    (targetKineticFeaturePolynomial feature)

/-- Product of unweighted reflected pairs along an ordered word. -/
def groupedKineticCrossUnweightedWordProduct :
    List BF4KineticFeature → RatPoly
  | [] => polyOne
  | feature :: rest =>
      polyMul
        (groupedKineticCrossUnweightedAtom feature)
        (groupedKineticCrossUnweightedWordProduct rest)

/-- Pair the complete source feature word with its reflected target word. -/
def bf4SeparatedReflectedKineticWordPolynomial
    (word : List BF4KineticFeature) : RatPoly :=
  polySmul (bf4FeatureWordWeight word)
    (polyMul
      (sourceFeatureWordPolynomial word)
      (targetFeatureWordPolynomial word))

/-- Source-word times target-word regroups into the product of paired atoms
inside every arbitrary ten-Haar insertion. -/
theorem sourceTargetFeatureWord_eqv_unweightedAtoms :
    ∀ word : List BF4KineticFeature,
      TenHaarCarrierEqv
        (polyMul
          (sourceFeatureWordPolynomial word)
          (targetFeatureWordPolynomial word))
        (groupedKineticCrossUnweightedWordProduct word)
  | [] => by
      change
        TenHaarCarrierEqv
          (polyMul polyOne polyOne) polyOne
      exact tenHaarCarrierEqv_mul_one polyOne
  | feature :: rest => by
      change
        TenHaarCarrierEqv
          (polyMul
            (polyMul
              (sourceKineticFeaturePolynomial feature)
              (sourceFeatureWordPolynomial rest))
            (polyMul
              (targetKineticFeaturePolynomial feature)
              (targetFeatureWordPolynomial rest)))
          (polyMul
            (groupedKineticCrossUnweightedAtom feature)
            (groupedKineticCrossUnweightedWordProduct rest))
      refine TenHaarCarrierEqv.trans
        (tenHaarCarrierEqv_four_swap
          (sourceKineticFeaturePolynomial feature)
          (sourceFeatureWordPolynomial rest)
          (targetKineticFeaturePolynomial feature)
          (targetFeatureWordPolynomial rest)) ?_
      exact TenHaarCarrierEqv.mul_left
        (groupedKineticCrossUnweightedAtom feature)
        (sourceTargetFeatureWord_eqv_unweightedAtoms rest)

/-- The recursively weighted Choi-atom word is its unweighted paired word
times the product of the physical LDL weights. -/
theorem groupedKineticCrossWordProduct_eqv_weightedUnweighted :
    ∀ word : List BF4KineticFeature,
      TenHaarCarrierEqv
        (groupedKineticCrossWordProduct word)
        (polySmul
          (bf4KineticFeatureWeightProduct word)
          (groupedKineticCrossUnweightedWordProduct word))
  | [] => by
      change
        TenHaarCarrierEqv polyOne
          (polySmul 1 polyOne)
      exact TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_smul_one polyOne)
  | feature :: rest => by
      let featureWeight :=
        bf4KineticFeatureWeight feature
      let restWeight :=
        bf4KineticFeatureWeightProduct rest
      let featurePair :=
        groupedKineticCrossUnweightedAtom feature
      let restPairs :=
        groupedKineticCrossUnweightedWordProduct rest
      change
        TenHaarCarrierEqv
          (polyMul
            (polySmul featureWeight featurePair)
            (groupedKineticCrossWordProduct rest))
          (polySmul (featureWeight * restWeight)
            (polyMul featurePair restPairs))
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.mul_left
          (polySmul featureWeight featurePair)
          (groupedKineticCrossWordProduct_eqv_weightedUnweighted
            rest)) ?_
      exact tenHaarCarrierEqv_of_termwise
        (ratPolyTermwiseEqv_polyMul_smul
          featureWeight restWeight featurePair restPairs)

/-- **One-word physical Choi regrouping.**  The literal source/target word
with its recursively defined physical coefficient is exactly the
factorially scaled product of the common weighted kinetic atoms, under every
arbitrary ten-holonomy insertion. -/
theorem bf4SeparatedReflectedKineticWord_eqv_groupedTaylor
    (word : List BF4KineticFeature) :
    TenHaarCarrierEqv
      (bf4SeparatedReflectedKineticWordPolynomial word)
      (groupedKineticCrossWordTaylorPolynomial word) := by
  let factorial := ExpNeg.termAbs 1 word.length
  let weightProduct :=
    bf4KineticFeatureWeightProduct word
  let unweighted :=
    groupedKineticCrossUnweightedWordProduct word
  let grouped := groupedKineticCrossWordProduct word
  have hsource :
      TenHaarCarrierEqv
        (bf4SeparatedReflectedKineticWordPolynomial word)
        (polySmul (bf4FeatureWordWeight word)
          unweighted) := by
    unfold bf4SeparatedReflectedKineticWordPolynomial
      unweighted
    exact TenHaarCarrierEqv.smul
      (bf4FeatureWordWeight word)
      (sourceTargetFeatureWord_eqv_unweightedAtoms word)
  have hcoefficient :
      TenHaarCarrierEqv
        (polySmul (bf4FeatureWordWeight word)
          unweighted)
        (polySmul (factorial * weightProduct)
          unweighted) :=
    tenHaarCarrierEqv_smul_coefficient
      (bf4FeatureWordWeight_eq_factorial_product word)
      unweighted
  have hgrouped :
      TenHaarCarrierEqv
        (polySmul factorial grouped)
        (polySmul (factorial * weightProduct)
          unweighted) := by
    refine TenHaarCarrierEqv.trans
      (TenHaarCarrierEqv.smul factorial
        (groupedKineticCrossWordProduct_eqv_weightedUnweighted
          word)) ?_
    exact tenHaarCarrierEqv_smul_assoc
      factorial weightProduct unweighted
  unfold groupedKineticCrossWordTaylorPolynomial
  exact TenHaarCarrierEqv.trans hsource
    (TenHaarCarrierEqv.trans hcoefficient
      (TenHaarCarrierEqv.symm hgrouped))

/-- Exact-length sum of the literal reflected source/target kinetic words
after one arbitrary carrier insertion. -/
def bf4SeparatedReflectedKineticWordsExactMoment
    (insertion : RatPoly) (length : Nat) : Q' :=
  listQSum
    (fun word =>
      quaternionHaar 10
        (polyMul insertion
          (bf4SeparatedReflectedKineticWordPolynomial
            word)))
    (bf4FeatureWordsExact length)

/-- **Finite source/target all-label Mertens theorem.**  Summing every
literal reflected physical word of exact length `n` gives the single
factorial Taylor term of the common fifteen-atom polynomial, for every
arbitrary ten-holonomy insertion. -/
theorem bf4SeparatedReflectedKineticWordsExactMoment_eq_term
    (insertion : RatPoly) (length : Nat) :
    bf4SeparatedReflectedKineticWordsExactMoment
        insertion length ≈
      quaternionHaar 10
        (polyMul insertion
          (polySmul (ExpNeg.termAbs 1 length)
            (polynomialPower
              groupedKineticCrossAtomSumPolynomial
              length))) := by
  refine Q'.eqv_trans _
    (groupedKineticCrossWordsExactTaylorMoment
      insertion length) _ ?_ ?_
  · unfold bf4SeparatedReflectedKineticWordsExactMoment
      groupedKineticCrossWordsExactTaylorMoment
    apply listQSum_congr
    intro word
    exact
      (bf4SeparatedReflectedKineticWord_eqv_groupedTaylor
        word) insertion
  · exact
      groupedKineticCrossWordsExactTaylorMoment_eq_term
        insertion length

/-! ## 4. Identification with the compiled physical kinetic cross term -/

/-- The expression compiler's literal zero polynomial. -/
def groupedCompiledZeroPolynomial : RatPoly :=
  exprToRatPoly (RingNormaliser.PolyExpr.const 0)

private theorem quaternionHaar_polyMul_groupedCompiledZero
    (insertion : RatPoly) :
    quaternionHaar 10
        (polyMul insertion groupedCompiledZeroPolynomial) ≈
      0 := by
  induction insertion with
  | nil => exact Q'.eqv_refl 0
  | cons term rest induction =>
      change
        (term.2 * 0) *
              quaternionHaarMono 10
                (monoMul term.1 []) +
            quaternionHaar 10
              (polyMul rest groupedCompiledZeroPolynomial) ≈
          0
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_zero_eqv term.2))
            (Q'.zero_mul_eqv _))
          induction
      · exact QPoly.q_zero_add_eqv 0

private theorem tenHaarCarrierEqv_zero_compiled :
    TenHaarCarrierEqv polyZero
      groupedCompiledZeroPolynomial := by
  intro insertion
  have hleft : polyMul insertion polyZero = polyZero := by
    simp [polyMul, polyZero]
  rw [hleft]
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_groupedCompiledZero
      insertion)

/-- The feature fold with the compiled final zero is exactly the atom fold
followed by that one zero term. -/
theorem groupedKineticCrossFeaturePolynomial_eq_atomSum_add_zero :
    groupedKineticCrossFeaturePolynomial =
      polyAdd groupedKineticCrossAtomSumPolynomial
        groupedCompiledZeroPolynomial := by
  decide

/-- Removing the compiler's trailing zero is invisible under every
arbitrary insertion. -/
theorem groupedKineticCrossAtomSum_eqv_featurePolynomial :
    TenHaarCarrierEqv
      groupedKineticCrossAtomSumPolynomial
      groupedKineticCrossFeaturePolynomial := by
  rw [groupedKineticCrossFeaturePolynomial_eq_atomSum_add_zero]
  have hadd :=
    TenHaarCarrierEqv.add_congr
      (TenHaarCarrierEqv.refl
        groupedKineticCrossAtomSumPolynomial)
      tenHaarCarrierEqv_zero_compiled
  change
    TenHaarCarrierEqv
      (polyAdd groupedKineticCrossAtomSumPolynomial
        polyZero)
      (polyAdd groupedKineticCrossAtomSumPolynomial
        groupedCompiledZeroPolynomial) at hadd
  simpa [polyAdd, polyZero] using hadd

/-- The enumerated fifteen-atom sum is the genuine compiled physical
source/target kinetic cross polynomial in the carrier quotient. -/
theorem groupedKineticCrossAtomSum_eqv_physical :
    TenHaarCarrierEqv
      groupedKineticCrossAtomSumPolynomial
      sourceTargetKineticCrossPolynomial :=
  TenHaarCarrierEqv.trans
    groupedKineticCrossAtomSum_eqv_featurePolynomial
    (tenHaarCarrierEqv_of_termwise
      groupedKineticCrossFeaturePolynomial_termwise)

/-- Carrier equivalence propagates through every literal polynomial power. -/
theorem TenHaarCarrierEqv.power :
    ∀ {left right : RatPoly},
      TenHaarCarrierEqv left right →
      ∀ exponent : Nat,
        TenHaarCarrierEqv
          (polynomialPower left exponent)
          (polynomialPower right exponent)
  | _, _, _, 0 => TenHaarCarrierEqv.refl polyOne
  | left, right, h, exponent + 1 => by
      change
        TenHaarCarrierEqv
          (polyMul (polynomialPower left exponent) left)
          (polyMul (polynomialPower right exponent) right)
      exact TenHaarCarrierEqv.mul_congr
        (TenHaarCarrierEqv.power h exponent)
        h

/-- Additive law for literal powers in the carrier quotient. -/
theorem tenHaarCarrierEqv_power_add
    (polynomial : RatPoly) :
    ∀ first second : Nat,
      TenHaarCarrierEqv
        (polynomialPower polynomial (first + second))
        (polyMul
          (polynomialPower polynomial first)
          (polynomialPower polynomial second))
  | first, 0 => by
      change
        TenHaarCarrierEqv
          (polynomialPower polynomial first)
          (polyMul
            (polynomialPower polynomial first)
            polyOne)
      exact TenHaarCarrierEqv.symm
        (tenHaarCarrierEqv_mul_one
          (polynomialPower polynomial first))
  | first, second + 1 => by
      rw [show first + (second + 1) =
          (first + second) + 1 by omega]
      change
        TenHaarCarrierEqv
          (polyMul
            (polynomialPower polynomial
              (first + second)) polynomial)
          (polyMul
            (polynomialPower polynomial first)
            (polyMul
              (polynomialPower polynomial second)
              polynomial))
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.mul_right
          (tenHaarCarrierEqv_power_add
            polynomial first second)
          polynomial) ?_
      exact tenHaarCarrierEqv_mul_assoc
        (polynomialPower polynomial first)
        (polynomialPower polynomial second)
        polynomial

/-- The source parity-arranged CP moment is the ordinary literal power in
the arbitrary ten-Haar carrier quotient. -/
theorem sourceDiagonalComplementMoment_eqv_power
    (exponent : Nat) :
    TenHaarCarrierEqv
      (sourceDiagonalComplementMomentPolynomial exponent)
      (polynomialPower
        sourceDiagonalComplementPolynomial exponent) := by
  let halfIndex := exponent / 2
  unfold sourceDiagonalComplementMomentPolynomial
  by_cases heven : exponent % 2 = 0
  · rw [if_pos heven]
    have hexponent :
        halfIndex + halfIndex = exponent := by
      unfold halfIndex
      omega
    change
      TenHaarCarrierEqv
        (polyMul
          (polynomialPower
            sourceDiagonalComplementPolynomial halfIndex)
          (polynomialPower
            sourceDiagonalComplementPolynomial halfIndex))
        (polynomialPower
          sourceDiagonalComplementPolynomial exponent)
    have hpower := TenHaarCarrierEqv.symm
      (tenHaarCarrierEqv_power_add
        sourceDiagonalComplementPolynomial
        halfIndex halfIndex)
    rw [hexponent] at hpower
    exact hpower
  · rw [if_neg heven]
    have hodd : exponent % 2 = 1 := by
      have hlt : exponent % 2 < 2 :=
        Nat.mod_lt exponent (by decide)
      omega
    have hexponent :
        halfIndex + halfIndex + 1 = exponent := by
      unfold halfIndex
      omega
    change
      TenHaarCarrierEqv
        (polyMul
          (polyMul
            (polynomialPower
              sourceDiagonalComplementPolynomial halfIndex)
            (polynomialPower
              sourceDiagonalComplementPolynomial halfIndex))
          sourceDiagonalComplementPolynomial)
        (polynomialPower
          sourceDiagonalComplementPolynomial exponent)
    have hpower :=
      TenHaarCarrierEqv.mul_right
        (TenHaarCarrierEqv.symm
          (tenHaarCarrierEqv_power_add
            sourceDiagonalComplementPolynomial
            halfIndex halfIndex))
        sourceDiagonalComplementPolynomial
    change
      TenHaarCarrierEqv
        (polyMul
          (polyMul
            (polynomialPower
              sourceDiagonalComplementPolynomial halfIndex)
            (polynomialPower
              sourceDiagonalComplementPolynomial halfIndex))
          sourceDiagonalComplementPolynomial)
        (polynomialPower
          sourceDiagonalComplementPolynomial
          (halfIndex + halfIndex + 1)) at hpower
    rw [hexponent] at hpower
    exact hpower

/-- Generic ordinary positive Taylor partial for one carrier polynomial. -/
def positivePolynomialTaylorPartial
    (polynomial : RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | order + 1 =>
      polyAdd
        (positivePolynomialTaylorPartial polynomial order)
        (polySmul (ExpNeg.termAbs 1 order)
          (polynomialPower polynomial order))

/-- Each source CP-preserving diagonal Taylor term is its ordinary Taylor
term in the same arbitrary-insertion carrier quotient. -/
theorem sourceDiagonalShiftedTerm_eqv_ordinary
    (exponent : Nat) :
    TenHaarCarrierEqv
      (sourceDiagonalShiftedTerm exponent)
      (polySmul (ExpNeg.termAbs 1 exponent)
        (polynomialPower
          sourceDiagonalComplementPolynomial exponent)) :=
  TenHaarCarrierEqv.smul
    (ExpNeg.termAbs 1 exponent)
    (sourceDiagonalComplementMoment_eqv_power exponent)

/-- The complete one-sided CP-preserving diagonal partial is the ordinary
positive exponential partial in the carrier quotient. -/
theorem sourceDiagonalFeynmanKacPartial_eqv_ordinary :
    ∀ order : Nat,
      TenHaarCarrierEqv
        (sourceDiagonalFeynmanKacPartial order)
        (positivePolynomialTaylorPartial
          sourceDiagonalComplementPolynomial order)
  | 0 => TenHaarCarrierEqv.refl polyZero
  | order + 1 => by
      change
        TenHaarCarrierEqv
          (polyAdd
            (sourceDiagonalFeynmanKacPartial order)
            (sourceDiagonalShiftedTerm order))
          (polyAdd
            (positivePolynomialTaylorPartial
              sourceDiagonalComplementPolynomial order)
            (polySmul (ExpNeg.termAbs 1 order)
              (polynomialPower
                sourceDiagonalComplementPolynomial order)))
      exact TenHaarCarrierEqv.add_congr
        (sourceDiagonalFeynmanKacPartial_eqv_ordinary
          order)
        (sourceDiagonalShiftedTerm_eqv_ordinary order)

/-! ## 4a. Reflection preserves the polynomial algebra -/

private theorem monoMul_shift_both
    (offset : Nat) (left right : List Nat) :
    monoMul
        (List.replicate offset 0 ++ left)
        (List.replicate offset 0 ++ right) =
      List.replicate offset 0 ++ monoMul left right := by
  induction offset with
  | zero => rfl
  | succ offset induction =>
      simp only [List.replicate_succ, List.cons_append,
        monoMul, Nat.zero_add, induction]

theorem shiftPolynomial_polyAdd_exact
    (offset : Nat) (left right : RatPoly) :
    shiftPolynomial offset (polyAdd left right) =
      polyAdd
        (shiftPolynomial offset left)
        (shiftPolynomial offset right) := by
  simp [shiftPolynomial, polyAdd]

theorem shiftPolynomial_polySmul_exact
    (offset : Nat) (scale : Q') (polynomial : RatPoly) :
    shiftPolynomial offset (polySmul scale polynomial) =
      polySmul scale
        (shiftPolynomial offset polynomial) := by
  simp [shiftPolynomial, polySmul]

private theorem shiftPolynomial_polyMul_single_exact
    (offset : Nat) (first : RatTerm) (right : RatPoly) :
    shiftPolynomial offset (polyMul [first] right) =
      polyMul
        (shiftPolynomial offset [first])
        (shiftPolynomial offset right) := by
  simp [shiftPolynomial, polyMul,
    monoMul_shift_both, Function.comp_def]

/-- Reflection is an exact homomorphism for the literal polynomial product.
The equality includes list order, not only evaluation. -/
theorem shiftPolynomial_polyMul_exact
    (offset : Nat) :
    ∀ left right : RatPoly,
      shiftPolynomial offset (polyMul left right) =
        polyMul
          (shiftPolynomial offset left)
          (shiftPolynomial offset right)
  | [], _ => rfl
  | first :: rest, right => by
      rw [polyMul_cons_left_exact first rest right,
        shiftPolynomial_polyAdd_exact,
        shiftPolynomial_polyMul_single_exact,
        shiftPolynomial_polyMul_exact offset rest right]
      change
        polyAdd
            (polyMul
              (shiftPolynomial offset [first])
              (shiftPolynomial offset right))
            (polyMul
              (shiftPolynomial offset rest)
              (shiftPolynomial offset right)) =
          polyMul
            ((List.replicate offset 0 ++ first.1,
                first.2) ::
              shiftPolynomial offset rest)
            (shiftPolynomial offset right)
      rw [polyMul_cons_left_exact]
      rfl

private theorem exponentAt_drop_local
    (monomial : List Nat) :
    ∀ offset index : Nat,
      exponentAt (monomial.drop offset) index =
        exponentAt monomial (offset + index)
  | 0, index => by simp [exponentAt]
  | offset + 1, index => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons exponent rest =>
          have hindex :
              offset + 1 + index =
                (offset + index) + 1 := by omega
          rw [hindex]
          simp only [List.drop_succ_cons]
          unfold exponentAt
          simp only [List.getD_cons_succ]
          exact exponentAt_drop_local rest offset index

private theorem exponentAt_monoMul_local
    (left right : List Nat) (index : Nat) :
    exponentAt (monoMul left right) index =
      exponentAt left index + exponentAt right index := by
  induction left generalizing right index with
  | nil => simp [monoMul, exponentAt]
  | cons x xs induction =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases index with
          | zero => simp [monoMul, exponentAt]
          | succ index =>
              change exponentAt (monoMul xs ys) index =
                exponentAt xs index + exponentAt ys index
              exact induction ys index

private theorem exponentAt_replicate_zero
    (offset index : Nat) :
    exponentAt (List.replicate offset 0) index = 0 := by
  induction offset generalizing index with
  | zero => simp [exponentAt]
  | succ offset induction =>
      cases index with
      | zero => simp [exponentAt]
      | succ index =>
          simpa [exponentAt] using induction index

private theorem monoMul_drop_of_right_length_le
    (left right : List Nat) (coordinates : Nat)
    (hright : right.length ≤ coordinates) :
    (monoMul left right).drop coordinates =
      left.drop coordinates := by
  induction coordinates generalizing left right with
  | zero =>
      cases right with
      | nil => cases left <;> rfl
      | cons y ys => simp at hright
  | succ coordinates induction =>
      cases left with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le hright
      | cons x xs =>
          cases right with
          | nil => simp [monoMul]
          | cons y ys =>
              simp only [List.length_cons] at hright
              simp [monoMul,
                induction xs ys (by omega)]

private theorem quaternionHaarPrefix_congr_exponents
    (blocks : Nat) :
    ∀ left right : List Nat,
      (∀ index,
        exponentAt left index =
          exponentAt right index) →
      quaternionHaarPrefix blocks left ≈
        quaternionHaarPrefix blocks right := by
  intro left right hexponents
  induction blocks generalizing left right with
  | zero => exact Q'.eqv_refl 1
  | succ blocks induction =>
      simp only [quaternionHaarPrefix]
      have hsphere :
          sphereMoment4
              (exponentAt left 0)
              (exponentAt left 1)
              (exponentAt left 2)
              (exponentAt left 3) =
            sphereMoment4
              (exponentAt right 0)
              (exponentAt right 1)
              (exponentAt right 2)
              (exponentAt right 3) := by
        rw [hexponents 0, hexponents 1,
          hexponents 2, hexponents 3]
      rw [hsphere]
      exact Q'.mul_eqv_congr_left _ _ _
        (induction (left.drop 4) (right.drop 4)
          (fun index => by
            rw [exponentAt_drop_local,
              exponentAt_drop_local]
            exact hexponents (4 + index)))

/-- Multiplication by an all-zero exponent vector does not change a
ten-Haar monomial moment. -/
theorem quaternionHaarMono_mul_zeroPadding
    (monomial : List Nat) (offset : Nat)
    (hoffset : offset ≤ 40) :
    quaternionHaarMono 10
        (monoMul monomial
          (List.replicate offset 0)) ≈
      quaternionHaarMono 10 monomial := by
  have hdrop :
      (monoMul monomial
          (List.replicate offset 0)).drop 40 =
        monomial.drop 40 :=
    monoMul_drop_of_right_length_le
      monomial (List.replicate offset 0) 40
      (by simp only [List.length_replicate]; exact hoffset)
  have hexponents :
      ∀ index,
        exponentAt
            (monoMul monomial
              (List.replicate offset 0)) index =
          exponentAt monomial index := by
    intro index
    rw [exponentAt_monoMul_local,
      exponentAt_replicate_zero, Nat.add_zero]
  unfold quaternionHaarMono
  rw [show 4 * 10 = 40 by decide, hdrop]
  by_cases htail :
      allZero (monomial.drop 40) = true
  · rw [if_pos htail, if_pos htail]
    exact quaternionHaarPrefix_congr_exponents
      10 _ _ hexponents
  · rw [if_neg htail, if_neg htail]
    exact Q'.eqv_refl 0

private theorem quaternionHaar_polyMul_shiftedOne_eq_self :
    ∀ insertion : RatPoly,
      quaternionHaar 10
          (polyMul insertion
            (shiftPolynomial 20 polyOne)) ≈
        quaternionHaar 10 insertion
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (term.2 * 1) *
              quaternionHaarMono 10
                (monoMul term.1
                  (List.replicate 20 0)) +
            quaternionHaar 10
              (polyMul rest
                (shiftPolynomial 20 polyOne)) ≈
          term.2 * quaternionHaarMono 10 term.1 +
            quaternionHaar 10 rest
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_one_eqv term.2))
          (Q'.mul_eqv_congr_left term.2 _ _
            (quaternionHaarMono_mul_zeroPadding
              term.1 20 (by decide))))
        (quaternionHaar_polyMul_shiftedOne_eq_self rest)

/-- The reflected polynomial unit is still the unit in the arbitrary
ten-Haar carrier quotient. -/
theorem shiftPolynomial_polyOne_eqv_one :
    TenHaarCarrierEqv
      (shiftPolynomial 20 polyOne) polyOne := by
  intro insertion
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_shiftedOne_eq_self insertion)
    (Q'.eqv_symm
      (quaternionHaar_polyMul_one_right
        10 insertion))

/-- Reflection transports literal powers to powers of the reflected
polynomial in the carrier quotient. -/
theorem shiftPolynomial_power_eqv_power_shift
    (polynomial : RatPoly) :
    ∀ exponent : Nat,
      TenHaarCarrierEqv
        (shiftPolynomial 20
          (polynomialPower polynomial exponent))
        (polynomialPower
          (shiftPolynomial 20 polynomial) exponent)
  | 0 => shiftPolynomial_polyOne_eqv_one
  | exponent + 1 => by
      change
        TenHaarCarrierEqv
          (shiftPolynomial 20
            (polyMul
              (polynomialPower polynomial exponent)
              polynomial))
          (polyMul
            (polynomialPower
              (shiftPolynomial 20 polynomial) exponent)
            (shiftPolynomial 20 polynomial))
      rw [shiftPolynomial_polyMul_exact]
      exact TenHaarCarrierEqv.mul_congr
        (shiftPolynomial_power_eqv_power_shift
          polynomial exponent)
        (TenHaarCarrierEqv.refl
          (shiftPolynomial 20 polynomial))

/-! ## 4b. Canonical padding is invisible under arbitrary insertion -/

private theorem canonicalQuaternionMonomial_exponentAt_supported
    (blocks : Nat) :
    ∀ (monomial : List Nat),
      monomial.length ≤ 4 * blocks →
      ∀ index,
        exponentAt
            (canonicalQuaternionMonomial blocks monomial)
            index =
          exponentAt monomial index := by
  induction blocks with
  | zero =>
      intro monomial hlength index
      have hnil : monomial = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      subst monomial
      simp [canonicalQuaternionMonomial, exponentAt]
  | succ blocks induction =>
      intro monomial hlength index
      cases index with
      | zero =>
          simp [canonicalQuaternionMonomial, exponentAt]
      | succ index =>
          cases index with
          | zero =>
              simp [canonicalQuaternionMonomial, exponentAt]
          | succ index =>
              cases index with
              | zero =>
                  simp [canonicalQuaternionMonomial, exponentAt]
              | succ index =>
                  cases index with
                  | zero =>
                      simp [canonicalQuaternionMonomial,
                        exponentAt]
                  | succ index =>
                      change
                        exponentAt
                            (canonicalQuaternionMonomial blocks
                              (monomial.drop 4)) index =
                          exponentAt monomial
                            (index + 4)
                      have hdropLength :
                          (monomial.drop 4).length ≤
                            4 * blocks := by
                        simp only [List.length_drop]
                        omega
                      refine Eq.trans
                        (induction (monomial.drop 4)
                          hdropLength index) ?_
                      rw [exponentAt_drop_local]
                      congr 1
                      omega

/-- Canonical padding of a supported right monomial is invisible after
multiplication by an arbitrary left monomial. -/
theorem quaternionHaarMono_mul_canonical_right
    (canonicalBlocks : Nat)
    (hblocks : 4 * canonicalBlocks ≤ 40)
    (monomial source : List Nat)
    (hsource : source.length ≤
      4 * canonicalBlocks) :
    quaternionHaarMono 10
        (monoMul monomial
          (canonicalQuaternionMonomial
            canonicalBlocks source)) ≈
      quaternionHaarMono 10
        (monoMul monomial source) := by
  have hcanonicalLength :
      (canonicalQuaternionMonomial
        canonicalBlocks source).length =
          4 * canonicalBlocks := by
    simpa using
      canonicalQuaternionMonomial_length
        canonicalBlocks source
  have hdropCanonical :
      (monoMul monomial
          (canonicalQuaternionMonomial
            canonicalBlocks source)).drop 40 =
        monomial.drop 40 :=
    monoMul_drop_of_right_length_le
      monomial
      (canonicalQuaternionMonomial
        canonicalBlocks source)
      40 (by omega)
  have hdropSource :
      (monoMul monomial source).drop 40 =
        monomial.drop 40 :=
    monoMul_drop_of_right_length_le
      monomial source 40 (Nat.le_trans hsource hblocks)
  have hcanonicalExponents :
      ∀ index,
        exponentAt
            (canonicalQuaternionMonomial
              canonicalBlocks source) index =
          exponentAt source index :=
    canonicalQuaternionMonomial_exponentAt_supported
      canonicalBlocks source hsource
  have hproductExponents :
      ∀ index,
        exponentAt
            (monoMul monomial
              (canonicalQuaternionMonomial
                canonicalBlocks source)) index =
          exponentAt (monoMul monomial source) index := by
    intro index
    rw [exponentAt_monoMul_local,
      exponentAt_monoMul_local,
      hcanonicalExponents index]
  unfold quaternionHaarMono
  rw [show 4 * 10 = 40 by decide,
    hdropCanonical, hdropSource]
  by_cases htail :
      allZero (monomial.drop 40) = true
  · rw [if_pos htail, if_pos htail]
    exact quaternionHaarPrefix_congr_exponents
      10 _ _ hproductExponents
  · rw [if_neg htail, if_neg htail]
    exact Q'.eqv_refl 0

private theorem quaternionHaar_single_mul_canonical
    (canonicalBlocks : Nat)
    (hblocks : 4 * canonicalBlocks ≤ 40)
    (insertion : RatTerm) :
    ∀ (polynomial : RatPoly),
      SupportedQuaternionBlocks
        canonicalBlocks polynomial →
      quaternionHaar 10
          (polyMul [insertion]
            (canonicalQuaternionPolynomial
              canonicalBlocks polynomial)) ≈
        quaternionHaar 10
          (polyMul [insertion] polynomial)
  | [], _ => Q'.eqv_refl 0
  | term :: rest, hsupport => by
      have hterm :
          term.1.length ≤ 4 * canonicalBlocks := by
        exact hsupport term List.mem_cons_self
      have hrest :
          SupportedQuaternionBlocks canonicalBlocks rest := by
        intro other hother
        exact hsupport other
          (List.mem_cons_of_mem term hother)
      change
        (insertion.2 * term.2) *
              quaternionHaarMono 10
                (monoMul insertion.1
                  (canonicalQuaternionMonomial
                    canonicalBlocks term.1)) +
            quaternionHaar 10
                (polyMul [insertion]
                (canonicalQuaternionPolynomial
                  canonicalBlocks rest)) ≈
          (insertion.2 * term.2) *
              quaternionHaarMono 10
                (monoMul insertion.1 term.1) +
            quaternionHaar 10
              (polyMul [insertion] rest)
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left
          (insertion.2 * term.2) _ _
          (quaternionHaarMono_mul_canonical_right
            canonicalBlocks hblocks
            insertion.1 term.1 hterm))
        (quaternionHaar_single_mul_canonical
          canonicalBlocks hblocks insertion rest hrest)

/-- Canonicalizing a supported polynomial is invisible even after every
arbitrary ten-holonomy insertion. -/
theorem canonicalQuaternionPolynomial_eqv
    (canonicalBlocks : Nat)
    (hblocks : 4 * canonicalBlocks ≤ 40)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks canonicalBlocks polynomial) :
    TenHaarCarrierEqv
      (canonicalQuaternionPolynomial
        canonicalBlocks polynomial)
      polynomial := by
  intro insertion
  induction insertion with
  | nil => exact Q'.eqv_refl 0
  | cons term rest induction =>
      rw [polyMul_cons_left_exact term rest,
        polyMul_cons_left_exact term rest]
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_append 10 _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (quaternionHaar_single_mul_canonical
              canonicalBlocks hblocks
              term polynomial hsupport)
            induction)
          (Q'.eqv_symm
            (quaternionHaar_append 10 _ _)))

/-! ## 4c. Forty-coordinate canonical termwise transport -/

/-- Two literal polynomial lists agree term-by-term after every monomial is
put in its canonical forty-coordinate quaternion form.  The explicit support
fields make this relation strong enough for multiplication by an arbitrary
ten-holonomy insertion.  Unlike `RatPolyTermwiseEqv`, it deliberately regards
`[]` and a finite all-zero exponent vector as the same constant monomial. -/
def RatPolyTenCanonicalTermwiseEqv : RatPoly → RatPoly → Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      left.1.length ≤ 40 ∧
      right.1.length ≤ 40 ∧
      canonicalQuaternionMonomial 10 left.1 =
        canonicalQuaternionMonomial 10 right.1 ∧
      left.2 ≈ right.2 ∧
      RatPolyTenCanonicalTermwiseEqv leftRest rightRest
  | _, _ => False

instance ratPolyTenCanonicalTermwiseEqvDecidable :
    ∀ left right : RatPoly,
      Decidable (RatPolyTenCanonicalTermwiseEqv left right)
  | [], [] => isTrue True.intro
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | left :: leftRest, right :: rightRest =>
      match (inferInstance : Decidable (left.1.length ≤ 40)),
          (inferInstance : Decidable (right.1.length ≤ 40)),
          decEq
            (canonicalQuaternionMonomial 10 left.1)
            (canonicalQuaternionMonomial 10 right.1),
          (inferInstance : Decidable (left.2 ≈ right.2)),
          ratPolyTenCanonicalTermwiseEqvDecidable
            leftRest rightRest with
      | isTrue hleft, isTrue hright, isTrue hcanonical,
          isTrue hcoefficient, isTrue hrest =>
          isTrue
            ⟨hleft, hright, hcanonical,
             hcoefficient, hrest⟩
      | isFalse hleft, _, _, _, _ =>
          isFalse (fun h => hleft h.1)
      | _, isFalse hright, _, _, _ =>
          isFalse (fun h => hright h.2.1)
      | _, _, isFalse hcanonical, _, _ =>
          isFalse (fun h => hcanonical h.2.2.1)
      | _, _, _, isFalse hcoefficient, _ =>
          isFalse (fun h => hcoefficient h.2.2.2.1)
      | _, _, _, _, isFalse hrest =>
          isFalse (fun h => hrest h.2.2.2.2)

private theorem quaternionHaarMono_mul_tenCanonical
    (insertion left right : List Nat)
    (hleft : left.length ≤ 40)
    (hright : right.length ≤ 40)
    (hcanonical :
      canonicalQuaternionMonomial 10 left =
        canonicalQuaternionMonomial 10 right) :
    quaternionHaarMono 10
        (monoMul insertion left) ≈
      quaternionHaarMono 10
        (monoMul insertion right) := by
  refine Q'.eqv_trans _
    (quaternionHaarMono 10
      (monoMul insertion
        (canonicalQuaternionMonomial 10 left))) _
    (Q'.eqv_symm
      (quaternionHaarMono_mul_canonical_right
        10 (by decide) insertion left hleft)) ?_
  rw [hcanonical]
  exact quaternionHaarMono_mul_canonical_right
    10 (by decide) insertion right hright

private theorem quaternionHaar_single_mul_tenCanonicalTermwise
    (insertion : RatTerm) :
    ∀ {left right : RatPoly},
      RatPolyTenCanonicalTermwiseEqv left right →
        quaternionHaar 10
            (polyMul [insertion] left) ≈
          quaternionHaar 10
            (polyMul [insertion] right)
  | [], [], _ => Q'.eqv_refl 0
  | left :: leftRest, right :: rightRest, h => by
      change
        (insertion.2 * left.2) *
              quaternionHaarMono 10
                (monoMul insertion.1 left.1) +
            quaternionHaar 10
              (polyMul [insertion] leftRest) ≈
          (insertion.2 * right.2) *
              quaternionHaarMono 10
                (monoMul insertion.1 right.1) +
            quaternionHaar 10
              (polyMul [insertion] rightRest)
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _
          ((insertion.2 * right.2) *
            quaternionHaarMono 10
              (monoMul insertion.1 left.1)) _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left
              insertion.2 left.2 right.2 h.2.2.2.1))
          (Q'.mul_eqv_congr_left _ _ _
            (quaternionHaarMono_mul_tenCanonical
              insertion.1 left.1 right.1
              h.1 h.2.1 h.2.2.1)))
        (quaternionHaar_single_mul_tenCanonicalTermwise
          insertion h.2.2.2.2)

/-- Canonical forty-coordinate termwise agreement is consumable under every
arbitrary ten-Haar insertion. -/
theorem tenHaarCarrierEqv_of_tenCanonicalTermwise
    {left right : RatPoly}
    (h : RatPolyTenCanonicalTermwiseEqv left right) :
    TenHaarCarrierEqv left right := by
  intro insertion
  induction insertion with
  | nil => exact Q'.eqv_refl 0
  | cons term rest induction =>
      rw [polyMul_cons_left_exact term rest left,
        polyMul_cons_left_exact term rest right]
      exact Q'.eqv_trans _
        (quaternionHaar 10
              (polyMul [term] left) +
            quaternionHaar 10
              (polyMul rest left)) _
        (quaternionHaar_append 10 _ _) <|
        Q'.eqv_trans _
          (quaternionHaar 10
                (polyMul [term] right) +
              quaternionHaar 10
                (polyMul rest right)) _
          (Q'.add_eqv_congr'
            (quaternionHaar_single_mul_tenCanonicalTermwise
              term h)
            induction)
          (Q'.eqv_symm
            (quaternionHaar_append 10 _ _))

/-- The separately compiled reflected target complement is exactly the
twenty-coordinate shift of the source complement in the arbitrary-insertion
Haar carrier.  Literal list equality fails only because the compiler trims
constant monomials while `shiftPolynomial` retains twenty trailing zeros. -/
theorem targetDiagonalComplement_eqv_shiftSource :
    TenHaarCarrierEqv
      targetDiagonalComplementPolynomial
      (shiftPolynomial 20
        sourceDiagonalComplementPolynomial) :=
  tenHaarCarrierEqv_of_tenCanonicalTermwise (by decide)

/-- Reflection of the parity-arranged source moment is the ordinary power
of the reflected source complement in the same ten-Haar carrier. -/
theorem shiftedSourceDiagonalComplementMoment_eqv_shiftPower
    (exponent : Nat) :
    TenHaarCarrierEqv
      (shiftPolynomial 20
        (sourceDiagonalComplementMomentPolynomial exponent))
      (polynomialPower
        (shiftPolynomial 20
          sourceDiagonalComplementPolynomial)
        exponent) := by
  let halfIndex := exponent / 2
  unfold sourceDiagonalComplementMomentPolynomial
  by_cases heven : exponent % 2 = 0
  · rw [if_pos heven, shiftPolynomial_polyMul_exact]
    have hexponent :
        halfIndex + halfIndex = exponent := by
      unfold halfIndex
      omega
    refine TenHaarCarrierEqv.trans
      (TenHaarCarrierEqv.mul_congr
        (shiftPolynomial_power_eqv_power_shift
          sourceDiagonalComplementPolynomial halfIndex)
        (shiftPolynomial_power_eqv_power_shift
          sourceDiagonalComplementPolynomial halfIndex)) ?_
    have hpower := TenHaarCarrierEqv.symm
      (tenHaarCarrierEqv_power_add
        (shiftPolynomial 20
          sourceDiagonalComplementPolynomial)
        halfIndex halfIndex)
    rw [hexponent] at hpower
    exact hpower
  · rw [if_neg heven, shiftPolynomial_polyMul_exact,
      shiftPolynomial_polyMul_exact]
    have hodd : exponent % 2 = 1 := by
      have hlt : exponent % 2 < 2 :=
        Nat.mod_lt exponent (by decide)
      omega
    have hexponent :
        halfIndex + halfIndex + 1 = exponent := by
      unfold halfIndex
      omega
    have hpair :
        TenHaarCarrierEqv
          (polyMul
            (shiftPolynomial 20
              (polynomialPower
                sourceDiagonalComplementPolynomial halfIndex))
            (shiftPolynomial 20
              (polynomialPower
                sourceDiagonalComplementPolynomial halfIndex)))
          (polynomialPower
            (shiftPolynomial 20
              sourceDiagonalComplementPolynomial)
            (halfIndex + halfIndex)) :=
      TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.mul_congr
          (shiftPolynomial_power_eqv_power_shift
            sourceDiagonalComplementPolynomial halfIndex)
          (shiftPolynomial_power_eqv_power_shift
            sourceDiagonalComplementPolynomial halfIndex))
        (TenHaarCarrierEqv.symm
          (tenHaarCarrierEqv_power_add
            (shiftPolynomial 20
              sourceDiagonalComplementPolynomial)
            halfIndex halfIndex))
    have hfull := TenHaarCarrierEqv.mul_right hpair
      (shiftPolynomial 20
        sourceDiagonalComplementPolynomial)
    change
      TenHaarCarrierEqv
        (polyMul
          (polyMul
            (shiftPolynomial 20
              (polynomialPower
                sourceDiagonalComplementPolynomial halfIndex))
            (shiftPolynomial 20
              (polynomialPower
                sourceDiagonalComplementPolynomial halfIndex)))
          (shiftPolynomial 20
            sourceDiagonalComplementPolynomial))
        (polynomialPower
          (shiftPolynomial 20
            sourceDiagonalComplementPolynomial)
          (halfIndex + halfIndex + 1)) at hfull
    rw [hexponent] at hfull
    exact hfull

/-- The reflected source moment is therefore the ordinary power of the
genuinely compiled target complement, not merely of a formal shifted copy. -/
theorem shiftedSourceDiagonalComplementMoment_eqv_targetPower
    (exponent : Nat) :
    TenHaarCarrierEqv
      (shiftPolynomial 20
        (sourceDiagonalComplementMomentPolynomial exponent))
      (polynomialPower
        targetDiagonalComplementPolynomial exponent) :=
  TenHaarCarrierEqv.trans
    (shiftedSourceDiagonalComplementMoment_eqv_shiftPower
      exponent)
    (TenHaarCarrierEqv.power
      (TenHaarCarrierEqv.symm
        targetDiagonalComplement_eqv_shiftSource)
      exponent)

/-- The reflected CP-preserving diagonal Taylor term is the corresponding
ordinary target-complement Taylor term. -/
theorem shiftedSourceDiagonalShiftedTerm_eqv_targetOrdinary
    (exponent : Nat) :
    TenHaarCarrierEqv
      (shiftPolynomial 20
        (sourceDiagonalShiftedTerm exponent))
      (polySmul (ExpNeg.termAbs 1 exponent)
        (polynomialPower
          targetDiagonalComplementPolynomial exponent)) := by
  unfold sourceDiagonalShiftedTerm
  rw [shiftPolynomial_polySmul_exact]
  exact TenHaarCarrierEqv.smul
    (ExpNeg.termAbs 1 exponent)
    (shiftedSourceDiagonalComplementMoment_eqv_targetPower
      exponent)

/-- The ordinary positive Taylor partial of the compiled reflected target
complement. -/
def targetDiagonalFeynmanKacPartial (order : Nat) : RatPoly :=
  positivePolynomialTaylorPartial
    targetDiagonalComplementPolynomial order

/-- The literal reflected source diagonal partial and the genuinely compiled
target diagonal partial agree under every arbitrary ten-Haar insertion. -/
theorem shiftedSourceDiagonalFeynmanKacPartial_eqv_target :
    ∀ order : Nat,
      TenHaarCarrierEqv
        (shiftPolynomial 20
          (sourceDiagonalFeynmanKacPartial order))
        (targetDiagonalFeynmanKacPartial order)
  | 0 => by
      change TenHaarCarrierEqv polyZero polyZero
      exact TenHaarCarrierEqv.refl polyZero
  | order + 1 => by
      change
        TenHaarCarrierEqv
          (shiftPolynomial 20
            (polyAdd
              (sourceDiagonalFeynmanKacPartial order)
              (sourceDiagonalShiftedTerm order)))
          (polyAdd
            (targetDiagonalFeynmanKacPartial order)
            (polySmul (ExpNeg.termAbs 1 order)
              (polynomialPower
                targetDiagonalComplementPolynomial order)))
      rw [shiftPolynomial_polyAdd_exact]
      exact TenHaarCarrierEqv.add_congr
        (shiftedSourceDiagonalFeynmanKacPartial_eqv_target
          order)
        (shiftedSourceDiagonalShiftedTerm_eqv_targetOrdinary
          order)

private theorem exponentAt_zeroPrefix :
    ∀ (offset : Nat) (monomial : List Nat) (index : Nat),
      exponentAt
          (List.replicate offset 0 ++ monomial) index =
        if index < offset then 0
        else exponentAt monomial (index - offset)
  | 0, monomial, index => by
      simp [exponentAt]
  | offset + 1, monomial, 0 => by
      simp [List.replicate_succ, exponentAt]
  | offset + 1, monomial, index + 1 => by
      simp only [List.replicate_succ, List.cons_append,
        exponentAt, List.getD_cons_succ,
        Nat.succ_lt_succ_iff]
      rw [show index + 1 - (offset + 1) =
          index - offset by omega]
      simpa only [exponentAt] using
        exponentAt_zeroPrefix offset monomial index

private theorem canonicalQuaternionMonomial_congr_exponents :
    ∀ (blocks : Nat) (left right : List Nat),
      (∀ index,
        exponentAt left index = exponentAt right index) →
      canonicalQuaternionMonomial blocks left =
        canonicalQuaternionMonomial blocks right
  | 0, _, _, _ => rfl
  | blocks + 1, left, right, h => by
      simp only [canonicalQuaternionMonomial]
      rw [h 0, h 1, h 2, h 3]
      exact congrArg
        (fun tail =>
          exponentAt right 0 ::
          exponentAt right 1 ::
          exponentAt right 2 ::
          exponentAt right 3 :: tail)
        (canonicalQuaternionMonomial_congr_exponents
          blocks (left.drop 4) (right.drop 4)
          (fun index => by
            rw [exponentAt_drop_local,
              exponentAt_drop_local]
            exact h (4 + index)))

private theorem shiftedCanonicalQuaternionMonomial_exponents
    (monomial : List Nat)
    (hsupport : monomial.length ≤ 20) :
    ∀ index,
      exponentAt
          (List.replicate 20 0 ++
            canonicalQuaternionMonomial 5 monomial)
          index =
        exponentAt
          (List.replicate 20 0 ++ monomial)
          index := by
  intro index
  rw [exponentAt_zeroPrefix,
    exponentAt_zeroPrefix]
  by_cases hprefix : index < 20
  · rw [if_pos hprefix, if_pos hprefix]
  · rw [if_neg hprefix, if_neg hprefix]
    exact canonicalQuaternionMonomial_exponentAt_supported
      5 monomial hsupport (index - 20)

private theorem shiftedCanonicalQuaternionMonomial_canonical_eq
    (monomial : List Nat)
    (hsupport : monomial.length ≤ 20) :
    canonicalQuaternionMonomial 10
        (List.replicate 20 0 ++
          canonicalQuaternionMonomial 5 monomial) =
      canonicalQuaternionMonomial 10
        (List.replicate 20 0 ++ monomial) :=
  canonicalQuaternionMonomial_congr_exponents
    10 _ _
    (shiftedCanonicalQuaternionMonomial_exponents
      monomial hsupport)

/-- Canonical source padding remains invisible after reflection into the
target half of the forty-coordinate carrier. -/
theorem shiftedCanonicalQuaternionPolynomial_eqv_shift
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 5 polynomial) :
    TenHaarCarrierEqv
      (shiftPolynomial 20
        (canonicalQuaternionPolynomial 5 polynomial))
      (shiftPolynomial 20 polynomial) := by
  apply tenHaarCarrierEqv_of_tenCanonicalTermwise
  induction polynomial with
  | nil => exact True.intro
  | cons term rest induction =>
      have hterm : term.1.length ≤ 20 := by
        exact hsupport term List.mem_cons_self
      have hrest :
          SupportedQuaternionBlocks 5 rest := by
        intro other hother
        exact hsupport other
          (List.mem_cons_of_mem term hother)
      change
        RatPolyTenCanonicalTermwiseEqv
          ((List.replicate 20 0 ++
                canonicalQuaternionMonomial 5 term.1,
              term.2) ::
            shiftPolynomial 20
              (canonicalQuaternionPolynomial 5 rest))
          ((List.replicate 20 0 ++ term.1, term.2) ::
            shiftPolynomial 20 rest)
      exact
        ⟨by
            rw [List.length_append,
              List.length_replicate,
              canonicalQuaternionMonomial_length]
            decide,
         by
            rw [List.length_append,
              List.length_replicate]
            omega,
         shiftedCanonicalQuaternionMonomial_canonical_eq
           term.1 hterm,
         Q'.eqv_refl term.2,
         induction hrest⟩

/-- Reflection transports the complete ordered source feature word to the
literal target feature word. -/
theorem shiftedSourceFeatureWordPolynomial_eqv_target :
    ∀ word : List BF4KineticFeature,
      TenHaarCarrierEqv
        (shiftPolynomial 20
          (sourceFeatureWordPolynomial word))
        (targetFeatureWordPolynomial word)
  | [] => shiftPolynomial_polyOne_eqv_one
  | feature :: rest => by
      change
        TenHaarCarrierEqv
          (shiftPolynomial 20
            (polyMul
              (sourceKineticFeaturePolynomial feature)
              (sourceFeatureWordPolynomial rest)))
          (polyMul
            (targetKineticFeaturePolynomial feature)
            (targetFeatureWordPolynomial rest))
      rw [shiftPolynomial_polyMul_exact,
        targetKineticFeaturePolynomial_eq_shift]
      exact TenHaarCarrierEqv.mul_left
        (shiftPolynomial 20
          (sourceKineticFeaturePolynomial feature))
        (shiftedSourceFeatureWordPolynomial_eqv_target rest)

/-! ## 4d. The literal packet half is one common boundary insertion -/

/-- Packet half-polynomial before the harmless five-block canonical
padding is applied to each state summand. -/
def bf4PacketRawHalfPolynomial
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    BF4HolonomyStatePacket → RatPoly
  | [] => polyZero
  | weightedState :: rest =>
      polyAdd
        (polySmul weightedState.1
          (bf4HolonomyHalfIntegrand
            diagonalOrder weightedState.2 word))
        (bf4PacketRawHalfPolynomial
          diagonalOrder word rest)

/-- Common geometric boundary polynomial of a signed all-spin packet,
before any diagonal or kinetic insertion. -/
def bf4PacketRawBoundaryPolynomial :
    BF4HolonomyStatePacket → RatPoly
  | [] => polyZero
  | weightedState :: rest =>
      polyAdd
        (polySmul weightedState.1
          (sourceMehlerWavefunction weightedState.2))
        (bf4PacketRawBoundaryPolynomial rest)

/-- Canonical padding used by the exact grouped Gram construction does not
change a packet half-polynomial under any arbitrary ten-Haar insertion. -/
theorem bf4PacketHalfPolynomial_eqv_raw
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    ∀ packet : BF4HolonomyStatePacket,
      TenHaarCarrierEqv
        (bf4PacketHalfPolynomial
          diagonalOrder word packet)
        (bf4PacketRawHalfPolynomial
          diagonalOrder word packet)
  | [] => TenHaarCarrierEqv.refl polyZero
  | weightedState :: rest => by
      change
        TenHaarCarrierEqv
          (polyAdd
            (polySmul weightedState.1
              (canonicalQuaternionPolynomial 5
                (bf4HolonomyHalfIntegrand
                  diagonalOrder weightedState.2 word)))
            (bf4PacketHalfPolynomial
              diagonalOrder word rest))
          (polyAdd
            (polySmul weightedState.1
              (bf4HolonomyHalfIntegrand
                diagonalOrder weightedState.2 word))
            (bf4PacketRawHalfPolynomial
              diagonalOrder word rest))
      exact TenHaarCarrierEqv.add_congr
        (TenHaarCarrierEqv.smul weightedState.1
          (canonicalQuaternionPolynomial_eqv
            5 (by decide)
            (bf4HolonomyHalfIntegrand
              diagonalOrder weightedState.2 word)
            (bf4HolonomyHalfIntegrand_supported
              diagonalOrder weightedState.2 word)))
        (bf4PacketHalfPolynomial_eqv_raw
          diagonalOrder word rest)

/-- Every raw packet half is the common packet boundary multiplied by the
same diagonal partial and feature word. -/
theorem bf4PacketRawHalfPolynomial_eqv_boundaryInsertion
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    ∀ packet : BF4HolonomyStatePacket,
      TenHaarCarrierEqv
        (bf4PacketRawHalfPolynomial
          diagonalOrder word packet)
        (polyMul
          (bf4PacketRawBoundaryPolynomial packet)
          (polyMul
            (sourceDiagonalFeynmanKacPartial diagonalOrder)
            (sourceFeatureWordPolynomial word)))
  | [] => by
      change
        TenHaarCarrierEqv polyZero
          (polyMul polyZero
            (polyMul
              (sourceDiagonalFeynmanKacPartial diagonalOrder)
              (sourceFeatureWordPolynomial word)))
      have hzero :
          polyMul polyZero
              (polyMul
                (sourceDiagonalFeynmanKacPartial diagonalOrder)
                (sourceFeatureWordPolynomial word)) =
            polyZero := by
        rfl
      rw [hzero]
      exact TenHaarCarrierEqv.refl polyZero
  | weightedState :: rest => by
      let wave :=
        sourceMehlerWavefunction weightedState.2
      let diagonal :=
        sourceDiagonalFeynmanKacPartial diagonalOrder
      let featureWord :=
        sourceFeatureWordPolynomial word
      let factor := polyMul diagonal featureWord
      change
        TenHaarCarrierEqv
          (polyAdd
            (polySmul weightedState.1
              (polyMul (polyMul wave diagonal)
                featureWord))
            (bf4PacketRawHalfPolynomial
              diagonalOrder word rest))
          (polyMul
            (polyAdd
              (polySmul weightedState.1 wave)
              (bf4PacketRawBoundaryPolynomial rest))
            factor)
      rw [polyMul_add_left_exact]
      apply TenHaarCarrierEqv.add_congr
      · refine TenHaarCarrierEqv.trans
          (TenHaarCarrierEqv.smul weightedState.1
            (tenHaarCarrierEqv_mul_assoc
              wave diagonal featureWord)) ?_
        exact TenHaarCarrierEqv.symm
          (tenHaarCarrierEqv_polyMul_smul_left
            weightedState.1 wave factor)
      · exact
          bf4PacketRawHalfPolynomial_eqv_boundaryInsertion
            diagonalOrder word rest

/-- The exact canonical packet half therefore has the same common boundary
factorization. -/
theorem bf4PacketHalfPolynomial_eqv_boundaryInsertion
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature)
    (packet : BF4HolonomyStatePacket) :
    TenHaarCarrierEqv
      (bf4PacketHalfPolynomial
        diagonalOrder word packet)
      (polyMul
        (bf4PacketRawBoundaryPolynomial packet)
        (polyMul
          (sourceDiagonalFeynmanKacPartial diagonalOrder)
          (sourceFeatureWordPolynomial word))) :=
  TenHaarCarrierEqv.trans
    (bf4PacketHalfPolynomial_eqv_raw
      diagonalOrder word packet)
    (bf4PacketRawHalfPolynomial_eqv_boundaryInsertion
      diagonalOrder word packet)

/-- Canonical padding is also invisible after the complete packet half is
reflected into the target coordinates. -/
theorem shiftedBF4PacketHalfPolynomial_eqv_raw
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    ∀ packet : BF4HolonomyStatePacket,
      TenHaarCarrierEqv
        (shiftPolynomial 20
          (bf4PacketHalfPolynomial
            diagonalOrder word packet))
        (shiftPolynomial 20
          (bf4PacketRawHalfPolynomial
            diagonalOrder word packet))
  | [] => TenHaarCarrierEqv.refl polyZero
  | weightedState :: rest => by
      change
        TenHaarCarrierEqv
          (shiftPolynomial 20
            (polyAdd
              (polySmul weightedState.1
                (canonicalQuaternionPolynomial 5
                  (bf4HolonomyHalfIntegrand
                    diagonalOrder weightedState.2 word)))
              (bf4PacketHalfPolynomial
                diagonalOrder word rest)))
          (shiftPolynomial 20
            (polyAdd
              (polySmul weightedState.1
                (bf4HolonomyHalfIntegrand
                  diagonalOrder weightedState.2 word))
              (bf4PacketRawHalfPolynomial
                diagonalOrder word rest)))
      rw [shiftPolynomial_polyAdd_exact,
        shiftPolynomial_polyAdd_exact,
        shiftPolynomial_polySmul_exact,
        shiftPolynomial_polySmul_exact]
      exact TenHaarCarrierEqv.add_congr
        (TenHaarCarrierEqv.smul weightedState.1
          (shiftedCanonicalQuaternionPolynomial_eqv_shift
            (bf4HolonomyHalfIntegrand
              diagonalOrder weightedState.2 word)
            (bf4HolonomyHalfIntegrand_supported
              diagonalOrder weightedState.2 word)))
        (shiftedBF4PacketHalfPolynomial_eqv_raw
          diagonalOrder word rest)

/-- Common reflected geometric boundary of a signed packet. -/
def bf4PacketRawTargetBoundaryPolynomial
    (packet : BF4HolonomyStatePacket) : RatPoly :=
  shiftPolynomial 20
    (bf4PacketRawBoundaryPolynomial packet)

/-- The reflected raw packet half factors through the compiled target
diagonal partial and the literal target feature word. -/
theorem shiftedBF4PacketRawHalfPolynomial_eqv_targetBoundaryInsertion
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature) :
    ∀ packet : BF4HolonomyStatePacket,
      TenHaarCarrierEqv
        (shiftPolynomial 20
          (bf4PacketRawHalfPolynomial
            diagonalOrder word packet))
        (polyMul
          (bf4PacketRawTargetBoundaryPolynomial packet)
          (polyMul
            (targetDiagonalFeynmanKacPartial diagonalOrder)
            (targetFeatureWordPolynomial word)))
  | [] => by
      change
        TenHaarCarrierEqv polyZero
          (polyMul polyZero
            (polyMul
              (targetDiagonalFeynmanKacPartial diagonalOrder)
              (targetFeatureWordPolynomial word)))
      exact TenHaarCarrierEqv.refl polyZero
  | weightedState :: rest => by
      let wave :=
        sourceMehlerWavefunction weightedState.2
      let targetWave := shiftPolynomial 20 wave
      let targetDiagonal :=
        targetDiagonalFeynmanKacPartial diagonalOrder
      let targetWord := targetFeatureWordPolynomial word
      let factor := polyMul targetDiagonal targetWord
      change
        TenHaarCarrierEqv
          (shiftPolynomial 20
            (polyAdd
              (polySmul weightedState.1
                (polyMul
                  (polyMul wave
                    (sourceDiagonalFeynmanKacPartial
                      diagonalOrder))
                  (sourceFeatureWordPolynomial word)))
              (bf4PacketRawHalfPolynomial
                diagonalOrder word rest)))
          (polyMul
            (shiftPolynomial 20
              (polyAdd
                (polySmul weightedState.1 wave)
                (bf4PacketRawBoundaryPolynomial rest)))
            factor)
      rw [shiftPolynomial_polyAdd_exact,
        shiftPolynomial_polySmul_exact,
        shiftPolynomial_polyMul_exact,
        shiftPolynomial_polyMul_exact,
        shiftPolynomial_polyAdd_exact,
        shiftPolynomial_polySmul_exact,
        polyMul_add_left_exact]
      apply TenHaarCarrierEqv.add_congr
      · refine TenHaarCarrierEqv.trans
          (TenHaarCarrierEqv.smul weightedState.1
            (TenHaarCarrierEqv.mul_congr
              (TenHaarCarrierEqv.mul_left targetWave
                (shiftedSourceDiagonalFeynmanKacPartial_eqv_target
                  diagonalOrder))
              (shiftedSourceFeatureWordPolynomial_eqv_target
                word))) ?_
        refine TenHaarCarrierEqv.trans
          (TenHaarCarrierEqv.smul weightedState.1
            (tenHaarCarrierEqv_mul_assoc
              targetWave targetDiagonal targetWord)) ?_
        exact TenHaarCarrierEqv.symm
          (tenHaarCarrierEqv_polyMul_smul_left
            weightedState.1 targetWave factor)
      · exact
          shiftedBF4PacketRawHalfPolynomial_eqv_targetBoundaryInsertion
            diagonalOrder word rest

/-- **Reflected target packet factorization.**  The actual canonical target
half used by the grouped Gram is one common reflected boundary multiplied by
the compiled target diagonal partial and the target feature word. -/
theorem shiftedBF4PacketHalfPolynomial_eqv_targetBoundaryInsertion
    (diagonalOrder : Nat)
    (word : List BF4KineticFeature)
    (packet : BF4HolonomyStatePacket) :
    TenHaarCarrierEqv
      (shiftPolynomial 20
        (bf4PacketHalfPolynomial
          diagonalOrder word packet))
      (polyMul
        (bf4PacketRawTargetBoundaryPolynomial packet)
        (polyMul
          (targetDiagonalFeynmanKacPartial diagonalOrder)
          (targetFeatureWordPolynomial word))) :=
  TenHaarCarrierEqv.trans
    (shiftedBF4PacketHalfPolynomial_eqv_raw
      diagonalOrder word packet)
    (shiftedBF4PacketRawHalfPolynomial_eqv_targetBoundaryInsertion
      diagonalOrder word packet)

/-- Common reflected packet boundary carried by every diagonal order and
every kinetic word. -/
def bf4PacketRawReflectedBoundaryPolynomial
    (packet : BF4HolonomyStatePacket) : RatPoly :=
  polyMul
    (bf4PacketRawBoundaryPolynomial packet)
    (bf4PacketRawTargetBoundaryPolynomial packet)

/-- Rectangular source-diagonal/target-diagonal/kinetic-word presentation of
one grouped packet channel. -/
def bf4PacketRectangularWordPolynomial
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) : RatPoly :=
  polyMul
    (bf4PacketRawReflectedBoundaryPolynomial packet)
    (polyMul
      (polyMul
        (sourceDiagonalFeynmanKacPartial diagonalOrder)
        (targetDiagonalFeynmanKacPartial diagonalOrder))
      (bf4SeparatedReflectedKineticWordPolynomial word))

/-- **Finite rectangular word identity.**  One literal reflected grouped
packet square is, under every arbitrary insertion, the common packet
boundary times the source and compiled-target diagonal partials times the
physical weighted kinetic word. -/
theorem bf4PacketReflectedSquarePolynomial_eqv_rectangularWord
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket)
    (word : List BF4KineticFeature) :
    TenHaarCarrierEqv
      (bf4PacketReflectedSquarePolynomial
        diagonalOrder packet word)
      (bf4PacketRectangularWordPolynomial
        diagonalOrder packet word) := by
  let half :=
    bf4PacketHalfPolynomial diagonalOrder word packet
  let sourceBoundary :=
    bf4PacketRawBoundaryPolynomial packet
  let targetBoundary :=
    bf4PacketRawTargetBoundaryPolynomial packet
  let sourceDiagonal :=
    sourceDiagonalFeynmanKacPartial diagonalOrder
  let targetDiagonal :=
    targetDiagonalFeynmanKacPartial diagonalOrder
  let sourceWord := sourceFeatureWordPolynomial word
  let targetWord := targetFeatureWordPolynomial word
  let boundaryPair := polyMul sourceBoundary targetBoundary
  let diagonalPair := polyMul sourceDiagonal targetDiagonal
  let wordPair := polyMul sourceWord targetWord
  let weight := bf4FeatureWordWeight word
  have hhalves :
      TenHaarCarrierEqv
        (polyMul half (shiftPolynomial 20 half))
        (polyMul
          (polyMul sourceBoundary
            (polyMul sourceDiagonal sourceWord))
          (polyMul targetBoundary
            (polyMul targetDiagonal targetWord))) :=
    TenHaarCarrierEqv.mul_congr
      (bf4PacketHalfPolynomial_eqv_boundaryInsertion
        diagonalOrder word packet)
      (shiftedBF4PacketHalfPolynomial_eqv_targetBoundaryInsertion
        diagonalOrder word packet)
  have hregroup :
      TenHaarCarrierEqv
        (polyMul
          (polyMul sourceBoundary
            (polyMul sourceDiagonal sourceWord))
          (polyMul targetBoundary
            (polyMul targetDiagonal targetWord)))
        (polyMul boundaryPair
          (polyMul diagonalPair wordPair)) :=
    TenHaarCarrierEqv.trans
      (tenHaarCarrierEqv_four_swap
        sourceBoundary
        (polyMul sourceDiagonal sourceWord)
        targetBoundary
        (polyMul targetDiagonal targetWord))
      (TenHaarCarrierEqv.mul_left boundaryPair
        (tenHaarCarrierEqv_four_swap
          sourceDiagonal sourceWord
          targetDiagonal targetWord))
  unfold bf4PacketReflectedSquarePolynomial
    bf4PacketRectangularWordPolynomial
    bf4PacketRawReflectedBoundaryPolynomial
    bf4SeparatedReflectedKineticWordPolynomial
  change
    TenHaarCarrierEqv
      (polySmul weight
        (polyMul half (shiftPolynomial 20 half)))
      (polyMul boundaryPair
        (polyMul diagonalPair
          (polySmul weight wordPair)))
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.smul weight
      (TenHaarCarrierEqv.trans hhalves hregroup)) ?_
  refine TenHaarCarrierEqv.trans
    (TenHaarCarrierEqv.symm
      (tenHaarCarrierEqv_polyMul_smul_right
        weight boundaryPair
        (polyMul diagonalPair wordPair))) ?_
  exact TenHaarCarrierEqv.mul_left boundaryPair
    (TenHaarCarrierEqv.symm
      (tenHaarCarrierEqv_polyMul_smul_right
        weight diagonalPair wordPair))

/-- Exact all-label powers now land on the genuine BF4 kinetic cross
polynomial, not merely on its enumerated atom presentation. -/
theorem groupedKineticCrossTaylorTerm_eqv_physical
    (length : Nat) :
    TenHaarCarrierEqv
      (polySmul (ExpNeg.termAbs 1 length)
        (polynomialPower
          groupedKineticCrossAtomSumPolynomial length))
      (polySmul (ExpNeg.termAbs 1 length)
        (polynomialPower
          sourceTargetKineticCrossPolynomial length)) :=
  TenHaarCarrierEqv.smul
    (ExpNeg.termAbs 1 length)
    (TenHaarCarrierEqv.power
      groupedKineticCrossAtomSum_eqv_physical
      length)

/-- **Physical-coordinate finite Mertens theorem.**  Every exact-length
reflected all-label BF4 sum equals the matching Taylor term of the genuine
coupled source/target kinetic cross polynomial. -/
theorem bf4SeparatedReflectedKineticWordsExactMoment_eq_physicalTerm
    (insertion : RatPoly) (length : Nat) :
    bf4SeparatedReflectedKineticWordsExactMoment
        insertion length ≈
      quaternionHaar 10
        (polyMul insertion
          (polySmul (ExpNeg.termAbs 1 length)
            (polynomialPower
              sourceTargetKineticCrossPolynomial
              length))) := by
  exact Q'.eqv_trans _ _ _
    (bf4SeparatedReflectedKineticWordsExactMoment_eq_term
      insertion length)
    (groupedKineticCrossTaylorTerm_eqv_physical
      length insertion)

/-! ## 5. Removal of the finite kinetic-word cutoff -/

/-- Ordinary positive Taylor partial of the genuine reflected kinetic cross
polynomial.  The `order` convention is the same as the diagonal partial:
orders `0,...,order-1` are included. -/
def sourceTargetKineticCrossTaylorPartial : Nat → RatPoly
  | 0 => polyZero
  | order + 1 =>
      polyAdd
        (sourceTargetKineticCrossTaylorPartial order)
        (polySmul (ExpNeg.termAbs 1 order)
          (polynomialPower
            sourceTargetKineticCrossPolynomial order))

/-- Sum of every literal reflected kinetic word through the displayed
cutoff after an arbitrary insertion. -/
def bf4SeparatedReflectedKineticWordsAtMostMoment
    (insertion : RatPoly) (crossOrder : Nat) : Q' :=
  listQSum
    (fun word =>
      quaternionHaar 10
        (polyMul insertion
          (bf4SeparatedReflectedKineticWordPolynomial
            word)))
    (bf4FeatureWordsAtMost crossOrder)

/-- **All-label finite-cutoff collapse.**  The whole displayed physical
word carrier, not just one exact shell, is exactly the ordinary Taylor
partial of the genuine kinetic cross polynomial. -/
theorem bf4SeparatedReflectedKineticWordsAtMostMoment_eq_partial :
    ∀ (insertion : RatPoly) (crossOrder : Nat),
      bf4SeparatedReflectedKineticWordsAtMostMoment
          insertion crossOrder ≈
        quaternionHaar 10
          (polyMul insertion
            (sourceTargetKineticCrossTaylorPartial
              (crossOrder + 1)))
  | insertion, 0 => by
      change
        bf4SeparatedReflectedKineticWordsExactMoment
            insertion 0 ≈
          quaternionHaar 10
            (polyMul insertion
              (polyAdd polyZero
                (polySmul (ExpNeg.termAbs 1 0)
                  (polynomialPower
                    sourceTargetKineticCrossPolynomial 0))))
      have hpartial :
          polyAdd polyZero
              (polySmul (ExpNeg.termAbs 1 0)
                (polynomialPower
                  sourceTargetKineticCrossPolynomial 0)) =
            polySmul (ExpNeg.termAbs 1 0)
              (polynomialPower
                sourceTargetKineticCrossPolynomial 0) := by
        rfl
      rw [hpartial]
      exact
        bf4SeparatedReflectedKineticWordsExactMoment_eq_physicalTerm
          insertion 0
  | insertion, crossOrder + 1 => by
      change
        listQSum
            (fun word =>
              quaternionHaar 10
                (polyMul insertion
                  (bf4SeparatedReflectedKineticWordPolynomial
                    word)))
            (bf4FeatureWordsAtMost crossOrder ++
              bf4FeatureWordsExact (crossOrder + 1)) ≈
          quaternionHaar 10
            (polyMul insertion
              (polyAdd
                (sourceTargetKineticCrossTaylorPartial
                  (crossOrder + 1))
                (polySmul
                  (ExpNeg.termAbs 1 (crossOrder + 1))
                  (polynomialPower
                    sourceTargetKineticCrossPolynomial
                    (crossOrder + 1)))))
      refine Q'.eqv_trans _
        (bf4SeparatedReflectedKineticWordsAtMostMoment
              insertion crossOrder +
          bf4SeparatedReflectedKineticWordsExactMoment
              insertion (crossOrder + 1)) _
        (listQSum_append
          (fun word =>
            quaternionHaar 10
              (polyMul insertion
                (bf4SeparatedReflectedKineticWordPolynomial
                  word)))
          (bf4FeatureWordsAtMost crossOrder)
          (bf4FeatureWordsExact (crossOrder + 1))) ?_
      refine Q'.eqv_trans _
        (quaternionHaar 10
              (polyMul insertion
                (sourceTargetKineticCrossTaylorPartial
                  (crossOrder + 1))) +
          quaternionHaar 10
            (polyMul insertion
              (polySmul
                (ExpNeg.termAbs 1 (crossOrder + 1))
                (polynomialPower
                  sourceTargetKineticCrossPolynomial
                  (crossOrder + 1))))) _
        (Q'.add_eqv_congr'
          (bf4SeparatedReflectedKineticWordsAtMostMoment_eq_partial
            insertion crossOrder)
          (bf4SeparatedReflectedKineticWordsExactMoment_eq_physicalTerm
            insertion (crossOrder + 1))) ?_
      exact Q'.eqv_symm
        (quaternionHaar_polyMul_add_right
          10 insertion
          (sourceTargetKineticCrossTaylorPartial
            (crossOrder + 1))
          (polySmul
            (ExpNeg.termAbs 1 (crossOrder + 1))
            (polynomialPower
              sourceTargetKineticCrossPolynomial
              (crossOrder + 1))))

/-! ## 6. Complete finite rectangular packet identity -/

/-- Literal polynomial sum of a displayed list of separated weighted kinetic
words. -/
def bf4SeparatedReflectedKineticWordPolynomialSumOn :
    List (List BF4KineticFeature) → RatPoly
  | [] => polyZero
  | word :: rest =>
      polyAdd
        (bf4SeparatedReflectedKineticWordPolynomial word)
        (bf4SeparatedReflectedKineticWordPolynomialSumOn rest)

/-- Sum of the rectangular packet word representatives over a displayed word
list. -/
def bf4PacketRectangularPolynomialOn
    (diagonalOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    List (List BF4KineticFeature) → RatPoly
  | [] => polyZero
  | word :: rest =>
      polyAdd
        (bf4PacketRectangularWordPolynomial
          diagonalOrder packet word)
        (bf4PacketRectangularPolynomialOn
          diagonalOrder packet rest)

/-- Every finite displayed grouped-square list equals its rectangular source /
target / kinetic presentation. -/
theorem bf4PacketGroupedSquarePolynomialOn_eqv_rectangular :
    ∀ (diagonalOrder : Nat)
      (packet : BF4HolonomyStatePacket)
      (words : List (List BF4KineticFeature)),
      TenHaarCarrierEqv
        (bf4PacketGroupedSquarePolynomialOn
          diagonalOrder packet words)
        (bf4PacketRectangularPolynomialOn
          diagonalOrder packet words)
  | _, _, [] => TenHaarCarrierEqv.refl polyZero
  | diagonalOrder, packet, word :: rest => by
      change
        TenHaarCarrierEqv
          (polyAdd
            (bf4PacketReflectedSquarePolynomial
              diagonalOrder packet word)
            (bf4PacketGroupedSquarePolynomialOn
              diagonalOrder packet rest))
          (polyAdd
            (bf4PacketRectangularWordPolynomial
              diagonalOrder packet word)
            (bf4PacketRectangularPolynomialOn
              diagonalOrder packet rest))
      exact TenHaarCarrierEqv.add_congr
        (bf4PacketReflectedSquarePolynomial_eqv_rectangularWord
          diagonalOrder packet word)
        (bf4PacketGroupedSquarePolynomialOn_eqv_rectangular
          diagonalOrder packet rest)

/-- The packet boundary and the two diagonal partials factor out of every
finite rectangular word list. -/
theorem bf4PacketRectangularPolynomialOn_eqv_factor :
    ∀ (diagonalOrder : Nat)
      (packet : BF4HolonomyStatePacket)
      (words : List (List BF4KineticFeature)),
      TenHaarCarrierEqv
        (bf4PacketRectangularPolynomialOn
          diagonalOrder packet words)
        (polyMul
          (bf4PacketRawReflectedBoundaryPolynomial packet)
          (polyMul
            (polyMul
              (sourceDiagonalFeynmanKacPartial diagonalOrder)
              (targetDiagonalFeynmanKacPartial diagonalOrder))
            (bf4SeparatedReflectedKineticWordPolynomialSumOn
              words)))
  | diagonalOrder, packet, [] => by
      unfold bf4PacketRectangularPolynomialOn
        bf4SeparatedReflectedKineticWordPolynomialSumOn
      change TenHaarCarrierEqv polyZero _
      rw [show
          polyMul
              (bf4PacketRawReflectedBoundaryPolynomial packet)
              (polyMul
                (polyMul
                  (sourceDiagonalFeynmanKacPartial diagonalOrder)
                  (targetDiagonalFeynmanKacPartial diagonalOrder))
                polyZero) =
            polyZero by
          rw [polyMul_zero_right_exact,
            polyMul_zero_right_exact]]
      exact TenHaarCarrierEqv.refl polyZero
  | diagonalOrder, packet, word :: rest => by
      let boundary :=
        bf4PacketRawReflectedBoundaryPolynomial packet
      let diagonal :=
        polyMul
          (sourceDiagonalFeynmanKacPartial diagonalOrder)
          (targetDiagonalFeynmanKacPartial diagonalOrder)
      let wordPolynomial :=
        bf4SeparatedReflectedKineticWordPolynomial word
      let restPolynomial :=
        bf4SeparatedReflectedKineticWordPolynomialSumOn rest
      change
        TenHaarCarrierEqv
          (polyAdd
            (polyMul boundary
              (polyMul diagonal wordPolynomial))
            (bf4PacketRectangularPolynomialOn
              diagonalOrder packet rest))
          (polyMul boundary
            (polyMul diagonal
              (polyAdd wordPolynomial restPolynomial)))
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.add_right
          (TenHaarCarrierEqv.refl
            (polyMul boundary
              (polyMul diagonal wordPolynomial)))
          (bf4PacketRectangularPolynomialOn
            diagonalOrder packet rest)) ?_
      refine TenHaarCarrierEqv.trans
        (TenHaarCarrierEqv.add_left
          (polyMul boundary
            (polyMul diagonal wordPolynomial))
          (bf4PacketRectangularPolynomialOn_eqv_factor
            diagonalOrder packet rest)) ?_
      exact TenHaarCarrierEqv.symm
        (TenHaarCarrierEqv.trans
          (TenHaarCarrierEqv.mul_left boundary
            (tenHaarCarrierEqv_polyMul_add_right
              diagonal wordPolynomial restPolynomial))
          (tenHaarCarrierEqv_polyMul_add_right
            boundary
            (polyMul diagonal wordPolynomial)
            (polyMul diagonal restPolynomial)))

private theorem bf4SeparatedReflectedKineticWordPolynomialSumOn_haar
    (insertion : RatPoly) :
    ∀ words : List (List BF4KineticFeature),
      quaternionHaar 10
          (polyMul insertion
            (bf4SeparatedReflectedKineticWordPolynomialSumOn
              words)) ≈
        listQSum
          (fun word =>
            quaternionHaar 10
              (polyMul insertion
                (bf4SeparatedReflectedKineticWordPolynomial
                  word)))
          words
  | [] => by
      change
        quaternionHaar 10
            (polyMul insertion polyZero) ≈ 0
      rw [polyMul_zero_right_exact]
      exact Q'.eqv_refl 0
  | word :: rest => by
      change
        quaternionHaar 10
            (polyMul insertion
              (polyAdd
                (bf4SeparatedReflectedKineticWordPolynomial word)
                (bf4SeparatedReflectedKineticWordPolynomialSumOn
                  rest))) ≈
          quaternionHaar 10
                (polyMul insertion
                  (bf4SeparatedReflectedKineticWordPolynomial word)) +
            listQSum
              (fun other =>
                quaternionHaar 10
                  (polyMul insertion
                    (bf4SeparatedReflectedKineticWordPolynomial
                      other)))
              rest
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_add_right
          10 insertion
          (bf4SeparatedReflectedKineticWordPolynomial word)
          (bf4SeparatedReflectedKineticWordPolynomialSumOn rest))
        (Q'.add_eqv_congr_left _ _ _
          (bf4SeparatedReflectedKineticWordPolynomialSumOn_haar
            insertion rest))

/-- The entire finite all-label word polynomial is the genuine kinetic-cross
Taylor partial in the arbitrary-insertion carrier. -/
theorem bf4SeparatedReflectedKineticWordPolynomialSumAtMost_eqv_partial
    (crossOrder : Nat) :
    TenHaarCarrierEqv
      (bf4SeparatedReflectedKineticWordPolynomialSumOn
        (bf4FeatureWordsAtMost crossOrder))
      (sourceTargetKineticCrossTaylorPartial
        (crossOrder + 1)) := by
  intro insertion
  exact Q'.eqv_trans _ _ _
    (bf4SeparatedReflectedKineticWordPolynomialSumOn_haar
      insertion (bf4FeatureWordsAtMost crossOrder))
    (bf4SeparatedReflectedKineticWordsAtMostMoment_eq_partial
      insertion crossOrder)

/-- **Complete finite rectangular BF4 identity.**  At both displayed cutoffs,
the actual grouped packet square is one common reflected boundary times the
source and compiled-target diagonal partials times the genuine kinetic-cross
Taylor partial. -/
theorem bf4PacketGroupedSquarePolynomial_eqv_rectangularPartial
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    TenHaarCarrierEqv
      (bf4PacketGroupedSquarePolynomial
        diagonalOrder crossOrder packet)
      (polyMul
        (bf4PacketRawReflectedBoundaryPolynomial packet)
        (polyMul
          (polyMul
            (sourceDiagonalFeynmanKacPartial diagonalOrder)
            (targetDiagonalFeynmanKacPartial diagonalOrder))
          (sourceTargetKineticCrossTaylorPartial
            (crossOrder + 1)))) := by
  unfold bf4PacketGroupedSquarePolynomial
  refine TenHaarCarrierEqv.trans
    (bf4PacketGroupedSquarePolynomialOn_eqv_rectangular
      diagonalOrder packet
      (bf4FeatureWordsAtMost crossOrder)) ?_
  refine TenHaarCarrierEqv.trans
    (bf4PacketRectangularPolynomialOn_eqv_factor
      diagonalOrder packet
      (bf4FeatureWordsAtMost crossOrder)) ?_
  exact TenHaarCarrierEqv.mul_left
    (bf4PacketRawReflectedBoundaryPolynomial packet)
    (TenHaarCarrierEqv.mul_left
      (polyMul
        (sourceDiagonalFeynmanKacPartial diagonalOrder)
        (targetDiagonalFeynmanKacPartial diagonalOrder))
      (bf4SeparatedReflectedKineticWordPolynomialSumAtMost_eqv_partial
        crossOrder))

end YMGap.Continuum.BF4GroupedCarrierMertens

#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.TenHaarCarrierEqv.mul_congr
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.ratPolyTermwiseEqv_polyMul_assoc
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.tenHaarCarrierEqv_mul_assoc
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.ratPolyTermwiseEqv_polyMul_smul
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.tenHaarCarrierEqv_four_swap
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.bf4SeparatedReflectedKineticWord_eqv_groupedTaylor
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.bf4SeparatedReflectedKineticWordsExactMoment_eq_term
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.groupedKineticCrossAtomSum_eqv_physical
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.bf4SeparatedReflectedKineticWordsExactMoment_eq_physicalTerm
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.bf4SeparatedReflectedKineticWordsAtMostMoment_eq_partial
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.sourceDiagonalComplementMoment_eqv_power
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.sourceDiagonalFeynmanKacPartial_eqv_ordinary
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.shiftPolynomial_polyMul_exact
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.shiftPolynomial_polyOne_eqv_one
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.canonicalQuaternionPolynomial_eqv
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.tenHaarCarrierEqv_of_tenCanonicalTermwise
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.targetDiagonalComplement_eqv_shiftSource
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.shiftedSourceDiagonalFeynmanKacPartial_eqv_target
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.shiftedCanonicalQuaternionPolynomial_eqv_shift
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.bf4PacketHalfPolynomial_eqv_boundaryInsertion
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.shiftedBF4PacketHalfPolynomial_eqv_targetBoundaryInsertion
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.bf4PacketReflectedSquarePolynomial_eqv_rectangularWord
#print axioms YMGap.Continuum.BF4GroupedCarrierMertens.bf4PacketGroupedSquarePolynomial_eqv_rectangularPartial
