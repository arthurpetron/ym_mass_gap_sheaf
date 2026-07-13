/-
The smallest multi-slice pilot forced by the two-slice quotient-collapse.

We use the actual non-unit `halfReferenceWeight 3`.  Its pointwise carrier
retains every ordered adjacent-pair coordinate and the cyclic time translation
is genuinely nonidentity in that carrier.  The interacting reflected form has
an exact finite rational one-character Gram resolution and is positive.

The pilot nevertheless fails before a positive-time compression can honestly
be constructed: the normalized product expectation is not additive for the
pointwise carrier.  More strongly, the failure is not repaired merely by
inventing another compatible module on the same pure-product observables.  The
Wilson form of every such module is rank one, depending only on the total
three-slice product.  Cyclic time fixes that product, hence is radical-trivial
in every compatible GNS quotient.  This is the corrected carrier invariant:
a successful next pilot must replace the pure-product observable carrier by a
linear span of character tensors whose state has a genuinely multi-coordinate
Gram matrix; retaining extra equivalence coordinates alone cannot suffice.

No toy sector or operator property is adjoined.  All counterexamples and Gram
identities are exact over `Q'`.
-/

import YMGap.Continuum.TwoSliceCharacterReflection

namespace YMGap.Continuum.MultiSliceWilsonPositiveTimePilot

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.InteractingReflectionTimeLaw
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.TwoSliceCharacterReflection
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem int_mul_two (a : Int) : a * 2 = a + a := by omega
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               one_num_cast, one_den_cast, zero_num_cast, zero_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero, Int.two_mul, int_mul_two];
             ac_rfl))

/-! ## Three physical slices and an oriented adjacent pair -/

/-- The actual character amplitude read by the three-factor product state. -/
def threeSliceTotal (a : Nat → Q') : Q' := (a 0 * a 1) * a 2

/-- The ordered positive-time adjacent-pair coordinate `(0,1)`. -/
def adjacentPair01 (a : Nat → Q') : Q' := a 0 * a 1

/-- Cyclic one-step time translation on the first three slices. -/
def rotateIndex3 : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | n + 3 => n + 3

def rotate3 (a : Nat → Q') : Nat → Q' := fun i => a (rotateIndex3 i)

theorem rotateIndex3_three (i : Nat) :
    rotateIndex3 (rotateIndex3 (rotateIndex3 i)) = i := by
  cases i with
  | zero => rfl
  | succ i => cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => rfl

theorem rotate3_three (a : Nat → Q') :
    rotate3 (rotate3 (rotate3 a)) = a := by
  funext i
  change a (rotateIndex3 (rotateIndex3 (rotateIndex3 i))) = a i
  rw [rotateIndex3_three]

/-- Total character is multiplicative under the pointwise observable product. -/
theorem threeSliceTotal_mul (a b : Nat → Q') :
    threeSliceTotal ((prodAlg (fun _ => realEdge) 3).mul a b) ≈
      threeSliceTotal a * threeSliceTotal b := by
  unfold threeSliceTotal prodAlg realEdge
  ring_qeqv

/-- Cyclic time fixes the total character but not its ordered factors. -/
theorem threeSliceTotal_rotate (a : Nat → Q') :
    threeSliceTotal (rotate3 a) ≈ threeSliceTotal a := by
  unfold threeSliceTotal rotate3 rotateIndex3
  ring_qeqv

/-- The normalized expectation of the genuine non-unit three-slice weight is
exactly the total three-slice character. -/
theorem halfReferenceWeight_three_E_eqv_total (a : Nat → Q') :
    ((halfReferenceWeight 3).E_Λ a) ≈ threeSliceTotal a := by
  apply referenceWeight_eqv_of_weighted_factor
  let h : Q' := Q'.mkPos 1 2 (by decide)
  change ((((1 : Q') * (h * a 0)) * (h * a 1)) * (h * a 2)) ≈
    (((((1 : Q') * (h * 1)) * (h * 1)) * (h * 1)) *
      ((a 0 * a 1) * a 2))
  ring_qeqv

/-! ## Genuine nonidentity cyclic time geometry on the pointwise carrier -/

def rotate3Hom :
    ObsHom (prodAlg (fun _ => realEdge) 3) (prodAlg (fun _ => realEdge) 3) where
  map := rotate3
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

theorem halfReferenceWeight_three_reference_rotate_invariant (a : Nat → Q') :
    ((halfReferenceWeight 3).I₀.E (rotate3 a)) ≈
      ((halfReferenceWeight 3).I₀.E a) := by
  change (((1 : Q') * a 1) * a 2) * a 0 ≈
    (((1 : Q') * a 0) * a 1) * a 2
  ring_qeqv

theorem halfWeight_three_rotate_fixed :
    rotate3 (halfReferenceWeight 3).w = (halfReferenceWeight 3).w := rfl

def halfRotate3Action : ReferenceTranslationAction (halfReferenceWeight 3) where
  hom := rotate3Hom
  weight_fixed := halfWeight_three_rotate_fixed
  reference_invariant := halfReferenceWeight_three_reference_rotate_invariant

/-- The pointwise carrier retains the ordered adjacent pair and all individual
slice coordinates. -/
abbrev threeSlicePointwiseModule :
    WilsonGNSData.CarrierModule (prodAlg (fun _ => realEdge) 3) :=
  realProductCarrierModule 3

def threeSlicePointwiseGeometry : GeometryEnrichedReferenceWeight
    (halfReferenceWeight 3) threeSlicePointwiseModule where
  timeExtent := 3
  timeExtent_pos := by decide
  action := halfRotate3Action
  periodic := rotate3_three
  map_veq := fun h i => h (rotateIndex3 i)
  map_add := fun _ _ i => Q'.eqv_refl _
  map_neg := fun _ i => Q'.eqv_refl _
  map_smul := fun _ _ i => Q'.eqv_refl _

/-- A physical ordered-pair observable: pair `(0,1)` is on, slice `2` is off. -/
def adjacentPairWitness : Nat → Q' := fun i =>
  if i = 0 then 1 else if i = 1 then 1 else 0

/-- Time translation genuinely changes the retained adjacent-pair coordinate. -/
theorem adjacentPair_rotates_nontrivially :
    ¬ (adjacentPair01 (rotate3 adjacentPairWitness) ≈
      adjacentPair01 adjacentPairWitness) := by
  decide

/-- Consequently cyclic time is not carrier-equivalent to identity on the
pointwise three-slice carrier. -/
theorem rotate3_not_pointwise_veq_identity :
    ¬ threeSlicePointwiseModule.veq (rotate3 adjacentPairWitness)
      adjacentPairWitness := by
  intro h
  exact adjacentPair_rotates_nontrivially
    (Q'.mul_eqv_congr_right _ _ _ (h 0) |>.trans
      (Q'.mul_eqv_congr_left _ _ _ (h 1)))

/-! ## Exact finite rational reflection Gram law -/

/-- The raw interacting reflected form is exactly the rank-one total-character
product. -/
theorem threeSlice_raw_reflected_form (a b : Nat → Q') :
    ((halfReferenceWeight 3).E_Λ
      ((prodAlg (fun _ => realEdge) 3).mul (rotate3 a) b)) ≈
      threeSliceTotal a * threeSliceTotal b := by
  refine Q'.eqv_trans _ _ _ (halfReferenceWeight_three_E_eqv_total _) ?_
  refine Q'.eqv_trans _ _ _ (threeSliceTotal_mul (rotate3 a) b) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (threeSliceTotal_rotate a)

/-- The same identity as an exact one-mode finite character Gram resolution. -/
theorem threeSlice_raw_character_resolution (a b : Nat → Q') :
    ((halfReferenceWeight 3).E_Λ
      ((prodAlg (fun _ => realEdge) 3).mul (rotate3 a) b)) ≈
      characterGramSum (fun x _ => threeSliceTotal x) a b 1 := by
  refine Q'.eqv_trans _ _ _ (threeSlice_raw_reflected_form a b) ?_
  change threeSliceTotal a * threeSliceTotal b ≈
    0 + threeSliceTotal a * threeSliceTotal b
  exact Q'.eqv_symm (QPoly.q_zero_add_eqv _)

/-- Reflection positivity is derived from the rational square in that Gram
identity. -/
theorem threeSlice_raw_reflected_positive (a : Nat → Q') :
    (0 : Q') ≤ (halfReferenceWeight 3).E_Λ
      ((prodAlg (fun _ => realEdge) 3).mul (rotate3 a) a) :=
  le_of_le_eqv (SumOfSquares.q_mul_self_nonneg (threeSliceTotal a))
    (Q'.eqv_symm (threeSlice_raw_reflected_form a a))

/-! ## Exact failure of the candidate carrier -/

def additivityLeftWitness : Nat → Q' := fun i =>
  if i = 0 then 1 else if i = 2 then 1 else 0

def additivityRightWitness : Nat → Q' := fun i =>
  if i = 1 then 1 else 0

/-- The pointwise carrier cannot support the Wilson GNS construction: two
zero-expectation pure tensors add to a unit-expectation observable. -/
theorem no_threeSlice_pointwise_elin_add :
    (∀ a b,
      ((halfReferenceWeight 3).E_Λ (threeSlicePointwiseModule.add a b)) ≈
        ((halfReferenceWeight 3).E_Λ a +
          (halfReferenceWeight 3).E_Λ b)) → False := by
  intro H
  have hsum := H additivityLeftWitness additivityRightWitness
  have hadd :
      ((halfReferenceWeight 3).E_Λ
        (threeSlicePointwiseModule.add additivityLeftWitness
          additivityRightWitness)) ≈ 1 :=
    Q'.eqv_trans _ _ _ (halfReferenceWeight_three_E_eqv_total _) (by decide)
  have hleft :
      ((halfReferenceWeight 3).E_Λ additivityLeftWitness) ≈ 0 :=
    Q'.eqv_trans _ _ _ (halfReferenceWeight_three_E_eqv_total _) (by decide)
  have hright :
      ((halfReferenceWeight 3).E_Λ additivityRightWitness) ≈ 0 :=
    Q'.eqv_trans _ _ _ (halfReferenceWeight_three_E_eqv_total _) (by decide)
  have hrhs :
      ((halfReferenceWeight 3).E_Λ additivityLeftWitness +
        (halfReferenceWeight 3).E_Λ additivityRightWitness) ≈ 0 :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_congr hleft hright) (by decide)
  have honezero : (1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hadd)
      (Q'.eqv_trans _ _ _ hsum hrhs)
  exact (by decide : ¬ ((1 : Q') ≈ 0)) honezero

/-- The pilot is genuinely non-unit despite its compatibility failure. -/
theorem threeSlice_weight_ne_one :
    (halfReferenceWeight 3).w ≠
      (prodAlg (fun _ => realEdge) 3).one := by
  intro h
  have h0 := congrFun h 0
  change Q'.mkPos 1 2 (by decide) = (1 : Q') at h0
  exact (by decide : ¬ (Q'.mkPos 1 2 (by decide) = (1 : Q'))) h0

theorem threeSlice_partition_not_eqv_one :
    ¬ ((halfReferenceWeight 3).Z ≈ 1) := by
  decide

/-! ## Corrected invariant: every compatible pure-product GNS is rank one -/

private theorem mul_eqv_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- If a GNS form factors through one scalar coordinate, equal coordinates are
radical-equivalent.  This algebraic lemma makes the rank-one collapse
independent of the chosen carrier module operations. -/
theorem rankOne_rad_of_coordinate_eqv
    (D : GNSData) (coordinate : D.V → Q')
    (form_rankOne : ∀ a b, D.B a b ≈ coordinate a * coordinate b)
    {a b : D.V} (hcoord : coordinate a ≈ coordinate b) :
    D.rad a b := by
  unfold GNSData.rad GNSData.sub
  refine Q'.eqv_trans _ _ _
    (D.B_add_left a (D.neg b) (D.add a (D.neg b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (D.B_add_right a a (D.neg b))
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_right a b)))
      (Q'.eqv_trans _ _ _ (D.B_add_right (D.neg b) a (D.neg b))
        (Q'.add_eqv_congr' (D.B_neg_left b a) (D.B_neg_neg b)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (form_rankOne a a)
        (Q'.neg_eqv_congr _ _ (form_rankOne a b)))
      (Q'.add_eqv_congr'
        (Q'.neg_eqv_congr _ _ (form_rankOne b a))
        (form_rankOne b b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (mul_eqv_congr hcoord hcoord)
        (Q'.neg_eqv_congr _ _ (mul_eqv_congr hcoord (Q'.eqv_refl _))))
      (Q'.add_eqv_congr'
        (Q'.neg_eqv_congr _ _ (mul_eqv_congr (Q'.eqv_refl _) hcoord))
        (Q'.eqv_refl _))) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_neg_self_eqv (coordinate b * coordinate b))
      (Q'.neg_add_self_eqv (coordinate b * coordinate b)))
    (QPoly.q_zero_add_eqv 0)

/-- Any carrier module on the same three pure-product observables that really
makes the interacting expectation linear still has a rank-one Wilson form.
The extra carrier coordinates cannot enter the physical Gram matrix. -/
theorem compatible_threeSlice_Wilson_form_rankOne
    (M : WilsonGNSData.CarrierModule (prodAlg (fun _ => realEdge) 3))
    (elin_congr : ∀ {a b}, M.veq a b →
      ((halfReferenceWeight 3).E_Λ a) ≈ ((halfReferenceWeight 3).E_Λ b))
    (elin_add : ∀ a b,
      ((halfReferenceWeight 3).E_Λ (M.add a b)) ≈
        ((halfReferenceWeight 3).E_Λ a + (halfReferenceWeight 3).E_Λ b))
    (elin_smul : ∀ (s : Q') a,
      ((halfReferenceWeight 3).E_Λ (M.smul s a)) ≈
        (s * (halfReferenceWeight 3).E_Λ a))
    (hconj : ∀ a b,
      ((halfReferenceWeight 3).E_Λ
        ((prodAlg (fun _ => realEdge) 3).mul
          ((prodAlg (fun _ => realEdge) 3).star a) b)) ≈
      ((halfReferenceWeight 3).E_Λ
        ((prodAlg (fun _ => realEdge) 3).mul
          ((prodAlg (fun _ => realEdge) 3).star b) a)))
    (a b : Nat → Q') :
    (WilsonGNSData.ofReferenceWeight (halfReferenceWeight 3) M
      elin_congr elin_add elin_smul hconj).toGNSData.B a b ≈
      threeSliceTotal a * threeSliceTotal b := by
  refine Q'.eqv_trans _ _ _ (halfReferenceWeight_three_E_eqv_total _) ?_
  exact threeSliceTotal_mul a b

/-- Hence cyclic time is radical-trivial for every genuinely compatible GNS
module on this pure-product ReferenceWeight, even if its carrier equivalence
retains the adjacent pair.  This is the sharp obstruction to a nonzero strict
compressed eigenmode in the three-slice pilot. -/
theorem compatible_threeSlice_rotation_radical
    (M : WilsonGNSData.CarrierModule (prodAlg (fun _ => realEdge) 3))
    (elin_congr : ∀ {a b}, M.veq a b →
      ((halfReferenceWeight 3).E_Λ a) ≈ ((halfReferenceWeight 3).E_Λ b))
    (elin_add : ∀ a b,
      ((halfReferenceWeight 3).E_Λ (M.add a b)) ≈
        ((halfReferenceWeight 3).E_Λ a + (halfReferenceWeight 3).E_Λ b))
    (elin_smul : ∀ (s : Q') a,
      ((halfReferenceWeight 3).E_Λ (M.smul s a)) ≈
        (s * (halfReferenceWeight 3).E_Λ a))
    (hconj : ∀ a b,
      ((halfReferenceWeight 3).E_Λ
        ((prodAlg (fun _ => realEdge) 3).mul
          ((prodAlg (fun _ => realEdge) 3).star a) b)) ≈
      ((halfReferenceWeight 3).E_Λ
        ((prodAlg (fun _ => realEdge) 3).mul
          ((prodAlg (fun _ => realEdge) 3).star b) a)))
    (a : Nat → Q') :
    (WilsonGNSData.ofReferenceWeight (halfReferenceWeight 3) M
      elin_congr elin_add elin_smul hconj).toGNSData.rad (rotate3 a) a := by
  let W := WilsonGNSData.ofReferenceWeight (halfReferenceWeight 3) M
    elin_congr elin_add elin_smul hconj
  apply rankOne_rad_of_coordinate_eqv W.toGNSData threeSliceTotal
  · intro x y
    exact compatible_threeSlice_Wilson_form_rankOne M elin_congr elin_add
      elin_smul hconj x y
  · exact threeSliceTotal_rotate a

end YMGap.Continuum.MultiSliceWilsonPositiveTimePilot

#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.halfReferenceWeight_three_E_eqv_total
#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.threeSlicePointwiseGeometry
#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.adjacentPair_rotates_nontrivially
#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.threeSlice_raw_character_resolution
#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.threeSlice_raw_reflected_positive
#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.no_threeSlice_pointwise_elin_add
#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.rankOne_rad_of_coordinate_eqv
#print axioms YMGap.Continuum.MultiSliceWilsonPositiveTimePilot.compatible_threeSlice_rotation_radical
