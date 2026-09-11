/-
# Factored positive-channel trace domination

The local Haar projectors at the links of a finite lattice have small positive
channel lists, but their global Cartesian product is exponentially large.  It
must not be materialized.  This leaf replaces that flat product by a nested
structural fold and lifts the square-root-free trace bound to it.

For local choice lists `C_1, ..., C_N`, `nestedListQSum` represents

  sum_{c_1 in C_1} ... sum_{c_N in C_N}

without constructing the list of global choices.  A factored resolution gives
one vector to each structurally selected channel word and a nonnegative local
weight.  The main theorem proves

  |nested trace| <= nested Gram mass.

When the global channel norm factors into the product of its local norms, a
second theorem identifies that nested mass with the product of the local
weighted masses.  This is the scalable analytic interface required by the
cutoff-one signed plaquette network.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.PositiveChannelTraceBound

namespace YMGap.Continuum.FactoredPositiveChannelTraceBound

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveChannelTraceBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Structural nested sums and products -/

/-- A nested finite sum over a list of local choice lists.  The selected word
is built only along the current recursion branch; no Cartesian list is ever
constructed. -/
def nestedListQSum {A : Type} :
    List (List A) -> (List A -> Q') -> Q'
  | [], family => family []
  | choices :: remaining, family =>
      listQSum (fun choice =>
        nestedListQSum remaining (fun selected =>
          family (choice :: selected))) choices

/-- Product of a scalar statistic along one selected channel word. -/
def listQProduct {A : Type} (factor : A -> Q') : List A -> Q'
  | [] => 1
  | value :: values => factor value * listQProduct factor values

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- Pointwise equivalence transports through the lightweight list sum. -/
theorem listQSum_eqv_congr {A : Type} {left right : A -> Q'}
    (h : forall value, left value ≈ right value) :
    forall values, listQSum left values ≈ listQSum right values
  | [] => Q'.eqv_refl 0
  | value :: values =>
      q_add_congr
        (h value) (listQSum_eqv_congr h values)

/-- Pointwise equivalence transports through every level of a nested sum. -/
theorem nestedListQSum_eqv_congr {A : Type} :
    forall (choiceLists : List (List A))
      (left right : List A -> Q'),
      (forall selected, left selected ≈ right selected) ->
      nestedListQSum choiceLists left ≈
        nestedListQSum choiceLists right
  | [], left, right, h => h []
  | choices :: remaining, left, right, h =>
      listQSum_eqv_congr (fun choice =>
        nestedListQSum_eqv_congr remaining
          (fun selected => left (choice :: selected))
          (fun selected => right (choice :: selected))
          (fun selected => h (choice :: selected))) choices

/-- Nested finite triangle/monotonicity in one statement. -/
theorem abs_nestedListQSum_le {A : Type} :
    forall (choiceLists : List (List A))
      (signed positive : List A -> Q'),
      (forall selected, Q'.abs (signed selected) <= positive selected) ->
      Q'.abs (nestedListQSum choiceLists signed) <=
        nestedListQSum choiceLists positive
  | [], signed, positive, h => h []
  | choices :: remaining, signed, positive, h => by
      exact Q'.le_trans' _ _ _
        (abs_listQSum_le
          (fun choice => nestedListQSum remaining (fun selected =>
            signed (choice :: selected))) choices)
        (listQSum_mono (fun choice =>
          abs_nestedListQSum_le remaining
            (fun selected => signed (choice :: selected))
            (fun selected => positive (choice :: selected))
            (fun selected => h (choice :: selected))) choices)

/-- A nonnegative local factor has a nonnegative product along every selected
word. -/
theorem listQProduct_nonneg {A : Type} {factor : A -> Q'}
    (hfactor : forall value, (0 : Q') <= factor value) :
    forall values, (0 : Q') <= listQProduct factor values
  | [] => by
      change (0 : Q') <= 1
      decide
  | value :: values =>
      Q'.mul_nonneg _ _ (hfactor value)
        (listQProduct_nonneg hfactor values)

/-! ## 2. Exact factorization of the nested positive mass -/

/-- A constant scalar pulls through a structural list sum. -/
theorem listQSum_mul_left {A : Type} (scalar : Q') (factor : A -> Q') :
    forall values,
      listQSum (fun value => scalar * factor value) values ≈
        scalar * listQSum factor values
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv scalar)
  | value :: values =>
      Q'.eqv_trans _ _ _
        (q_add_congr
          (Q'.eqv_refl (scalar * factor value))
          (listQSum_mul_left scalar factor values))
        (Q'.eqv_symm
          (Q'.mul_add_eqv scalar (factor value)
            (listQSum factor values)))

/-- Right-handed form of scalar extraction. -/
theorem listQSum_mul_right {A : Type} (factor : A -> Q') (scalar : Q')
    (values : List A) :
    listQSum (fun value => factor value * scalar) values ≈
      listQSum factor values * scalar := by
  refine Q'.eqv_trans _ _ _
    (listQSum_eqv_congr
      (fun value => Q'.mul_comm_eqv (factor value) scalar) values) ?_
  exact Q'.eqv_trans _ _ _
    (listQSum_mul_left scalar factor values)
    (Q'.mul_comm_eqv scalar (listQSum factor values))

/-- A constant scalar pulls through every nested choice level. -/
theorem nestedListQSum_mul_left {A : Type} :
    forall (choiceLists : List (List A)) (scalar : Q')
      (factor : List A -> Q'),
      nestedListQSum choiceLists (fun selected => scalar * factor selected) ≈
        scalar * nestedListQSum choiceLists factor
  | [], scalar, factor => Q'.eqv_refl (scalar * factor [])
  | choices :: remaining, scalar, factor => by
      refine Q'.eqv_trans _ _ _
        (listQSum_eqv_congr (fun choice =>
          nestedListQSum_mul_left remaining scalar
            (fun selected => factor (choice :: selected))) choices) ?_
      exact listQSum_mul_left scalar
        (fun choice => nestedListQSum remaining
          (fun selected => factor (choice :: selected))) choices

private theorem q_mul_four_swap (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ (a * (b * (c * d))) _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ (a * ((b * c) * d)) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ (a * ((c * b) * d)) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_right (b * c) (c * b) d
        (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ (a * (c * (b * d))) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- Products of two local statistics combine pointwise along a selected word. -/
theorem listQProduct_mul {A : Type} (left right : A -> Q') :
    forall selected,
      listQProduct left selected * listQProduct right selected ≈
        listQProduct (fun value => left value * right value) selected
  | [] => Q'.mul_one_eqv 1
  | value :: selected =>
      Q'.eqv_trans _ _ _
        (q_mul_four_swap (left value) (listQProduct left selected)
          (right value) (listQProduct right selected))
        (q_mul_congr (Q'.eqv_refl (left value * right value))
          (listQProduct_mul left right selected))

/-- The nested sum of a product statistic is exactly the product of the local
sums.  This is the non-materializing replacement for distributively forming a
Cartesian list of channel choices. -/
theorem nestedListQSum_product_eqv_product_localSums {A : Type}
    (factor : A -> Q') :
    forall choiceLists,
      nestedListQSum choiceLists (listQProduct factor) ≈
        listQProduct (fun choices => listQSum factor choices) choiceLists
  | [] => Q'.eqv_refl 1
  | choices :: remaining => by
      refine Q'.eqv_trans _ _ _
        (listQSum_eqv_congr (fun choice => by
          simpa only [listQProduct] using
            (nestedListQSum_mul_left remaining (factor choice)
              (listQProduct factor))) choices) ?_
      refine Q'.eqv_trans _ _ _
        (listQSum_mul_right factor
          (nestedListQSum remaining (listQProduct factor)) choices) ?_
      exact q_mul_congr
        (Q'.eqv_refl (listQSum factor choices))
        (nestedListQSum_product_eqv_product_localSums factor remaining)

/-! ## 3. Factored positive-channel resolutions -/

/-- A positive resolution represented by local channel lists rather than by
their global Cartesian product.  `vector` is evaluated only on one structural
choice word at a time. -/
structure FactoredPositiveChannelResolution {V A : Type}
    (F : PreInnerForm V) where
  channelChoices : List (List A)
  vector : List A -> V
  weight : A -> Q'
  weight_nonneg : forall channel, (0 : Q') <= weight channel

variable {V A : Type}

/-- Product of the local positive weights on one structural choice word. -/
def selectionWeight (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (selected : List A) : Q' :=
  listQProduct R.weight selected

/-- One global channel selected from a factored resolution. -/
def selectedPositiveChannel (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (selected : List A) : PositiveChannel V where
  vector := R.vector selected
  weight := selectionWeight F R selected
  weight_nonneg := listQProduct_nonneg R.weight_nonneg selected

/-- Signed trace represented by structural nested channel choices. -/
def factoredResolvedTrace (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (W : GramIsometry F) : Q' :=
  nestedListQSum R.channelChoices (fun selected =>
    channelTraceTerm F W (selectedPositiveChannel F R selected))

/-- Positive Gram mass represented by the same nested choices. -/
def factoredResolvedTraceMass (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F) : Q' :=
  nestedListQSum R.channelChoices (fun selected =>
    channelTraceMass F (selectedPositiveChannel F R selected))

/-- **Factored square-root-free trace domination.**  The proof is pointwise in
one selected channel word and then structural in the nested local choices. -/
theorem abs_factoredResolvedTrace_le_mass (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (W : GramIsometry F) :
    Q'.abs (factoredResolvedTrace F R W) <=
      factoredResolvedTraceMass F R := by
  unfold factoredResolvedTrace factoredResolvedTraceMass
  exact abs_nestedListQSum_le R.channelChoices _ _ (fun selected =>
    abs_channelTraceTerm_le_mass F W
      (selectedPositiveChannel F R selected))

/-! ## 4. Tensor-Gram mass factorization interface -/

/-- Product of the local weighted channel masses, one factor per link. -/
def productLocalTraceMass (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (localNorm : A -> Q') : Q' :=
  listQProduct
    (fun choices =>
      listQSum (fun channel => R.weight channel * localNorm channel) choices)
    R.channelChoices

/-- If the Gram norm of each global tensor channel is the product of its local
norms, then the nested resolved mass is exactly the product of the local
weighted masses.  The hypothesis is the concrete tensor-coordinate theorem
to be supplied by the Boolean wiring layer; no mass or rank conclusion is
stored in the resolution. -/
theorem factoredResolvedTraceMass_eqv_productLocalTraceMass
    (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (localNorm : A -> Q')
    (hTensorNorm : forall selected,
      F.B (R.vector selected) (R.vector selected) ≈
        listQProduct localNorm selected) :
    factoredResolvedTraceMass F R ≈
      productLocalTraceMass F R localNorm := by
  unfold factoredResolvedTraceMass productLocalTraceMass
  refine Q'.eqv_trans _ _ _
    (nestedListQSum_eqv_congr R.channelChoices _ _
      (fun selected => by
        unfold channelTraceMass selectedPositiveChannel selectionWeight
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (listQProduct R.weight selected) _ _
            (hTensorNorm selected)) ?_
        exact listQProduct_mul R.weight localNorm selected)) ?_
  exact nestedListQSum_product_eqv_product_localSums
    (fun channel => R.weight channel * localNorm channel)
    R.channelChoices

#print axioms nestedListQSum_eqv_congr
#print axioms abs_nestedListQSum_le
#print axioms nestedListQSum_product_eqv_product_localSums
#print axioms abs_factoredResolvedTrace_le_mass
#print axioms factoredResolvedTraceMass_eqv_productLocalTraceMass

end YMGap.Continuum.FactoredPositiveChannelTraceBound
