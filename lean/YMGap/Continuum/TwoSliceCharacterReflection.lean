/-
The strongest currently inhabitable interacting time-reflection model in the
`ReferenceWeight` substrate.

The repository's heat-kernel/Peter--Weyl data are `CReal`-valued external
Schur forms; they are not an inhabitant of the rational `ReferenceWeight`
interface.  The one concrete non-unit `ReferenceWeight` is
`halfReferenceWeight 2`, a two-factor product with weight `1/2` on each
factor.  Its raw pointwise carrier module is not compatible with the needed
linearity: the state of a pure tensor is the product of its two coordinates.

We first bank that obstruction exactly.  We then use the correct one-mode
tensor/character coordinate `a(0)*a(1)` as the carrier equivalence and module
coordinate.  On this repaired quotient module the existing interacting
weight has a genuine nonidentity two-slice swap geometry, an exact one-mode
finite character Gram resolution, and hence an inhabited `TimeHalfspaceLaw`
and completed transfer extension.  The swap is nontrivial on representatives
but acts trivially on the one-mode quotient; this limitation is exposed by an
exact radical theorem rather than hidden.

All declarations are constructive and axiom-clean modulo `propext` and
`Quot.sound`.
-/

import YMGap.Continuum.InteractingReflectionTimeLaw
import YMGap.Constructive.TrigAdd

namespace YMGap.Continuum.TwoSliceCharacterReflection

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.ReferenceWeightTransferConstruction
open YMGap.Continuum.InteractingReflectionTimeLaw
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

/-- The exact two-factor tensor/character coordinate. -/
def twoSliceCharacter (a : Nat → Q') : Q' := a 0 * a 1

/-- General normalization helper: if the unnormalized weighted expectation is
`Z*x`, normalization by the positive partition function returns `x`. -/
theorem referenceWeight_eqv_of_weighted_factor
    {A : ObsAlg} (R : ReferenceWeight A) (o : A.carrier) (x : Q')
    (h : (R.I₀.E (A.mul R.w o)).eqv (R.Z * x)) :
    (R.E_Λ o).eqv x := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (PlaquetteReweight.recip R.Z) h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (R.Z * x) (x * R.Z)
      (PlaquetteReweight.recip R.Z) (Q'.mul_comm_eqv R.Z x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv x R.Z (PlaquetteReweight.recip R.Z)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left x _ _
      (PlaquetteReweight.mul_recip_eqv_one R.Z_pos)) ?_
  exact Q'.mul_one_eqv x

/-- The actual normalized interacting expectation of the two-factor half
weight is exactly its one tensor-character coordinate. -/
theorem halfReferenceWeight_two_E_eqv_character (a : Nat → Q') :
    ((halfReferenceWeight 2).E_Λ a).eqv (twoSliceCharacter a) := by
  apply referenceWeight_eqv_of_weighted_factor
  let h : Q' := Q'.mkPos 1 2 (by decide)
  change (((1 : Q') * (h * a 0)) * (h * a 1)).eqv
    (((1 : Q') * (h * 1)) * (h * 1) * (a 0 * a 1))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (h * a 1) (Q'.one_mul_eqv (h * a 0))) ?_
  refine Q'.eqv_trans _ _ _ (TrigAdd.mul_shuffle_4 h (a 0) h (a 1)) ?_
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (a 0 * a 1)
      (Q'.mul_eqv_congr_right _ _ (h * 1) (Q'.one_mul_eqv (h * 1)))) ?_)
  refine Q'.mul_eqv_congr_right _ _ (a 0 * a 1) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (h * 1) (Q'.mul_one_eqv h))
    (Q'.mul_eqv_congr_left h _ _ (Q'.mul_one_eqv h))

/-! ## The precise obstruction in the repository's pointwise module -/

def leftPureTensor : Nat → Q' := fun i => if i = 0 then 1 else 0
def rightPureTensor : Nat → Q' := fun i => if i = 1 then 1 else 0

/-- Pointwise addition of pure tensors is not tensor-space addition: the
interacting product expectation is therefore not linear for the existing
`realProductCarrierModule 2`. -/
theorem no_halfReferenceWeight_pointwise_elin_add :
    (∀ a b,
      ((halfReferenceWeight 2).E_Λ ((realProductCarrierModule 2).add a b)).eqv
        ((halfReferenceWeight 2).E_Λ a + (halfReferenceWeight 2).E_Λ b)) → False := by
  intro H
  have hsum := H leftPureTensor rightPureTensor
  have hadd :
      ((halfReferenceWeight 2).E_Λ
        ((realProductCarrierModule 2).add leftPureTensor rightPureTensor)).eqv 1 :=
    Q'.eqv_trans _ _ _
      (halfReferenceWeight_two_E_eqv_character _)
      (by decide)
  have hleft : ((halfReferenceWeight 2).E_Λ leftPureTensor).eqv 0 :=
    Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character _) (by decide)
  have hright : ((halfReferenceWeight 2).E_Λ rightPureTensor).eqv 0 :=
    Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character _) (by decide)
  have hrhs :
      ((halfReferenceWeight 2).E_Λ leftPureTensor +
        (halfReferenceWeight 2).E_Λ rightPureTensor).eqv 0 :=
    Q'.eqv_trans _ _ _ (QPoly.q_add_congr hleft hright) (by decide)
  have honezero : (1 : Q').eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hadd) (Q'.eqv_trans _ _ _ hsum hrhs)
  exact (by decide : ¬ ((1 : Q').eqv 0)) honezero

/-! ## The tensor-character quotient module -/

/-- Canonical representative of a one-mode tensor-character amplitude. -/
def characterRep (q : Q') : Nat → Q' := fun i => if i = 0 then q else 1

theorem twoSliceCharacter_characterRep (q : Q') :
    (twoSliceCharacter (characterRep q)).eqv q := by
  change (q * 1).eqv q
  exact Q'.mul_one_eqv q

theorem characterRep_congr {q r : Q'} (h : q.eqv r) :
    (twoSliceCharacter (characterRep q)).eqv
      (twoSliceCharacter (characterRep r)) :=
  Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep q)
    (Q'.eqv_trans _ _ _ h (Q'.eqv_symm (twoSliceCharacter_characterRep r)))

theorem twoSliceCharacter_mul (a b : Nat → Q') :
    (twoSliceCharacter ((prodAlg (fun _ => realEdge) 2).mul a b)).eqv
      (twoSliceCharacter a * twoSliceCharacter b) := by
  change ((a 0 * b 0) * (a 1 * b 1)).eqv ((a 0 * a 1) * (b 0 * b 1))
  exact TrigAdd.mul_shuffle_4 (a 0) (b 0) (a 1) (b 1)

theorem twoSliceCharacter_swap (a : Nat → Q') :
    (twoSliceCharacter (swap01 a)).eqv (twoSliceCharacter a) := by
  change (a 1 * a 0).eqv (a 0 * a 1)
  exact Q'.mul_comm_eqv (a 1) (a 0)

/-- The correct module on the pure-tensor carrier identifies representatives
with the same exact two-factor character amplitude.  Vector operations are
performed on that amplitude and returned through `characterRep`. -/
def twoSliceCharacterModule :
    WilsonGNSData.CarrierModule (prodAlg (fun _ => realEdge) 2) where
  veq := fun a b => (twoSliceCharacter a).eqv (twoSliceCharacter b)
  veq_refl := fun a => Q'.eqv_refl (twoSliceCharacter a)
  veq_symm := fun h => Q'.eqv_symm h
  veq_trans := fun h k => Q'.eqv_trans _ _ _ h k
  zero := characterRep 0
  add := fun a b => characterRep (twoSliceCharacter a + twoSliceCharacter b)
  neg := fun a => characterRep (-(twoSliceCharacter a))
  smul := fun s a => characterRep (s * twoSliceCharacter a)
  add_congr := by
    intro a a' b b' ha hb
    exact characterRep_congr (QPoly.q_add_congr ha hb)
  neg_congr := by
    intro a a' h
    exact characterRep_congr (Q'.neg_eqv_congr _ _ h)
  smul_congr := by
    intro s a a' h
    exact characterRep_congr (Q'.mul_eqv_congr_left s _ _ h)
  add_assoc := by
    intro a b c
    refine Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (twoSliceCharacter_characterRep _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (twoSliceCharacter_characterRep _))) ?_
    exact Q'.eqv_symm (twoSliceCharacter_characterRep _)
  add_comm := by
    intro a b
    refine Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
    exact Q'.eqv_symm (twoSliceCharacter_characterRep _)
  zero_add := by
    intro a
    refine Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (twoSliceCharacter_characterRep 0)) ?_
    exact QPoly.q_zero_add_eqv _
  neg_add := by
    intro a
    refine Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (twoSliceCharacter_characterRep _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_self_eqv _) ?_
    exact Q'.eqv_symm (twoSliceCharacter_characterRep 0)
  mul_congr := by
    intro a a' b b' ha hb
    refine Q'.eqv_trans _ _ _ (twoSliceCharacter_mul a b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ ha) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hb) ?_
    exact Q'.eqv_symm (twoSliceCharacter_mul a' b')
  star_congr := fun h => h
  star_add := fun _ _ => Q'.eqv_refl _
  star_smul := fun _ _ => Q'.eqv_refl _
  mul_add_right := by
    intro a b c
    refine Q'.eqv_trans _ _ _ (twoSliceCharacter_mul _ c) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (twoSliceCharacter_characterRep _)) ?_
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul _ _ _) ?_
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_)
    exact QPoly.q_add_congr (twoSliceCharacter_mul a c) (twoSliceCharacter_mul b c)
  smul_mul := by
    intro s a b
    refine Q'.eqv_trans _ _ _ (twoSliceCharacter_mul _ b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (twoSliceCharacter_characterRep _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv s _ _) ?_
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_)
    exact Q'.mul_eqv_congr_left s _ _ (twoSliceCharacter_mul a b)

/-! ## Linearity and time geometry for the interacting weight -/

theorem twoSlice_elin_congr {a b : Nat → Q'}
    (h : twoSliceCharacterModule.veq a b) :
    ((halfReferenceWeight 2).E_Λ a).eqv ((halfReferenceWeight 2).E_Λ b) :=
  Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character a)
    (Q'.eqv_trans _ _ _ h
      (Q'.eqv_symm (halfReferenceWeight_two_E_eqv_character b)))

theorem twoSlice_elin_add (a b : Nat → Q') :
    ((halfReferenceWeight 2).E_Λ (twoSliceCharacterModule.add a b)).eqv
      ((halfReferenceWeight 2).E_Λ a + (halfReferenceWeight 2).E_Λ b) := by
  refine Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character _) ?_
  refine Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_
  exact Q'.eqv_symm (QPoly.q_add_congr
    (halfReferenceWeight_two_E_eqv_character a)
    (halfReferenceWeight_two_E_eqv_character b))

theorem twoSlice_elin_smul (s : Q') (a : Nat → Q') :
    ((halfReferenceWeight 2).E_Λ (twoSliceCharacterModule.smul s a)).eqv
      (s * (halfReferenceWeight 2).E_Λ a) := by
  refine Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character _) ?_
  refine Q'.eqv_trans _ _ _ (twoSliceCharacter_characterRep _) ?_
  exact Q'.eqv_symm (Q'.mul_eqv_congr_left s _ _
    (halfReferenceWeight_two_E_eqv_character a))

theorem twoSlice_hconj (a b : Nat → Q') :
    ((halfReferenceWeight 2).E_Λ
      ((prodAlg (fun _ => realEdge) 2).mul
        ((prodAlg (fun _ => realEdge) 2).star a) b)).eqv
    ((halfReferenceWeight 2).E_Λ
      ((prodAlg (fun _ => realEdge) 2).mul
        ((prodAlg (fun _ => realEdge) 2).star b) a)) := by
  refine Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character _) ?_
  refine Q'.eqv_trans _ _ _ (twoSliceCharacter_mul a b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (twoSliceCharacter_mul b a)) ?_
  exact Q'.eqv_symm (halfReferenceWeight_two_E_eqv_character _)

/-- The two-slice swap is the identity in the exact tensor-character
equivalence, although it remains a nonidentity raw observable map. -/
theorem twoSlice_swap_veq (a : Nat → Q') :
    twoSliceCharacterModule.veq (swap01 a) a :=
  twoSliceCharacter_swap a

/-- The existing non-unit interacting weight with its genuine period-two raw
swap, now equipped with the tensor-character module on which its expectation
is linear. -/
def twoSliceSwapCharacterGeometry : GeometryEnrichedReferenceWeight
    (halfReferenceWeight 2) twoSliceCharacterModule where
  timeExtent := 2
  timeExtent_pos := by decide
  action := halfSwapAction
  periodic := swap01_involutive
  map_veq := by
    intro a b h
    exact twoSliceCharacterModule.veq_trans (twoSlice_swap_veq a)
      (twoSliceCharacterModule.veq_trans h
        (twoSliceCharacterModule.veq_symm (twoSlice_swap_veq b)))
  map_add := by
    intro a b
    exact twoSliceCharacterModule.veq_trans
      (twoSlice_swap_veq (twoSliceCharacterModule.add a b))
      (twoSliceCharacterModule.add_congr
        (twoSliceCharacterModule.veq_symm (twoSlice_swap_veq a))
        (twoSliceCharacterModule.veq_symm (twoSlice_swap_veq b)))
  map_neg := by
    intro a
    exact twoSliceCharacterModule.veq_trans
      (twoSlice_swap_veq (twoSliceCharacterModule.neg a))
      (twoSliceCharacterModule.neg_congr
        (twoSliceCharacterModule.veq_symm (twoSlice_swap_veq a)))
  map_smul := by
    intro s a
    exact twoSliceCharacterModule.veq_trans
      (twoSlice_swap_veq (twoSliceCharacterModule.smul s a))
      (twoSliceCharacterModule.smul_congr s
        (twoSliceCharacterModule.veq_symm (twoSlice_swap_veq a)))

/-! ## The actual finite character Gram and Markov-square inhabitants -/

/-- The interacting reflected form of the period-two swap is exactly the
product of the two one-mode character amplitudes. -/
theorem twoSlice_reflected_form_eqv_product (a b : Nat → Q') :
    ((twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj).B
      (twoSliceSwapCharacterGeometry.action.hom.map a) b).eqv
      (twoSliceCharacter a * twoSliceCharacter b) := by
  change ((halfReferenceWeight 2).E_Λ
    ((prodAlg (fun _ => realEdge) 2).mul (swap01 a) b)).eqv
      (twoSliceCharacter a * twoSliceCharacter b)
  refine Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character _) ?_
  refine Q'.eqv_trans _ _ _ (twoSliceCharacter_mul (swap01 a) b) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (twoSliceCharacter_swap a)

/-- The reflected form is an exact one-mode finite character Gram sum. -/
theorem twoSlice_reflected_character_resolution (a b : Nat → Q') :
    ((twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj).B
      (twoSliceSwapCharacterGeometry.action.hom.map a) b).eqv
    (characterGramSum (fun x _ => twoSliceCharacter x) a b 1) := by
  refine Q'.eqv_trans _ _ _ (twoSlice_reflected_form_eqv_product a b) ?_
  change (twoSliceCharacter a * twoSliceCharacter b).eqv
    (0 + twoSliceCharacter a * twoSliceCharacter b)
  exact Q'.eqv_symm (QPoly.q_zero_add_eqv _)

/-- A genuine `FiniteCharacterGramLaw` inhabitant on the existing non-unit
interacting two-factor weight. -/
def twoSliceFiniteCharacterGramLaw :
    FiniteCharacterGramLaw twoSliceSwapCharacterGeometry twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj where
  modeCount := 1
  coordinate := fun a _ => twoSliceCharacter a
  reflected_character_resolution := twoSlice_reflected_character_resolution

/-- The canonical half-time representative carrying only the exact one-mode
character amplitude. -/
def twoSliceHalfTime (a : Nat → Q') : Nat → Q' :=
  characterRep (twoSliceCharacter a)

theorem twoSlice_halfTime_form_eqv_product (a b : Nat → Q') :
    ((twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj).B
      (twoSliceHalfTime a) (twoSliceHalfTime b)).eqv
      (twoSliceCharacter a * twoSliceCharacter b) := by
  change ((halfReferenceWeight 2).E_Λ
    ((prodAlg (fun _ => realEdge) 2).mul
      (twoSliceHalfTime a) (twoSliceHalfTime b))).eqv
      (twoSliceCharacter a * twoSliceCharacter b)
  refine Q'.eqv_trans _ _ _ (halfReferenceWeight_two_E_eqv_character _) ?_
  refine Q'.eqv_trans _ _ _
    (twoSliceCharacter_mul (twoSliceHalfTime a) (twoSliceHalfTime b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (twoSliceCharacter_characterRep _)) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (twoSliceCharacter_characterRep _)

/-- The same concrete model also inhabits the interacting Markov-square law:
the reflected form factors through the canonical half-time character
representative. -/
def twoSliceInteractingMarkovSquareLaw :
    InteractingMarkovSquareLaw twoSliceSwapCharacterGeometry twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj where
  halfTime := twoSliceHalfTime
  reflected_factor := fun a b =>
    Q'.eqv_trans _ _ _ (twoSlice_reflected_form_eqv_product a b)
      (Q'.eqv_symm (twoSlice_halfTime_form_eqv_product a b))

/-- The concrete interacting two-slice halfspace law, derived from its exact
finite character Gram identity. -/
def twoSliceTimeHalfspaceLaw :
    TimeHalfspaceLaw twoSliceSwapCharacterGeometry twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj :=
  twoSliceFiniteCharacterGramLaw.toTimeHalfspaceLaw

/-- The completed positive self-adjoint contraction for the concrete
interacting two-slice model. -/
def twoSliceTransferExtension :
    twoSliceSwapCharacterGeometry.TransferExtension twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj :=
  twoSliceTimeHalfspaceLaw.toTransferExtension

/-! ## Nondegeneracy and the exact limitation -/

/-- The model is genuinely reweighted: its Boltzmann weight is not the unit
observable. -/
theorem twoSlice_weight_ne_one :
    (halfReferenceWeight 2).w ≠ (prodAlg (fun _ => realEdge) 2).one := by
  intro h
  have h0 := congrFun h 0
  change Q'.mkPos 1 2 (by decide) = (1 : Q') at h0
  exact (by decide : ¬ (Q'.mkPos 1 2 (by decide) = (1 : Q'))) h0

/-- Its two-factor partition function is also genuinely non-unit. -/
theorem twoSlice_partition_not_eqv_one :
    ¬ ((halfReferenceWeight 2).Z).eqv 1 := by
  decide

/-- The one-mode carrier has a genuine unit-norm direction. -/
theorem twoSlice_character_unit_norm :
    ((twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj).B
      (characterRep 1) (characterRep 1)).eqv 1 := by
  refine Q'.eqv_trans _ _ _
    (twoSlice_halfTime_form_eqv_product (characterRep 1) (characterRep 1)) ?_
  decide

/-- The period-two swap is nonidentity on raw observable representatives. -/
theorem twoSlice_swap_raw_nontrivial :
    (identityAction (halfReferenceWeight 2)).hom.map ≠
      twoSliceSwapCharacterGeometry.action.hom.map :=
  identity_swap_ne

/-- Exact limitation: the positive isometric swap acts as identity after the
one-mode character equivalence.  Thus this inhabitant closes the finite
two-slice connector but does not manufacture a nontrivial excited transfer
spectrum. -/
theorem twoSlice_swap_character_trivial (a : Nat → Q') :
    twoSliceCharacterModule.veq
      (twoSliceSwapCharacterGeometry.action.hom.map a) a :=
  twoSlice_swap_veq a

/-- The same limitation stated in the actual Wilson radical. -/
theorem twoSlice_swap_rad (a : Nat → Q') :
    (twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj).toGNSData.rad
      (twoSliceSwapCharacterGeometry.action.hom.map a) a := by
  let W := twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
    twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj
  change (W.toGNSData.B
    (W.toGNSData.sub (twoSliceSwapCharacterGeometry.action.hom.map a) a)
    (W.toGNSData.sub (twoSliceSwapCharacterGeometry.action.hom.map a) a)).eqv 0
  have hsub : W.toGNSData.veq
      (W.toGNSData.sub (twoSliceSwapCharacterGeometry.action.hom.map a) a)
      (W.toGNSData.sub a a) :=
    W.toGNSData.add_congr (twoSlice_swap_veq a) (W.toGNSData.veq_refl _)
  exact Q'.eqv_trans _ _ _ (W.toGNSData.B_diag_congr hsub)
    (W.toGNSData.rad_refl a)

/-- Therefore the induced one-step map is exactly the identity on every dense
radical-quotient representative. -/
theorem twoSlice_quotientTimeShift_qmk_identity (a : Nat → Q') :
    twoSliceSwapCharacterGeometry.quotientTimeShift twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj
      ((twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
        twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj).toGNSData.qmk a) =
    (twoSliceSwapCharacterGeometry.toWilsonGNSData twoSlice_elin_congr
      twoSlice_elin_add twoSlice_elin_smul twoSlice_hconj).toGNSData.qmk a := by
  apply Quotient.sound
  exact twoSlice_swap_rad a

end YMGap.Continuum.TwoSliceCharacterReflection

#print axioms YMGap.Continuum.TwoSliceCharacterReflection.referenceWeight_eqv_of_weighted_factor
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.halfReferenceWeight_two_E_eqv_character
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.no_halfReferenceWeight_pointwise_elin_add
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSliceCharacterModule
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_elin_add
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSliceSwapCharacterGeometry
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_reflected_character_resolution
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSliceFiniteCharacterGramLaw
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSliceInteractingMarkovSquareLaw
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSliceTimeHalfspaceLaw
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSliceTransferExtension
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_weight_ne_one
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_partition_not_eqv_one
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_character_unit_norm
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_swap_raw_nontrivial
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_swap_character_trivial
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_swap_rad
#print axioms YMGap.Continuum.TwoSliceCharacterReflection.twoSlice_quotientTimeShift_qmk_identity
