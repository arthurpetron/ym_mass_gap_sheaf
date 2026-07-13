/-
The exact time-geometry boundary of the finite-volume ReferenceWeight substrate.

`ReferenceWeight` contains a static observable algebra, a reference functional,
an invariant weight, and its normalized interacting expectation.  It contains
no lattice sites, directions, time extent, or distinguished translation.  This
file makes that omission kernel-visible and then gives the smallest useful
geometry extension.

The concrete two-factor half-weight datum admits both the identity action and
the nontrivial swap of coordinates zero and one.  Both actions are strict
unital *-homomorphisms, fix the same weight, preserve the same reference
functional, and hence preserve the same interacting expectation, but their
maps are unequal.  Thus the existing ReferenceWeight fields do not determine a
one-step time translation.

`GeometryEnrichedReferenceWeight` adds a positive periodic time extent, the
selected state-preserving *-action, and its compatibility with the Wilson
carrier module.  From these data the action preserves the Wilson form and GNS
radical and therefore descends to the quotient.  A completed positive
self-adjoint contraction is still not present in the lattice substrate;
`TransferExtension` isolates exactly that remaining field and constructs the
previous `WilsonTimeTranslationPin` when it is supplied.

Finally `CharacterTransferExtension` records the independent normalized
character-coordinate Schur pin.  Its `formGap` is the existing genuine
operator-form normalized-character gap, now tied to the selected lattice
translation.

# Axiom gate

Every declaration below has axiom dependencies contained in
`{propext, Quot.sound}`.  There is no custom axiom, choice, `sorry`,
`native_decide`, or noncomputable definition.  Closed rational and natural
facts use kernel `decide` only.
-/

import YMGap.Continuum.WilsonGNSTransferUnderdetermination

namespace YMGap.Continuum.ReferenceWeightTimeGeometry

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

/-! ## State-preserving observable translations -/

/-- A candidate one-step time translation on a `ReferenceWeight`.  The
observable map is a strict unital *-homomorphism; the two extra fields say that
it fixes every remaining static datum from which `E_Λ` is computed. -/
structure ReferenceTranslationAction {A : ObsAlg} (R : ReferenceWeight A) : Type where
  hom : ObsHom A A
  weight_fixed : hom.map R.w = R.w
  reference_invariant : ∀ a, (R.I₀.E (hom.map a)).eqv (R.I₀.E a)

/-- Fixing the weight and reference functional forces invariance of the actual
normalized interacting expectation. -/
theorem ReferenceTranslationAction.interacting_invariant
    {A : ObsAlg} {R : ReferenceWeight A} (T : ReferenceTranslationAction R)
    (a : A.carrier) : (R.E_Λ (T.hom.map a)).eqv (R.E_Λ a) := by
  change (R.I₀.E (A.mul R.w (T.hom.map a)) * PlaquetteReweight.recip R.Z).eqv
    (R.I₀.E (A.mul R.w a) * PlaquetteReweight.recip R.Z)
  refine Q'.mul_eqv_congr_right _ _ (PlaquetteReweight.recip R.Z) ?_
  have h := T.reference_invariant (A.mul R.w a)
  rw [T.hom.map_mul, T.weight_fixed] at h
  exact h

/-- The identity is always one state-preserving action. -/
def identityAction {A : ObsAlg} (R : ReferenceWeight A) : ReferenceTranslationAction R where
  hom := ObsHom.idHom A
  weight_fixed := rfl
  reference_invariant := fun a => Q'.eqv_refl (R.I₀.E a)

/-! ## A concrete ambiguity on one fixed ReferenceWeight -/

/-- Exchange coordinates zero and one, fixing all later coordinates. -/
def swapIndex : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

theorem swapIndex_involutive (i : Nat) : swapIndex (swapIndex i) = i := by
  cases i with
  | zero => rfl
  | succ i => cases i with
    | zero => rfl
    | succ i => rfl

/-- Coordinate pullback along `swapIndex`. -/
def swap01 (a : Nat → Q') : Nat → Q' := fun i => a (swapIndex i)

theorem swap01_involutive (a : Nat → Q') : swap01 (swap01 a) = a := by
  funext i
  change a (swapIndex (swapIndex i)) = a i
  rw [swapIndex_involutive]

/-- The swap is a strict unital *-endomorphism of the two-factor real product
observable algebra. -/
def swapHom : ObsHom (prodAlg (fun _ => realEdge) 2) (prodAlg (fun _ => realEdge) 2) where
  map := swap01
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

/-- The two-factor reference product is symmetric under the swap. -/
theorem halfReferenceWeight_two_reference_swap_invariant (a : Nat → Q') :
    (((halfReferenceWeight 2).I₀.E (swap01 a)).eqv
      ((halfReferenceWeight 2).I₀.E a)) := by
  change (((1 : Q') * a 1) * a 0) ≈ (((1 : Q') * a 0) * a 1)
  refine Q'.eqv_trans _ (a 1 * a 0) _
    (Q'.mul_eqv_congr_right _ _ (a 0) (Q'.one_mul_eqv (a 1))) ?_
  refine Q'.eqv_trans _ (a 0 * a 1) _ (Q'.mul_comm_eqv _ _) ?_
  exact Q'.eqv_symm
    (Q'.mul_eqv_congr_right _ _ (a 1) (Q'.one_mul_eqv (a 0)))

theorem halfWeight_two_swap_fixed :
    swap01 (halfReferenceWeight 2).w = (halfReferenceWeight 2).w := by
  rfl

/-- The nontrivial swap action on the exact same half-weight datum. -/
def halfSwapAction : ReferenceTranslationAction (halfReferenceWeight 2) where
  hom := swapHom
  weight_fixed := halfWeight_two_swap_fixed
  reference_invariant := halfReferenceWeight_two_reference_swap_invariant

/-- A coordinate observable separating identity from swap. -/
def witnessObs : Nat → Q' := fun i => if i = 0 then 0 else 1

/-- The two state-preserving *-actions on the same `ReferenceWeight` are
genuinely different. -/
theorem identity_swap_ne :
    (identityAction (halfReferenceWeight 2)).hom.map ≠ halfSwapAction.hom.map := by
  intro h
  have hf := congrFun h witnessObs
  have h0 := congrFun hf 0
  exact (by decide : ¬ ((0 : Q') = (1 : Q'))) h0

/-! ## Minimal periodic time geometry -/

/-- Pointwise constructive module structure for the product diagnostic. -/
def realProductCarrierModule (n : Nat) :
    WilsonGNSData.CarrierModule (prodAlg (fun _ => realEdge) n) where
  veq := fun (a b : Nat → Q') => ∀ i, (a i).eqv (b i)
  veq_refl := fun (a : Nat → Q') i => Q'.eqv_refl (a i)
  veq_symm := fun h i => Q'.eqv_symm (h i)
  veq_trans := fun h₁ h₂ i => Q'.eqv_trans _ _ _ (h₁ i) (h₂ i)
  zero := (fun _ => (0 : Q') : Nat → Q')
  add := fun (a b : Nat → Q') i => a i + b i
  neg := fun (a : Nat → Q') i => -(a i)
  smul := fun s (a : Nat → Q') i => s * a i
  add_congr := fun {_ _ _ _} ha hb i => QPoly.q_add_congr (ha i) (hb i)
  neg_congr := fun {_ _} h i => Q'.neg_eqv_congr _ _ (h i)
  smul_congr := fun s {_ _} h i => Q'.mul_eqv_congr_left s _ _ (h i)
  add_assoc := fun (a b c : Nat → Q') i => Q'.add_assoc_eqv (a i) (b i) (c i)
  add_comm := fun (a b : Nat → Q') i => Q'.add_comm_eqv (a i) (b i)
  zero_add := fun (a : Nat → Q') i => QPoly.q_zero_add_eqv (a i)
  neg_add := fun (a : Nat → Q') i => Q'.neg_add_self_eqv (a i)
  mul_congr := fun {_ _ _ _} ha hb i => Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (ha i))
    (Q'.mul_eqv_congr_left _ _ _ (hb i))
  star_congr := fun {_ _} h i => h i
  star_add := fun (a b : Nat → Q') i => Q'.eqv_refl (a i + b i)
  star_smul := fun s (a : Nat → Q') i => Q'.eqv_refl (s * a i)
  mul_add_right := fun (a b c : Nat → Q') i => QPoly.q_add_mul (a i) (b i) (c i)
  smul_mul := fun s (a b : Nat → Q') i => Q'.mul_assoc_eqv s (a i) (b i)

/-- Iteration convention for a one-step periodic time action. -/
def iterateTau {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => f (iterateTau f n a)

/-- Minimal geometry absent from `ReferenceWeight`: a nonempty periodic time
circle, its selected one-step state-preserving *-action, and compatibility with
the additive/scalar Wilson carrier structure. -/
structure GeometryEnrichedReferenceWeight {A : ObsAlg} (R : ReferenceWeight A)
    (M : WilsonGNSData.CarrierModule A) : Type where
  timeExtent : Nat
  timeExtent_pos : 0 < timeExtent
  action : ReferenceTranslationAction R
  periodic : ∀ a, iterateTau action.hom.map timeExtent a = a
  map_veq : ∀ {a b}, M.veq a b → M.veq (action.hom.map a) (action.hom.map b)
  map_add : ∀ a b, M.veq (action.hom.map (M.add a b))
    (M.add (action.hom.map a) (action.hom.map b))
  map_neg : ∀ a, M.veq (action.hom.map (M.neg a)) (M.neg (action.hom.map a))
  map_smul : ∀ s a, M.veq (action.hom.map (M.smul s a))
    (M.smul s (action.hom.map a))

theorem GeometryEnrichedReferenceWeight.map_sub
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M) (a b : A.carrier) :
    M.veq (G.action.hom.map (M.add a (M.neg b)))
      (M.add (G.action.hom.map a) (M.neg (G.action.hom.map b))) := by
  exact M.veq_trans (G.map_add a (M.neg b))
    (M.add_congr (M.veq_refl _) (G.map_neg b))

/-- Period-one identity geometry on the fixed two-factor datum. -/
def halfIdentityGeometry : GeometryEnrichedReferenceWeight
    (halfReferenceWeight 2) (realProductCarrierModule 2) where
  timeExtent := 1
  timeExtent_pos := by decide
  action := identityAction _
  periodic := fun _ => rfl
  map_veq := fun h => h
  map_add := fun _ _ i => Q'.eqv_refl _
  map_neg := fun _ i => Q'.eqv_refl _
  map_smul := fun _ _ i => Q'.eqv_refl _

/-- Period-two swap geometry on the exact same datum and module. -/
def halfSwapGeometry : GeometryEnrichedReferenceWeight
    (halfReferenceWeight 2) (realProductCarrierModule 2) where
  timeExtent := 2
  timeExtent_pos := by decide
  action := halfSwapAction
  periodic := swap01_involutive
  map_veq := fun h i => h (swapIndex i)
  map_add := fun _ _ i => Q'.eqv_refl _
  map_neg := fun _ i => Q'.eqv_refl _
  map_smul := fun _ _ i => Q'.eqv_refl _

/-- Machine-checked underdetermination after requiring all static and module
compatibility laws: the same data still support unequal time actions. -/
theorem halfReferenceWeight_two_time_geometries :
    halfIdentityGeometry.action.hom.map ≠ halfSwapGeometry.action.hom.map :=
  identity_swap_ne

/-- The nontrivial action preserves the actual normalized interacting state. -/
theorem halfSwap_interacting_invariant (a : Nat → Q') :
    ((halfReferenceWeight 2).E_Λ (halfSwapAction.hom.map a)).eqv
      ((halfReferenceWeight 2).E_Λ a) :=
  halfSwapAction.interacting_invariant a

/-! ## Wilson form and radical descent -/

/-- Attach the already-required linearity and conjugate-symmetry laws of the
interacting expectation, producing the actual `E_Λ` Wilson GNS datum. -/
def GeometryEnrichedReferenceWeight.toWilsonGNSData
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (_G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))) :
    WilsonGNSData A :=
  WilsonGNSData.ofReferenceWeight R M elin_congr elin_add elin_smul hconj

/-- A state-preserving *-action is an isometry of the finite-volume Wilson
form. -/
theorem GeometryEnrichedReferenceWeight.wilsonForm_translation_invariant
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (a b : A.carrier) :
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map a) (G.action.hom.map b)).eqv
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B a b) := by
  change (R.E_Λ (A.mul (A.star (G.action.hom.map a))
      (G.action.hom.map b))).eqv
    (R.E_Λ (A.mul (A.star a) b))
  have hmap : G.action.hom.map (A.mul (A.star a) b) =
      A.mul (A.star (G.action.hom.map a)) (G.action.hom.map b) := by
    rw [G.action.hom.map_mul, G.action.hom.map_star]
  rw [← hmap]
  exact G.action.interacting_invariant _

/-- The selected lattice translation preserves the Wilson radical.  This is
proved directly from state invariance and module compatibility, before any
completed transfer operator is assumed. -/
theorem GeometryEnrichedReferenceWeight.translation_preserves_rad
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    {a b : A.carrier}
    (h : (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.rad a b) :
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.rad
      (G.action.hom.map a) (G.action.hom.map b) := by
  let W := G.toWilsonGNSData elin_congr elin_add elin_smul hconj
  change (W.toGNSData.B
    (W.toGNSData.sub (G.action.hom.map a) (G.action.hom.map b))
    (W.toGNSData.sub (G.action.hom.map a) (G.action.hom.map b))).eqv 0
  have hsub : W.toGNSData.veq
      (G.action.hom.map (W.toGNSData.sub a b))
      (W.toGNSData.sub (G.action.hom.map a) (G.action.hom.map b)) := by
    exact G.map_sub a b
  refine Q'.eqv_trans _ _ _
    (W.toGNSData.B_diag_congr (W.toGNSData.veq_symm hsub)) ?_
  refine Q'.eqv_trans _ _ _
    (G.wilsonForm_translation_invariant elin_congr elin_add elin_smul hconj
      (W.toGNSData.sub a b) (W.toGNSData.sub a b)) ?_
  exact h

/-- The induced one-step action on radical classes. -/
def GeometryEnrichedReferenceWeight.quotientTimeShift
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))) :
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.QuotSpace →
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.QuotSpace :=
  Quotient.lift
    (fun a =>
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.qmk
        (G.action.hom.map a))
    (fun _ _ h => Quotient.sound
      (G.translation_preserves_rad elin_congr elin_add elin_smul hconj h))

theorem GeometryEnrichedReferenceWeight.quotientTimeShift_qmk
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (a : A.carrier) :
    G.quotientTimeShift elin_congr elin_add elin_smul hconj
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.qmk a) =
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.qmk
      (G.action.hom.map a) := rfl

/-! ## Exact remaining completion and character fields -/

/-- The exact field still needed after radical descent: a completed positive
self-adjoint contraction extending the selected observable translation on the
dense image.  Positivity, self-adjointness, and contractivity are fields of
`TransferOperator`, not hidden assumptions here. -/
structure GeometryEnrichedReferenceWeight.TransferExtension
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))) : Type where
  op : TransferOperator
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.gnsComplete
  dense_intertwines : ∀ a,
    op.T (embedV
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData a) =
    embedV (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
      (G.action.hom.map a)

/-- Supplying the exact completion field constructs the repaired Wilson time
pin with `tau` definitionally equal to the selected lattice action. -/
def GeometryEnrichedReferenceWeight.TransferExtension.toWilsonTimeTranslationPin
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))}
    (X : G.TransferExtension elin_congr elin_add elin_smul hconj) :
    WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj) where
  tau := G.action.hom.map
  op := X.op
  dense_intertwines := X.dense_intertwines

/-- The independent character-coordinate bridge required to identify the
selected transfer's normalized character spectrum. -/
structure GeometryEnrichedReferenceWeight.CharacterTransferExtension
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (w t : Q') (ht : (0 : Q') <= t) (N : Nat) : Type where
  transfer : G.TransferExtension elin_congr elin_add elin_smul hconj
  diagonal : PhysicalWilsonBridge.PhysicalCharacterCoordinateMap
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.gnsComplete
    transfer.op w t ht N

def GeometryEnrichedReferenceWeight.CharacterTransferExtension.toWilsonCharacterSpectrumPin
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))}
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    (X : G.CharacterTransferExtension elin_congr elin_add elin_smul hconj
      w t ht N) :
    WilsonGNSTransferUnderdetermination.WilsonCharacterSpectrumPin
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj)
      X.transfer.toWilsonTimeTranslationPin w t ht N where
  diagonal := X.diagonal

/-- Once the completion and coordinate fields are supplied, the selected
lattice translation obtains the genuine normalized-character operator-form
gap. -/
def GeometryEnrichedReferenceWeight.CharacterTransferExtension.formGap
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))}
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    (X : G.CharacterTransferExtension elin_congr elin_add elin_smul hconj
      w t ht N)
    (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q')) :
    TransferFormGapResidual
      (X.transfer.toWilsonTimeTranslationPin.normalizedCharacterGapData
        (N := N) hw0 hw1) :=
  X.toWilsonCharacterSpectrumPin.formGap hw0 hw1

end YMGap.Continuum.ReferenceWeightTimeGeometry

#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.ReferenceTranslationAction
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.ReferenceTranslationAction.interacting_invariant
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.identityAction
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.swapIndex_involutive
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.swap01_involutive
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.swapHom
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.halfReferenceWeight_two_reference_swap_invariant
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.halfSwapAction
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.identity_swap_ne
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.realProductCarrierModule
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.halfIdentityGeometry
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.halfSwapGeometry
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.halfReferenceWeight_two_time_geometries
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.halfSwap_interacting_invariant
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.toWilsonGNSData
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.wilsonForm_translation_invariant
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.translation_preserves_rad
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.quotientTimeShift
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.quotientTimeShift_qmk
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.TransferExtension
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.TransferExtension.toWilsonTimeTranslationPin
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.CharacterTransferExtension
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.CharacterTransferExtension.toWilsonCharacterSpectrumPin
#print axioms YMGap.Continuum.ReferenceWeightTimeGeometry.GeometryEnrichedReferenceWeight.CharacterTransferExtension.formGap
