/-
A constructive repair of the positive-time transfer interface.

The ambient Euclidean time translation remains a state-preserving isometric
automorphism.  The physical transfer is instead the compression of that
automorphism to a positive-time carrier.  Reflection positivity supplies the
positive-time GNS form; an exact finite weighted-Gram identity proves transfer
positivity and self-adjointness, while an exact orthogonal decomposition proves
contractivity.  None of those three operator properties is assumed.

The interface is inhabited by an exact rational model.  Ambient time swaps an
excited coordinate with an auxiliary coordinate.  Compression to the
positive-time plane has vacuum eigenvalue 1 and a genuine non-vacuum
eigenvalue 0.  Thus `0 <= lambda < 1` holds without any measured constant.
All identities are in `Q'`.

No classical choice, measured input, or unproved spectral premise is used.
Axiom dependencies are contained in `{propext, Quot.sound}`.
-/

import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.GNSDynamics
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.PositiveTimeCompressedTransfer

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

/- A small exact rational ring normalizer.  It only unfolds the substrate's
cross-multiplication representation and closes by associativity/commutativity. -/
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Finite exact weighted Gram sums -/

def weightedGram {V : Type} (coordinate : V → Nat → Q') (weight : Nat → Q')
    (a b : V) : Nat → Q'
  | 0 => 0
  | n + 1 => weightedGram coordinate weight a b n
      + weight n * (coordinate a n * coordinate b n)

theorem weightedGram_symm {V : Type} (coordinate : V → Nat → Q')
    (weight : Nat → Q') (a b : V) : ∀ n,
    weightedGram coordinate weight a b n ≈ weightedGram coordinate weight b a n
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      exact Q'.add_eqv_congr'
        (weightedGram_symm coordinate weight a b n)
        (Q'.mul_eqv_congr_left (weight n) _ _
          (Q'.mul_comm_eqv (coordinate a n) (coordinate b n)))

theorem weightedGram_diag_nonneg {V : Type} (coordinate : V → Nat → Q')
    (weight : Nat → Q') (hweight : ∀ i, (0 : Q') ≤ weight i) (a : V) : ∀ n,
    (0 : Q') ≤ weightedGram coordinate weight a a n
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.zero_le_add _ _ (weightedGram_diag_nonneg coordinate weight hweight a n)
        (Q'.mul_nonneg _ _ (hweight n)
          (SumOfSquares.q_mul_self_nonneg (coordinate a n)))

/-! ## Direct sums of constructive GNS data -/

/-- Orthogonal direct sum of two rational GNS data. -/
def gnsProduct (D E : GNSData) : GNSData where
  V := D.V × E.V
  veq := fun a b => D.veq a.1 b.1 ∧ E.veq a.2 b.2
  veq_refl := fun a => ⟨D.veq_refl a.1, E.veq_refl a.2⟩
  veq_symm := fun h => ⟨D.veq_symm h.1, E.veq_symm h.2⟩
  veq_trans := fun h₁ h₂ => ⟨D.veq_trans h₁.1 h₂.1, E.veq_trans h₁.2 h₂.2⟩
  zero := (D.zero, E.zero)
  add := fun a b => (D.add a.1 b.1, E.add a.2 b.2)
  neg := fun a => (D.neg a.1, E.neg a.2)
  smul := fun s a => (D.smul s a.1, E.smul s a.2)
  add_congr := fun ha hb =>
    ⟨D.add_congr ha.1 hb.1, E.add_congr ha.2 hb.2⟩
  neg_congr := fun h => ⟨D.neg_congr h.1, E.neg_congr h.2⟩
  smul_congr := fun s {a a'} h =>
    ⟨D.smul_congr s h.1, E.smul_congr s h.2⟩
  add_assoc := fun a b c => ⟨D.add_assoc a.1 b.1 c.1, E.add_assoc a.2 b.2 c.2⟩
  add_comm := fun a b => ⟨D.add_comm a.1 b.1, E.add_comm a.2 b.2⟩
  zero_add := fun a => ⟨D.zero_add a.1, E.zero_add a.2⟩
  neg_add := fun a => ⟨D.neg_add a.1, E.neg_add a.2⟩
  B := fun a b => D.B a.1 b.1 + E.B a.2 b.2
  B_congr_left := fun b h => Q'.add_eqv_congr'
    (D.B_congr_left b.1 h.1) (E.B_congr_left b.2 h.2)
  B_add_left := fun a b c => by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (D.B_add_left a.1 b.1 c.1)
        (E.B_add_left a.2 b.2 c.2)) ?_
    exact QPoly.q_interchange (D.B a.1 c.1) (D.B b.1 c.1)
      (E.B a.2 c.2) (E.B b.2 c.2)
  B_smul_left := fun s a b => by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (D.B_smul_left s a.1 b.1)
        (E.B_smul_left s a.2 b.2)) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv s (D.B a.1 b.1) (E.B a.2 b.2))
  B_symm := fun a b => Q'.add_eqv_congr' (D.B_symm a.1 b.1) (E.B_symm a.2 b.2)
  self_nonneg := fun a => Q'.zero_le_add _ _ (D.self_nonneg a.1) (E.self_nonneg a.2)

/-! ## Ambient time/reflection and positive-time compression -/

/-- Ambient state-preserving Euclidean time is an isometric module
automorphism.  Reflection is kept separate and conjugates time to its inverse. -/
structure AmbientTimeReflection where
  space : GNSData
  tau : space.V → space.V
  tauInv : space.V → space.V
  theta : space.V → space.V
  tau_map_veq : ∀ {a b}, space.veq a b → space.veq (tau a) (tau b)
  tau_map_add : ∀ a b, space.veq (tau (space.add a b))
    (space.add (tau a) (tau b))
  tau_map_neg : ∀ a, space.veq (tau (space.neg a)) (space.neg (tau a))
  tau_map_smul : ∀ s a, space.veq (tau (space.smul s a)) (space.smul s (tau a))
  tau_left_inv : ∀ a, space.veq (tauInv (tau a)) a
  tau_right_inv : ∀ a, space.veq (tau (tauInv a)) a
  tau_isometry : ∀ a b, (space.B (tau a) (tau b)).eqv (space.B a b)
  theta_involutive : ∀ a, space.veq (theta (theta a)) a
  theta_time_inverse : ∀ a, space.veq (theta (tau (theta a))) (tauInv a)

/-- The repaired bridge.  `transfer` is the projection of ambient time onto
the positive-time carrier.  Positivity is certified by a finite weighted Gram
identity, while contraction is certified by an orthogonal residual
decomposition.  These are exact identities, not operator-property fields. -/
structure PositiveTimeCompression (A : AmbientTimeReflection) where
  positive : GNSData
  embed : positive.V → A.space.V
  project : A.space.V → positive.V
  transfer : positive.V → positive.V
  residual : positive.V → A.space.V
  embed_form : ∀ a b,
    (A.space.B (embed a) (embed b)).eqv (positive.B a b)
  reflected_form : ∀ a b,
    (A.space.B (A.theta (embed a)) (embed b)).eqv (positive.B a b)
  project_embed : ∀ a, positive.veq (project (embed a)) a
  transfer_projected_time : ∀ a,
    positive.veq (transfer a) (project (A.tau (embed a)))
  transfer_map_veq : ∀ {a b}, positive.veq a b →
    positive.veq (transfer a) (transfer b)
  transfer_map_zero : positive.veq (transfer positive.zero) positive.zero
  transfer_map_add : ∀ a b, positive.veq (transfer (positive.add a b))
    (positive.add (transfer a) (transfer b))
  transfer_map_neg : ∀ a,
    positive.veq (transfer (positive.neg a)) (positive.neg (transfer a))
  transfer_map_smul : ∀ s a, positive.veq (transfer (positive.smul s a))
    (positive.smul s (transfer a))
  compressed_decomposition : ∀ a, A.space.veq (A.tau (embed a))
    (A.space.add (embed (transfer a)) (residual a))
  compressed_orthogonal : ∀ a,
    (A.space.B (embed (transfer a)) (residual a)).eqv 0
  modeCount : Nat
  coordinate : positive.V → Nat → Q'
  modeWeight : Nat → Q'
  modeWeight_nonneg : ∀ i, (0 : Q') ≤ modeWeight i
  transfer_weightedGram : ∀ a b,
    (positive.B (transfer a) b).eqv
      (weightedGram coordinate modeWeight a b modeCount)

/-- Public positive-time transfer interface: the name emphasizes the physical
operator, while the defining implementation records its compression data. -/
abbrev PositiveTimeTransfer := PositiveTimeCompression

namespace PositiveTimeCompression

variable {A : AmbientTimeReflection} (C : PositiveTimeCompression A)

theorem transfer_map_sub (a b : C.positive.V) :
    C.positive.veq (C.transfer (C.positive.sub a b))
      (C.positive.sub (C.transfer a) (C.transfer b)) :=
  C.positive.veq_trans (C.transfer_map_add a (C.positive.neg b))
    (C.positive.add_congr (C.positive.veq_refl _)
      (C.transfer_map_neg b))

/-- The positive-time OS form really is reflection-positive in the ambient
reflection geometry. -/
theorem reflected_nonneg (a : C.positive.V) :
    (0 : Q') ≤ A.space.B (A.theta (C.embed a)) (C.embed a) :=
  le_of_le_eqv (C.positive.self_nonneg a)
    (Q'.eqv_symm (C.reflected_form a a))

/-- The weighted character Gram identity derives representative transfer
self-adjointness. -/
theorem transfer_selfAdjoint (a b : C.positive.V) :
    (C.positive.B (C.transfer a) b).eqv
      (C.positive.B a (C.transfer b)) := by
  refine Q'.eqv_trans _ _ _ (C.transfer_weightedGram a b) ?_
  refine Q'.eqv_trans _ _ _
    (weightedGram_symm C.coordinate C.modeWeight a b C.modeCount) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (C.transfer_weightedGram b a)) ?_
  exact C.positive.B_symm (C.transfer b) a

/-- The same exact weighted Gram identity derives transfer positivity. -/
theorem transfer_positive (a : C.positive.V) :
    (0 : Q') ≤ C.positive.B (C.transfer a) a :=
  le_of_le_eqv
    (weightedGram_diag_nonneg C.coordinate C.modeWeight C.modeWeight_nonneg
      a C.modeCount)
    (Q'.eqv_symm (C.transfer_weightedGram a a))

/-- Orthogonal Pythagoras in an arbitrary constructive GNS datum. -/
theorem diag_add_of_orthogonal (D : GNSData) (a r : D.V)
    (h : (D.B a r).eqv 0) :
    (D.B (D.add a r) (D.add a r)).eqv (D.B a a + D.B r r) := by
  refine Q'.eqv_trans _ _ _ (D.B_add_left a r (D.add a r)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (D.B_add_right a a r) (D.B_add_right r a r)) ?_
  have hr : (D.B r a).eqv 0 := Q'.eqv_trans _ _ _ (D.B_symm r a) h
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) h)
      (Q'.add_eqv_congr' hr (Q'.eqv_refl _))) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (QPoly.q_add_zero_eqv _) (QPoly.q_zero_add_eqv _))
    (Q'.eqv_refl _)

/-- The ambient isometry and its exact orthogonal compression decomposition
derive the norm split; no contraction inequality is stored in the interface. -/
theorem transfer_norm_split (a : C.positive.V) :
    (C.positive.B a a).eqv
      (C.positive.B (C.transfer a) (C.transfer a)
        + A.space.B (C.residual a) (C.residual a)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (C.embed_form a a)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (A.tau_isometry (C.embed a) (C.embed a))) ?_
  refine Q'.eqv_trans _ _ _
    (A.space.B_diag_congr (C.compressed_decomposition a)) ?_
  refine Q'.eqv_trans _ _ _
    (diag_add_of_orthogonal A.space (C.embed (C.transfer a))
      (C.residual a) (C.compressed_orthogonal a)) ?_
  exact Q'.add_eqv_congr' (C.embed_form (C.transfer a) (C.transfer a))
    (Q'.eqv_refl _)

/-- Pythagoras derives representative contractivity. -/
theorem transfer_contraction (a : C.positive.V) :
    C.positive.B (C.transfer a) (C.transfer a) ≤ C.positive.B a a := by
  refine Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (A.space.self_nonneg (C.residual a))) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (C.transfer_norm_split a))

/-- The compressed transfer contracts squared distances, the exact input
needed to descend it to the constructive completion. -/
theorem transfer_distSq_contraction (a b : C.positive.V) :
    C.positive.distSqQ (C.transfer a) (C.transfer b) ≤
      C.positive.distSqQ a b := by
  have hsub := C.transfer_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (C.positive.B_diag_congr hsub))
    (C.transfer_contraction (C.positive.sub a b))

/-! ## Sound descent to the existing constructive GNS completion -/

def applyCauchy (x : CauchyGNS C.positive) : CauchyGNS C.positive where
  seq := fun n => C.transfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro ε hε p q hp hq
    exact Q'.le_trans' _ _ _
      (C.transfer_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy ε hε p q hp hq)

theorem applyCauchy_null {x y : CauchyGNS C.positive}
    (h : CauchyNull C.positive x y) :
    CauchyNull C.positive (C.applyCauchy x) (C.applyCauchy y) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (C.transfer_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

/-- The compressed transfer on the completion. -/
def completedTransfer : GNSCompletionSpace C.positive → GNSCompletionSpace C.positive :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid C.positive) (C.applyCauchy x))
    (fun _ _ h => Quotient.sound (C.applyCauchy_null h))

theorem completedTransfer_embed (a : C.positive.V) :
    C.completedTransfer (embedV C.positive a) =
      embedV C.positive (C.transfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

/-- Lift `Q'` equivalence to the constructive-real equivalence used by the
completed inner product. -/
theorem lifted_eqv {a b : Q'} (h : a.eqv b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro ε hε
  exact ⟨0, fun _ _ => ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b ε (Q'.le_of_lt hε)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a ε (Q'.le_of_lt hε))⟩⟩

theorem cinnerRep_transfer_selfAdjoint (x y : CauchyGNS C.positive) :
    CReal.Equiv
      (C.positive.cinnerRep (C.applyCauchy x) y)
      (C.positive.cinnerRep x (C.applyCauchy y)) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (C.positive.cInnerSeq (C.applyCauchy x) y n))
    (bSeq := fun n => CReal.ofQ'
      (C.positive.cInnerSeq x (C.applyCauchy y) n))
    (fun n => lifted_eqv (C.transfer_selfAdjoint (x.seq n) (y.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedTransfer_selfAdjoint (x y : GNSCompletionSpace C.positive) :
    C.positive.cinnerCompl (C.completedTransfer x) y =
      C.positive.cinnerCompl x (C.completedTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact C.cinnerRep_transfer_selfAdjoint u v

theorem completedTransfer_positive (x : GNSCompletionSpace C.positive) :
    CReal.RCnonneg (C.positive.cinnerCompl (C.completedTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (C.positive.cinnerRep (C.applyCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => C.transfer_positive (u.seq _))

theorem cinnerRep_transfer_contraction (x : CauchyGNS C.positive) :
    CReal.leEv
      (C.positive.cinnerRep (C.applyCauchy x) (C.applyCauchy x))
      (C.positive.cinnerRep x x) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (C.transfer_contraction (x.seq n))
    (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))⟩

theorem completedTransfer_contraction (x : GNSCompletionSpace C.positive) :
    CReal.RCle
      (C.positive.cinnerCompl (C.completedTransfer x) (C.completedTransfer x))
      (C.positive.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact C.cinnerRep_transfer_contraction u

theorem completedTransfer_vacuum :
    C.completedTransfer (embedV C.positive C.positive.zero) =
      embedV C.positive C.positive.zero := by
  refine Eq.trans (C.completedTransfer_embed C.positive.zero) ?_
  apply Quotient.sound
  apply embed_null_of_rad C.positive
  have hsub : C.positive.veq
      (C.positive.sub (C.transfer C.positive.zero) C.positive.zero)
      (C.positive.sub C.positive.zero C.positive.zero) :=
    C.positive.add_congr C.transfer_map_zero (C.positive.veq_refl _)
  exact Q'.eqv_trans _ _ _ (C.positive.B_diag_congr hsub)
    (C.positive.rad_refl C.positive.zero)

/-- Structural adapter to the legacy completed `TransferOperator`, whose weak
interface permits the additive zero as its distinguished vector.  This is not
a physical-vacuum claim: concrete models below construct separate operators
with a proved nonzero unit vacuum.  All three operator laws are derived. -/
def toZeroVacuumTransferOperator : TransferOperator C.positive.gnsComplete where
  T := C.completedTransfer
  vacuum := embedV C.positive C.positive.zero
  selfAdjoint := C.completedTransfer_selfAdjoint
  positive := C.completedTransfer_positive
  contraction := C.completedTransfer_contraction

end PositiveTimeCompression

/-! ## Exact rational swap-compression model -/

/-- A reducible unit-weight rational line, used so concrete coordinate types
remain definitionally visible to the kernel. -/
abbrev unitQGNS : GNSData where
  V := Q'
  veq := Q'.eqv
  veq_refl := Q'.eqv_refl
  veq_symm := fun h => Q'.eqv_symm h
  veq_trans := fun h₁ h₂ => Q'.eqv_trans _ _ _ h₁ h₂
  zero := 0
  add := fun a b => a + b
  neg := fun a => -a
  smul := fun s a => s * a
  add_congr := fun ha hb => Q'.add_eqv_congr' ha hb
  neg_congr := fun h => Q'.neg_eqv_congr _ _ h
  smul_congr := fun s {a a'} h => Q'.mul_eqv_congr_left s _ _ h
  add_assoc := Q'.add_assoc_eqv
  add_comm := Q'.add_comm_eqv
  zero_add := QPoly.q_zero_add_eqv
  neg_add := Q'.neg_add_self_eqv
  B := fun a b => 1 * (a * b)
  B_congr_left := fun b h => Q'.mul_eqv_congr_left 1 _ _
    (Q'.mul_eqv_congr_right _ _ b h)
  B_add_left := fun a b c => by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 1 _ _ (QPoly.q_add_mul a b c)) ?_
    exact Q'.mul_add_eqv 1 (a * c) (b * c)
  B_smul_left := fun s a b => by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 1 _ _ (Q'.mul_assoc_eqv s a b)) ?_
    ring_qeqv
  B_symm := fun a b => Q'.mul_eqv_congr_left 1 _ _ (Q'.mul_comm_eqv a b)
  self_nonneg := fun a => Q'.mul_nonneg _ _ (by decide)
    (SumOfSquares.q_mul_self_nonneg a)

abbrev positivePlane : GNSData := gnsProduct unitQGNS unitQGNS

abbrev ambientThree : GNSData := gnsProduct unitQGNS (gnsProduct unitQGNS unitQGNS)

def swapTime (x : Q' × (Q' × Q')) : Q' × (Q' × Q') :=
  (x.1, (x.2.2, x.2.1))

def identityReflection (x : Q' × (Q' × Q')) : Q' × (Q' × Q') := x

/-- Ambient time is a nontrivial rational isometric automorphism.  It is an
involution, so the identity reflection conjugates it to its inverse. -/
def ambientSwap : AmbientTimeReflection where
  space := ambientThree
  tau := swapTime
  tauInv := swapTime
  theta := identityReflection
  tau_map_veq := by
    intro a b h
    exact ⟨h.1, ⟨h.2.2, h.2.1⟩⟩
  tau_map_add := fun _ _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩
  tau_map_neg := fun _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩
  tau_map_smul := fun _ _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩
  tau_left_inv := fun _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩
  tau_right_inv := fun _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩
  tau_isometry := by
    intro a b
    change
      ((1 * (a.1 * b.1)) +
        ((1 * (a.2.2 * b.2.2)) + (1 * (a.2.1 * b.2.1)))) ≈
      ((1 * (a.1 * b.1)) + ((1 * (a.2.1 * b.2.1)) + (1 * (a.2.2 * b.2.2))))
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_comm_eqv _ _)
  theta_involutive := fun _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩
  theta_time_inverse := fun _ =>
    ⟨Q'.eqv_refl _, ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩⟩

def embedPositive (x : Q' × Q') : Q' × (Q' × Q') := (x.1, (x.2, 0))

def projectPositive (x : Q' × (Q' × Q')) : Q' × Q' := (x.1, x.2.1)

def compressedSwap (x : Q' × Q') : Q' × Q' := (x.1, 0)

def residualSwap (x : Q' × Q') : Q' × (Q' × Q') := (0, (0, x.2))

def positiveCoordinate (x : Q' × Q') : Nat → Q'
  | 0 => x.1
  | _ + 1 => x.2

def positiveModeWeight : Nat → Q'
  | 0 => 1
  | _ + 1 => 0

/-- Exact compression of the ambient coordinate swap to the positive-time
plane.  Positivity and contraction follow from the certificates in the
generic interface, not from assumed operator laws. -/
def rationalSwapCompression : PositiveTimeCompression ambientSwap where
  positive := positivePlane
  embed := embedPositive
  project := projectPositive
  transfer := compressedSwap
  residual := residualSwap
  embed_form := by
    intro a b
    change
      ((1 * (a.1 * b.1)) + ((1 * (a.2 * b.2)) + (1 * (0 * 0)))) ≈
        ((1 * (a.1 * b.1)) + (1 * (a.2 * b.2)))
    refine Q'.add_eqv_congr' (Q'.eqv_refl _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _ (QPoly.q_zero_mul 0))
          (QPoly.q_mul_zero 1))) ?_
    exact QPoly.q_add_zero_eqv _
  reflected_form := by
    intro a b
    change
      ((1 * (a.1 * b.1)) + ((1 * (a.2 * b.2)) + (1 * (0 * 0)))) ≈
        ((1 * (a.1 * b.1)) + (1 * (a.2 * b.2)))
    refine Q'.add_eqv_congr' (Q'.eqv_refl _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _ (QPoly.q_zero_mul 0))
          (QPoly.q_mul_zero 1))) ?_
    exact QPoly.q_add_zero_eqv _
  project_embed := fun a => ⟨Q'.eqv_refl a.1, Q'.eqv_refl a.2⟩
  transfer_projected_time := fun a =>
    ⟨Q'.eqv_refl a.1, Q'.eqv_refl 0⟩
  transfer_map_veq := by
    intro a b h
    exact ⟨h.1, Q'.eqv_refl 0⟩
  transfer_map_zero := ⟨Q'.eqv_refl 0, Q'.eqv_refl 0⟩
  transfer_map_add := by
    intro a b
    exact ⟨Q'.eqv_refl _, Q'.eqv_symm (QPoly.q_zero_add_eqv 0)⟩
  transfer_map_neg := by
    intro a
    refine ⟨Q'.eqv_refl _, ?_⟩
    change (0 : Q') ≈ -(0 : Q')
    decide
  transfer_map_smul := by
    intro r a
    exact ⟨Q'.eqv_refl _, Q'.eqv_symm (QPoly.q_mul_zero r)⟩
  compressed_decomposition := by
    intro a
    exact ⟨Q'.eqv_symm (QPoly.q_add_zero_eqv a.1),
      ⟨Q'.eqv_symm (QPoly.q_zero_add_eqv 0),
        Q'.eqv_symm (QPoly.q_zero_add_eqv a.2)⟩⟩
  compressed_orthogonal := by
    intro a
    change
      ((1 * (a.1 * 0)) +
        ((1 * (0 * 0)) + (1 * (0 * a.2)))) ≈ 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _ (QPoly.q_mul_zero a.1))
          (QPoly.q_mul_zero 1))
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left 1 _ _ (QPoly.q_zero_mul 0))
            (QPoly.q_mul_zero 1))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left 1 _ _ (QPoly.q_zero_mul a.2))
            (QPoly.q_mul_zero 1)))) ?_
    exact Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (0 + 0))
      (QPoly.q_zero_add_eqv 0)
  modeCount := 2
  coordinate := positiveCoordinate
  modeWeight := positiveModeWeight
  modeWeight_nonneg := by
    intro i
    cases i with
    | zero => decide
    | succ _ =>
        change (0 : Q') ≤ (0 : Q')
        exact Q'.le_refl' 0
  transfer_weightedGram := by
    intro a b
    change
      ((1 * (a.1 * b.1)) + (1 * (0 * b.2))) ≈
        ((0 + 1 * (a.1 * b.1)) + 0 * (a.2 * b.2))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _ (QPoly.q_zero_mul b.2))
          (QPoly.q_mul_zero 1))) ?_
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (QPoly.q_zero_add_eqv _)
        (QPoly.q_zero_mul (a.2 * b.2))) ?_
    exact QPoly.q_add_zero_eqv _

def vacuumMode : positivePlane.V := (1, 0)

def excitedMode : positivePlane.V := (0, 1)

theorem zeroMode_nonneg : (0 : Q') ≤ (0 : Q') := by decide

theorem zeroMode_lt_one : (0 : Q') < (1 : Q') := by decide

theorem compressedSwap_vacuum_eigen :
    positivePlane.veq (compressedSwap vacuumMode) vacuumMode := by
  exact ⟨by decide, by decide⟩

theorem compressedSwap_excited_eigen :
    positivePlane.veq (compressedSwap excitedMode)
      (positivePlane.smul 0 excitedMode) := by
  exact ⟨by decide, by decide⟩

/-- The excited quotient vector is genuinely different from the vacuum
quotient vector. -/
theorem excited_qmk_ne_vacuum_qmk :
    positivePlane.qmk excitedMode ≠ positivePlane.qmk vacuumMode := by
  intro h
  have hr : positivePlane.rad excitedMode vacuumMode := Quotient.exact h
  unfold GNSData.rad GNSData.sub positivePlane gnsProduct unitQGNS
    excitedMode vacuumMode at hr
  exact (by decide : ¬ ((((1 : Q') * (((0 : Q') + -(1 : Q')) * ((0 : Q') + -(1 : Q')))) +
    ((1 : Q') * (((1 : Q') + -(0 : Q')) * ((1 : Q') + -(0 : Q'))))).eqv 0)) hr

/-- The excited quotient vector is nonzero, so the eigenvalue-zero mode is
not a vacuous representative. -/
theorem excited_qmk_ne_zero_qmk :
    positivePlane.qmk excitedMode ≠ positivePlane.qmk positivePlane.zero := by
  intro h
  have hr : positivePlane.rad excitedMode positivePlane.zero := Quotient.exact h
  unfold GNSData.rad GNSData.sub positivePlane gnsProduct unitQGNS
    excitedMode at hr
  exact (by decide : ¬ ((((1 : Q') * (((0 : Q') + -(0 : Q')) * ((0 : Q') + -(0 : Q')))) +
    ((1 : Q') * (((1 : Q') + -(0 : Q')) * ((1 : Q') + -(0 : Q'))))).eqv 0)) hr

/-- The repaired interface reaches the existing completed transfer type.  In
this concrete operator the distinguished vacuum is the physical unit vector,
not merely the additive zero used by the generic bridge. -/
def rationalSwapTransferOperator : TransferOperator positivePlane.gnsComplete where
  T := rationalSwapCompression.completedTransfer
  vacuum := embedV positivePlane vacuumMode
  selfAdjoint := rationalSwapCompression.completedTransfer_selfAdjoint
  positive := rationalSwapCompression.completedTransfer_positive
  contraction := rationalSwapCompression.completedTransfer_contraction

theorem rationalSwap_completed_vacuum_eigen :
    rationalSwapTransferOperator.T (embedV positivePlane vacuumMode) =
      embedV positivePlane vacuumMode := by
  refine Eq.trans
    (PositiveTimeCompression.completedTransfer_embed rationalSwapCompression vacuumMode) ?_
  apply Quotient.sound
  apply embed_null_of_rad positivePlane
  have hsub : positivePlane.veq
      (positivePlane.sub (compressedSwap vacuumMode) vacuumMode)
      (positivePlane.sub vacuumMode vacuumMode) :=
    positivePlane.add_congr compressedSwap_vacuum_eigen (positivePlane.veq_refl _)
  exact Q'.eqv_trans _ _ _ (positivePlane.B_diag_congr hsub)
    (positivePlane.rad_refl vacuumMode)

theorem rationalSwap_completed_excited_eigen :
    rationalSwapTransferOperator.T (embedV positivePlane excitedMode) =
      embedV positivePlane (positivePlane.smul 0 excitedMode) := by
  refine Eq.trans
    (PositiveTimeCompression.completedTransfer_embed rationalSwapCompression excitedMode) ?_
  apply Quotient.sound
  apply embed_null_of_rad positivePlane
  have hsub : positivePlane.veq
      (positivePlane.sub (compressedSwap excitedMode)
        (positivePlane.smul 0 excitedMode))
      (positivePlane.sub (positivePlane.smul 0 excitedMode)
        (positivePlane.smul 0 excitedMode)) :=
    positivePlane.add_congr compressedSwap_excited_eigen (positivePlane.veq_refl _)
  exact Q'.eqv_trans _ _ _ (positivePlane.B_diag_congr hsub)
    (positivePlane.rad_refl (positivePlane.smul 0 excitedMode))

theorem rationalSwap_vacuum_fixed :
    rationalSwapTransferOperator.T rationalSwapTransferOperator.vacuum =
      rationalSwapTransferOperator.vacuum :=
  rationalSwap_completed_vacuum_eigen

theorem completed_excited_ne_zero :
    embedV positivePlane excitedMode ≠
      embedV positivePlane positivePlane.zero := by
  intro h
  apply excited_qmk_ne_zero_qmk
  apply embedQuot_injective positivePlane
  exact h

/-- The completed positive self-adjoint contraction is not the identity: it
kills the nonzero excited vector.  This is the explicit constructive witness
that compression avoids the ambient-automorphism identity no-go. -/
theorem rationalSwap_completed_nonidentity :
    rationalSwapTransferOperator.T (embedV positivePlane excitedMode) ≠
      embedV positivePlane excitedMode := by
  intro hid
  apply completed_excited_ne_zero
  have hzero : embedV positivePlane (positivePlane.smul 0 excitedMode) =
      embedV positivePlane positivePlane.zero := by
    apply Quotient.sound
    apply embed_null_of_rad positivePlane
    unfold GNSData.rad GNSData.sub positivePlane gnsProduct unitQGNS excitedMode
    decide
  exact Eq.trans (Eq.symm hid)
    (Eq.trans rationalSwap_completed_excited_eigen hzero)

end YMGap.Continuum.PositiveTimeCompressedTransfer

#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.weightedGram_diag_nonneg
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.gnsProduct
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.AmbientTimeReflection
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.PositiveTimeCompression.transfer_selfAdjoint
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.PositiveTimeCompression.transfer_positive
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.PositiveTimeCompression.transfer_contraction
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.PositiveTimeCompression.toZeroVacuumTransferOperator
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.ambientSwap
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.rationalSwapCompression
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.rationalSwapTransferOperator
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.excited_qmk_ne_vacuum_qmk
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.excited_qmk_ne_zero_qmk
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.rationalSwap_completed_vacuum_eigen
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.rationalSwap_completed_excited_eigen
#print axioms YMGap.Continuum.PositiveTimeCompressedTransfer.rationalSwap_completed_nonidentity
