/-
# A Type-modulated constructive GNS completion

The legacy `GNSCompletionSpace` uses a null relation of the form

  `forall epsilon, exists N, ...`

in `Prop`. This module instead retains an explicit Type-valued null modulus.
The propositional witness alone cannot be selected into Type. However, both
representatives ALSO carry Cauchy moduli, and those additional data suffice
to compute a null modulus; see `GNSNullModulusRecovery.recoverNullModulus`.

This module retains the null modulus as data.  `CauchyNullModulus` is a
structure in `Type`; the quotient relation is `Nonempty` such a structure.
Reflexivity, symmetry, and transitivity construct their moduli explicitly.
The resulting completion has the same representative inner-product limit and
maps canonically to the legacy completion by forgetting the modulus.

The inverse is constructed downstream in `GNSNullModulusRecovery`, with rate
max(X.modulus(epsilon/10),Y.modulus(epsilon/10)) and a two-triangle proof.
Its `fromLegacyCompletion` and `to_from_legacy` / `from_to_legacy` show that
the two completions are canonically equivalent without choice. This corrects
the earlier, overly strong assertion that such an inverse was forbidden.
-/

import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.Continuum.GNSModulusCompletion

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Type-valued asymptotic null data -/

/-- Explicit modulus data witnessing that two GNS Cauchy representatives
approach one another in squared distance. -/
structure CauchyNullModulus (D : GNSData)
    (X Y : CauchyGNS D) : Type where
  modulus : Q' → Nat
  close : ∀ epsilon, (0 : Q') < epsilon → ∀ n,
    modulus epsilon ≤ n → D.distSqQ (X.seq n) (Y.seq n) ≤ epsilon

namespace CauchyNullModulus

variable {D : GNSData} {X Y Z : CauchyGNS D}

/-- Forgetting the Type-valued modulus recovers the legacy propositional null
relation. -/
theorem toCauchyNull (h : CauchyNullModulus D X Y) : CauchyNull D X Y := by
  intro epsilon hepsilon
  exact ⟨h.modulus epsilon,
    fun n hn => h.close epsilon hepsilon n hn⟩

/-- Reflexivity with the constant zero modulus. -/
def refl (D : GNSData) (X : CauchyGNS D) :
    CauchyNullModulus D X X where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ 0 epsilon
      (Q'.le_of_eqv (D.rad_refl (X.seq n)))
      (Q'.le_of_lt hepsilon)

/-- Symmetry preserves the supplied modulus. -/
def symm (h : CauchyNullModulus D X Y) :
    CauchyNullModulus D Y X where
  modulus := h.modulus
  close := by
    intro epsilon hepsilon n hn
    exact le_of_eqv_le
      (D.distSqQ_comm (Y.seq n) (X.seq n))
      (h.close epsilon hepsilon n hn)

private def quarterTolerance (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

private theorem quarterTolerance_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < quarterTolerance epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)

private theorem four_quarters_eqv (epsilon : Q') :
    ((quarterTolerance epsilon + quarterTolerance epsilon) +
      (quarterTolerance epsilon + quarterTolerance epsilon)) ≈ epsilon := by
  have hpair :
      (quarterTolerance epsilon + quarterTolerance epsilon) ≈
        HalfPow.half * epsilon :=
    ExpNeg.two_halves (HalfPow.half * epsilon)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hpair hpair)
    (ExpNeg.two_halves epsilon)

/-- Transitivity constructs the maximum of the two quarter-tolerance moduli. -/
def trans (hXY : CauchyNullModulus D X Y)
    (hYZ : CauchyNullModulus D Y Z) :
    CauchyNullModulus D X Z where
  modulus := fun epsilon =>
    max (hXY.modulus (quarterTolerance epsilon))
      (hYZ.modulus (quarterTolerance epsilon))
  close := by
    intro epsilon hepsilon n hn
    have hquarter : (0 : Q') < quarterTolerance epsilon :=
      quarterTolerance_pos hepsilon
    have hnXY : hXY.modulus (quarterTolerance epsilon) ≤ n :=
      Nat.le_trans (Nat.le_max_left _ _) hn
    have hnYZ : hYZ.modulus (quarterTolerance epsilon) ≤ n :=
      Nat.le_trans (Nat.le_max_right _ _) hn
    have hleft := hXY.close
      (quarterTolerance epsilon) hquarter n hnXY
    have hright := hYZ.close
      (quarterTolerance epsilon) hquarter n hnYZ
    have htriangle := D.distSqQ_triangle (X.seq n) (Y.seq n) (Z.seq n)
    have hsum :
        (D.distSqQ (X.seq n) (Y.seq n) +
            D.distSqQ (X.seq n) (Y.seq n)) +
          (D.distSqQ (Y.seq n) (Z.seq n) +
            D.distSqQ (Y.seq n) (Z.seq n)) ≤
        (quarterTolerance epsilon + quarterTolerance epsilon) +
          (quarterTolerance epsilon + quarterTolerance epsilon) :=
      Q'.add_le_add (Q'.add_le_add hleft hleft)
        (Q'.add_le_add hright hright)
    exact le_of_le_eqv
      (Q'.le_trans' _ _ _ htriangle hsum)
      (four_quarters_eqv epsilon)

end CauchyNullModulus

/-! ## 2. The modulated quotient completion -/

/-- Propositional quotient relation whose witness retains a Type-valued
modulus. -/
def ModulatedCauchyRel (D : GNSData)
    (X Y : CauchyGNS D) : Prop :=
  Nonempty (CauchyNullModulus D X Y)

theorem modulatedCauchyRel_refl (D : GNSData) (X : CauchyGNS D) :
    ModulatedCauchyRel D X X :=
  ⟨CauchyNullModulus.refl D X⟩

theorem modulatedCauchyRel_symm (D : GNSData)
    {X Y : CauchyGNS D}
    (h : ModulatedCauchyRel D X Y) :
    ModulatedCauchyRel D Y X := by
  rcases h with ⟨hdata⟩
  exact ⟨hdata.symm⟩

theorem modulatedCauchyRel_trans (D : GNSData)
    {X Y Z : CauchyGNS D}
    (hXY : ModulatedCauchyRel D X Y)
    (hYZ : ModulatedCauchyRel D Y Z) :
    ModulatedCauchyRel D X Z := by
  rcases hXY with ⟨hXYdata⟩
  rcases hYZ with ⟨hYZdata⟩
  exact ⟨hXYdata.trans hYZdata⟩

def modulatedCauchySetoid (D : GNSData) : Setoid (CauchyGNS D) where
  r := ModulatedCauchyRel D
  iseqv :=
    ⟨modulatedCauchyRel_refl D,
      fun h => modulatedCauchyRel_symm D h,
      fun hXY hYZ => modulatedCauchyRel_trans D hXY hYZ⟩

/-- The GNS completion whose asymptotic null relation retains an explicit
Type-valued modulus. -/
def ModulatedGNSCompletionSpace (D : GNSData) : Type :=
  Quotient (modulatedCauchySetoid D)

/-! ## 3. Dense embedding and the canonical forgetful map -/

theorem constCauchy_modulatedNull_of_rad
    (D : GNSData) {a b : D.V} (h : D.rad a b) :
    ModulatedCauchyRel D (constCauchy D a) (constCauchy D b) :=
  ⟨{
    modulus := fun _ => 0
    close := by
      intro epsilon hepsilon n hn
      exact Q'.le_trans' _ 0 epsilon
        (Q'.le_of_eqv h) (Q'.le_of_lt hepsilon)
  }⟩

/-- Dense constant embedding into the Type-modulated completion. -/
def modulatedEmbedV (D : GNSData) (a : D.V) :
    ModulatedGNSCompletionSpace D :=
  Quotient.mk (modulatedCauchySetoid D) (constCauchy D a)

/-- Forget the explicit null modulus and map to the legacy GNS completion. -/
def toLegacyCompletion (D : GNSData) :
    ModulatedGNSCompletionSpace D → GNSCompletionSpace D :=
  Quotient.lift
    (fun X => Quotient.mk (cauchySetoid D) X)
    (fun _ _ h => by
      rcases h with ⟨hdata⟩
      exact Quotient.sound hdata.toCauchyNull)

@[simp] theorem toLegacyCompletion_mk (D : GNSData)
    (X : CauchyGNS D) :
    toLegacyCompletion D
        (Quotient.mk (modulatedCauchySetoid D) X) =
      Quotient.mk (cauchySetoid D) X :=
  rfl

theorem toLegacyCompletion_embed (D : GNSData) (a : D.V) :
    toLegacyCompletion D (modulatedEmbedV D a) = embedV D a :=
  rfl

/-! ## 4. The completed inner form -/

/-- The same representative CReal limit descends through the Type-modulated
null relation (proved equivalent to the legacy relation downstream). -/
def modulatedCinnerCompl (D : GNSData) :
    ModulatedGNSCompletionSpace D →
      ModulatedGNSCompletionSpace D → CReal.RC :=
  Quotient.lift₂
    (fun X Y => D.cinnerRepR X Y)
    (fun _ _ _ _ hX hY => by
      rcases hX with ⟨hXdata⟩
      rcases hY with ⟨hYdata⟩
      exact Quotient.sound
        (D.cinnerRep_welldef _ _ _ _
          hXdata.toCauchyNull hYdata.toCauchyNull))

/-- Forgetting the modulus preserves the full completed inner product. -/
theorem toLegacyCompletion_inner (D : GNSData)
    (left right : ModulatedGNSCompletionSpace D) :
    D.cinnerCompl (toLegacyCompletion D left) (toLegacyCompletion D right) =
      modulatedCinnerCompl D left right := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  rfl

/-- On dense constants, the modulated inner form is the original rational
pre-Hilbert form embedded into `RC`. -/
theorem modulatedCinnerCompl_embed (D : GNSData) (left right : D.V) :
    modulatedCinnerCompl D
        (modulatedEmbedV D left) (modulatedEmbedV D right) =
      Quotient.mk CReal.crealSetoid (D.cInner left right) := by
  rw [← toLegacyCompletion_inner D]
  rw [toLegacyCompletion_embed D, toLegacyCompletion_embed D]
  exact D.cinnerCompl_embed left right

end YMGap.Continuum.GNSModulusCompletion

#print axioms YMGap.Continuum.GNSModulusCompletion.CauchyNullModulus.toCauchyNull
#print axioms YMGap.Continuum.GNSModulusCompletion.CauchyNullModulus.trans
#print axioms YMGap.Continuum.GNSModulusCompletion.modulatedCauchySetoid
#print axioms YMGap.Continuum.GNSModulusCompletion.modulatedEmbedV
#print axioms YMGap.Continuum.GNSModulusCompletion.toLegacyCompletion
#print axioms YMGap.Continuum.GNSModulusCompletion.modulatedCinnerCompl
#print axioms YMGap.Continuum.GNSModulusCompletion.toLegacyCompletion_inner
#print axioms YMGap.Continuum.GNSModulusCompletion.modulatedCinnerCompl_embed
