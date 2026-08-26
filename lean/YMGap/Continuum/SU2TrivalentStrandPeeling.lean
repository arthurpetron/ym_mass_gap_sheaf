/-
# Constructive strand resolution and peeling for one SU(2) trivalent vertex

An admissible SU(2) triple of twice-spin labels `(a,b,c)` has three unique
nonnegative strand multiplicities

    a = ca + ab,    b = bc + ab,    c = bc + ca.

The existing proposition-level theorem `fusionOK_strand` records this
parametrization.  The present module keeps the multiplicities as computable
`Type`-level data.  Its canonical constructor uses the literal half-differences

    ab = (a+b-c)/2,  bc = (b+c-a)/2,  ca = (c+a-b)/2.

It then proves the local rank-lowering move needed by a stranded spin-foam
argument: selecting any positive strand bundle and removing one strand from
its two endpoints produces another explicit trivalent resolution, preserves
SU(2) admissibility, and lowers the total twice-spin by exactly two.  A
deterministic selector returns such a peel whenever the original total label
is positive.

Honest scope: this is one local trivalent vertex.  It does not yet assemble
the local strands across a lattice face, extract a global closed component,
compare BF4 heat weights, or prove a posterior Poincare/spectral-gap bound.

Constructive contract: `Nat` arithmetic and decidable case splits only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.FusionQuotientCollapse

namespace YMGap.Continuum.SU2TrivalentStrandPeeling

set_option autoImplicit false

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse

/-! ## 1. Explicit trivalent strand data -/

/-- A strand resolution of the admissible trivalent labels `(a,b,c)`.
`ab` joins the `a` and `b` legs, and similarly for `bc` and `ca`. -/
structure TrivalentStrandResolution (a b c : Nat) : Type where
  ab : Nat
  bc : Nat
  ca : Nat
  a_balance : a = ca + ab
  b_balance : b = bc + ab
  c_balance : c = bc + ca

/-- The `a-b` strand count computed directly from the external labels. -/
def canonicalAB (a b c : Nat) : Nat :=
  (a + b - c) / 2

/-- The `b-c` strand count computed directly from the external labels. -/
def canonicalBC (a b c : Nat) : Nat :=
  (b + c - a) / 2

/-- The `c-a` strand count computed directly from the external labels. -/
def canonicalCA (a b c : Nat) : Nat :=
  (c + a - b) / 2

private theorem fusionOK_linear_data
    {a b c : Nat} (hadmissible : fusionOK a b c = true) :
    a <= b + c /\ b <= a + c /\ c <= a + b /\
      (a + b + c) % 2 = 0 := by
  obtain ⟨hlower, hupper, hparity⟩ :=
    (fusionOK_eq_true_iff a b c).mp hadmissible
  have htriangle : a <= b + c /\ b <= a + c := by
    rcases Nat.le_total a b with hab | hba
    · have hmax : Nat.max a b = b := Nat.max_eq_right hab
      have hmin : Nat.min a b = a := Nat.min_eq_left hab
      exact ⟨by omega, by omega⟩
    · have hmax : Nat.max a b = a := Nat.max_eq_left hba
      have hmin : Nat.min a b = b := Nat.min_eq_right hba
      exact ⟨by omega, by omega⟩
  exact ⟨htriangle.1, htriangle.2, hupper, hparity⟩

/-- Every admissible SU(2) triple constructively computes its canonical
three strand multiplicities.  No witness is extracted from `Prop`: the data
are the displayed natural-number formulas. -/
def canonicalTrivalentStrandResolution
    (a b c : Nat) (hadmissible : fusionOK a b c = true) :
    TrivalentStrandResolution a b c where
  ab := canonicalAB a b c
  bc := canonicalBC a b c
  ca := canonicalCA a b c
  a_balance := by
    have hdata := fusionOK_linear_data hadmissible
    unfold canonicalAB canonicalCA
    omega
  b_balance := by
    have hdata := fusionOK_linear_data hadmissible
    unfold canonicalAB canonicalBC
    omega
  c_balance := by
    have hdata := fusionOK_linear_data hadmissible
    unfold canonicalBC canonicalCA
    omega

/-- Strand data imply the SU(2) fusion rule directly. -/
theorem TrivalentStrandResolution.admissible
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c) :
    fusionOK a b c = true := by
  cases resolution with
  | mk ab bc ca ha hb hc =>
    subst a
    subst b
    subst c
    rw [fusionOK_eq_true_iff]
    rcases Nat.le_total (ca + ab) (bc + ab) with hab | hba
    · have hmax : Nat.max (ca + ab) (bc + ab) = bc + ab :=
        Nat.max_eq_right hab
      have hmin : Nat.min (ca + ab) (bc + ab) = ca + ab :=
        Nat.min_eq_left hab
      exact ⟨by omega, by omega, by omega⟩
    · have hmax : Nat.max (ca + ab) (bc + ab) = ca + ab :=
        Nat.max_eq_left hba
      have hmin : Nat.min (ca + ab) (bc + ab) = bc + ab :=
        Nat.min_eq_right hba
      exact ⟨by omega, by omega, by omega⟩

/-- The `a-b` strand count is forced by the three balance equations. -/
theorem TrivalentStrandResolution.ab_eq_canonical
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c) :
    resolution.ab = canonicalAB a b c := by
  unfold canonicalAB
  have ha := resolution.a_balance
  have hb := resolution.b_balance
  have hc := resolution.c_balance
  have hdiff : a + b - c = resolution.ab + resolution.ab := by
    omega
  rw [hdiff]
  omega

/-- The `b-c` strand count is forced by the three balance equations. -/
theorem TrivalentStrandResolution.bc_eq_canonical
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c) :
    resolution.bc = canonicalBC a b c := by
  unfold canonicalBC
  have ha := resolution.a_balance
  have hb := resolution.b_balance
  have hc := resolution.c_balance
  have hdiff : b + c - a = resolution.bc + resolution.bc := by
    omega
  rw [hdiff]
  omega

/-- The `c-a` strand count is forced by the three balance equations. -/
theorem TrivalentStrandResolution.ca_eq_canonical
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c) :
    resolution.ca = canonicalCA a b c := by
  unfold canonicalCA
  have ha := resolution.a_balance
  have hb := resolution.b_balance
  have hc := resolution.c_balance
  have hdiff : c + a - b = resolution.ca + resolution.ca := by
    omega
  rw [hdiff]
  omega

/-- The strand resolution of fixed trivalent labels is unique. -/
theorem TrivalentStrandResolution.unique
    {a b c : Nat}
    (left right : TrivalentStrandResolution a b c) :
    left = right := by
  cases left with
  | mk leftAB leftBC leftCA leftA leftB leftC =>
      cases right with
      | mk rightAB rightBC rightCA rightA rightB rightC =>
          have hab : leftAB = rightAB := by omega
          have hbc : leftBC = rightBC := by omega
          have hca : leftCA = rightCA := by omega
          subst rightAB
          subst rightBC
          subst rightCA
          rfl

/-! ## 2. Remove one explicit strand -/

/-- The three possible bundles from which a local strand can be peeled. -/
inductive TrivalentStrandPair : Type
  | ab
  | bc
  | ca
  deriving DecidableEq

/-- The number of strands in a selected pair bundle. -/
def TrivalentStrandResolution.pairCount
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c) :
    TrivalentStrandPair -> Nat
  | .ab => resolution.ab
  | .bc => resolution.bc
  | .ca => resolution.ca

/-- A constructive choice of one nonempty strand bundle. -/
structure TrivalentStrandPeel
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c) : Type where
  pair : TrivalentStrandPair
  positive : 0 < resolution.pairCount pair

/-- The residual external labels after removing the selected strand from its
two endpoints. -/
def TrivalentStrandPeel.nextLabels
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (peel : TrivalentStrandPeel resolution) : Nat × Nat × Nat :=
  match peel.pair with
  | .ab => (a - 1, b - 1, c)
  | .bc => (a, b - 1, c - 1)
  | .ca => (a - 1, b, c - 1)

/-- Peeling one strand also returns the residual strand resolution as data. -/
def TrivalentStrandPeel.nextResolution
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (peel : TrivalentStrandPeel resolution) :
    TrivalentStrandResolution
      peel.nextLabels.1 peel.nextLabels.2.1 peel.nextLabels.2.2 := by
  cases hpair : peel.pair with
  | ab =>
      have hpositive := peel.positive
      simp only [TrivalentStrandResolution.pairCount, hpair] at hpositive
      have ha := resolution.a_balance
      have hb := resolution.b_balance
      have hc := resolution.c_balance
      refine
        { ab := resolution.ab - 1
          bc := resolution.bc
          ca := resolution.ca
          a_balance := ?_
          b_balance := ?_
          c_balance := ?_ }
      all_goals
        simp only [TrivalentStrandPeel.nextLabels, hpair]
      all_goals omega
  | bc =>
      have hpositive := peel.positive
      simp only [TrivalentStrandResolution.pairCount, hpair] at hpositive
      have ha := resolution.a_balance
      have hb := resolution.b_balance
      have hc := resolution.c_balance
      refine
        { ab := resolution.ab
          bc := resolution.bc - 1
          ca := resolution.ca
          a_balance := ?_
          b_balance := ?_
          c_balance := ?_ }
      all_goals
        simp only [TrivalentStrandPeel.nextLabels, hpair]
      all_goals omega
  | ca =>
      have hpositive := peel.positive
      simp only [TrivalentStrandResolution.pairCount, hpair] at hpositive
      have ha := resolution.a_balance
      have hb := resolution.b_balance
      have hc := resolution.c_balance
      refine
        { ab := resolution.ab
          bc := resolution.bc
          ca := resolution.ca - 1
          a_balance := ?_
          b_balance := ?_
          c_balance := ?_ }
      all_goals
        simp only [TrivalentStrandPeel.nextLabels, hpair]
      all_goals omega

/-- The residual labels remain SU(2)-admissible. -/
theorem TrivalentStrandPeel.next_admissible
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (peel : TrivalentStrandPeel resolution) :
    fusionOK peel.nextLabels.1
      peel.nextLabels.2.1 peel.nextLabels.2.2 = true :=
  peel.nextResolution.admissible

/-- One local strand peel lowers total twice-spin by exactly two. -/
theorem TrivalentStrandPeel.rank_drop_exact
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (peel : TrivalentStrandPeel resolution) :
    peel.nextLabels.1 + peel.nextLabels.2.1 +
        peel.nextLabels.2.2 + 2 =
      a + b + c := by
  have ha := resolution.a_balance
  have hb := resolution.b_balance
  have hc := resolution.c_balance
  have hpositive := peel.positive
  cases hpair : peel.pair <;>
    simp only [TrivalentStrandPeel.nextLabels, hpair] <;>
    simp only [TrivalentStrandResolution.pairCount, hpair] at hpositive <;>
    omega

/-- Hence the natural total label decreases strictly. -/
theorem TrivalentStrandPeel.rank_lt
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (peel : TrivalentStrandPeel resolution) :
    peel.nextLabels.1 + peel.nextLabels.2.1 +
        peel.nextLabels.2.2 <
      a + b + c := by
  have hdrop := peel.rank_drop_exact
  omega

/-! ## 3. Every nonvacuum trivalent vertex has a deterministic peel -/

/-- A positive total label constructively selects the first nonempty bundle
in the order `ab`, `bc`, `ca`. -/
def TrivalentStrandResolution.selectPeel
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c)
    (hpositive : 0 < a + b + c) :
    TrivalentStrandPeel resolution := by
  by_cases hab : 0 < resolution.ab
  · exact ⟨.ab, hab⟩
  · by_cases hbc : 0 < resolution.bc
    · exact ⟨.bc, hbc⟩
    · have hca : 0 < resolution.ca := by
        have ha := resolution.a_balance
        have hb := resolution.b_balance
        have hc := resolution.c_balance
        omega
      exact ⟨.ca, hca⟩

/-- The data returned by one local rank-lowering step. -/
structure TrivalentStrandDescent (a b c : Nat) : Type where
  next : Nat × Nat × Nat
  resolution : TrivalentStrandResolution next.1 next.2.1 next.2.2
  rank_drop_exact : next.1 + next.2.1 + next.2.2 + 2 = a + b + c

/-- End-to-end local descent: every admissible nonvacuum triple computes a
strictly smaller admissible triple together with its explicit strand data. -/
def peelAdmissibleNonvacuum
    (a b c : Nat) (hadmissible : fusionOK a b c = true)
    (hpositive : 0 < a + b + c) :
    TrivalentStrandDescent a b c :=
  let resolution :=
    canonicalTrivalentStrandResolution a b c hadmissible
  let peel := resolution.selectPeel hpositive
  { next := peel.nextLabels
    resolution := peel.nextResolution
    rank_drop_exact := peel.rank_drop_exact }

#print axioms canonicalTrivalentStrandResolution
#print axioms TrivalentStrandResolution.admissible
#print axioms TrivalentStrandResolution.ab_eq_canonical
#print axioms TrivalentStrandResolution.bc_eq_canonical
#print axioms TrivalentStrandResolution.ca_eq_canonical
#print axioms TrivalentStrandResolution.unique
#print axioms TrivalentStrandPeel.nextResolution
#print axioms TrivalentStrandPeel.next_admissible
#print axioms TrivalentStrandPeel.rank_drop_exact
#print axioms TrivalentStrandPeel.rank_lt
#print axioms TrivalentStrandResolution.selectPeel
#print axioms peelAdmissibleNonvacuum

end YMGap.Continuum.SU2TrivalentStrandPeeling
