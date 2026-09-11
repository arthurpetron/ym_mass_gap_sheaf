/-
# A constructive root for every nonempty inward-mate debt word

The exact stretched-debt expansion is indexed by Boolean words on the twelve
cube-boundary incidences.  This file equips every nonempty word with a
canonical geometric root: its first `true` bit, computed by structural
recursion.  The resulting finite index selects an attached production
incidence and is proved to carry a stretched choice.

This is data, not an existential proposition.  The next strand compiler may
therefore start tracing at the selected link without choice or a search hidden
behind proof irrelevance.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel

/-! ## 1. Shape and nonemptiness of the generated words -/

/-- Every full expansion word has exactly one bit per input item. -/
theorem debtChoiceWords_word_length {A : Type} :
    ∀ (items : List A) (word : List Bool),
      word ∈ debtChoiceWords items → word.length = items.length
  | [], word, hword => by
      simp only [debtChoiceWords, List.mem_singleton] at hword
      subst word
      rfl
  | _ :: tail, word, hword => by
      simp only [debtChoiceWords, List.mem_append, List.mem_map] at hword
      rcases hword with ⟨rest, hrest, rfl⟩ | ⟨rest, hrest, rfl⟩
      · simp only [List.length_cons]
        rw [debtChoiceWords_word_length tail rest hrest]
      · simp only [List.length_cons]
        rw [debtChoiceWords_word_length tail rest hrest]

/-- Every nonempty expansion word has exactly one bit per input item. -/
theorem nonemptyDebtChoiceWords_word_length {A : Type} :
    ∀ (items : List A) (word : List Bool),
      word ∈ nonemptyDebtChoiceWords items →
        word.length = items.length
  | [], word, hword => by
      simp only [nonemptyDebtChoiceWords, List.not_mem_nil] at hword
  | _ :: tail, word, hword => by
      simp only [nonemptyDebtChoiceWords, List.mem_append, List.mem_map] at hword
      rcases hword with ⟨rest, hrest, rfl⟩ | ⟨rest, hrest, rfl⟩
      · simp only [List.length_cons]
        rw [nonemptyDebtChoiceWords_word_length tail rest hrest]
      · simp only [List.length_cons]
        rw [debtChoiceWords_word_length tail rest hrest]

/-- Membership in the nonempty expansion is positive data at the Boolean-word
level: some bit is literally `true`. -/
theorem true_mem_of_mem_nonemptyDebtChoiceWords {A : Type} :
    ∀ (items : List A) (word : List Bool),
      word ∈ nonemptyDebtChoiceWords items → true ∈ word
  | [], word, hword => by
      simp only [nonemptyDebtChoiceWords, List.not_mem_nil] at hword
  | _ :: tail, word, hword => by
      simp only [nonemptyDebtChoiceWords, List.mem_append, List.mem_map] at hword
      rcases hword with ⟨rest, hrest, rfl⟩ | ⟨rest, _, rfl⟩
      · exact List.mem_cons_of_mem false
          (true_mem_of_mem_nonemptyDebtChoiceWords tail rest hrest)
      · exact List.mem_cons_self

/-! ## 2. Total first-true computation -/

/-- Index of the first true bit, returning the word length when none exists. -/
def firstTrueIndex : List Bool → Nat
  | [] => 0
  | true :: _ => 0
  | false :: tail => firstTrueIndex tail + 1

theorem firstTrueIndex_lt_of_mem_true :
    ∀ (word : List Bool), true ∈ word → firstTrueIndex word < word.length
  | [], hword => by simp at hword
  | true :: tail, _ => by simp [firstTrueIndex]
  | false :: tail, hword => by
      have htail : true ∈ tail := by simpa using hword
      have ih := firstTrueIndex_lt_of_mem_true tail htail
      simp only [firstTrueIndex, List.length_cons]
      omega

theorem getD_firstTrueIndex_eq_true_of_mem :
    ∀ (word : List Bool), true ∈ word →
      word.getD (firstTrueIndex word) false = true
  | [], hword => by simp at hword
  | true :: tail, _ => by simp [firstTrueIndex]
  | false :: tail, hword => by
      have htail : true ∈ tail := by simpa using hword
      simpa [firstTrueIndex] using
        getD_firstTrueIndex_eq_true_of_mem tail htail

/-! ## 3. The actual cube-boundary root -/

/-- A Boolean remainder word together with its membership certificate. -/
abbrev CubeNonemptyDebtWord :=
  { word : List Bool //
    word ∈ nonemptyDebtChoiceWords cubeProductionIncidences.attach }

/-- The computed root position, intrinsically bounded by the twelve attached
cube-production incidences. -/
def cubeDebtRootPosition (word : CubeNonemptyDebtWord) :
    Fin cubeProductionIncidences.attach.length :=
  ⟨firstTrueIndex word.1, by
    have htrue : true ∈ word.1 :=
      true_mem_of_mem_nonemptyDebtChoiceWords
        cubeProductionIncidences.attach word.1 word.2
    have hlt := firstTrueIndex_lt_of_mem_true word.1 htrue
    have hlength := nonemptyDebtChoiceWords_word_length
      cubeProductionIncidences.attach word.1 word.2
    rw [hlength] at hlt
    exact hlt⟩

/-- The geometric cube-boundary incidence selected by the first stretched
choice. -/
def cubeDebtRootIncidence (word : CubeNonemptyDebtWord) :
    CubeProductionIncidenceMember :=
  cubeProductionIncidences.attach.get (cubeDebtRootPosition word)

/-- The root position really is a stretched (`true`) choice in the word. -/
theorem cubeDebtRootChoice_eq_true (word : CubeNonemptyDebtWord) :
    word.1.getD (cubeDebtRootPosition word).1 false = true := by
  exact getD_firstTrueIndex_eq_true_of_mem word.1
    (true_mem_of_mem_nonemptyDebtChoiceWords
      cubeProductionIncidences.attach word.1 word.2)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.debtChoiceWords_word_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.true_mem_of_mem_nonemptyDebtChoiceWords
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.cubeDebtRootPosition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.cubeDebtRootChoice_eq_true
