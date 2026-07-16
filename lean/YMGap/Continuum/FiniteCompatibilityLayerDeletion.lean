/-
# Iterated deletion of small marked layers in a finite compatibility gas

This module iterates the exact factor-two deletion estimate for an arbitrary
finite list of marked atom classes.  If each marked single-atom activity sum
is at most one half, deleting all listed layers costs at most `2^N` in the
finite partition.  Repeated filters and duplicate marks are allowed.
-/

import YMGap.Continuum.FiniteCompatibilityMarkedBound

namespace YMGap.Continuum.FiniteCompatibilityLayerDeletion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityMarkedBound

variable {A Face : Type}

/-- Successively remove every atom marked by each face in the supplied list. -/
def deleteMarkedLayers (mark : Face → A → Bool) :
    List Face → List A → List A
  | [], ambient => ambient
  | face :: rest, ambient =>
      deleteMarkedLayers mark rest
        (ambient.filter (fun atom => !(mark face atom)))

/-- Every survivor of iterated deletion came from the original ambient list. -/
theorem mem_deleteMarkedLayers_source
    (mark : Face → A → Bool) :
    ∀ (faces : List Face) (ambient : List A) (atom : A),
      atom ∈ deleteMarkedLayers mark faces ambient → atom ∈ ambient
  | [], _, _, hatom => hatom
  | face :: rest, ambient, atom, hatom => by
      have hnext : atom ∈
          ambient.filter (fun item => !(mark face item)) :=
        mem_deleteMarkedLayers_source mark rest _ atom hatom
      exact (List.mem_filter.mp hnext).1

/-- A survivor is unmarked by every deleted layer. -/
theorem mem_deleteMarkedLayers_mark_false
    (mark : Face → A → Bool) :
    ∀ (faces : List Face) (ambient : List A) (atom : A),
      atom ∈ deleteMarkedLayers mark faces ambient →
      ∀ face, face ∈ faces → mark face atom = false
  | [], _, _, _, face, hface => absurd hface List.not_mem_nil
  | head :: rest, ambient, atom, hatom, face, hface => by
      let next := ambient.filter (fun item => !(mark head item))
      have hnext : atom ∈ next :=
        mem_deleteMarkedLayers_source mark rest next atom hatom
      rcases List.mem_cons.mp hface with heq | hrest
      · subst face
        have hnot : (!(mark head atom)) = true :=
          (List.mem_filter.mp hnext).2
        cases hmark : mark head atom <;> simp_all
      · exact mem_deleteMarkedLayers_mark_false
          mark rest next atom hatom face hrest

/-- Iterated layer deletion preserves duplicate-freeness of the ambient
enumeration.  This is needed when the surviving compatible families are used
as the source of a weighted injection. -/
theorem deleteMarkedLayers_nodup
    (mark : Face → A → Bool) :
    ∀ (faces : List Face) {ambient : List A}, ambient.Nodup →
      (deleteMarkedLayers mark faces ambient).Nodup
  | [], _, hambient => hambient
  | face :: rest, ambient, hambient => by
      exact deleteMarkedLayers_nodup mark rest
        (List.filter_sublist.nodup hambient)

/-- Iterated exact deletion bound.  The smallness assumption is evaluated in
the original ambient list at each induction stage; monotonicity of a marked
activity sum under filtering supplies the recursive assumptions. -/
theorem partition_le_two_pow_mul_deleteMarkedLayers
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark : Face → A → Bool) :
    ∀ (faces : List Face) (ambient : List A),
      (∀ face, face ∈ faces →
        markedActivitySum weight (mark face) ambient ≤
          Q'.mkPos 1 2 (by decide)) →
      partition compat weight ambient ≤
        (Q'.ofNat 2) ^ faces.length *
          partition compat weight (deleteMarkedLayers mark faces ambient)
  | [], ambient, _ => by
      change partition compat weight ambient ≤
        (1 : Q') * partition compat weight ambient
      exact Q'.ge_of_eqv
        (Q'.one_mul_eqv (partition compat weight ambient))
  | face :: rest, ambient, hsmall => by
      let next := ambient.filter (fun atom => !(mark face atom))
      have hhead : markedActivitySum weight (mark face) ambient ≤
          Q'.mkPos 1 2 (by decide) :=
        hsmall face List.mem_cons_self
      have hstep : partition compat weight ambient ≤
          Q'.ofNat 2 * partition compat weight next := by
        exact partition_le_two_mul_avoiding_of_activitySum_le_half
          compat weight hweight (mark face) ambient hhead
      have htailSmall : ∀ tailFace, tailFace ∈ rest →
          markedActivitySum weight (mark tailFace) next ≤
            Q'.mkPos 1 2 (by decide) := by
        intro tailFace htailFace
        exact Q'.le_trans' _ _ _
          (markedActivitySum_filter_le weight hweight
            (mark tailFace) (fun atom => !(mark face atom)) ambient)
          (hsmall tailFace (List.mem_cons_of_mem face htailFace))
      have htail :=
        partition_le_two_pow_mul_deleteMarkedLayers
          compat weight hweight mark rest next htailSmall
      have hscaled :
          Q'.ofNat 2 * partition compat weight next ≤
            Q'.ofNat 2 *
              ((Q'.ofNat 2) ^ rest.length *
                partition compat weight
                  (deleteMarkedLayers mark rest next)) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ htail (by decide)
      have hassoc :
          Q'.ofNat 2 *
              ((Q'.ofNat 2) ^ rest.length *
                partition compat weight
                  (deleteMarkedLayers mark rest next)) ≤
            (Q'.ofNat 2 * (Q'.ofNat 2) ^ rest.length) *
              partition compat weight
                (deleteMarkedLayers mark rest next) :=
        Q'.ge_of_eqv
          (Q'.mul_assoc_eqv (Q'.ofNat 2)
            ((Q'.ofNat 2) ^ rest.length)
            (partition compat weight
              (deleteMarkedLayers mark rest next)))
      change partition compat weight ambient ≤
        (Q'.ofNat 2) ^ (rest.length + 1) *
          partition compat weight
            (deleteMarkedLayers mark rest next)
      rw [Q'.pow_succ]
      exact Q'.le_trans' _ _ _ hstep
        (Q'.le_trans' _ _ _ hscaled hassoc)

end YMGap.Continuum.FiniteCompatibilityLayerDeletion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteCompatibilityLayerDeletion.deleteMarkedLayers
#print axioms YMGap.Continuum.FiniteCompatibilityLayerDeletion.mem_deleteMarkedLayers_source
#print axioms YMGap.Continuum.FiniteCompatibilityLayerDeletion.mem_deleteMarkedLayers_mark_false
#print axioms YMGap.Continuum.FiniteCompatibilityLayerDeletion.deleteMarkedLayers_nodup
#print axioms YMGap.Continuum.FiniteCompatibilityLayerDeletion.partition_le_two_pow_mul_deleteMarkedLayers
