/-
# Finite fixed-output reconstruction from ordered right sections

The constructive enumeration of fixed-output right channels is now used to
assemble the corresponding global coordinate sections.  We sum their
coordinate data and synthesize once through the checked global ordered-right
inverse.  Analysis of the result recovers every enumerated fixed-output
channel exactly; coordinates of a different final degree vanish.
-/

import YMGap.Continuum.SU2DirectRightFixedOutputEnumeration

namespace YMGap.Continuum.SU2DirectRightFixedOutputReconstruction

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2ChannelSectionSchurReconstruction
open YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration

local infix:50 " ≈ " => Q'.eqv

/-- Constructive equality decision for proof-carrying fixed right channels;
the inner order determines the entire channel. -/
instance fixedRightCGChannelDecidableEq (a b c d : Nat) :
    DecidableEq (FixedRightCGChannel a b c d) :=
  fun q u =>
    if h : q.p = u.p then
      isTrue (fixedRightChannel_eq_of_p_eq q u h)
    else
      isFalse (fun hqu => h (congrArg FixedRightCGChannel.p hqu))

/-- Finite sum of the coordinate data of the global sections belonging to a
list of fixed-output right channels. -/
def fixedRightSectionDataSum {a b c d : Nat}
    (qs : List (FixedRightCGChannel a b c d)) (x : TriForm) :
    DirectRightNestedCGChannel a b c → Q' :=
  fun u =>
    let rec go : List (FixedRightCGChannel a b c d) → Q'
      | [] => 0
      | q :: rest =>
          fixedRightSectionData q (fixedRightAnalysis q x) u + go rest
    go qs

/-- Synthesize the finite sum of the selected global right-channel sections
from their summed coordinate data. -/
def fixedRightSectionSum {a b c d : Nat}
    (qs : List (FixedRightCGChannel a b c d)) (x : TriForm) : TriForm :=
  directRightNestedReconstruct a b c (fixedRightSectionDataSum qs x)

/-- Canonical fixed-output projection obtained by summing every enumerated
right-channel section. -/
def fixedRightEnumeratedSectionSum (a b c d : Nat) (x : TriForm) : TriForm :=
  fixedRightSectionSum (fixedRightChannels a b c d) x

/-- One section-data summand, evaluated on a fixed channel coordinate, is
the selected form exactly when the two proof-carrying channels agree. -/
theorem fixedRightSectionData_at_fixed {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) (v : BForm)
    (s : Nat) (hs : s ≤ d) :
    fixedRightSectionData q v (fixedRightNestedChannel u s hs) ≈
      if q = u then v s else 0 := by
  by_cases hqu : q = u
  · subst q
    unfold fixedRightSectionData fixedRightNestedChannel
    rw [dif_pos ⟨rfl, rfl⟩, if_pos rfl]
    exact Q'.eqv_refl _
  · have hlabels : ¬ (u.p = q.p ∧ u.r = q.r) := by
      intro h
      apply hqu
      exact fixedRightChannel_eq_of_p_eq q u h.1.symm
    unfold fixedRightSectionData fixedRightNestedChannel
    rw [dif_neg hlabels, if_neg hqu]
    exact Q'.eqv_refl _

/-- On a duplicate-free channel list, the summed section data at a fixed
channel is its analyzed coefficient if the channel occurs in the list, and
zero otherwise. -/
theorem fixedRightSectionDataSum_at_fixed {a b c d : Nat}
    (qs : List (FixedRightCGChannel a b c d)) (hqs : qs.Nodup)
    (x : TriForm) (u : FixedRightCGChannel a b c d)
    (s : Nat) (hs : s ≤ d) :
    fixedRightSectionDataSum qs x (fixedRightNestedChannel u s hs) ≈
      if u ∈ qs then fixedRightAnalysis u x s else 0 := by
  induction qs with
  | nil =>
      simp only [fixedRightSectionDataSum, List.not_mem_nil, if_false]
      exact Q'.eqv_refl _
  | cons q rest ih =>
      have hnodup := List.nodup_cons.mp hqs
      have hhead := fixedRightSectionData_at_fixed q u
        (fixedRightAnalysis q x) s hs
      have htail := ih hnodup.2
      simp only [fixedRightSectionDataSum]
      by_cases hqu : q = u
      · subst q
        rw [if_pos rfl] at hhead
        rw [if_neg hnodup.1] at htail
        rw [if_pos List.mem_cons_self]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hhead htail)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · rw [if_neg hqu] at hhead
        by_cases hu : u ∈ rest
        · rw [if_pos hu] at htail
          have hucons : u ∈ q :: rest := List.mem_cons_of_mem q hu
          rw [if_pos hucons]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' hhead htail)
            (Q'.eqv_of_eq (Q'.zero_add' _))
        · rw [if_neg hu] at htail
          have hucons : u ∉ q :: rest := by
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem
            · exact hqu heq.symm
            · exact hu hmem
          rw [if_neg hucons]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' hhead htail)
            (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- **Finite fixed-output analysis/synthesis completeness.**  Summing the
global sections over a duplicate-free list recovers the analysis of every
channel in that list on the complete final output window. -/
theorem fixedRightAnalysis_sectionSum {a b c d : Nat}
    (qs : List (FixedRightCGChannel a b c d)) (hqs : qs.Nodup)
    (x : TriForm) (q : FixedRightCGChannel a b c d) (hq : q ∈ qs) :
    FormEqv (d + 1)
      (fixedRightAnalysis q (fixedRightSectionSum qs x))
      (fixedRightAnalysis q x) := by
  intro s hs
  have hsd : s ≤ d := by omega
  unfold fixedRightAnalysis fixedRightSectionSum
  rw [dif_pos hsd]
  have hcoord := directRightNestedCoordinates_reconstruct a b c
    (fixedRightSectionDataSum qs x) (fixedRightNestedChannel q s hsd)
  have hsum := fixedRightSectionDataSum_at_fixed qs hqs x q s hsd
  rw [if_pos hq] at hsum
  exact Q'.eqv_trans _ _ _ hcoord hsum

/-- Canonical completeness over the full constructive enumeration. -/
theorem fixedRightAnalysis_enumeratedSectionSum {a b c d : Nat}
    (x : TriForm) (q : FixedRightCGChannel a b c d) :
    FormEqv (d + 1)
      (fixedRightAnalysis q
        (fixedRightEnumeratedSectionSum a b c d x))
      (fixedRightAnalysis q x) := by
  exact fixedRightAnalysis_sectionSum
    (fixedRightChannels a b c d)
    (fixedRightChannels_nodup a b c d) x q
    (fixedRightChannels_complete q)

/-- Fixed-output analysis is definitionally zero beyond the selected final
degree, including after finite reconstruction. -/
theorem fixedRightAnalysis_zero_outside {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (x : TriForm)
    (s : Nat) (hs : d < s) :
    fixedRightAnalysis q x s ≈ 0 := by
  unfold fixedRightAnalysis
  rw [dif_neg (by omega)]
  exact Q'.eqv_refl _

/-- Final degree carried by an arbitrary global ordered-right coordinate. -/
def directRightFinalDegree {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) : Nat :=
  a + (b + c - 2 * u.k) - 2 * u.outer.k

private theorem fixedRightSectionDataSum_zero_of_finalDegree_ne
    {a b c d : Nat} (qs : List (FixedRightCGChannel a b c d))
    (x : TriForm) (u : DirectRightNestedCGChannel a b c)
    (hdegree : directRightFinalDegree u ≠ d) :
    fixedRightSectionDataSum qs x u ≈ 0 := by
  induction qs with
  | nil => exact Q'.eqv_refl _
  | cons q rest ih =>
      have hlabels : ¬ (u.k = q.p ∧ u.outer.k = q.r) := by
        intro h
        apply hdegree
        have hqdeg := q.degree_eq
        unfold directRightFinalDegree
        omega
      have hzero : fixedRightSectionData q (fixedRightAnalysis q x) u ≈ 0 := by
        unfold fixedRightSectionData
        rw [dif_neg hlabels]
        exact Q'.eqv_refl _
      simp only [fixedRightSectionDataSum]
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hzero ih)
        (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- Every synthesized coordinate of a different final degree is zero. -/
theorem fixedRightSectionSum_coordinate_zero_of_finalDegree_ne
    {a b c d : Nat} (qs : List (FixedRightCGChannel a b c d))
    (x : TriForm) (u : DirectRightNestedCGChannel a b c)
    (hdegree : directRightFinalDegree u ≠ d) :
    directRightNestedCoordinates a b c (fixedRightSectionSum qs x) u ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (directRightNestedCoordinates_reconstruct a b c
      (fixedRightSectionDataSum qs x) u)
    (fixedRightSectionDataSum_zero_of_finalDegree_ne qs x u hdegree)

/-! ## Finite evaluation and the concrete Schur wrapper -/

/-- Total lookup in a channel list.  All load-bearing uses below have an
index below the list length, so the fallback is never selected. -/
def fixedRightChannelAt {a b c d : Nat}
    (fallback : FixedRightCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c d)) (q : Nat) :
    FixedRightCGChannel a b c d :=
  (qs[q]?).getD fallback

/-- Pointwise sum of a list of output forms. -/
def formListSum {α : Type} : List α → (α → BForm) → BForm
  | [], _ => zeroF
  | x :: xs, term => addForm (term x) (formListSum xs term)

/-- Evaluating every concrete channel section separately and summing the
resulting output forms. -/
def fixedRightEvalSectionSum {a b c d : Nat}
    (evalL : TriForm → BForm)
    (qs : List (FixedRightCGChannel a b c d)) (x : TriForm) : BForm :=
  formListSum qs (fun q =>
    evalL (fixedRightSection q (fixedRightAnalysis q x)))

/-- A `formPrefix` indexed by total list lookup equals the recursive list
sum.  This is the exact bridge from the constructive enumeration to the
Nat-indexed ambient Schur interface. -/
theorem formPrefix_channelAt {a b c d : Nat}
    (fallback : FixedRightCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c d))
    (term : FixedRightCGChannel a b c d → BForm) :
    BFormEqv
      (formPrefix qs.length (fun q =>
        term (fixedRightChannelAt fallback qs q)))
      (formListSum qs term) := by
  induction qs with
  | nil =>
      intro s
      exact Q'.eqv_refl _
  | cons q rest ih =>
      intro s
      simp only [List.length_cons, formPrefix, formListSum, addForm]
      exact Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (by simpa only [fixedRightChannelAt, List.getElem?_cons_succ]
          using ih s)

/-- **Concrete fixed-output Schur theorem with finite reconstruction.**

The earlier concrete wrapper's monomial reconstruction hypothesis is now
discharged by the enumerated section sum.  Two map-specific evaluation laws
remain explicit and separate:

* `hevalProjection`: on physical monomials, `evalL` ignores coordinates of
  final degree different from `d`;
* `hevalSectionSum`: evaluating the single synthesis of summed section data
  equals the list sum of separately evaluated global sections.

The diagonal and lowering hypotheses are unchanged. -/
theorem directRightFixedOutput_schur
    (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm)
    (fallback : FixedRightCGChannel a b c d)
    (evalL : TriForm → BForm)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q,
      q < (fixedRightChannels a b c d).length → HasDiagonalModel
        (ambientInduced evalL (fixedRightSection
          (fixedRightChannelAt fallback
            (fixedRightChannels a b c d) q))) (coeff q))
    (hF : ∀ q,
      q < (fixedRightChannels a b c d).length →
        EndomorphismLoweringCovariant d
          (ambientInduced evalL (fixedRightSection
            (fixedRightChannelAt fallback
              (fixedRightChannels a b c d) q))))
    (hpack : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (L (mono i) (mono j) (mono l))
          (evalL (pureTri (mono i) (mono j) (mono l))))
    (hevalProjection : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv
          (evalL (pureTri (mono i) (mono j) (mono l)))
          (evalL (fixedRightEnumeratedSectionSum a b c d
            (pureTri (mono i) (mono j) (mono l)))))
    (hevalSectionSum : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv
          (evalL (fixedRightEnumeratedSectionSum a b c d
            (pureTri (mono i) (mono j) (mono l))))
          (fixedRightEvalSectionSum evalL
            (fixedRightChannels a b c d)
            (pureTri (mono i) (mono j) (mono l)))) :
    TriMapEqv a b c d L
      (rightChannelPrefix a b c d
        (fixedRightChannels a b c d).length
        (fun q => (fixedRightChannelAt fallback
          (fixedRightChannels a b c d) q).p)
        (fun q => coeff q 0)) := by
  apply triMapEqv_rightFixedChannels_of_sections_schur
    a b c d (fixedRightChannels a b c d).length L
    (fixedRightChannelAt fallback (fixedRightChannels a b c d))
    evalL coeff hdiag hF hpack
  intro i hi j hj l hl
  let x := pureTri (mono i) (mono j) (mono l)
  have hprojection := hevalProjection i hi j hj l hl
  have hsections := hevalSectionSum i hi j hj l hl
  have hprefix := formPrefix_channelAt fallback
    (fixedRightChannels a b c d)
    (fun q => evalL (fixedRightSection q (fixedRightAnalysis q x)))
  intro s
  exact Q'.eqv_trans _ _ _ (hprojection s)
    (Q'.eqv_trans _ _ _ (hsections s)
      (Q'.eqv_symm (by
        simpa only [x, fixedRightEvalSectionSum, ambientInduced]
          using hprefix s)))

end YMGap.Continuum.SU2DirectRightFixedOutputReconstruction

#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.fixedRightSectionData_at_fixed
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.fixedRightSectionDataSum_at_fixed
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.fixedRightAnalysis_sectionSum
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.fixedRightAnalysis_enumeratedSectionSum
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.fixedRightAnalysis_zero_outside
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.fixedRightSectionSum_coordinate_zero_of_finalDegree_ne
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.formPrefix_channelAt
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputReconstruction.directRightFixedOutput_schur
