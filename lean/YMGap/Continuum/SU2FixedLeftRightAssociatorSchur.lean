/-
# Concrete all-label fixed-output SU(2) associator row

This successor instantiates the finite ordered-right Schur wrapper with the
actual fixed-left transvectant evaluator.  Final-degree projection is supplied
by the preceding block-diagonality theorem; here Cartan grading and lowering
covariance provide the diagonal Schur models for every enumerated section.
-/

import YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation

namespace YMGap.Continuum.SU2FixedLeftRightAssociatorSchur

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.SU2DiagonalSchurUniqueness
open YMGap.Continuum.SU2ChannelSectionSchurReconstruction
open YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftEvaluationLinearity
open YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock
open YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation
open YMGap.Continuum.SU2ProjectedRawSupportedBridge

local infix:50 " ≈ " => Q'.eqv

/-- Forget a fixed-output right channel's final-degree proof while retaining
its two contraction labels. -/
def directChannelOfFixedRight {a b c d : Nat}
    (qR : FixedRightCGChannel a b c d) :
    DirectRightNestedCGChannel a b c :=
  fixedRightNestedChannel qR 0 (by omega)

theorem directChannelOfFixedRight_degree {a b c d : Nat}
    (qR : FixedRightCGChannel a b c d) :
    directRightFinalDegree (directChannelOfFixedRight qR) = d := by
  simpa only [directChannelOfFixedRight, fixedRightNestedChannel,
    directRightFinalDegree] using qR.degree_eq

/-- Left and right channels with the same final degree remove the same total
number of contractions. -/
theorem fixedLeft_fixedRight_contraction_sum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    qL.r + qL.k = qR.r + qR.p := by
  let u := directChannelOfFixedRight qR
  have hL := fixedLeft_total_degree qL
  have hR := directRight_total_degree u
  have hLle := fixedLeft_total_contraction_le qL
  have hRle := directRight_total_contraction_le u
  have hdegree := directChannelOfFixedRight_degree qR
  rw [hdegree] at hR
  dsimp only [u, directChannelOfFixedRight, fixedRightNestedChannel] at hR hRle
  omega

/-- The exact diagonal coefficient of the section-induced endomorphism. -/
def fixedLeftRightDiagonalCoeff {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (s : Nat) : Q' :=
  fixedLeftAnalysis qL (fixedRightSection qR (mono s)) s

/-- Cartan grading kills every off-diagonal monomial coefficient of a
same-final-degree channel section. -/
theorem fixedLeft_fixedRightSection_mono_zero_offdiag
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (t s : Nat) (hne : s ≠ t) :
    fixedLeftAnalysis qL (fixedRightSection qR (mono t)) s ≈ 0 := by
  let u := directChannelOfFixedRight qR
  have hsum := fixedLeft_fixedRight_contraction_sum qL qR
  have hzero := fixedLeftAnalysis_directRightSection_mono_zero_of_shell_ne
    qL u t s (by
      dsimp only [u, directChannelOfFixedRight, fixedRightNestedChannel]
      intro hshell
      apply hne
      omega)
  simpa only [u, directChannelOfFixedRight, fixedRightNestedChannel,
    fixedRightSection, directRightChannelSection, fixedRightSectionData,
    directRightChannelSectionData] using hzero

/-- The section-induced endomorphism is diagonal on every monomial. -/
theorem fixedLeft_fixedRightSection_mono_diagonal
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (t : Nat) :
    BFormEqv
      (fixedLeftAnalysis qL (fixedRightSection qR (mono t)))
      (diagonalMap (fixedLeftRightDiagonalCoeff qL qR) (mono t)) := by
  intro s
  by_cases hst : s = t
  · subst s
    unfold fixedLeftRightDiagonalCoeff diagonalMap mono
    rw [if_pos rfl]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · have hzero := fixedLeft_fixedRightSection_mono_zero_offdiag
      qL qR t s hst
    unfold diagonalMap mono
    rw [if_neg hst]
    exact Q'.eqv_trans _ 0 _ hzero (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-- The concrete section-induced map commutes with lowering on the complete
physical monomial window. -/
theorem fixedLeft_fixedRightSection_loweringCovariant
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    EndomorphismLoweringCovariant d
      (ambientInduced (fixedLeftAnalysis qL) (fixedRightSection qR)) := by
  intro k hk
  let u := directChannelOfFixedRight qR
  have hsupp := mono_degreeSupported d k (by omega)
  have hF := fixedLeft_directRightSection_Fop qL u (mono k)
    (by
      rw [directChannelOfFixedRight_degree qR]
      exact hsupp)
  simpa only [ambientInduced, u, directChannelOfFixedRight,
    fixedRightNestedChannel, fixedRightSection, directRightChannelSection,
    fixedRightSectionData, directRightChannelSectionData] using hF

/-! ## Extension of diagonality from monomials to arbitrary forms -/

theorem fixedLeft_fixedRightSection_congr
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (v w : BForm)
    (hvw : BFormEqv v w) :
    BFormEqv
      (fixedLeftAnalysis qL (fixedRightSection qR v))
      (fixedLeftAnalysis qL (fixedRightSection qR w)) := by
  let u := directChannelOfFixedRight qR
  simpa only [u, directChannelOfFixedRight, fixedRightNestedChannel,
    fixedRightSection, directRightChannelSection, fixedRightSectionData,
    directRightChannelSectionData] using
      fixedLeft_directRightSection_congr qL u v w hvw

theorem fixedLeft_fixedRightSection_add
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (v w : BForm) :
    BFormEqv
      (fixedLeftAnalysis qL (fixedRightSection qR (addForm v w)))
      (addForm
        (fixedLeftAnalysis qL (fixedRightSection qR v))
        (fixedLeftAnalysis qL (fixedRightSection qR w))) := by
  let u := directChannelOfFixedRight qR
  simpa only [u, directChannelOfFixedRight, fixedRightNestedChannel,
    fixedRightSection, directRightChannelSection, fixedRightSectionData,
    directRightChannelSectionData] using
      fixedLeft_directRightSection_add qL u v w

theorem fixedLeft_fixedRightSection_scale
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (q : Q') (v : BForm) :
    BFormEqv
      (fixedLeftAnalysis qL (fixedRightSection qR (scaleForm q v)))
      (scaleForm q (fixedLeftAnalysis qL (fixedRightSection qR v))) := by
  let u := directChannelOfFixedRight qR
  simpa only [u, directChannelOfFixedRight, fixedRightNestedChannel,
    fixedRightSection, directRightChannelSection, fixedRightSectionData,
    directRightChannelSectionData] using
      fixedLeft_directRightSection_scale qL u q v

theorem fixedLeft_fixedRightSection_zero
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    BFormEqv
      (fixedLeftAnalysis qL (fixedRightSection qR zeroF)) zeroF := by
  let u := directChannelOfFixedRight qR
  simpa only [u, directChannelOfFixedRight, fixedRightNestedChannel,
    fixedRightSection, directRightChannelSection, fixedRightSectionData,
    directRightChannelSectionData] using
      fixedLeft_directRightSection_zero qL u

/-- A fixed-right section reads no coefficients beyond its final degree. -/
theorem fixedRightSection_truncate_finalDegree
    {a b c d : Nat} (qR : FixedRightCGChannel a b c d) (v : BForm) :
    PhysicalBoxEqv a b c
      (fixedRightSection qR (truncateForm v (d + 1)))
      (fixedRightSection qR v) := by
  apply directRightNestedReconstruct_congr_data
  intro u
  unfold fixedRightSectionData truncateForm
  by_cases hlabels : u.k = qR.p ∧ u.outer.k = qR.r
  · rw [dif_pos hlabels, dif_pos hlabels]
    rw [if_pos]
    · exact Q'.eqv_refl _
    · have hdegree := qR.degree_eq
      have hs := u.outer.s_le
      omega
  · rw [dif_neg hlabels, dif_neg hlabels]
    exact Q'.eqv_refl _

theorem diagonalMap_truncateForm_succ (coeff : Nat → Q')
    (v : BForm) (N : Nat) :
    BFormEqv
      (addForm (diagonalMap coeff (truncateForm v N))
        (scaleForm (v N) (diagonalMap coeff (mono N))))
      (diagonalMap coeff (truncateForm v (N + 1))) := by
  intro s
  have htrunc := truncateForm_succ v N s
  exact Q'.eqv_trans _
    (coeff s * (truncateForm v N s + v N * mono N s)) _
    (by
      unfold addForm diagonalMap scaleForm
      ring_qeqv)
    (Q'.mul_eqv_congr_left (coeff s) _ _ htrunc)

/-- Every finite coefficient prefix is carried diagonally. -/
theorem fixedLeft_fixedRightSection_truncate_diagonal
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (v : BForm) :
    ∀ N, BFormEqv
      (fixedLeftAnalysis qL (fixedRightSection qR (truncateForm v N)))
      (diagonalMap (fixedLeftRightDiagonalCoeff qL qR)
        (truncateForm v N)) := by
  intro N
  induction N with
  | zero =>
      have htrunc : BFormEqv (truncateForm v 0) zeroF := by
        intro s
        unfold truncateForm zeroF
        rw [if_neg (by omega : ¬s < 0)]
        exact Q'.eqv_refl _
      have hcongr := fixedLeft_fixedRightSection_congr qL qR
        (truncateForm v 0) zeroF htrunc
      intro s
      exact Q'.eqv_trans _ _ _ (hcongr s)
        (Q'.eqv_trans _ 0 _ (fixedLeft_fixedRightSection_zero qL qR s)
          (by
            unfold diagonalMap truncateForm
            rw [if_neg (by omega : ¬s < 0)]
            exact Q'.eqv_symm (Q'.mul_zero_eqv _)))
  | succ N ih =>
      have htrunc : BFormEqv
          (addForm (truncateForm v N) (scaleForm (v N) (mono N)))
          (truncateForm v (N + 1)) := by
        intro s
        simpa only [addForm, scaleForm] using truncateForm_succ v N s
      have hcongr := fixedLeft_fixedRightSection_congr qL qR
        (addForm (truncateForm v N) (scaleForm (v N) (mono N)))
        (truncateForm v (N + 1)) htrunc
      have hadd := fixedLeft_fixedRightSection_add qL qR
        (truncateForm v N) (scaleForm (v N) (mono N))
      have hscale := fixedLeft_fixedRightSection_scale qL qR
        (v N) (mono N)
      have hmono := fixedLeft_fixedRightSection_mono_diagonal qL qR N
      have hscaledMono : BFormEqv
          (fixedLeftAnalysis qL
            (fixedRightSection qR (scaleForm (v N) (mono N))))
          (scaleForm (v N)
            (diagonalMap (fixedLeftRightDiagonalCoeff qL qR) (mono N))) := by
        intro s
        exact Q'.eqv_trans _ _ _ (hscale s)
          (Q'.mul_eqv_congr_left (v N) _ _ (hmono s))
      intro s
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongr s))
        (Q'.eqv_trans _ _ _ (hadd s)
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (ih s) (hscaledMono s))
            (diagonalMap_truncateForm_succ
              (fixedLeftRightDiagonalCoeff qL qR) v N s)))

/-- **Concrete diagonal model for every fixed-output section-induced
endomorphism.** -/
theorem fixedLeft_fixedRightSection_hasDiagonalModel
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    HasDiagonalModel
      (ambientInduced (fixedLeftAnalysis qL) (fixedRightSection qR))
      (fixedLeftRightDiagonalCoeff qL qR) := by
  intro v
  unfold ambientInduced
  have htrunc := fixedLeft_fixedRightSection_truncate_diagonal
    qL qR v (d + 1)
  have hsection := fixedRightSection_truncate_finalDegree qR v
  have hleft := fixedLeftAnalysis_congr qL _ _ hsection
  intro s
  by_cases hs : s ≤ d
  · have hvalue : truncateForm v (d + 1) s ≈ v s := by
      unfold truncateForm
      rw [if_pos (by omega)]
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hleft s))
      (Q'.eqv_trans _ _ _ (htrunc s)
        (Q'.mul_eqv_congr_left
          (fixedLeftRightDiagonalCoeff qL qR s) _ _ hvalue))
  · have hleftZero := fixedLeftAnalysis_zero_outside qL
      (fixedRightSection qR v) s (by omega)
    have hcoeffZero : fixedLeftRightDiagonalCoeff qL qR s ≈ 0 := by
      unfold fixedLeftRightDiagonalCoeff
      exact fixedLeftAnalysis_zero_outside qL
        (fixedRightSection qR (mono s)) s (by omega)
    exact Q'.eqv_trans _ 0 _ hleftZero
      (Q'.eqv_symm (Q'.eqv_trans _ (0 * v s) _
        (Q'.mul_eqv_congr_right _ _ (v s) hcoeffZero)
        (Q'.zero_mul_eqv (v s))))

/-! ## Concrete fixed-output Schur row -/

/-- The concrete fixed-left analysis agrees with raw `triLeft` on every
coefficient, including the zero extension above the final degree. -/
theorem fixedLeftAnalysis_pure_monomial_eq_triLeft_all
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c) :
    BFormEqv
      (fixedLeftAnalysis qL (pureTri (mono i) (mono j) (mono l)))
      (triLeft a b c d qL.intermediate (mono i) (mono j) (mono l)) := by
  intro s
  by_cases hs : s ≤ d
  · exact fixedLeftAnalysis_pure_monomial_eq_triLeft
      qL i j l hi hj hl s (by omega)
  · have hleft := fixedLeftAnalysis_zero_outside qL
      (pureTri (mono i) (mono j) (mono l)) s (by omega)
    let source : BForm2 :=
      tprod (transvect a b qL.k (tprod (mono i) (mono j))) (mono l)
    have hordersInner := fixedLeft_inner_couplingOrder qL
    have hordersOuter := fixedLeft_outer_couplingOrder qL
    have hright := transvect_zero_above_degree
      qL.intermediate c qL.r source
      (Nat.le_min.mp qL.r_le).1 (Nat.le_min.mp qL.r_le).2
      (by simpa only [source] using
        fixedLeft_outerTensor_supported qL i j l hi hj hl)
      s (by
        have hdegree := qL.degree_eq
        unfold FixedLeftCGChannel.intermediate at hdegree ⊢
        omega)
    have hright' :
        triLeft a b c d qL.intermediate
          (mono i) (mono j) (mono l) s ≈ 0 := by
      simpa only [triLeft, hordersInner, hordersOuter, source] using hright
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright')

/-- All wrapper premises are discharged for the concrete fixed-left row;
the only temporary parameter is a total lookup fallback, irrelevant at every
bounded enumerated index. -/
theorem fixedLeft_directRightFixedOutput_schur_withFallback
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (fallback : FixedRightCGChannel a b c d) :
    TriMapEqv a b c d (triLeft a b c d qL.intermediate)
      (rightChannelPrefix a b c d
        (fixedRightChannels a b c d).length
        (fun q => (fixedRightChannelAt fallback
          (fixedRightChannels a b c d) q).p)
        (fun q => fixedLeftRightDiagonalCoeff qL
          (fixedRightChannelAt fallback
            (fixedRightChannels a b c d) q) 0)) := by
  let coeff : Nat → Nat → Q' := fun q s =>
    fixedLeftRightDiagonalCoeff qL
      (fixedRightChannelAt fallback (fixedRightChannels a b c d) q) s
  apply directRightFixedOutput_schur a b c d
    (triLeft a b c d qL.intermediate) fallback (fixedLeftAnalysis qL) coeff
  · intro q _hq
    exact fixedLeft_fixedRightSection_hasDiagonalModel qL
      (fixedRightChannelAt fallback (fixedRightChannels a b c d) q)
  · intro q _hq
    exact fixedLeft_fixedRightSection_loweringCovariant qL
      (fixedRightChannelAt fallback (fixedRightChannels a b c d) q)
  · intro i hi j hj l hl
    intro s
    exact Q'.eqv_symm
      (fixedLeftAnalysis_pure_monomial_eq_triLeft_all qL i j l
        (by omega) (by omega) (by omega) s)
  · intro i _hi j _hj l _hl
    exact fixedLeftAnalysis_projection qL
      (pureTri (mono i) (mono j) (mono l))
  · intro i _hi j _hj l _hl
    exact fixedLeftAnalysis_enumeratedSectionSum qL
      (pureTri (mono i) (mono j) (mono l))

/-! ## Canonical constructive fallback and all-label theorem -/

/-- Reassociate one valid left channel to an explicit valid right channel.
Writing `R = k+r` for the total contraction count, choose the right inner
order `p = R-a` and outer order `R-p = min R a`.  The left-channel triangle
bounds and nonnegative residual degree prove both right triangle bounds. -/
def fixedRightFallbackOfFixedLeft
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) :
    FixedRightCGChannel a b c d := by
  let R := qL.k + qL.r
  let p := R - a
  let rR := R - p
  have hk := Nat.le_min.mp qL.k_le
  have hr := Nat.le_min.mp qL.r_le
  have htotal := fixedLeft_total_contraction_le qL
  have hdegree := fixedLeft_total_degree qL
  have hpB : p ≤ b := by
    unfold p R
    omega
  have hpC : p ≤ c := by
    unfold p R
    omega
  have hp : p ≤ min b c := Nat.le_min.mpr ⟨hpB, hpC⟩
  have hrA : rR ≤ a := by
    unfold rR p R
    omega
  have hrI : rR ≤ b + c - 2 * p := by
    unfold rR p R
    omega
  have hrRight : rR ≤ min a (b + c - 2 * p) :=
    Nat.le_min.mpr ⟨hrA, hrI⟩
  refine
    { p := p
      p_le := hp
      r := rR
      r_le := hrRight
      degree_eq := ?_ }
  dsimp only [rR, p, R] at hpB hpC hrA hrI hdegree htotal ⊢
  omega

theorem fixedRightFallbackOfFixedLeft_mem
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) :
    fixedRightFallbackOfFixedLeft qL ∈ fixedRightChannels a b c d :=
  fixedRightChannels_complete (fixedRightFallbackOfFixedLeft qL)

/-- **Actual all-label fixed-output associator row.**  Every valid left
channel is a finite exact rational combination of all enumerated valid right
channels, with coefficients derived as the checked section diagonal entries. -/
theorem fixedLeft_directRightFixedOutput_schur
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) :
    TriMapEqv a b c d (triLeft a b c d qL.intermediate)
      (rightChannelPrefix a b c d
        (fixedRightChannels a b c d).length
        (fun q => (fixedRightChannelAt (fixedRightFallbackOfFixedLeft qL)
          (fixedRightChannels a b c d) q).p)
        (fun q => fixedLeftRightDiagonalCoeff qL
          (fixedRightChannelAt (fixedRightFallbackOfFixedLeft qL)
            (fixedRightChannels a b c d) q) 0)) := by
  exact fixedLeft_directRightFixedOutput_schur_withFallback qL
    (fixedRightFallbackOfFixedLeft qL)

end YMGap.Continuum.SU2FixedLeftRightAssociatorSchur

#print axioms YMGap.Continuum.SU2FixedLeftRightAssociatorSchur.fixedLeft_fixedRightSection_loweringCovariant
#print axioms YMGap.Continuum.SU2FixedLeftRightAssociatorSchur.fixedLeft_fixedRightSection_hasDiagonalModel
#print axioms YMGap.Continuum.SU2FixedLeftRightAssociatorSchur.fixedLeft_directRightFixedOutput_schur_withFallback
#print axioms YMGap.Continuum.SU2FixedLeftRightAssociatorSchur.fixedRightFallbackOfFixedLeft_mem
#print axioms YMGap.Continuum.SU2FixedLeftRightAssociatorSchur.fixedLeft_directRightFixedOutput_schur
