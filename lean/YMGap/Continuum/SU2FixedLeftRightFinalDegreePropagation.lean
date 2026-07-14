/-
# Lowering propagation across distinct final-degree blocks

This successor proves the ordered-right half of total-lowering covariance,
uses coordinate uniqueness to show that every supported right-channel section
intertwines lowering, and combines that with the frozen Cartan grading and
fixed-left covariance to eliminate cross-final-degree coefficients.
-/

import YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock

namespace YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.SU2TransvectantOutputRowInvariant
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2ProjectedRawSupportedBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftEvaluationLinearity
open YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## Ordered-right total-lowering covariance -/

theorem rightTriSlice_supported (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (i : Nat) :
    BidegreeSupported b c (rightTriSlice x i) := by
  intro j l hout
  unfold rightTriSlice
  exact hx i j l (by rcases hout with hj | hl <;> omega)

theorem rightTriSlice_F3 (a b c : Nat) (x : TriForm) (i : Nat) :
    BForm2Eqv (rightTriSlice (F3 a b c x) i)
      (badd
        (bscale (Q'.ofNat (i + 1)) (rightTriSlice x (i + 1)))
        (F2 b c (rightTriSlice x i))) := by
  intro j l
  unfold rightTriSlice F3 badd bscale F2
  exact Q'.eqv_refl _

theorem lastPairOutput_eq_raw (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (k i s : Nat) :
    lastPairOutput b c x k i s ≈
      transvect b c k (rightTriSlice x i) s := by
  have hproject := bidegreeSupported_eqv_rectProject b c
    (rightTriSlice x i) (rightTriSlice_supported a b c x hx i)
  have hcongr := transvect_congr b c k
    (fun j l => Q'.eqv_symm (hproject j l)) s
  simpa only [lastPairOutput] using hcongr

theorem lastPairOutput_supported (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (k : Nat) (hk : k ≤ min b c) :
    BidegreeSupported a (b + c - 2 * k) (lastPairOutput b c x k) := by
  intro i s hout
  rcases hout with hi | hs
  · by_cases hs' : s ≤ b + c - 2 * k
    · let q : PhysicalCGChannel b c :=
        { k := k, k_le := hk, s := s, s_le := hs' }
      have hslice : ∀ j l, j ≤ b → l ≤ c →
          j + l = q.shell → rightTriSlice x i j l ≈ 0 := by
        intro j l hj hl _
        unfold rightTriSlice
        exact hx i j l (Or.inl hi)
      have hzero := globalTransvectCoordinates_zero_of_source_shell
        b c (rightTriSlice x i) q hslice
      simpa only [lastPairOutput, globalTransvectCoordinates, q] using hzero
    · have hmin := Nat.le_min.mp hk
      exact transvect_zero_above_degree b c k
        (rectProject b c (rightTriSlice x i)) hmin.1 hmin.2
        (rectProject_supported b c (rightTriSlice x i)) s (by omega)
  · have hmin := Nat.le_min.mp hk
    exact transvect_zero_above_degree b c k
      (rectProject b c (rightTriSlice x i)) hmin.1 hmin.2
      (rectProject_supported b c (rightTriSlice x i)) s hs

theorem lastPairOutput_F3 (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (k : Nat) (hk : k ≤ min b c) :
    BForm2Eqv (lastPairOutput b c (F3 a b c x) k)
      (F2 a (b + c - 2 * k) (lastPairOutput b c x k)) := by
  intro i s
  have hxF := F3_supported a b c x hx
  have hraw := lastPairOutput_eq_raw a b c (F3 a b c x) hxF k i s
  have hslice := transvect_congr b c k (rightTriSlice_F3 a b c x i) s
  have hadd := transvect_add b c k
    (bscale (Q'.ofNat (i + 1)) (rightTriSlice x (i + 1)))
    (F2 b c (rightTriSlice x i)) s
  have hfirst := transvect_scale b c k (Q'.ofNat (i + 1))
    (rightTriSlice x (i + 1)) s
  have hmin := Nat.le_min.mp hk
  have hinner := transvect_F2_supported b c k s (rightTriSlice x i)
    hmin.1 hmin.2 (rightTriSlice_supported a b c x hx i)
  have hrawFirst := lastPairOutput_eq_raw a b c x hx k (i + 1) s
  have hrawNext := lastPairOutput_eq_raw a b c x hx k i (s + 1)
  refine Q'.eqv_trans _ _ _ hraw ?_
  refine Q'.eqv_trans _ _ _ hslice ?_
  refine Q'.eqv_trans _ _ _ hadd ?_
  unfold F2
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ hfirst
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hrawFirst)))
    (by
      have h := Q'.eqv_trans _ _ _ hinner
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hrawNext))
      simpa only [Fop] using h)

/-- Complete zero-extended output form for one arbitrary ordered-right
contraction-order pair. -/
def directRightChannelAnalysis {a b c : Nat}
    (q : DirectRightNestedCGChannel a b c) (x : TriForm) : BForm :=
  fun s => if hs : s ≤ a + (b + c - 2 * q.k) - 2 * q.outer.k then
    directRightNestedCoordinates a b c x
      { k := q.k
        k_le := q.k_le
        outer :=
          { k := q.outer.k
            k_le := q.outer.k_le
            s := s
            s_le := hs } }
  else 0

theorem directRightNestedCoordinates_F3 (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x)
    (q : DirectRightNestedCGChannel a b c) :
    directRightNestedCoordinates a b c (F3 a b c x) q ≈
      Fop (a + (b + c - 2 * q.k) - 2 * q.outer.k)
        (directRightChannelAnalysis q x) q.outer.s := by
  have hxF := F3_supported a b c x hx
  have hsupp := lastPairOutput_supported a b c x hx q.k q.k_le
  have hsuppF := lastPairOutput_supported a b c (F3 a b c x) hxF
    q.k q.k_le
  have hrawF := globalTransvectCoordinates_eq_raw_of_supported
    a (b + c - 2 * q.k)
    (lastPairOutput b c (F3 a b c x) q.k) hsuppF q.outer
  have hlast := transvect_congr a (b + c - 2 * q.k) q.outer.k
    (lastPairOutput_F3 a b c x hx q.k q.k_le) q.outer.s
  have hmin := Nat.le_min.mp q.outer.k_le
  have houter := transvect_F2_supported
    a (b + c - 2 * q.k) q.outer.k q.outer.s
    (lastPairOutput b c x q.k) hmin.1 hmin.2 hsupp
  have hrawAt : ∀ s,
      transvect a (b + c - 2 * q.k) q.outer.k
          (lastPairOutput b c x q.k) s ≈
        directRightChannelAnalysis q x s := by
    intro s
    by_cases hsBound : s ≤ a + (b + c - 2 * q.k) - 2 * q.outer.k
    · let outer : PhysicalCGChannel a (b + c - 2 * q.k) :=
        { k := q.outer.k, k_le := q.outer.k_le, s := s, s_le := hsBound }
      have hraw := globalTransvectCoordinates_eq_raw_of_supported
        a (b + c - 2 * q.k) (lastPairOutput b c x q.k) hsupp outer
      exact Q'.eqv_symm (by
        simp only [directRightChannelAnalysis, dif_pos hsBound]
        simpa only [directRightNestedCoordinates, outer] using hraw)
    · have hzero := transvect_zero_above_degree
        a (b + c - 2 * q.k) q.outer.k
        (lastPairOutput b c x q.k) hmin.1 hmin.2 hsupp s (by omega)
      exact Q'.eqv_trans _ 0 _ hzero (by
        simp only [directRightChannelAnalysis, dif_neg hsBound]
        exact Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightNestedCoordinates] using hrawF)
    (Q'.eqv_trans _ _ _ hlast
      (Q'.eqv_trans _ _ _ houter
        (Q'.mul_eqv_congr_left _ _ _ (hrawAt (q.outer.s + 1)))))

/-! ## Lowering covariance of one right-channel section -/

/-- Literal zero support beyond a binary form's physical degree. -/
def FormDegreeSupported (D : Nat) (v : BForm) : Prop :=
  ∀ s, D < s → v s ≈ 0

theorem mono_degreeSupported (D t : Nat) (ht : t ≤ D) :
    FormDegreeSupported D (mono t) := by
  intro s hs
  unfold mono
  rw [if_neg (by omega : ¬ s = t)]
  exact Q'.eqv_refl _

/-- Exact analysis of an arbitrary ordered-right section, including the
zero extension beyond the analyzing channel's final degree. -/
theorem directRightChannelAnalysis_section {a b c : Nat}
    (u w : DirectRightNestedCGChannel a b c) (v : BForm) (s : Nat) :
    directRightChannelAnalysis w (directRightChannelSection u v) s ≈
      if _hs : s ≤ a + (b + c - 2 * w.k) - 2 * w.outer.k then
        if _h : w.k = u.k ∧ w.outer.k = u.outer.k then v s else 0
      else 0 := by
  unfold directRightChannelAnalysis
  by_cases hs : s ≤ a + (b + c - 2 * w.k) - 2 * w.outer.k
  · rw [dif_pos hs, dif_pos hs]
    have hcoord := directRightNestedCoordinates_reconstruct a b c
      (directRightChannelSectionData u v)
      { k := w.k
        k_le := w.k_le
        outer :=
          { k := w.outer.k
            k_le := w.outer.k_le
            s := s
            s_le := hs } }
    exact Q'.eqv_trans _ _ _
      (by simpa only [directRightChannelSection] using hcoord)
      (by unfold directRightChannelSectionData; rfl)
  · rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_refl _

/-- Total lowering of a supported right-channel section has exactly the
dependent coordinates of the section of the lowered output form. -/
theorem directRightNestedCoordinates_F3_channelSection
    {a b c : Nat} (u : DirectRightNestedCGChannel a b c)
    (v : BForm) (hv : FormDegreeSupported (directRightFinalDegree u) v)
    (w : DirectRightNestedCGChannel a b c) :
    directRightNestedCoordinates a b c
        (F3 a b c (directRightChannelSection u v)) w ≈
      directRightChannelSectionData u
        (Fop (directRightFinalDegree u) v) w := by
  have hcov := directRightNestedCoordinates_F3 a b c
    (directRightChannelSection u v)
    (directRightChannelSection_supported u v) w
  unfold Fop at hcov ⊢
  by_cases hlabels : w.k = u.k ∧ w.outer.k = u.outer.k
  · have hdegree :
        a + (b + c - 2 * w.k) - 2 * w.outer.k =
          directRightFinalDegree u := by
      unfold directRightFinalDegree
      omega
    unfold directRightChannelSectionData
    rw [dif_pos hlabels]
    by_cases hnext : w.outer.s + 1 ≤
        a + (b + c - 2 * w.k) - 2 * w.outer.k
    · have hanalysis := directRightChannelAnalysis_section
        u w v (w.outer.s + 1)
      rw [dif_pos hnext, dif_pos hlabels] at hanalysis
      exact Q'.eqv_trans _ _ _ hcov
        (Q'.mul_eqv_congr_left _ _ _ hanalysis)
    · have hanalysis := directRightChannelAnalysis_section
        u w v (w.outer.s + 1)
      rw [dif_neg hnext] at hanalysis
      have hvzero : v (w.outer.s + 1) ≈ 0 := by
        apply hv
        rw [← hdegree]
        omega
      exact Q'.eqv_trans _ _ _ hcov
        (Q'.eqv_trans _ (Q'.ofNat (w.outer.s + 1) * 0) _
          (Q'.mul_eqv_congr_left _ _ _ hanalysis)
          (Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ hvzero)))
  · unfold directRightChannelSectionData
    rw [dif_neg hlabels]
    by_cases hnext : w.outer.s + 1 ≤
        a + (b + c - 2 * w.k) - 2 * w.outer.k
    · have hanalysis := directRightChannelAnalysis_section
        u w v (w.outer.s + 1)
      rw [dif_pos hnext, dif_neg hlabels] at hanalysis
      exact Q'.eqv_trans _ _ _ hcov
        (Q'.eqv_trans _ (Q'.ofNat (w.outer.s + 1) * 0) _
          (Q'.mul_eqv_congr_left _ _ _ hanalysis)
          (Q'.mul_zero_eqv _))
    · have hanalysis := directRightChannelAnalysis_section
        u w v (w.outer.s + 1)
      rw [dif_neg hnext] at hanalysis
      exact Q'.eqv_trans _ _ _ hcov
        (Q'.eqv_trans _ (Q'.ofNat (w.outer.s + 1) * 0) _
          (Q'.mul_eqv_congr_left _ _ _ hanalysis)
          (Q'.mul_zero_eqv _))

/-- **Concrete ordered-right section lowering covariance.** -/
theorem F3_directRightChannelSection {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c)
    (v : BForm) (hv : FormDegreeSupported (directRightFinalDegree u) v) :
    PhysicalBoxEqv a b c
      (F3 a b c (directRightChannelSection u v))
      (directRightChannelSection u (Fop (directRightFinalDegree u) v)) := by
  let x := F3 a b c (directRightChannelSection u v)
  let data' := directRightChannelSectionData u
    (Fop (directRightFinalDegree u) v)
  have hcoords : ∀ w : DirectRightNestedCGChannel a b c,
      directRightNestedCoordinates a b c x w ≈ data' w := by
    intro w
    simpa only [x, data'] using
      directRightNestedCoordinates_F3_channelSection u v hv w
  have hcongr := directRightNestedReconstruct_congr_data a b c
    (directRightNestedCoordinates a b c x) data' hcoords
  intro i j l hi hj hl
  have hsemantic := directRightNestedReconstruct_coordinates a b c x
    i j l hi hj hl
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsemantic)
    (by simpa only [x, data', directRightChannelSection] using
      hcongr i j l hi hj hl)

/-- The concrete fixed-left/right cross map commutes with lowering whenever
the right input form is physically supported in its final degree. -/
theorem fixedLeft_directRightSection_Fop {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (v : BForm) (hv : FormDegreeSupported (directRightFinalDegree u) v) :
    BFormEqv
      (fixedLeftAnalysis qL
        (directRightChannelSection u (Fop (directRightFinalDegree u) v)))
      (Fop d (fixedLeftAnalysis qL (directRightChannelSection u v))) := by
  have hsection := F3_directRightChannelSection u v hv
  have hcongr := fixedLeftAnalysis_congr qL _ _ hsection
  have hF := fixedLeftAnalysis_F3 qL (directRightChannelSection u v)
    (directRightChannelSection_supported u v)
  intro s
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongr s)) (hF s)

/-! ## Rational scaling of the concrete analysis/synthesis maps -/

theorem rectProject_bscale (m n : Nat) (q : Q') (x : BForm2) :
    BForm2Eqv (rectProject m n (bscale q x))
      (bscale q (rectProject m n x)) := by
  intro i j
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ n
    · exact Q'.eqv_trans _ _ _
        (rectProject_apply_physical m n (bscale q x) i j hi hj)
        (Q'.mul_eqv_congr_left q _ _
          (Q'.eqv_symm (rectProject_apply_physical m n x i j hi hj)))
    · have hleft := rectProject_zero_outside m n (bscale q x)
        i j (Or.inr (by omega))
      have hright := rectProject_zero_outside m n x i j (Or.inr (by omega))
      exact Q'.eqv_trans _ 0 _ hleft
        (Q'.eqv_symm (Q'.eqv_trans _ (q * 0) _
          (Q'.mul_eqv_congr_left q _ _ hright) (Q'.mul_zero_eqv q)))
  · have hleft := rectProject_zero_outside m n (bscale q x)
      i j (Or.inl (by omega))
    have hright := rectProject_zero_outside m n x i j (Or.inl (by omega))
    exact Q'.eqv_trans _ 0 _ hleft
      (Q'.eqv_symm (Q'.eqv_trans _ (q * 0) _
        (Q'.mul_eqv_congr_left q _ _ hright) (Q'.mul_zero_eqv q)))

theorem globalTransvectCoordinates_bscale (m n : Nat)
    (q : Q') (x : BForm2) (u : PhysicalCGChannel m n) :
    globalTransvectCoordinates m n (bscale q x) u ≈
      q * globalTransvectCoordinates m n x u := by
  have hproject := transvect_congr m n u.k
    (rectProject_bscale m n q x) u.s
  have hscale := transvect_scale m n u.k q (rectProject m n x) u.s
  exact Q'.eqv_trans _ _ _
    (by simpa only [globalTransvectCoordinates] using hproject)
    (by simpa only [globalTransvectCoordinates] using hscale)

def cgDataScale {m n : Nat} (q : Q')
    (data : PhysicalCGChannel m n → Q') :
    PhysicalCGChannel m n → Q' := fun u => q * data u

theorem globalHahnReconstruct_dataScale (m n : Nat) (q : Q')
    (data : PhysicalCGChannel m n → Q') (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) :
    globalHahnReconstruct m n (cgDataScale q data) i j ≈
      bscale q (globalHahnReconstruct m n data) i j := by
  let z := bscale q (globalHahnReconstruct m n data)
  have hcoords : ∀ u : PhysicalCGChannel m n,
      globalTransvectCoordinates m n z u ≈ cgDataScale q data u := by
    intro u
    exact Q'.eqv_trans _ _ _
      (globalTransvectCoordinates_bscale m n q
        (globalHahnReconstruct m n data) u)
      (Q'.mul_eqv_congr_left q _ _
        (Q'.eqv_trans _ _ _
          (globalTransvectCoordinates_eq_hahn m n
            (globalHahnReconstruct m n data) u)
          (globalHahnCoordinates_reconstruct m n data u)))
  exact Q'.eqv_trans _ _ _
    (globalHahnReconstruct_congr m n (cgDataScale q data)
      (globalTransvectCoordinates m n z)
      (fun u => Q'.eqv_symm (hcoords u)) i j hi hj)
    (globalHahnReconstruct_transvectCoordinates m n z i j hi hj)

def directRightDataScale {a b c : Nat} (q : Q')
    (data : DirectRightNestedCGChannel a b c → Q') :
    DirectRightNestedCGChannel a b c → Q' := fun u => q * data u

def triScale (q : Q') (x : TriForm) : TriForm :=
  fun i j l => q * x i j l

theorem directRightNestedReconstruct_dataScale (a b c : Nat) (q : Q')
    (data : DirectRightNestedCGChannel a b c → Q') :
    PhysicalBoxEqv a b c
      (directRightNestedReconstruct a b c (directRightDataScale q data))
      (triScale q (directRightNestedReconstruct a b c data)) := by
  intro i j l hi hj hl
  have hinner : ∀ inner : PhysicalCGChannel b c,
      directRightInnerData (directRightDataScale q data) i inner ≈
        cgDataScale q (directRightInnerData data i) inner := by
    intro inner
    unfold directRightInnerData directRightOuterReconstruct
    simpa only [directRightOuterData, directRightDataScale, cgDataScale]
      using globalHahnReconstruct_dataScale
        a (b + c - 2 * inner.k) q
        (directRightOuterData data inner.k inner.k_le)
        i inner.s hi inner.s_le
  have hcongr := globalHahnReconstruct_congr b c
    (directRightInnerData (directRightDataScale q data) i)
    (cgDataScale q (directRightInnerData data i)) hinner j l hj hl
  have hscale := globalHahnReconstruct_dataScale b c q
    (directRightInnerData data i) j l hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightNestedReconstruct] using hcongr)
    (by simpa only [directRightNestedReconstruct, triScale, bscale] using hscale)

theorem firstPairOutput_triScale (a b c : Nat) (q : Q') (x : TriForm)
    (k : Nat) (hk : k ≤ min a b) :
    PhysicalRectangleEqv (a + b - 2 * k) c
      (firstPairOutput a b (triScale q x) k)
      (bscale q (firstPairOutput a b x k)) := by
  intro s l hs hl
  let inner : PhysicalCGChannel a b :=
    { k := k, k_le := hk, s := s, s_le := hs }
  have hscale := globalTransvectCoordinates_bscale a b q (triSlice x l) inner
  simpa only [firstPairOutput, globalTransvectCoordinates, triSlice,
    triScale, bscale, inner] using hscale

theorem leftNestedCoordinates_triScale (a b c : Nat) (q : Q')
    (x : TriForm) (u : LeftNestedCGChannel a b c) :
    leftNestedCoordinates a b c (triScale q x) u ≈
      q * leftNestedCoordinates a b c x u := by
  have hphysical := firstPairOutput_triScale a b c q x u.k u.k_le
  have hcongr := globalTransvectCoordinates_congr
    (a + b - 2 * u.k) c
    (firstPairOutput a b (triScale q x) u.k)
    (bscale q (firstPairOutput a b x u.k)) hphysical u.outer
  exact Q'.eqv_trans _ _ _
    (by simpa only [leftNestedCoordinates] using hcongr)
    (globalTransvectCoordinates_bscale (a + b - 2 * u.k) c q
      (firstPairOutput a b x u.k) u.outer)

theorem fixedLeftAnalysis_triScale {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (q : Q') (x : TriForm) :
    BFormEqv (fixedLeftAnalysis qL (triScale q x))
      (scaleForm q (fixedLeftAnalysis qL x)) := by
  intro s
  unfold fixedLeftAnalysis scaleForm
  by_cases hs : s ≤ d
  · simp only [dif_pos hs]
    exact leftNestedCoordinates_triScale a b c q x
      (fixedLeftNestedChannel qL s hs)
  · simp only [dif_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv q)

theorem directRightChannelSection_congr {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) (v w : BForm)
    (hvw : BFormEqv v w) :
    PhysicalBoxEqv a b c
      (directRightChannelSection u v) (directRightChannelSection u w) := by
  apply directRightNestedReconstruct_congr_data
  intro q
  unfold directRightChannelSectionData
  by_cases hlabels : q.k = u.k ∧ q.outer.k = u.outer.k
  · rw [dif_pos hlabels, dif_pos hlabels]
    exact hvw q.outer.s
  · rw [dif_neg hlabels, dif_neg hlabels]
    exact Q'.eqv_refl _

theorem directRightChannelSection_scale {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) (q : Q') (v : BForm) :
    PhysicalBoxEqv a b c
      (directRightChannelSection u (scaleForm q v))
      (triScale q (directRightChannelSection u v)) := by
  have hdata : ∀ w : DirectRightNestedCGChannel a b c,
      directRightChannelSectionData u (scaleForm q v) w ≈
        directRightDataScale q (directRightChannelSectionData u v) w := by
    intro w
    unfold directRightChannelSectionData directRightDataScale scaleForm
    by_cases hlabels : w.k = u.k ∧ w.outer.k = u.outer.k
    · simp only [dif_pos hlabels]
      exact Q'.eqv_refl _
    · simp only [dif_neg hlabels]
      exact Q'.eqv_symm (Q'.mul_zero_eqv q)
  have hcongr := directRightNestedReconstruct_congr_data a b c
    (directRightChannelSectionData u (scaleForm q v))
    (directRightDataScale q (directRightChannelSectionData u v)) hdata
  have hscale := directRightNestedReconstruct_dataScale a b c q
    (directRightChannelSectionData u v)
  intro i j l hi hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightChannelSection] using hcongr i j l hi hj hl)
    (by simpa only [directRightChannelSection] using hscale i j l hi hj hl)

theorem fixedLeft_directRightSection_congr {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c) (v w : BForm)
    (hvw : BFormEqv v w) :
    BFormEqv (fixedLeftAnalysis qL (directRightChannelSection u v))
      (fixedLeftAnalysis qL (directRightChannelSection u w)) :=
  fixedLeftAnalysis_congr qL _ _ (directRightChannelSection_congr u v w hvw)

theorem directRightChannelSection_add {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) (v w : BForm) :
    PhysicalBoxEqv a b c
      (directRightChannelSection u (addForm v w))
      (triAdd (directRightChannelSection u v)
        (directRightChannelSection u w)) := by
  have hdata : ∀ z : DirectRightNestedCGChannel a b c,
      directRightChannelSectionData u (addForm v w) z ≈
        directRightDataAdd (directRightChannelSectionData u v)
          (directRightChannelSectionData u w) z := by
    intro z
    unfold directRightChannelSectionData directRightDataAdd addForm
    by_cases hlabels : z.k = u.k ∧ z.outer.k = u.outer.k
    · simp only [dif_pos hlabels]
      exact Q'.eqv_refl _
    · simp only [dif_neg hlabels]
      exact Q'.eqv_of_eq (Q'.zero_add' 0).symm
  have hcongr := directRightNestedReconstruct_congr_data a b c
    (directRightChannelSectionData u (addForm v w))
    (directRightDataAdd (directRightChannelSectionData u v)
      (directRightChannelSectionData u w)) hdata
  have hadd := directRightNestedReconstruct_dataAdd a b c
    (directRightChannelSectionData u v)
    (directRightChannelSectionData u w)
  intro i j l hi hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightChannelSection] using hcongr i j l hi hj hl)
    (by simpa only [directRightChannelSection] using hadd i j l hi hj hl)

theorem fixedLeft_directRightSection_add {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c) (v w : BForm) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u (addForm v w)))
      (addForm
        (fixedLeftAnalysis qL (directRightChannelSection u v))
        (fixedLeftAnalysis qL (directRightChannelSection u w))) := by
  have hsection := directRightChannelSection_add u v w
  have hcongr := fixedLeftAnalysis_congr qL _ _ hsection
  have hadd := fixedLeftAnalysis_triAdd qL
    (directRightChannelSection u v) (directRightChannelSection u w)
  intro s
  exact Q'.eqv_trans _ _ _ (hcongr s) (hadd s)

theorem directRightChannelSection_zero {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) :
    PhysicalBoxEqv a b c (directRightChannelSection u zeroF) triZero := by
  have hdata : ∀ z : DirectRightNestedCGChannel a b c,
      directRightChannelSectionData u zeroF z ≈ directRightDataZero z := by
    intro z
    unfold directRightChannelSectionData directRightDataZero zeroF
    by_cases hlabels : z.k = u.k ∧ z.outer.k = u.outer.k
    · simp only [dif_pos hlabels]
      exact Q'.eqv_refl _
    · simp only [dif_neg hlabels]
      exact Q'.eqv_refl _
  have hcongr := directRightNestedReconstruct_congr_data a b c
    (directRightChannelSectionData u zeroF) directRightDataZero hdata
  have hzero := directRightNestedReconstruct_dataZero a b c
  intro i j l hi hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightChannelSection] using hcongr i j l hi hj hl)
    (hzero i j l hi hj hl)

theorem fixedLeft_directRightSection_zero {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u zeroF)) zeroF := by
  have hsection := directRightChannelSection_zero u
  have hcongr := fixedLeftAnalysis_congr qL _ _ hsection
  have hzero := fixedLeftAnalysis_triZero qL
  intro s
  exact Q'.eqv_trans _ _ _ (hcongr s) (hzero s)

theorem fixedLeft_directRightSection_scale {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c) (q : Q') (v : BForm) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u (scaleForm q v)))
      (scaleForm q (fixedLeftAnalysis qL (directRightChannelSection u v))) := by
  have hsection := directRightChannelSection_scale u q v
  have hcongr := fixedLeftAnalysis_congr qL _ _ hsection
  have hscale := fixedLeftAnalysis_triScale qL q
    (directRightChannelSection u v)
  intro s
  exact Q'.eqv_trans _ _ _ (hcongr s) (hscale s)

/-- Exact lowering of a successor monomial. -/
theorem Fop_mono_succ (D t : Nat) :
    BFormEqv (Fop D (mono (t + 1)))
      (scaleForm (Q'.ofNat (t + 1)) (mono t)) := by
  intro s
  unfold Fop scaleForm mono
  by_cases hst : s = t
  · subst s
    rw [if_pos rfl, if_pos rfl]
    exact Q'.eqv_refl _
  · rw [if_neg hst, if_neg (by omega : ¬ s + 1 = t + 1)]
    exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _)
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-- Lowering the bottom monomial is zero. -/
theorem Fop_mono_zero (D : Nat) :
    BFormEqv (Fop D (mono 0)) zeroF := by
  intro s
  unfold Fop mono zeroF
  rw [if_neg (by omega : ¬ s + 1 = 0)]
  exact Q'.mul_zero_eqv _

/-- Adjacent cross-tree coefficient rows obey the exact lowering recurrence. -/
theorem fixedLeft_directRight_mono_lowering_recurrence
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (t : Nat) (ht : t + 1 ≤ directRightFinalDegree u) :
    BFormEqv
      (scaleForm (Q'.ofNat (t + 1))
        (fixedLeftAnalysis qL (directRightChannelSection u (mono t))))
      (Fop d
        (fixedLeftAnalysis qL
          (directRightChannelSection u (mono (t + 1))))) := by
  have hsupp := mono_degreeSupported (directRightFinalDegree u) (t + 1) ht
  have hF := fixedLeft_directRightSection_Fop qL u (mono (t + 1)) hsupp
  have hinput := fixedLeft_directRightSection_congr qL u
    (Fop (directRightFinalDegree u) (mono (t + 1)))
    (scaleForm (Q'.ofNat (t + 1)) (mono t))
    (Fop_mono_succ (directRightFinalDegree u) t)
  have hscale := fixedLeft_directRightSection_scale qL u
    (Q'.ofNat (t + 1)) (mono t)
  intro s
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hscale s))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (hinput s)) (hF s))

/-- The bottom right monomial maps to a form killed by lowering. -/
theorem fixedLeft_directRight_mono_zero_lowering
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c) :
    BFormEqv
      (Fop d (fixedLeftAnalysis qL (directRightChannelSection u (mono 0))))
      zeroF := by
  have hsupp := mono_degreeSupported (directRightFinalDegree u) 0 (by omega)
  have hF := fixedLeft_directRightSection_Fop qL u (mono 0) hsupp
  have hinput := fixedLeft_directRightSection_congr qL u
    (Fop (directRightFinalDegree u) (mono 0))
    (scaleForm 0 (mono 0)) (fun s => by
      exact Q'.eqv_trans _ 0 _
        (Fop_mono_zero (directRightFinalDegree u) s)
        (Q'.eqv_symm (Q'.zero_mul_eqv _)))
  have hscale := fixedLeft_directRightSection_scale qL u 0 (mono 0)
  intro s
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hF s))
    (Q'.eqv_trans _ _ _ (hinput s)
      (Q'.eqv_trans _ _ _ (hscale s) (Q'.zero_mul_eqv _)))

/-! ## Endpoint cancellation of cross-final-degree rows -/

theorem Fop_zeroF (d : Nat) : BFormEqv (Fop d zeroF) zeroF := by
  intro s
  unfold Fop zeroF
  exact Q'.mul_zero_eqv _

theorem scaleForm_cancel_ofNat_succ (n : Nat) (f : BForm)
    (hzero : BFormEqv (scaleForm (Q'.ofNat (n + 1)) f) zeroF) :
    BFormEqv f zeroF := by
  intro s
  have hscaled : Q'.ofNat (n + 1) * f s ≈
      Q'.ofNat (n + 1) * 0 := by
    exact Q'.eqv_trans _ 0 _
      (by simpa only [scaleForm, zeroF] using hzero s)
      (Q'.eqv_symm (Q'.mul_zero_eqv _))
  exact Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos n) hscaled

/-- Both contractions in a physical fixed-left channel subtract from the
same total input degree.  This subtraction-normalized form is convenient for
endpoint arithmetic. -/
theorem fixedLeft_total_degree
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) :
    a + b + c - 2 * (qL.k + qL.r) = d := by
  have hk := Nat.le_min.mp qL.k_le
  have hr := Nat.le_min.mp qL.r_le
  have hdegree := qL.degree_eq
  omega

theorem fixedLeft_total_contraction_le
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) :
    2 * (qL.k + qL.r) ≤ a + b + c := by
  have hk := Nat.le_min.mp qL.k_le
  have hr := Nat.le_min.mp qL.r_le
  omega

/-- The analogous subtraction-normalized total degree of an ordered-right
channel. -/
theorem directRight_total_degree
    {a b c : Nat} (u : DirectRightNestedCGChannel a b c) :
    a + b + c - 2 * (u.k + u.outer.k) = directRightFinalDegree u := by
  have hk := Nat.le_min.mp u.k_le
  have hr := Nat.le_min.mp u.outer.k_le
  unfold directRightFinalDegree
  omega

theorem directRight_total_contraction_le
    {a b c : Nat} (u : DirectRightNestedCGChannel a b c) :
    2 * (u.k + u.outer.k) ≤ a + b + c := by
  have hk := Nat.le_min.mp u.k_le
  have hr := Nat.le_min.mp u.outer.k_le
  omega

/-- If the right final degree is larger, the top right monomial has no
grading-compatible coefficient in the fixed-left degree window. -/
theorem fixedLeft_directRight_top_zero_of_lt
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hlt : d < directRightFinalDegree u) :
    BFormEqv
      (fixedLeftAnalysis qL
        (directRightChannelSection u (mono (directRightFinalDegree u))))
      zeroF := by
  intro s
  by_cases hs : s ≤ d
  · apply fixedLeftAnalysis_directRightSection_mono_zero_of_shell_ne
    intro hshell
    have hL := fixedLeft_total_degree qL
    have hR := directRight_total_degree u
    have hLle := fixedLeft_total_contraction_le qL
    have hRle := directRight_total_contraction_le u
    omega
  · simpa only [zeroF] using fixedLeftAnalysis_zero_outside qL
      (directRightChannelSection u (mono (directRightFinalDegree u))) s
      (by omega)

/-- Descending endpoint propagation from a zero top right monomial. -/
theorem fixedLeft_directRight_descend_zero
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (htop : BFormEqv
      (fixedLeftAnalysis qL
        (directRightChannelSection u (mono (directRightFinalDegree u))))
      zeroF) :
    ∀ r, r ≤ directRightFinalDegree u →
      BFormEqv
        (fixedLeftAnalysis qL
          (directRightChannelSection u
            (mono (directRightFinalDegree u - r)))) zeroF := by
  intro r
  induction r with
  | zero =>
      intro _
      simpa only [Nat.sub_zero] using htop
  | succ r ih =>
      intro hr
      have hr' : r ≤ directRightFinalDegree u := by omega
      have hnext := ih hr'
      let t := directRightFinalDegree u - (r + 1)
      have ht : t + 1 ≤ directRightFinalDegree u := by
        unfold t
        omega
      have hrec := fixedLeft_directRight_mono_lowering_recurrence
        qL u t ht
      have hnext' : BFormEqv
          (fixedLeftAnalysis qL
            (directRightChannelSection u (mono (t + 1)))) zeroF := by
        simpa only [t, show directRightFinalDegree u - (r + 1) + 1 =
          directRightFinalDegree u - r by omega] using hnext
      have hFzero : BFormEqv
          (Fop d (fixedLeftAnalysis qL
            (directRightChannelSection u (mono (t + 1))))) zeroF := by
        intro s
        exact Q'.eqv_trans _ _ _
          (YMGap.Continuum.SU2ChannelSectionSchurReconstruction.Fop_congr
            d hnext' s)
          (Fop_zeroF d s)
      apply scaleForm_cancel_ofNat_succ t
      intro s
      exact Q'.eqv_trans _ _ _ (hrec s) (hFzero s)

/-- Hence every physical right monomial maps to zero when its final degree is
strictly larger than the fixed-left final degree. -/
theorem fixedLeft_directRight_mono_zero_of_lt
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hlt : d < directRightFinalDegree u)
    (t : Nat) (ht : t ≤ directRightFinalDegree u) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u (mono t))) zeroF := by
  have hdesc := fixedLeft_directRight_descend_zero qL u
    (fixedLeft_directRight_top_zero_of_lt qL u hlt)
    (directRightFinalDegree u - t) (by omega)
  simpa only [Nat.sub_sub_self ht] using hdesc

/-- If the right final degree is smaller, grading and the killed-by-lowering
bottom equation force the bottom right monomial to vanish. -/
theorem fixedLeft_directRight_bottom_zero_of_lt
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hlt : directRightFinalDegree u < d) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u (mono 0))) zeroF := by
  intro s
  by_cases hshell : s + qL.r + qL.k = u.outer.k + u.k
  · have hspos : 0 < s := by
      have hL := fixedLeft_total_degree qL
      have hR := directRight_total_degree u
      omega
    have hkill := fixedLeft_directRight_mono_zero_lowering qL u (s - 1)
    unfold Fop at hkill
    have hindex : s - 1 + 1 = s := by omega
    rw [hindex] at hkill
    have hscaled : Q'.ofNat s *
          fixedLeftAnalysis qL (directRightChannelSection u (mono 0)) s ≈
        Q'.ofNat s * 0 := by
      exact Q'.eqv_trans _ 0 _ hkill
        (Q'.eqv_symm (Q'.mul_zero_eqv _))
    cases s with
    | zero => omega
    | succ n =>
        exact Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos n) hscaled
  · simpa only [zeroF] using
      fixedLeftAnalysis_directRightSection_mono_zero_of_shell_ne
        qL u 0 s (by simpa only [Nat.zero_add] using hshell)

/-- Upward endpoint propagation from a zero bottom right monomial. -/
theorem fixedLeft_directRight_ascend_zero
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hlt : directRightFinalDegree u < d)
    (hbottom : BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u (mono 0))) zeroF) :
    ∀ t, t ≤ directRightFinalDegree u →
      BFormEqv
        (fixedLeftAnalysis qL (directRightChannelSection u (mono t))) zeroF := by
  intro t
  induction t with
  | zero => intro _; exact hbottom
  | succ t ih =>
      intro ht
      have htprev : t ≤ directRightFinalDegree u := by omega
      have hprev := ih htprev
      have hrec := fixedLeft_directRight_mono_lowering_recurrence
        qL u t ht
      intro s
      by_cases hshell : s + qL.r + qL.k =
          (t + 1) + u.outer.k + u.k
      · have hspos : 0 < s := by
          have hL := fixedLeft_total_degree qL
          have hR := directRight_total_degree u
          omega
        have hrow := hrec (s - 1)
        unfold scaleForm Fop at hrow
        have hindex : s - 1 + 1 = s := by omega
        rw [hindex] at hrow
        have hleftzero : Q'.ofNat (t + 1) *
            fixedLeftAnalysis qL (directRightChannelSection u (mono t))
              (s - 1) ≈ 0 := by
          exact Q'.eqv_trans _ (Q'.ofNat (t + 1) * 0) _
            (Q'.mul_eqv_congr_left _ _ _ (hprev (s - 1)))
            (Q'.mul_zero_eqv _)
        have hscaled : Q'.ofNat s *
              fixedLeftAnalysis qL
                (directRightChannelSection u (mono (t + 1))) s ≈
            Q'.ofNat s * 0 := by
          exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrow)
            (Q'.eqv_trans _ 0 _ hleftzero
              (Q'.eqv_symm (Q'.mul_zero_eqv _)))
        cases s with
        | zero => omega
        | succ n =>
            exact Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos n) hscaled
      · simpa only [zeroF] using
          fixedLeftAnalysis_directRightSection_mono_zero_of_shell_ne
            qL u (t + 1) s hshell

/-- Hence every physical right monomial maps to zero when its final degree is
strictly smaller than the fixed-left final degree. -/
theorem fixedLeft_directRight_mono_zero_of_gt
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hlt : directRightFinalDegree u < d)
    (t : Nat) (ht : t ≤ directRightFinalDegree u) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u (mono t))) zeroF := by
  exact fixedLeft_directRight_ascend_zero qL u hlt
    (fixedLeft_directRight_bottom_zero_of_lt qL u hlt) t ht

/-- **Cross-final-degree monomial vanishing.** -/
theorem fixedLeft_directRight_mono_zero_of_finalDegree_ne
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hne : directRightFinalDegree u ≠ d)
    (t : Nat) (ht : t ≤ directRightFinalDegree u) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u (mono t))) zeroF := by
  by_cases hlt : d < directRightFinalDegree u
  · exact fixedLeft_directRight_mono_zero_of_lt qL u hlt t ht
  · exact fixedLeft_directRight_mono_zero_of_gt qL u (by omega) t ht

/-! ## Finite arbitrary-form extension -/

/-- Every finite coefficient prefix of a wrong-final-degree channel is
annihilated.  The cutoff hypothesis ensures that all added monomials are
physical for that channel. -/
theorem fixedLeft_directRight_truncate_zero_of_finalDegree_ne
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hne : directRightFinalDegree u ≠ d) (v : BForm) :
    ∀ N, N ≤ directRightFinalDegree u + 1 →
      BFormEqv
        (fixedLeftAnalysis qL
          (directRightChannelSection u (truncateForm v N))) zeroF := by
  intro N
  induction N with
  | zero =>
      intro _
      have htrunc : BFormEqv (truncateForm v 0) zeroF := by
        intro s
        unfold truncateForm zeroF
        rw [if_neg (by omega : ¬s < 0)]
        exact Q'.eqv_refl _
      have hcongr := fixedLeft_directRightSection_congr qL u
        (truncateForm v 0) zeroF htrunc
      intro s
      exact Q'.eqv_trans _ _ _ (hcongr s)
        (fixedLeft_directRightSection_zero qL u s)
  | succ N ih =>
      intro hN
      have hNphys : N ≤ directRightFinalDegree u := by omega
      have hprev := ih (by omega)
      have htrunc : BFormEqv (truncateForm v (N + 1))
          (addForm (truncateForm v N) (scaleForm (v N) (mono N))) := by
        intro s
        exact Q'.eqv_symm (by
          simpa only [addForm, scaleForm] using truncateForm_succ v N s)
      have hcongr := fixedLeft_directRightSection_congr qL u
        (truncateForm v (N + 1))
        (addForm (truncateForm v N) (scaleForm (v N) (mono N))) htrunc
      have hadd := fixedLeft_directRightSection_add qL u
        (truncateForm v N) (scaleForm (v N) (mono N))
      have hmono := fixedLeft_directRight_mono_zero_of_finalDegree_ne
        qL u hne N hNphys
      have hscale := fixedLeft_directRightSection_scale qL u
        (v N) (mono N)
      have hscaledzero : BFormEqv
          (fixedLeftAnalysis qL
            (directRightChannelSection u (scaleForm (v N) (mono N))))
          zeroF := by
        intro s
        exact Q'.eqv_trans _ _ _ (hscale s)
          (Q'.eqv_trans _ (v N * 0) _
            (Q'.mul_eqv_congr_left (v N) _ _ (hmono s))
            (Q'.mul_zero_eqv (v N)))
      intro s
      exact Q'.eqv_trans _ _ _ (hcongr s)
        (Q'.eqv_trans _ _ _ (hadd s)
          (Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr' (hprev s) (hscaledzero s))
            (Q'.eqv_of_eq (Q'.zero_add' 0))))

/-- **Wrong-final-degree section vanishing for every physically supported
output form.**  This is the arbitrary-form extension of the endpoint
propagation theorem. -/
theorem fixedLeft_directRight_supported_zero_of_finalDegree_ne
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c)
    (hne : directRightFinalDegree u ≠ d) (v : BForm)
    (hv : FormDegreeSupported (directRightFinalDegree u) v) :
    BFormEqv
      (fixedLeftAnalysis qL (directRightChannelSection u v)) zeroF := by
  have hprefix := fixedLeft_directRight_truncate_zero_of_finalDegree_ne
    qL u hne v (directRightFinalDegree u + 1) (by omega)
  have htrunc : BFormEqv
      (truncateForm v (directRightFinalDegree u + 1)) v := by
    intro s
    unfold truncateForm
    by_cases hs : s < directRightFinalDegree u + 1
    · rw [if_pos hs]
      exact Q'.eqv_refl _
    · rw [if_neg hs]
      exact Q'.eqv_symm (hv s (by omega))
  have hcongr := fixedLeft_directRightSection_congr qL u
    (truncateForm v (directRightFinalDegree u + 1)) v htrunc
  intro s
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongr s)) (hprefix s)

/-! ## Complete fixed-output blocks -/

/-- Equality of all ordered-right coordinates is equality on the complete
physical coefficient box. -/
theorem directRightNestedCoordinates_ext (a b c : Nat) (x y : TriForm)
    (hxy : ∀ u : DirectRightNestedCGChannel a b c,
      directRightNestedCoordinates a b c x u ≈
        directRightNestedCoordinates a b c y u) :
    PhysicalBoxEqv a b c x y := by
  have hsynth := directRightNestedReconstruct_congr_data a b c
    (directRightNestedCoordinates a b c x)
    (directRightNestedCoordinates a b c y) hxy
  intro i j l hi hj hl
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (directRightNestedReconstruct_coordinates a b c x i j l hi hj hl))
    (Q'.eqv_trans _ _ _ (hsynth i j l hi hj hl)
      (directRightNestedReconstruct_coordinates a b c y i j l hi hj hl))

theorem fixedRightAnalysis_degreeSupported
    {a b c D : Nat} (q : FixedRightCGChannel a b c D) (x : TriForm) :
    FormDegreeSupported D (fixedRightAnalysis q x) := by
  intro s hs
  unfold fixedRightAnalysis
  rw [dif_neg (by omega)]
  exact Q'.eqv_refl _

/-- One concrete fixed-output right section in the wrong final degree is
annihilated by the fixed-left row. -/
theorem fixedLeft_fixedRightSection_zero_of_degree_ne
    {a b c d D : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c D) (hne : D ≠ d) (x : TriForm) :
    BFormEqv
      (fixedLeftAnalysis qL
        (fixedRightSection qR (fixedRightAnalysis qR x))) zeroF := by
  let u := fixedRightNestedChannel qR 0 (by omega)
  have hdegree : directRightFinalDegree u = D := by
    simpa only [u, fixedRightNestedChannel, directRightFinalDegree] using
      qR.degree_eq
  have hdegreeNe : directRightFinalDegree u ≠ d := by
    intro h
    apply hne
    omega
  have hzero := fixedLeft_directRight_supported_zero_of_finalDegree_ne
    qL u hdegreeNe (fixedRightAnalysis qR x)
      (by simpa only [hdegree] using fixedRightAnalysis_degreeSupported qR x)
  simpa only [u, fixedRightNestedChannel, fixedRightSection,
    directRightChannelSection, fixedRightSectionData,
    directRightChannelSectionData] using hzero

/-- A finite synthesis of right sections all carrying one wrong final degree
is annihilated. -/
theorem fixedLeft_fixedRightSectionSum_zero_of_degree_ne
    {a b c d D : Nat} (qL : FixedLeftCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c D))
    (hne : D ≠ d) (x : TriForm) :
    BFormEqv (fixedLeftAnalysis qL (fixedRightSectionSum qs x)) zeroF := by
  induction qs with
  | nil =>
      have hphysical := fixedRightSectionSum_nil
        (a := a) (b := b) (c := c) (d := D) x
      have hcongr := fixedLeftAnalysis_congr qL _ _ hphysical
      intro s
      exact Q'.eqv_trans _ _ _ (hcongr s)
        (fixedLeftAnalysis_triZero qL s)
  | cons q qs ih =>
      have hphysical := fixedRightSectionSum_cons q qs x
      have hcongr := fixedLeftAnalysis_congr qL _ _ hphysical
      have hadd := fixedLeftAnalysis_triAdd qL
        (fixedRightSection q (fixedRightAnalysis q x))
        (fixedRightSectionSum qs x)
      have hhead := fixedLeft_fixedRightSection_zero_of_degree_ne
        qL q hne x
      intro s
      exact Q'.eqv_trans _ _ _ (hcongr s)
        (Q'.eqv_trans _ _ _ (hadd s)
          (Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr' (hhead s) (ih s))
            (Q'.eqv_of_eq (Q'.zero_add' 0))))

theorem fixedLeft_fixedRightEnumeratedSectionSum_zero_of_degree_ne
    {a b c d D : Nat} (qL : FixedLeftCGChannel a b c d)
    (hne : D ≠ d) (x : TriForm) :
    BFormEqv
      (fixedLeftAnalysis qL (fixedRightEnumeratedSectionSum a b c D x))
      zeroF := by
  simpa only [fixedRightEnumeratedSectionSum] using
    fixedLeft_fixedRightSectionSum_zero_of_degree_ne qL
      (fixedRightChannels a b c D) hne x

theorem fixedRightEnumeratedSectionSum_coordinate_zero_of_finalDegree_ne
    {a b c D : Nat} (x : TriForm)
    (u : DirectRightNestedCGChannel a b c)
    (hne : directRightFinalDegree u ≠ D) :
    directRightNestedCoordinates a b c
        (fixedRightEnumeratedSectionSum a b c D x) u ≈ 0 := by
  simpa only [fixedRightEnumeratedSectionSum] using
    fixedRightSectionSum_coordinate_zero_of_finalDegree_ne
      (fixedRightChannels a b c D) x u hne

/-- The complete fixed-output block is extensional in precisely its own
final-degree coordinates. -/
theorem fixedRightEnumeratedSectionSum_congr_of_coordinates
    {a b c D : Nat} (x y : TriForm)
    (hxy : ∀ u : DirectRightNestedCGChannel a b c,
      directRightFinalDegree u = D →
        directRightNestedCoordinates a b c x u ≈
          directRightNestedCoordinates a b c y u) :
    PhysicalBoxEqv a b c
      (fixedRightEnumeratedSectionSum a b c D x)
      (fixedRightEnumeratedSectionSum a b c D y) := by
  apply directRightNestedCoordinates_ext
  intro u
  by_cases hdegree : directRightFinalDegree u = D
  · exact Q'.eqv_trans _ _ _
      (fixedRightEnumeratedSectionSum_coordinate_eq_of_finalDegree
        x u hdegree)
      (Q'.eqv_trans _ _ _ (hxy u hdegree)
        (Q'.eqv_symm
          (fixedRightEnumeratedSectionSum_coordinate_eq_of_finalDegree
            y u hdegree)))
  · exact Q'.eqv_trans _ 0 _
      (fixedRightEnumeratedSectionSum_coordinate_zero_of_finalDegree_ne
        x u hdegree)
      (Q'.eqv_symm
        (fixedRightEnumeratedSectionSum_coordinate_zero_of_finalDegree_ne
          y u hdegree))

/-- At its matching final degree, the enumerated block data is the original
ordered-right coordinate. -/
theorem fixedRightEnumeratedSectionData_eq_of_finalDegree
    {a b c D : Nat} (x : TriForm)
    (u : DirectRightNestedCGChannel a b c)
    (hdegree : directRightFinalDegree u = D) :
    fixedRightSectionDataSum (fixedRightChannels a b c D) x u ≈
      directRightNestedCoordinates a b c x u := by
  have hrec := directRightNestedCoordinates_reconstruct a b c
    (fixedRightSectionDataSum (fixedRightChannels a b c D) x) u
  have hblock :=
    fixedRightEnumeratedSectionSum_coordinate_eq_of_finalDegree x u hdegree
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrec)
    (by simpa only [fixedRightEnumeratedSectionSum, fixedRightSectionSum]
      using hblock)

/-- Away from its final degree, the enumerated block data is zero. -/
theorem fixedRightEnumeratedSectionData_zero_of_finalDegree_ne
    {a b c D : Nat} (x : TriForm)
    (u : DirectRightNestedCGChannel a b c)
    (hne : directRightFinalDegree u ≠ D) :
    fixedRightSectionDataSum (fixedRightChannels a b c D) x u ≈ 0 := by
  have hrec := directRightNestedCoordinates_reconstruct a b c
    (fixedRightSectionDataSum (fixedRightChannels a b c D) x) u
  have hzero :=
    fixedRightEnumeratedSectionSum_coordinate_zero_of_finalDegree_ne
      x u hne
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrec)
    (by simpa only [fixedRightEnumeratedSectionSum, fixedRightSectionSum]
      using hzero)

/-! ## Finite sum over every possible final degree -/

/-- Sum the complete ordered-right coordinate blocks of degrees `< N` at
the dependent-data level. -/
def allRightDegreeData (a b c : Nat) (x : TriForm) :
    Nat → DirectRightNestedCGChannel a b c → Q'
  | 0 => directRightDataZero
  | N + 1 => directRightDataAdd (allRightDegreeData a b c x N)
      (fixedRightSectionDataSum (fixedRightChannels a b c N) x)

theorem allRightDegreeData_zero_of_le (a b c : Nat) (x : TriForm)
    (N : Nat) (u : DirectRightNestedCGChannel a b c)
    (hN : N ≤ directRightFinalDegree u) :
    allRightDegreeData a b c x N u ≈ 0 := by
  induction N with
  | zero =>
      unfold allRightDegreeData directRightDataZero
      exact Q'.eqv_refl _
  | succ N ih =>
      unfold allRightDegreeData directRightDataAdd
      have hprev := ih (by omega)
      have hblock := fixedRightEnumeratedSectionData_zero_of_finalDegree_ne
        (D := N) x u (by omega)
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' hprev hblock)
        (Q'.eqv_of_eq (Q'.zero_add' 0))

theorem allRightDegreeData_eq_coordinate_of_lt (a b c : Nat) (x : TriForm)
    (N : Nat) (u : DirectRightNestedCGChannel a b c)
    (hN : directRightFinalDegree u < N) :
    allRightDegreeData a b c x N u ≈
      directRightNestedCoordinates a b c x u := by
  induction N with
  | zero => omega
  | succ N ih =>
      unfold allRightDegreeData directRightDataAdd
      by_cases hdegree : directRightFinalDegree u = N
      · have hprev := allRightDegreeData_zero_of_le a b c x N u (by omega)
        have hblock := fixedRightEnumeratedSectionData_eq_of_finalDegree
          (D := N) x u hdegree
        exact Q'.eqv_trans _ (0 + directRightNestedCoordinates a b c x u) _
          (Q'.add_eqv_congr' hprev hblock)
          (Q'.eqv_of_eq (Q'.zero_add' _))
      · have hprev := ih (by omega)
        have hblock := fixedRightEnumeratedSectionData_zero_of_finalDegree_ne
          (D := N) x u hdegree
        exact Q'.eqv_trans _ (directRightNestedCoordinates a b c x u + 0) _
          (Q'.add_eqv_congr' hprev hblock)
          (Q'.eqv_of_eq (Q'.add_zero' _))

theorem directRightFinalDegree_le_total {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) :
    directRightFinalDegree u ≤ a + b + c := by
  unfold directRightFinalDegree
  omega

/-- Reconstruct the sum of all possible final-degree blocks. -/
def allRightDegreeReconstruct (a b c : Nat) (x : TriForm) : TriForm :=
  directRightNestedReconstruct a b c
    (allRightDegreeData a b c x (a + b + c + 1))

/-- The finite all-degree reconstruction is the original tensor on the full
physical box. -/
theorem allRightDegreeReconstruct_eq (a b c : Nat) (x : TriForm) :
    PhysicalBoxEqv a b c (allRightDegreeReconstruct a b c x) x := by
  have hdata : ∀ u : DirectRightNestedCGChannel a b c,
      allRightDegreeData a b c x (a + b + c + 1) u ≈
        directRightNestedCoordinates a b c x u := by
    intro u
    apply allRightDegreeData_eq_coordinate_of_lt
    have hle := directRightFinalDegree_le_total u
    omega
  have hcongr := directRightNestedReconstruct_congr_data a b c
    (allRightDegreeData a b c x (a + b + c + 1))
    (directRightNestedCoordinates a b c x) hdata
  intro i j l hi hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [allRightDegreeReconstruct] using
      hcongr i j l hi hj hl)
    (directRightNestedReconstruct_coordinates a b c x i j l hi hj hl)

/-- Partial reconstruction through all final-degree blocks `< N`. -/
def rightDegreePrefixReconstruct (a b c : Nat) (x : TriForm)
    (N : Nat) : TriForm :=
  directRightNestedReconstruct a b c (allRightDegreeData a b c x N)

theorem rightDegreePrefixReconstruct_succ (a b c : Nat)
    (x : TriForm) (N : Nat) :
    PhysicalBoxEqv a b c
      (rightDegreePrefixReconstruct a b c x (N + 1))
      (triAdd (rightDegreePrefixReconstruct a b c x N)
        (fixedRightEnumeratedSectionSum a b c N x)) := by
  simpa only [rightDegreePrefixReconstruct, allRightDegreeData,
    fixedRightEnumeratedSectionSum, fixedRightSectionSum] using
    directRightNestedReconstruct_dataAdd a b c
      (allRightDegreeData a b c x N)
      (fixedRightSectionDataSum (fixedRightChannels a b c N) x)

/-- Fixed-left evaluation of the degree prefix depends only on the matching
final-degree coordinates. -/
theorem fixedLeft_rightDegreePrefix_congr
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (x y : TriForm)
    (hxy : ∀ u : DirectRightNestedCGChannel a b c,
      directRightFinalDegree u = d →
        directRightNestedCoordinates a b c x u ≈
          directRightNestedCoordinates a b c y u) :
    ∀ N, BFormEqv
      (fixedLeftAnalysis qL (rightDegreePrefixReconstruct a b c x N))
      (fixedLeftAnalysis qL (rightDegreePrefixReconstruct a b c y N)) := by
  intro N
  induction N with
  | zero =>
      intro s
      exact Q'.eqv_refl _
  | succ N ih =>
      have hrecX := rightDegreePrefixReconstruct_succ a b c x N
      have hrecY := rightDegreePrefixReconstruct_succ a b c y N
      have hcongrX := fixedLeftAnalysis_congr qL _ _ hrecX
      have hcongrY := fixedLeftAnalysis_congr qL _ _ hrecY
      have haddX := fixedLeftAnalysis_triAdd qL
        (rightDegreePrefixReconstruct a b c x N)
        (fixedRightEnumeratedSectionSum a b c N x)
      have haddY := fixedLeftAnalysis_triAdd qL
        (rightDegreePrefixReconstruct a b c y N)
        (fixedRightEnumeratedSectionSum a b c N y)
      have hstepX : BFormEqv
          (fixedLeftAnalysis qL
            (rightDegreePrefixReconstruct a b c x (N + 1)))
          (addForm
            (fixedLeftAnalysis qL (rightDegreePrefixReconstruct a b c x N))
            (fixedLeftAnalysis qL
              (fixedRightEnumeratedSectionSum a b c N x))) := by
        intro s
        exact Q'.eqv_trans _ _ _ (hcongrX s) (haddX s)
      have hstepY : BFormEqv
          (fixedLeftAnalysis qL
            (rightDegreePrefixReconstruct a b c y (N + 1)))
          (addForm
            (fixedLeftAnalysis qL (rightDegreePrefixReconstruct a b c y N))
            (fixedLeftAnalysis qL
              (fixedRightEnumeratedSectionSum a b c N y))) := by
        intro s
        exact Q'.eqv_trans _ _ _ (hcongrY s) (haddY s)
      have hblock : BFormEqv
          (fixedLeftAnalysis qL
            (fixedRightEnumeratedSectionSum a b c N x))
          (fixedLeftAnalysis qL
            (fixedRightEnumeratedSectionSum a b c N y)) := by
        by_cases hdegree : N = d
        · subst N
          exact fixedLeftAnalysis_congr qL _ _
            (fixedRightEnumeratedSectionSum_congr_of_coordinates x y hxy)
        · have hzeroX :=
            fixedLeft_fixedRightEnumeratedSectionSum_zero_of_degree_ne
              qL hdegree x
          have hzeroY :=
            fixedLeft_fixedRightEnumeratedSectionSum_zero_of_degree_ne
              qL hdegree y
          intro s
          exact Q'.eqv_trans _ 0 _ (hzeroX s) (Q'.eqv_symm (hzeroY s))
      intro s
      exact Q'.eqv_trans _ _ _ (hstepX s)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (ih s) (hblock s))
          (Q'.eqv_symm (hstepY s)))

/-- **Final-degree block diagonality of the concrete fixed-left
transvectant evaluator.** -/
theorem fixedLeftRespectsRightFinalDegree_proved
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) :
    FixedLeftRespectsRightFinalDegree qL := by
  intro x y hxy
  have hprefix := fixedLeft_rightDegreePrefix_congr qL x y hxy
    (a + b + c + 1)
  have hphysicalX := allRightDegreeReconstruct_eq a b c x
  have hphysicalY := allRightDegreeReconstruct_eq a b c y
  have hcongrX := fixedLeftAnalysis_congr qL
    (allRightDegreeReconstruct a b c x) x hphysicalX
  have hcongrY := fixedLeftAnalysis_congr qL
    (allRightDegreeReconstruct a b c y) y hphysicalY
  intro s
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongrX s))
    (Q'.eqv_trans _ _ _
      (by simpa only [allRightDegreeReconstruct, rightDegreePrefixReconstruct]
        using hprefix s)
      (hcongrY s))

/-- The concrete fixed-left evaluator equals its full enumerated
same-final-degree ordered-right projection. -/
theorem fixedLeftAnalysis_projection
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d) (x : TriForm) :
    BFormEqv (fixedLeftAnalysis qL x)
      (fixedLeftAnalysis qL
        (fixedRightEnumeratedSectionSum a b c d x)) := by
  exact fixedLeftAnalysis_projection_of_rightFinalDegree qL
    (fixedLeftRespectsRightFinalDegree_proved qL) x

end YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation

#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation.fixedLeft_directRight_mono_zero_of_finalDegree_ne
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation.fixedLeft_directRight_supported_zero_of_finalDegree_ne
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation.allRightDegreeReconstruct_eq
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation.fixedLeftRespectsRightFinalDegree_proved
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation.fixedLeftAnalysis_projection
