/-
# Cross-final-degree block diagonality for concrete nested transvectants

The finite fixed-output reconstruction preserves all ordered-right coordinates
of the selected final degree.  To show that a concrete fixed-left row ignores
the other final-degree blocks, we first expose the exact total-shell (Cartan
weight) grading of the checked dependent Hahn synthesis, then use the E/F
boundary equations to eliminate the only grading-compatible shifted diagonal.
-/

import YMGap.Continuum.SU2FixedLeftEvaluationLinearity
import YMGap.Continuum.SU2TransvectantOutputRowInvariant

namespace YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.SU2TransvectantOutputRowInvariant
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases
open YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2ProjectedRawSupportedBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftEvaluationLinearity

local infix:50 " ≈ " => Q'.eqv

/-! ## Arbitrary ordered-right channel sections -/

/-- Insert one output form into an arbitrary ordered-right nested channel,
without fixing its final degree in advance. -/
def directRightChannelSectionData {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) (v : BForm) :
    DirectRightNestedCGChannel a b c → Q' :=
  fun w => if _h : w.k = u.k ∧ w.outer.k = u.outer.k then
    v w.outer.s
  else 0

/-- Global section of one arbitrary ordered-right nested channel. -/
def directRightChannelSection {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) (v : BForm) : TriForm :=
  directRightNestedReconstruct a b c (directRightChannelSectionData u v)

/-- Final output degree of one arbitrary ordered-right channel. -/
def directRightChannelFinalDegree {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) : Nat :=
  a + (b + c - 2 * u.k) - 2 * u.outer.k

theorem finalDegree_eq_directRightFinalDegree {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) :
    directRightChannelFinalDegree u = directRightFinalDegree u := rfl

/-! ## Shell-locality of the checked binary inverse -/

/-- At a physical coefficient `(i,j)`, global Hahn reconstruction depends
only on dependent channels whose source shell is `i+j`. -/
theorem globalHahnReconstruct_congr_on_shell (m n : Nat)
    (c d : PhysicalCGChannel m n → Q') (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n)
    (hcd : ∀ q : PhysicalCGChannel m n,
      q.shell = i + j → c q ≈ d q) :
    globalHahnReconstruct m n c i j ≈
      globalHahnReconstruct m n d i j := by
  let t := i + j
  have ht : t ≤ m + n := Nat.add_le_add hi hj
  let yc := shellDataFromGlobal m n t ht c
  let yd := shellDataFromGlobal m n t ht d
  have hy : ∀ k, k < shellWidth m n t + 1 → yc k ≈ yd k := by
    intro k hk
    unfold yc yd shellDataFromGlobal
    rw [dif_pos hk, dif_pos hk]
    apply hcd
    simpa only [t] using shellChannelOfIndex_shell m n t k ht
      (Nat.lt_succ_iff.mp hk)
  have hsolve : ∀ r, r < shellWidth m n t + 1 →
      allShellHahnSolve m n t ht yc r ≈
        allShellHahnSolve m n t ht yd r := by
    apply physicalHahnAction_injective m n t ht
    intro k hk
    have hc := allShellHahnSolve_rightInverse m n t ht yc k hk
    have hd := allShellHahnSolve_rightInverse m n t ht yd k hk
    exact Q'.eqv_trans _ _ _ hc
      (Q'.eqv_trans _ _ _ (hy k hk) (Q'.eqv_symm hd))
  unfold globalHahnReconstruct
  simp only [dif_pos hi, dif_pos hj]
  change allShellHahnSolve m n t ht yc (i - shellLo n t) ≈
    allShellHahnSolve m n t ht yd (i - shellLo n t)
  exact hsolve (i - shellLo n t) (by
    have hactive : SourceActive m n t i := by
      unfold SourceActive t
      exact ⟨by omega, hi, by omega⟩
    exact Nat.lt_succ_iff.mpr
      (sourceActive_index_complete m n t i hactive).1)

/-- Shellwise-zero dependent data reconstruct to zero at the corresponding
physical source coefficient. -/
theorem globalHahnReconstruct_zero_of_shell (m n : Nat)
    (c : PhysicalCGChannel m n → Q') (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n)
    (hc : ∀ q : PhysicalCGChannel m n,
      q.shell = i + j → c q ≈ 0) :
    globalHahnReconstruct m n c i j ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (globalHahnReconstruct_congr_on_shell m n c cgDataZero
      i j hi hj (fun q hq => by simpa only [cgDataZero] using hc q hq))
    (globalHahnReconstruct_dataZero m n i j hi hj)

/-! ## Exact total-shell grading of arbitrary right sections -/

/-- Total source coefficient shell carried by an ordered-right coordinate.
Each inner and outer Cayley contraction lowers the output coefficient index
by one, hence the source shell is `s + outer.k + inner.k`. -/
def directRightTotalShell {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) : Nat :=
  u.outer.s + u.outer.k + u.k

/-- A monomial section has dependent data on exactly one total shell. -/
theorem directRightChannelSectionData_mono_zero_offshell
    {a b c : Nat} (u w : DirectRightNestedCGChannel a b c) (t : Nat)
    (hoff : directRightTotalShell w ≠
      t + u.outer.k + u.k) :
    directRightChannelSectionData u (mono t) w ≈ 0 := by
  unfold directRightChannelSectionData
  by_cases hlabels : w.k = u.k ∧ w.outer.k = u.outer.k
  · rw [dif_pos hlabels]
    unfold mono
    rw [if_neg (by
      intro hs
      apply hoff
      unfold directRightTotalShell
      omega)]
    exact Q'.eqv_refl _
  · rw [dif_neg hlabels]
    exact Q'.eqv_refl _

/-- **Cartan grading of a concrete ordered-right section.**  The section of
output monomial `t` in channel `(inner k, outer k)` is zero at every physical
three-factor coefficient outside total source shell
`t + outer.k + inner.k`. -/
theorem directRightChannelSection_mono_zero_offshell
    {a b c : Nat} (u : DirectRightNestedCGChannel a b c) (t : Nat)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c)
    (hoff : i + j + l ≠ t + u.outer.k + u.k) :
    directRightChannelSection u (mono t) i j l ≈ 0 := by
  unfold directRightChannelSection directRightNestedReconstruct
  apply globalHahnReconstruct_zero_of_shell b c
    (directRightInnerData (directRightChannelSectionData u (mono t)) i)
    j l hj hl
  intro q hq
  unfold directRightInnerData directRightOuterReconstruct
  apply globalHahnReconstruct_zero_of_shell a (b + c - 2 * q.k)
    (directRightOuterData (directRightChannelSectionData u (mono t))
      q.k q.k_le) i q.s hi q.s_le
  intro outer houter
  unfold directRightOuterData
  apply directRightChannelSectionData_mono_zero_offshell
  intro htotal
  unfold directRightTotalShell at htotal
  change outer.s + outer.k + q.k = t + u.outer.k + u.k at htotal
  unfold PhysicalCGChannel.shell at hq houter
  apply hoff
  omega

/-! ## Shell grading of left-nested analysis -/

/-- Physical support on one total coefficient shell of a three-factor
coefficient tensor. -/
def TriShellSupported (a b c T : Nat) (x : TriForm) : Prop :=
  ∀ i j l, i ≤ a → j ≤ b → l ≤ c →
    i + j + l ≠ T → x i j l ≈ 0

/-- The concrete arbitrary-channel monomial section has its advertised
single-shell support. -/
theorem directRightChannelSection_mono_shellSupported
    {a b c : Nat} (u : DirectRightNestedCGChannel a b c) (t : Nat) :
    TriShellSupported a b c (t + u.outer.k + u.k)
      (directRightChannelSection u (mono t)) := by
  intro i j l hi hj hl hoff
  exact directRightChannelSection_mono_zero_offshell
    u t i j l hi hj hl hoff

/-- A projected binary transvectant coordinate vanishes when every physical
source coefficient on its unique source shell vanishes. -/
theorem globalTransvectCoordinates_zero_of_source_shell
    (m n : Nat) (x : BForm2) (q : PhysicalCGChannel m n)
    (hx : ∀ i j, i ≤ m → j ≤ n →
      i + j = q.shell → x i j ≈ 0) :
    globalTransvectCoordinates m n x q ≈ 0 := by
  have hhahn : globalHahnCoordinates m n x q ≈
      globalHahnCoordinates m n zeroForm2 q := by
    unfold globalHahnCoordinates
    apply physicalHahnAction_congr
    intro r hr
    have hsrc := sourceActive_of_index m n q.shell r q.shell_le
      (Nat.lt_succ_iff.mp hr)
    unfold sourceShellCoordinates zeroForm2
    apply hx _ _ hsrc.2.1 hsrc.2.2
    have hle : shellLo n q.shell + r ≤ q.shell := hsrc.1
    omega
  exact Q'.eqv_trans _ _ _
    (globalTransvectCoordinates_eq_hahn m n x q)
    (Q'.eqv_trans _ _ _ hhahn
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (globalTransvectCoordinates_eq_hahn m n zeroForm2 q))
        (globalTransvectCoordinates_zeroForm2 m n q)))

/-- If an ambient tensor lies on total shell `T`, its first-pair output at
inner contraction order `k` lies on bidegree shell `T-k`.  The subtraction-free
statement records the exact relation `s+l+k=T`. -/
theorem firstPairOutput_zero_offshell
    (a b c T : Nat) (x : TriForm) (hx : TriShellSupported a b c T x)
    (k : Nat) (hk : k ≤ min a b)
    (s l : Nat) (hs : s ≤ a + b - 2 * k) (hl : l ≤ c)
    (hoff : s + l + k ≠ T) :
    firstPairOutput a b x k s l ≈ 0 := by
  let q : PhysicalCGChannel a b :=
    { k := k, k_le := hk, s := s, s_le := hs }
  have hslice : ∀ i j, i ≤ a → j ≤ b →
      i + j = q.shell → triSlice x l i j ≈ 0 := by
    intro i j hi hj hshell
    apply hx i j l hi hj hl
    intro htotal
    apply hoff
    unfold PhysicalCGChannel.shell at hshell
    change i + j = s + k at hshell
    omega
  have hzero := globalTransvectCoordinates_zero_of_source_shell
    a b (triSlice x l) q hslice
  simpa only [firstPairOutput, globalTransvectCoordinates, q] using hzero

/-- Total source shell carried by a left-nested coordinate. -/
def leftNestedTotalShell {a b c : Nat}
    (q : LeftNestedCGChannel a b c) : Nat :=
  q.outer.s + q.outer.k + q.k

/-- A left-nested coordinate annihilates a tensor supported on a different
total source shell. -/
theorem leftNestedCoordinates_zero_offshell
    (a b c T : Nat) (x : TriForm) (hx : TriShellSupported a b c T x)
    (q : LeftNestedCGChannel a b c)
    (hoff : leftNestedTotalShell q ≠ T) :
    leftNestedCoordinates a b c x q ≈ 0 := by
  have hfirst : ∀ s l,
      s ≤ a + b - 2 * q.k → l ≤ c →
      s + l = q.outer.shell →
        firstPairOutput a b x q.k s l ≈ 0 := by
    intro s l hs hl hshell
    apply firstPairOutput_zero_offshell a b c T x hx
      q.k q.k_le s l hs hl
    intro htotal
    apply hoff
    unfold leftNestedTotalShell
    unfold PhysicalCGChannel.shell at hshell
    omega
  have hzero := globalTransvectCoordinates_zero_of_source_shell
    (a + b - 2 * q.k) c
    (firstPairOutput a b x q.k) q.outer hfirst
  simpa only [leftNestedCoordinates] using hzero

/-- **Exact Cartan grading of a cross-tree coefficient.**  A fixed-left
coefficient `s` evaluated on an ordered-right channel section of monomial `t`
vanishes unless the two nested total source shells agree. -/
theorem fixedLeftAnalysis_directRightSection_mono_zero_of_shell_ne
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (u : DirectRightNestedCGChannel a b c) (t s : Nat)
    (hoff : s + qL.r + qL.k ≠ t + u.outer.k + u.k) :
    fixedLeftAnalysis qL (directRightChannelSection u (mono t)) s ≈ 0 := by
  unfold fixedLeftAnalysis
  by_cases hs : s ≤ d
  · rw [dif_pos hs]
    apply leftNestedCoordinates_zero_offshell a b c
      (t + u.outer.k + u.k)
      (directRightChannelSection u (mono t))
      (directRightChannelSection_mono_shellSupported u t)
      (fixedLeftNestedChannel qL s hs)
    simpa only [leftNestedTotalShell, fixedLeftNestedChannel] using hoff
  · rw [dif_neg hs]
    exact Q'.eqv_refl _

/-! ## Physical support and total lowering -/

/-- Literal zero support outside the complete three-factor coefficient box. -/
def TriBoxSupported (a b c : Nat) (x : TriForm) : Prop :=
  ∀ i j l, (a < i ∨ b < j ∨ c < l) → x i j l ≈ 0

/-- Every checked ordered-right synthesis is already the zero-outside
representative of its physical three-factor coefficient box. -/
theorem directRightNestedReconstruct_supported (a b c : Nat)
    (data : DirectRightNestedCGChannel a b c → Q') :
    TriBoxSupported a b c (directRightNestedReconstruct a b c data) := by
  intro i j l hout
  rcases hout with hi | hj | hl
  · by_cases hj' : j ≤ b
    · by_cases hl' : l ≤ c
      · have hdata : ∀ q : PhysicalCGChannel b c,
            directRightInnerData data i q ≈ cgDataZero q := by
          intro q
          unfold directRightInnerData directRightOuterReconstruct
          unfold globalHahnReconstruct
          rw [dif_neg (by omega : ¬ i ≤ a)]
          exact Q'.eqv_refl _
        have hcongr := globalHahnReconstruct_congr b c
          (directRightInnerData data i) cgDataZero hdata j l hj' hl'
        exact Q'.eqv_trans _ _ _
          (by simpa only [directRightNestedReconstruct] using hcongr)
          (globalHahnReconstruct_dataZero b c j l hj' hl')
      · unfold directRightNestedReconstruct globalHahnReconstruct
        rw [dif_pos hj', dif_neg hl']
        exact Q'.eqv_refl _
    · unfold directRightNestedReconstruct globalHahnReconstruct
      rw [dif_neg hj']
      exact Q'.eqv_refl _
  · unfold directRightNestedReconstruct globalHahnReconstruct
    rw [dif_neg (by omega : ¬ j ≤ b)]
    exact Q'.eqv_refl _
  · by_cases hj' : j ≤ b
    · unfold directRightNestedReconstruct globalHahnReconstruct
      rw [dif_pos hj', dif_neg (by omega : ¬ l ≤ c)]
      exact Q'.eqv_refl _
    · unfold directRightNestedReconstruct globalHahnReconstruct
      rw [dif_neg hj']
      exact Q'.eqv_refl _

theorem directRightChannelSection_supported {a b c : Nat}
    (u : DirectRightNestedCGChannel a b c) (v : BForm) :
    TriBoxSupported a b c (directRightChannelSection u v) := by
  exact directRightNestedReconstruct_supported a b c
    (directRightChannelSectionData u v)

/-- Total lowering on a three-factor coefficient tensor. -/
def F3 (_a _b _c : Nat) (x : TriForm) : TriForm :=
  fun i j l =>
    Q'.ofNat (i + 1) * x (i + 1) j l +
      (Q'.ofNat (j + 1) * x i (j + 1) l +
        Q'.ofNat (l + 1) * x i j (l + 1))

private theorem scale_zero (q x : Q') (hx : x ≈ 0) : q * x ≈ 0 :=
  Q'.eqv_trans _ (q * 0) _ (Q'.mul_eqv_congr_left q _ _ hx)
    (Q'.mul_zero_eqv q)

/-- Total lowering preserves the physical three-factor box. -/
theorem F3_supported (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) :
    TriBoxSupported a b c (F3 a b c x) := by
  intro i j l hout
  unfold F3
  have h0 := hx (i + 1) j l (by rcases hout with h | h | h <;> omega)
  have h1 := hx i (j + 1) l (by rcases hout with h | h | h <;> omega)
  have h2 := hx i j (l + 1) (by rcases hout with h | h | h <;> omega)
  exact Q'.eqv_trans _ (0 + (0 + 0)) _
    (Q'.add_eqv_congr' (scale_zero _ _ h0)
      (Q'.add_eqv_congr' (scale_zero _ _ h1) (scale_zero _ _ h2)))
    (by decide)

/-- Every physical slice of a box-supported tensor has the expected binary
bidegree support; slices beyond the third degree are zero as well. -/
theorem triSlice_supported (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (l : Nat) :
    BidegreeSupported a b (triSlice x l) := by
  intro i j hout
  unfold triSlice
  exact hx i j l (by rcases hout with hi | hj <;> omega)

/-- Physical rectangle projection has literal physical bidegree support. -/
theorem rectProject_supported (m n : Nat) (x : BForm2) :
    BidegreeSupported m n (rectProject m n x) := by
  intro i j hout
  exact rectProject_zero_outside m n x i j hout

/-- Slicing total lowering separates into lowering of the first two factors
and lowering of the fixed third coefficient. -/
theorem triSlice_F3 (a b c : Nat) (x : TriForm) (l : Nat) :
    BForm2Eqv (triSlice (F3 a b c x) l)
      (badd (F2 a b (triSlice x l))
        (bscale (Q'.ofNat (l + 1)) (triSlice x (l + 1)))) := by
  intro i j
  unfold triSlice F3 F2 badd bscale
  exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

/-- On a physically supported tensor, projected first-pair analysis equals
the corresponding raw transvectant. -/
theorem firstPairOutput_eq_raw (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (k s l : Nat) :
    firstPairOutput a b x k s l ≈
      transvect a b k (triSlice x l) s := by
  have hproject := bidegreeSupported_eqv_rectProject a b
    (triSlice x l) (triSlice_supported a b c x hx l)
  have hcongr := transvect_congr a b k
    (fun i j => Q'.eqv_symm (hproject i j)) s
  simpa only [firstPairOutput] using hcongr

/-- First-pair output of a box-supported tensor has the expected physical
bidegree support `(a+b-2k,c)`. -/
theorem firstPairOutput_supported (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (k : Nat) (hk : k ≤ min a b) :
    BidegreeSupported (a + b - 2 * k) c (firstPairOutput a b x k) := by
  intro s l hout
  rcases hout with hs | hl
  · have hmin := Nat.le_min.mp hk
    exact transvect_zero_above_degree a b k
      (rectProject a b (triSlice x l)) hmin.1 hmin.2
      (rectProject_supported a b (triSlice x l)) s hs
  · by_cases hs : s ≤ a + b - 2 * k
    · let q : PhysicalCGChannel a b :=
        { k := k, k_le := hk, s := s, s_le := hs }
      have hslice : ∀ i j, i ≤ a → j ≤ b →
          i + j = q.shell → triSlice x l i j ≈ 0 := by
        intro i j hi hj _
        unfold triSlice
        exact hx i j l (Or.inr (Or.inr hl))
      have hzero := globalTransvectCoordinates_zero_of_source_shell
        a b (triSlice x l) q hslice
      simpa only [firstPairOutput, globalTransvectCoordinates, q] using hzero
    · have hmin := Nat.le_min.mp hk
      exact transvect_zero_above_degree a b k
        (rectProject a b (triSlice x l)) hmin.1 hmin.2
        (rectProject_supported a b (triSlice x l)) s (by omega)

/-- Total lowering passes through the first binary coupling, producing total
lowering on the intermediate-output/third-leg tensor. -/
theorem firstPairOutput_F3 (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (k : Nat) (hk : k ≤ min a b) :
    BForm2Eqv (firstPairOutput a b (F3 a b c x) k)
      (F2 (a + b - 2 * k) c (firstPairOutput a b x k)) := by
  intro s l
  have hxF := F3_supported a b c x hx
  have hraw := firstPairOutput_eq_raw a b c (F3 a b c x) hxF k s l
  have hslice := transvect_congr a b k (triSlice_F3 a b c x l) s
  have hadd := transvect_add a b k
    (F2 a b (triSlice x l))
    (bscale (Q'.ofNat (l + 1)) (triSlice x (l + 1))) s
  have hmin := Nat.le_min.mp hk
  have hinner := transvect_F2_supported a b k s (triSlice x l)
    hmin.1 hmin.2 (triSlice_supported a b c x hx l)
  have hthird := transvect_scale a b k (Q'.ofNat (l + 1))
    (triSlice x (l + 1)) s
  have hrawNext := firstPairOutput_eq_raw a b c x hx k (s + 1) l
  have hrawThird := firstPairOutput_eq_raw a b c x hx k s (l + 1)
  refine Q'.eqv_trans _ _ _ hraw ?_
  refine Q'.eqv_trans _ _ _ hslice ?_
  refine Q'.eqv_trans _ _ _ hadd ?_
  unfold F2
  exact Q'.add_eqv_congr'
    (by
      have h := Q'.eqv_trans _ _ _ hinner
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hrawNext))
      simpa only [Fop] using h)
    (Q'.eqv_trans _ _ _ hthird
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hrawThird)))

/-- The complete zero-extended output form belonging to one arbitrary
left-nested contraction-order pair. -/
def leftNestedChannelAnalysis {a b c : Nat}
    (q : LeftNestedCGChannel a b c) (x : TriForm) : BForm :=
  fun s => if hs : s ≤ a + b - 2 * q.k + c - 2 * q.outer.k then
    leftNestedCoordinates a b c x
      { k := q.k
        k_le := q.k_le
        outer :=
          { k := q.outer.k
            k_le := q.outer.k_le
            s := s
            s_le := hs } }
  else 0

/-- Every left-nested coordinate intertwines total lowering with ordinary
lowering in its final output degree. -/
theorem leftNestedCoordinates_F3 (a b c : Nat) (x : TriForm)
    (hx : TriBoxSupported a b c x) (q : LeftNestedCGChannel a b c) :
    leftNestedCoordinates a b c (F3 a b c x) q ≈
      Fop (a + b - 2 * q.k + c - 2 * q.outer.k)
        (leftNestedChannelAnalysis q x) q.outer.s := by
  have hxF := F3_supported a b c x hx
  have hsupp := firstPairOutput_supported a b c x hx q.k q.k_le
  have hsuppF := firstPairOutput_supported a b c (F3 a b c x) hxF
    q.k q.k_le
  have hrawF := globalTransvectCoordinates_eq_raw_of_supported
    (a + b - 2 * q.k) c
    (firstPairOutput a b (F3 a b c x) q.k) hsuppF q.outer
  have hfirst := transvect_congr (a + b - 2 * q.k) c q.outer.k
    (firstPairOutput_F3 a b c x hx q.k q.k_le) q.outer.s
  have hmin := Nat.le_min.mp q.outer.k_le
  have houter := transvect_F2_supported
    (a + b - 2 * q.k) c q.outer.k q.outer.s
    (firstPairOutput a b x q.k) hmin.1 hmin.2 hsupp
  have hrawAt : ∀ s,
      transvect (a + b - 2 * q.k) c q.outer.k
          (firstPairOutput a b x q.k) s ≈
        leftNestedChannelAnalysis q x s := by
    intro s
    by_cases hsBound : s ≤ a + b - 2 * q.k + c - 2 * q.outer.k
    · let outer : PhysicalCGChannel (a + b - 2 * q.k) c :=
        { k := q.outer.k, k_le := q.outer.k_le, s := s, s_le := hsBound }
      have hraw := globalTransvectCoordinates_eq_raw_of_supported
        (a + b - 2 * q.k) c (firstPairOutput a b x q.k) hsupp outer
      exact Q'.eqv_symm (by
        simp only [leftNestedChannelAnalysis, dif_pos hsBound]
        simpa only [leftNestedCoordinates, outer] using hraw)
    · have hzero := transvect_zero_above_degree
        (a + b - 2 * q.k) c q.outer.k
        (firstPairOutput a b x q.k) hmin.1 hmin.2 hsupp s (by omega)
      exact Q'.eqv_trans _ 0 _ hzero (by
        simp only [leftNestedChannelAnalysis, dif_neg hsBound]
        exact Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (by simpa only [leftNestedCoordinates] using hrawF)
    (Q'.eqv_trans _ _ _ hfirst
      (Q'.eqv_trans _ _ _ houter
        (Q'.mul_eqv_congr_left _ _ _ (hrawAt (q.outer.s + 1)))))

/-- The zero-extended arbitrary left-channel form agrees with the concrete
fixed-output left analysis when the contraction orders are those of `qL`. -/
theorem leftNestedChannelAnalysis_fixedLeft {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (x : TriForm)
    (s0 : Nat) (hs0 : s0 ≤ d) :
    BFormEqv
      (leftNestedChannelAnalysis (fixedLeftNestedChannel qL s0 hs0) x)
      (fixedLeftAnalysis qL x) := by
  intro s
  unfold leftNestedChannelAnalysis fixedLeftAnalysis
  simp only [fixedLeftNestedChannel]
  have hdegree : a + b - 2 * qL.k + c - 2 * qL.r = d := qL.degree_eq
  by_cases hs : s ≤ d
  · have hs' : s ≤ a + b - 2 * qL.k + c - 2 * qL.r := by
      rw [hdegree]
      exact hs
    rw [dif_pos hs', dif_pos hs]
    exact Q'.eqv_refl _
  · have hs' : ¬ s ≤ a + b - 2 * qL.k + c - 2 * qL.r := by
      rw [hdegree]
      exact hs
    rw [dif_neg hs', dif_neg hs]
    exact Q'.eqv_refl _

/-- **Concrete fixed-left lowering covariance.** -/
theorem fixedLeftAnalysis_F3 {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (x : TriForm)
    (hx : TriBoxSupported a b c x) :
    BFormEqv (fixedLeftAnalysis qL (F3 a b c x))
      (Fop d (fixedLeftAnalysis qL x)) := by
  intro s
  by_cases hs : s ≤ d
  · unfold fixedLeftAnalysis
    rw [dif_pos hs]
    have hcoord := leftNestedCoordinates_F3 a b c x hx
      (fixedLeftNestedChannel qL s hs)
    have hanalysis := leftNestedChannelAnalysis_fixedLeft qL x s hs
    have hdegree :
        a + b - 2 * (fixedLeftNestedChannel qL s hs).k + c -
          2 * (fixedLeftNestedChannel qL s hs).outer.k = d := by
      simpa only [fixedLeftNestedChannel] using qL.degree_eq
    rw [hdegree] at hcoord
    exact Q'.eqv_trans _ _ _ hcoord
      (Q'.mul_eqv_congr_left _ _ _ (hanalysis (s + 1)))
  · have hleft := fixedLeftAnalysis_zero_outside qL (F3 a b c x) s
      (by omega)
    have hright : Fop d (fixedLeftAnalysis qL x) s ≈ 0 := by
      unfold Fop
      exact scale_zero _ _
        (fixedLeftAnalysis_zero_outside qL x (s + 1) (by omega))
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)

/-- Ordered-right synthesis respects pointwise equivalence of complete
dependent coordinate data on the physical three-factor box. -/
theorem directRightNestedReconstruct_congr_data (a b c : Nat)
    (data data' : DirectRightNestedCGChannel a b c → Q')
    (hdata : ∀ u, data u ≈ data' u) :
    PhysicalBoxEqv a b c
      (directRightNestedReconstruct a b c data)
      (directRightNestedReconstruct a b c data') := by
  intro i j l hi hj hl
  have hinner : ∀ q : PhysicalCGChannel b c,
      directRightInnerData data i q ≈
        directRightInnerData data' i q := by
    intro q
    unfold directRightInnerData directRightOuterReconstruct
    apply globalHahnReconstruct_congr a (b + c - 2 * q.k)
      (directRightOuterData data q.k q.k_le)
      (directRightOuterData data' q.k q.k_le)
      (fun outer => by
        unfold directRightOuterData
        exact hdata _)
      i q.s hi q.s_le
  simpa only [directRightNestedReconstruct] using
    globalHahnReconstruct_congr b c
      (directRightInnerData data i) (directRightInnerData data' i)
      hinner j l hj hl

end YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock

#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.finalDegree_eq_directRightFinalDegree
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.globalHahnReconstruct_congr_on_shell
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.globalHahnReconstruct_zero_of_shell
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.directRightChannelSectionData_mono_zero_offshell
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.directRightChannelSection_mono_zero_offshell
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.directRightChannelSection_mono_shellSupported
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.globalTransvectCoordinates_zero_of_source_shell
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.firstPairOutput_zero_offshell
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.leftNestedCoordinates_zero_offshell
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.fixedLeftAnalysis_directRightSection_mono_zero_of_shell_ne
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.directRightNestedReconstruct_supported
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.directRightChannelSection_supported
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.F3_supported
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.triSlice_supported
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.rectProject_supported
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.triSlice_F3
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.firstPairOutput_eq_raw
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.firstPairOutput_supported
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.firstPairOutput_F3
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.leftNestedCoordinates_F3
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.leftNestedChannelAnalysis_fixedLeft
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.fixedLeftAnalysis_F3
#print axioms YMGap.Continuum.SU2FixedLeftRightFinalDegreeBlock.directRightNestedReconstruct_congr_data
