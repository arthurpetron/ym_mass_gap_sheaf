/-
# Linearity of the concrete fixed-left evaluation

The fixed-output right reconstruction synthesizes one tensor from a finite
sum of dependent channel data.  This module proves, from the checked binary
Hahn coordinate equivalence, that the concrete fixed-left evaluator carries
that synthesis to the pointwise sum of the separately synthesized sections.
-/

import YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
import YMGap.Continuum.SU2TransvectantAdmissibleSynthesis

namespace YMGap.Continuum.SU2FixedLeftEvaluationLinearity

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation

local infix:50 " ≈ " => Q'.eqv

/-! ## Binary projected-coordinate linearity -/

/-- Physical projection distributes over pointwise addition. -/
theorem rectProject_badd (m n : Nat) (x y : BForm2) :
    BForm2Eqv (rectProject m n (badd x y))
      (badd (rectProject m n x) (rectProject m n y)) := by
  intro i j
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ n
    · exact Q'.eqv_trans _ _ _
        (rectProject_apply_physical m n (badd x y) i j hi hj)
        (Q'.add_eqv_congr'
          (Q'.eqv_symm (rectProject_apply_physical m n x i j hi hj))
          (Q'.eqv_symm (rectProject_apply_physical m n y i j hi hj)))
    · have hx := rectProject_zero_outside m n x i j (Or.inr (by omega))
      have hy := rectProject_zero_outside m n y i j (Or.inr (by omega))
      exact Q'.eqv_trans _ 0 _
        (rectProject_zero_outside m n (badd x y) i j (Or.inr (by omega)))
        (Q'.eqv_symm (Q'.eqv_trans _ (0 + 0) _
          (Q'.add_eqv_congr' hx hy) (Q'.eqv_of_eq (Q'.zero_add' 0))))
  · have hx := rectProject_zero_outside m n x i j (Or.inl (by omega))
    have hy := rectProject_zero_outside m n y i j (Or.inl (by omega))
    exact Q'.eqv_trans _ 0 _
      (rectProject_zero_outside m n (badd x y) i j (Or.inl (by omega)))
      (Q'.eqv_symm (Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' hx hy) (Q'.eqv_of_eq (Q'.zero_add' 0))))

/-- Projected transvectant coordinates distribute over pointwise addition. -/
theorem globalTransvectCoordinates_badd (m n : Nat) (x y : BForm2)
    (q : PhysicalCGChannel m n) :
    globalTransvectCoordinates m n (badd x y) q ≈
      globalTransvectCoordinates m n x q +
        globalTransvectCoordinates m n y q := by
  have hproject := transvect_congr m n q.k (rectProject_badd m n x y) q.s
  have hadd := transvect_add m n q.k
    (rectProject m n x) (rectProject m n y) q.s
  exact Q'.eqv_trans _ _ _
    (by simpa only [globalTransvectCoordinates] using hproject)
    (by simpa only [globalTransvectCoordinates] using hadd)

/-- Physical projection of the literal zero tensor is zero. -/
theorem rectProject_zeroForm2 (m n : Nat) :
    BForm2Eqv (rectProject m n zeroForm2) zeroForm2 := by
  intro i j
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ n
    · exact rectProject_apply_physical m n zeroForm2 i j hi hj
    · exact rectProject_zero_outside m n zeroForm2 i j (Or.inr (by omega))
  · exact rectProject_zero_outside m n zeroForm2 i j (Or.inl (by omega))

/-- Every projected coordinate of the literal zero tensor vanishes. -/
theorem globalTransvectCoordinates_zeroForm2 (m n : Nat)
    (q : PhysicalCGChannel m n) :
    globalTransvectCoordinates m n zeroForm2 q ≈ 0 := by
  have hproject := transvect_congr m n q.k (rectProject_zeroForm2 m n) q.s
  exact Q'.eqv_trans _ _ _
    (by simpa only [globalTransvectCoordinates] using hproject)
    (transvect_zeroForm2 m n q.k q.s)

/-- Pointwise addition of dependent binary CG data. -/
def cgDataAdd {m n : Nat} (c d : PhysicalCGChannel m n → Q') :
    PhysicalCGChannel m n → Q' := fun q => c q + d q

/-- The zero dependent binary CG family. -/
def cgDataZero {m n : Nat} : PhysicalCGChannel m n → Q' := fun _ => 0

/-- The checked global Hahn inverse distributes over dependent-data addition
on the complete physical rectangle. -/
theorem globalHahnReconstruct_dataAdd (m n : Nat)
    (c d : PhysicalCGChannel m n → Q') (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) :
    globalHahnReconstruct m n (cgDataAdd c d) i j ≈
      badd (globalHahnReconstruct m n c)
        (globalHahnReconstruct m n d) i j := by
  let z := badd (globalHahnReconstruct m n c)
    (globalHahnReconstruct m n d)
  have hcoords : ∀ q : PhysicalCGChannel m n,
      globalTransvectCoordinates m n z q ≈ cgDataAdd c d q := by
    intro q
    exact Q'.eqv_trans _ _ _
      (globalTransvectCoordinates_badd m n
        (globalHahnReconstruct m n c) (globalHahnReconstruct m n d) q)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (globalTransvectCoordinates_eq_hahn m n
            (globalHahnReconstruct m n c) q)
          (globalHahnCoordinates_reconstruct m n c q))
        (Q'.eqv_trans _ _ _
          (globalTransvectCoordinates_eq_hahn m n
            (globalHahnReconstruct m n d) q)
          (globalHahnCoordinates_reconstruct m n d q)))
  exact Q'.eqv_trans _ _ _
    (globalHahnReconstruct_congr m n (cgDataAdd c d)
      (globalTransvectCoordinates m n z)
      (fun q => Q'.eqv_symm (hcoords q)) i j hi hj)
    (globalHahnReconstruct_transvectCoordinates m n z i j hi hj)

/-- The checked global Hahn inverse sends zero data to the zero tensor on the
complete physical rectangle. -/
theorem globalHahnReconstruct_dataZero (m n : Nat) (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) :
    globalHahnReconstruct m n cgDataZero i j ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (globalHahnReconstruct_congr m n cgDataZero
      (globalTransvectCoordinates m n zeroForm2)
      (fun q => Q'.eqv_symm (globalTransvectCoordinates_zeroForm2 m n q))
      i j hi hj)
    (globalHahnReconstruct_transvectCoordinates m n zeroForm2 i j hi hj)

/-! ## Ordered right-nested synthesis linearity -/

/-- Pointwise addition of complete ordered-right dependent data. -/
def directRightDataAdd {m n p : Nat}
    (c d : DirectRightNestedCGChannel m n p → Q') :
    DirectRightNestedCGChannel m n p → Q' := fun q => c q + d q

/-- The zero ordered-right dependent family. -/
def directRightDataZero {m n p : Nat} :
    DirectRightNestedCGChannel m n p → Q' := fun _ => 0

/-- At one inner order, outer reconstruction distributes over data addition
on its complete physical rectangle. -/
theorem directRightOuterReconstruct_dataAdd {m n p : Nat}
    (c d : DirectRightNestedCGChannel m n p → Q')
    (k : Nat) (hk : k ≤ min n p) (i s : Nat)
    (hi : i ≤ m) (hs : s ≤ n + p - 2 * k) :
    directRightOuterReconstruct (directRightDataAdd c d) k hk i s ≈
      badd (directRightOuterReconstruct c k hk)
        (directRightOuterReconstruct d k hk) i s := by
  simpa only [directRightOuterReconstruct, directRightOuterData,
    directRightDataAdd, cgDataAdd, badd] using
    globalHahnReconstruct_dataAdd m (n + p - 2 * k)
      (directRightOuterData c k hk) (directRightOuterData d k hk)
      i s hi hs

/-- Outer reconstruction of zero ordered-right data vanishes physically. -/
theorem directRightOuterReconstruct_dataZero {m n p : Nat}
    (k : Nat) (hk : k ≤ min n p) (i s : Nat)
    (hi : i ≤ m) (hs : s ≤ n + p - 2 * k) :
    directRightOuterReconstruct
        (directRightDataZero : DirectRightNestedCGChannel m n p → Q')
        k hk i s ≈ 0 := by
  simpa only [directRightOuterReconstruct, directRightOuterData,
    directRightDataZero, cgDataZero] using
    globalHahnReconstruct_dataZero m (n + p - 2 * k) i s hi hs

/-- Pointwise addition and zero on ambient three-factor tensors. -/
def triAdd (x y : TriForm) : TriForm :=
  fun i j l => x i j l + y i j l

def triZero : TriForm := fun _ _ _ => 0

/-- Complete ordered-right synthesis distributes over dependent-data
addition on the physical three-factor box. -/
theorem directRightNestedReconstruct_dataAdd (m n p : Nat)
    (c d : DirectRightNestedCGChannel m n p → Q') :
    PhysicalBoxEqv m n p
      (directRightNestedReconstruct m n p (directRightDataAdd c d))
      (triAdd (directRightNestedReconstruct m n p c)
        (directRightNestedReconstruct m n p d)) := by
  intro i j l hi hj hl
  have hdata : ∀ q : PhysicalCGChannel n p,
      directRightInnerData (directRightDataAdd c d) i q ≈
        cgDataAdd (directRightInnerData c i)
          (directRightInnerData d i) q := by
    intro q
    exact directRightOuterReconstruct_dataAdd c d q.k q.k_le
      i q.s hi q.s_le
  have hcongr := globalHahnReconstruct_congr n p
    (directRightInnerData (directRightDataAdd c d) i)
    (cgDataAdd (directRightInnerData c i) (directRightInnerData d i))
    hdata j l hj hl
  have hadd := globalHahnReconstruct_dataAdd n p
    (directRightInnerData c i) (directRightInnerData d i) j l hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightNestedReconstruct] using hcongr)
    (by simpa only [directRightNestedReconstruct, triAdd, badd] using hadd)

/-- Complete ordered-right synthesis sends zero data to the zero tensor on
the physical three-factor box. -/
theorem directRightNestedReconstruct_dataZero (m n p : Nat) :
    PhysicalBoxEqv m n p
      (directRightNestedReconstruct m n p directRightDataZero) triZero := by
  intro i j l hi hj hl
  have hdata : ∀ q : PhysicalCGChannel n p,
      directRightInnerData
          (directRightDataZero : DirectRightNestedCGChannel m n p → Q')
          i q ≈ cgDataZero q := by
    intro q
    exact directRightOuterReconstruct_dataZero q.k q.k_le
      i q.s hi q.s_le
  have hcongr := globalHahnReconstruct_congr n p
    (directRightInnerData
      (directRightDataZero : DirectRightNestedCGChannel m n p → Q') i)
    cgDataZero hdata j l hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightNestedReconstruct] using hcongr)
    (by simpa only [triZero] using
      globalHahnReconstruct_dataZero n p j l hj hl)

/-! ## Concrete fixed-left evaluation linearity -/

/-- A first-pair output distributes over ambient tensor addition on the
physical intermediate-output/third-leg rectangle. -/
theorem firstPairOutput_triAdd (m n p : Nat) (x y : TriForm)
    (k : Nat) (hk : k ≤ min m n) :
    PhysicalRectangleEqv (m + n - 2 * k) p
      (firstPairOutput m n (triAdd x y) k)
      (badd (firstPairOutput m n x k) (firstPairOutput m n y k)) := by
  intro s l hs hl
  let q : PhysicalCGChannel m n :=
    { k := k, k_le := hk, s := s, s_le := hs }
  have hadd := globalTransvectCoordinates_badd m n
    (triSlice x l) (triSlice y l) q
  simpa only [firstPairOutput, triSlice, triAdd,
    globalTransvectCoordinates, badd, q] using hadd

/-- A first-pair output of the ambient zero tensor vanishes on the physical
intermediate-output/third-leg rectangle. -/
theorem firstPairOutput_triZero (m n p : Nat)
    (k : Nat) (hk : k ≤ min m n) :
    PhysicalRectangleEqv (m + n - 2 * k) p
      (firstPairOutput m n triZero k) zeroForm2 := by
  intro s l hs hl
  let q : PhysicalCGChannel m n :=
    { k := k, k_le := hk, s := s, s_le := hs }
  have hz := globalTransvectCoordinates_zeroForm2 m n q
  simpa only [firstPairOutput, triSlice, triZero,
    globalTransvectCoordinates, zeroForm2, q] using hz

/-- Every left-nested coordinate distributes over ambient tensor addition. -/
theorem leftNestedCoordinates_triAdd (m n p : Nat) (x y : TriForm)
    (q : LeftNestedCGChannel m n p) :
    leftNestedCoordinates m n p (triAdd x y) q ≈
      leftNestedCoordinates m n p x q +
        leftNestedCoordinates m n p y q := by
  have hphysical := firstPairOutput_triAdd m n p x y q.k q.k_le
  have hcongr := globalTransvectCoordinates_congr
    (m + n - 2 * q.k) p
    (firstPairOutput m n (triAdd x y) q.k)
    (badd (firstPairOutput m n x q.k) (firstPairOutput m n y q.k))
    hphysical q.outer
  exact Q'.eqv_trans _ _ _
    (by simpa only [leftNestedCoordinates] using hcongr)
    (globalTransvectCoordinates_badd (m + n - 2 * q.k) p
      (firstPairOutput m n x q.k) (firstPairOutput m n y q.k) q.outer)

/-- Every left-nested coordinate of the zero tensor vanishes. -/
theorem leftNestedCoordinates_triZero (m n p : Nat)
    (q : LeftNestedCGChannel m n p) :
    leftNestedCoordinates m n p triZero q ≈ 0 := by
  have hphysical := firstPairOutput_triZero m n p q.k q.k_le
  have hcongr := globalTransvectCoordinates_congr
    (m + n - 2 * q.k) p
    (firstPairOutput m n triZero q.k) zeroForm2 hphysical q.outer
  exact Q'.eqv_trans _ _ _
    (by simpa only [leftNestedCoordinates] using hcongr)
    (globalTransvectCoordinates_zeroForm2 (m + n - 2 * q.k) p q.outer)

/-- The concrete fixed-left analysis respects equality on the physical
three-factor coefficient box. -/
theorem fixedLeftAnalysis_congr {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (x y : TriForm)
    (hxy : PhysicalBoxEqv a b c x y) :
    BFormEqv (fixedLeftAnalysis q x) (fixedLeftAnalysis q y) := by
  intro s
  unfold fixedLeftAnalysis
  by_cases hs : s ≤ d
  · rw [dif_pos hs, dif_pos hs]
    exact leftNestedCoordinates_congr a b c x y hxy
      (fixedLeftNestedChannel q s hs)
  · rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_refl _

/-- The concrete fixed-left analysis is additive on ambient tensors. -/
theorem fixedLeftAnalysis_triAdd {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (x y : TriForm) :
    BFormEqv (fixedLeftAnalysis q (triAdd x y))
      (addForm (fixedLeftAnalysis q x) (fixedLeftAnalysis q y)) := by
  intro s
  unfold fixedLeftAnalysis addForm
  by_cases hs : s ≤ d
  · simp only [dif_pos hs]
    exact leftNestedCoordinates_triAdd a b c x y
      (fixedLeftNestedChannel q s hs)
  · simp only [dif_neg hs]
    exact Q'.eqv_of_eq (Q'.zero_add' 0).symm

/-- The concrete fixed-left analysis sends the ambient zero tensor to the
zero output form. -/
theorem fixedLeftAnalysis_triZero {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    BFormEqv (fixedLeftAnalysis q triZero) zeroF := by
  intro s
  unfold fixedLeftAnalysis
  by_cases hs : s ≤ d
  · rw [dif_pos hs]
    exact leftNestedCoordinates_triZero a b c
      (fixedLeftNestedChannel q s hs)
  · rw [dif_neg hs]
    exact Q'.eqv_refl _

/-! ## Evaluation of finite fixed-output section sums -/

/-- The empty fixed-right section synthesis is physically the zero ambient
tensor. -/
theorem fixedRightSectionSum_nil {a b c d : Nat} (x : TriForm) :
    PhysicalBoxEqv a b c
      (fixedRightSectionSum
        ([] : List (FixedRightCGChannel a b c d)) x) triZero := by
  simpa only [fixedRightSectionSum, fixedRightSectionDataSum,
    directRightDataZero] using
    directRightNestedReconstruct_dataZero a b c

/-- Adding a head channel to a section list is physically the ambient sum
of its individual section and the remaining section synthesis. -/
theorem fixedRightSectionSum_cons {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c d)) (x : TriForm) :
    PhysicalBoxEqv a b c
      (fixedRightSectionSum (q :: qs) x)
      (triAdd (fixedRightSection q (fixedRightAnalysis q x))
        (fixedRightSectionSum qs x)) := by
  simpa only [fixedRightSectionSum, fixedRightSection,
    fixedRightSectionDataSum, directRightDataAdd] using
    directRightNestedReconstruct_dataAdd a b c
      (fixedRightSectionData q (fixedRightAnalysis q x))
      (fixedRightSectionDataSum qs x)

/-- **Finite-section evaluation law.**  Concrete fixed-left analysis of one
synthesis from summed right-channel data equals the recursive pointwise sum
of the separately analyzed global sections.  The law holds for every ambient
tensor and every channel list. -/
theorem fixedLeftAnalysis_fixedRightSectionSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c d)) (x : TriForm) :
    BFormEqv
      (fixedLeftAnalysis qL (fixedRightSectionSum qs x))
      (fixedRightEvalSectionSum (fixedLeftAnalysis qL) qs x) := by
  induction qs with
  | nil =>
      have hphysical := fixedRightSectionSum_nil
        (a := a) (b := b) (c := c) (d := d) x
      have hcongr := fixedLeftAnalysis_congr qL _ _ hphysical
      have hzero := fixedLeftAnalysis_triZero qL
      intro s
      exact Q'.eqv_trans _ _ _ (hcongr s)
        (by simpa only [fixedRightEvalSectionSum, formListSum] using hzero s)
  | cons q qs ih =>
      have hphysical := fixedRightSectionSum_cons q qs x
      have hcongr := fixedLeftAnalysis_congr qL _ _ hphysical
      have hadd := fixedLeftAnalysis_triAdd qL
        (fixedRightSection q (fixedRightAnalysis q x))
        (fixedRightSectionSum qs x)
      intro s
      exact Q'.eqv_trans _ _ _ (hcongr s)
        (Q'.eqv_trans _ _ _ (hadd s)
          (by simpa only [fixedRightEvalSectionSum, formListSum, addForm]
            using Q'.add_eqv_congr' (Q'.eqv_refl _) (ih s)))

/-- Canonical enumerated specialization of the finite-section evaluation
law, directly discharging the concrete wrapper's `hevalSectionSum` premise. -/
theorem fixedLeftAnalysis_enumeratedSectionSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (x : TriForm) :
    BFormEqv
      (fixedLeftAnalysis qL
        (fixedRightEnumeratedSectionSum a b c d x))
      (fixedRightEvalSectionSum (fixedLeftAnalysis qL)
        (fixedRightChannels a b c d) x) := by
  simpa only [fixedRightEnumeratedSectionSum] using
    fixedLeftAnalysis_fixedRightSectionSum qL
      (fixedRightChannels a b c d) x

/-- Fixed-left analysis has literal zero coefficients above its selected
final degree. -/
theorem fixedLeftAnalysis_zero_outside {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (x : TriForm)
    (s : Nat) (hs : d < s) : fixedLeftAnalysis qL x s ≈ 0 := by
  unfold fixedLeftAnalysis
  rw [dif_neg (by omega)]
  exact Q'.eqv_refl _

/-! ## Exact final-degree projection residual -/

/-- Regard an arbitrary ordered-right channel known to have final degree `d`
as a proof-carrying fixed-output channel. -/
def fixedRightChannelOfFinalDegree {a b c d : Nat}
    (u : DirectRightNestedCGChannel a b c)
    (hdegree : directRightFinalDegree u = d) :
    FixedRightCGChannel a b c d where
  p := u.k
  p_le := u.k_le
  r := u.outer.k
  r_le := u.outer.k_le
  degree_eq := hdegree

/-- Converting an ordered-right channel to fixed-output form and then
rebuilding its coefficient channel returns the original dependent channel. -/
theorem fixedRightNestedChannel_ofFinalDegree {a b c d : Nat}
    (u : DirectRightNestedCGChannel a b c)
    (hdegree : directRightFinalDegree u = d) :
    fixedRightNestedChannel (fixedRightChannelOfFinalDegree u hdegree)
      u.outer.s (by
        unfold directRightFinalDegree at hdegree
        rw [← hdegree]
        exact u.outer.s_le) = u := by
  cases u with
  | mk k hk outer =>
      cases outer
      rfl

/-- **The enumerated fixed-output synthesis preserves every ordered-right
coordinate in final degree `d`.**  This is the full coordinate content of
the finite reconstruction, stated without a fixed-channel wrapper. -/
theorem fixedRightEnumeratedSectionSum_coordinate_eq_of_finalDegree
    {a b c d : Nat} (x : TriForm)
    (u : DirectRightNestedCGChannel a b c)
    (hdegree : directRightFinalDegree u = d) :
    directRightNestedCoordinates a b c
        (fixedRightEnumeratedSectionSum a b c d x) u ≈
      directRightNestedCoordinates a b c x u := by
  let q := fixedRightChannelOfFinalDegree u hdegree
  have hs : u.outer.s ≤ d := by
    unfold directRightFinalDegree at hdegree
    rw [← hdegree]
    exact u.outer.s_le
  have hcomplete := fixedRightAnalysis_enumeratedSectionSum x q
    u.outer.s (by omega)
  unfold fixedRightAnalysis at hcomplete
  rw [dif_pos hs, dif_pos hs] at hcomplete
  have hchannel := fixedRightNestedChannel_ofFinalDegree u hdegree
  simpa only [q, hchannel] using hcomplete

/-- The exact representation-block statement required by fixed-output
projection: the concrete fixed-left row factors through the family of
ordered-right coordinates having the same final degree `d`.

Unlike the desired projection equality, this predicate mentions no chosen
enumeration or reconstruction.  It is precisely the remaining cross-degree
block-diagonality theorem for the actual nested transvectant evaluator. -/
def FixedLeftRespectsRightFinalDegree {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) : Prop :=
  ∀ x y : TriForm,
    (∀ u : DirectRightNestedCGChannel a b c,
      directRightFinalDegree u = d →
        directRightNestedCoordinates a b c x u ≈
          directRightNestedCoordinates a b c y u) →
    BFormEqv (fixedLeftAnalysis qL x) (fixedLeftAnalysis qL y)

/-- The representation-block statement implies the required fixed-output
projection theorem for every ambient tensor. -/
theorem fixedLeftAnalysis_projection_of_rightFinalDegree
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (hblock : FixedLeftRespectsRightFinalDegree qL) (x : TriForm) :
    BFormEqv (fixedLeftAnalysis qL x)
      (fixedLeftAnalysis qL
        (fixedRightEnumeratedSectionSum a b c d x)) := by
  apply hblock
  intro u hdegree
  exact Q'.eqv_symm
    (fixedRightEnumeratedSectionSum_coordinate_eq_of_finalDegree
      x u hdegree)

end YMGap.Continuum.SU2FixedLeftEvaluationLinearity

#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.rectProject_badd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.globalTransvectCoordinates_badd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.rectProject_zeroForm2
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.globalTransvectCoordinates_zeroForm2
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.globalHahnReconstruct_dataAdd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.globalHahnReconstruct_dataZero
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.directRightOuterReconstruct_dataAdd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.directRightOuterReconstruct_dataZero
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.directRightNestedReconstruct_dataAdd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.directRightNestedReconstruct_dataZero
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.firstPairOutput_triAdd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.firstPairOutput_triZero
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.leftNestedCoordinates_triAdd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.leftNestedCoordinates_triZero
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedLeftAnalysis_congr
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedLeftAnalysis_triAdd
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedLeftAnalysis_triZero
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedRightSectionSum_nil
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedRightSectionSum_cons
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedLeftAnalysis_fixedRightSectionSum
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedLeftAnalysis_enumeratedSectionSum
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedLeftAnalysis_zero_outside
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedRightNestedChannel_ofFinalDegree
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedRightEnumeratedSectionSum_coordinate_eq_of_finalDegree
#print axioms YMGap.Continuum.SU2FixedLeftEvaluationLinearity.fixedLeftAnalysis_projection_of_rightFinalDegree
