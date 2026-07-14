/-
# Concrete left-associated fixed-output evaluation

This module chooses the actual left-associated transvectant coordinate used
for an F-matrix row.  It is built from the checked left-nested global Hahn
coordinate basis and is identified, on the complete physical monomial box,
with the repository's raw ordered `triLeft` map.
-/

import YMGap.Continuum.SU2DirectRightFixedOutputReconstruction

namespace YMGap.Continuum.SU2FixedLeftTransvectantEvaluation

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2ProjectedRawSupportedBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections

local infix:50 " ≈ " => Q'.eqv

/-- A physical left-associated channel with fixed final degree `d`. -/
structure FixedLeftCGChannel (a b c d : Nat) where
  k : Nat
  k_le : k ≤ min a b
  r : Nat
  r_le : r ≤ min (a + b - 2 * k) c
  degree_eq : (a + b - 2 * k) + c - 2 * r = d

/-- Intermediate degree after the first left-associated contraction. -/
def FixedLeftCGChannel.intermediate {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) : Nat :=
  a + b - 2 * q.k

theorem fixedLeft_inner_couplingOrder {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    couplingOrder a b q.intermediate = q.k := by
  have hk := Nat.le_min.mp q.k_le
  have h := couplingOrder_rightChannelLabel a b q.k (by omega)
  simpa only [FixedLeftCGChannel.intermediate, rightChannelLabel] using h

theorem fixedLeft_outer_couplingOrder {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    couplingOrder q.intermediate c d = q.r := by
  have h2r : 2 * q.r ≤ q.intermediate + c := by
    have hr := Nat.le_min.mp q.r_le
    unfold FixedLeftCGChannel.intermediate
    omega
  have hdeg := q.degree_eq
  have hsub : q.intermediate + c - d = 2 * q.r := by
    unfold FixedLeftCGChannel.intermediate at h2r hdeg ⊢
    omega
  unfold couplingOrder
  rw [hsub]
  omega

/-- Global left-nested coordinate carrying output coefficient `s`. -/
def fixedLeftNestedChannel {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (s : Nat) (hs : s ≤ d) :
    LeftNestedCGChannel a b c where
  k := q.k
  k_le := q.k_le
  outer :=
    { k := q.r
      k_le := q.r_le
      s := s
      s_le := by rw [q.degree_eq]; exact hs }

/-- Actual left-associated evaluation on an ambient coefficient tensor. -/
def fixedLeftAnalysis {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (x : TriForm) : BForm :=
  fun s => if hs : s ≤ d then
    leftNestedCoordinates a b c x (fixedLeftNestedChannel q s hs)
  else 0

private theorem bscale_supported (m n : Nat) (q : Q') (x : BForm2)
    (hx : BidegreeSupported m n x) :
    BidegreeSupported m n (bscale q x) := by
  intro i j hij
  exact Q'.eqv_trans _ (q * 0) _
    (Q'.mul_eqv_congr_left q _ _ (hx i j hij))
    (Q'.mul_zero_eqv q)

private theorem pure_leftSlice_scale (i j l x : Nat) :
    BForm2Eqv
      (triSlice (pureTri (mono i) (mono j) (mono l)) x)
      (bscale (mono l x) (tprod (mono i) (mono j))) := by
  intro u v
  unfold triSlice pureTri bscale tprod
  exact Q'.eqv_trans _ ((mono i u * mono j v) * mono l x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ (mono l x * (mono i u * mono j v)) _
      (Q'.mul_comm_eqv _ _) (Q'.eqv_refl _))

/-- On a pure monomial triple, the projected first-pair output agrees with
the literal inner transvectant tensored with the third monomial. -/
theorem firstPairOutput_pure_monomial {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) :
    BForm2Eqv
      (firstPairOutput a b (pureTri (mono i) (mono j) (mono l)) q.k)
      (tprod (transvect a b q.k (tprod (mono i) (mono j))) (mono l)) := by
  intro s x
  let source : BForm2 :=
    triSlice (pureTri (mono i) (mono j) (mono l)) x
  have hsourceScale := pure_leftSlice_scale i j l x
  have hscaled : BidegreeSupported a b
      (bscale (mono l x) (tprod (mono i) (mono j))) :=
    bscale_supported a b (mono l x) (tprod (mono i) (mono j))
      (tprod_mono_supported a b i j hi hj)
  have hsource : BidegreeSupported a b source := by
    intro u v huv
    exact Q'.eqv_trans _ _ _
      (by simpa only [source] using hsourceScale u v)
      (hscaled u v huv)
  have hproject := bidegreeSupported_eqv_rectProject a b source hsource
  have hremove := transvect_congr a b q.k
    (fun u v => Q'.eqv_symm (hproject u v)) s
  have htoscale := transvect_congr a b q.k
    (by simpa only [source] using hsourceScale) s
  have hscale := transvect_scale a b q.k (mono l x)
    (tprod (mono i) (mono j)) s
  exact Q'.eqv_trans _ _ _
    (by simpa only [firstPairOutput, source] using hremove)
    (Q'.eqv_trans _ _ _ htoscale
      (Q'.eqv_trans _ _ _ hscale (Q'.mul_comm_eqv _ _)))

/-- The literal outer tensor in a physical left channel has the expected
bidegree support. -/
theorem fixedLeft_outerTensor_supported {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c) :
    BidegreeSupported q.intermediate c
      (tprod (transvect a b q.k (tprod (mono i) (mono j))) (mono l)) := by
  intro s x houtside
  rcases houtside with hs | hx
  · have hk := Nat.le_min.mp q.k_le
    have hzero := transvect_zero_above_degree a b q.k
      (tprod (mono i) (mono j)) hk.1 hk.2
      (tprod_mono_supported a b i j hi hj) s (by
        simpa only [FixedLeftCGChannel.intermediate] using hs)
    exact Q'.eqv_trans _ (0 * mono l x) _
      (Q'.mul_eqv_congr_right _ _ (mono l x) hzero)
      (Q'.zero_mul_eqv (mono l x))
  · unfold tprod mono
    rw [if_neg (by omega)]
    exact Q'.mul_zero_eqv _

/-- The concrete left evaluation is exactly raw `triLeft` on every physical
pure monomial and the full final output window. -/
theorem fixedLeftAnalysis_pure_monomial_eq_triLeft {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c) :
    FormEqv (d + 1)
      (fixedLeftAnalysis q (pureTri (mono i) (mono j) (mono l)))
      (triLeft a b c d q.intermediate (mono i) (mono j) (mono l)) := by
  intro s hs
  have hsd : s ≤ d := by omega
  unfold fixedLeftAnalysis
  rw [dif_pos hsd]
  let target : BForm2 :=
    tprod (transvect a b q.k (tprod (mono i) (mono j))) (mono l)
  have hfirst := firstPairOutput_pure_monomial q i j l hi hj
  have hphysical : PhysicalRectangleEqv q.intermediate c
      (firstPairOutput a b (pureTri (mono i) (mono j) (mono l)) q.k)
      target := by
    intro u v hu hv
    exact hfirst u v
  have hcongr := globalTransvectCoordinates_congr q.intermediate c
    (firstPairOutput a b (pureTri (mono i) (mono j) (mono l)) q.k)
    target hphysical (fixedLeftNestedChannel q s hsd).outer
  have hraw := globalTransvectCoordinates_eq_raw_of_supported
    q.intermediate c target
    (by simpa only [target] using
      fixedLeft_outerTensor_supported q i j l hi hj hl)
    (fixedLeftNestedChannel q s hsd).outer
  have horders :
      transvect q.intermediate c q.r target s ≈
        triLeft a b c d q.intermediate
          (mono i) (mono j) (mono l) s := by
    simp only [triLeft, fixedLeft_inner_couplingOrder q,
      fixedLeft_outer_couplingOrder q, target]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hcongr
    (Q'.eqv_trans _ _ _ (by
      simpa only [fixedLeftNestedChannel] using hraw) horders)

end YMGap.Continuum.SU2FixedLeftTransvectantEvaluation

#print axioms YMGap.Continuum.SU2FixedLeftTransvectantEvaluation.fixedLeft_inner_couplingOrder
#print axioms YMGap.Continuum.SU2FixedLeftTransvectantEvaluation.fixedLeft_outer_couplingOrder
#print axioms YMGap.Continuum.SU2FixedLeftTransvectantEvaluation.firstPairOutput_pure_monomial
#print axioms YMGap.Continuum.SU2FixedLeftTransvectantEvaluation.fixedLeft_outerTensor_supported
#print axioms YMGap.Continuum.SU2FixedLeftTransvectantEvaluation.fixedLeftAnalysis_pure_monomial_eq_triLeft
