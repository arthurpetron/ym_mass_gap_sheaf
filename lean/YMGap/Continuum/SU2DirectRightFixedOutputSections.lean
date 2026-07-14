/-
# Fixed-output ordered right-channel sections

The global ordered right-nested coordinate basis contains every output
degree at once.  For a fixed final degree `d`, a physical right channel is
an inner contraction order `p` and an outer contraction order `r` whose
residual degree is exactly `d`.  Extending one output form by zero on all
other nested coordinates gives a concrete ambient section.  The global
coordinate inverse then proves exact same-channel recovery and cross-channel
annihilation.
-/

import YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
import YMGap.Continuum.SU2ProjectedRawSupportedBridge
import YMGap.Continuum.SU2TransvectantCentralChannelEquation
import YMGap.Continuum.SU2ChannelAmbientMonomialSectionSchurReconstruction

namespace YMGap.Continuum.SU2DirectRightFixedOutputSections

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
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2ProjectedRawSupportedBridge
open YMGap.Continuum.SU2ChannelSectionSchurReconstruction
open YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction
open YMGap.Continuum.SU2ChannelAmbientMonomialSectionSchurReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- A physical ordered right-associated channel with fixed final degree
`d`: first contract `(b,c)` at order `p`, then contract the ordered pair
`(a,b+c-2p)` at order `r`. -/
structure FixedRightCGChannel (a b c d : Nat) where
  p : Nat
  p_le : p ≤ min b c
  r : Nat
  r_le : r ≤ min a (b + c - 2 * p)
  degree_eq : a + (b + c - 2 * p) - 2 * r = d

/-- The intermediate degree carried by a fixed right channel. -/
def FixedRightCGChannel.intermediate {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Nat :=
  b + c - 2 * q.p

/-- The intermediate label has exactly the recorded inner contraction
order. -/
theorem fixedRight_inner_couplingOrder {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    couplingOrder b c q.intermediate = q.p := by
  have hp := Nat.le_min.mp q.p_le
  have h := couplingOrder_rightChannelLabel b c q.p (by omega)
  simpa only [FixedRightCGChannel.intermediate, rightChannelLabel] using h

/-- The final label has exactly the recorded outer contraction order. -/
theorem fixedRight_outer_couplingOrder {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    couplingOrder a q.intermediate d = q.r := by
  have h2r : 2 * q.r ≤ a + q.intermediate := by
    have hr := Nat.le_min.mp q.r_le
    unfold FixedRightCGChannel.intermediate
    omega
  have hdeg := q.degree_eq
  have hsub : a + q.intermediate - d = 2 * q.r := by
    unfold FixedRightCGChannel.intermediate at h2r hdeg ⊢
    omega
  unfold couplingOrder
  rw [hsub]
  omega

/-- Insert one output coefficient into the global ordered right-nested
coordinate family. -/
def fixedRightSectionData {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (v : BForm) :
    DirectRightNestedCGChannel a b c → Q' :=
  fun u => if h : u.k = q.p ∧ u.outer.k = q.r then v u.outer.s else 0

/-- Concrete ambient section of one fixed-output right channel. -/
def fixedRightSection {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (v : BForm) : TriForm :=
  directRightNestedReconstruct a b c (fixedRightSectionData q v)

/-- The global nested channel coordinate associated to output coefficient
`s` in a fixed-output channel. -/
def fixedRightNestedChannel {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) (hs : s ≤ d) :
    DirectRightNestedCGChannel a b c where
  k := q.p
  k_le := q.p_le
  outer :=
    { k := q.r
      k_le := q.r_le
      s := s
      s_le := by rw [q.degree_eq]; exact hs }

/-- Analyze one fixed-output right channel, setting coefficients above the
final degree window to zero. -/
def fixedRightAnalysis {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (x : TriForm) : BForm :=
  fun s => if hs : s ≤ d then
    directRightNestedCoordinates a b c x
      (fixedRightNestedChannel q s hs)
  else 0

/-- Exact analysis of a concrete channel section.  This is the master
same-channel/cross-channel law before deciding whether the two channel labels
agree. -/
theorem fixedRightAnalysis_section {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) (v : BForm)
    (s : Nat) (hs : s ≤ d) :
    fixedRightAnalysis u (fixedRightSection q v) s ≈
      if h : u.p = q.p ∧ u.r = q.r then v s else 0 := by
  unfold fixedRightAnalysis
  rw [dif_pos hs]
  have hcoord := directRightNestedCoordinates_reconstruct a b c
    (fixedRightSectionData q v) (fixedRightNestedChannel u s hs)
  exact Q'.eqv_trans _ _ _ hcoord (by
    unfold fixedRightSectionData fixedRightNestedChannel
    rfl)

/-- Analyzed data is recovered exactly on the selected channel. -/
theorem fixedRightAnalysis_own_section {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (v : BForm) :
    FormEqv (d + 1) (fixedRightAnalysis q (fixedRightSection q v)) v := by
  intro s hs
  have hs' : s ≤ d := by omega
  have h := fixedRightAnalysis_section q q v s hs'
  have heq : q.p = q.p ∧ q.r = q.r := ⟨rfl, rfl⟩
  rw [dif_pos heq] at h
  exact h

/-- Sections of distinct `(inner,outer)` channels have zero analysis in the
chosen channel. -/
theorem fixedRightAnalysis_other_section {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) (v : BForm)
    (hqu : ¬ (u.p = q.p ∧ u.r = q.r)) :
    FormEqv (d + 1) (fixedRightAnalysis u (fixedRightSection q v)) zeroF := by
  intro s hs
  have hs' : s ≤ d := by omega
  have h := fixedRightAnalysis_section q u v s hs'
  rw [dif_neg hqu] at h
  simpa only [zeroF] using h

/-! ## Identification with the raw ordered `triRight` channel -/

/-- Coefficient tensor of a pure ordered triple. -/
def pureTri (x y z : BForm) : TriForm :=
  fun i j l => x i * (y j * z l)

private theorem bscale_supported (m n : Nat) (q : Q') (x : BForm2)
    (hx : BidegreeSupported m n x) :
    BidegreeSupported m n (bscale q x) := by
  intro i j hij
  exact Q'.eqv_trans _ (q * 0) _
    (Q'.mul_eqv_congr_left q _ _ (hx i j hij))
    (Q'.mul_zero_eqv q)

/-- On a pure monomial triple, the projected last-pair output agrees
pointwise with the literal inner transvectant tensored on the right of the
first monomial. -/
theorem lastPairOutput_pure_monomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hj : j ≤ b) (hl : l ≤ c) :
    BForm2Eqv
      (lastPairOutput b c (pureTri (mono i) (mono j) (mono l)) q.p)
      (tprod (mono i)
        (transvect b c q.p (tprod (mono j) (mono l)))) := by
  intro x s
  let source : BForm2 :=
    rightTriSlice (pureTri (mono i) (mono j) (mono l)) x
  have hsource : BidegreeSupported b c source := by
    have ht := tprod_mono_supported b c j l hj hl
    have hs := bscale_supported b c (mono i x)
      (tprod (mono j) (mono l)) ht
    simpa only [source, rightTriSlice, pureTri, bscale, tprod] using hs
  have hproject := bidegreeSupported_eqv_rectProject b c source hsource
  have hremove := transvect_congr b c q.p
    (fun y z => Q'.eqv_symm (hproject y z)) s
  have hscale := transvect_scale b c q.p (mono i x)
    (tprod (mono j) (mono l)) s
  exact Q'.eqv_trans _ _ _
    (by simpa only [lastPairOutput, source] using hremove)
    (by simpa only [source, rightTriSlice, pureTri, bscale, tprod] using hscale)

/-- The literal outer tensor occurring in a physical ordered right channel
has its expected bidegree support. -/
theorem fixedRight_outerTensor_supported {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c) :
    BidegreeSupported a q.intermediate
      (tprod (mono i)
        (transvect b c q.p (tprod (mono j) (mono l)))) := by
  intro x s houtside
  rcases houtside with hx | hs
  · unfold tprod mono
    rw [if_neg (by omega)]
    exact Q'.zero_mul_eqv _
  · have hp := Nat.le_min.mp q.p_le
    have hzero := transvect_zero_above_degree b c q.p
      (tprod (mono j) (mono l)) hp.1 hp.2
      (tprod_mono_supported b c j l hj hl) s (by
        simpa only [FixedRightCGChannel.intermediate] using hs)
    exact Q'.eqv_trans _ ((mono i x) * 0) _
      (Q'.mul_eqv_congr_left (mono i x) _ _ hzero)
      (Q'.mul_zero_eqv (mono i x))

/-- On every pure monomial in the physical source box, fixed-output analysis
is exactly the repository's raw ordered right-associated channel. -/
theorem fixedRightAnalysis_pure_monomial_eq_triRight {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c) :
    FormEqv (d + 1)
      (fixedRightAnalysis q (pureTri (mono i) (mono j) (mono l)))
      (triRight a b c d q.intermediate (mono i) (mono j) (mono l)) := by
  intro s hs
  have hsd : s ≤ d := by omega
  unfold fixedRightAnalysis
  rw [dif_pos hsd]
  let target : BForm2 := tprod (mono i)
    (transvect b c q.p (tprod (mono j) (mono l)))
  have hlast := lastPairOutput_pure_monomial q i j l hj hl
  have hphysical : PhysicalRectangleEqv a q.intermediate
      (lastPairOutput b c (pureTri (mono i) (mono j) (mono l)) q.p)
      target := by
    intro x t hx ht
    exact hlast x t
  have hcongr := globalTransvectCoordinates_congr a q.intermediate
    (lastPairOutput b c (pureTri (mono i) (mono j) (mono l)) q.p)
    target hphysical (fixedRightNestedChannel q s hsd).outer
  have hraw := globalTransvectCoordinates_eq_raw_of_supported
    a q.intermediate target
    (by simpa only [target] using
      fixedRight_outerTensor_supported q i j l hi hj hl)
    (fixedRightNestedChannel q s hsd).outer
  have horders :
      transvect a q.intermediate q.r target s ≈
        triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s := by
    simp only [triRight, fixedRight_inner_couplingOrder q,
      fixedRight_outer_couplingOrder q, target]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hcongr
    (Q'.eqv_trans _ _ _ (by
      simpa only [fixedRightNestedChannel] using hraw) horders)

/-! ## Concrete ambient-section specialization -/

/-- **Fixed-output ordered right-channel Schur wrapper.**

The carrier, packing, analyses, and channel sections are now completely
concrete.  The remaining hypotheses concern only the map being recoupled:
its evaluation on pure tensors, reconstruction through a chosen finite
enumeration of physical fixed-output channels, and diagonal/lowering
covariance of each evaluated channel section. -/
theorem triMapEqv_rightFixedChannels_of_sections_schur
    (a b c d N : Nat)
    (L : BForm → BForm → BForm → BForm)
    (channel : Nat → FixedRightCGChannel a b c d)
    (evalL : TriForm → BForm)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q, q < N → HasDiagonalModel
      (ambientInduced evalL (fixedRightSection (channel q))) (coeff q))
    (hF : ∀ q, q < N → EndomorphismLoweringCovariant d
      (ambientInduced evalL (fixedRightSection (channel q))))
    (hpack : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (L (mono i) (mono j) (mono l))
          (evalL (pureTri (mono i) (mono j) (mono l))))
    (hreconstruct : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (evalL (pureTri (mono i) (mono j) (mono l)))
          (formPrefix N (fun q =>
            ambientInduced evalL (fixedRightSection (channel q))
              (fixedRightAnalysis (channel q)
                (pureTri (mono i) (mono j) (mono l)))))) :
    TriMapEqv a b c d L
      (rightChannelPrefix a b c d N (fun q => (channel q).p)
        (fun q => coeff q 0)) := by
  apply triMapEqv_rightChannels_of_ambient_sections_schur_on_monomials
    TriForm a b c d N L (fun q => (channel q).p)
    pureTri evalL (fun q => fixedRightAnalysis (channel q))
    (fun q => fixedRightSection (channel q)) coeff
    hdiag hF hpack hreconstruct
  intro q hq i hi j hj l hl
  have h := fixedRightAnalysis_pure_monomial_eq_triRight
    (channel q) i j l (by omega) (by omega) (by omega)
  simpa only [FixedRightCGChannel.intermediate, rightChannelLabel] using h

end YMGap.Continuum.SU2DirectRightFixedOutputSections

#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.fixedRight_inner_couplingOrder
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.fixedRight_outer_couplingOrder
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.fixedRightAnalysis_section
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.fixedRightAnalysis_own_section
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.fixedRightAnalysis_other_section
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.lastPairOutput_pure_monomial
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.fixedRight_outerTensor_supported
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.fixedRightAnalysis_pure_monomial_eq_triRight
#print axioms YMGap.Continuum.SU2DirectRightFixedOutputSections.triMapEqv_rightFixedChannels_of_sections_schur
