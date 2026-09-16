/-
# Original multi-time spatial probes realize the constructed window limit

A finite schedule of signed spatial face-character lists is placed at its
literal times inside one selected fixed-width chain. The complete window
embedding and temporal sweep identify the original numerator with the
existing observedMessage pairing. Both reciprocal constructions cancel
the SAME original partition. No action factor, coefficient or probe order
is changed, and the final spatial V occurs once.

The original varying-extent finiteValue stream consequently has the already
constructed window CReal as its two-boundary time limit, with the same
explicit modulus and rectangular representative bound. Only scheduled
physical spatial probes are identified; arbitrary coordinate polynomials
are not silently declared gauge observables. The ambient box encodes a
selected fixed-width action, not the full growing-box plaquette action.

Nome, spatial width and retained heat cutoff remain fixed. Reflected OS
positivity for the same selected chain, physical transfer/vacuum, cutoff
removal, width/spacing control and the continuum mass gap remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (terminalPair_total)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary (windowTimeCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal (reciprocalTerm)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- The original signed probe schedule and complete selected action share
one Haar-preserving sweep and the literal complete-window placement. -/
theorem original_window_pairing {width start m L n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent) (w : Q') (K : Nat)
    (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    quaternionHaar (B extent)
        (polyMul (sweptProduct extent 0 (placeWindowProbes (start+m) fs))
          (originalChainAction w K extent width start (m+(L+n)))) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width m L (windowProbe width fs))
          (terminalMessage w K width n)) := by
  have hm : start+m+L ≤ extent := by omega
  let M := embedding L (start := start+m) hw hm
  let p := windowProbe width fs
  let probes := placeWindowProbes (start+m) fs
  have hprobe := windowProbe_pin hw hm fs hwithin hfaces
  have ha := ambientChain_supported w K extent width start (m+(L+n))
  have hprobes := product_supported (sweptCharacter extent 0)
    (swept_character_supported extent 0) probes
  have hreplace := (hprobe.symm.mul (.refl _ (ambientChain w K extent width start (m+(L+n))))).haar
    (supported_polyMul hprobes ha) (supported_polyMul (M.polynomial_supported p) ha)
  have horiginal := original_chain_pairing w K extent width start (m+(L+n)) probes
    (placeWindowProbes_physical hw hm fs hwithin hfaces)
    (placeWindowProbes_spatial (start+m) fs hfaces)
  exact Q'.eqv_trans _ _ _ horiginal (Q'.eqv_trans _ _ _ hreplace
    (swept_window_pairing hw ht w K p (windowProbe_supported width L fs hwithin)))

/-- The window ratio is the existing original finiteValue, with its actual
selected partition and cutoff schedule. Positive-factor cancellation reuses
the proved rational algebra; no new reciprocal or positivity premise. -/
theorem windowRatio_originalFiniteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start m L n extent : Nat} (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent)
    (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) (stage : Nat) :
    windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        m L n (windowProbe width fs) ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start (m+(L+n)))
        (fun _ hi => chainIds_physical hi)
        (sweptProduct extent 0 (placeWindowProbes (start+m) fs)) stage := by
  let K := headCutoff w+stage
  let z := weightedMass w K width
    (polyMul (terminalMessage w K width (m+L)) (terminalMessage w K width n))
  have hz : (0 : Q') < z := terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _) (m+L) n
  let r := Q'.recipPos z hz
  let s := reciprocalTerm w hw0 hw1 extent (chainIds extent width start (m+(L+n)))
    (fun _ hi => chainIds_physical hi) stage
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z hz
  have hpartition : z ≈ compactPartition w K width (m+(L+n)) := by
    simpa only [Nat.add_assoc] using Q'.eqv_trans _ _ _ (terminalPair_total w K width (m+L) n)
      (weightedMass_iterate_compactPartition w K width ((m+L)+n))
  have hs : z*s ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ s hpartition)
    (compactPartition_reciprocal w hw0 hw1 hw ht stage)
  have hrs : r ≈ s := Q'.mul_left_cancel_of_pos hz (Q'.eqv_trans _ _ _ hr (Q'.eqv_symm hs))
  change weightedMass w K width
      (polyMul (observedMessage w K width m L (windowProbe width fs))
        (terminalMessage w K width n)) * r ≈
    numerator w (B extent) extent (chainIds extent width start (m+(L+n)))
      (sweptProduct extent 0 (placeWindowProbes (start+m) fs)) K * s
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ r (Q'.eqv_symm (original_window_pairing hw ht w K fs hwithin hfaces)))
    (Q'.mul_eqv_congr_left _ _ _ hrs)

/-- The literal original finiteValue on a computed admissible ambient box.
Only the selected fixed-width chain carries action factors. -/
def originalWindowScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width L : Nat) (fs : List (Nat × List FaceFactor)) (stage m n : Nat) : Q' :=
  finiteValue w hw0 hw1 (width+(m+(L+n)))
    (chainIds (width+(m+(L+n))) width 0 (m+(L+n)))
    (fun _ hi => chainIds_physical hi)
    (sweptProduct (width+(m+(L+n))) 0 (placeWindowProbes m fs)) stage

theorem originalWindowScalar_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width L : Nat) (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) (stage m n : Nat) :
    originalWindowScalar hw0 hw1 width L fs stage m n ≈
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n
        (windowProbe width fs) := by
  simpa only [Nat.zero_add] using Q'.eqv_symm (windowRatio_originalFiniteValue hw0 hw1
    (width := width) (start := 0) (m := m) (L := L) (n := n) (extent := width+(m+(L+n)))
    (Nat.le_add_right _ _) (by omega) fs hwithin hfaces stage)

attribute [local irreducible] originalWindowScalar windowRatio baseLinks

/-- Type-level Cauchy data for the original growing-extent diagonal, with
the same explicit cutoff-independent time modulus as the window family. -/
def originalWindowCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width L : Nat) (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) (stage : Nat) :
    QCauchy (fun t => originalWindowScalar hw0 hw1 width L fs stage t t) where
  M := windowTimeModulus hw0 hw1 width (polynomialCap (windowProbe width fs))
  bound := by
    intro epsilon he i j hi hj
    have h := (polynomialWindowCauchy hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) L (windowProbe width fs) (windowProbe_supported width L fs hwithin)).bound
      epsilon he i j hi hj
    have hip := originalWindowScalar_pin hw0 hw1 width L fs hwithin hfaces stage i i
    have hjp := originalWindowScalar_pin hw0 hw1 width L fs hwithin hfaces stage j j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

theorem originalWindowCauchy_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width L : Nat) (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (stage : Nat) (epsilon : Q') :
    (originalWindowCauchy hw0 hw1 width L fs hwithin hfaces stage).M epsilon =
      windowTimeModulus hw0 hw1 width (polynomialCap (windowProbe width fs)) epsilon := rfl

/-- The original physical spatial-probe stream reaches the SAME positive
window family, not a separately normalized or separately chosen limit. -/
theorem originalWindow_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width L : Nat) (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) (stage : Nat) :
    ConvergesTo (fun t => ofQ' (originalWindowScalar hw0 hw1 width L fs stage t t))
      (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        L (windowProbe width fs) (windowProbe_supported width L fs hwithin)) :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun t => ofQ' (windowRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) t L t (windowProbe width fs)))
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 width L fs hwithin hfaces stage t t)))
    (polynomialWindow_converges hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      L (windowProbe width fs) (windowProbe_supported width L fs hwithin))

/-- Arbitrary original left/right distances approach the actual window
representative with the unchanged explicit rectangle error. -/
theorem originalWindow_approx_rectangular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width L : Nat) (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (stage s m n k : Nat) (hm : s+1 ≤ m) (hn : s+1 ≤ n) (hk : s+1 ≤ k) :
    originalWindowScalar hw0 hw1 width L fs stage m n ≤
        (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
          L (windowProbe width fs) (windowProbe_supported width L fs hwithin)).approx k +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap (windowProbe width fs)) ∧
      (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        L (windowProbe width fs) (windowProbe_supported width L fs hwithin)).approx k ≤
        originalWindowScalar hw0 hw1 width L fs stage m n +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap (windowProbe width fs)) := by
  have hb := polynomialWindow_approx_rectangular hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) L (windowProbe width fs) (windowProbe_supported width L fs hwithin)
    s m n k hm hn hk
  have he := originalWindowScalar_pin hw0 hw1 width L fs hwithin hfaces stage m n
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hb.1,
    Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv he))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.original_window_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.windowRatio_originalFiniteValue
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.originalWindowScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.originalWindowScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.originalWindowCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.originalWindowCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.originalWindow_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow.originalWindow_approx_rectangular
