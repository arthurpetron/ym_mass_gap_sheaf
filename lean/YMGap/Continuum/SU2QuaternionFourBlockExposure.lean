/-
# Constructive four-block exposure on an arbitrary Haar carrier

Four distinct original blocks are moved to 0, 1, 2, 3 by four explicit
transpositions. Each extension preserves the already pinned coordinates.
The source pins feed the existing coordinate-polynomial and full-Haar
change-of-variables theorems; no finite-carrier search is used.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

namespace YMGap.Continuum.SU2QuaternionFourBlockExposure

set_option autoImplicit false

open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier

/-- Forward coordinate map, inverse to the existing contravariant source map. -/
def chainTarget {blocks : Nat} : List (QuaternionBlockInvolution blocks) → Nat → Nat
  | [], block => block
  | swap :: rest, block => chainTarget rest (swap.map block)

theorem chainTarget_lt {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    {block : Nat} (hb : block < blocks) : chainTarget steps block < blocks := by
  induction steps generalizing block with
  | nil => exact hb
  | cons swap rest ih => exact ih (swap.map_lt block hb)

theorem source_target {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    {block : Nat} (hb : block < blocks) :
    quaternionBlockSwapChainSource steps (chainTarget steps block) = block := by
  induction steps generalizing block with
  | nil => rfl
  | cons swap rest ih =>
    change swap.map (quaternionBlockSwapChainSource rest (chainTarget rest (swap.map block))) = block
    rw [ih (swap.map_lt block hb), swap.involutive block hb]

theorem source_append {blocks : Nat} (first second : List (QuaternionBlockInvolution blocks))
    (block : Nat) : quaternionBlockSwapChainSource (first ++ second) block =
      quaternionBlockSwapChainSource first (quaternionBlockSwapChainSource second block) := by
  induction first with
  | nil => rfl
  | cons swap rest ih =>
    change swap.map (quaternionBlockSwapChainSource (rest ++ second) block) = _
    rw [ih]
    rfl

/-- Append one explicit transposition sending the requested source to target. -/
def extend {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    (target source : Fin blocks) : List (QuaternionBlockInvolution blocks) :=
  steps ++ [blockSwapInvolution blocks target.val (chainTarget steps source.val)
    target.isLt (chainTarget_lt steps source.isLt)]

theorem extend_source {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    (target source : Fin blocks) :
    quaternionBlockSwapChainSource (extend steps target source) target.val = source.val := by
  unfold extend
  rw [source_append]
  change quaternionBlockSwapChainSource steps
    ((blockSwapInvolution blocks target.val (chainTarget steps source.val)
      target.isLt (chainTarget_lt steps source.isLt)).map target.val) = source.val
  rw [blockSwapInvolution_map_first]
  exact source_target steps source.isLt

/-- An earlier pin survives when both its source and target are distinct. -/
theorem extend_preserves {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    (target source : Fin blocks) {oldTarget oldSource : Nat}
    (hp : quaternionBlockSwapChainSource steps oldTarget = oldSource)
    (ht : oldTarget ≠ target.val) (hs : oldSource ≠ source.val) :
    quaternionBlockSwapChainSource (extend steps target source) oldTarget = oldSource := by
  have hn : oldTarget ≠ chainTarget steps source.val := by
    intro h
    have hh := source_target steps source.isLt
    rw [← h, hp] at hh
    exact hs hh
  unfold extend
  rw [source_append]
  simpa only [quaternionBlockSwapChainSource, blockSwapInvolution, blockSwapMap,
    if_neg ht, if_neg hn] using hp

/-- Witnessing data for the original four coordinates and their exact pins. -/
structure FourBlockExposure {blocks : Nat} (a b c d : Fin blocks) where
  steps : List (QuaternionBlockInvolution blocks)
  source_zero : quaternionBlockSwapChainSource steps 0 = a.val
  source_one : quaternionBlockSwapChainSource steps 1 = b.val
  source_two : quaternionBlockSwapChainSource steps 2 = c.val
  source_three : quaternionBlockSwapChainSource steps 3 = d.val

/-- Four deterministic swaps, with no search, choice, or carrier-size scan. -/
def fourBlockExposure {blocks : Nat} (hb : 3 < blocks) (a b c d : Fin blocks)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    FourBlockExposure a b c d := by
  let z : Fin blocks := ⟨0, by omega⟩
  let o : Fin blocks := ⟨1, by omega⟩
  let t : Fin blocks := ⟨2, by omega⟩
  let h : Fin blocks := ⟨3, hb⟩
  let s0 := extend [] z a
  let s1 := extend s0 o b
  let s2 := extend s1 t c
  let s3 := extend s2 h d
  have p0 : quaternionBlockSwapChainSource s0 0 = a.val := extend_source [] z a
  have p10 : quaternionBlockSwapChainSource s1 0 = a.val :=
    extend_preserves s0 o b p0 (by change (0 : Nat) ≠ 1; decide) hab
  have p11 : quaternionBlockSwapChainSource s1 1 = b.val := extend_source s0 o b
  have p20 : quaternionBlockSwapChainSource s2 0 = a.val :=
    extend_preserves s1 t c p10 (by change (0 : Nat) ≠ 2; decide) hac
  have p21 : quaternionBlockSwapChainSource s2 1 = b.val :=
    extend_preserves s1 t c p11 (by change (1 : Nat) ≠ 2; decide) hbc
  have p22 : quaternionBlockSwapChainSource s2 2 = c.val := extend_source s1 t c
  exact ⟨s3, extend_preserves s2 h d p20 (by change (0 : Nat) ≠ 3; decide) had,
    extend_preserves s2 h d p21 (by change (1 : Nat) ≠ 3; decide) hbd,
    extend_preserves s2 h d p22 (by change (2 : Nat) ≠ 3; decide) hcd, extend_source s2 h d⟩

end YMGap.Continuum.SU2QuaternionFourBlockExposure

#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.chainTarget
#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.chainTarget_lt
#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.source_target
#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.source_append
#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.extend
#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.extend_source
#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.extend_preserves
#print axioms YMGap.Continuum.SU2QuaternionFourBlockExposure.fourBlockExposure
