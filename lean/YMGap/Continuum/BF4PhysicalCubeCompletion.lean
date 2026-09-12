/-
# Constructive completion of the same all-spin raw physical cube form

The input GNSData is constructed, not assumed. Its representative vectors are
finite signed combinations of all cube/common-parity labellings. Completion
uses the generic Cauchy quotient and CReal inner-product limit, with explicit
representative moduli and a computed diagonal limit. Every embedded kernel
section has exactly its original, eventually stable physical OS matrix entry.
The vacuum-labelled root remains nonzero in the completion.

Completeness has precisely the existing GeneralCompletionCauchy scope: a
Type-level family of representatives and outer modulus, with propositional
eventual inter-family bounds. No choice of representatives from an arbitrary
quotient-valued sequence is asserted. This is the RAW reflected-form completion
at extent one, not yet the normalized marginal-weighted transfer completion.
No time operator, transfer-fixed vacuum, mass gap, volume limit or continuum
theory is constructed by this module.
-/

import YMGap.Continuum.BF4PhysicalCubeGNSData
import YMGap.Continuum.GNSComplete

namespace YMGap.Continuum.BF4PhysicalCubeCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeKernelSaturation
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

abbrev CubeCompletion (w : Q') (hw : (0 : Q') ≤ w) :=
  GNSCompletionSpace (cubeGNSData w hw)

def embedSpan (w : Q') (hw : (0 : Q') ≤ w) (terms : CubeSpan) : CubeCompletion w hw :=
  embedV (cubeGNSData w hw) terms

def completedInner (w : Q') (hw : (0 : Q') ≤ w) :
    CubeCompletion w hw → CubeCompletion w hw → CReal.RC :=
  (cubeGNSData w hw).cinnerCompl

theorem completedInner_embedSpan (w : Q') (hw : (0 : Q') ≤ w) (left right : CubeSpan) :
    completedInner w hw (embedSpan w hw left) (embedSpan w hw right) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (form (kernel w) left right)) :=
  (cubeGNSData w hw).cinnerCompl_embed left right

def completedBasis (w : Q') (hw : (0 : Q') ≤ w) (state : CubeSectorState) :
    CubeCompletion w hw := embedSpan w hw (basis state)

/-- Exact matrix entries on the embedded all-spin states, not a free model. -/
theorem completedBasis_inner (w : Q') (hw : (0 : Q') ≤ w) (left right : CubeSectorState) :
    completedInner w hw (completedBasis w hw left) (completedBasis w hw right) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (cubeStableRawKernel w left.val right.val)) := by
  rw [completedBasis, completedBasis, completedInner_embedSpan]
  exact Quotient.sound (CReal.ofQ'_equiv_of_eqv (form_basis (kernel w) left right))

/-- After the computed saturation cutoff the completed entry is the literal
finite physical entry, with no limiting approximation error. -/
theorem completedBasis_inner_at_cutoff (w : Q') (hw : (0 : Q') ≤ w)
    (left right : CubeSectorState) (K : Nat)
    (hK : cubeKernelSaturationCutoff left.val right.val ≤ K) :
    completedInner w hw (completedBasis w hw left) (completedBasis w hw right) =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (centralPhysicalReflectedKernel w K 0 left.val right.val)) := by
  rw [completedBasis_inner]
  exact Quotient.sound (CReal.ofQ'_equiv_of_eqv (Q'.eqv_symm
    (cubeStableRawKernel_eventual w left.val right.val left.property.1 right.property.1 K hK)))

/-- A root labelled by the canonical finite vacuum, not yet a transfer vacuum. -/
def completedRoot (w : Q') (hw : (0 : Q') ≤ w) : CubeCompletion w hw :=
  embedSpan w hw rootVector

theorem completedRoot_ne_zero (w : Q') (hw : (0 : Q') ≤ w) :
    completedRoot w hw ≠ embedSpan w hw [] := by
  intro h
  have hembed : embedQuot (cubeGNSData w hw) ((cubeGNSData w hw).qmk rootVector) =
      embedQuot (cubeGNSData w hw) ((cubeGNSData w hw).qmk []) := h
  have hquot := embedQuot_injective (cubeGNSData w hw) hembed
  exact root_not_radical w hw (Quotient.exact hquot)

/-- A finite rational approximation, selected by the supplied squared-norm modulus. -/
def finiteApproximation (w : Q') (hw : (0 : Q') ≤ w)
    (X : CauchyGNS (cubeGNSData w hw)) (epsilon : Q') : CubeSpan :=
  X.seq (X.modulus epsilon)

theorem finiteApproximation_close (w : Q') (hw : (0 : Q') ≤ w)
    (X : CauchyGNS (cubeGNSData w hw)) (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : X.modulus epsilon ≤ n) :
    (cubeGNSData w hw).distSqQ (finiteApproximation w hw X epsilon) (X.seq n) ≤ epsilon :=
  X.isCauchy epsilon hepsilon (X.modulus epsilon) n (Nat.le_refl _) hn

/-- The cofinal-reindexed diagonal limit is retained as data, not chosen from Exists. -/
def cubeCauchyLimit (w : Q') (hw : (0 : Q') ≤ w)
    (X : GeneralCompletionCauchy (cubeGNSData w hw)) : CauchyGNS (cubeGNSData w hw) :=
  X.lim

theorem cubeCauchyLimit_seq (w : Q') (hw : (0 : Q') ≤ w)
    (X : GeneralCompletionCauchy (cubeGNSData w hw)) (n : Nat) :
    (cubeCauchyLimit w hw X).seq n =
      (X.pt (X.phi n)).seq ((X.pt (X.phi n)).modulus (Q'.invSucc n)) := rfl

/-- Its representative squared-distance modulus is the explicit rational rate inverter. -/
theorem cubeCauchyLimit_modulus (w : Q') (hw : (0 : Q') ≤ w)
    (X : GeneralCompletionCauchy (cubeGNSData w hw)) :
    (cubeCauchyLimit w hw X).modulus = gMod := rfl

/-- Generic representative-family completeness for the constructed physical datum. -/
def cubeCompleteHilbert (w : Q') (hw : (0 : Q') ≤ w) :
    CompleteGNSHilbertGeneral (cubeGNSData w hw) where
  hilbert := (cubeGNSData w hw).gnsHilbertSpace
  complete := fun X => ⟨cubeCauchyLimit w hw X, X.converges⟩

end YMGap.Continuum.BF4PhysicalCubeCompletion

#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.embedSpan
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.completedInner
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.completedInner_embedSpan
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.completedBasis_inner
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.completedBasis_inner_at_cutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.completedRoot_ne_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.finiteApproximation
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.finiteApproximation_close
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.cubeCauchyLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.cubeCauchyLimit_seq
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.cubeCauchyLimit_modulus
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletion.cubeCompleteHilbert
