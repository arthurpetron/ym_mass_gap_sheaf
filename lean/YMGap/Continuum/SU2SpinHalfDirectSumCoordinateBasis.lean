/-
# The corrected simultaneous Clebsch--Gordan basis for two spin halves

Separate right inverses for individual transvectants interfere.  At the first
nontrivial label, however, the interference can be removed exactly: symmetric
and antisymmetric combinations of the two middle tensor monomials give three
order-zero coordinates and one order-one coordinate with no cross-channel
leakage.  This is the finite pilot for the general triangular/Hahn elimination.

All coefficients are derived exact rationals.  The four source reconstruction
identities prove that the displayed vectors are a basis of the complete
bidegree-(1,1) tensor window, not merely four convenient test vectors.
-/

import YMGap.Continuum.SU2TransvectantLocalSectionInterferenceFence

namespace YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity

private def half : Q' := Q'.mkPos 1 2 (by decide)

/-- Lowest, middle, and highest symmetric vectors in `V_1/2 tensor V_1/2`. -/
def tripletLow : BForm2 := mono2 0 0

def tripletMid : BForm2 :=
  bscale half (badd (mono2 0 1) (mono2 1 0))

def tripletHigh : BForm2 := mono2 1 1

/-- The corrected antisymmetric scalar section.  Unlike the independently
assembled local section, this vector is killed by the order-zero channel. -/
def singlet : BForm2 :=
  bscale half (badd (mono2 1 0) (bscale (-1) (mono2 0 1)))

/-! ## Simultaneous channel separation -/

theorem tripletLow_orderZero :
    FormEqv 3 (transvect 1 1 0 tripletLow) (mono 0) := by decide

theorem tripletMid_orderZero :
    FormEqv 3 (transvect 1 1 0 tripletMid) (mono 1) := by decide

theorem tripletHigh_orderZero :
    FormEqv 3 (transvect 1 1 0 tripletHigh) (mono 2) := by decide

theorem singlet_orderZero_kernel :
    FormEqv 3 (transvect 1 1 0 singlet) zeroF := by decide

theorem tripletLow_orderOne_kernel :
    FormEqv 1 (transvect 1 1 1 tripletLow) zeroF := by decide

theorem tripletMid_orderOne_kernel :
    FormEqv 1 (transvect 1 1 1 tripletMid) zeroF := by decide

theorem tripletHigh_orderOne_kernel :
    FormEqv 1 (transvect 1 1 1 tripletHigh) zeroF := by decide

theorem singlet_orderOne :
    FormEqv 1 (transvect 1 1 1 singlet) (mono 0) := by decide

/-! ## Full source-window reconstruction -/

theorem source00_reconstruct :
    FormEqv2 2 2 (mono2 0 0) tripletLow := by decide

theorem source01_reconstruct :
    FormEqv2 2 2 (mono2 0 1)
      (badd tripletMid (bscale (-1) singlet)) := by decide

theorem source10_reconstruct :
    FormEqv2 2 2 (mono2 1 0)
      (badd tripletMid singlet) := by decide

theorem source11_reconstruct :
    FormEqv2 2 2 (mono2 1 1) tripletHigh := by decide

/-- The four corrected vectors simultaneously give the full three-plus-one
Clebsch--Gordan coordinate table and reconstruct every source tensor monomial.
This packages the complete degree-(1,1) direct-sum pilot. -/
theorem spinHalf_directSum_coordinate_basis :
    (FormEqv 3 (transvect 1 1 0 tripletLow) (mono 0) ∧
     FormEqv 3 (transvect 1 1 0 tripletMid) (mono 1) ∧
     FormEqv 3 (transvect 1 1 0 tripletHigh) (mono 2) ∧
     FormEqv 3 (transvect 1 1 0 singlet) zeroF) ∧
    (FormEqv 1 (transvect 1 1 1 tripletLow) zeroF ∧
     FormEqv 1 (transvect 1 1 1 tripletMid) zeroF ∧
     FormEqv 1 (transvect 1 1 1 tripletHigh) zeroF ∧
     FormEqv 1 (transvect 1 1 1 singlet) (mono 0)) ∧
    (FormEqv2 2 2 (mono2 0 0) tripletLow ∧
     FormEqv2 2 2 (mono2 0 1) (badd tripletMid (bscale (-1) singlet)) ∧
     FormEqv2 2 2 (mono2 1 0) (badd tripletMid singlet) ∧
     FormEqv2 2 2 (mono2 1 1) tripletHigh) :=
  ⟨⟨tripletLow_orderZero, tripletMid_orderZero, tripletHigh_orderZero,
      singlet_orderZero_kernel⟩,
   ⟨tripletLow_orderOne_kernel, tripletMid_orderOne_kernel,
      tripletHigh_orderOne_kernel, singlet_orderOne⟩,
   ⟨source00_reconstruct, source01_reconstruct, source10_reconstruct,
      source11_reconstruct⟩⟩

end YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis

#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.tripletLow_orderZero
#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.tripletMid_orderZero
#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.tripletHigh_orderZero
#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.singlet_orderZero_kernel
#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.singlet_orderOne
#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.source01_reconstruct
#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.source10_reconstruct
#print axioms YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis.spinHalf_directSum_coordinate_basis
