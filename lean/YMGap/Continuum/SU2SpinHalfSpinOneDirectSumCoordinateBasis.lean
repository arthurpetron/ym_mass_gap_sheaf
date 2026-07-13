/-
# Simultaneous CG coordinates for spin one-half tensor spin one

The first corrected direct-sum pilot is extended from bidegree `(1,1)` to
`(1,2)`.  Exact thirds separate the four order-zero coordinates (spin 3/2)
from the two order-one coordinates (spin 1/2).  The six inverse identities
reconstruct the entire source tensor window and expose the first denominator
pattern that the general Hahn elimination must explain.
-/

import YMGap.Continuum.SU2SpinHalfDirectSumCoordinateBasis

namespace YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity

private def third : Q' := Q'.mkPos 1 3 (by decide)
private def twoThirds : Q' := Q'.mkPos 2 3 (by decide)

def quartet0 : BForm2 := mono2 0 0

def quartet1 : BForm2 :=
  badd (bscale twoThirds (mono2 0 1)) (bscale third (mono2 1 0))

def quartet2 : BForm2 :=
  badd (bscale third (mono2 0 2)) (bscale twoThirds (mono2 1 1))

def quartet3 : BForm2 := mono2 1 2

def doublet0 : BForm2 :=
  badd (bscale (-third) (mono2 0 1)) (bscale third (mono2 1 0))

def doublet1 : BForm2 :=
  badd (bscale (-third) (mono2 0 2)) (bscale third (mono2 1 1))

/-! ## Leakage-free channel table -/

theorem quartet0_orderZero :
    FormEqv 4 (transvect 1 2 0 quartet0) (mono 0) := by decide

theorem quartet1_orderZero :
    FormEqv 4 (transvect 1 2 0 quartet1) (mono 1) := by decide

theorem quartet2_orderZero :
    FormEqv 4 (transvect 1 2 0 quartet2) (mono 2) := by decide

theorem quartet3_orderZero :
    FormEqv 4 (transvect 1 2 0 quartet3) (mono 3) := by decide

theorem doublet0_orderZero_kernel :
    FormEqv 4 (transvect 1 2 0 doublet0) zeroF := by decide

theorem doublet1_orderZero_kernel :
    FormEqv 4 (transvect 1 2 0 doublet1) zeroF := by decide

theorem quartet0_orderOne_kernel :
    FormEqv 2 (transvect 1 2 1 quartet0) zeroF := by decide

theorem quartet1_orderOne_kernel :
    FormEqv 2 (transvect 1 2 1 quartet1) zeroF := by decide

theorem quartet2_orderOne_kernel :
    FormEqv 2 (transvect 1 2 1 quartet2) zeroF := by decide

theorem quartet3_orderOne_kernel :
    FormEqv 2 (transvect 1 2 1 quartet3) zeroF := by decide

theorem doublet0_orderOne :
    FormEqv 2 (transvect 1 2 1 doublet0) (mono 0) := by decide

theorem doublet1_orderOne :
    FormEqv 2 (transvect 1 2 1 doublet1) (mono 1) := by decide

/-! ## Reconstruction of the six source monomials -/

theorem source00_reconstruct :
    FormEqv2 2 3 (mono2 0 0) quartet0 := by decide

theorem source01_reconstruct :
    FormEqv2 2 3 (mono2 0 1)
      (badd quartet1 (bscale (-1) doublet0)) := by decide

theorem source10_reconstruct :
    FormEqv2 2 3 (mono2 1 0)
      (badd quartet1 (bscale 2 doublet0)) := by decide

theorem source02_reconstruct :
    FormEqv2 2 3 (mono2 0 2)
      (badd quartet2 (bscale (-2) doublet1)) := by decide

theorem source11_reconstruct :
    FormEqv2 2 3 (mono2 1 1)
      (badd quartet2 doublet1) := by decide

theorem source12_reconstruct :
    FormEqv2 2 3 (mono2 1 2) quartet3 := by decide

/-- Complete leakage-free `4+2` direct-sum coordinate basis for
`V_(1/2) tensor V_1`. -/
theorem spinHalf_spinOne_directSum_coordinate_basis :
    (FormEqv 4 (transvect 1 2 0 quartet0) (mono 0) ∧
     FormEqv 4 (transvect 1 2 0 quartet1) (mono 1) ∧
     FormEqv 4 (transvect 1 2 0 quartet2) (mono 2) ∧
     FormEqv 4 (transvect 1 2 0 quartet3) (mono 3) ∧
     FormEqv 4 (transvect 1 2 0 doublet0) zeroF ∧
     FormEqv 4 (transvect 1 2 0 doublet1) zeroF) ∧
    (FormEqv 2 (transvect 1 2 1 quartet0) zeroF ∧
     FormEqv 2 (transvect 1 2 1 quartet1) zeroF ∧
     FormEqv 2 (transvect 1 2 1 quartet2) zeroF ∧
     FormEqv 2 (transvect 1 2 1 quartet3) zeroF ∧
     FormEqv 2 (transvect 1 2 1 doublet0) (mono 0) ∧
     FormEqv 2 (transvect 1 2 1 doublet1) (mono 1)) ∧
    (FormEqv2 2 3 (mono2 0 0) quartet0 ∧
     FormEqv2 2 3 (mono2 0 1) (badd quartet1 (bscale (-1) doublet0)) ∧
     FormEqv2 2 3 (mono2 1 0) (badd quartet1 (bscale 2 doublet0)) ∧
     FormEqv2 2 3 (mono2 0 2) (badd quartet2 (bscale (-2) doublet1)) ∧
     FormEqv2 2 3 (mono2 1 1) (badd quartet2 doublet1) ∧
     FormEqv2 2 3 (mono2 1 2) quartet3) :=
  ⟨⟨quartet0_orderZero, quartet1_orderZero, quartet2_orderZero,
      quartet3_orderZero, doublet0_orderZero_kernel, doublet1_orderZero_kernel⟩,
   ⟨quartet0_orderOne_kernel, quartet1_orderOne_kernel,
      quartet2_orderOne_kernel, quartet3_orderOne_kernel,
      doublet0_orderOne, doublet1_orderOne⟩,
   ⟨source00_reconstruct, source01_reconstruct, source10_reconstruct,
      source02_reconstruct, source11_reconstruct, source12_reconstruct⟩⟩

end YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis

#print axioms YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis.quartet1_orderZero
#print axioms YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis.doublet0_orderZero_kernel
#print axioms YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis.doublet0_orderOne
#print axioms YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis.source01_reconstruct
#print axioms YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis.source10_reconstruct
#print axioms YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis.spinHalf_spinOne_directSum_coordinate_basis
