/-
# Exact finite chain contraction with one middle insertion

An insertion after m chronological slices is retained while those slices
are integrated, and is then multiplied into the actual message before the
remaining n steps. The chain still contains exactly m+n+1 spatial weights;
in particular, its middle spatial weight is not duplicated or divided out.

This is a signed rational Haar/Fubini identity for the existing ordered
chain and step. The underlying pairing lemmas need no support assumptions.
Original geometric placement still requires its separate support and face
guards. No kernel symmetry, positivity, normalization, stationary state,
completion, OS identification or physical gap is asserted here.
-/

import YMGap.Continuum.SU2QuaternionHeadChainComposition

namespace YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal

local infix:50 " ≈ " => Q'.eqv

/-- Two successive chronological lifts are one literal combined lift. -/
theorem liftBoundary_add (a b : Nat) (p : RatPoly) :
    liftBoundary (a+b) p = liftBoundary a (liftBoundary b p) := by
  induction a with
  | zero => simp only [Nat.zero_add, liftBoundary]
  | succ a ih => simp only [Nat.succ_add, liftBoundary, ih]

private theorem mul_swap_left (a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul b c)) (polyMul b (polyMul a c)) :=
  (RatPolyCoeffEqv.mul_assoc a b c).symm.trans
    (((RatPolyCoeffEqv.mul_comm a b).mul_right c).trans
      (RatPolyCoeffEqv.mul_assoc b a c))

/-- Move the retained probe past the first kernel and spatial weight, but
leave its product with the entire remaining chain inside the same lift. -/
private theorem middle_reorder (f p kernel weight tail : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul f p) (polyMul kernel (polyMul weight tail)))
      (polyMul f (polyMul kernel (polyMul weight (polyMul p tail)))) :=
  (RatPolyCoeffEqv.mul_assoc f p (polyMul kernel (polyMul weight tail))).trans
    (((mul_swap_left p kernel (polyMul weight tail)).mul_left f).trans
      (((mul_swap_left p weight tail).mul_left kernel).mul_left f))

/-- Exact finite middle-insertion contraction. The first m steps act on f;
the middle probe p is multiplied into that retained message; the remaining
n steps then act on the product. The last spatial weight stays explicit.
No positivity, symmetry, normalization or extra integration premise is used. -/
theorem chain_middle_pairing (blocks : Nat) (kernel weight : RatPoly)
    (m n : Nat) (f p g : RatPoly) :
    quaternionHaar ((m+n+1)*blocks)
        (polyMul (polyMul f (liftBoundary (m*blocks) p))
          (chain blocks kernel weight (m+n) g)) ≈
      quaternionHaar blocks
        (polyMul
          (iterateStep blocks kernel weight n
            (polyMul (iterateStep blocks kernel weight m f) p))
          (polyMul weight g)) := by
  induction m generalizing f with
  | zero =>
      simpa only [Nat.zero_mul, Nat.zero_add, liftBoundary, iterateStep] using
        (chain_pairing blocks kernel weight n (polyMul f p) g)
  | succ m ih =>
      let probe := liftBoundary (m*blocks) p
      let tail := chain blocks kernel weight (m+n) g
      have hcount : m+1+n = (m+n)+1 := by omega
      have hoffset : (m+1)*blocks = blocks+m*blocks := by
        simp only [Nat.succ_mul]
        omega
      have hsize : (m+1+n+1)*blocks = (m+n+1)*blocks+blocks := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hsource : RatPolyCoeffEqv
          (polyMul (polyMul f (liftBoundary ((m+1)*blocks) p))
            (chain blocks kernel weight (m+1+n) g))
          (polyMul f (polyMul kernel
            (polyMul weight (liftBoundary blocks (polyMul probe tail))))) := by
        rw [hcount, chain, hoffset, liftBoundary_add, lift_product]
        exact middle_reorder f (liftBoundary blocks probe) kernel weight
          (liftBoundary blocks tail)
      have hstep := chain_step_pairing ((m+n+1)*blocks) blocks
        kernel weight f (polyMul probe tail)
      have hafter := haar_of_coeff
        (blocks := (m+n+1)*blocks)
        (RatPolyCoeffEqv.mul_assoc (step blocks kernel weight f) probe tail).symm
      rw [hsize]
      exact Q'.eqv_trans _ _ _ (haar_of_coeff hsource)
        (Q'.eqv_trans _ _ _ hstep
          (Q'.eqv_trans _ _ _ hafter (ih (step blocks kernel weight f))))

end YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion

#print axioms YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion.liftBoundary_add
#print axioms YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion.chain_middle_pairing
