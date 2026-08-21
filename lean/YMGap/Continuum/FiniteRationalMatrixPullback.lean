/-
# Exact pullback of a finite rational matrix quadratic

For a full matrix `M` and a rational linear coordinate map `A`, this module
defines the reduced matrix `A^T M A` by literal finite sums.  It proves that
the complete reduced quadratic is exactly the full quadratic evaluated on the
lifted coefficient vector.  All rearrangements are finite rational Fubini and
distributivity identities checked in Lean.

This is generic finite algebra.  It constructs no centered coordinate map,
positive weight, LDL factor, physical gap, cutoff family, continuum theory,
or Clay conclusion.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate

namespace YMGap.Continuum.FiniteRationalMatrixPullback

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Apply a finite rational coordinate matrix to reduced coefficients. -/
def finiteLinearApply
    (reducedSize : Nat) (transform : Nat → Nat → Q')
    (coefficient : Nat → Q') (fullIndex : Nat) : Q' :=
  listQSum
    (fun reducedIndex =>
      coefficient reducedIndex * transform fullIndex reducedIndex)
    (List.range reducedSize)

/-- Literal entry of the pullback `A^T M A`. -/
def finiteMatrixPullback
    (fullSize : Nat) (matrix : Nat → Nat → Q')
    (transform : Nat → Nat → Q')
    (left right : Nat) : Q' :=
  listQSum
    (fun i => listQSum
      (fun j => matrix i j *
        (transform i left * transform j right))
      (List.range fullSize))
    (List.range fullSize)

private def pullbackTerm
    (matrix : Nat → Nat → Q')
    (transform : Nat → Nat → Q')
    (coefficient : Nat → Q')
    (left right i j : Nat) : Q' :=
  matrix i j *
    ((coefficient left * transform i left) *
      (coefficient right * transform j right))

/-- The quadratic of `A^T M A` is the quadratic of `M` on the explicit
linear lift `A coefficient`. -/
theorem finiteMatrixQuadratic_pullback
    (fullSize reducedSize : Nat)
    (matrix : Nat → Nat → Q')
    (transform : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic reducedSize
        (finiteMatrixPullback fullSize matrix transform) coefficient ≈
      finiteMatrixQuadratic fullSize matrix
        (finiteLinearApply reducedSize transform coefficient) := by
  let reduced := List.range reducedSize
  let full := List.range fullSize
  have hdistribute :
      finiteMatrixQuadratic reducedSize
          (finiteMatrixPullback fullSize matrix transform) coefficient ≈
        listQSum
          (fun left => listQSum
            (fun right => listQSum
              (fun i => listQSum
                (fun j =>
                  pullbackTerm matrix transform coefficient
                    left right i j)
                full)
              full)
            reduced)
          reduced := by
    unfold finiteMatrixQuadratic finiteMatrixPullback
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    let scalar := coefficient left * coefficient right
    refine Q'.eqv_trans _
      (listQSum
        (fun i => scalar * listQSum
          (fun j => matrix i j *
            (transform i left * transform j right))
          full)
        full) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_mul_left scalar
          (fun i => listQSum
            (fun j => matrix i j *
              (transform i left * transform j right))
            full)
          full)
    · apply listQSum_congr
      intro i
      refine Q'.eqv_trans _
        (listQSum
          (fun j => scalar *
            (matrix i j *
              (transform i left * transform j right)))
          full) _ ?_ ?_
      · exact Q'.eqv_symm
          (listQSum_mul_left scalar
            (fun j => matrix i j *
              (transform i left * transform j right))
            full)
      · apply listQSum_congr
        intro j
        exact mul6_rearrange
          (coefficient left) (coefficient right)
          (matrix i j) (transform i left) (transform j right)
  have hswapRightFull :
      listQSum
          (fun left => listQSum
            (fun right => listQSum
              (fun i => listQSum
                (fun j => pullbackTerm matrix transform coefficient
                  left right i j)
                full)
              full)
            reduced)
          reduced ≈
        listQSum
          (fun left => listQSum
            (fun i => listQSum
              (fun right => listQSum
                (fun j => pullbackTerm matrix transform coefficient
                  left right i j)
                full)
              reduced)
            full)
          reduced := by
    apply listQSum_congr
    intro left
    exact Q'.eqv_symm
      (listQSum_swap
        (fun right i => listQSum
          (fun j => pullbackTerm matrix transform coefficient
            left right i j)
          full)
        reduced full)
  have hswapLeftFull :
      listQSum
          (fun left => listQSum
            (fun i => listQSum
              (fun right => listQSum
                (fun j => pullbackTerm matrix transform coefficient
                  left right i j)
                full)
              reduced)
            full)
          reduced ≈
        listQSum
          (fun i => listQSum
            (fun left => listQSum
              (fun right => listQSum
                (fun j => pullbackTerm matrix transform coefficient
                  left right i j)
                full)
              reduced)
            reduced)
          full := by
    exact Q'.eqv_symm
      (listQSum_swap
        (fun left i => listQSum
          (fun right => listQSum
            (fun j => pullbackTerm matrix transform coefficient
              left right i j)
            full)
          reduced)
        reduced full)
  have hswapRightReduced :
      listQSum
          (fun i => listQSum
            (fun left => listQSum
              (fun right => listQSum
                (fun j => pullbackTerm matrix transform coefficient
                  left right i j)
                full)
              reduced)
            reduced)
          full ≈
        listQSum
          (fun i => listQSum
            (fun left => listQSum
              (fun j => listQSum
                (fun right => pullbackTerm matrix transform coefficient
                  left right i j)
                reduced)
              full)
            reduced)
          full := by
    apply listQSum_congr
    intro i
    apply listQSum_congr
    intro left
    exact Q'.eqv_symm
      (listQSum_swap
        (fun right j => pullbackTerm matrix transform coefficient
          left right i j)
        reduced full)
  have hswapLeftReduced :
      listQSum
          (fun i => listQSum
            (fun left => listQSum
              (fun j => listQSum
                (fun right => pullbackTerm matrix transform coefficient
                  left right i j)
                reduced)
              full)
            reduced)
          full ≈
        listQSum
          (fun i => listQSum
            (fun j => listQSum
              (fun left => listQSum
                (fun right => pullbackTerm matrix transform coefficient
                  left right i j)
                reduced)
              reduced)
            full)
          full := by
    apply listQSum_congr
    intro i
    exact Q'.eqv_symm
      (listQSum_swap
        (fun left j => listQSum
          (fun right => pullbackTerm matrix transform coefficient
            left right i j)
          reduced)
        reduced full)
  have hcollapse :
      listQSum
          (fun i => listQSum
            (fun j => listQSum
              (fun left => listQSum
                (fun right => pullbackTerm matrix transform coefficient
                  left right i j)
                reduced)
              reduced)
            full)
          full ≈
        finiteMatrixQuadratic fullSize matrix
          (finiteLinearApply reducedSize transform coefficient) := by
    unfold finiteMatrixQuadratic finiteLinearApply
    apply listQSum_congr
    intro i
    apply listQSum_congr
    intro j
    let leftValue := fun left =>
      coefficient left * transform i left
    let rightValue := fun right =>
      coefficient right * transform j right
    refine Q'.eqv_trans _
      (matrix i j *
        listQSum
          (fun left => listQSum
            (fun right => leftValue left * rightValue right)
            reduced)
          reduced) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun left => matrix i j *
            listQSum
              (fun right => leftValue left * rightValue right)
              reduced)
          reduced) _ ?_ ?_
      · apply listQSum_congr
        intro left
        exact listQSum_mul_left
          (matrix i j)
          (fun right => leftValue left * rightValue right)
          reduced
      · exact listQSum_mul_left
          (matrix i j)
          (fun left => listQSum
            (fun right => leftValue left * rightValue right)
            reduced)
          reduced
    · refine Q'.eqv_trans _
        (matrix i j *
          (listQSum leftValue reduced * listQSum rightValue reduced)) _
        (Q'.mul_eqv_congr_left (matrix i j) _ _
          (listQSum_product leftValue rightValue reduced reduced)) ?_
      exact Q'.mul_comm_eqv _ _
  exact Q'.eqv_trans _ _ _ hdistribute
    (Q'.eqv_trans _ _ _ hswapRightFull
      (Q'.eqv_trans _ _ _ hswapLeftFull
        (Q'.eqv_trans _ _ _ hswapRightReduced
          (Q'.eqv_trans _ _ _ hswapLeftReduced hcollapse))))

end YMGap.Continuum.FiniteRationalMatrixPullback

#print axioms
  YMGap.Continuum.FiniteRationalMatrixPullback.finiteMatrixQuadratic_pullback
