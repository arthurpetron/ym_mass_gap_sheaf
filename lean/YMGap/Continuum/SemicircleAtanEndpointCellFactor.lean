/-
# Exact endpoint Darboux-cell factorization

For endpoint `1/k`, every existing `scaledCell` is exactly the uniform mesh
`2/(kn)` times the normalized kernel `1/(1+x_j^2)`.  This is the finite
interface needed before the genuine monomial power-sum limit.
-/

import YMGap.Continuum.SemicircleAtanEndpointSeriesKernel
import YMGap.Continuum.SemicircleAtanInducedPartition

namespace YMGap.Continuum.SemicircleAtanEndpointCellFactor

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanEndpointSeriesKernel

private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : (((1 : Q').den : Int)) = 1 := rfl

/-- The endpoint node used by the scaled cell at `1/k`. -/
def endpointNode (k n j : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  gridNode 1 k n j hk hn

/-- Clearing the kernel denominator from a scaled Darboux cell leaves exactly
the uniform endpoint mesh. -/
theorem scaledCell_mul_kernelDen_eqv_scaledMesh
    (k n j : Nat) (hk : 0 < k) (hn : 0 < n) :
    (scaledCell 1 k n j hk hn *
        ((1 : Q') + endpointNode k n j hk hn * endpointNode k n j hk hn)).eqv
      (scaledMesh 1 k n hk hn) := by
  show (scaledCell 1 k n j hk hn *
      ((1 : Q') + endpointNode k n j hk hn * endpointNode k n j hk hn)).num *
      ((scaledMesh 1 k n hk hn).den : Int) =
    (scaledMesh 1 k n hk hn).num *
      ((scaledCell 1 k n j hk hn *
        ((1 : Q') + endpointNode k n j hk hn * endpointNode k n j hk hn)).den : Int)
  unfold scaledCell scaledMesh scaledDen endpointNode gridNode
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    one_num, one_den]
  push_cast
  simp only [Int.mul_one, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- **Exact cell factorization.** -/
theorem scaledCell_eqv_mesh_mul_unitKernel
    (k n j : Nat) (hk : 0 < k) (hn : 0 < n) :
    (scaledCell 1 k n j hk hn).eqv
      (scaledMesh 1 k n hk hn * unitKernel (endpointNode k n j hk hn)) := by
  let x := endpointNode k n j hk hn
  let D := (1 : Q') + x*x
  have hD : (0 : Q') < D := kernelDen_pos x
  apply Q'.mul_left_cancel_of_pos hD
  have hleft : (D * scaledCell 1 k n j hk hn).eqv
      (scaledMesh 1 k n hk hn) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv D _) ?_
    exact scaledCell_mul_kernelDen_eqv_scaledMesh k n j hk hn
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left D _ _
      (Q'.mul_comm_eqv (scaledMesh 1 k n hk hn) (unitKernel x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv D (unitKernel x)
      (scaledMesh 1 k n hk hn))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (scaledMesh 1 k n hk hn)
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv D (unitKernel x))
        (unitKernel_mul_den x))) ?_
  exact Q'.one_mul_eqv (scaledMesh 1 k n hk hn)

end YMGap.Continuum.SemicircleAtanEndpointCellFactor

#print axioms YMGap.Continuum.SemicircleAtanEndpointCellFactor.scaledCell_mul_kernelDen_eqv_scaledMesh
#print axioms YMGap.Continuum.SemicircleAtanEndpointCellFactor.scaledCell_eqv_mesh_mul_unitKernel
