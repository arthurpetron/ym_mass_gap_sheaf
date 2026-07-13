/-
# Finite endpoint-series decomposition and geometric remainder envelope

Every rational endpoint Darboux sum is split exactly into the paired Machin
polynomial and its positive geometric remainder.  The remainder is bounded
uniformly in the mesh by

    (2/k) * ((1/k)^4)^N.

Thus the finite-algebra interface and the series-tail estimate are both
closed; only the finite polynomial power-sum limit remains.
-/

import YMGap.Continuum.SemicircleAtanEndpointCellFactor
import YMGap.Continuum.FusedAmplitudeDerivation

namespace YMGap.Continuum.SemicircleAtanEndpointSeriesSum

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanEndpointSeriesKernel
open YMGap.Continuum.SemicircleAtanEndpointCellFactor

/-- The polynomial part of one endpoint Darboux cell. -/
def endpointPairedTerm (k n j N : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  scaledMesh 1 k n hk hn * pairedKernel (endpointNode k n j hk hn) N

/-- The exact geometric remainder in one endpoint Darboux cell. -/
def endpointRemainderTerm (k n j N : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  scaledMesh 1 k n hk hn *
    (unitKernel (endpointNode k n j hk hn) *
      RGTransport.qpow (quartic (endpointNode k n j hk hn)) N)

def endpointPairedSum (k n N : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  finSum (fun j => endpointPairedTerm k n j N hk hn) n

def endpointRemainderSum (k n N : Nat) (hk : 0 < k) (hn : 0 < n) : Q' :=
  finSum (fun j => endpointRemainderTerm k n j N hk hn) n

/-- Pointwise exact decomposition of a Darboux cell. -/
theorem scaledCell_eqv_paired_add_remainder
    (k n j N : Nat) (hk : 0 < k) (hn : 0 < n) :
    (scaledCell 1 k n j hk hn).eqv
      (endpointPairedTerm k n j N hk hn +
        endpointRemainderTerm k n j N hk hn) := by
  let x := endpointNode k n j hk hn
  let mesh := scaledMesh 1 k n hk hn
  have hcell := scaledCell_eqv_mesh_mul_unitKernel k n j hk hn
  have hkernel := unitKernel_eq_paired_add_remainder x N
  refine Q'.eqv_trans _ _ _ hcell ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left mesh _ _ hkernel) ?_
  exact Q'.mul_add_eqv mesh (pairedKernel x N)
    (unitKernel x * RGTransport.qpow (quartic x) N)

/-- **Exact finite decomposition.** -/
theorem scaledLeftSum_eqv_paired_add_remainder
    (k n N : Nat) (hk : 0 < k) (hn : 0 < n) :
    (scaledLeftSum 1 k n hk hn).eqv
      (endpointPairedSum k n N hk hn +
        endpointRemainderSum k n N hk hn) := by
  unfold scaledLeftSum endpointPairedSum endpointRemainderSum
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _
      (fun j => scaledCell_eqv_paired_add_remainder k n j N hk hn) n) ?_
  exact finSum_add _ _ n

theorem endpointNode_le_endpoint
    (k n j : Nat) (hk : 0 < k) (hn : 0 < n) (hj : j ≤ n) :
    endpointNode k n j hk hn ≤ rat 1 k hk := by
  exact Q'.le_trans' _ _ _
    (gridNode_mono 1 k n j n hk hn hj)
    (Q'.le_of_eqv (gridNode_endpoint_eqv 1 k n hk hn))

theorem endpoint_rat_nonnegative (k : Nat) (hk : 0 < k) :
    (0 : Q') ≤ rat 1 k hk := by
  unfold rat
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
  decide

theorem quartic_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    quartic x ≤ quartic y := by
  have hy : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
  have hsquare : x*x ≤ y*y :=
    Q'.mul_le_mul_of_nonneg hxy hxy hy hx
  have hxx : (0 : Q') ≤ x*x := Q'.mul_nonneg _ _ hx hx
  have hyy : (0 : Q') ≤ y*y := Q'.mul_nonneg _ _ hy hy
  unfold quartic
  exact Q'.mul_le_mul_of_nonneg hsquare hsquare hyy hxx

theorem unitKernel_le_one (x : Q') : unitKernel x ≤ (1 : Q') := by
  apply Q'.divPos_le_of_le_mul 1 ((1 : Q') + x*x) (kernelDen_pos x)
  have hsquare : (0 : Q') ≤ x*x := SumOfSquares.q_mul_self_nonneg x
  have hden : (1 : Q') ≤ (1 : Q') + x*x :=
    Q'.add_le_self_of_nonneg _ _ hsquare
  exact Q'.le_trans' _ _ _ hden
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))

theorem scaledMesh_nonnegative
    (k n : Nat) (hk : 0 < k) (hn : 0 < n) :
    (0 : Q') ≤ scaledMesh 1 k n hk hn := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold scaledMesh
  rw [Q'.mkPos_num]
  decide

theorem endpointRemainderTerm_nonnegative
    (k n j N : Nat) (hk : 0 < k) (hn : 0 < n) :
    (0 : Q') ≤ endpointRemainderTerm k n j N hk hn := by
  let x := endpointNode k n j hk hn
  have hx : (0 : Q') ≤ x := gridNode_nonneg 1 k n j hk hn
  have hquartic : (0 : Q') ≤ quartic x := by
    unfold quartic
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hx hx) (Q'.mul_nonneg _ _ hx hx)
  have hunit : (0 : Q') ≤ unitKernel x :=
    Q'.le_of_lt (Q'.divPos_pos 1 _ (kernelDen_pos x) (by decide))
  unfold endpointRemainderTerm
  exact Q'.mul_nonneg _ _ (scaledMesh_nonnegative k n hk hn)
    (Q'.mul_nonneg _ _ hunit (RGTransport.qpow_nonneg _ hquartic N))

private theorem finSum_nonnegative (f : Nat → Q')
    (hf : ∀ j, (0 : Q') ≤ f j) : ∀ n, (0 : Q') ≤ finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => Q'.zero_le_add _ _ (finSum_nonnegative f hf n) (hf n)

theorem endpointRemainderSum_nonnegative
    (k n N : Nat) (hk : 0 < k) (hn : 0 < n) :
    (0 : Q') ≤ endpointRemainderSum k n N hk hn := by
  unfold endpointRemainderSum
  exact finSum_nonnegative _
    (fun j => endpointRemainderTerm_nonnegative k n j N hk hn) n

/-- The endpoint width `2/k`. -/
def endpointWidth (k : Nat) (hk : 0 < k) : Q' :=
  Q'.mkPos 2 k hk

/-- The quartic endpoint ratio `(1/k)^4`. -/
def endpointQuartic (k : Nat) (hk : 0 < k) : Q' :=
  quartic (rat 1 k hk)

theorem endpointRemainderTerm_le
    (k n j N : Nat) (hk : 0 < k) (hn : 0 < n) (hj : j < n) :
    endpointRemainderTerm k n j N hk hn ≤
      scaledMesh 1 k n hk hn *
        RGTransport.qpow (endpointQuartic k hk) N := by
  let x := endpointNode k n j hk hn
  let y := rat 1 k hk
  have hx : (0 : Q') ≤ x := gridNode_nonneg 1 k n j hk hn
  have hxy : x ≤ y := endpointNode_le_endpoint k n j hk hn (Nat.le_of_lt hj)
  have hquartic : quartic x ≤ quartic y := quartic_mono hx hxy
  have hxquartic : (0 : Q') ≤ quartic x := by
    unfold quartic
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hx hx) (Q'.mul_nonneg _ _ hx hx)
  have hpow : RGTransport.qpow (quartic x) N ≤
      RGTransport.qpow (quartic y) N :=
    qpow_mono hxquartic hquartic N
  have hpow0 : (0 : Q') ≤ RGTransport.qpow (quartic x) N :=
    RGTransport.qpow_nonneg _ hxquartic N
  have hunit : unitKernel x * RGTransport.qpow (quartic x) N ≤
      (1 : Q') * RGTransport.qpow (quartic x) N :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (unitKernel_le_one x) hpow0
  have hinner : unitKernel x * RGTransport.qpow (quartic x) N ≤
      RGTransport.qpow (quartic y) N :=
    Q'.le_trans' _ _ _ hunit
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hpow)
  unfold endpointRemainderTerm endpointQuartic
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hinner
    (scaledMesh_nonnegative k n hk hn)

theorem endpointWidth_eqv_count_mul_mesh
    (k n : Nat) (hk : 0 < k) (hn : 0 < n) :
    (Q'.ofNat n * scaledMesh 1 k n hk hn).eqv (endpointWidth k hk) := by
  show (Q'.ofNat n * scaledMesh 1 k n hk hn).num *
      ((endpointWidth k hk).den : Int) =
    (endpointWidth k hk).num *
      ((Q'.ofNat n * scaledMesh 1 k n hk hn).den : Int)
  unfold scaledMesh endpointWidth
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  simp only [Int.one_mul, Int.mul_assoc, Int.mul_comm]

private theorem finSum_le_const_on_range (f : Nat → Q') (c : Q') :
    ∀ n, (∀ j, j < n → f j ≤ c) →
      finSum f n ≤ finSum (fun _ => c) n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
      show finSum f n + f n ≤ finSum (fun _ => c) n + c
      exact Q'.add_le_add
        (finSum_le_const_on_range f c n
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n))))
        (h n (Nat.lt_succ_self n))

/-- **Uniform geometric remainder envelope.**  The mesh has disappeared from
the right side, so the bound is ready for the series cutoff `N → ∞`. -/
theorem endpointRemainderSum_le_geometric
    (k n N : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointRemainderSum k n N hk hn ≤
      endpointWidth k hk * RGTransport.qpow (endpointQuartic k hk) N := by
  unfold endpointRemainderSum
  have hsum := finSum_le_const_on_range
    (fun j => endpointRemainderTerm k n j N hk hn)
    (scaledMesh 1 k n hk hn *
      RGTransport.qpow (endpointQuartic k hk) N) n
    (fun j hj => endpointRemainderTerm_le k n j N hk hn hj)
  refine Q'.le_trans' _ _ _ hsum ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (SemicircleConvClosed.finSum_const_eqv
      (scaledMesh 1 k n hk hn *
        RGTransport.qpow (endpointQuartic k hk) N) n) ?_)
  refine Q'.eqv_trans _
    ((Q'.ofNat n * scaledMesh 1 k n hk hn) *
      RGTransport.qpow (endpointQuartic k hk) N) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (endpointWidth_eqv_count_mul_mesh k n hk hn)

theorem rgQpow_eqv_pow (q : Q') : ∀ N,
    (RGTransport.qpow q N).eqv (q ^ N)
  | 0 => Q'.eqv_refl 1
  | N + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ q (rgQpow_eqv_pow q N)) ?_
      exact Q'.mul_comm_eqv (q ^ N) q

theorem endpointQuartic_eqv_ratio (k : Nat) (hk : 0 < k) :
    (endpointQuartic k hk).eqv (Pi.ratio k hk) := by
  show (endpointQuartic k hk).num * ((Pi.ratio k hk).den : Int) =
    (Pi.ratio k hk).num * ((endpointQuartic k hk).den : Int)
  unfold endpointQuartic quartic rat Pi.ratio
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  simp only [Int.one_mul]
  simp only [Int.pow_succ, Int.pow_zero]
  ac_rfl

theorem endpointQuartic_nonnegative (k : Nat) (hk : 0 < k) :
    (0 : Q') ≤ endpointQuartic k hk := by
  have hrat := endpoint_rat_nonnegative k hk
  unfold endpointQuartic quartic
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ hrat hrat) (Q'.mul_nonneg _ _ hrat hrat)

theorem endpointQuartic_le_half {k : Nat} (hk : 2 ≤ k) :
    endpointQuartic k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) ≤
      HalfPow.half := by
  let hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (endpointQuartic_eqv_ratio k hk0))
    (Pi.ratio_le_half hk)

theorem endpointWidth_nonnegative (k : Nat) (hk : 0 < k) :
    (0 : Q') ≤ endpointWidth k hk := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold endpointWidth
  rw [Q'.mkPos_num]
  decide

theorem endpointWidth_le_one {k : Nat} (hk : 2 ≤ k) :
    endpointWidth k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) ≤ (1 : Q') := by
  let hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  show (endpointWidth k hk0).num * ((1 : Q').den : Int) ≤
    (1 : Q').num * ((endpointWidth k hk0).den : Int)
  unfold endpointWidth
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]
  change (2 : Int) ≤ (k : Int)
  exact_mod_cast hk

/-- Mesh-uniform harmonic envelope for the endpoint geometric remainder. -/
theorem endpointRemainderSum_le_invSucc
    {k : Nat} (hk : 2 ≤ k) (n N : Nat) (hn : 0 < n) :
    endpointRemainderSum k n N
        (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) hn ≤ Q'.invSucc N := by
  let hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  have htail := endpointRemainderSum_le_geometric k n N hk0 hn
  have hpow : RGTransport.qpow (endpointQuartic k hk0) N ≤
      RGTransport.qpow HalfPow.half N :=
    qpow_mono (endpointQuartic_nonnegative k hk0)
      (endpointQuartic_le_half hk) N
  have hprod : endpointWidth k hk0 *
        RGTransport.qpow (endpointQuartic k hk0) N ≤
      (1 : Q') * RGTransport.qpow HalfPow.half N :=
    Q'.mul_le_mul_of_nonneg (endpointWidth_le_one hk) hpow
      Q'.zero_le_one
      (RGTransport.qpow_nonneg _ (endpointQuartic_nonnegative k hk0) N)
  refine Q'.le_trans' _ _ _ htail (Q'.le_trans' _ _ _ hprod ?_)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (rgQpow_eqv_pow HalfPow.half N)) ?_
  exact HalfPow.pow_half_le_invSucc N

/-- Explicit target modulus: cutoff `N = epsilon.den` makes the endpoint
remainder at every positive mesh resolution at most `epsilon`. -/
theorem endpointRemainderSum_le_target
    {k : Nat} (hk : 2 ≤ k) (n : Nat) (hn : 0 < n)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    endpointRemainderSum k n epsilon.den
        (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) hn ≤ epsilon := by
  exact Q'.le_trans' _ _ _
    (endpointRemainderSum_le_invSucc hk n epsilon.den hn)
    (HalfPow.invSucc_den_le epsilon hepsilon)

#print axioms endpointPairedTerm
#print axioms endpointRemainderTerm
#print axioms scaledCell_eqv_paired_add_remainder
#print axioms scaledLeftSum_eqv_paired_add_remainder
#print axioms endpointNode_le_endpoint
#print axioms quartic_mono
#print axioms unitKernel_le_one
#print axioms endpointRemainderTerm_nonnegative
#print axioms endpointRemainderSum_nonnegative
#print axioms endpointWidth_eqv_count_mul_mesh
#print axioms endpointRemainderSum_le_geometric
#print axioms rgQpow_eqv_pow
#print axioms endpointQuartic_eqv_ratio
#print axioms endpointQuartic_le_half
#print axioms endpointWidth_le_one
#print axioms endpointRemainderSum_le_invSucc
#print axioms endpointRemainderSum_le_target

end YMGap.Continuum.SemicircleAtanEndpointSeriesSum
