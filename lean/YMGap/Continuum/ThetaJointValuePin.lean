/-
# Actual finite joint theta value at the endpoint

The signed box sum at y=1 equals the square of the ORIGINAL bareTheta,
with its central one and factor two. Signed reflection symmetrizes the
Chebyshev sum/difference kernel; no Euler-weighted product is substituted.
All rational w,x and N=0 are included. No infinite addition or jet-limit
identity is asserted here.
-/

import YMGap.Continuum.ThetaParityWeights
import YMGap.Continuum.FiniteJacobiSeriesComparison
import YMGap.Continuum.ChebyshevHalfShiftProduct
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.ThetaJointValuePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.ThetaParityWeights (thetaCell)
open YMGap.Continuum.FiniteJacobiSeriesComparison (bareTheta)
open YMGap.Continuum.ChebyshevHalfShiftProduct (natDist rotation_difference)
open YMGap.Continuum.ChebyshevEvenSOS (rotation_add)
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_add listQSum_mul_left)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_append listQSum_map listQSum_flatMap)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (h' : c ≈ d) :
    a+c ≈ b+d := QPoly.q_add_congr h h'

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (h' : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ h')

private theorem sum_singleton {A : Type} (f : A → Q') (a : A) :
    listQSum f [a] ≈ f a := QPoly.q_add_zero_eqv _

/-- Exact finite rational sum transport through a witnessed permutation. -/
theorem sum_perm {A : Type} (f : A → Q') {xs ys : List A}
    (h : xs.Perm ys) : listQSum f xs ≈ listQSum f ys := by
  induction h with
  | nil => exact Q'.eqv_refl 0
  | cons a _ ih => exact Q'.add_eqv_congr_left (f a) _ _ ih
  | swap a b xs =>
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2)))
        (by decide) (fun
          | 0 => f b
          | 1 => f a
          | _ => listQSum f xs)
  | trans _ _ ih ih' => exact Q'.eqv_trans _ _ _ ih ih'

private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro i hi j hj hij
      have hjN : j = N := List.mem_singleton.mp hj
      rw [hij, hjN] at hi
      exact (Nat.lt_irrefl N) (List.mem_range.mp hi)

private theorem signed_nodup (N : Nat) : (signedIndices N).Nodup :=
  TorusWilsonAction.nodup_map_on (fun i : Nat => (i : Int)-(N : Int))
    (fun i _ j _ he => by
      change (i : Int)-(N : Int) = (j : Int)-(N : Int) at he
      omega) (range_nodup (2*N+1))

/-- Actual two-endpoint increment permutation, used by bilateral series limits. -/
theorem signed_succ_perm (N : Nat) :
    (signedIndices (N+1)).Perm
      (-((N+1 : Nat) : Int) :: (signedIndices N ++ [((N+1 : Nat) : Int)])) := by
  apply TorusWilsonAction.perm_of_nodup_mem (signed_nodup (N+1))
  · apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hmid | hend
      · have hb := (signedIndices_mem N _).1 hmid
        omega
      · have he := List.mem_singleton.mp hend
        omega
    · apply List.nodup_append.mpr
      refine ⟨signed_nodup N, List.nodup_cons.mpr ⟨List.not_mem_nil,List.nodup_nil⟩, ?_⟩
      intro a ha b hb he
      have hab := (signedIndices_mem N a).1 ha
      have hbN := List.mem_singleton.mp hb
      omega
  · intro k
    constructor
    · intro hk
      have hb := (signedIndices_mem (N+1) k).1 hk
      by_cases hlo : k = -((N+1 : Nat) : Int)
      · exact List.mem_cons.mpr (Or.inl hlo)
      · apply List.mem_cons.mpr
        apply Or.inr
        by_cases hhi : k = ((N+1 : Nat) : Int)
        · exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hhi))
        · apply List.mem_append.mpr
          apply Or.inl
          apply (signedIndices_mem N k).2
          constructor <;> omega
    · intro hk
      apply (signedIndices_mem (N+1) k).2
      rcases List.mem_cons.mp hk with hlo | hrest
      · constructor <;> omega
      · rcases List.mem_append.mp hrest with hmid | hend
        · have hb := (signedIndices_mem N k).1 hmid
          constructor <;> omega
        · have he := List.mem_singleton.mp hend
          constructor <;> omega

/-- Constructive negation permutation of the literal bilateral interval. -/
theorem signed_neg_perm (N : Nat) :
    ((signedIndices N).map (fun k => -k)).Perm (signedIndices N) := by
  apply TorusWilsonAction.perm_of_nodup_mem
    (TorusWilsonAction.nodup_map_on (fun k : Int => -k)
      (fun a _ b _ he => by
        change -a = -b at he
        omega) (signed_nodup N)) (signed_nodup N)
  intro k
  constructor
  · intro hk
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hk
    have hb := (signedIndices_mem N j).1 hj
    apply (signedIndices_mem N k).2
    constructor <;> omega
  · intro hk
    have hb := (signedIndices_mem N k).1 hk
    exact List.mem_map.mpr ⟨-k,(signedIndices_mem N (-k)).2 (by
      constructor <;> omega), by omega⟩

private theorem signed_sum_neg (f : Int → Q') (N : Nat) :
    listQSum (fun k => f (-k)) (signedIndices N) ≈ listQSum f (signedIndices N) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (listQSum_map f (fun k : Int => -k) (signedIndices N)).symm)
    (sum_perm f (signed_neg_perm N))

/-- Literal signed Gaussian/Chebyshev coefficient of the original bare prefix. -/
def bareTerm (w x : Q') (k : Int) : Q' :=
  w^(k.natAbs*k.natAbs)*Cheb.T k.natAbs x

/-- The original bilateral signed prefix is exactly the original bareTheta. -/
theorem bareTheta_signed_pin (w x : Q') : ∀ N,
    listQSum (bareTerm w x) (signedIndices N) ≈ bareTheta w x N
  | 0 => QPoly.q_add_zero_eqv 1
  | N+1 => by
      have hneg : bareTerm w x (-((N+1 : Nat) : Int)) =
          w^((N+1)*(N+1))*Cheb.T (N+1) x := by
        simp only [bareTerm, Int.natAbs_neg]
        rfl
      have hp : listQSum (bareTerm w x) (signedIndices (N+1)) ≈
          (w^((N+1)*(N+1))*Cheb.T (N+1) x) +
            (bareTheta w x N + w^((N+1)*(N+1))*Cheb.T (N+1) x) := by
        refine Q'.eqv_trans _ _ _ (sum_perm (bareTerm w x) (signed_succ_perm N)) ?_
        change bareTerm w x (-((N+1 : Nat) : Int)) +
          listQSum (bareTerm w x) (signedIndices N ++ [((N+1 : Nat) : Int)]) ≈ _
        rw [hneg]
        exact add_congr (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (listQSum_append _ _ _)
            (add_congr (bareTheta_signed_pin w x N) (sum_singleton _ _)))
      exact Q'.eqv_trans _ _ _ hp (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.add (.var 2) (.mul (.var 0) (.var 1))))
        (.add (.var 2) (.mul (.mul (.const 2) (.var 0)) (.var 1)))
        (by decide) (fun
          | 0 => w^((N+1)*(N+1))
          | 1 => Cheb.T (N+1) x
          | _ => bareTheta w x N))

private theorem product_sum_nat (n m : Nat) (x : Q') :
    Cheb.T (n+m) x + Cheb.T (natDist n m) x ≈ 2*(Cheb.T n x*Cheb.T m x) :=
  Q'.eqv_trans _ _ _ (add_congr (rotation_add n m x).1 (rotation_difference n m x))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
      (.mul (.const 2) (.var 0)) (by decide) (fun
        | 0 => Cheb.T n x*Cheb.T m x
        | _ => (1 + -(x*x))*(ChebyshevEvenSOS.sinCoord n x*ChebyshevEvenSOS.sinCoord m x)))

private theorem signed_frequencies (m n : Int) :
    ((m+n).natAbs = m.natAbs+n.natAbs ∧ (m-n).natAbs = natDist m.natAbs n.natAbs) ∨
    ((m-n).natAbs = m.natAbs+n.natAbs ∧ (m+n).natAbs = natDist m.natAbs n.natAbs) := by
  have habs (j : Int) : (j.natAbs : Int) = j ∨ (j.natAbs : Int) = -j := by
    rcases Int.le_total 0 j with hj | hj
    · exact Or.inl (Int.natAbs_of_nonneg hj)
    · exact Or.inr (Int.ofNat_natAbs_of_nonpos hj)
  rcases habs m with hm | hm
  · rcases habs n with hn | hn
    · apply Or.inl
      constructor
      · rcases habs (m+n) with hs | hs <;> omega
      · rcases habs (m-n) with hd | hd <;> dsimp [natDist] <;> omega
    · apply Or.inr
      constructor
      · rcases habs (m-n) with hd | hd <;> omega
      · rcases habs (m+n) with hs | hs <;> dsimp [natDist] <;> omega
  · rcases habs n with hn | hn
    · apply Or.inr
      constructor
      · rcases habs (m-n) with hd | hd <;> omega
      · rcases habs (m+n) with hs | hs <;> dsimp [natDist] <;> omega
    · apply Or.inl
      constructor
      · rcases habs (m+n) with hs | hs <;> omega
      · rcases habs (m-n) with hd | hd <;> dsimp [natDist] <;> omega

/-- Actual signed-frequency product-to-sum identity for the finite numerator. -/
theorem product_sum_signed (m n : Int) (x : Q') :
    Cheb.T (m+n).natAbs x + Cheb.T (m-n).natAbs x ≈
      2*(Cheb.T m.natAbs x*Cheb.T n.natAbs x) := by
  rcases signed_frequencies m n with h | h
  · rw [h.1,h.2]
    exact product_sum_nat _ _ x
  · rw [h.1,h.2]
    exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (product_sum_nat _ _ x)

private def jointWeight (w x : Q') (z : SignedPair) : Q' :=
  w^(z.1.natAbs*z.1.natAbs+z.2.natAbs*z.2.natAbs)*Cheb.T (z.1+z.2).natAbs x

private theorem T_at_one : ∀ n, Cheb.T n 1 ≈ 1 ∧ Cheb.T (n+1) 1 ≈ 1
  | 0 => ⟨Q'.eqv_refl _,Q'.eqv_refl _⟩
  | n+1 => by
      have h := T_at_one n
      refine ⟨h.2,?_⟩
      rw [Cheb.T_succ_succ]
      exact Q'.eqv_trans _ _ _
        (add_congr (Q'.mul_eqv_congr_left _ _ _ h.2) (Q'.neg_eqv_congr _ _ h.1))
        (by decide : ((2 : Q')*1)*1 + -1 ≈ (1 : Q'))

/-- Actual joint box cell at the second-coordinate endpoint. -/
theorem cell_endpoint_pin (w x : Q') (z : SignedPair) :
    thetaCell w x 1 z ≈ jointWeight w x z :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (T_at_one (z.1-z.2).natAbs).1)
    (Q'.mul_one_eqv _)

private theorem joint_pair_pin (w x : Q') (m n : Int) :
    jointWeight w x (m,n) + jointWeight w x (m,-n) ≈
      2*(bareTerm w x m*bareTerm w x n) := by
  unfold jointWeight
  rw [Int.natAbs_neg, show m + -n = m-n by omega]
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (product_sum_signed m n x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.pow_add_eqv w _ _)) ?_
  exact poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.mul (.var 2) (.var 3))))
    (.mul (.const 2) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
    (by decide) (fun
      | 0 => w^(m.natAbs*m.natAbs)
      | 1 => w^(n.natAbs*n.natAbs)
      | 2 => Cheb.T m.natAbs x
      | _ => Cheb.T n.natAbs x)

private theorem box_nested (f : SignedPair → Q') (N : Nat) :
    listQSum f (boxIndices N) ≈
      listQSum (fun m => listQSum (fun n => f (m,n)) (signedIndices N)) (signedIndices N) := by
  refine Q'.eqv_trans _ _ _ (listQSum_flatMap f
    (fun m => (signedIndices N).map (fun n => (m,n))) (signedIndices N)) ?_
  exact listQSum_congr (fun m => Q'.eqv_of_eq (listQSum_map f (fun n => (m,n)) _)) _

/-- Exact second-coordinate reflection of a literal signed box sum. -/
theorem box_neg_sum (f : SignedPair → Q') (N : Nat) :
    listQSum (fun z : SignedPair => f (z.1,-z.2)) (boxIndices N) ≈ listQSum f (boxIndices N) :=
  Q'.eqv_trans _ _ _ (box_nested _ N)
    (Q'.eqv_trans _ _ _
      (listQSum_congr (fun m => signed_sum_neg (fun n => f (m,n)) N) _)
      (Q'.eqv_symm (box_nested f N)))

private theorem cancel_two {a b : Q'} (h : 2*a ≈ 2*b) : a ≈ b := by
  change (2*a.num)*(1*(b.den : Int)) = (2*b.num)*(1*(a.den : Int)) at h
  rw [Int.one_mul, Int.one_mul, Int.mul_assoc, Int.mul_assoc] at h
  change a.num*(b.den : Int) = b.num*(a.den : Int)
  omega

/-- Actual joint signed-box value at y=1 equals the square of the ORIGINAL
bareTheta, with no Euler coefficient or finite cutoff substitution. -/
theorem theta_box_endpoint_value_pin (w x : Q') (N : Nat) :
    listQSum (thetaCell w x 1) (boxIndices N) ≈ bareTheta w x N*bareTheta w x N := by
  let J := listQSum (jointWeight w x) (boxIndices N)
  let B := listQSum (bareTerm w x) (signedIndices N)
  have hd : J+J ≈ 2*(B*B) := by
    refine Q'.eqv_trans _ _ _ (add_congr (Q'.eqv_refl _)
      (Q'.eqv_symm (box_neg_sum (jointWeight w x) N))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_add (jointWeight w x)
      (fun z : SignedPair => jointWeight w x (z.1,-z.2)) (boxIndices N))) ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_congr (fun z : SignedPair => joint_pair_pin w x z.1 z.2) _) ?_
    refine Q'.eqv_trans _ _ _ (listQSum_mul_left 2
      (fun z : SignedPair => bareTerm w x z.1*bareTerm w x z.2) (boxIndices N)) ?_
    exact Q'.mul_eqv_congr_left 2 _ _
      (listQSum_cartesian_product (bareTerm w x) (bareTerm w x) _ _)
  have hJ : J ≈ B*B := cancel_two (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (poly_identity_of_normal_eq
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) (by decide) (fun _ => J))) hd)
  exact Q'.eqv_trans _ _ _ (listQSum_congr (cell_endpoint_pin w x) _)
    (Q'.eqv_trans _ _ _ hJ (mul_congr (bareTheta_signed_pin w x N) (bareTheta_signed_pin w x N)))

end YMGap.Continuum.ThetaJointValuePin

#print axioms YMGap.Continuum.ThetaJointValuePin.bareTerm
#print axioms YMGap.Continuum.ThetaJointValuePin.sum_perm
#print axioms YMGap.Continuum.ThetaJointValuePin.signed_succ_perm
#print axioms YMGap.Continuum.ThetaJointValuePin.signed_neg_perm
#print axioms YMGap.Continuum.ThetaJointValuePin.product_sum_signed
#print axioms YMGap.Continuum.ThetaJointValuePin.box_neg_sum
#print axioms YMGap.Continuum.ThetaJointValuePin.cell_endpoint_pin
#print axioms YMGap.Continuum.ThetaJointValuePin.bareTheta_signed_pin
#print axioms YMGap.Continuum.ThetaJointValuePin.theta_box_endpoint_value_pin
