/-
# First-pair Casimir on the invariant trilinear pairing

This module regroups the fourfold invariant Hilbert--Schmidt contraction into
first-pair tensor-binomial slices.  Pair-exchange self-adjointness then holds
slice by slice, and the pointwise left-channel eigenvalue theorem lifts to an
exact all-label pairing identity.
-/

import YMGap.Continuum.SU2OrderedLeftCasimirEigen

namespace YMGap.Continuum.SU2OrderedLeftCasimirPairing

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantRowNormConstancy
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2OrderedLeftCasimirEigen

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

/-- One fixed third-input/output slice of the invariant pairing, with the
first two legs retained as the tensor-binomial pair. -/
def triMapFirstPairSlice (_a _b _c _d l s : Nat)
    (L R : BForm → BForm → BForm → BForm) : Q' :=
  tensorBinomPair _a _b
    (fun i j => L (mono i) (mono j) (mono l) s)
    (fun i j => R (mono i) (mono j) (mono l) s)

def triMapFirstPairSliceSum (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) : Q' :=
  finSum (fun l => finSum (fun s =>
    (tvBinomQ c l * symMonomialNormSq d s) *
      triMapFirstPairSlice a b c d l s L R) (d + 1)) (c + 1)

private theorem factor_first_pair_slice (a b c d l s : Nat)
    (L R : BForm → BForm → BForm → BForm) :
    finSum (fun i => finSum (fun j =>
      tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
        symMonomialNormSq d s *
          (L (mono i) (mono j) (mono l) s *
            R (mono i) (mono j) (mono l) s)) (b + 1)) (a + 1) ≈
      (tvBinomQ c l * symMonomialNormSq d s) *
        triMapFirstPairSlice a b c d l s L R := by
  let K : Q' := tvBinomQ c l * symMonomialNormSq d s
  let U : Nat → Nat → Q' := fun i j =>
    tvBinomQ b j * (tvBinomQ a i *
      (L (mono i) (mono j) (mono l) s *
        R (mono i) (mono j) (mono l) s))
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun j => K * U i j) (b + 1)) (a + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
    dsimp only [K, U]
    ring_qeqv
  · refine Q'.eqv_trans _
      (finSum (fun i => K * finSum (fun j => U i j) (b + 1)) (a + 1)) _ ?_ ?_
    · refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
      exact Q'.eqv_symm (const_mul_finSum (fun j => U i j) K (b + 1))
    · refine Q'.eqv_trans _
        (K * finSum (fun i => finSum (fun j => U i j) (b + 1)) (a + 1)) _
        (Q'.eqv_symm (const_mul_finSum
          (fun i => finSum (fun j => U i j) (b + 1)) K (a + 1))) ?_
      simp only [triMapFirstPairSlice, tensorBinomPair, K, U]
      exact Q'.eqv_refl _

/-- The original fourfold invariant pairing is exactly the sum of its
first-pair tensor-binomial slices. -/
theorem triMapInner_eq_firstPairSliceSum (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d L R ≈ triMapFirstPairSliceSum a b c d L R := by
  unfold triMapInner triMapFirstPairSliceSum
  let T : Nat → Nat → Nat → Nat → Q' := fun i j l s =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s *
        (L (mono i) (mono j) (mono l) s *
          R (mono i) (mono j) (mono l) s)
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun j => finSum (fun l => finSum (fun s =>
      T i j l s) (d + 1)) (c + 1)) (b + 1)) (a + 1)) _ (by rfl) ?_
  have hJL :
      finSum (fun i => finSum (fun j => finSum (fun l => finSum (fun s =>
          T i j l s) (d + 1)) (c + 1)) (b + 1)) (a + 1) ≈
        finSum (fun i => finSum (fun l => finSum (fun j => finSum (fun s =>
          T i j l s) (d + 1)) (b + 1)) (c + 1)) (a + 1) := by
    refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    exact finSum_swap
      (fun j l => finSum (fun s => T i j l s) (d + 1)) (b + 1) (c + 1)
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun l => finSum (fun j => finSum (fun s =>
      T i j l s) (d + 1)) (b + 1)) (c + 1)) (a + 1)) _ hJL ?_
  have hIL := finSum_swap
    (fun i l => finSum (fun j => finSum (fun s => T i j l s) (d + 1))
      (b + 1)) (a + 1) (c + 1)
  refine Q'.eqv_trans _
    (finSum (fun l => finSum (fun i => finSum (fun j => finSum (fun s =>
      T i j l s) (d + 1)) (b + 1)) (a + 1)) (c + 1)) _ hIL ?_
  have hJS :
      finSum (fun l => finSum (fun i => finSum (fun j => finSum (fun s =>
          T i j l s) (d + 1)) (b + 1)) (a + 1)) (c + 1) ≈
        finSum (fun l => finSum (fun i => finSum (fun s => finSum (fun j =>
          T i j l s) (b + 1)) (d + 1)) (a + 1)) (c + 1) := by
    refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
    refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
    exact finSum_swap (fun j s => T i j l s) (b + 1) (d + 1)
  refine Q'.eqv_trans _
    (finSum (fun l => finSum (fun i => finSum (fun s => finSum (fun j =>
      T i j l s) (b + 1)) (d + 1)) (a + 1)) (c + 1)) _ hJS ?_
  have hIS :
      finSum (fun l => finSum (fun i => finSum (fun s => finSum (fun j =>
          T i j l s) (b + 1)) (d + 1)) (a + 1)) (c + 1) ≈
        finSum (fun l => finSum (fun s => finSum (fun i => finSum (fun j =>
          T i j l s) (b + 1)) (a + 1)) (d + 1)) (c + 1) := by
    refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
    exact finSum_swap
      (fun i s => finSum (fun j => T i j l s) (b + 1)) (a + 1) (d + 1)
  refine Q'.eqv_trans _
    (finSum (fun l => finSum (fun s => finSum (fun i => finSum (fun j =>
      T i j l s) (b + 1)) (a + 1)) (d + 1)) (c + 1)) _ hIS ?_
  refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
  refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
  simpa only [T] using factor_first_pair_slice a b c d l s L R

/-- Symmetry of the invariant Hilbert--Schmidt pairing. -/
theorem triMapInner_symm (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d L R ≈ triMapInner a b c d R L := by
  refine Q'.eqv_trans _ (triMapFirstPairSliceSum a b c d L R) _
    (triMapInner_eq_firstPairSliceSum a b c d L R) ?_
  refine Q'.eqv_trans _ (triMapFirstPairSliceSum a b c d R L) _ ?_
    (Q'.eqv_symm (triMapInner_eq_firstPairSliceSum a b c d R L))
  unfold triMapFirstPairSliceSum triMapFirstPairSlice
  refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
  refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
  exact Q'.mul_eqv_congr_left _ _ _
    (tensorBinomPair_symm a b _ _)

/-- Pair exchange applied to the first factor, written in the regrouped
first-pair slices. -/
def triMapFirstPairExchangeInner (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) : Q' :=
  finSum (fun l => finSum (fun s =>
    (tvBinomQ c l * symMonomialNormSq d s) *
      tensorBinomPair a b
        (pairExchange a b
          (fun i j => L (mono i) (mono j) (mono l) s))
        (fun i j => R (mono i) (mono j) (mono l) s)) (d + 1)) (c + 1)

/-- Pair exchange is self-adjoint for the complete invariant trilinear
pairing, now on the first two input legs. -/
theorem triMapFirstPairExchange_self_adjoint (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) :
    triMapFirstPairExchangeInner a b c d L R ≈
      triMapFirstPairExchangeInner a b c d R L := by
  unfold triMapFirstPairExchangeInner
  refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
  refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
    (pairExchange_self_adjoint a b
      (fun i j => L (mono i) (mono j) (mono l) s)
      (fun i j => R (mono i) (mono j) (mono l) s))
    (tensorBinomPair_symm a b
      (fun i j => L (mono i) (mono j) (mono l) s)
      (pairExchange a b
        (fun i j => R (mono i) (mono j) (mono l) s))))

private theorem tensorBinomPair_congr_left (m n : Nat)
    (f f' g : Nat → Nat → Q')
    (h : ∀ i, i < m + 1 → ∀ j, j < n + 1 → f i j ≈ f' i j) :
    tensorBinomPair m n f g ≈ tensorBinomPair m n f' g := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (h i hi j hj)))

private theorem tensorBinomPair_scale_left (m n : Nat) (A : Q')
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n (fun i j => A * f i j) g ≈
      A * tensorBinomPair m n f g := by
  unfold tensorBinomPair
  refine Q'.eqv_trans _
    (finSum (fun i => A * finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j))) (n + 1))
      (m + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
    refine Q'.eqv_trans _
      (finSum (fun j => A * (tvBinomQ n j *
        (tvBinomQ m i * (f i j * g i j)))) (n + 1)) _ ?_ ?_
    · refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
      ring_qeqv
    · exact Q'.eqv_symm (const_mul_finSum _ A (n + 1))
  · exact Q'.eqv_symm (const_mul_finSum _ A (m + 1))

private theorem firstPairSlice_left_eigen {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d)
    (R : BForm → BForm → BForm → BForm) (l s : Nat) :
    tensorBinomPair a b
        (pairExchange a b (fun i j =>
          triLeft a b c d q.intermediate
            (mono i) (mono j) (mono l) s))
        (fun i j => R (mono i) (mono j) (mono l) s) ≈
      (-pairEigenvalue a b q.k) *
        triMapFirstPairSlice a b c d l s
          (triLeft a b c d q.intermediate) R := by
  let F : Nat → Nat → Q' := fun i j =>
    triLeft a b c d q.intermediate (mono i) (mono j) (mono l) s
  let G : Nat → Nat → Q' := fun i j =>
    R (mono i) (mono j) (mono l) s
  have hcongr := tensorBinomPair_congr_left a b
    (pairExchange a b F)
    (fun i j => (-pairEigenvalue a b q.k) * F i j) G (by
      intro i hi j hj
      have h := fixedLeftCoefficient_pairExchange_eigen q i j l s
        (by omega) (by omega)
      exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm (Q'.neg_mul_eqv _ _)))
  refine Q'.eqv_trans _
    (tensorBinomPair a b
      (fun i j => (-pairEigenvalue a b q.k) * F i j) G) _
    (by simpa only [F, G] using hcongr) ?_
  simpa only [triMapFirstPairSlice, F, G] using
    tensorBinomPair_scale_left a b (-pairEigenvalue a b q.k) F G

private theorem weighted_double_sum_scale
    (C : Q') (N M : Nat) (K P : Nat → Nat → Q') :
    finSum (fun i => finSum (fun s => K i s * (C * P i s)) M) N ≈
      C * finSum (fun i => finSum (fun s => K i s * P i s) M) N := by
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun s => C * (K i s * P i s)) M) N) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ N (fun i hi => ?_)
    refine finSum_eqv_congr_lt _ _ M (fun s hs => ?_)
    ring_qeqv
  refine Q'.eqv_trans _
    (finSum (fun i => C * finSum (fun s => K i s * P i s) M) N) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ N (fun i hi => ?_)
    exact Q'.eqv_symm (const_mul_finSum _ C M)
  exact Q'.eqv_symm (const_mul_finSum _ C N)

/-- The complete first-pair exchange pairing against a physical left channel
is multiplication by its exact Casimir eigenvalue. -/
theorem triMapFirstPairExchange_left_eigen {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d)
    (R : BForm → BForm → BForm → BForm) :
    triMapFirstPairExchangeInner a b c d
        (triLeft a b c d q.intermediate) R ≈
      (-pairEigenvalue a b q.k) *
        triMapInner a b c d (triLeft a b c d q.intermediate) R := by
  let K : Nat → Nat → Q' := fun l s =>
    tvBinomQ c l * symMonomialNormSq d s
  let P : Nat → Nat → Q' := fun l s =>
    triMapFirstPairSlice a b c d l s
      (triLeft a b c d q.intermediate) R
  unfold triMapFirstPairExchangeInner
  refine Q'.eqv_trans _
    (finSum (fun l => finSum (fun s =>
      K l s * ((-pairEigenvalue a b q.k) * P l s)) (d + 1)) (c + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
    refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
    exact Q'.mul_eqv_congr_left _ _ _ (by
      simpa only [P] using firstPairSlice_left_eigen q R l s)
  · have hscale := weighted_double_sum_scale (-pairEigenvalue a b q.k)
      (c + 1) (d + 1) K P
    refine Q'.eqv_trans _
      ((-pairEigenvalue a b q.k) *
        finSum (fun l => finSum (fun s => K l s * P l s)
          (d + 1)) (c + 1)) _ hscale ?_
    change ((-pairEigenvalue a b q.k) *
        triMapFirstPairSliceSum a b c d
          (triLeft a b c d q.intermediate) R) ≈ _
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (triMapInner_eq_firstPairSliceSum a b c d
        (triLeft a b c d q.intermediate) R))

/-- Equivalently, applying first-pair exchange to an arbitrary right factor
and pairing against a physical left channel gives the same left Casimir
eigenvalue.  This is the exact interface consumed by the right-basis
tridiagonal action. -/
theorem triMapFirstPairExchange_right_against_left_eigen {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d)
    (R : BForm → BForm → BForm → BForm) :
    triMapFirstPairExchangeInner a b c d R
        (triLeft a b c d q.intermediate) ≈
      (-pairEigenvalue a b q.k) *
        triMapInner a b c d R (triLeft a b c d q.intermediate) := by
  refine Q'.eqv_trans _
    (triMapFirstPairExchangeInner a b c d
      (triLeft a b c d q.intermediate) R) _
    (triMapFirstPairExchange_self_adjoint a b c d R
      (triLeft a b c d q.intermediate)) ?_
  refine Q'.eqv_trans _
    ((-pairEigenvalue a b q.k) *
      triMapInner a b c d (triLeft a b c d q.intermediate) R) _
    (triMapFirstPairExchange_left_eigen q R) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (triMapInner_symm a b c d (triLeft a b c d q.intermediate) R)

end YMGap.Continuum.SU2OrderedLeftCasimirPairing

#print axioms YMGap.Continuum.SU2OrderedLeftCasimirPairing.triMapInner_eq_firstPairSliceSum
#print axioms YMGap.Continuum.SU2OrderedLeftCasimirPairing.triMapInner_symm
#print axioms YMGap.Continuum.SU2OrderedLeftCasimirPairing.triMapFirstPairExchange_self_adjoint
#print axioms YMGap.Continuum.SU2OrderedLeftCasimirPairing.triMapFirstPairExchange_left_eigen
#print axioms YMGap.Continuum.SU2OrderedLeftCasimirPairing.triMapFirstPairExchange_right_against_left_eigen
