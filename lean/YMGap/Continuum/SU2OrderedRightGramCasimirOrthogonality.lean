/-
# Pair-Casimir proof of ordered right-channel Gram orthogonality

The last two input legs carry an exact discrete exchange Casimir.  It is the
cross-term in total raising after total lowering, hence is self-adjoint for
the tensor-binomial metric by the already proved raising/lowering adjointness.
The factorial Hahn carrier of contraction order `p` is an eigenvector with
eigenvalue `-p*(b+c-p+1)`.  These eigenvalues are distinct throughout the
physical Clebsch--Gordan window.  This separates arbitrary fixed-output right
channels without a finite-label computation.
-/

import YMGap.Continuum.SU2OrderedRightGramOrthogonality
import YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
import YMGap.Continuum.SU2TransvectantRowNormConstancy
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality

set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization
open YMGap.Continuum.SU2TransvectantRowNormConstancy
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. The exact pair exchange operator -/

/-- Total lowering on the two last monomial indices. -/
def pairLower (f : Nat → Nat → Q') (j l : Nat) : Q' :=
  Q'.ofNat j * f (j - 1) l + Q'.ofNat l * f j (l - 1)

/-- Total raising on bidegree `(b,c)`. -/
def pairRaise (b c : Nat) (f : Nat → Nat → Q')
    (j l : Nat) : Q' :=
  Q'.ofNat (b - j) * f (j + 1) l +
    Q'.ofNat (c - l) * f j (l + 1)

/-- The exchange part of the pair Casimir.  Both shifts preserve `j+l`. -/
def pairExchange (b c : Nat) (f : Nat → Nat → Q')
    (j l : Nat) : Q' :=
  (Q'.ofNat (b - j) * Q'.ofNat l) *
      (f (j + 1) (l - 1) + -f j l) +
    (Q'.ofNat j * Q'.ofNat (c - l)) *
      (f (j - 1) (l + 1) + -f j l)

/-- The diagonal removed from `raise ∘ lower` depends only on total weight. -/
def pairTotalScalar (b c j l : Nat) : Q' :=
  Q'.ofNat (b - j) * Q'.ofNat (j + 1) +
    Q'.ofNat (c - l) * Q'.ofNat (l + 1) +
    Q'.ofNat (b - j) * Q'.ofNat l +
    Q'.ofNat j * Q'.ofNat (c - l)

private def raiseLowerExchangeLHS : PolyExpr :=
  .add
    (.add
      (.mul (.var 0)
        (.add (.mul (.var 4) (.var 6)) (.mul (.var 3) (.var 7))))
      (.mul (.var 1)
        (.add (.mul (.var 2) (.var 8)) (.mul (.var 5) (.var 6)))))
    (.neg (.mul
      (.add
        (.add
          (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
          (.mul (.var 0) (.var 3)))
        (.mul (.var 2) (.var 1)))
      (.var 6)))

private def raiseLowerExchangeRHS : PolyExpr :=
  .add
    (.mul (.mul (.var 0) (.var 3))
      (.add (.var 7) (.neg (.var 6))))
    (.mul (.mul (.var 2) (.var 1))
      (.add (.var 8) (.neg (.var 6))))

private theorem raiseLowerExchange_normal :
    normalize raiseLowerExchangeLHS = normalize raiseLowerExchangeRHS := by
  decide

private theorem raiseLower_exchange_ring
    (A B J L JP LP X Y Z : Q') :
    A * (JP * X + L * Y) + B * (J * Z + LP * X) +
        -((A * JP + B * LP + A * L + J * B) * X) ≈
      (A * L) * (Y + -X) + (J * B) * (Z + -X) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then A else if r = 1 then B else if r = 2 then J else
    if r = 3 then L else if r = 4 then JP else if r = 5 then LP else
    if r = 6 then X else if r = 7 then Y else Z
  have h := poly_identity_of_normal_eq raiseLowerExchangeLHS
    raiseLowerExchangeRHS raiseLowerExchange_normal ρ
  simpa [raiseLowerExchangeLHS, raiseLowerExchangeRHS, eval, ρ] using h

/-- Pointwise algebraic identification of the exchange operator with total
raising after lowering minus the scalar total-weight part. -/
theorem pairRaise_pairLower_eq_exchange (b c : Nat)
    (f : Nat → Nat → Q') (j l : Nat) :
    pairRaise b c (pairLower f) j l +
        -(pairTotalScalar b c j l * f j l) ≈
      pairExchange b c f j l := by
  unfold pairRaise pairLower pairTotalScalar pairExchange
  simp only [Nat.add_sub_cancel]
  exact raiseLower_exchange_ring _ _ _ _ _ _ _ _ _

/-! ## 2. Self-adjointness from the existing raising/lowering adjoint -/

theorem tensorBinomPair_symm (m n : Nat) (f g : Nat → Nat → Q') :
    tensorBinomPair m n f g ≈ tensorBinomPair m n g f := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  ring_qeqv

theorem pairLower_adjoint_pairRaise (b c : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair b c (pairLower f) g ≈
      tensorBinomPair b c f (pairRaise b c g) := by
  simpa only [pairLower, pairRaise] using
    tensor_binomial_total_shift_adjoint b c f g

theorem pairRaise_adjoint_pairLower (b c : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair b c (pairRaise b c f) g ≈
      tensorBinomPair b c f (pairLower g) := by
  refine Q'.eqv_trans _ (tensorBinomPair b c g (pairRaise b c f)) _
    (tensorBinomPair_symm b c _ _) ?_
  refine Q'.eqv_trans _ (tensorBinomPair b c (pairLower g) f) _
    (Q'.eqv_symm (pairLower_adjoint_pairRaise b c g f)) ?_
  exact tensorBinomPair_symm b c _ _

theorem pairRaiseLower_self_adjoint (b c : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair b c (pairRaise b c (pairLower f)) g ≈
      tensorBinomPair b c f (pairRaise b c (pairLower g)) := by
  refine Q'.eqv_trans _
    (tensorBinomPair b c (pairLower f) (pairLower g)) _
    (pairRaise_adjoint_pairLower b c (pairLower f) g) ?_
  exact pairLower_adjoint_pairRaise b c f (pairLower g)

private theorem tensorBinomPair_congr_left' (m n : Nat)
    (f f' g : Nat → Nat → Q')
    (h : ∀ i, i < m + 1 → ∀ j, j < n + 1 → f i j ≈ f' i j) :
    tensorBinomPair m n f g ≈ tensorBinomPair m n f' g := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (h i hi j hj)))

private theorem tensorBinomPair_congr_right' (m n : Nat)
    (f g g' : Nat → Nat → Q')
    (h : ∀ i, i < m + 1 → ∀ j, j < n + 1 → g i j ≈ g' i j) :
    tensorBinomPair m n f g ≈ tensorBinomPair m n f g' := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (h i hi j hj)))

private theorem tensorBinomPair_add_left' (m n : Nat)
    (f h g : Nat → Nat → Q') :
    tensorBinomPair m n (fun i j => f i j + h i j) g ≈
      tensorBinomPair m n f g + tensorBinomPair m n h g := by
  unfold tensorBinomPair
  have houter := RationalTail.finSum_add
    (fun i => finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j))) (n + 1))
    (fun i => finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (h i j * g i j))) (n + 1)) (m + 1)
  refine Q'.eqv_trans _
    (finSum (fun i =>
      finSum (fun j => tvBinomQ n j *
        (tvBinomQ m i * (f i j * g i j))) (n + 1) +
      finSum (fun j => tvBinomQ n j *
        (tvBinomQ m i * (h i j * g i j))) (n + 1)) (m + 1)) _ ?_ houter
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine Q'.eqv_trans _
    (finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j)) +
      tvBinomQ n j * (tvBinomQ m i * (h i j * g i j))) (n + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
    ring_qeqv
  · exact RationalTail.finSum_add _ _ (n + 1)

private theorem tensorBinomPair_add_right' (m n : Nat)
    (f g h : Nat → Nat → Q') :
    tensorBinomPair m n f (fun i j => g i j + h i j) ≈
      tensorBinomPair m n f g + tensorBinomPair m n f h := by
  refine Q'.eqv_trans _
    (tensorBinomPair m n (fun i j => g i j + h i j) f) _
    (tensorBinomPair_symm m n _ _) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair m n g f + tensorBinomPair m n h f) _
    (tensorBinomPair_add_left' m n g h f) ?_
  exact Q'.add_eqv_congr'
    (tensorBinomPair_symm m n g f) (tensorBinomPair_symm m n h f)

private theorem tensorBinomPair_scale_left' (m n : Nat) (a : Q')
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n (fun i j => a * f i j) g ≈
      a * tensorBinomPair m n f g := by
  unfold tensorBinomPair
  refine Q'.eqv_trans _
    (finSum (fun i => a * finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j))) (n + 1))
      (m + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
    refine Q'.eqv_trans _
      (finSum (fun j => a * (tvBinomQ n j *
        (tvBinomQ m i * (f i j * g i j)))) (n + 1)) _ ?_ ?_
    · refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
      ring_qeqv
    · exact Q'.eqv_symm (const_mul_finSum _ a (n + 1))
  · exact Q'.eqv_symm (const_mul_finSum _ a (m + 1))

private theorem tensorBinomPair_scale_right' (m n : Nat) (a : Q')
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n f (fun i j => a * g i j) ≈
      a * tensorBinomPair m n f g := by
  refine Q'.eqv_trans _ (tensorBinomPair m n (fun i j => a * f i j) g) _
    ?_ (tensorBinomPair_scale_left' m n a f g)
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  ring_qeqv

private theorem pairTotalScalar_self_adjoint (b c : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair b c (fun j l => pairTotalScalar b c j l * f j l) g ≈
      tensorBinomPair b c f
        (fun j l => pairTotalScalar b c j l * g j l) := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
  refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
  ring_qeqv

private def pairExchangeViaRaiseLower (b c : Nat)
    (f : Nat → Nat → Q') (j l : Nat) : Q' :=
  pairRaise b c (pairLower f) j l +
    -(pairTotalScalar b c j l * f j l)

private theorem pairExchange_eq_viaRaiseLower (b c : Nat)
    (f : Nat → Nat → Q') (j l : Nat) :
    pairExchange b c f j l ≈ pairExchangeViaRaiseLower b c f j l :=
  Q'.eqv_symm (pairRaise_pairLower_eq_exchange b c f j l)

/-- The discrete last-pair exchange Casimir is self-adjoint for the exact
tensor-binomial metric. -/
theorem pairExchange_self_adjoint (b c : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair b c (pairExchange b c f) g ≈
      tensorBinomPair b c f (pairExchange b c g) := by
  let Sf : Nat → Nat → Q' := fun j l =>
    pairTotalScalar b c j l * f j l
  let Sg : Nat → Nat → Q' := fun j l =>
    pairTotalScalar b c j l * g j l
  let Rf := pairRaise b c (pairLower f)
  let Rg := pairRaise b c (pairLower g)
  refine Q'.eqv_trans _
    (tensorBinomPair b c (pairExchangeViaRaiseLower b c f) g) _
    (tensorBinomPair_congr_left' b c _ _ g
      (fun j hj l hl => pairExchange_eq_viaRaiseLower b c f j l)) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair b c Rf g +
      tensorBinomPair b c (fun j l => (-1 : Q') * Sf j l) g) _
    (by
      refine Q'.eqv_trans _
        (tensorBinomPair b c (fun j l => Rf j l + (-1 : Q') * Sf j l) g) _
        (tensorBinomPair_congr_left' b c _ _ g (fun j hj l hl => ?_)) ?_
      · dsimp only [pairExchangeViaRaiseLower, Rf, Sf]
        ring_qeqv
      · exact tensorBinomPair_add_left' b c Rf (fun j l => (-1) * Sf j l) g) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair b c Rf g +
      (-1 : Q') * tensorBinomPair b c Sf g) _
    (Q'.add_eqv_congr_left _ _ _
      (tensorBinomPair_scale_left' b c (-1) Sf g)) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair b c f Rg +
      (-1 : Q') * tensorBinomPair b c f Sg) _
    (Q'.add_eqv_congr'
      (by simpa only [Rf, Rg] using pairRaiseLower_self_adjoint b c f g)
      (Q'.mul_eqv_congr_left (-1) _ _ (pairTotalScalar_self_adjoint b c f g))) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair b c f Rg +
      tensorBinomPair b c f (fun j l => (-1 : Q') * Sg j l)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (tensorBinomPair_scale_right' b c (-1) f Sg))) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair b c f
      (fun j l => Rg j l + (-1 : Q') * Sg j l)) _
    (Q'.eqv_symm (tensorBinomPair_add_right' b c f Rg
      (fun j l => (-1) * Sg j l))) ?_
  exact tensorBinomPair_congr_right' b c f _ _ (fun j hj l hl => by
    have hvia : Rg j l + (-1 : Q') * Sg j l ≈
        pairExchangeViaRaiseLower b c g j l := by
      change pairRaise b c (pairLower g) j l +
          (-1 : Q') * (pairTotalScalar b c j l * g j l) ≈
        pairRaise b c (pairLower g) j l +
          -(pairTotalScalar b c j l * g j l)
      ring_qeqv
    exact Q'.eqv_trans _ _ _ hvia
      (Q'.eqv_symm (pairExchange_eq_viaRaiseLower b c g j l)))

/-! ## 3. The all-order factorial Hahn eigen-equation -/

/-- Exact pair-Casimir eigenvalue of contraction order `k`. -/
def pairEigenvalue (m n k : Nat) : Q' :=
  Q'.ofNat (k * (m + n - k + 1))

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show (a * b : Int) *
      ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (Q'.ofNat a * Q'.ofNat b).num * (1 : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one]

private theorem equal_of_scale_eqv_zero (s x y : Q') (hs : s ≈ 0) :
    s * x ≈ s * y := by
  refine Q'.eqv_trans _ (0 * x) _
    (Q'.mul_eqv_congr_right _ _ x hs) ?_
  refine Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv x) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ (0 * y) _
    (Q'.mul_eqv_congr_right _ _ y hs) (Q'.zero_mul_eqv y))

private theorem product_scale_zero_left (x : Q') :
    Q'.ofNat 0 * x ≈ 0 := by
  refine Q'.eqv_trans _ ((0 : Q') * x) _
    (Q'.mul_eqv_congr_right _ _ x Q'.ofNat_zero_eqv) ?_
  exact Q'.zero_mul_eqv x

private theorem product_scale_zero_right (x : Q') :
    x * Q'.ofNat 0 ≈ 0 := by
  refine Q'.eqv_trans _ (x * (0 : Q')) _
    (Q'.mul_eqv_congr_left x _ _ Q'.ofNat_zero_eqv) ?_
  exact Q'.mul_zero_eqv x

private theorem neg_zero_eqv : (-(0 : Q')) ≈ 0 := by decide

private theorem reverse_difference {A B C : Q'} (h : A + -B ≈ C) :
    B + -A ≈ -C := by
  refine Q'.eqv_trans _ (-A + B) _ (Q'.add_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ (-A + -(-B)) _
    (Q'.add_eqv_congr_left (-A) _ _
      (Q'.eqv_symm (Q'.neg_neg_eqv B))) ?_
  refine Q'.eqv_trans _ (-(A + -B)) _
    (Q'.eqv_symm (Q'.neg_add_eqv A (-B))) ?_
  exact Q'.neg_eqv_congr _ _ h

private theorem factorial_forward_scaled (m n k i j : Nat)
    (hkm : k ≤ m) (hkn : k ≤ n) (hi : i ≤ m) (hj : j ≤ n) :
    (Q'.ofNat (m - i) * Q'.ofNat j) *
        (transvectFactorialCoeff m n k (i + 1) (j - 1) +
          -transvectFactorialCoeff m n k i j) ≈
      (Q'.ofNat (m - i) * Q'.ofNat j) *
        (pairEigenvalue m n k *
          transvectFactorialCoeff (m - 1) (n - 1) (k - 1) i (j - 1)) := by
  by_cases him : i < m
  · by_cases hj0 : 0 < j
    · exact Q'.mul_eqv_congr_left _ _ _ (by
        simpa only [pairEigenvalue] using
          transvectFactorialCoeff_adjacent k m n i j
            hkm hkn him hj0 hj)
    · have hjz : j = 0 := by omega
      rw [hjz]
      exact equal_of_scale_eqv_zero _ _ _
        (product_scale_zero_right (Q'.ofNat (m - i)))
  · have hmz : m - i = 0 := by omega
    rw [hmz]
    exact equal_of_scale_eqv_zero _ _ _
      (product_scale_zero_left (Q'.ofNat j))

private theorem factorial_backward_scaled (m n k i j : Nat)
    (hkm : k ≤ m) (hkn : k ≤ n) (hi : i ≤ m) (hj : j ≤ n) :
    (Q'.ofNat i * Q'.ofNat (n - j)) *
        (transvectFactorialCoeff m n k (i - 1) (j + 1) +
          -transvectFactorialCoeff m n k i j) ≈
      (Q'.ofNat i * Q'.ofNat (n - j)) *
        ((-pairEigenvalue m n k) *
          transvectFactorialCoeff (m - 1) (n - 1) (k - 1) (i - 1) j) := by
  by_cases hi0 : 0 < i
  · by_cases hjn : j < n
    · have hadj := transvectFactorialCoeff_adjacent k m n (i - 1) (j + 1)
          hkm hkn (by omega) (by omega) (by omega)
      have hrev := reverse_difference hadj
      have hneg :
          -(pairEigenvalue m n k *
              transvectFactorialCoeff (m - 1) (n - 1) (k - 1) (i - 1) j) ≈
            (-pairEigenvalue m n k) *
              transvectFactorialCoeff (m - 1) (n - 1) (k - 1) (i - 1) j :=
        Q'.eqv_symm (Q'.neg_mul_eqv _ _)
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (by
          simpa only [pairEigenvalue, show i - 1 + 1 = i by omega,
            show j + 1 - 1 = j by omega] using hrev) hneg)
    · have hnz : n - j = 0 := by omega
      rw [hnz]
      exact equal_of_scale_eqv_zero _ _ _
        (product_scale_zero_right (Q'.ofNat i))
  · have hiz : i = 0 := by omega
    rw [hiz]
    exact equal_of_scale_eqv_zero _ _ _
      (product_scale_zero_left (Q'.ofNat (n - j)))

private def eigenCombineLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.mul (.var 2) (.var 4)))
    (.mul (.var 1) (.mul (.neg (.var 2)) (.var 3)))

private def eigenCombineRHS : PolyExpr :=
  .neg (.mul (.var 2)
    (.add (.mul (.var 1) (.var 3))
      (.mul (.neg (.var 0)) (.var 4))))

private theorem eigenCombine_normal :
    normalize eigenCombineLHS = normalize eigenCombineRHS := by decide

private theorem eigen_combine_ring (B D L R0 R1 : Q') :
    B * (L * R1) + D * ((-L) * R0) ≈
      -(L * (D * R0 + (-B) * R1)) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then B else if r = 1 then D else if r = 2 then L else
    if r = 3 then R0 else R1
  have h := poly_identity_of_normal_eq eigenCombineLHS eigenCombineRHS
    eigenCombine_normal ρ
  simpa [eigenCombineLHS, eigenCombineRHS, eval, ρ] using h

private theorem factorial_recurrence_product (m n k i j : Nat) :
    (Q'.ofNat i * Q'.ofNat (n - j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j +
      (-(Q'.ofNat (m - i) * Q'.ofNat j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1) ≈
      transvectFactorialCoeff m n (k + 1) i j := by
  have hrec := transvectFactorialCoeff_succ m n k i j
  have hD := ofNat_mul_eqv i (n - j)
  have hB := ofNat_mul_eqv (m - i) j
  have hconv :
      Q'.ofNat (i * (n - j)) *
          transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j +
        (-(Q'.ofNat ((m - i) * j))) *
          transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1) ≈
      (Q'.ofNat i * Q'.ofNat (n - j)) *
          transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j +
        (-(Q'.ofNat (m - i) * Q'.ofNat j)) *
          transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1) := by
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ hD)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_eqv_congr _ _ hB))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hconv) hrec

/-- Every all-order factorial Hahn row is an eigenvector of the exact pair
exchange Casimir on the full physical source rectangle. -/
theorem transvectFactorialCoeff_pairExchange_eigen
    (m n k i j : Nat) (hkm : k ≤ m) (hkn : k ≤ n)
    (hi : i ≤ m) (hj : j ≤ n) :
    pairExchange m n (fun x y => transvectFactorialCoeff m n k x y) i j ≈
      -(pairEigenvalue m n k * transvectFactorialCoeff m n k i j) := by
  cases k with
  | zero =>
      have hshift := transvectFactorialCoeff_zero m n (i + 1) (j - 1)
      have hbase := transvectFactorialCoeff_zero m n i j
      have hprev := transvectFactorialCoeff_zero m n (i - 1) (j + 1)
      unfold pairExchange pairEigenvalue
      simp only [Nat.zero_mul]
      refine Q'.eqv_trans _
        ((Q'.ofNat (m - i) * Q'.ofNat j) * ((1 : Q') + -1) +
          (Q'.ofNat i * Q'.ofNat (n - j)) * ((1 : Q') + -1)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.add_eqv_congr' hshift (Q'.neg_eqv_congr _ _ hbase)))
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.add_eqv_congr' hprev (Q'.neg_eqv_congr _ _ hbase)))
      · refine Q'.eqv_trans _ 0 _ (by
            have hz := Q'.add_neg_self_eqv (1 : Q')
            exact Q'.eqv_trans _ ((Q'.ofNat (m - i) * Q'.ofNat j) * 0 +
                (Q'.ofNat i * Q'.ofNat (n - j)) * 0) _
              (Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left _ _ _ hz)
                (Q'.mul_eqv_congr_left _ _ _ hz)) (by ring_qeqv)) ?_
        exact Q'.eqv_symm (Q'.eqv_trans _ (-(0 *
          transvectFactorialCoeff m n 0 i j)) _
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _
            Q'.ofNat_zero_eqv)) (by
              exact Q'.eqv_trans _ (-0) _
                (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv _))
                (Q'.eqv_symm (Q'.neg_add_self_eqv 0))))
  | succ k =>
      let B : Q' := Q'.ofNat (m - i) * Q'.ofNat j
      let D : Q' := Q'.ofNat i * Q'.ofNat (n - j)
      let L : Q' := pairEigenvalue m n (k + 1)
      let R0 : Q' :=
        transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j
      let R1 : Q' :=
        transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1)
      have hf := factorial_forward_scaled m n (k + 1) i j hkm hkn hi hj
      have hb := factorial_backward_scaled m n (k + 1) i j hkm hkn hi hj
      unfold pairExchange
      refine Q'.eqv_trans _ (B * (L * R1) + D * ((-L) * R0)) _ ?_ ?_
      · exact Q'.add_eqv_congr' (by simpa only [B, L, R1] using hf)
          (by simpa only [D, L, R0] using hb)
      · refine Q'.eqv_trans _ (-(L * (D * R0 + (-B) * R1))) _
          (eigen_combine_ring B D L R0 R1) ?_
        exact Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left L _ _ (by
            simpa only [B, D, R0, R1] using
              factorial_recurrence_product m n k i j))

/-! ## 4. The nested right channel inherits the same eigenvalue -/

def fixedRightOuterCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i t s : Nat) : Q' :=
  transvect a q.intermediate q.r
    (tprod (mono i) (mono (t - q.p))) s

theorem fixedRight_monomial_factorization {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat)
    (hp : q.p ≤ j + l) :
    triRight a b c d q.intermediate (mono i) (mono j) (mono l) s ≈
      transvectFactorialCoeff b c q.p j l *
        fixedRightOuterCoefficient q i (j + l) s := by
  have h := triRight_monomial_factorization
    a b c d q.intermediate i j l s (by
      rw [fixedRight_inner_couplingOrder q]
      exact hp)
  simpa only [fixedRight_inner_couplingOrder q,
    fixedRight_outer_couplingOrder q, hahnEntry,
    fixedRightOuterCoefficient,
    show j + l - j = l by omega] using h

private theorem difference_mul_factor (A B O : Q') :
    A * O + -(B * O) ≈ (A + -B) * O := by
  ring_qeqv

private theorem fixedRight_forward_scaled {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat)
    (hj : j ≤ b) (_hl : l ≤ c) (hp : q.p ≤ j + l) :
    (Q'.ofNat (b - j) * Q'.ofNat l) *
        (triRight a b c d q.intermediate
            (mono i) (mono (j + 1)) (mono (l - 1)) s +
          -triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s) ≈
      (Q'.ofNat (b - j) * Q'.ofNat l) *
        ((transvectFactorialCoeff b c q.p (j + 1) (l - 1) +
            -transvectFactorialCoeff b c q.p j l) *
          fixedRightOuterCoefficient q i (j + l) s) := by
  by_cases hjb : j < b
  · by_cases hl0 : 0 < l
    · have hshift := fixedRight_monomial_factorization q i (j + 1)
          (l - 1) s (by omega)
      have hbase := fixedRight_monomial_factorization q i j l s hp
      have htotal : j + 1 + (l - 1) = j + l := by omega
      rw [htotal] at hshift
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hshift (Q'.neg_eqv_congr _ _ hbase))
          (difference_mul_factor _ _ _))
    · have hlz : l = 0 := by omega
      rw [hlz]
      exact equal_of_scale_eqv_zero _ _ _
        (product_scale_zero_right (Q'.ofNat (b - j)))
  · have hbz : b - j = 0 := by omega
    rw [hbz]
    exact equal_of_scale_eqv_zero _ _ _
      (product_scale_zero_left (Q'.ofNat l))

private theorem fixedRight_backward_scaled {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat)
    (_hj : j ≤ b) (hl : l ≤ c) (hp : q.p ≤ j + l) :
    (Q'.ofNat j * Q'.ofNat (c - l)) *
        (triRight a b c d q.intermediate
            (mono i) (mono (j - 1)) (mono (l + 1)) s +
          -triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s) ≈
      (Q'.ofNat j * Q'.ofNat (c - l)) *
        ((transvectFactorialCoeff b c q.p (j - 1) (l + 1) +
            -transvectFactorialCoeff b c q.p j l) *
          fixedRightOuterCoefficient q i (j + l) s) := by
  by_cases hj0 : 0 < j
  · by_cases hlc : l < c
    · have hprev := fixedRight_monomial_factorization q i (j - 1)
          (l + 1) s (by omega)
      have hbase := fixedRight_monomial_factorization q i j l s hp
      have htotal : j - 1 + (l + 1) = j + l := by omega
      rw [htotal] at hprev
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hprev (Q'.neg_eqv_congr _ _ hbase))
          (difference_mul_factor _ _ _))
    · have hcz : c - l = 0 := by omega
      rw [hcz]
      exact equal_of_scale_eqv_zero _ _ _
        (product_scale_zero_right (Q'.ofNat j))
  · have hjz : j = 0 := by omega
    rw [hjz]
    exact equal_of_scale_eqv_zero _ _ _
      (product_scale_zero_left (Q'.ofNat (c - l)))

private theorem exchange_factor_ring
    (B D Xp Xm X O : Q') :
    B * ((Xp + -X) * O) + D * ((Xm + -X) * O) ≈
      (B * (Xp + -X) + D * (Xm + -X)) * O := by
  ring_qeqv

private theorem neg_eigen_factor_ring (L H O : Q') :
    (-(L * H)) * O ≈ -(L * (H * O)) := by
  ring_qeqv

/-- Every physical nested right-channel coefficient is an eigenvector of the
last-pair exchange Casimir, uniformly in the first input and output slots. -/
theorem fixedRightCoefficient_pairExchange_eigen {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat)
    (hj : j ≤ b) (hl : l ≤ c) :
    pairExchange b c
        (fun x y => triRight a b c d q.intermediate
          (mono i) (mono x) (mono y) s) j l ≈
      -(pairEigenvalue b c q.p *
        triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s) := by
  by_cases hp : q.p ≤ j + l
  · let O := fixedRightOuterCoefficient q i (j + l) s
    let H : Nat → Nat → Q' := fun x y =>
      transvectFactorialCoeff b c q.p x y
    have hf := fixedRight_forward_scaled q i j l s hj hl hp
    have hb := fixedRight_backward_scaled q i j l s hj hl hp
    have heig := transvectFactorialCoeff_pairExchange_eigen
      b c q.p j l (Nat.le_trans q.p_le (Nat.min_le_left _ _))
      (Nat.le_trans q.p_le (Nat.min_le_right _ _)) hj hl
    have hbase := fixedRight_monomial_factorization q i j l s hp
    unfold pairExchange
    refine Q'.eqv_trans _
      ((Q'.ofNat (b - j) * Q'.ofNat l) *
          ((H (j + 1) (l - 1) + -H j l) * O) +
        (Q'.ofNat j * Q'.ofNat (c - l)) *
          ((H (j - 1) (l + 1) + -H j l) * O)) _ ?_ ?_
    · exact Q'.add_eqv_congr' (by simpa only [H, O] using hf)
        (by simpa only [H, O] using hb)
    · refine Q'.eqv_trans _ (pairExchange b c H j l * O) _
          (by
            unfold pairExchange
            exact exchange_factor_ring _ _ _ _ _ _) ?_
      refine Q'.eqv_trans _ ((-(pairEigenvalue b c q.p * H j l)) * O) _
        (Q'.mul_eqv_congr_right _ _ O (by simpa only [H] using heig)) ?_
      refine Q'.eqv_trans _ (-(pairEigenvalue b c q.p * (H j l * O))) _
        (neg_eigen_factor_ring _ _ _) ?_
      exact Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (pairEigenvalue b c q.p) _ _
          (Q'.eqv_symm (by simpa only [H, O] using hbase)))
  · have hbase := triRight_monomial_zero_below_inner_order q i j l s
        (by omega)
    have hforward :
        (Q'.ofNat (b - j) * Q'.ofNat l) *
          (triRight a b c d q.intermediate
              (mono i) (mono (j + 1)) (mono (l - 1)) s +
            -triRight a b c d q.intermediate
              (mono i) (mono j) (mono l) s) ≈ 0 := by
      by_cases hjb : j < b
      · by_cases hl0 : 0 < l
        · have hshift := triRight_monomial_zero_below_inner_order q i
              (j + 1) (l - 1) s (by omega)
          refine Q'.eqv_trans _
            ((Q'.ofNat (b - j) * Q'.ofNat l) * ((0 : Q') + -0)) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.add_eqv_congr' hshift (Q'.neg_eqv_congr _ _ hbase))) ?_
          ring_qeqv
        · have hlz : l = 0 := by omega
          rw [hlz]
          refine Q'.eqv_trans _ (0 * _) _
            (Q'.mul_eqv_congr_right _ _ _
              (product_scale_zero_right (Q'.ofNat (b - j)))) ?_
          exact Q'.zero_mul_eqv _
      · have hbz : b - j = 0 := by omega
        rw [hbz]
        refine Q'.eqv_trans _ (0 * _) _
          (Q'.mul_eqv_congr_right _ _ _
            (product_scale_zero_left (Q'.ofNat l))) ?_
        exact Q'.zero_mul_eqv _
    have hbackward :
        (Q'.ofNat j * Q'.ofNat (c - l)) *
          (triRight a b c d q.intermediate
              (mono i) (mono (j - 1)) (mono (l + 1)) s +
            -triRight a b c d q.intermediate
              (mono i) (mono j) (mono l) s) ≈ 0 := by
      by_cases hj0 : 0 < j
      · by_cases hlc : l < c
        · have hprev := triRight_monomial_zero_below_inner_order q i
              (j - 1) (l + 1) s (by omega)
          refine Q'.eqv_trans _
            ((Q'.ofNat j * Q'.ofNat (c - l)) * ((0 : Q') + -0)) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.add_eqv_congr' hprev (Q'.neg_eqv_congr _ _ hbase))) ?_
          ring_qeqv
        · have hcz : c - l = 0 := by omega
          rw [hcz]
          refine Q'.eqv_trans _ (0 * _) _
            (Q'.mul_eqv_congr_right _ _ _
              (product_scale_zero_right (Q'.ofNat j))) ?_
          exact Q'.zero_mul_eqv _
      · have hjz : j = 0 := by omega
        rw [hjz]
        refine Q'.eqv_trans _ (0 * _) _
          (Q'.mul_eqv_congr_right _ _ _
            (product_scale_zero_left (Q'.ofNat (c - l)))) ?_
        exact Q'.zero_mul_eqv _
    unfold pairExchange
    refine Q'.eqv_trans _ ((0 : Q') + 0) _
      (Q'.add_eqv_congr' hforward hbackward) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.eqv_of_eq (Q'.zero_add' 0)) ?_
    have hz : pairEigenvalue b c q.p *
        triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s ≈ 0 :=
      Q'.eqv_trans _ (pairEigenvalue b c q.p * 0) _
        (Q'.mul_eqv_congr_left _ _ _ hbase) (Q'.mul_zero_eqv _)
    exact Q'.eqv_symm (Q'.eqv_trans _ (-0) _
      (Q'.neg_eqv_congr _ _ hz) neg_zero_eqv)

/-! ## 5. Slice decomposition of the trilinear Hilbert--Schmidt pairing -/

def triMapPairSlice (_a b c _d i s : Nat)
    (L R : BForm → BForm → BForm → BForm) : Q' :=
  tensorBinomPair b c
    (fun j l => L (mono i) (mono j) (mono l) s)
    (fun j l => R (mono i) (mono j) (mono l) s)

def triMapPairSliceSum (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) : Q' :=
  finSum (fun i => finSum (fun s =>
    (tvBinomQ a i * symMonomialNormSq d s) *
      triMapPairSlice a b c d i s L R) (d + 1)) (a + 1)

private theorem factor_pair_slice (a b c d i s : Nat)
    (L R : BForm → BForm → BForm → BForm) :
    finSum (fun j => finSum (fun l =>
      tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
        symMonomialNormSq d s *
          (L (mono i) (mono j) (mono l) s *
            R (mono i) (mono j) (mono l) s)) (c + 1)) (b + 1) ≈
      (tvBinomQ a i * symMonomialNormSq d s) *
        triMapPairSlice a b c d i s L R := by
  let K : Q' := tvBinomQ a i * symMonomialNormSq d s
  let U : Nat → Nat → Q' := fun j l =>
    tvBinomQ c l * (tvBinomQ b j *
      (L (mono i) (mono j) (mono l) s *
        R (mono i) (mono j) (mono l) s))
  refine Q'.eqv_trans _
    (finSum (fun j => finSum (fun l => K * U j l) (c + 1)) (b + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
    refine finSum_eqv_congr_lt _ _ (c + 1) (fun l hl => ?_)
    dsimp only [K, U]
    ring_qeqv
  · refine Q'.eqv_trans _
      (finSum (fun j => K * finSum (fun l => U j l) (c + 1)) (b + 1)) _ ?_ ?_
    · refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
      exact Q'.eqv_symm (const_mul_finSum (fun l => U j l) K (c + 1))
    · refine Q'.eqv_trans _
        (K * finSum (fun j => finSum (fun l => U j l) (c + 1)) (b + 1)) _
        (Q'.eqv_symm (const_mul_finSum
          (fun j => finSum (fun l => U j l) (c + 1)) K (b + 1))) ?_
      simp only [triMapPairSlice, tensorBinomPair, K, U]
      exact Q'.eqv_refl _

/-- The original fourfold invariant pairing is exactly the sum of the
last-pair tensor-binomial slices. -/
theorem triMapInner_eq_pairSliceSum (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) :
    triMapInner a b c d L R ≈ triMapPairSliceSum a b c d L R := by
  unfold triMapInner triMapPairSliceSum
  refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
  let T : Nat → Nat → Nat → Q' := fun j l s =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s *
        (L (mono i) (mono j) (mono l) s *
          R (mono i) (mono j) (mono l) s)
  have hswapLS :
      finSum (fun j => finSum (fun l => finSum (fun s => T j l s) (d + 1))
          (c + 1)) (b + 1) ≈
        finSum (fun j => finSum (fun s => finSum (fun l => T j l s) (c + 1))
          (d + 1)) (b + 1) := by
    refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
    exact RationalTail.finSum_swap (fun l s => T j l s) (c + 1) (d + 1)
  have hswapJS := RationalTail.finSum_swap
    (fun j s => finSum (fun l => T j l s) (c + 1)) (b + 1) (d + 1)
  refine Q'.eqv_trans _
    (finSum (fun j => finSum (fun l => finSum (fun s => T j l s) (d + 1))
      (c + 1)) (b + 1)) _ (by rfl) ?_
  refine Q'.eqv_trans _
    (finSum (fun j => finSum (fun s => finSum (fun l => T j l s) (c + 1))
      (d + 1)) (b + 1)) _ hswapLS ?_
  refine Q'.eqv_trans _
    (finSum (fun s => finSum (fun j => finSum (fun l => T j l s) (c + 1))
      (b + 1)) (d + 1)) _ hswapJS ?_
  refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
  simpa only [T] using factor_pair_slice a b c d i s L R

/-! ## 6. Casimir separation on every slice -/

def fixedRightCoefficientArray {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i s : Nat) : Nat → Nat → Q' :=
  fun j l => triRight a b c d q.intermediate
    (mono i) (mono j) (mono l) s

private theorem remove_common_negative_scale {A B X : Q'}
    (h : (-A) * X ≈ (-B) * X) : A * X ≈ B * X := by
  have hn := Q'.neg_eqv_congr _ _ h
  refine Q'.eqv_trans _ (-((-A) * X)) _ ?_ ?_
  · exact Q'.eqv_trans _ ((-(-A)) * X) _
      (Q'.mul_eqv_congr_right _ _ X
        (Q'.eqv_symm (Q'.neg_neg_eqv A)))
      (Q'.neg_mul_eqv (-A) X)
  refine Q'.eqv_trans _ (-((-B) * X)) _ hn ?_
  exact Q'.eqv_trans _ ((-(-B)) * X) _
    (Q'.eqv_symm (Q'.neg_mul_eqv (-B) X))
    (Q'.mul_eqv_congr_right _ _ X (Q'.neg_neg_eqv B))

theorem fixedRight_pairSlice_eigenvalue_balance {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) (i s : Nat) :
    pairEigenvalue b c q.p *
        tensorBinomPair b c (fixedRightCoefficientArray q i s)
          (fixedRightCoefficientArray u i s) ≈
      pairEigenvalue b c u.p *
        tensorBinomPair b c (fixedRightCoefficientArray q i s)
          (fixedRightCoefficientArray u i s) := by
  let fq := fixedRightCoefficientArray q i s
  let fu := fixedRightCoefficientArray u i s
  have hq : ∀ j, j < b + 1 → ∀ l, l < c + 1 →
      pairExchange b c fq j l ≈ (-pairEigenvalue b c q.p) * fq j l := by
    intro j hj l hl
    have h := fixedRightCoefficient_pairExchange_eigen q i j l s
      (by omega) (by omega)
    exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm (Q'.neg_mul_eqv _ _))
  have hu : ∀ j, j < b + 1 → ∀ l, l < c + 1 →
      pairExchange b c fu j l ≈ (-pairEigenvalue b c u.p) * fu j l := by
    intro j hj l hl
    have h := fixedRightCoefficient_pairExchange_eigen u i j l s
      (by omega) (by omega)
    exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm (Q'.neg_mul_eqv _ _))
  have hleft := tensorBinomPair_congr_left' b c
    (pairExchange b c fq)
    (fun j l => (-pairEigenvalue b c q.p) * fq j l) fu hq
  have hright := tensorBinomPair_congr_right' b c fq
    (pairExchange b c fu)
    (fun j l => (-pairEigenvalue b c u.p) * fu j l) hu
  have hadj := pairExchange_self_adjoint b c fq fu
  have hscaled :
      (-pairEigenvalue b c q.p) * tensorBinomPair b c fq fu ≈
        (-pairEigenvalue b c u.p) * tensorBinomPair b c fq fu := by
    refine Q'.eqv_trans _
      (tensorBinomPair b c
        (fun j l => (-pairEigenvalue b c q.p) * fq j l) fu) _
      (Q'.eqv_symm (tensorBinomPair_scale_left' b c _ fq fu)) ?_
    refine Q'.eqv_trans _ (tensorBinomPair b c (pairExchange b c fq) fu) _
      (Q'.eqv_symm hleft) ?_
    refine Q'.eqv_trans _ (tensorBinomPair b c fq (pairExchange b c fu)) _
      hadj ?_
    refine Q'.eqv_trans _
      (tensorBinomPair b c fq
        (fun j l => (-pairEigenvalue b c u.p) * fu j l)) _ hright ?_
    exact tensorBinomPair_scale_right' b c _ fq fu
  exact remove_common_negative_scale hscaled

private theorem scale_weighted_double_sum
    (A B : Q') (N M : Nat) (K P : Nat → Nat → Q')
    (h : ∀ i, i < N → ∀ s, s < M → A * P i s ≈ B * P i s) :
    A * finSum (fun i => finSum (fun s => K i s * P i s) M) N ≈
      B * finSum (fun i => finSum (fun s => K i s * P i s) M) N := by
  refine Q'.eqv_trans _
    (finSum (fun i => A * finSum (fun s => K i s * P i s) M) N) _
    (const_mul_finSum
      (fun i => finSum (fun s => K i s * P i s) M) A N) ?_
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun s => A * (K i s * P i s)) M) N) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ N (fun i hi => ?_)
    exact const_mul_finSum (fun s => K i s * P i s) A M
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun s => B * (K i s * P i s)) M) N) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ N (fun i hi => ?_)
    refine finSum_eqv_congr_lt _ _ M (fun s hs => ?_)
    refine Q'.eqv_trans _ (K i s * (A * P i s)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _ (K i s * (B * P i s)) _
      (Q'.mul_eqv_congr_left _ _ _ (h i hi s hs)) ?_
    ring_qeqv
  refine Q'.eqv_trans _
    (finSum (fun i => B * finSum (fun s => K i s * P i s) M) N) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ N (fun i hi => ?_)
    exact Q'.eqv_symm (const_mul_finSum (fun s => K i s * P i s) B M)
  exact Q'.eqv_symm (const_mul_finSum
    (fun i => finSum (fun s => K i s * P i s) M) B N)

/-- On the complete invariant Hilbert--Schmidt pairing, either right-channel
eigenvalue may be moved from one factor to the other. -/
theorem fixedRight_triMapInner_eigenvalue_balance {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) :
    pairEigenvalue b c q.p *
        triMapInner a b c d
          (triRight a b c d q.intermediate)
          (triRight a b c d u.intermediate) ≈
      pairEigenvalue b c u.p *
        triMapInner a b c d
          (triRight a b c d q.intermediate)
          (triRight a b c d u.intermediate) := by
  let L := triRight a b c d q.intermediate
  let R := triRight a b c d u.intermediate
  have hdecomp := triMapInner_eq_pairSliceSum a b c d L R
  refine Q'.eqv_trans _
    (pairEigenvalue b c q.p * triMapPairSliceSum a b c d L R) _
    (Q'.mul_eqv_congr_left _ _ _ hdecomp) ?_
  refine Q'.eqv_trans _
    (pairEigenvalue b c u.p * triMapPairSliceSum a b c d L R) _ ?_
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hdecomp))
  unfold triMapPairSliceSum
  apply scale_weighted_double_sum
  intro i hi s hs
  simpa only [triMapPairSlice, fixedRightCoefficientArray, L, R] using
    fixedRight_pairSlice_eigenvalue_balance q u i s

/-! ## 7. Strict separation of physical eigenvalues and final orthogonality -/

def pairEigenNat (m n k : Nat) : Nat :=
  k * (m + n - k + 1)

theorem pairEigenNat_strict_mono_on_physical_half
    (M k u : Nat) (hku : k < u) (hsum : k + u ≤ M) :
    k * (M - k + 1) < u * (M - u + 1) := by
  let h := u - k
  let r := M - u - k
  have hh : 0 < h := by dsimp only [h]; omega
  have hu : k + h = u := by dsimp only [h]; omega
  have hM : u + k + r = M := by dsimp only [r]; omega
  have hkTail : M - k + 1 = u + r + 1 := by omega
  have huTail : M - u + 1 = k + r + 1 := by omega
  rw [hkTail, huTail, ← hu]
  have hid :
      (k + h) * (k + r + 1) =
        k * (k + h + r + 1) + h * (r + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    ac_rfl
  rw [hid]
  have hp : 0 < h * (r + 1) := Nat.mul_pos hh (Nat.succ_pos r)
  omega

theorem fixedRight_pairEigenNat_ne {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) (hpu : q.p ≠ u.p) :
    pairEigenNat b c q.p ≠ pairEigenNat b c u.p := by
  intro heq
  have hq := Nat.le_min.mp q.p_le
  have hu := Nat.le_min.mp u.p_le
  rcases Nat.lt_or_gt_of_ne hpu with hlt | hgt
  · have hsum : q.p + u.p ≤ b + c := by omega
    have hstrict := pairEigenNat_strict_mono_on_physical_half
      (b + c) q.p u.p hlt hsum
    unfold pairEigenNat at heq
    omega
  · have hsum : u.p + q.p ≤ b + c := by omega
    have hstrict := pairEigenNat_strict_mono_on_physical_half
      (b + c) u.p q.p hgt hsum
    unfold pairEigenNat at heq
    omega

private theorem ofNat_sub_add_eqv (A B : Nat) (hBA : B ≤ A) :
    Q'.ofNat A ≈ Q'.ofNat (A - B) + Q'.ofNat B := by
  have hnat : A - B + B = A := by omega
  have h := Q'.ofNat_add_eqv (A - B) B
  rw [hnat] at h
  exact h

private theorem difference_scale_of_scale_eq
    (A B : Nat) (X : Q') (hAB : A ≤ B)
    (h : Q'.ofNat A * X ≈ Q'.ofNat B * X) :
    Q'.ofNat (B - A) * X ≈ 0 := by
  have hB := ofNat_sub_add_eqv B A hAB
  have hcancel :
      Q'.ofNat B * X + -(Q'.ofNat A * X) ≈ 0 := by
    refine Q'.eqv_trans _
      (Q'.ofNat A * X + -(Q'.ofNat A * X)) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm h)) ?_
    exact Q'.add_neg_self_eqv _
  refine Q'.eqv_trans _
    ((Q'.ofNat (B - A) + Q'.ofNat A) * X +
      -(Q'.ofNat A * X)) _ ?_ ?_
  · refine Q'.eqv_trans _ (Q'.ofNat (B - A) * X + 0) _
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat (B - A) * X +
        (Q'.ofNat A * X + -(Q'.ofNat A * X))) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.add_neg_self_eqv _))) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat (B - A) * X + Q'.ofNat A * X) +
        -(Q'.ofNat A * X)) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ X))
  refine Q'.eqv_trans _
    (Q'.ofNat B * X + -(Q'.ofNat A * X)) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ X (Q'.eqv_symm hB))) ?_
  exact hcancel

private theorem ofNat_pos_of_pos (N : Nat) (hN : 0 < N) :
    (0 : Q') < Q'.ofNat N := by
  cases N with
  | zero => omega
  | succ N => exact Q'.ofNat_succ_pos N

private theorem eqv_zero_of_distinct_nat_scales
    (A B : Nat) (X : Q') (hAB : A ≠ B)
    (h : Q'.ofNat A * X ≈ Q'.ofNat B * X) : X ≈ 0 := by
  rcases Nat.lt_or_gt_of_ne hAB with hlt | hgt
  · have hdiff := difference_scale_of_scale_eq A B X (by omega) h
    have hpos : (0 : Q') < Q'.ofNat (B - A) :=
      ofNat_pos_of_pos _ (by omega)
    apply Q'.mul_left_cancel_of_pos hpos
    exact Q'.eqv_trans _ 0 _ hdiff
      (Q'.eqv_symm (Q'.mul_zero_eqv _))
  · have hdiff := difference_scale_of_scale_eq B A X (by omega)
      (Q'.eqv_symm h)
    have hpos : (0 : Q') < Q'.ofNat (A - B) :=
      ofNat_pos_of_pos _ (by omega)
    apply Q'.mul_left_cancel_of_pos hpos
    exact Q'.eqv_trans _ 0 _ hdiff
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-- **All-label ordered right-channel off-diagonal orthogonality.** -/
theorem rightChannel_offDiagonalOrthogonality_all (a b c d : Nat) :
    RightChannelOffDiagonalOrthogonality a b c d := by
  intro q u hpu
  let G : Q' := triMapInner a b c d
    (triRight a b c d q.intermediate)
    (triRight a b c d u.intermediate)
  have hbalance := fixedRight_triMapInner_eigenvalue_balance q u
  have hne := fixedRight_pairEigenNat_ne q u hpu
  apply eqv_zero_of_distinct_nat_scales
    (pairEigenNat b c q.p) (pairEigenNat b c u.p) G hne
  simpa only [pairEigenvalue, pairEigenNat, G] using hbalance

/-- Complete all-label right-channel Gram law, with no remaining hypothesis. -/
theorem rightChannel_gram_all {a b c d : Nat}
    (q u : FixedRightCGChannel a b c d) :
    triMapInner a b c d
        (triRight a b c d q.intermediate)
        (triRight a b c d u.intermediate) ≈
      if q.p = u.p then triRightChannelWeight a b c d u.intermediate else 0 :=
  rightChannel_gram_of_offDiagonal
    (rightChannel_offDiagonalOrthogonality_all a b c d) q u

/-- Every valid target in the canonical fixed-output enumeration has the
exact one-hot Gram row required by the Schur bridge. -/
theorem enumeratedRightGramOrthogonalAt_all {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (target : Nat)
    (htarget : target < (fixedRightChannels a b c d).length) :
    EnumeratedRightGramOrthogonalAt qL target :=
  enumeratedRightGramOrthogonalAt_of_offDiagonal qL target htarget
    (rightChannel_offDiagonalOrthogonality_all a b c d)

/-- Unconditional canonical Schur-pairing collapse at every valid target. -/
theorem fixedLeft_schur_pairing_all {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (target : Nat)
    (htarget : target < (fixedRightChannels a b c d).length) :
    triMapInner a b c d (triLeft a b c d qL.intermediate)
        (triRight a b c d
          (enumeratedRightChannel qL target).intermediate) ≈
      fixedLeftRightDiagonalCoeff qL
          (enumeratedRightChannel qL target) 0 *
        triRightChannelWeight a b c d
          (enumeratedRightChannel qL target).intermediate :=
  fixedLeft_schur_pairing_of_enumerated_right_orthogonality qL target
    (enumeratedRightGramOrthogonalAt_all qL target htarget)

/-- Unconditional inverse cross normalization of the collapsed factorial
carrier at every valid canonical target. -/
theorem collapsed_cross_inverse_normalization_all {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) (target : Nat)
    (htarget : target < (fixedRightChannels a b c d).length) :
    collapsedFactorialCrossSum qL (enumeratedRightChannel qL target) ≈
      triRightChannelWeight a b c d
          (enumeratedRightChannel qL target).intermediate *
        fixedLeftRightDiagonalCoeff qL
          (enumeratedRightChannel qL target) 0 :=
  collapsed_cross_inverse_normalization_of_right_orthogonality qL target
    (enumeratedRightGramOrthogonalAt_all qL target htarget)

end YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality

#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.pairRaise_pairLower_eq_exchange
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.pairLower_adjoint_pairRaise
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.pairRaiseLower_self_adjoint
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.pairExchange_self_adjoint
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.transvectFactorialCoeff_pairExchange_eigen
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.fixedRightCoefficient_pairExchange_eigen
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.triMapInner_eq_pairSliceSum
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.fixedRight_triMapInner_eigenvalue_balance
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.fixedRight_pairEigenNat_ne
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.rightChannel_offDiagonalOrthogonality_all
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.rightChannel_gram_all
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.enumeratedRightGramOrthogonalAt_all
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.fixedLeft_schur_pairing_all
#print axioms YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality.collapsed_cross_inverse_normalization_all
