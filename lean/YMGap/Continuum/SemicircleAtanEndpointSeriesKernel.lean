/-
# Exact endpoint-series kernel for the rational atan integral

This module aligns the two finite algebraic objects on the still-open endpoint
value path:

* `SemicircleAtanRationalEndpoint.scaledCell 1 k n j`, the uniform Darboux
  cell for `2/(1+x^2)` at `x = j/(kn)`;
* `Pi.cPart k ... N`, the paired alternating arctangent partial sum used by
  the definitions of `Pi.at5`, `Pi.at239`, and hence `Pi.halfPi`.

The common kernel is deliberately finite and exact.  `pairedKernel x N` is the first
`N` paired terms

    (1-x^2) (1+x^4+...+x^(4(N-1))).

It satisfies the checked geometric-remainder identity

    (1+x^2) pairedKernel(x,N) + (x^4)^N = 1.

Consequently the exact rational kernel is the paired polynomial plus its
explicit remainder.  Independently, termwise formal integration at the
endpoint `1/k` identifies the first `2N` alternating monomials with exactly
`2*cPart k N`.  Thus no coefficient/sign/grouping ambiguity remains in the
finite polynomial that must be compared with the Darboux carrier.

What remains is to factor the existing `scaledCell` through this normalized
kernel (an exact finite rational identity), then prove that the resulting
finite uniform power sums converge to their formal monomial integrals,
uniformly enough to pass first the mesh limit and then the displayed geometric
remainder.  The second step is the genuine analytic residual.  This file does
not assume either step, an angle-addition law, or an endpoint value identity.

All declarations are constructive and gated at EOF.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, or measured constant occurs.
-/

import YMGap.Continuum.SemicircleAtanRationalEndpoint
import YMGap.Constructive.Pi
import YMGap.Constructive.QDivArctanSeries
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.TrigAdd
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SemicircleAtanEndpointSeriesKernel

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.HeatKernelRGStep

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : (((1 : Q').den : Int)) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, one_num, one_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.mul_assoc, Int.mul_comm,
               Int.mul_left_comm] <;>
             omega))

/-! ## 1. The exact paired geometric kernel -/

/-- The quartic ratio `x^4`, kept in the multiplication shape used by the
paired arctangent series. -/
def quartic (x : Q') : Q' := (x*x)*(x*x)

/-- The first `N` paired terms of the geometric expansion of `1/(1+x^2)`:
`(1-x^2) * (1+x^4+...+x^(4(N-1)))`. -/
def pairedKernel (x : Q') (n : Nat) : Q' :=
  (1 + -(x*x)) * geomSum (quartic x) n

@[simp] theorem pairedKernel_zero (x : Q') : pairedKernel x 0 =
    (1 + -(x*x)) * 0 := rfl

@[simp] theorem pairedKernel_succ (x : Q') (n : Nat) :
    pairedKernel x (n+1) =
      (1 + -(x*x)) *
        (geomSum (quartic x) n + RGTransport.qpow (quartic x) n) := rfl

/-- The Horner recursion is exactly the paired finite sum
`sum_{r<N} (x^(4r)-x^(4r+2))`, expressed through the quartic ratio. -/
theorem pairedKernel_eq_finSum (x : Q') (n : Nat) :
    (pairedKernel x n).eqv
      (finSum (fun r =>
        (1 + -(x*x)) * RGTransport.qpow (quartic x) r) n) := by
  unfold pairedKernel
  have hgeom : geomSum (quartic x) n =
      finSum (fun r => RGTransport.qpow (quartic x) r) n := by
    induction n with
    | zero => rfl
    | succ m ih =>
        show geomSum (quartic x) m + RGTransport.qpow (quartic x) m =
          finSum (fun r => RGTransport.qpow (quartic x) r) m +
            RGTransport.qpow (quartic x) m
        rw [ih]
  rw [hgeom]
  exact const_mul_finSum
    (fun r => RGTransport.qpow (quartic x) r) (1 + -(x*x)) n

private def diffSquaresL : RingNormaliser.PolyExpr :=
  .mul (.add (.const 1) (.var 0)) (.add (.const 1) (.neg (.var 0)))

private def diffSquaresR : RingNormaliser.PolyExpr :=
  .add (.const 1) (.neg (.mul (.var 0) (.var 0)))

private theorem diffSquares_normal :
    RingNormaliser.normalize diffSquaresL =
      RingNormaliser.normalize diffSquaresR := by decide

private theorem diff_squares (s : Q') :
    (((1 : Q') + s) * (1 + -s)).eqv (1 + -(s*s)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    diffSquaresL diffSquaresR diffSquares_normal (fun _ => s)
  simpa [diffSquaresL, diffSquaresR, RingNormaliser.eval] using h

private theorem add_neg_add_self (a : Q') :
    (((1 : Q') + -a) + a).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-a) a) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 (-a+a) 0 (Q'.neg_add_self_eqv a)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' 1)

/-- **Exact geometric remainder.**  For every rational `x` and every finite
pair cutoff `N`,

`(1+x^2) * pairedKernel(x,N) + (x^4)^N = 1`.

This is the pointwise algebra required to compare endpoint Darboux sums with
the paired arctangent series. -/
theorem pairedKernel_remainder (x : Q') : ∀ n,
    (((1 : Q') + x*x) * pairedKernel x n +
      RGTransport.qpow (quartic x) n).eqv 1 := by
  intro n
  unfold pairedKernel
  have hds := diff_squares (x*x)
  have hfac := oneSub_pow_factor (quartic x) n
  have hleft :
      (((1 : Q') + x*x) * ((1 + -(x*x)) * geomSum (quartic x) n)).eqv
        ((1 + -(quartic x)) * geomSum (quartic x) n) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (1+x*x) (1 + -(x*x)) _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _ hds
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (RGTransport.qpow (quartic x) n) hleft) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (RGTransport.qpow (quartic x) n)
      (Q'.eqv_symm hfac)) ?_
  exact add_neg_add_self (RGTransport.qpow (quartic x) n)

/-! ## 2. Quotient form: exact kernel = polynomial + exact remainder -/

/-- The positive denominator `1+x^2`. -/
theorem kernelDen_pos (x : Q') : (0 : Q') < (1 : Q') + x*x := by
  have hsq : (0 : Q') ≤ x*x := SumOfSquares.q_mul_self_nonneg x
  have hnum : ((1 : Q') + x*x).num = (x*x).den + (x*x).num := by
    show (1 : Int) * ((x*x).den : Int) + (x*x).num * (1 : Int) =
      ((x*x).den : Int) + (x*x).num
    rw [Int.one_mul, Int.mul_one]
  have hxnum : (0 : Int) ≤ (x*x).num := (Q'.zero_le_iff_num_nonneg _).mp hsq
  show (0 : Q').num * ((((1 : Q') + x*x).den) : Int) <
    ((1 : Q') + x*x).num * (((0 : Q').den) : Int)
  rw [hnum]
  have hd : (1 : Int) ≤ ((x*x).den : Int) := by
    have hp := (x*x).den_pos
    omega
  simp only [show (0 : Q').num = 0 from rfl,
    show (((0 : Q').den) : Int) = 1 from rfl,
    Int.zero_mul, Int.mul_one]
  omega

/-- The normalized rational kernel `1/(1+x^2)`.  The endpoint Darboux cell
has an external mesh factor `2/(kn)`, so keeping the factor `2` outside makes
the series coefficients match `2*cPart` transparently. -/
def unitKernel (x : Q') : Q' :=
  Q'.divPos 1 ((1 : Q') + x*x) (kernelDen_pos x)

theorem unitKernel_mul_den (x : Q') :
    (unitKernel x * ((1 : Q') + x*x)).eqv 1 :=
  Q'.divPos_mul_eqv _ _ (kernelDen_pos x)

/-- **Exact quotient remainder.**  The kernel equals the paired polynomial
plus a positive-ratio remainder, with no limiting argument:

`1/(1+x^2) = pairedKernel(x,N) + (1/(1+x^2))*(x^4)^N`. -/
theorem unitKernel_eq_paired_add_remainder (x : Q') (n : Nat) :
    (unitKernel x).eqv
      (pairedKernel x n + unitKernel x * RGTransport.qpow (quartic x) n) := by
  have hrem := pairedKernel_remainder x n
  have hmul :
      (unitKernel x *
        (((1 : Q') + x*x) * pairedKernel x n +
          RGTransport.qpow (quartic x) n)).eqv
      (unitKernel x * 1) :=
    Q'.mul_eqv_congr_left _ _ _ hrem
  have hden := unitKernel_mul_den x
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_trans _ _ _ hmul (Q'.mul_one_eqv (unitKernel x))))
  refine Q'.eqv_trans _
    (((unitKernel x * ((1 : Q') + x*x)) * pairedKernel x n) +
      unitKernel x * RGTransport.qpow (quartic x) n) _ ?_ ?_
  · refine Q'.add_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.one_mul_eqv (pairedKernel x n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hden)) ?_
    exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      (unitKernel x * (((1 : Q') + x*x) * pairedKernel x n) +
        unitKernel x * RGTransport.qpow (quartic x) n) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_assoc_eqv (unitKernel x) ((1 : Q') + x*x)
          (pairedKernel x n))
    · exact Q'.eqv_symm
        (Q'.mul_add_eqv (unitKernel x)
          (((1 : Q') + x*x) * pairedKernel x n)
          (RGTransport.qpow (quartic x) n))

/-! ## 3. The same paired coefficients are exactly `2 * Pi.cPart` -/

/-- The formal integral at `1/k` of the signed monomial
`2*(-1)^m*x^(2m)`.  `Pi.bMag k hk m` is exactly
`1/((2m+1)k^(2m+1))`; the word "formal" is load-bearing here: the theorem below
is finite coefficient algebra, while convergence of uniform power sums to this
value is the remaining analytic step. -/
def formalIntegratedKernelTerm (k : Nat) (hk : 0 < k) (m : Nat) : Q' :=
  (2 : Q') * (Trig.negPow m * Pi.bMag k hk m)

/-- First `2N` formally integrated alternating-kernel monomials. -/
def formalEndpointPartial (k : Nat) (hk : 0 < k) (N : Nat) : Q' :=
  finSum (formalIntegratedKernelTerm k hk) (2*N)

theorem negPow_odd_eqv_neg_one (n : Nat) :
    (Trig.negPow (2*n+1)).eqv (-(1 : Q')) := by
  show (-(Trig.negPow (2*n))).eqv (-(1 : Q'))
  exact Q'.neg_eqv_congr _ _ (TrigAdd.negPow_two_mul n)

/-- One adjacent even/odd pair of formally integrated monomials is exactly
twice the paired `Pi.cTerm`. -/
theorem formalIntegratedKernel_pair
    (k : Nat) (hk : 0 < k) (n : Nat) :
    (formalIntegratedKernelTerm k hk (2*n) +
      formalIntegratedKernelTerm k hk (2*n+1)).eqv
      ((2 : Q') * Pi.cTerm k hk n) := by
  unfold formalIntegratedKernelTerm Pi.cTerm
  have he := TrigAdd.negPow_two_mul n
  have ho := negPow_odd_eqv_neg_one n
  have heTerm :
      ((2 : Q') * (Trig.negPow (2*n) * Pi.bMag k hk (2*n))).eqv
        ((2 : Q') * ((1 : Q') * Pi.bMag k hk (2*n))) :=
    Q'.mul_eqv_congr_left 2 _ _
      (Q'.mul_eqv_congr_right _ _ _ he)
  have hoTerm :
      ((2 : Q') * (Trig.negPow (2*n+1) * Pi.bMag k hk (2*n+1))).eqv
        ((2 : Q') * ((-(1 : Q')) * Pi.bMag k hk (2*n+1))) :=
    Q'.mul_eqv_congr_left 2 _ _
      (Q'.mul_eqv_congr_right _ _ _ ho)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ heTerm) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hoTerm) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.one_mul_eqv _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.neg_mul_eqv 1 _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left 2 _ _
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))) ?_
  exact Q'.eqv_symm (Q'.mul_add_eqv 2 _ _)

/-- **Finite termwise-integration identity.**  The first `2N` alternating
kernel monomials, formally integrated at `1/k`, are exactly

`2 * Pi.cPart k N`.

In particular this applies verbatim to `k=5` and `k=239`, the two concrete
series defining the project's Machin `pi`. -/
theorem formalEndpointPartial_eq_two_cPart
    (k : Nat) (hk : 0 < k) : ∀ N,
    (formalEndpointPartial k hk N).eqv ((2 : Q') * Pi.cPart k hk N)
  | 0 => by
      unfold formalEndpointPartial Pi.cPart
      exact Q'.eqv_symm (Q'.mul_zero_eqv 2)
  | N + 1 => by
      have ih := formalEndpointPartial_eq_two_cPart k hk N
      unfold formalEndpointPartial
      have hlen : 2 * (N + 1) = 2*N + 2 := by omega
      rw [hlen, TrigAdd.finSum_two_step]
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv
          (finSum (formalIntegratedKernelTerm k hk) (2*N))
          (formalIntegratedKernelTerm k hk (2*N))
          (formalIntegratedKernelTerm k hk (2*N+1))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (formalIntegratedKernel_pair k hk N)) ?_
      unfold Pi.cPart
      rw [finSum_succ]
      exact Q'.eqv_symm (Q'.mul_add_eqv 2 _ _)

theorem formalEndpointPartial_five (N : Nat) :
    (formalEndpointPartial 5 (by decide) N).eqv ((2 : Q') * Pi.at5.approx N) := by
  rw [Pi.at5_approx]
  exact formalEndpointPartial_eq_two_cPart 5 (by decide) N

theorem formalEndpointPartial_twoThirtyNinth (N : Nat) :
    (formalEndpointPartial 239 (by decide) N).eqv ((2 : Q') * Pi.at239.approx N) := by
  rw [Pi.at239_approx]
  exact formalEndpointPartial_eq_two_cPart 239 (by decide) N

end YMGap.Continuum.SemicircleAtanEndpointSeriesKernel

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.pairedKernel_eq_finSum
#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.pairedKernel_remainder
#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.kernelDen_pos
#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.unitKernel_eq_paired_add_remainder
#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.formalIntegratedKernel_pair
#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.formalEndpointPartial_eq_two_cPart
#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.formalEndpointPartial_five
#print axioms YMGap.Continuum.SemicircleAtanEndpointSeriesKernel.formalEndpointPartial_twoThirtyNinth
