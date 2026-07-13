/-
# Finite endpoint atan series: monomial assembly and convergence

This file distributes the paired geometric kernel into the already-closed
endpoint monomial Riemann sequences.  The finite mesh sum is thereby reduced
exactly to a finite signed sum of convergent monomial sequences.
-/

import YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann
import YMGap.Constructive.TrigAddCReal
import Lean.Elab.Tactic.Omega

namespace YMGap.Continuum.SemicircleAtanEndpointSeriesConvergence

set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanEndpointCellFactor
open YMGap.Continuum.SemicircleAtanEndpointSeriesKernel
open YMGap.Continuum.SemicircleAtanEndpointSeriesSum
open YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               two_num_cast, two_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem rgQpow_eqv_congr {a b : Q'} (h : a ≈ b) : ∀ p,
    qpow a p ≈ qpow b p
  | 0 => Q'.eqv_refl 1
  | p + 1 => by
      refine Q'.eqv_trans _ (qpow b p * a) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ (rgQpow_eqv_congr h p)
      · exact Q'.mul_eqv_congr_left _ _ _ h

private theorem qpow_two_eq_square (x : Q') : qpow x 2 ≈ x*x := by
  unfold qpow
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

theorem quartic_eq_qpow_four (x : Q') :
    quartic x ≈ qpow x 4 := by
  refine Q'.eqv_trans _ (qpow x 2 * qpow x 2) _ ?_ ?_
  · unfold quartic
    refine Q'.eqv_trans _ (qpow x 2 * (x*x)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (qpow_two_eq_square x))
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (qpow_two_eq_square x))
  · exact Q'.eqv_symm (qpow_add x 2 2)

theorem qpow_quartic_eq_qpow_four_mul (x : Q') (r : Nat) :
    qpow (quartic x) r ≈ qpow x (4 * r) := by
  refine Q'.eqv_trans _ (qpow (qpow x 4) r) _ ?_ ?_
  · exact rgQpow_eqv_congr (quartic_eq_qpow_four x) r
  · exact qpow_qpow x 4 r

/-- One paired-kernel summand is exactly its two signed monomials. -/
theorem pairedKernelSummand_eq_monomialPair (x : Q') (r : Nat) :
    ((1 + -(x*x)) * qpow (quartic x) r) ≈
      (qpow x (4*r) + -qpow x (4*r+2)) := by
  let A := qpow x (4*r)
  have hquartic := qpow_quartic_eq_qpow_four_mul x r
  have htail : A * (x*x) ≈ qpow x (4*r+2) := by
    refine Q'.eqv_trans _ (A * qpow x 2) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left A _ _ (Q'.eqv_symm (qpow_two_eq_square x))
    · exact Q'.eqv_symm (qpow_add x (4*r) 2)
  refine Q'.eqv_trans _ ((1 + -(x*x)) * A) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hquartic
  refine Q'.eqv_trans _ (A + -(A*(x*x))) _ ?_ ?_
  · ring_qeqv
  exact Q'.add_eqv_congr_left A _ _ (Q'.neg_eqv_congr _ _ htail)

private theorem finSum_neg (f : Nat → Q') : ∀ n,
    finSum (fun j => -(f j)) n ≈ -(finSum f n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      refine Q'.eqv_trans _ (-(finSum f n) + -(f n)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ (finSum_neg f n)
      · exact Q'.eqv_symm (Q'.neg_add_eqv (finSum f n) (f n))

private theorem scaledPairedSummand_eq
    (k n j r : Nat) (hk : 0 < k) (hn : 0 < n) :
    (scaledMesh 1 k n hk hn *
      ((1 + -(endpointNode k n j hk hn * endpointNode k n j hk hn)) *
        qpow (quartic (endpointNode k n j hk hn)) r)) ≈
      (scaledMesh 1 k n hk hn * qpow (endpointNode k n j hk hn) (4*r) +
        -(scaledMesh 1 k n hk hn *
          qpow (endpointNode k n j hk hn) (4*r+2))) := by
  let mesh := scaledMesh 1 k n hk hn
  let x := endpointNode k n j hk hn
  refine Q'.eqv_trans _
    (mesh * (qpow x (4*r) + -qpow x (4*r+2))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left mesh _ _
      (pairedKernelSummand_eq_monomialPair x r)
  refine Q'.eqv_trans _
    (mesh * qpow x (4*r) + mesh * (-qpow x (4*r+2))) _
    (Q'.mul_add_eqv mesh _ _) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv mesh (qpow x (4*r+2)))

/-- **Exact finite signed-monomial assembly.**  At every positive mesh
resolution, the paired endpoint sum is the finite sum of its two monomial
left rectangles. -/
theorem endpointPairedSum_eq_monomialPairs
    (k n R : Nat) (hk : 0 < k) (hn : 0 < n) :
    endpointPairedSum k n R hk hn ≈
      finSum (fun r =>
        endpointMonomialLeftSum k n (4*r) hk hn +
          -endpointMonomialLeftSum k n (4*r+2) hk hn) R := by
  unfold endpointPairedSum endpointPairedTerm
  refine Q'.eqv_trans _
    (finSum (fun j => scaledMesh 1 k n hk hn *
      finSum (fun r =>
        (1 + -(endpointNode k n j hk hn * endpointNode k n j hk hn)) *
          qpow (quartic (endpointNode k n j hk hn)) r) R) n) _ ?_ ?_
  · exact finSum_eqv_congr _ _ (fun j =>
      Q'.mul_eqv_congr_left _ _ _
        (pairedKernel_eq_finSum (endpointNode k n j hk hn) R)) n
  refine Q'.eqv_trans _
    (finSum (fun j => finSum (fun r =>
      scaledMesh 1 k n hk hn *
        ((1 + -(endpointNode k n j hk hn * endpointNode k n j hk hn)) *
          qpow (quartic (endpointNode k n j hk hn)) r)) R) n) _ ?_ ?_
  · exact finSum_eqv_congr _ _ (fun j =>
      const_mul_finSum _ (scaledMesh 1 k n hk hn) R) n
  refine Q'.eqv_trans _
    (finSum (fun r => finSum (fun j =>
      scaledMesh 1 k n hk hn *
        ((1 + -(endpointNode k n j hk hn * endpointNode k n j hk hn)) *
          qpow (quartic (endpointNode k n j hk hn)) r)) n) R) _ ?_ ?_
  · exact finSum_swap _ n R
  refine finSum_eqv_congr _ _ (fun r => ?_) R
  refine Q'.eqv_trans _
    (finSum (fun j =>
      scaledMesh 1 k n hk hn * qpow (endpointNode k n j hk hn) (4*r) +
        -(scaledMesh 1 k n hk hn *
          qpow (endpointNode k n j hk hn) (4*r+2))) n) _ ?_ ?_
  · exact finSum_eqv_congr _ _
      (fun j => scaledPairedSummand_eq k n j r hk hn) n
  refine Q'.eqv_trans _
    (finSum (fun j => scaledMesh 1 k n hk hn *
        qpow (endpointNode k n j hk hn) (4*r)) n +
      finSum (fun j => -(scaledMesh 1 k n hk hn *
        qpow (endpointNode k n j hk hn) (4*r+2))) n) _
    (finSum_add _ _ n) ?_
  unfold endpointMonomialLeftSum
  exact Q'.add_eqv_congr_left _ _ _ (finSum_neg _ n)

/-- The mesh-indexed finite signed-monomial sequence for a fixed series
cutoff `R`. -/
def endpointPairedMonomialSeq
    (k R : Nat) (hk : 0 < k) : Nat → CReal :=
  fun N => CReal.ofQ' (finSum (fun r =>
    endpointMonomialLeftSum k (N+1) (4*r) hk (Nat.succ_pos N) +
      -endpointMonomialLeftSum k (N+1) (4*r+2) hk (Nat.succ_pos N)) R)

/-- The corresponding finite sum of exact endpoint monomial values. -/
def endpointPairedMonomialValue
    (k R : Nat) (hk : 0 < k) : Q' :=
  finSum (fun r =>
    endpointMonomialValue k (4*r) hk +
      -endpointMonomialValue k (4*r+2) hk) R

/-- Finite sums of the signed monomial Riemann sequences converge to the
finite sum of their exact endpoint values. -/
theorem endpointPairedMonomialSeq_converges
    (k : Nat) (hk : 0 < k) : ∀ R,
    CReal.ConvergesTo (endpointPairedMonomialSeq k R hk)
      (CReal.ofQ' (endpointPairedMonomialValue k R hk))
  | 0 => by
      simpa [endpointPairedMonomialSeq, endpointPairedMonomialValue]
        using CReal.convergesTo_self (CReal.ofQ' (0 : Q'))
  | R + 1 => by
      have hprev := endpointPairedMonomialSeq_converges k hk R
      have heven := endpointMonomialSeq_converges k (4*R) hk
      have hodd := endpointMonomialSeq_converges k (4*R+2) hk
      have hsigned := TrigAddCReal.convergesTo_add heven
        (TrigAddCReal.convergesTo_neg hodd)
      have hsum := TrigAddCReal.convergesTo_add hprev hsigned
      simpa only [endpointPairedMonomialSeq, endpointPairedMonomialValue,
        endpointMonomialSeq, finSum_succ, CReal.ofQ'_add, CReal.ofQ'_neg]
        using hsum

/-- The original paired-kernel mesh sequence converges to the assembled
finite monomial value. -/
theorem endpointPairedSeq_converges
    (k R : Nat) (hk : 0 < k) :
    CReal.ConvergesTo
      (fun N => CReal.ofQ'
        (endpointPairedSum k (N+1) R hk (Nat.succ_pos N)))
      (CReal.ofQ' (endpointPairedMonomialValue k R hk)) := by
  apply TrigAddCReal.convergesTo_congr_seq
    (s := endpointPairedMonomialSeq k R hk)
  · intro N
    exact TrigAdd.equiv_ofQ'_of_eqv
      (Q'.eqv_symm
        (endpointPairedSum_eq_monomialPairs
          k (N+1) R hk (Nat.succ_pos N)))
  · exact endpointPairedMonomialSeq_converges k hk R

theorem endpointMonomialValue_pair_eq_two_cTerm
    (k : Nat) (hk : 0 < k) (r : Nat) :
    (endpointMonomialValue k (4*r) hk +
      -endpointMonomialValue k (4*r+2) hk) ≈
      ((2 : Q') * Pi.cTerm k hk r) := by
  have he : endpointMonomialValue k (4*r) hk ≈
      (2 : Q') * Pi.bMag k hk (2*r) := by
    have h := endpointMonomialValue_even_eq_two_bMag k (2*r) hk
    have hexp : 2 * (2*r) = 4*r := by omega
    rw [hexp] at h
    exact h
  have ho : endpointMonomialValue k (4*r+2) hk ≈
    (2 : Q') * Pi.bMag k hk (2*r+1) := by
    have h := endpointMonomialValue_even_eq_two_bMag k (2*r+1) hk
    have hexp : 2 * (2*r+1) = 4*r+2 := by omega
    rw [hexp] at h
    exact h
  refine Q'.eqv_trans _
    ((2 : Q') * Pi.bMag k hk (2*r) +
      -((2 : Q') * Pi.bMag k hk (2*r+1))) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((2 : Q') * Pi.bMag k hk (2*r) +
        -endpointMonomialValue k (4*r+2) hk) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ he
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ ho)
  change ((2 : Q') * Pi.bMag k hk (2*r) +
      -((2 : Q') * Pi.bMag k hk (2*r+1))) ≈
    (2 : Q') * (Pi.bMag k hk (2*r) + -Pi.bMag k hk (2*r+1))
  refine Q'.eqv_trans _
    ((2 : Q') * Pi.bMag k hk (2*r) +
      (2 : Q') * (-Pi.bMag k hk (2*r+1))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_neg_eqv 2 (Pi.bMag k hk (2*r+1))))
  exact Q'.eqv_symm (Q'.mul_add_eqv 2 _ _)

/-- The assembled finite monomial value is exactly the formal endpoint
partial sum, hence also `2 * Pi.cPart`. -/
theorem endpointPairedMonomialValue_eq_formalEndpointPartial
    (k R : Nat) (hk : 0 < k) :
    endpointPairedMonomialValue k R hk ≈
      formalEndpointPartial k hk R := by
  refine Q'.eqv_trans _
    (finSum (fun r => (2 : Q') * Pi.cTerm k hk r) R) _ ?_ ?_
  · exact finSum_eqv_congr _ _
      (fun r => endpointMonomialValue_pair_eq_two_cTerm k hk r) R
  refine Q'.eqv_trans _ ((2 : Q') * Pi.cPart k hk R) _ ?_ ?_
  · unfold Pi.cPart
    exact Q'.eqv_symm (const_mul_finSum _ 2 R)
  exact Q'.eqv_symm (formalEndpointPartial_eq_two_cPart k hk R)

theorem endpointPairedMonomialValue_eq_two_cPart
    (k R : Nat) (hk : 0 < k) :
    endpointPairedMonomialValue k R hk ≈
      (2 : Q') * Pi.cPart k hk R := by
  exact Q'.eqv_trans _ _ _
    (endpointPairedMonomialValue_eq_formalEndpointPartial k R hk)
    (formalEndpointPartial_eq_two_cPart k hk R)

private theorem four_error_chain
    (a b c d e q epsilon : Q')
    (hq4 : ((q+q)+(q+q)) ≈ epsilon)
    (hab : a ≤ b+q) (hbc : b ≤ c+q) (hcd : c ≤ d+q)
    (hde : d ≤ e+q) : a ≤ e+epsilon := by
  have h1 : a ≤ (c+q)+q :=
    Q'.le_trans' _ _ _ hab (Q'.add_le_add_right _ _ q hbc)
  have h2 : a ≤ ((d+q)+q)+q :=
    Q'.le_trans' _ _ _ h1
      (Q'.add_le_add_right _ _ q
        (Q'.add_le_add_right _ _ q hcd))
  have h3 : a ≤ (((e+q)+q)+q)+q :=
    Q'.le_trans' _ _ _ h2
      (Q'.add_le_add_right _ _ q
        (Q'.add_le_add_right _ _ q
          (Q'.add_le_add_right _ _ q hde)))
  refine Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ (e + ((q+q)+(q+q))) _ ?_ ?_
  · ring_qeqv
  · exact Q'.add_eqv_congr_left e _ _ hq4

private theorem two_mul_le_two_mul_add
    {a b t q : Q'} (hab : a ≤ b+t) (htwo : (2 : Q') * t ≈ q) :
    (2 : Q') * a ≤ (2 : Q') * b + q := by
  have hmul : (2 : Q') * a ≤ (2 : Q') * (b+t) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hab (by decide)
  refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ ((2 : Q') * b + (2 : Q') * t) _
    (Q'.mul_add_eqv 2 b t) ?_
  exact Q'.add_eqv_congr_left _ _ _ htwo

/-- **Two-cutoff endpoint theorem.**  If `A` is the constructive arctangent
real whose approximations are the paired partial sums at `1/k`, then the full
endpoint Darboux left sums converge to `2*A`.  The proof chooses a series
cutoff large enough simultaneously for `A`'s Cauchy modulus and the uniform
geometric remainder, then uses the already-closed finite monomial limit. -/
theorem scaledLeftEndpointSeq_converges
    (k : Nat) (hk2 : 2 ≤ k) (A : CReal)
    (hA : ∀ n, A.approx n =
      Pi.cPart k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk2) n) :
    CReal.ConvergesTo
      (fun N => CReal.ofQ'
        (scaledLeftSum 1 k (N+1)
          (Nat.lt_of_lt_of_le Nat.zero_lt_two hk2) (Nat.succ_pos N)))
      (CReal.mul (CReal.ofQ' (2 : Q')) A) := by
  let hk : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk2
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * (HalfPow.half * epsilon)
  let t : Q' := HalfPow.half * q
  have hq : (0 : Q') < q :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
  have ht : (0 : Q') < t := ExpNeg.half_mul_pos q hq
  have hq4 : ((q+q)+(q+q)) ≈ epsilon := by
    have hqq : (q+q) ≈ HalfPow.half * epsilon :=
      ExpNeg.two_halves (HalfPow.half * epsilon)
    refine Q'.eqv_trans _
      ((HalfPow.half * epsilon) + (q+q)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ hqq
    refine Q'.eqv_trans _
      ((HalfPow.half * epsilon) + (HalfPow.half * epsilon)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _ hqq
    · exact ExpNeg.two_halves epsilon
  have htwoT : (2 : Q') * t ≈ q := by
    refine Q'.eqv_trans _ (t+t) _ ?_ ?_
    · refine Q'.eqv_trans _ (((1 : Q') + 1) * t) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
      refine Q'.eqv_trans _ ((1 : Q') * t + (1 : Q') * t) _
        (Q'.add_mul_eqv 1 1 t) ?_
      refine Q'.eqv_trans _ (t + (1 : Q') * t) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv t)
      · exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv t)
    · exact ExpNeg.two_halves q
  obtain ⟨Nc, hNc⟩ := A.cauchy t ht
  let R : Nat := max q.den Nc
  have hqdenR : q.den ≤ R := Nat.le_max_left _ _
  have hNcR : Nc ≤ R := Nat.le_max_right _ _
  have hpairConv := endpointPairedSeq_converges k R hk
  obtain ⟨Ns, hNs⟩ := hpairConv q hq
  refine ⟨Ns, fun N hN => ?_⟩
  obtain ⟨Np, hNp⟩ := hNs N hN
  refine ⟨max Np Nc, fun n hn => ?_⟩
  have hnP : Np ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnC : Nc ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hpUpper, hpLower⟩ := hNp n hnP
  have hAc := hNc R n hNcR hnC
  rw [hA R, hA n] at hAc
  let full := scaledLeftSum 1 k (N+1) hk (Nat.succ_pos N)
  let paired := endpointPairedSum k (N+1) R hk (Nat.succ_pos N)
  let rem := endpointRemainderSum k (N+1) R hk (Nat.succ_pos N)
  let value := endpointPairedMonomialValue k R hk
  let cR := Pi.cPart k hk R
  let cN := Pi.cPart k hk n
  have hsplit : full ≈ paired + rem :=
    scaledLeftSum_eqv_paired_add_remainder
      k (N+1) R hk (Nat.succ_pos N)
  have hrem0 : (0 : Q') ≤ rem :=
    endpointRemainderSum_nonnegative k (N+1) R hk (Nat.succ_pos N)
  have hrem : rem ≤ q := by
    refine Q'.le_trans' _ _ _
      (endpointRemainderSum_le_invSucc hk2 (N+1) R (Nat.succ_pos N)) ?_
    refine Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenR) ?_
    exact HalfPow.invSucc_den_le q hq
  have hfullUpper : full ≤ paired + q :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.add_le_add_left _ _ _ hrem)
  have hpairedLower : paired ≤ full := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg paired rem hrem0) ?_
    exact Q'.ge_of_eqv hsplit
  have hvalue : value ≈ (2 : Q') * cR :=
    endpointPairedMonomialValue_eq_two_cPart k R hk
  have hcRUpper : (2 : Q') * cR ≤ (2 : Q') * cN + q :=
    two_mul_le_two_mul_add hAc.1 htwoT
  have hcNUpper : (2 : Q') * cN ≤ (2 : Q') * cR + q :=
    two_mul_le_two_mul_add hAc.2 htwoT
  have hvalueUpper : value ≤ (2 : Q') * cR + q :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hvalue)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hq))
  have hcRValueUpper : (2 : Q') * cR ≤ value + q :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hvalue)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hq))
  change full ≤ (2 : Q') * A.approx n + epsilon ∧
    (2 : Q') * A.approx n ≤ full + epsilon
  rw [hA n]
  constructor
  · exact four_error_chain full paired value ((2 : Q') * cR)
      ((2 : Q') * cN) q epsilon hq4 hfullUpper hpUpper
      hvalueUpper hcRUpper
  · exact four_error_chain ((2 : Q') * cN) ((2 : Q') * cR)
      value paired full q epsilon hq4 hcNUpper hcRValueUpper
      hpLower
      (Q'.le_trans' _ _ _ hpairedLower
        (Q'.add_le_self_of_nonneg full q (Q'.le_of_lt hq)))

/-- The generic rational Darboux integral at endpoint `1/k` is exactly twice
the project's paired-series arctangent real. -/
theorem rationalAtanIntegral_one_recip_eq_two
    (k : Nat) (hk2 : 2 ≤ k) (A : CReal)
    (hA : ∀ n, A.approx n =
      Pi.cPart k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk2) n) :
    CReal.Equiv
      (rationalAtanIntegral 1 k
        (Nat.lt_of_lt_of_le Nat.zero_lt_two hk2))
      (CReal.mul (CReal.ofQ' (2 : Q')) A) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := rationalAtanSeq 1 k
      (Nat.lt_of_lt_of_le Nat.zero_lt_two hk2))
    (bSeq := fun N => CReal.ofQ'
      (scaledLeftSum 1 k (N+1)
        (Nat.lt_of_lt_of_le Nat.zero_lt_two hk2) (Nat.succ_pos N)))
    (fun N => ?_)
    (rationalAtanSeq_converges 1 k
      (Nat.lt_of_lt_of_le Nat.zero_lt_two hk2))
    (scaledLeftEndpointSeq_converges k hk2 A hA)
  exact TrigAdd.equiv_ofQ'_of_eqv (Q'.eqv_refl _)

theorem rationalAtanIntegral_one_five_eq_two_at5 :
    CReal.Equiv (rationalAtanIntegral 1 5 (by decide))
      (CReal.mul (CReal.ofQ' (2 : Q')) Pi.at5) := by
  exact rationalAtanIntegral_one_recip_eq_two 5 (by decide) Pi.at5
    Pi.at5_approx

theorem rationalAtanIntegral_one_239_eq_two_at239 :
    CReal.Equiv (rationalAtanIntegral 1 239 (by decide))
      (CReal.mul (CReal.ofQ' (2 : Q')) Pi.at239) := by
  exact rationalAtanIntegral_one_recip_eq_two 239 (by decide) Pi.at239
    Pi.at239_approx

#print axioms quartic_eq_qpow_four
#print axioms qpow_quartic_eq_qpow_four_mul
#print axioms pairedKernelSummand_eq_monomialPair
#print axioms endpointPairedSum_eq_monomialPairs
#print axioms endpointPairedMonomialSeq_converges
#print axioms endpointPairedSeq_converges
#print axioms endpointMonomialValue_pair_eq_two_cTerm
#print axioms endpointPairedMonomialValue_eq_formalEndpointPartial
#print axioms endpointPairedMonomialValue_eq_two_cPart
#print axioms scaledLeftEndpointSeq_converges
#print axioms rationalAtanIntegral_one_recip_eq_two
#print axioms rationalAtanIntegral_one_five_eq_two_at5
#print axioms rationalAtanIntegral_one_239_eq_two_at239

end YMGap.Continuum.SemicircleAtanEndpointSeriesConvergence
