/-
# Constructive finite SU(2) Haar-L2 and Hilbert--Schmidt limits

This module lifts the repository's genuine midpoint-Riemann construction of
the SU(2) character Gram matrix to finite character packets and finite-rank
kernels.

No integration or convergence field is assumed here.  Every limit starts from
the explicit rational midpoint sequence `ChebOrthoMatrix.seqOrth2`, uses the
unconditional all-order orthogonality theorem, and then applies only proved
finite-sum and constant-multiplication stability of `CReal.ConvergesTo`.

The resulting theorems are deliberately finite in character rank.  They close
the exact Haar-L2/Hilbert--Schmidt layer needed for any fixed character
truncation, while leaving honest the still-missing analytic atom for the
nonlinear five-holonomy problem: a uniform infinite-rank/tail majorant (with
the nonlinear rescaling/Jacobian error controlled uniformly in the Riemann
resolution).

# Axiom gate

The load-bearing theorems at the end of the file are checked with
`#print axioms`.  No `Classical.*`, `Real`, choice, or placeholder axiom is
used.
-/

import YMGap.Continuum.SU2FiniteHaarRiemannTwoModeClosed
import YMGap.Continuum.ChebRProjection

namespace YMGap.Continuum.SU2HaarL2HilbertSchmidt

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMatrix
open YMGap.Continuum.ChebOrthoMatrixUncond

/-! ## 1. All-order normalized Haar moments from actual midpoint sums -/

/-- The normalized midpoint-Riemann approximation to the SU(2) character
moment `⟨U_c,U_d⟩`: `(2/pi) * seqOrth2 c d N`. -/
def normalizedRiemannMoment (c d N : Nat) : CReal :=
  CReal.mul Constructive.Pi.twoOverPi (seqOrth2 c d N)

/-- The exact normalized Haar moment table in the character basis. -/
def haarMoment (c d : Nat) : CReal :=
  if c = d then CReal.ofQ' (1 : Q') else CReal.czero

/-- Scaling the raw all-order orthogonality limit gives the normalized
Kronecker moment table. -/
theorem scaledRawLimit_equiv_haarMoment (c d : Nat) :
    CReal.Equiv
      (CReal.mul Constructive.Pi.twoOverPi
        (if c = d then SemicircleBoundClosed.semiInt else CReal.czero))
      (haarMoment c d) := by
  rcases Nat.decEq c d with hne | heq
  · rw [if_neg hne]
    unfold haarMoment
    rw [if_neg hne]
    exact HaarClassIntegral.mul_czero Constructive.Pi.twoOverPi
  · subst d
    rw [if_pos rfl]
    unfold haarMoment
    rw [if_pos rfl]
    exact CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_right
        SemicircleMidpointValueClosed.semiInt_eq_halfPi)
      SU2FiniteHaarRiemannTwoMode.twoOverPi_mul_halfPi

/-- **All-order normalized Haar orthogonality with genuine Riemann
provenance.**  The explicit midpoint sequence converges to `δ_cd`. -/
theorem normalizedRiemannMoment_converges (c d : Nat) :
    CReal.ConvergesTo (normalizedRiemannMoment c d) (haarMoment c d) := by
  have hscaled :=
    ChebRProjection.convergesTo_const_mul Constructive.Pi.twoOverPi
      (orthMatrix_unconditional c d)
  exact convergesTo_retarget hscaled (scaledRawLimit_equiv_haarMoment c d)

/-! ## 2. Finite character packets: constructive Haar-L2 pairing -/

/-- A coefficient-scaled normalized moment. -/
def scaledMoment (q : Q') (c d N : Nat) : CReal :=
  CReal.mul (CReal.ofQ' q) (normalizedRiemannMoment c d N)

/-- Constant scaling preserves the genuine normalized moment limit. -/
theorem scaledMoment_converges (q : Q') (c d : Nat) :
    CReal.ConvergesTo (scaledMoment q c d)
      (CReal.mul (CReal.ofQ' q) (haarMoment c d)) := by
  exact ChebRProjection.convergesTo_const_mul (CReal.ofQ' q)
    (normalizedRiemannMoment_converges c d)

/-- A diagonal scaled moment converges to its rational coefficient. -/
theorem diagonalScaledMoment_converges (q : Q') (i : Nat) :
    CReal.ConvergesTo (scaledMoment q i i) (CReal.ofQ' q) := by
  have h := scaledMoment_converges q i i
  unfold haarMoment at h
  rw [if_pos rfl] at h
  exact convergesTo_retarget h
    (HaarClassIntegral.mul_ofQ'_one (CReal.ofQ' q))

/-- An off-diagonal scaled moment converges to zero. -/
theorem offDiagonalScaledMoment_converges (q : Q') (c d : Nat)
    (hne : c ≠ d) :
    CReal.ConvergesTo (scaledMoment q c d) CReal.czero := by
  have h := scaledMoment_converges q c d
  unfold haarMoment at h
  rw [if_neg hne] at h
  exact convergesTo_retarget h
    (HaarClassIntegral.mul_czero (CReal.ofQ' q))

/-- Finite-sum convergence requiring hypotheses only on the summands that
actually occur (`i < L`).  This avoids adding arbitrary convergence data
outside a finite truncation. -/
theorem convergesTo_csum_bounded
    (S : Nat → Nat → CReal) (lim : Nat → CReal) :
    ∀ L, (∀ i, i < L → CReal.ConvergesTo (S i) (lim i)) →
      CReal.ConvergesTo (fun N => CReal.csum (fun i => S i N) L)
        (CReal.csum lim L)
  | 0, _ => by
      intro ε hε
      refine ⟨0, fun N _ => ⟨0, fun n _ => ?_⟩⟩
      show (CReal.czero).approx n ≤ (CReal.czero).approx n + ε
        ∧ (CReal.czero).approx n ≤ (CReal.czero).approx n + ε
      exact ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε)⟩
  | L + 1, h => by
      have ih := convergesTo_csum_bounded S lim L
        (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have hlast := h L (Nat.lt_add_one L)
      simpa only [CReal.csum_succ] using
        ChebOrthoMatrix.convergesTo_add ih hlast

/-- A finite constructive sum of zeros is equivalent to zero. -/
theorem csum_czero_equiv : ∀ L,
    CReal.Equiv (CReal.csum (fun _ : Nat => CReal.czero) L) CReal.czero
  | 0 => CReal.Equiv.refl CReal.czero
  | L + 1 =>
      CReal.Equiv.trans
        (Pivot2.add_congr (csum_czero_equiv L)
          (CReal.Equiv.refl CReal.czero))
        (ChebRProjection.add_czero_right CReal.czero)

/-- The two off-diagonal entries associated with an unordered pair of
character modes. -/
def offDiagonalPairTerm
    (a b : Nat → Q') (i j N : Nat) : CReal :=
  CReal.add
    (scaledMoment (a i * b j) i j N)
    (scaledMoment (a j * b i) j i N)

/-- Each strict off-diagonal pair tends to zero. -/
theorem offDiagonalPairTerm_converges
    (a b : Nat → Q') (i j : Nat) (hji : j < i) :
    CReal.ConvergesTo (offDiagonalPairTerm a b i j) CReal.czero := by
  have hji_ne : j ≠ i := Nat.ne_of_lt hji
  have hij_ne : i ≠ j := fun h => hji_ne h.symm
  have hsum := ChebOrthoMatrix.convergesTo_add
    (offDiagonalScaledMoment_converges (a i * b j) i j hij_ne)
    (offDiagonalScaledMoment_converges (a j * b i) j i hji_ne)
  exact convergesTo_retarget hsum
    (ChebRProjection.add_czero_right CReal.czero)

/-- The strict lower/upper triangular part of the packet pairing in row `i`.
Both orientations are included, so together with the diagonal this enumerates
the full square character Gram sum. -/
def offDiagonalRow
    (a b : Nat → Q') (i N : Nat) : CReal :=
  CReal.csum (fun j => offDiagonalPairTerm a b i j N) i

/-- The whole finite off-diagonal row tends to zero. -/
theorem offDiagonalRow_converges (a b : Nat → Q') (i : Nat) :
    CReal.ConvergesTo (offDiagonalRow a b i) CReal.czero := by
  have hsum :
      CReal.ConvergesTo
        (fun N => CReal.csum
          (fun j => offDiagonalPairTerm a b i j N) i)
        (CReal.csum (fun _ : Nat => CReal.czero) i) :=
    convergesTo_csum_bounded
      (fun j => offDiagonalPairTerm a b i j)
      (fun _ => CReal.czero) i
      (fun j hj => offDiagonalPairTerm_converges a b i j hj)
  exact convergesTo_retarget hsum (csum_czero_equiv i)

/-- The row contribution to the normalized midpoint pairing: its diagonal
moment plus both orientations of every earlier off-diagonal mode. -/
def packetRowRiemann
    (a b : Nat → Q') (i N : Nat) : CReal :=
  CReal.add
    (scaledMoment (a i * b i) i i N)
    (offDiagonalRow a b i N)

/-- A packet row converges exactly to the diagonal coefficient product. -/
theorem packetRowRiemann_converges (a b : Nat → Q') (i : Nat) :
    CReal.ConvergesTo (packetRowRiemann a b i)
      (CReal.ofQ' (a i * b i)) := by
  have hsum := ChebOrthoMatrix.convergesTo_add
    (diagonalScaledMoment_converges (a i * b i) i)
    (offDiagonalRow_converges a b i)
  exact convergesTo_retarget hsum
    (ChebRProjection.add_czero_right (CReal.ofQ' (a i * b i)))

/-- The full normalized midpoint-Riemann pairing of two character packets
truncated to modes `< L`.  The triangular enumeration is exactly the full
`L × L` Gram sum: one diagonal term per row and both orientations for each
strict pair. -/
def packetRiemannPairing
    (a b : Nat → Q') (L N : Nat) : CReal :=
  CReal.csum (fun i => packetRowRiemann a b i N) L

/-- The constructive Haar-L2 pairing of finite character packets.  Parseval
is built into the exact diagonal coefficient formula. -/
def haarL2Pairing (a b : Nat → Q') (L : Nat) : CReal :=
  CReal.csum (fun i => CReal.ofQ' (a i * b i)) L

/-- **Finite-packet Haar-L2/Parseval theorem.**  The explicit normalized
midpoint-Riemann pairings converge to the diagonal coefficient pairing. -/
theorem packetRiemannPairing_converges
    (a b : Nat → Q') (L : Nat) :
    CReal.ConvergesTo (packetRiemannPairing a b L)
      (haarL2Pairing a b L) := by
  exact ChebOrthoMatrix.convergesTo_csum
    (fun i => packetRowRiemann a b i)
    (fun i => CReal.ofQ' (a i * b i))
    (fun i => packetRowRiemann_converges a b i) L

/-! ## 3. Finite-rank Hilbert--Schmidt kernels -/

/-- Resolution-`N` normalized Haar-L2 square of a finite matrix kernel,
summed over rows `< R` and character columns `< C`. -/
def finiteKernelHSRiemannSq
    (K : Nat → Nat → Q') (R C N : Nat) : CReal :=
  CReal.csum
    (fun i => packetRiemannPairing (K i) (K i) C N) R

/-- The exact finite-rank Hilbert--Schmidt square:
`Σ_{i<R} Σ_{j<C} K_ij²`, represented constructively in `CReal`. -/
def finiteKernelHSSq
    (K : Nat → Nat → Q') (R C : Nat) : CReal :=
  CReal.csum
    (fun i => haarL2Pairing (K i) (K i) C) R

/-- **Finite-rank Hilbert--Schmidt cutoff removal.**  The explicit normalized
midpoint Haar sums converge to the exact coefficient Hilbert--Schmidt square.
There is no assumed integration functional and no assumed HS convergence. -/
theorem finiteKernelHSRiemannSq_converges
    (K : Nat → Nat → Q') (R C : Nat) :
    CReal.ConvergesTo (finiteKernelHSRiemannSq K R C)
      (finiteKernelHSSq K R C) := by
  exact ChebOrthoMatrix.convergesTo_csum
    (fun i => packetRiemannPairing (K i) (K i) C)
    (fun i => haarL2Pairing (K i) (K i) C)
    (fun i => packetRiemannPairing_converges (K i) (K i) C) R

/-- At every approximation level, the finite HS square is literally the
nested rational sum of coefficient squares. -/
theorem finiteKernelHSSq_approx
    (K : Nat → Nat → Q') (R C p : Nat) :
    (finiteKernelHSSq K R C).approx p =
      finSum (fun i => finSum (fun j => K i j * K i j) C) R := by
  unfold finiteKernelHSSq haarL2Pairing
  rw [CReal.csum_approx]
  apply congrArg (fun f : Nat → Q' => finSum f R)
  funext i
  rw [CReal.csum_approx]
  rfl

/-- The exact finite HS square has nonnegative rational approximations at
every constructive precision. -/
theorem finiteKernelHSSq_approx_nonneg
    (K : Nat → Nat → Q') (R C p : Nat) :
    (0 : Q') ≤ (finiteKernelHSSq K R C).approx p := by
  rw [finiteKernelHSSq_approx]
  let rowSq : Nat → Q' :=
    fun i => finSum (fun j => K i j * K i j) C
  have hrow : ∀ i, (0 : Q') ≤ rowSq i := by
    intro i
    unfold rowSq
    induction C with
    | zero => exact Q'.le_refl' 0
    | succ n ih =>
        exact Q'.zero_le_add _ _ ih
          (SumOfSquares.q_mul_self_nonneg (K i n))
  induction R with
  | zero => exact Q'.le_refl' 0
  | succ n ih =>
      exact Q'.zero_le_add _ _ ih (hrow n)

/-- The finite-rank Hilbert--Schmidt square is nonnegative as a constructive
real, not only as a coefficient-level mnemonic. -/
theorem finiteKernelHSSq_nonneg
    (K : Nat → Nat → Q') (R C : Nat) :
    ExpPos.geRat (finiteKernelHSSq K R C) 0 :=
  ExpPos.geRat_of_eventually
    ⟨0, fun p _ => finiteKernelHSSq_approx_nonneg K R C p⟩

end YMGap.Continuum.SU2HaarL2HilbertSchmidt

#print axioms YMGap.Continuum.SU2HaarL2HilbertSchmidt.normalizedRiemannMoment_converges
#print axioms YMGap.Continuum.SU2HaarL2HilbertSchmidt.packetRiemannPairing_converges
#print axioms YMGap.Continuum.SU2HaarL2HilbertSchmidt.finiteKernelHSRiemannSq_converges
#print axioms YMGap.Continuum.SU2HaarL2HilbertSchmidt.finiteKernelHSSq_approx_nonneg
#print axioms YMGap.Continuum.SU2HaarL2HilbertSchmidt.finiteKernelHSSq_nonneg
