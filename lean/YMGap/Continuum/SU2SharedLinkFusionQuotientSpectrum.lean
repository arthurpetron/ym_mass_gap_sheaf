/-
# Shared-link radical quotient, exact spectrum, and third-plaquette gluing

The two-plaquette shared-link block has one radical direction (`10-01`).
Its explicit quotient coordinates are the three irreducible characters
`chi_0, chi_1, chi_2`.  This file records their orthonormal Haar basis and the
exact heat-kernel spectrum `1,1/8,1/256`.

The same mechanism is then tested on a third overlapping fundamental
plaquette.  Fusing the first pair and then the third, or the last pair and
then the first, gives the same four irreducible coordinates.  In particular
`chi_1^3 = 2 chi_1 + chi_3`; the multiplicity two is retained explicitly.

Finally, an arbitrary finite irreducible packet is treated at once.  The
standard gap-edge dominance theorem says every nonvacuum eigenvalue
`w^{s(s+2)}` is at most the `s=1` value `1/8`.  A termwise finite-sum proof
therefore gives the volume/cutoff-independent squared contraction `1/64` on
every packet with zero vacuum coordinate.  This applies uniformly after any
finite associative shared-link fusion, independently of the number of
generated irreducible channels.

Honest scope: the result is local to a shared link.  Gluing these quotient
maps consistently over an entire lattice with several links per plaquette is
still required; no global Wilson-measure factorization is asserted.
-/

import YMGap.Continuum.SU2SharedLinkFusionBlock
import YMGap.Continuum.SpectralLocalizationCrux

namespace YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFusionBlock

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## The explicit three-dimensional radical quotient -/

def quotientVacuum : IrrepVec := (1, (0, 0))
def quotientFundamental : IrrepVec := (0, (1, 0))
def quotientQuadratic : IrrepVec := (0, (0, 1))

theorem quotientGram_basis_matrix :
    irrepGram quotientVacuum quotientVacuum ≈ 1 ∧
    irrepGram quotientVacuum quotientFundamental ≈ 0 ∧
    irrepGram quotientVacuum quotientQuadratic ≈ 0 ∧
    irrepGram quotientFundamental quotientFundamental ≈ 1 ∧
    irrepGram quotientFundamental quotientQuadratic ≈ 0 ∧
    irrepGram quotientQuadratic quotientQuadratic ≈ 1 := by decide

theorem quotientTransfer_exact_spectrum :
    IrrepEq (irrepTransfer quotientVacuum) quotientVacuum ∧
    IrrepEq (irrepTransfer quotientFundamental)
      (0, (eighth, 0)) ∧
    IrrepEq (irrepTransfer quotientQuadratic)
      (0, (0, quadraticEigen)) := by
  unfold IrrepEq irrepTransfer quotientVacuum quotientFundamental quotientQuadratic
  exact ⟨⟨by decide, by decide, by decide⟩,
    ⟨⟨by decide, by decide, by decide⟩,
      ⟨by decide, by decide, by decide⟩⟩⟩

theorem quotient_spectrum_values :
    eighth ≈ Q'.mkPos 1 8 (by decide) ∧
    quadraticEigen ≈ Q'.mkPos 1 256 (by decide) :=
  ⟨Q'.eqv_refl _, quadraticEigen_exact⟩

/-! ## Associative gluing of a third overlapping plaquette -/

/-- Eight tensor labels, stored as the four labels with the third bit `0`
and the four labels with the third bit `1`. -/
abbrev TripleVec := SharedVec × SharedVec
abbrev TripleIrrep := Q' × (Q' × (Q' × Q'))

def TripleIrrepEq (a b : TripleIrrep) : Prop :=
  a.1 ≈ b.1 ∧ a.2.1 ≈ b.2.1 ∧
    a.2.2.1 ≈ b.2.2.1 ∧ a.2.2.2 ≈ b.2.2.2

/-- Fuse the first two plaquette labels, then multiply the result by the
third fundamental label using
`chi_0 chi_1=chi_1`, `chi_1^2=chi_0+chi_2`,
`chi_2 chi_1=chi_1+chi_3`. -/
def fuseFirstPairThenThird (a : TripleVec) : TripleIrrep :=
  let r := fusionCollapse a.1
  let d := fusionCollapse a.2
  (r.1 + d.2.1,
    (r.2.1 + (d.1 + d.2.2),
      (r.2.2 + d.2.1, d.2.2)))

private def lastPairSliceZero (a : TripleVec) : SharedVec :=
  (a.1.1, (a.1.2.2.1, (a.2.1, a.2.2.2.1)))

private def lastPairSliceOne (a : TripleVec) : SharedVec :=
  (a.1.2.1, (a.1.2.2.2, (a.2.2.1, a.2.2.2.2)))

/-- Fuse the last two labels first, then multiply by the first fundamental
label. -/
def fuseLastPairThenFirst (a : TripleVec) : TripleIrrep :=
  let r := fusionCollapse (lastPairSliceZero a)
  let d := fusionCollapse (lastPairSliceOne a)
  (r.1 + d.2.1,
    (r.2.1 + (d.1 + d.2.2),
      (r.2.2 + d.2.1, d.2.2)))

/-- Exact associativity of the shared-link fusion map for arbitrary
eight-component superpositions. -/
theorem third_gluing_associative (a : TripleVec) :
    TripleIrrepEq (fuseFirstPairThenThird a) (fuseLastPairThenFirst a) := by
  unfold TripleIrrepEq fuseFirstPairThenThird fuseLastPairThenFirst
    lastPairSliceZero lastPairSliceOne fusionCollapse vacuumCoord
    fundamentalCoord quadraticCoord
  exact ⟨by ring_qeqv, by ring_qeqv, by ring_qeqv, Q'.eqv_refl _⟩

def tripleFundamentalMode : TripleVec :=
  ((0, (0, (0, 0))), (0, (0, (0, 1))))

/-- The all-excited triple fuses to `2 chi_1 + chi_3`; the multiplicity two
is explicit and not confused with a transfer eigenvalue. -/
theorem tripleFundamental_fusion_multiplicity :
    TripleIrrepEq (fuseFirstPairThenThird tripleFundamentalMode)
      (0, (2, (0, 1))) := by
  unfold TripleIrrepEq fuseFirstPairThenThird tripleFundamentalMode
    fusionCollapse vacuumCoord fundamentalCoord quadraticCoord
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- Haar audits of `chi_1^3 = 2 chi_1 + chi_3`. -/
theorem tripleFundamental_Haar_audit :
    bareVacuumHaar (pmul (pmul chi1 chi1) chi1) ≈ 0 ∧
    bareVacuumHaar (pmul (pmul (pmul chi1 chi1) chi1) chi1) ≈ 2 ∧
    bareVacuumHaar (pmul (pmul (pmul chi1 chi1) chi1) chi3) ≈ 1 := by decide

theorem tripleFundamental_polynomial_associative :
    PolyEqv (pmul (pmul chi1 chi1) chi1) (pmul chi1 (pmul chi1 chi1)) :=
  pmul_assoc chi1 chi1 chi1

def cubicEigen : Q' := physLinkWeight coupling 3

theorem cubicEigen_exact :
    cubicEigen ≈ Q'.mkPos 1 32768 (by decide) := by decide

/-! ## Uniform contraction for every finite fused quotient -/

/-- Diagonal Haar norm of the first `N` irreducible coefficients. -/
def modeNorm (f : Nat → Q') (N : Nat) : Q' :=
  fsum (fun s => f s * f s) N

def modeTransfer (f : Nat → Q') (s : Nat) : Q' :=
  eigA coupling s * f s

private theorem fsum_le_fsum {f g : Nat → Q'}
    (h : ∀ s, f s ≤ g s) : ∀ N, fsum f N ≤ fsum g N
  | 0 => Q'.le_refl' 0
  | N + 1 => Q'.add_le_add (fsum_le_fsum h N) (h N)

private theorem fsum_const_mul (c : Q') (f : Nat → Q') : ∀ N,
    fsum (fun s => c * f s) N ≈ c * fsum f N
  | 0 => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | N + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_const_mul c f N)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c (fsum f N) (f N))

private theorem scaled_term_le (a b x : Q')
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hb : (0 : Q') ≤ b) :
    (a * x) * (a * x) ≤ (b * b) * (x * x) := by
  have h1 := Q'.mul_le_mul_of_nonneg_right a b a hab ha
  have h2 := Q'.mul_le_mul_of_nonneg_left a b b hab hb
  have hs : a * a ≤ b * b := Q'.le_trans' _ _ _ h1 h2
  have hm := Q'.mul_le_mul_of_nonneg_right
    (a * a) (b * b) (x * x) hs
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg x)
  exact Q'.le_trans' _ ((a * a) * (x * x)) _
    (Q'.le_of_eqv (by ring_qeqv)) hm

private theorem mode_term_uniform (f : Nat → Q')
    (h0 : f 0 ≈ 0) (s : Nat) :
    modeTransfer f s * modeTransfer f s ≤
      (eighth * eighth) * (f s * f s) := by
  cases s with
  | zero =>
      have hx : (f 0 * f 0).eqv 0 :=
        Q'.eqv_trans _ _ _ (q_mul_congr h0 h0) (Q'.zero_mul_eqv 0)
      have hl : (modeTransfer f 0 * modeTransfer f 0).eqv 0 := by
        unfold modeTransfer
        rw [eigA_zero]
        exact Q'.eqv_trans _ _ _
          (q_mul_congr (Q'.one_mul_eqv (f 0)) (Q'.one_mul_eqv (f 0))) hx
      have hr : ((eighth * eighth) * (f 0 * f 0)).eqv 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (eighth * eighth) _ _ hx)
          (Q'.mul_zero_eqv _)
      exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hl)
        (Q'.le_of_eqv (Q'.eqv_symm hr))
  | succ k =>
      have heig0 : (0 : Q') ≤ eigA coupling (k + 1) :=
        eigA_nonneg (by decide) (k + 1)
      have hedge : eigA coupling (k + 1) ≤ eigA coupling 1 :=
        gapEdge_dominates (by decide) (by decide) (by omega)
      have heig1 : eigA coupling 1 ≈ eighth := by decide
      have hle : eigA coupling (k + 1) ≤ eighth :=
        Q'.le_trans' _ _ _ hedge (Q'.le_of_eqv heig1)
      exact scaled_term_le _ _ _ heig0 hle (by decide)

/-- **Volume/cutoff-independent fused-quotient contraction.**  Every finite
irreducible packet with zero vacuum coefficient contracts in squared Haar
norm by the same factor `(1/8)^2`, regardless of how many overlapping
fundamental plaquettes generated its channels. -/
theorem finite_fused_quotient_uniform_contraction
    (f : Nat → Q') (h0 : f 0 ≈ 0) (N : Nat) :
    modeNorm (modeTransfer f) N ≤
      (eighth * eighth) * modeNorm f N := by
  have hs := fsum_le_fsum (mode_term_uniform f h0) N
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_of_eqv (fsum_const_mul (eighth * eighth)
      (fun s => f s * f s) N))

end YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum

#print axioms YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum.quotientGram_basis_matrix
#print axioms YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum.quotientTransfer_exact_spectrum
#print axioms YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum.third_gluing_associative
#print axioms YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum.tripleFundamental_fusion_multiplicity
#print axioms YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum.tripleFundamental_Haar_audit
#print axioms YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum.cubicEigen_exact
#print axioms YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum.finite_fused_quotient_uniform_contraction
