/-
# Grouped five-holonomy fusion and Hilbert--Schmidt completion

This file moves the SU(2) Haar/Hilbert--Schmidt frontier from one diagonal
character channel to the first genuinely five-factor carrier that can be
proved from the present library without inserting the missing BF4 analytic
identification.

There are two complementary results.

1.  At every finite character cutoff, four successive Clebsch--Gordan fusion
    products synthesize exactly to the pointwise fifth power of the heat
    character packet.  Its Haar-L2 square is obtained from the repository's
    genuine normalized midpoint sums, so this is an actual nonlinear finite
    product theorem, not a diagonal coefficient mnemonic.

2.  On the five independent transmitted holonomy coordinates, the full
    all-label box Hilbert--Schmidt square is constructed as a CReal.  The
    finite five-dimensional coefficient boxes converge to it.  Moreover a
    grouped heat corridor `q ↦ q^steps`, for every positive number of steps,
    preserves the original certified tail cutoff, so the same joint
    all-label convergence theorem holds after every finite heat-time
    rescaling.

The tempting estimate that would identify these two carriers is false even
at the first nontrivial heat cutoff.  At `q = 1/2`, cutoff one, the nonlinear
fifth-power Haar square is exactly `215753357 / 524288`, whereas the
independent five-label tensor box is only `9765625 / 1048576`.  The
kernel-checked strict counterexample below therefore fences off an invalid
L2-tensor shortcut: coherent Clebsch--Gordan recombination needs a separate
weighted fusion-tail estimate.

Honest scope: the second theorem is the tensor-product Haar carrier on
`SU(2)^5`; the first theorem supplies exact nonlinear pointwise fusion on
each SU(2) coordinate.  This file does NOT identify that carrier with the
coupled BF4 kernel

  k_s (M_{\bar W_s} k_s)^(m-1),

and it proves no BCH remainder, exponential-chart Jacobian estimate,
complement-chart estimate, or nonlinear-to-Gaussian operator convergence.
Those are still the named analytic wall.  In particular no physical BF4 or
mass-gap certificate is inhabited here.

# Axiom gate

All constructions are finite `Type`-level data or constructive CReal
completions.  There is no `Classical.*`, `Real`, choice, `native_decide`,
custom axiom, or placeholder.
-/

import YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion
import YMGap.Continuum.SU2CharacterFusionSynthesis
import YMGap.Constructive.CRealLog

namespace YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialPacketDescent
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2HaarL2HilbertSchmidt
open YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact nonlinear fivefold Clebsch--Gordan carrier -/

/-- Left-associated pointwise fifth power of a class polynomial. -/
def fivePointwiseProduct (p : Poly) : Poly :=
  pmul (pmul (pmul (pmul p p) p) p) p

/-- The same fivefold product built by four successive, coefficient-bearing
Clebsch--Gordan fusion packets.  Every multiplication is the actual packet
descent/fusion/synthesis construction. -/
def fiveFusionCarrier (p : Poly) : Poly :=
  polynomialFusionProduct
    (polynomialFusionProduct
      (polynomialFusionProduct
        (polynomialFusionProduct p p) p) p) p

/-- **Exact nonlinear five-factor synthesis.**  Four successive
Clebsch--Gordan packet products are extensionally the ordinary pointwise
fifth power. -/
theorem fiveFusionCarrier_eq_pointwise (p : Poly) :
    PolyEqv (fiveFusionCarrier p) (fivePointwiseProduct p) := by
  have h2 :
      PolyEqv (polynomialFusionProduct p p) (pmul p p) :=
    polynomialFusionProduct_eq_pmul p p
  have h3 :
      PolyEqv
        (polynomialFusionProduct (polynomialFusionProduct p p) p)
        (pmul (pmul p p) p) :=
    peqv_trans
      (polynomialFusionProduct_eq_pmul
        (polynomialFusionProduct p p) p)
      (pmul_congr h2 (peqv_refl p))
  have h4 :
      PolyEqv
        (polynomialFusionProduct
          (polynomialFusionProduct (polynomialFusionProduct p p) p) p)
        (pmul (pmul (pmul p p) p) p) :=
    peqv_trans
      (polynomialFusionProduct_eq_pmul
        (polynomialFusionProduct
          (polynomialFusionProduct p p) p) p)
      (pmul_congr h3 (peqv_refl p))
  have h5 :
      PolyEqv
        (polynomialFusionProduct
          (polynomialFusionProduct
            (polynomialFusionProduct
              (polynomialFusionProduct p p) p) p) p)
        (pmul (pmul (pmul (pmul p p) p) p) p) :=
    peqv_trans
      (polynomialFusionProduct_eq_pmul
        (polynomialFusionProduct
          (polynomialFusionProduct
            (polynomialFusionProduct p p) p) p) p)
      (pmul_congr h4 (peqv_refl p))
  exact h5

/-- The finite heat-character packet through label `N`. -/
def heatPacket (q : Q') (N : Nat) : CharacterPacket N where
  coeff i := TruncationTailChannelBound.chanCoeff q i.val

/-- The actual finite heat class polynomial through label `N`. -/
def heatPolynomial (q : Q') (N : Nat) : Poly :=
  synthesis (heatPacket q N)

/-- Four successive nonlinear fusion products of the finite heat packet. -/
def nonlinearFiveHeatCarrier (q : Q') (N : Nat) : Poly :=
  fiveFusionCarrier (heatPolynomial q N)

/-- The finite nonlinear heat carrier is exactly the pointwise fifth power
of the synthesized heat packet. -/
theorem nonlinearFiveHeatCarrier_eq_pointwise (q : Q') (N : Nat) :
    PolyEqv (nonlinearFiveHeatCarrier q N)
      (fivePointwiseProduct (heatPolynomial q N)) :=
  fiveFusionCarrier_eq_pointwise (heatPolynomial q N)

/-! ## 2. Genuine finite Haar-L2 limits of the nonlinear carrier -/

/-- The canonical coefficient packet obtained by descending the nonlinear
fivefold carrier. -/
def nonlinearFiveHaarPacket (q : Q') (N : Nat) :
    CharacterPacket
      (pairCutoff (nonlinearFiveHeatCarrier q N)
        (nonlinearFiveHeatCarrier q N)) :=
  leftPolynomialPacket
    (nonlinearFiveHeatCarrier q N) (nonlinearFiveHeatCarrier q N)

/-- The descended packet still synthesizes to the exact nonlinear carrier. -/
theorem nonlinearFiveHaarPacket_synthesis (q : Q') (N : Nat) :
    PolyEqv (synthesis (nonlinearFiveHaarPacket q N))
      (nonlinearFiveHeatCarrier q N) :=
  synthesis_leftPolynomialPacket
    (nonlinearFiveHeatCarrier q N) (nonlinearFiveHeatCarrier q N)

/-- Consequently the packet whose Haar square is taken below synthesizes
directly to the pointwise fifth power of the finite heat packet. -/
theorem nonlinearFiveHaarPacket_synthesizes_pointwise
    (q : Q') (N : Nat) :
    PolyEqv (synthesis (nonlinearFiveHaarPacket q N))
      (fivePointwiseProduct (heatPolynomial q N)) :=
  peqv_trans (nonlinearFiveHaarPacket_synthesis q N)
    (nonlinearFiveHeatCarrier_eq_pointwise q N)

/-- Number of modes in the canonical descended packet. -/
def nonlinearFiveModeCount (q : Q') (N : Nat) : Nat :=
  pairCutoff (nonlinearFiveHeatCarrier q N)
    (nonlinearFiveHeatCarrier q N) + 1

/-- The exact finite Haar-L2 square of the nonlinear fivefold heat carrier. -/
def nonlinearFiveHaarL2Sq (q : Q') (N : Nat) : CReal :=
  haarL2Pairing
    (coeffAt (nonlinearFiveHaarPacket q N))
    (coeffAt (nonlinearFiveHaarPacket q N))
    (nonlinearFiveModeCount q N)

/-- The rational coefficient sum underlying the finite nonlinear Haar square. -/
def nonlinearFiveHaarL2SqQ (q : Q') (N : Nat) : Q' :=
  finSum
    (fun i =>
      coeffAt (nonlinearFiveHaarPacket q N) i *
        coeffAt (nonlinearFiveHaarPacket q N) i)
    (nonlinearFiveModeCount q N)

/-- Every approximation of the finite nonlinear Haar square is the same exact
rational coefficient sum. -/
theorem nonlinearFiveHaarL2Sq_approx
    (q : Q') (N p : Nat) :
    (nonlinearFiveHaarL2Sq q N).approx p =
      nonlinearFiveHaarL2SqQ q N := by
  unfold nonlinearFiveHaarL2Sq nonlinearFiveHaarL2SqQ haarL2Pairing
  rw [CReal.csum_approx]
  rfl

/-- The normalized midpoint approximation to the same nonlinear Haar square. -/
def nonlinearFiveHaarRiemannSq
    (q : Q') (N resolution : Nat) : CReal :=
  packetRiemannPairing
    (coeffAt (nonlinearFiveHaarPacket q N))
    (coeffAt (nonlinearFiveHaarPacket q N))
    (nonlinearFiveModeCount q N) resolution

/-- **Finite nonlinear Haar theorem.**  For every heat cutoff, genuine
normalized midpoint sums converge to the Haar-L2 square of the exact
Clebsch--Gordan fivefold product. -/
theorem nonlinearFiveHaarRiemannSq_converges (q : Q') (N : Nat) :
    CReal.ConvergesTo (nonlinearFiveHaarRiemannSq q N)
      (nonlinearFiveHaarL2Sq q N) :=
  packetRiemannPairing_converges
    (coeffAt (nonlinearFiveHaarPacket q N))
    (coeffAt (nonlinearFiveHaarPacket q N))
    (nonlinearFiveModeCount q N)

/-- Every rational approximation to the nonlinear finite Haar square is
nonnegative. -/
theorem nonlinearFiveHaarL2Sq_approx_nonneg
    (q : Q') (N p : Nat) :
    (0 : Q') ≤ (nonlinearFiveHaarL2Sq q N).approx p := by
  unfold nonlinearFiveHaarL2Sq haarL2Pairing
  rw [CReal.csum_approx]
  exact finSum_nonneg_local _ (fun i =>
    SumOfSquares.q_mul_self_nonneg
      (coeffAt (nonlinearFiveHaarPacket q N) i))
    (nonlinearFiveModeCount q N)

/-- The finite nonlinear Haar square is nonnegative as a constructive real. -/
theorem nonlinearFiveHaarL2Sq_nonneg (q : Q') (N : Nat) :
    ExpPos.geRat (nonlinearFiveHaarL2Sq q N) 0 :=
  ExpPos.geRat_of_eventually
    ⟨0, fun p _ => nonlinearFiveHaarL2Sq_approx_nonneg q N p⟩

/-! ## 3. Five-coordinate coefficient boxes

The recursive definition below is a literal nested five-dimensional sum.
It is kept generic because the factorization is the finite Fubini/Tonelli
identity used by the joint all-label completion. -/

/-- `tensorBoxMass f d M` is the `d`-fold box sum over labels `< M` of
the product of the `d` factors `f(label)`. -/
def tensorBoxMass (f : Nat → Q') : Nat → Nat → Q'
  | 0, _ => 1
  | d + 1, M =>
      finSum (fun i => f i * tensorBoxMass f d M) M

/-- Right-associated rational power, chosen to match the approximation
sequence of `cTensorPower` definitionally. -/
def qTensorPower (x : Q') : Nat → Q'
  | 0 => 1
  | d + 1 => x * qTensorPower x d

/-- Constructive-real right-associated tensor power. -/
def cTensorPower (X : CReal) : Nat → CReal
  | 0 => CReal.cone
  | d + 1 => CReal.mul X (cTensorPower X d)

@[simp] theorem cTensorPower_approx
    (X : CReal) (d p : Nat) :
    (cTensorPower X d).approx p = qTensorPower (X.approx p) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change X.approx p * (cTensorPower X d).approx p =
        X.approx p * qTensorPower (X.approx p) d
      rw [ih]

/-- Finite Fubini factorization: a `d`-dimensional rectangular product sum
is the `d`-th power of the one-dimensional sum. -/
theorem tensorBoxMass_factor (f : Nat → Q') (M : Nat) :
    ∀ d, tensorBoxMass f d M ≈
      qTensorPower (finSum f M) d
  | 0 => Q'.eqv_refl 1
  | d + 1 => by
      refine Q'.eqv_trans _
        (finSum f M * tensorBoxMass f d M) _ ?_ ?_
      · exact Q'.eqv_symm
          (finSum_mul_const f (tensorBoxMass f d M) M)
      · exact Q'.mul_eqv_congr_left (finSum f M) _ _
          (tensorBoxMass_factor f M d)

/-- Semantic powers respect rational equivalence. -/
theorem qTensorPower_congr {x y : Q'} (h : x ≈ y) :
    ∀ d, qTensorPower x d ≈ qTensorPower y d
  | 0 => Q'.eqv_refl 1
  | d + 1 => by
      refine Q'.eqv_trans _
        (y * qTensorPower x d) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right x y
          (qTensorPower x d) h
      · exact Q'.mul_eqv_congr_left y _ _
          (qTensorPower_congr h d)

/-- The literal five-label Hilbert--Schmidt coefficient box for the heat
channel on `SU(2)^5`. -/
def fiveHolonomyHSBox (q : Q') (M : Nat) : Q' :=
  tensorBoxMass (channelCoeffSq q) 5 M

/-- The five-dimensional box factors as the fifth tensor power of the
one-coordinate heat Hilbert--Schmidt partial sum. -/
theorem fiveHolonomyHSBox_factor (q : Q') (M : Nat) :
    fiveHolonomyHSBox q M ≈
      qTensorPower (heatHSPartial q M) 5 :=
  tensorBoxMass_factor (channelCoeffSq q) M 5

/-! ## 3a. Exact fence against an invalid tensor-L2 shortcut -/

/-- The extractor-defined Haar square of the actual four-step fusion
carrier.  This is a small semantic carrier used only to compare the
nonlinear one-coordinate product with the independent tensor box below. -/
def nonlinearFiveFusedHaarL2SqQ (q : Q') (N : Nat) : Q' :=
  bareVacuumHaar
    (pmul (nonlinearFiveHeatCarrier q N)
      (nonlinearFiveHeatCarrier q N))

/-- The corresponding pointwise fifth-power Haar square. -/
def nonlinearFivePointwiseHaarL2SqQ (q : Q') (N : Nat) : Q' :=
  bareVacuumHaar
    (pmul
      (fivePointwiseProduct (heatPolynomial q N))
      (fivePointwiseProduct (heatPolynomial q N)))

/-- Exact fusion synthesis transports the nonlinear Haar square to the much
smaller pointwise polynomial computation. -/
theorem nonlinearFiveFusedHaarL2SqQ_eqv_pointwise
    (q : Q') (N : Nat) :
    nonlinearFiveFusedHaarL2SqQ q N ≈
      nonlinearFivePointwiseHaarL2SqQ q N := by
  exact bareVacuumHaar_congr
    (pmul_congr
      (nonlinearFiveHeatCarrier_eq_pointwise q N)
      (nonlinearFiveHeatCarrier_eq_pointwise q N))

/-- The exact rational pilot nome used by the counterexample. -/
def nonlinearTensorFenceHalf : Q' := Q'.mkPos 1 2 (by decide)

/-- Kernel-computed nonlinear Haar square at the first nontrivial heat
cutoff. -/
theorem nonlinearTensorFence_pointwise_exact :
    nonlinearFivePointwiseHaarL2SqQ nonlinearTensorFenceHalf 1 ≈
      Q'.mkPos 215753357 524288 (by decide) := by
  decide

/-- Kernel-computed independent five-label tensor box for the same two heat
labels. -/
theorem nonlinearTensorFence_box_exact :
    fiveHolonomyHSBox nonlinearTensorFenceHalf 2 ≈
      Q'.mkPos 9765625 1048576 (by decide) := by
  decide

/-- **Machine-checked obstruction.**  The nonlinear fused fifth-power Haar
square is not bounded by the independent five-coordinate tensor box, already
for `q = 1/2` and labels `0,1`.  Thus an all-label nonlinear completion
cannot be obtained from the five-label Hilbert--Schmidt tensor completion by
that direct domination; it needs a new weighted fusion-tail estimate. -/
theorem nonlinearFive_not_le_independentTensorBox :
    ¬ nonlinearFiveFusedHaarL2SqQ nonlinearTensorFenceHalf 1 ≤
      fiveHolonomyHSBox nonlinearTensorFenceHalf 2 := by
  intro h
  have hfused :
      nonlinearFiveFusedHaarL2SqQ nonlinearTensorFenceHalf 1 ≈
        Q'.mkPos 215753357 524288 (by decide) :=
    Q'.eqv_trans _ _ _
      (nonlinearFiveFusedHaarL2SqQ_eqv_pointwise
        nonlinearTensorFenceHalf 1)
      nonlinearTensorFence_pointwise_exact
  have hlarge :
      Q'.mkPos 215753357 524288 (by decide) ≤
        nonlinearFiveFusedHaarL2SqQ nonlinearTensorFenceHalf 1 :=
    Q'.ge_of_eqv hfused
  have hsmall :
      fiveHolonomyHSBox nonlinearTensorFenceHalf 2 ≤
        Q'.mkPos 9765625 1048576 (by decide) :=
    Q'.le_of_eqv nonlinearTensorFence_box_exact
  have hfalse :
      Q'.mkPos 215753357 524288 (by decide) ≤
        Q'.mkPos 9765625 1048576 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hlarge h) hsmall
  have hstrict :
      ¬ Q'.mkPos 215753357 524288 (by decide) ≤
        Q'.mkPos 9765625 1048576 (by decide) := by
    decide
  exact hstrict hfalse

/-! ## 4. Joint all-label Hilbert--Schmidt completion -/

/-- The completed five-coordinate Hilbert--Schmidt square. -/
def fiveHolonomyTensorHSSq (D : HeatChannelHSCutoff) : CReal :=
  cTensorPower (heatChannelHSSq D) 5

/-- Rational form of the shifted one-coordinate completion identity. -/
theorem shiftedHeatHSPartial_eqv_completionApprox
    (D : HeatChannelHSCutoff) (M : Nat) :
    heatHSPartial D.q (D.cutoff + M) ≈
      (heatChannelHSSq D).approx M := by
  show heatHSPartial D.q (D.cutoff + M) ≈
    squaredHead D + squaredTailPartial D M
  exact
    SU2HeatChannelHilbertSchmidtCompletion.finSum_split
      (channelCoeffSq D.q) D.cutoff M

/-- A shifted finite five-label box is termwise the approximation sequence
of the completed five-coordinate Hilbert--Schmidt square. -/
theorem shiftedFiveHolonomyHSBox_equiv_completionApprox
    (D : HeatChannelHSCutoff) (M : Nat) :
    CReal.Equiv
      (CReal.ofQ' (fiveHolonomyHSBox D.q (D.cutoff + M)))
      (CReal.ofQ' ((fiveHolonomyTensorHSSq D).approx M)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  change fiveHolonomyHSBox D.q (D.cutoff + M) ≈
    (fiveHolonomyTensorHSSq D).approx M
  refine Q'.eqv_trans _
    (qTensorPower (heatHSPartial D.q (D.cutoff + M)) 5) _
    (fiveHolonomyHSBox_factor D.q (D.cutoff + M)) ?_
  change qTensorPower (heatHSPartial D.q (D.cutoff + M)) 5 ≈
    (cTensorPower (heatChannelHSSq D) 5).approx M
  rw [cTensorPower_approx]
  exact qTensorPower_congr
    (shiftedHeatHSPartial_eqv_completionApprox D M) 5

/-- Cofinal five-label boxes converge to the completed joint square. -/
theorem shiftedFiveHolonomyHSBox_converges
    (D : HeatChannelHSCutoff) :
    CReal.ConvergesTo
      (fun M =>
        CReal.ofQ'
          (fiveHolonomyHSBox D.q (D.cutoff + M)))
      (fiveHolonomyTensorHSSq D) := by
  exact ChebOrthoMatrix.convergesTo_congr_seq
    (fun M => CReal.Equiv.symm
      (shiftedFiveHolonomyHSBox_equiv_completionApprox D M))
    (CReal.convergesTo_self (fiveHolonomyTensorHSSq D))

/-- **Joint five-holonomy all-label convergence.**  Every finite
five-dimensional coefficient box converges to the constructed
Hilbert--Schmidt square on the tensor-product Haar carrier. -/
theorem fiveHolonomyHSBox_converges
    (D : HeatChannelHSCutoff) :
    CReal.ConvergesTo
      (fun M => CReal.ofQ' (fiveHolonomyHSBox D.q M))
      (fiveHolonomyTensorHSSq D) := by
  apply convergesTo_of_fixedShift D.cutoff
  simpa [Nat.add_comm] using shiftedFiveHolonomyHSBox_converges D

/-! ## 5. Stability under grouped heat-time rescaling -/

/-- Strict positivity of the repository's recursive heat power. -/
theorem qpow_pos_local {q : Q'} (hq : (0 : Q') < q) :
    ∀ n, (0 : Q') < qpow q n
  | 0 => by
      change (0 : Q') < 1
      decide
  | n + 1 => Q'.mul_pos (qpow_pos_local hq n) hq

/-- A positive finite heat corridor preserves the certified all-label
cutoff: replacing `q` by `q^steps` can only decrease the tail ratio. -/
def groupedHeatHSCutoff
    (D : HeatChannelHSCutoff) (steps : Nat) (hsteps : 1 ≤ steps) :
    HeatChannelHSCutoff where
  q := qpow D.q steps
  q_pos := by
    exact qpow_pos_local D.q_pos steps
  q_le_one := by
    exact qpow_le_one (Q'.le_of_lt D.q_pos) D.q_le_one steps
  cutoff := D.cutoff
  cutoff_one := D.cutoff_one
  ratio_lt_one := by
    have hgroup_le :
        qpow D.q steps ≤ D.q := by
      cases steps with
      | zero => omega
      | succ k =>
          exact qpow_succ_le_self
            (Q'.le_of_lt D.q_pos) D.q_le_one k
    have hgroup0 : (0 : Q') ≤ qpow D.q steps :=
      qpow_nonneg D.q (Q'.le_of_lt D.q_pos) steps
    have hp :
        (qpow D.q steps) ^ (2 * (D.cutoff + 1))
          ≤ D.q ^ (2 * (D.cutoff + 1)) :=
      CRealLog.pow_le_pow_base
        (qpow D.q steps) D.q hgroup0 hgroup_le _
    have hratio :
        channelRatio (qpow D.q steps) D.cutoff
          ≤ channelRatio D.q D.cutoff :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hp (by decide)
    exact HeatKernelGap.lt_of_le_of_lt hratio D.ratio_lt_one

/-- Completed five-coordinate Hilbert--Schmidt square after a positive
finite grouped heat corridor. -/
def groupedFiveHolonomyTensorHSSq
    (D : HeatChannelHSCutoff) (steps : Nat) (hsteps : 1 ≤ steps) : CReal :=
  fiveHolonomyTensorHSSq (groupedHeatHSCutoff D steps hsteps)

/-- **Joint all-label/rescaling convergence.**  For every positive finite
grouping length, the five-coordinate boxes at the exact semigroup coordinate
`q^steps` converge to a genuine CReal Hilbert--Schmidt square, with the same
certified character cutoff. -/
theorem groupedFiveHolonomyHSBox_converges
    (D : HeatChannelHSCutoff) (steps : Nat) (hsteps : 1 ≤ steps) :
    CReal.ConvergesTo
      (fun M =>
        CReal.ofQ'
          (fiveHolonomyHSBox (qpow D.q steps) M))
      (groupedFiveHolonomyTensorHSSq D steps hsteps) :=
  fiveHolonomyHSBox_converges
    (groupedHeatHSCutoff D steps hsteps)

end YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt

#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.fiveFusionCarrier_eq_pointwise
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHeatCarrier_eq_pointwise
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarPacket_synthesizes_pointwise
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarRiemannSq_converges
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarL2Sq_nonneg
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.fiveHolonomyHSBox_factor
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveFusedHaarL2SqQ_eqv_pointwise
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearTensorFence_pointwise_exact
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearTensorFence_box_exact
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFive_not_le_independentTensorBox
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.fiveHolonomyHSBox_converges
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.groupedHeatHSCutoff
#print axioms YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt.groupedFiveHolonomyHSBox_converges
