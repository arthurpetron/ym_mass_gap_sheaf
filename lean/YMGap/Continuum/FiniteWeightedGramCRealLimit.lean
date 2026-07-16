/-
# Passing exact finite Gram positivity to a constructive-real limit

Reflection positivity is first proved on finite rational approximants.  The
simultaneous cutoff/volume cylinder construction, however, is a `CReal`.  This
file supplies the small but load-bearing bridge between those levels.

If every approximation of a `CReal` is semantically equal to a nonnegative
rational quantity, then the constructive real is nonnegative both in the
development's one-slack order and in the sound eventual lower-bound predicate
`ExpPos.geRat`.  More robustly, `ExpPos.geRat _ 0` is proved closed under the
development's explicit `CReal.ConvergesTo` relation.  Specializing either form
to the finite weighted Gram quadratic form turns the exact Gram/SOS theorem
into limit-level positivity.

The finite state and channel lists, weights, amplitudes, and coefficients may
all vary with the approximation stage.  Consequently no fixed-cutoff or
fixed-volume assumption is hidden in the bridge.  Conversely, this theorem
does not construct a Cauchy modulus and does not identify a Yang--Mills
reflection summand with a Gram matrix; those are the two physical inputs that
must be derived elsewhere.
-/

import YMGap.Constructive.ExpPos
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.FiniteWeightedGramCRealLimit

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedGramSOS

local infix:50 " ≈ " => Q'.eqv

/-! ## Semantic-equality lower-bound transport -/

/-- Pointwise nonnegative rational representatives give nonnegativity in the
standard `CReal` one-slack order. -/
theorem creal_nonnegative_of_approx_eqv
    (x : CReal) (representative : Nat -> Q')
    (happrox : forall stage, x.approx stage ≈ representative stage)
    (hnonnegative : forall stage, (0 : Q') ≤ representative stage) :
    CReal.ofQ' 0 ≤ x := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact Q'.le_trans' _ _ _
    (hnonnegative stage)
    (Q'.le_of_eqv (Q'.eqv_symm (happrox stage)))

/-- The same pointwise representatives give the sound eventual lower bound
`x >= 0`, not merely the weak one-slack order. -/
theorem creal_geRat_zero_of_approx_eqv
    (x : CReal) (representative : Nat -> Q')
    (happrox : forall stage, x.approx stage ≈ representative stage)
    (hnonnegative : forall stage, (0 : Q') ≤ representative stage) :
    ExpPos.geRat x 0 := by
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun stage _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (hnonnegative stage)
    (Q'.le_of_eqv (Q'.eqv_symm (happrox stage)))

/-! ## Positivity through a genuine `ConvergesTo` limit -/

/-- Sound nonnegativity is closed under the development's explicit
`CReal.ConvergesTo` relation.  This is the robust limit bridge: the terms may
themselves be constructive reals and need only satisfy the sound eventual
lower-bound predicate.  No choice of a convergence modulus is extracted; the
given `ConvergesTo` proof is consumed propositionally at each tolerance. -/
theorem creal_geRat_zero_of_converges
    {sequence : Nat -> CReal} {limit : CReal}
    (hconverges : CReal.ConvergesTo sequence limit)
    (hnonnegative : forall stage, ExpPos.geRat (sequence stage) 0) :
    ExpPos.geRat limit 0 := by
  intro epsilon hepsilon
  have hhalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨stage, hstage⟩ := hconverges (HalfPow.half * epsilon) hhalf
  obtain ⟨approxStage, hclose⟩ := hstage stage (Nat.le_refl _)
  obtain ⟨nonnegativeStage, hnonnegativeStage⟩ :=
    hnonnegative stage (HalfPow.half * epsilon) hhalf
  refine ⟨max approxStage nonnegativeStage, fun index hindex => ?_⟩
  have hcloseIndex : approxStage ≤ index :=
    Nat.le_trans (Nat.le_max_left _ _) hindex
  have hnonnegativeIndex : nonnegativeStage ≤ index :=
    Nat.le_trans (Nat.le_max_right _ _) hindex
  have hterm : (0 : Q') ≤
      (sequence stage).approx index + HalfPow.half * epsilon :=
    hnonnegativeStage index hnonnegativeIndex
  have htoLimit : (sequence stage).approx index ≤
      limit.approx index + HalfPow.half * epsilon :=
    (hclose index hcloseIndex).1
  have hchain : (0 : Q') ≤
      (limit.approx index + HalfPow.half * epsilon) +
        HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ hterm
      (Q'.add_le_add_right _ _ (HalfPow.half * epsilon) htoLimit)
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv (limit.approx index)
        (HalfPow.half * epsilon) (HalfPow.half * epsilon))) ?_
  refine Q'.add_le_add_left _
    (HalfPow.half * epsilon + HalfPow.half * epsilon) epsilon ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves epsilon)

/-! ## Stage-varying finite weighted Grams -/

/-- If every approximation of `x` is exactly a finite weighted Gram quadratic
form with nonnegative enumerated channel weights, then `x` is nonnegative in
the standard `CReal` order.  All finite data are allowed to vary with `stage`.
-/
theorem weightedGramCReal_nonnegative
    {State Channel : Type}
    (x : CReal)
    (states : Nat -> List State)
    (channels : Nat -> List Channel)
    (channelWeight : Nat -> Channel -> Q')
    (amplitude : Nat -> State -> Channel -> Q')
    (coefficient : Nat -> State -> Q')
    (happrox : forall stage,
      x.approx stage ≈
        weightedGramQuadratic
          (states stage) (channels stage)
          (channelWeight stage) (amplitude stage) (coefficient stage))
    (hweight : forall stage channel, channel ∈ channels stage ->
      (0 : Q') ≤ channelWeight stage channel) :
    CReal.ofQ' 0 ≤ x :=
  creal_nonnegative_of_approx_eqv x
    (fun stage =>
      weightedGramQuadratic
        (states stage) (channels stage)
        (channelWeight stage) (amplitude stage) (coefficient stage))
    happrox
    (fun stage =>
      weightedGramQuadratic_nonnegative
        (states stage) (channels stage)
        (channelWeight stage) (amplitude stage) (coefficient stage)
        (hweight stage))

/-- Sound eventual-order version of `weightedGramCReal_nonnegative`.  This is
the form suitable for transport through `CReal.Equiv` and later OS/GNS order
arguments. -/
theorem weightedGramCReal_geRat_zero
    {State Channel : Type}
    (x : CReal)
    (states : Nat -> List State)
    (channels : Nat -> List Channel)
    (channelWeight : Nat -> Channel -> Q')
    (amplitude : Nat -> State -> Channel -> Q')
    (coefficient : Nat -> State -> Q')
    (happrox : forall stage,
      x.approx stage ≈
        weightedGramQuadratic
          (states stage) (channels stage)
          (channelWeight stage) (amplitude stage) (coefficient stage))
    (hweight : forall stage channel, channel ∈ channels stage ->
      (0 : Q') ≤ channelWeight stage channel) :
    ExpPos.geRat x 0 :=
  creal_geRat_zero_of_approx_eqv x
    (fun stage =>
      weightedGramQuadratic
        (states stage) (channels stage)
        (channelWeight stage) (amplitude stage) (coefficient stage))
    happrox
    (fun stage =>
      weightedGramQuadratic_nonnegative
        (states stage) (channels stage)
        (channelWeight stage) (amplitude stage) (coefficient stage)
        (hweight stage))

/-- Convergence-level version of finite weighted-Gram positivity.  Each stage
is the constant constructive real associated to its exact rational Gram form;
an independently derived `ConvergesTo` witness then transports positivity to
the target limit.  This is the form needed by a simultaneous cutoff/volume
cylinder construction: the physical work remains precisely the convergence
proof and the identification of its rational terms with these Gram forms. -/
theorem weightedGramCReal_geRat_zero_of_converges
    {State Channel : Type}
    (limit : CReal)
    (states : Nat -> List State)
    (channels : Nat -> List Channel)
    (channelWeight : Nat -> Channel -> Q')
    (amplitude : Nat -> State -> Channel -> Q')
    (coefficient : Nat -> State -> Q')
    (hconverges : CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        (weightedGramQuadratic
          (states stage) (channels stage)
          (channelWeight stage) (amplitude stage) (coefficient stage)))
      limit)
    (hweight : forall stage channel, channel ∈ channels stage ->
      (0 : Q') ≤ channelWeight stage channel) :
    ExpPos.geRat limit 0 := by
  apply creal_geRat_zero_of_converges hconverges
  intro stage
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun _ _ => ?_⟩
  exact weightedGramQuadratic_nonnegative
    (states stage) (channels stage)
    (channelWeight stage) (amplitude stage) (coefficient stage)
    (hweight stage)

end YMGap.Continuum.FiniteWeightedGramCRealLimit

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteWeightedGramCRealLimit.creal_nonnegative_of_approx_eqv
#print axioms YMGap.Continuum.FiniteWeightedGramCRealLimit.creal_geRat_zero_of_approx_eqv
#print axioms YMGap.Continuum.FiniteWeightedGramCRealLimit.creal_geRat_zero_of_converges
#print axioms YMGap.Continuum.FiniteWeightedGramCRealLimit.weightedGramCReal_nonnegative
#print axioms YMGap.Continuum.FiniteWeightedGramCRealLimit.weightedGramCReal_geRat_zero
#print axioms YMGap.Continuum.FiniteWeightedGramCRealLimit.weightedGramCReal_geRat_zero_of_converges
