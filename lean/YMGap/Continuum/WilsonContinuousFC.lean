/-
Retiring the operator side of core ④ (`fcApply`): the polynomial-LINEARITY chain
down to SUBTRACTION for the FORMED transfer operator `polyApply`, and the honest
reduction of `BoundedTransferCalculusResidual` for a polynomial-LIMIT symbol
`f = lim pₙ` to the two genuinely-analytic limit-passing facts.

# What this module adds (all axiom-clean)

`Continuum/ContinuousFunctionalCalculusForm.lean` FORMED `p(T)x = Σ_k cₖ·Tᵏx` and
proved it self-adjoint and (via `dischargeBTC`) norm-bounded for a FIXED polynomial
`p`.  `Continuum/ContinuousFCCarrierLimit.lean` proved the polynomial ADDITIVITY
`polyApply_padd` and built the carrier limit `fcApply := lim_n pₙ(T)x` from a
`PolyImageCauchy` supplier.  The remaining OPERATOR-side algebra was the linearity
to SUBTRACTION — the difference form `polyApply (p ⊖ q)` that the per-difference
distance-Cauchy estimate consumes.  That needs a scalar-COMPOSITION law and a
scalar-NEGATION law that neither `SmulGNSData` nor `LinearSmulGNSData` exposes.

  * **PART 1 — the two missing completion scalar laws.**  `cSmul_cSmul`
    (`(s·t)·x = s·(t·x)`) and `cSmul_negOne` (`(−1)·x = −x`), each a one-liner off
    a carrier module law descended through `rad_of_veq`.  Those carrier laws are
    NOT derivable from `smul_sub`/`smul_add_scalar` (there is no scalar-composition
    or scalar-negation law anywhere in the interface), so they are packaged as the
    `Type`-level datum `ScalarSquareLaws` — INHABITED (`qScalarSquareLaws`) by the
    `Q'`-weighted module, where the two laws are `Q'` `mul_assoc` and `(−1)·a = −a`.

  * **PART 2 — polynomial linearity to subtraction.**  `polyApply_pscale`
    (`polyApply (c·p) = c·polyApply p`), `polyApply_pneg`
    (`polyApply (−p) = −polyApply p`), and the load-bearing `polyApply_psub`
    (`polyApply (p ⊖ q) = polyApply p ⊖ polyApply q`).  `pscale` is by induction
    (cons step: `cSmul_cSmul` + `T_smul` + `cSmul_cAdd`); `pneg`/`psub` compose it
    with `cSmul_negOne` and the reused `polyApply_padd`.

  * **PART 3 — the honest continuous-`f` reduction.**  `ContinuousFCLimitData`
    packages, for a uniformly-Cauchy polynomial sequence `pseq`, a per-point
    `PolyImageCauchy` supplier and the TWO limit-passing facts of the carrier limit
    `fcApply` (self-adjointness and the operator-norm bound).  `dischargeBTC_limit`
    turns that datum into a `BoundedTransferCalculusResidual` whose operator is the
    GENUINE limit `fun x => fcApply (img x)` — a strict upgrade over `dischargeBTC`
    (fixed `p`).  The two carried facts are exactly the RC-Cauchy–Schwarz /
    limit-continuity residual named honestly in `ContinuousFCCarrierLimit.lean`; we
    do not fake them.

# Honest scope

Genuinely proved: the whole linearity-to-subtraction chain (Parts 1–2) and its
non-vacuity.  Genuinely REDUCED (not closed): the continuous-`f` calculus, whose
sole open content is now the two `fcApply` limit-passing facts — carried as
explicit `Type`-level fields, inhabited nowhere here (they need the deliberately
undeveloped RC inner-product Cauchy–Schwarz).  Nothing is faked.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.ContinuousFCCarrierLimit
import YMGap.Continuum.LinearTransferOperator
import YMGap.Continuum.BoundedTransferCalculus

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ContinuousFunctionalCalculusForm
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.WilsonContinuousFC

/-! ## Part 1 — the two missing completion scalar laws -/

/-- **The scalar-square module laws** absent from `LinearSmulGNSData`: the
scalar-COMPOSITION `(s·t)·a ≈ s·(t·a)` and the scalar-NEGATION `(−1)·a ≈ −a`.
Neither follows from `smul_sub`/`smul_add_scalar`; packaged here as `Type`-level
data (parallel to how `smul_add_scalar` was introduced), inhabited by the
`Q'`-weighted module below. -/
structure ScalarSquareLaws (SL : LinearSmulGNSData) : Type where
  /-- Scalar composition `(s·t)·a ≈ s·(t·a)`. -/
  mulLaw : ∀ (s t : Q') (a : SL.toGNSData.V),
    SL.toGNSData.veq (SL.toGNSData.smul (s * t) a)
      (SL.toGNSData.smul s (SL.toGNSData.smul t a))
  /-- Scalar negation at `−1`: `(−1)·a ≈ −a`. -/
  negOneLaw : ∀ (a : SL.toGNSData.V),
    SL.toGNSData.veq (SL.toGNSData.smul (-1) a) (SL.toGNSData.neg a)

/-- **Non-vacuity.**  The `Q'`-weighted module carries the scalar-square laws:
composition is `Q'` `mul_assoc`, and `(−1)·a = −a` is `neg_mul`/`one_mul`. -/
def qScalarSquareLaws (w : Q') (hw : (0 : Q') ≤ w) :
    ScalarSquareLaws (qLinearSmulGNS w hw) where
  mulLaw := fun s t a => Q'.mul_assoc_eqv s t a
  negOneLaw := fun a => Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))

/-- **Scalar composition on the completion.**  `(s·t)·x = s·(t·x)`, descended from
`mulLaw` through `rad_of_veq` (template = `cSmul_cAdd`). -/
theorem cSmul_cSmul (SL : LinearSmulGNSData) (SQ : ScalarSquareLaws SL)
    (s t : Q') (x : GNSCompletionSpace SL.toGNSData) :
    SL.toSmulGNSData.cSmul (s * t) x
      = SL.toSmulGNSData.cSmul s (SL.toSmulGNSData.cSmul t x) := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : SL.toGNSData.veq
      (SL.toGNSData.smul (s * t) (u.seq n))
      (SL.toGNSData.smul s (SL.toGNSData.smul t (u.seq n))) := SQ.mulLaw s t (u.seq n)
  exact le_of_eqv_le (rad_of_veq SL.toGNSData hva) (Q'.le_of_lt hε)

/-- **Scalar `−1` on the completion equals negation.**  `(−1)·x = −x`, descended
from `negOneLaw` through `rad_of_veq`. -/
theorem cSmul_negOne (SL : LinearSmulGNSData) (SQ : ScalarSquareLaws SL)
    (x : GNSCompletionSpace SL.toGNSData) :
    SL.toSmulGNSData.cSmul (-1) x = SL.toGNSData.cNeg x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : SL.toGNSData.veq
      (SL.toGNSData.smul (-1) (u.seq n)) (SL.toGNSData.neg (u.seq n)) := SQ.negOneLaw (u.seq n)
  exact le_of_eqv_le (rad_of_veq SL.toGNSData hva) (Q'.le_of_lt hε)

/-- **`c·0 = 0` on the completion.**  Needed for the `pscale` base case, descended
from the carrier law `smul_zero`. -/
theorem cSmul_embedZero (SL : LinearSmulGNSData) (c : Q') :
    SL.toSmulGNSData.cSmul c (embedV SL.toGNSData SL.toGNSData.zero)
      = embedV SL.toGNSData SL.toGNSData.zero := by
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : SL.toGNSData.veq
      (SL.toGNSData.smul c SL.toGNSData.zero) SL.toGNSData.zero := SL.toSmulGNSData.smul_zero c
  exact le_of_eqv_le (rad_of_veq SL.toGNSData hva) (Q'.le_of_lt hε)

/-! ## Part 2 — polynomial linearity to subtraction -/

/-- **`polyApply` scales in the polynomial.**  `polyApply (c·p) x = c·polyApply p x`.
Induction on `p`; the cons step uses `cSmul_cSmul`, scalar-homogeneity `T_smul`,
and the scalar/`cAdd` distributivity `cSmul_cAdd`. -/
theorem polyApply_pscale (SL : LinearSmulGNSData) (SQ : ScalarSquareLaws SL)
    (LT : LinearTransferOperator SL.toSmulGNSData) (c : Q') :
    ∀ (p : QPoly.Poly) (x : GNSCompletionSpace SL.toGNSData),
      polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (QPoly.pscale c p) x
        = SL.toSmulGNSData.cSmul c
            (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator p x) := by
  have hTs : ∀ (r : Q') (y : GNSCompletionSpace SL.toGNSData),
      LT.toAdditiveTransferOperator.T (SL.toSmulGNSData.cSmul r y)
        = SL.toSmulGNSData.cSmul r (LT.toAdditiveTransferOperator.T y) := LT.T_smul
  intro p
  induction p with
  | nil =>
      intro x
      exact (cSmul_embedZero SL c).symm
  | cons a p ih =>
      intro x
      show SL.toGNSData.cAdd (SL.toSmulGNSData.cSmul (c * a) x)
            (LT.toAdditiveTransferOperator.T
              (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (QPoly.pscale c p) x))
          = SL.toSmulGNSData.cSmul c
              (SL.toGNSData.cAdd (SL.toSmulGNSData.cSmul a x)
                (LT.toAdditiveTransferOperator.T
                  (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator p x)))
      rw [ih x, cSmul_cSmul SL SQ c a x, hTs c, SL.toSmulGNSData.cSmul_cAdd c]

/-- **`polyApply` negates in the polynomial.**  `polyApply (−p) x = −polyApply p x`,
via `polyApply_pscale` at `c = −1` and `cSmul_negOne`. -/
theorem polyApply_pneg (SL : LinearSmulGNSData) (SQ : ScalarSquareLaws SL)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (p : QPoly.Poly) (x : GNSCompletionSpace SL.toGNSData) :
    polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (QPoly.pneg p) x
      = SL.toGNSData.cNeg
          (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator p x) := by
  show polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (QPoly.pscale (-1) p) x
    = SL.toGNSData.cNeg (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator p x)
  rw [polyApply_pscale SL SQ LT (-1) p x, cSmul_negOne SL SQ]

/-- **`polyApply` subtracts in the polynomial (load-bearing).**
`polyApply (p ⊖ q) x = polyApply p x ⊖ polyApply q x` — the difference form the
per-difference distance-Cauchy estimate consumes.  `psub = padd _ (pneg _)`, so
this is `polyApply_padd` composed with `polyApply_pneg` (and `cSub := cAdd _ (cNeg _)`). -/
theorem polyApply_psub (SL : LinearSmulGNSData) (SQ : ScalarSquareLaws SL)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (p q : QPoly.Poly) (x : GNSCompletionSpace SL.toGNSData) :
    polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (QPoly.psub p q) x
      = SL.toGNSData.cSub
          (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator p x)
          (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator q x) := by
  show polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator (QPoly.padd p (QPoly.pneg q)) x
      = SL.toGNSData.cAdd
          (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator p x)
          (SL.toGNSData.cNeg
            (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator q x))
  rw [ContinuousFCCarrierLimit.polyApply_padd SL LT.toAdditiveTransferOperator x p (QPoly.pneg q),
      polyApply_pneg SL SQ LT q x]

/-! ## Part 3 — the honest continuous-`f` reduction -/

/-- **The continuous-`f` calculus datum for a polynomial-LIMIT symbol.**  For a
(uniformly-Cauchy) polynomial sequence `pseq`, a per-point `PolyImageCauchy`
supplier — so `fcApply (img x) = lim_n pₙ(T)x` is a genuine carrier point — plus a
uniform squared bound `M` and the TWO limit-passing facts of `fcApply`
(self-adjointness and the operator-norm bound `‖f(T)x‖² ≤ M·‖x‖²`).  Those two
facts are the RC-Cauchy–Schwarz / limit-continuity residual, carried honestly as
data (not derived — the RC inner product is deliberately undeveloped). -/
structure ContinuousFCLimitData (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (model : SpectralModel) (gap : LocatedSpectralGap model) : Type where
  /-- The uniformly-Cauchy polynomial sequence approximating `f`. -/
  pseq : Nat → QPoly.Poly
  /-- Per-point supplier: `n ↦ pₙ(T)x` presented as a distance-Cauchy sequence. -/
  img : ∀ x : GNSCompletionSpace SL.toGNSData,
    PolyImageCauchy SL LT.toAdditiveTransferOperator pseq x
  /-- The uniform squared operator-norm bound `M = (sup|f|)²`. -/
  normSqBound : Q'
  /-- `f(T)` self-adjoint (limit of the `pₙ(T)` self-adjointness). -/
  fcApply_selfAdjoint : ∀ x y : GNSCompletionSpace SL.toGNSData,
    SL.toGNSData.cinnerCompl (fcApply (img x)) y
      = SL.toGNSData.cinnerCompl x (fcApply (img y))
  /-- **Operator-norm bound** `‖f(T)x‖² ≤ M·‖x‖²` (limit of `polyNormBound`). -/
  fcApply_normBound : ∀ x : GNSCompletionSpace SL.toGNSData,
    RCle (SL.toGNSData.cinnerCompl (fcApply (img x)) (fcApply (img x)))
         (RCscale normSqBound (SL.toGNSData.cinnerCompl x x))

/-- **DISCHARGE of `BoundedTransferCalculusResidual` for a polynomial-LIMIT symbol.**
The bounded operator is the GENUINE carrier limit `fun x => fcApply (img x)`
(= `lim_n pₙ(T)x`), a strict upgrade over `dischargeBTC` (fixed `p`).
Self-adjointness and the norm bound are supplied by the two limit-passing facts of
`ContinuousFCLimitData`; nothing is faked. -/
def dischargeBTC_limit (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (model : SpectralModel) (gap : LocatedSpectralGap model)
    (C : ContinuousFCLimitData SL LT model gap) :
    BoundedTransferCalculusResidual
      (spectralGapDataOfL SL.toSmulGNSData LT.toAdditiveTransferOperator model gap) where
  normSqBound := C.normSqBound
  fT := fun x => fcApply (C.img x)
  fT_selfAdjoint := C.fcApply_selfAdjoint
  fT_normBound := C.fcApply_normBound

end YMGap.Continuum.WilsonContinuousFC

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonContinuousFC.qScalarSquareLaws
#print axioms YMGap.Continuum.WilsonContinuousFC.cSmul_cSmul
#print axioms YMGap.Continuum.WilsonContinuousFC.cSmul_negOne
#print axioms YMGap.Continuum.WilsonContinuousFC.cSmul_embedZero
#print axioms YMGap.Continuum.WilsonContinuousFC.polyApply_pscale
#print axioms YMGap.Continuum.WilsonContinuousFC.polyApply_pneg
#print axioms YMGap.Continuum.WilsonContinuousFC.polyApply_psub
#print axioms YMGap.Continuum.WilsonContinuousFC.dischargeBTC_limit
