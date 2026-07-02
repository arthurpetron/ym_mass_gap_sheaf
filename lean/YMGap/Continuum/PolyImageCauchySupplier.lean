/-
The `img` supplier for the continuous functional calculus — the representative-level
polynomial-image sequence `n ↦ pₙ(T)x` presented, choice-free, as the last unbuilt
field of `CompleteFCLimitData` (the `img : ∀ x, PolyImageCauchy …` datum feeding
`fcApply` / `dischargeBTC_complete`).

# What this module delivers

`PolyImageCauchy SL L pseq x` extends `GeneralCompletionCauchy SL.toGNSData` (fields
`pt`, `mod`, `cauchy`) with `represents : ∀ n, ⟦pt n⟧ = polyApply … (pseq n) x`.  The
operator-side (`pt` + `represents`) is the deliverable this module discharges GREEN;
the distance modulus (`mod` + `cauchy`) is the carried analytic residual.

  * **STEP A — the `pt` / `represents` half (GREEN).**
    `polyApplyLinCauchy` is the representative-level mirror of `polyApply`, built by
    the rep-level lifts `cSmulCauchy` (scalar), `TCauchy` (transfer), `cAddCauchy`
    (sum) and the base `constCauchy 0`.  `polyApplyLinCauchy_represents` proves
    `⟦polyApplyLinCauchy p xc⟧ = polyApply p ⟦xc⟧` by induction on `p`: the descent
    steps are `rfl` (`cSmul`/`cAdd` are `Quotient.lift`s) plus `LT.T_ofCauchy` for the
    transfer step.  This is exactly what the representative-level transfer lift
    unblocked.

  * **STEP B1 — the difference identification (GREEN).**
    `polyApplyLinCauchy_diff` identifies the completion difference of two polynomial
    images with the image of the difference polynomial:
    `cSub ⟦pₚ-image⟧ ⟦p_q-image⟧ = polyApply (psub (pseq p) (pseq q)) ⟦xc⟧`, from
    `represents` and `polyApply_psub` (the sole consumer of `ScalarSquareLaws`).

  * **STEP B4 — the reindexed distance modulus from an `RC` difference bound (GREEN).**
    `reindexedDistModulus_of_RCdiffBound` feeds a difference-form `RC`-order self-inner
    bound straight through `rcDistBridge`, emitting the `QMhat`-reindexed rational
    squared-distance modulus.  This wires the `polyNormBound → rcDistBridge` pipeline.

  * **The assembled supplier (GREEN wiring).**
    `polyImageCauchyOfCert` / `polyImageCauchyOfPointCert` / `img` combine STEP A with a
    named distance-cert residual to produce the `PolyImageCauchy` / `∀ x, PolyImageCauchy`
    datum — choice-free, since the point-cert carries its own representative.

# Honest scope — the named residual

`PolyImageDistCert` carries exactly the two `GeneralCompletionCauchy` analytic fields
(`mod` + `cauchy`) for the polynomial-image representatives.  Its genuine derivation is
the STEP B chain: B1 difference identity (proved) → B2 `polyNormBound` self-inner bound
→ B3 the finite-mode uniformly-Cauchy spectral-difference datum `Bq(p,q) → 0` (a
`SpectralUnifCauchy` per mode maxed over the finite resolved index set — carried as
data) → B4 `rcDistBridge` (proved) → B5 the `reindex`→raw `QMhat`-cofinality conversion.
B3 and B5 remain the two carried inputs; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.WilsonContinuousFC
import YMGap.Continuum.RCDistBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ContinuousFunctionalCalculusForm
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum
open YMGap.Continuum.WilsonContinuousFC

namespace YMGap.Continuum.PolyImageCauchySupplier

/-! ## STEP A — the representative-level polynomial image and its `represents` -/

/-- **The representative-level mirror of `polyApply`.**  `polyApplyLinCauchy p xc`
realizes `p(T)·(rep xc)` at the level of Cauchy representatives, in Horner form
`c₀·xc + T(c₁·xc + T(…))`, using the rep-level lifts `cSmulCauchy` (scalar action),
`LT.TCauchy` (transfer), `cAddCauchy` (sum), and the constant-zero base. -/
def polyApplyLinCauchy (SL : LinearSmulGNSData) (LT : LinearTransferOperator SL.toSmulGNSData) :
    QPoly.Poly → CauchyGNS SL.toGNSData → CauchyGNS SL.toGNSData
  | [], _ => constCauchy SL.toGNSData SL.toGNSData.zero
  | (c :: cs), xc =>
      SL.toGNSData.cAddCauchy (SL.toSmulGNSData.cSmulCauchy c xc)
        (LT.TCauchy (polyApplyLinCauchy SL LT cs xc))

/-- **STEP A — the represented point IS the polynomial image.**
`⟦polyApplyLinCauchy p xc⟧ = polyApply p ⟦xc⟧`.  Induction on `p`: the base is
`rfl` (`embedV D 0 = ⟦constCauchy D 0⟧`), and the cons step rewrites the transfer
descent `LT.T_ofCauchy` against the inductive image, the `cSmul`/`cAdd` descents
being `rfl` (both are `Quotient.lift`s). -/
theorem polyApplyLinCauchy_represents
    (SL : LinearSmulGNSData) (LT : LinearTransferOperator SL.toSmulGNSData)
    (p : QPoly.Poly) (xc : CauchyGNS SL.toGNSData) :
    Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT p xc)
      = polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator p
          (Quotient.mk (cauchySetoid SL.toGNSData) xc) := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
      show Quotient.mk (cauchySetoid SL.toGNSData)
            (SL.toGNSData.cAddCauchy (SL.toSmulGNSData.cSmulCauchy c xc)
              (LT.TCauchy (polyApplyLinCauchy SL LT cs xc)))
          = SL.toGNSData.cAdd
              (SL.toSmulGNSData.cSmul c (Quotient.mk (cauchySetoid SL.toGNSData) xc))
              (LT.toAdditiveTransferOperator.T
                (polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator cs
                  (Quotient.mk (cauchySetoid SL.toGNSData) xc)))
      rw [← ih, LT.T_ofCauchy (polyApplyLinCauchy SL LT cs xc)]
      rfl

/-! ## STEP B1 — the difference identification -/

/-- **STEP B1 — the completion difference of two polynomial images is the image of
the difference polynomial.**  `cSub ⟦pₚ-image⟧ ⟦p_q-image⟧ = polyApply (psub pₚ p_q) ⟦xc⟧`,
from `polyApplyLinCauchy_represents` (both legs) and `polyApply_psub` — the sole place
`ScalarSquareLaws` is consumed. -/
theorem polyApplyLinCauchy_diff
    (SL : LinearSmulGNSData) (SQ : ScalarSquareLaws SL)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData) (p q : Nat) :
    SL.toGNSData.cSub
        (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq p) xc))
        (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq q) xc))
      = polyApply SL.toSmulGNSData LT.toAdditiveTransferOperator
          (QPoly.psub (pseq p) (pseq q)) (Quotient.mk (cauchySetoid SL.toGNSData) xc) := by
  rw [polyApplyLinCauchy_represents SL LT (pseq p) xc,
      polyApplyLinCauchy_represents SL LT (pseq q) xc]
  exact (WilsonContinuousFC.polyApply_psub SL SQ LT (pseq p) (pseq q)
    (Quotient.mk (cauchySetoid SL.toGNSData) xc)).symm

/-! ## STEP B4 — the reindexed rational distance modulus from an `RC` difference bound -/

/-- **STEP B4 — the reindexed distance modulus.**  Given a difference-form `RC`-order
self-inner bound `⟨Δ,Δ⟩ ≤ Bq` on the difference `Δ = cSub ⟦pₚ-image⟧ ⟦p_q-image⟧`,
`rcDistBridge` delivers the `QMhat`-reindexed rational squared-distance modulus
`distSqQ ((pₚ-image)_{reindex n}) ((p_q-image)_{reindex n}) ≤ Bq + ε`.  This wires the
`polyNormBound → rcDistBridge` half of the STEP B chain; only the `Bq → 0` spectral
datum (B3) and the `reindex`→raw conversion (B5) remain carried. -/
theorem reindexedDistModulus_of_RCdiffBound
    (SL : LinearSmulGNSData) (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData) (p q : Nat) (Bq : Q')
    (h : CReal.RCle
          (SL.toGNSData.cinnerCompl
            (SL.toGNSData.cSub
              (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq p) xc))
              (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq q) xc)))
            (SL.toGNSData.cSub
              (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq p) xc))
              (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq q) xc))))
          (Quotient.mk CReal.crealSetoid (CReal.ofQ' Bq))) :
    ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      SL.toGNSData.distSqQ
          ((polyApplyLinCauchy SL LT (pseq p) xc).seq
            (SL.toGNSData.reindex (polyApplyLinCauchy SL LT (pseq p) xc)
              (polyApplyLinCauchy SL LT (pseq q) xc) n))
          ((polyApplyLinCauchy SL LT (pseq q) xc).seq
            (SL.toGNSData.reindex (polyApplyLinCauchy SL LT (pseq p) xc)
              (polyApplyLinCauchy SL LT (pseq q) xc) n)) ≤ Bq + ε :=
  SL.toGNSData.rcDistBridge.toDistSqModulus
    (polyApplyLinCauchy SL LT (pseq p) xc) (polyApplyLinCauchy SL LT (pseq q) xc) Bq h

/-! ## The distance-cert residual and the assembled supplier -/

/-- **The carried distance modulus for the polynomial-image representatives** (STEP B,
`mod` + `cauchy`).  Its honest derivation is the STEP B chain (B1 proved → B2
`polyNormBound` → B3 `Bq → 0` spectral datum → B4 `rcDistBridge` proved → B5 reindex→raw);
B3 and B5 are the two carried inputs.  Here it is the named `Type`-level residual. -/
structure PolyImageDistCert (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData) : Type where
  /-- The distance-Cauchy modulus for the polynomial-image sequence. -/
  mod : Q' → Nat
  /-- Past `mod ε`, the rep-level squared distance of the images is eventually `≤ ε`. -/
  cauchy : ∀ ε : Q', (0 : Q') < ε → ∀ p q : Nat, mod ε ≤ p → mod ε ≤ q →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      SL.toGNSData.distSqQ
          ((polyApplyLinCauchy SL LT (pseq p) xc).seq n)
          ((polyApplyLinCauchy SL LT (pseq q) xc).seq n) ≤ ε

/-- **The per-representative supplier.**  STEP A (`pt` = `polyApplyLinCauchy`,
`represents` = `polyApplyLinCauchy_represents`) plus a distance cert assemble a genuine
`PolyImageCauchy` at the embedded representative `⟦xc⟧`. -/
def polyImageCauchyOfCert (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData)
    (cert : PolyImageDistCert SL LT pseq xc) :
    PolyImageCauchy SL LT.toAdditiveTransferOperator pseq
      (Quotient.mk (cauchySetoid SL.toGNSData) xc) where
  toGeneralCompletionCauchy :=
    { pt := fun n => polyApplyLinCauchy SL LT (pseq n) xc
      mod := cert.mod
      cauchy := cert.cauchy }
  represents := fun n => polyApplyLinCauchy_represents SL LT (pseq n) xc

/-- **A point-cert: a completion point together with a representative and a distance
cert for it.**  Carrying the representative makes the `∀ x` supplier choice-free (no
`Quotient.out`). -/
structure PolyImagePointCert (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (x : GNSCompletionSpace SL.toGNSData) : Type where
  /-- A chosen representative of `x`. -/
  xrep : CauchyGNS SL.toGNSData
  /-- The representative represents `x`. -/
  hrep : Quotient.mk (cauchySetoid SL.toGNSData) xrep = x
  /-- The distance cert at that representative. -/
  dist : PolyImageDistCert SL LT pseq xrep

/-- **The per-point supplier.**  From a point-cert, the `PolyImageCauchy` at `x` — the
represented points are the polynomial images at `x` (via `represents` and `hrep`). -/
def polyImageCauchyOfPointCert (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (x : GNSCompletionSpace SL.toGNSData)
    (R : PolyImagePointCert SL LT pseq x) :
    PolyImageCauchy SL LT.toAdditiveTransferOperator pseq x where
  toGeneralCompletionCauchy :=
    { pt := fun n => polyApplyLinCauchy SL LT (pseq n) R.xrep
      mod := R.dist.mod
      cauchy := R.dist.cauchy }
  represents := fun n => by
    rw [polyApplyLinCauchy_represents SL LT (pseq n) R.xrep, R.hrep]

/-- **The assembled `img` supplier.**  A family of point-certs (one per completion
point) produces the `img : ∀ x, PolyImageCauchy …` field of `CompleteFCLimitData`. -/
def img (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly)
    (cert : ∀ x : GNSCompletionSpace SL.toGNSData, PolyImagePointCert SL LT pseq x) :
    ∀ x : GNSCompletionSpace SL.toGNSData,
      PolyImageCauchy SL LT.toAdditiveTransferOperator pseq x :=
  fun x => polyImageCauchyOfPointCert SL LT pseq x (cert x)

end YMGap.Continuum.PolyImageCauchySupplier

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PolyImageCauchySupplier.polyApplyLinCauchy
#print axioms YMGap.Continuum.PolyImageCauchySupplier.polyApplyLinCauchy_represents
#print axioms YMGap.Continuum.PolyImageCauchySupplier.polyApplyLinCauchy_diff
#print axioms YMGap.Continuum.PolyImageCauchySupplier.reindexedDistModulus_of_RCdiffBound
#print axioms YMGap.Continuum.PolyImageCauchySupplier.polyImageCauchyOfCert
#print axioms YMGap.Continuum.PolyImageCauchySupplier.polyImageCauchyOfPointCert
#print axioms YMGap.Continuum.PolyImageCauchySupplier.img
