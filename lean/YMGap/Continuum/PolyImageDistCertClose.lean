/-
Closing the `PolyImageDistCert` residual for the continuous functional calculus:
the B5 reindex→raw cofinality conversion, its B4∘B5 raw-index sibling, and the
assembly that inhabits `PolyImageDistCert` from a finite-mode spectral-difference
datum `SpectralDiffBound`.

# What this module discharges (GREEN)

  * **B5 — `GNSData.rawDistSqModulus_of_reindexed`.**  Converts a `QMhat`-reindexed
    rational squared-distance modulus (`distSqQ (u_{reindex n}) (v_{reindex n}) ≤ Bq+ε`)
    into the RAW-index modulus (`distSqQ (uₙ) (vₙ) ≤ Bq+ε`).  Runs entirely on the
    `QCauchy` two-sided bound and the cofinality `n ≤ QMhat r c n`
    (`self_le_QMhat`), tolerance-split `half·ε + half·ε ≃ ε`.  ~12 lines, all deps
    GREEN.

  * **B4∘B5 — `rawDistModulus_of_RCdiffBound`.**  The raw-index sibling of
    `reindexedDistModulus_of_RCdiffBound`: B5 applied to the already-GREEN B4 output.
    One line.

  * **Assembly — `polyImageDistCertOfSpectralDiffBound`.**  From a `SpectralDiffBound`
    it inhabits `PolyImageDistCert` unconditionally: the raw B4∘B5 modulus at tolerance
    `half·ε` gives `≤ Bq p q + half·ε`, and `Bq p q ≤ half·ε` (the `vanish` field)
    collapses it to `≤ ε` via `two_halves`.  Fully dischargeable.

# Honest scope — the single carried Type-level residual

  * **B3 — `SpectralDiffBound`.**  The finite-mode spectral-difference datum
    (`Bq : Nat → Nat → Q'` with an `RC`-order self-inner bound on each image difference
    `Δ p q` and a per-mode `Bq p q → 0` vanishing).  Its genuine construction from
    `ContinuousTransferCalculus.polyNormBound` (the `Fin Br.k` finite-max feeding
    `rcbound`) and `BernsteinStageData.bernsteinSpectralCauchyOfMOV` (per-mode
    `SpectralUnifCauchy` maxed over `Fin Br.k`, feeding `vanish`) is NOT done here; the
    structure is carried as the honest named Type-level residual.  Nothing is faked:
    everything downstream of `SpectralDiffBound` is proved.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.PolyImageCauchySupplier

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ContinuousFunctionalCalculusForm
open YMGap.Continuum.ContinuousFCCarrierLimit
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum
open YMGap.Continuum.WilsonContinuousFC
open YMGap.Continuum.PolyImageCauchySupplier

/-! ## B5 — the reindex→raw cofinality conversion (extends `GNSData`) -/

namespace YMGap.Continuum.GNSQuotient

namespace GNSData

variable (D : GNSData)

/-- **B5 — the reindex→raw cofinality conversion.**  A `QMhat`-reindexed rational
squared-distance modulus `distSqQ (u_{reindex n}) (v_{reindex n}) ≤ Bq + ε` (for every
`ε > 0`) upgrades to the RAW-index modulus `distSqQ (uₙ) (vₙ) ≤ Bq + ε`.

Proof: at tolerance `δ := half·ε`, obtain the reindexed cutoff `N0`.  Take
`N := max N0 (c.M δ)`; for `n ≥ N`, the diagonal cofinality `n ≤ QMhat r c n`
(`self_le_QMhat`) both feeds the reindexed bound at index `n`
(`r (QMhat r c n) ≤ Bq + δ`) and puts `QMhat r c n` past `c.M δ`, so the `QCauchy`
two-sided bound gives `r n ≤ r (QMhat r c n) + δ`.  Chaining yields
`r n ≤ (Bq + δ) + δ`, and `(δ + δ) ≃ ε` (`two_halves`) collapses this to `Bq + ε`. -/
theorem rawDistSqModulus_of_reindexed (u v : CauchyGNS D) (Bq : Q')
    (hre : ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
       D.distSqQ (u.seq (D.reindex u v n)) (v.seq (D.reindex u v n)) ≤ Bq + ε) :
    ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
       D.distSqQ (u.seq n) (v.seq n) ≤ Bq + ε := by
  intro ε hε
  have hδ : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N0, hN0⟩ := hre (HalfPow.half * ε) hδ
  refine ⟨max N0 ((D.distSqSeqCauchy u v).M (HalfPow.half * ε)), fun n hn => ?_⟩
  have hnN0 : N0 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnM : (D.distSqSeqCauchy u v).M (HalfPow.half * ε) ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  -- reindexed bound at index n :  r (QMhat r c n) ≤ Bq + δ
  have h1 : D.distSqQ (u.seq (D.reindex u v n)) (v.seq (D.reindex u v n))
      ≤ Bq + HalfPow.half * ε := hN0 n hnN0
  -- diagonal cofinality :  n ≤ QMhat r c n = reindex u v n
  have hself : n ≤ D.reindex u v n :=
    CReal.self_le_QMhat (fun k => D.distSqQ (u.seq k) (v.seq k))
      (D.distSqSeqCauchy u v) n
  have hnQ : (D.distSqSeqCauchy u v).M (HalfPow.half * ε) ≤ D.reindex u v n :=
    Nat.le_trans hnM hself
  -- QCauchy two-sided bound :  r n ≤ r (QMhat r c n) + δ
  have h2 : D.distSqQ (u.seq n) (v.seq n)
      ≤ D.distSqQ (u.seq (D.reindex u v n)) (v.seq (D.reindex u v n))
          + HalfPow.half * ε :=
    ((D.distSqSeqCauchy u v).bound (HalfPow.half * ε) hδ n (D.reindex u v n)
      hnM hnQ).1
  -- chain and collapse the two halves
  have h3 : D.distSqQ (u.seq n) (v.seq n)
      ≤ (Bq + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ h2 (Q'.add_le_add_right _ _ (HalfPow.half * ε) h1)
  have heqv : ((Bq + HalfPow.half * ε) + HalfPow.half * ε).eqv (Bq + ε) :=
    Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv Bq (HalfPow.half * ε) (HalfPow.half * ε))
      (Q'.add_eqv_congr_left Bq _ ε (ExpNeg.two_halves ε))
  exact le_of_le_eqv h3 heqv

end GNSData

end YMGap.Continuum.GNSQuotient

namespace YMGap.Continuum.PolyImageDistCertClose

/-! ## B4∘B5 — the raw-index sibling of `reindexedDistModulus_of_RCdiffBound` -/

/-- The completion difference of the two polynomial images (`Δ p q` of the postulate). -/
def imgDiff (SL : LinearSmulGNSData) (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData) (p q : Nat) :
    GNSCompletionSpace SL.toGNSData :=
  SL.toGNSData.cSub
    (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq p) xc))
    (Quotient.mk (cauchySetoid SL.toGNSData) (polyApplyLinCauchy SL LT (pseq q) xc))

/-- **B4∘B5 — the raw-index distance modulus from an `RC` difference bound.**  B5
(`rawDistSqModulus_of_reindexed`) applied to the already-GREEN B4 output
(`reindexedDistModulus_of_RCdiffBound`): from the difference-form `RC`-order self-inner
bound on `Δ p q` it emits the RAW-index rational squared-distance modulus
`distSqQ ((pₚ-image)ₙ) ((p_q-image)ₙ) ≤ Bq + ε`. -/
theorem rawDistModulus_of_RCdiffBound
    (SL : LinearSmulGNSData) (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData) (p q : Nat) (Bq : Q')
    (h : CReal.RCle
          (SL.toGNSData.cinnerCompl (imgDiff SL LT pseq xc p q) (imgDiff SL LT pseq xc p q))
          (Quotient.mk CReal.crealSetoid (CReal.ofQ' Bq))) :
    ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      SL.toGNSData.distSqQ
          ((polyApplyLinCauchy SL LT (pseq p) xc).seq n)
          ((polyApplyLinCauchy SL LT (pseq q) xc).seq n) ≤ Bq + ε :=
  SL.toGNSData.rawDistSqModulus_of_reindexed
    (polyApplyLinCauchy SL LT (pseq p) xc) (polyApplyLinCauchy SL LT (pseq q) xc) Bq
    (reindexedDistModulus_of_RCdiffBound SL LT pseq xc p q Bq h)

/-! ## B3 — the carried finite-mode spectral-difference datum (Type-level residual) -/

/-- **B3 — the finite-mode spectral-difference datum** (the honest carried Type-level
residual).  A rational bound `Bq p q` on each polynomial-image difference `Δ p q`,
witnessed by an `RC`-order self-inner bound (`rcbound`) and vanishing uniformly past a
modulus (`vanish`).  Its genuine construction feeds `rcbound` from
`ContinuousTransferCalculus.polyNormBound` (the `Fin Br.k` finite spectral max) and
`vanish` from `BernsteinStageData.bernsteinSpectralCauchyOfMOV` (per-mode
`SpectralUnifCauchy` maxed over `Fin Br.k`); that constructor is NOT provided here. -/
structure SpectralDiffBound (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData) : Type where
  /-- The per-pair rational spectral bound. -/
  Bq : Nat → Nat → Q'
  /-- The vanishing modulus. -/
  mod : Q' → Nat
  /-- The difference-form `RC`-order self-inner bound on `Δ p q`. -/
  rcbound : ∀ p q : Nat, CReal.RCle
    (SL.toGNSData.cinnerCompl (imgDiff SL LT pseq xc p q) (imgDiff SL LT pseq xc p q))
    (Quotient.mk CReal.crealSetoid (CReal.ofQ' (Bq p q)))
  /-- Uniform vanishing of the bound past `mod ε`. -/
  vanish : ∀ ε : Q', (0 : Q') < ε → ∀ p q : Nat, mod ε ≤ p → mod ε ≤ q → Bq p q ≤ ε

/-! ## Assembly — inhabiting `PolyImageDistCert` from a `SpectralDiffBound` -/

/-- **The assembly.**  A `SpectralDiffBound` inhabits `PolyImageDistCert`
unconditionally: at pair `(p,q)` past `mod (half·ε)`, the raw B4∘B5 modulus at tolerance
`half·ε` gives `distSqQ … ≤ Bq p q + half·ε`, and `vanish` gives `Bq p q ≤ half·ε`, so
`two_halves` collapses the sum to `≤ ε`. -/
def polyImageDistCertOfSpectralDiffBound (SL : LinearSmulGNSData)
    (LT : LinearTransferOperator SL.toSmulGNSData)
    (pseq : Nat → QPoly.Poly) (xc : CauchyGNS SL.toGNSData)
    (S : SpectralDiffBound SL LT pseq xc) :
    PolyImageDistCert SL LT pseq xc where
  mod := fun ε => S.mod (HalfPow.half * ε)
  cauchy := by
    intro ε hε p q hp hq
    have hδ : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
    have hBq : S.Bq p q ≤ HalfPow.half * ε := S.vanish _ hδ p q hp hq
    obtain ⟨N, hN⟩ :=
      rawDistModulus_of_RCdiffBound SL LT pseq xc p q (S.Bq p q) (S.rcbound p q)
        (HalfPow.half * ε) hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 : SL.toGNSData.distSqQ
        ((polyApplyLinCauchy SL LT (pseq p) xc).seq n)
        ((polyApplyLinCauchy SL LT (pseq q) xc).seq n)
        ≤ S.Bq p q + HalfPow.half * ε := hN n hn
    have h2 : S.Bq p q + HalfPow.half * ε ≤ HalfPow.half * ε + HalfPow.half * ε :=
      Q'.add_le_add_right _ _ (HalfPow.half * ε) hBq
    exact le_of_le_eqv (Q'.le_trans' _ _ _ h1 h2) (ExpNeg.two_halves ε)

end YMGap.Continuum.PolyImageDistCertClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GNSQuotient.GNSData.rawDistSqModulus_of_reindexed
#print axioms YMGap.Continuum.PolyImageDistCertClose.imgDiff
#print axioms YMGap.Continuum.PolyImageDistCertClose.rawDistModulus_of_RCdiffBound
#print axioms YMGap.Continuum.PolyImageDistCertClose.polyImageDistCertOfSpectralDiffBound
