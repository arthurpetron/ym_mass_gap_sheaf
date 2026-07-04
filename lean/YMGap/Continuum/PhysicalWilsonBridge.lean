/-
The **physical single-bond Wilson Peter–Weyl bridge** and the honest reduction of
the full arbitrary-`x` `CharacterDiagResolution` on the PHYSICAL `cinner`.

# The three tiers (design + honest scope)

The finite-volume Wilson operator-form gap is gated by
`WilsonSpectralBridge.CharacterDiagResolution op R w N` — a Parseval / character
diagonalization datum realized INSIDE the completed GNS inner product
`H.hilbert.cinner`.  This module discharges the SINGLE-BOND piece completely
(modulo one elementary analytic primitive) and REDUCES the arbitrary-`x` piece to
exactly the two named obligations that the rational/irrational codomain mismatch
forces.

## Tier 1 — single-bond basis level: CLOSED (modulo `AngleCosineIntegral`)

The single-bond physical two-site reflection pairing, reconstructed from the
double-Haar Schur orthogonality times the weight character-expansion, is proved
equal to the char-diagonal `charHilbert.cinner` on the character basis:

    physPairing C t ht m n  =  reflWeight t ht (m+1) · charOrtho C m n
                            =  (weight expansion) × (double-Haar Schur ½(J_{|m−n|}−J_{m+n+2}))
                            =  charHilbert.cinner (basisVec m) (basisVec n).

`physicalWilsonPeterWeyl` is exactly this identity (a restatement of
`HaarClassIntegral.physPairing_eq_cinner`); composed with the diagonal collapse it
gives `δ_{mn}·⟦reflWeight(m+1)⟧` and INHABITS
`WilsonCharBridge.PhysicalReflectionSchurBridge` from the sole primitive
`AngleCosineIntegral` (`J_k = (2/π)∫₀^π cos kθ dθ = 2δ_{k0}`, i.e. `sin(kπ)=0` —
`cos` of a `CReal` multiple-of-π angle).  Nothing new analytic is required.

## Product-assembly — the free decoupled product-of-single-bonds

On a separable character observable `⊗_p χ_{m_p}` the free (decoupled) product
functional factorizes edge-by-edge, so the multi-bond reflection pairing is the
`K`-fold product of the Tier-1 single-bond pairing:

    Π_{e<K} physPairing C t ht (m e) (n e)
       =  (all edges diagonal)  Π_{e<K} reflWeight t ht (m e + 1),
       =  (some edge off-diag)  0.

`cprod_physPairing_diag` / `cprod_physPairing_offdiag` prove exactly this over the
`CReal` product `cprod`.  The INTERACTING plaquette insertion `w = e^{−S_Λ}` is
NOT in this decoupled factorization: it is carried as the OS2 datum
`ReferenceWeight.weighted_pos` / `prodReferenceWeight`'s `hOS2` — the honest
"too heavy" part, correctly isolated as a named field, not opened here.

## Tier 2 — arbitrary-`x` Parseval on the physical `cinner`: REDUCED, not closed

`CharacterDiagResolution` needs the two Parseval identities for ARBITRARY `x`, not
just basis vectors.  Two honest residuals block equality on the *physical*
`cinner`:

  * **(A) linear extension / physical coordinate map.**  Extending the basis
    identity to `x = Σ_m c_m χ_m` needs a character Fourier coordinate map `coord`
    on the physical Wilson carrier plus the bilinear expansion through
    `E_Λ`-linearity and off-diagonal orthogonality.  We name this exactly as the
    Type-level datum `PhysicalCharacterCoordinateMap` (the two Schur identities in
    `cinner`).  `physicalCharacterDiagResolution` shows this ONE datum discharges
    the ENTIRE `CharacterDiagResolution` (via
    `CharacterDiagResolutionProof.wilsonCharacterDiagResolution`).

  * **(B) rational/irrational codomain mismatch — the crux.**  `parseval_self`
    demands `⟦E_Λ(x*·x)⟧ = Σ_i ⟦reflWeight(i+1)·c_i²⟧`.  The LHS is a RATIONAL
    class (`E_Λ : Q'`, rational Boltzmann weights + rational Haar moments); the RHS
    is genuinely IRRATIONAL (`reflWeight = e^{−t·C₂}` is a `CReal`).  Exact
    equality is therefore UNSATISFIABLE for any rational-weight `ReferenceWeight`.
    It holds only if the Boltzmann weight IS the heat kernel — a `CReal`-valued
    heat-kernel single-edge reference weight, which does not exist in the
    codebase.  We name this obstruction as `HeatKernelReferenceWeight` (the
    `CReal`-valued single-edge moment) — deliberately NOT inhabited; the physical
    `cinner` must NOT be re-pointed at a `Q'`-valued `E_Λ` to paper over it.

`PhysicalCharacterCoordinateMap` is therefore the load-bearing frontier datum: for
the physical (rational-`E_Λ`) Wilson `H`, its `schur_self` field is the
unsatisfiable equality of crux (B).  It is parametric in `H` (so satisfiable for
the character model) and is deliberately NOT inhabited here.

# Honest verdict

  * **Single bond — CLOSED** modulo the sole primitive `AngleCosineIntegral`
    (`physicalWilsonPeterWeyl`, `physicalReflectionSchurBridge_of_primitive`).
  * **Full arbitrary-`x` `CharacterDiagResolution` on the physical `cinner` —
    REDUCED, not closed**, to exactly `PhysicalCharacterCoordinateMap`
    (residual A, which discharges the whole datum by
    `physicalCharacterDiagResolution`) with the load-bearing obstruction
    `HeatKernelReferenceWeight` (residual B, the rational→irrational weight
    mismatch that makes the equality form structurally unsatisfiable for the
    rational `E_Λ`).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`, no
`native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.HaarClassIntegral
import YMGap.Continuum.CharacterDiagResolutionProof

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.RCScaleClose
open YMGap.Continuum.WilsonCharBridge
open YMGap.Continuum.WilsonSchurIdentities
open YMGap.Continuum.HaarClassIntegral

namespace YMGap.Continuum.PhysicalWilsonBridge

/-! ## 1. Tier 1 — the physical single-bond Peter–Weyl bridge (CLOSED mod primitive)

`physicalWilsonPeterWeyl` is the single-bond physical reflection pairing
identified with the char-diagonal `cinner` — a restatement of the sharpest named
single-bond datum `HaarClassIntegral.physPairing_eq_cinner`.  Nothing new analytic
is required; the sole residual is the elementary cosine-integral primitive
`AngleCosineIntegral`. -/

/-- **The physical single-bond Wilson Peter–Weyl identity.**  The physical
two-site reflection pairing on the character basis (weight char-expansion ×
double-Haar Schur orthogonality, reconstructed from the cosine-integral primitive
`C`) equals the char-diagonal `charHilbert.cinner`.  Restatement of
`HaarClassIntegral.physPairing_eq_cinner`. -/
theorem physicalWilsonPeterWeyl
    (C : AngleCosineIntegral) (t : Q') (ht : (0 : Q') ≤ t) (N m n : Nat)
    (hm : m < N) (hn : n < N) :
    Quotient.mk CReal.crealSetoid (physPairing C t ht m n)
      = (charHilbert t ht N).cinner (basisVec m) (basisVec n) :=
  physPairing_eq_cinner C t ht N m n hm hn

/-- **The single-bond diagonalization.**  `physicalWilsonPeterWeyl` collapses to
`δ_{mn}·⟦reflWeight(m+1)⟧` — the diagonal single-slice reflection weight. -/
theorem physicalWilsonPeterWeyl_diagonal
    (C : AngleCosineIntegral) (t : Q') (ht : (0 : Q') ≤ t) (N m n : Nat)
    (hm : m < N) (hn : n < N) :
    Quotient.mk CReal.crealSetoid (physPairing C t ht m n)
      = if m = n then Quotient.mk CReal.crealSetoid (reflWeight t ht (m + 1))
        else Quotient.mk CReal.crealSetoid CReal.czero := by
  rw [physicalWilsonPeterWeyl C t ht N m n hm hn,
      charHilbert_cinner_basis_orthogonal t ht N m n hm hn]

/-- **The physical reflection / Schur–Haar bridge, INHABITED from the primitive.**
Given the cosine-angle-integral primitive `C`, the single-bond physical reflection
functional realizes the `PhysicalReflectionSchurBridge` residual (re-export of
`HaarClassIntegral.physical_bridge_of_primitive`). -/
def physicalReflectionSchurBridge_of_primitive
    (C : AngleCosineIntegral) (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) :
    PhysicalReflectionSchurBridge t ht N :=
  physical_bridge_of_primitive C t ht N

/-! ## 2. `CReal` finite products (for the free product-assembly) -/

/-- `0·A ≃ 0` (from `A·0 ≃ 0` and commutativity). -/
theorem czero_mul (A : CReal) : CReal.Equiv (CReal.mul CReal.czero A) CReal.czero :=
  CReal.Equiv.trans (CRealAlg.cmul_comm CReal.czero A)
    (HaarClassIntegral.mul_czero A)

/-- Full multiplicative congruence: `A ≃ A'`, `B ≃ B' ⇒ A·B ≃ A'·B'`. -/
theorem cmul_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B') :=
  CReal.Equiv.trans (CReal.mul_congr_left hA)
    (HaarClassIntegral.cmul_congr_right hB)

/-- **The finite `CReal` product** `cprod f K = Π_{i<K} f i`, left-folded from
`1`. -/
def cprod (f : Nat → CReal) : Nat → CReal
  | 0 => CReal.ofQ' (1 : Q')
  | k + 1 => CReal.mul (cprod f k) (f k)

/-- **Factorwise congruence of the product.**  If `f i ≃ g i` for every `i < K`
then `cprod f K ≃ cprod g K`. -/
theorem cprod_congr (f g : Nat → CReal) :
    ∀ K, (∀ i, i < K → CReal.Equiv (f i) (g i)) → CReal.Equiv (cprod f K) (cprod g K)
  | 0, _ => CReal.Equiv.refl _
  | K + 1, hK =>
      cmul_congr
        (cprod_congr f g K (fun i hi => hK i (Nat.lt_succ_of_lt hi)))
        (hK K (Nat.lt_succ_self K))

/-- **A zero factor kills the whole product.**  If `f j ≃ 0` for some `j < K`
then `cprod f K ≃ 0`. -/
theorem cprod_zero_of_factor (f : Nat → CReal) :
    ∀ K j, j < K → CReal.Equiv (f j) CReal.czero → CReal.Equiv (cprod f K) CReal.czero
  | 0, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | K + 1, j, hj, hz => by
      rcases Nat.lt_or_ge j K with hlt | hge
      · -- j < K: the tail product already vanishes; fold the top factor
        have ih := cprod_zero_of_factor f K j hlt hz
        exact CReal.Equiv.trans (CReal.mul_congr_left ih)
          (czero_mul (f K))
      · -- j = K: the top factor vanishes
        have hjK : j = K := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hge
        subst hjK
        exact CReal.Equiv.trans (HaarClassIntegral.cmul_congr_right hz)
          (HaarClassIntegral.mul_czero (cprod f j))

/-! ## 3. Product-assembly: the free decoupled product-of-single-bonds

The multi-bond physical reflection pairing on a separable character observable is
the `K`-fold product of the Tier-1 single-bond pairing.  (The interacting
plaquette insertion is NOT here — it is the named OS2 datum.) -/

/-- **Diagonal multi-bond product.**  If every edge is diagonal (`m e = n e` for
all `e < K`) the product of single-bond pairings collapses to the product of the
single-slice reflection weights. -/
theorem cprod_physPairing_diag
    (C : AngleCosineIntegral) (t : Q') (ht : (0 : Q') ≤ t) (m n : Nat → Nat)
    (K : Nat) (hd : ∀ e, e < K → m e = n e) :
    CReal.Equiv
      (cprod (fun e => physPairing C t ht (m e) (n e)) K)
      (cprod (fun e => reflWeight t ht (m e + 1)) K) :=
  cprod_congr _ _ K
    (fun e he => by
      have hmn : m e = n e := hd e he
      have := physPairing_diag C t ht (m e)
      -- physPairing (m e) (m e) ≃ reflWeight (m e + 1); rewrite n e ↦ m e
      rw [← hmn]
      exact this)

/-- **Off-diagonal multi-bond product.**  If some edge is off-diagonal
(`m e ≠ n e` for a witnessing `e < K`) the whole product vanishes. -/
theorem cprod_physPairing_offdiag
    (C : AngleCosineIntegral) (t : Q') (ht : (0 : Q') ≤ t) (m n : Nat → Nat)
    (K e : Nat) (he : e < K) (hne : m e ≠ n e) :
    CReal.Equiv (cprod (fun e => physPairing C t ht (m e) (n e)) K) CReal.czero :=
  cprod_zero_of_factor _ K e he (physPairing_offdiag C t ht hne)

/-! ## 4. Tier 2 — the physical arbitrary-`x` coordinate map (named residual A)

The whole `CharacterDiagResolution` on the physical `cinner` is REDUCED to ONE
datum: a character Fourier coordinate map on the physical Wilson carrier carrying
the two diagonal Schur / Peter–Weyl identities (the linear extension of the
single-bond identity through `E_Λ`-linearity).  For the physical (rational-`E_Λ`)
Wilson `H`, the `schur_self` field IS the unsatisfiable rational-vs-irrational
equality of crux (B); the datum is parametric in `H` and deliberately NOT
inhabited here. -/

/-- **The physical character coordinate map (named residual A).**  A finite
character Fourier coordinate map `coord` on the physical Wilson carrier, together
with the two diagonal Schur / Peter–Weyl identities realized inside the physical
`cinner`:

  * `schur_self` : `⟨x,x⟩  = Σ_{i<N} ⟦ reflWeight(i+1) · c_i² ⟧`;
  * `schur_T`    : `⟨Tx,x⟩ = Σ_{i<N} ⟦ (qpow w (c4(i+1))) · (reflWeight(i+1) · c_i²) ⟧`.

These are the linear extension (through `E_Λ`-linearity + off-diagonal
orthogonality) of the single-bond `physicalWilsonPeterWeyl` identity to arbitrary
`x = Σ_m c_m χ_m`.  For the physical rational-`E_Λ` Wilson `H`, `schur_self`
demands a RATIONAL class equal an IRRATIONAL sum — the crux-(B) obstruction — so
this datum is deliberately NOT inhabited. -/
structure PhysicalCharacterCoordinateMap
    {D : GNSData} (H : CompleteGNSHilbert D)
    (op : TransferOperator H) (w t : Q') (ht : (0 : Q') ≤ t) (N : Nat) : Type where
  /-- The physical character Fourier coordinate map `c_i = coord x i`. -/
  coord : H.hilbert.carrier → Fin N → Q'
  /-- Schur self-orthogonality realized in the physical `cinner`. -/
  schur_self : ∀ x, H.hilbert.cinner x x
      = CReal.RCfinSum N (fun i =>
          Quotient.mk CReal.crealSetoid
            (CReal.mul (reflWeight t ht (i.val + 1))
              (CReal.ofQ' (coord x i * coord x i))))
  /-- Diagonal transfer action realized in the physical `cinner`. -/
  schur_T : ∀ x, H.hilbert.cinner (op.T x) x
      = CReal.RCfinSum N (fun i =>
          Quotient.mk CReal.crealSetoid
            (CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1))))
              (CReal.mul (reflWeight t ht (i.val + 1))
                (CReal.ofQ' (coord x i * coord x i)))))

/-- **The whole `CharacterDiagResolution` REDUCED to residual A.**  Any inhabitant
of `PhysicalCharacterCoordinateMap` on the physical `H` discharges the entire
`CharacterDiagResolution op rcScaleResidualPlus w N` (via
`CharacterDiagResolutionProof.wilsonCharacterDiagResolution`).  So the arbitrary-`x`
Parseval datum on the physical `cinner` is exactly residual A. -/
def physicalCharacterDiagResolution
    {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w t : Q') (ht : (0 : Q') ≤ t) (N : Nat)
    (M : PhysicalCharacterCoordinateMap H op w t ht N) :
    CharacterDiagResolution op rcScaleResidualPlus w N :=
  CharacterDiagResolutionProof.wilsonCharacterDiagResolution
    op w t ht N M.coord M.schur_self M.schur_T

/-- **The physical operator-form gap, conditional on residual A.**  Given the
coordinate map `M` and the scalar-order monotonicity `Rscalar`, the finite-volume
Wilson operator-form gap fires: on `vac⊥`, `⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩`.
Composes `physicalCharacterDiagResolution` with the already-proved
`WilsonSpectralBridge.wilsonTransferFormGap`. -/
def physicalWilsonFormGap
    {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w t : Q') (ht : (0 : Q') ≤ t)
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (Rscalar : ∀ {s t : Q'}, s ≤ t → ∀ {c : CReal.RC}, CReal.RCnonneg c →
      CReal.RCle (rcScaleResidualPlus.RCscale s c) (rcScaleResidualPlus.RCscale t c))
    (M : PhysicalCharacterCoordinateMap H op w t ht N) :
    TransferFormGapResidual (excitedCharSpectralGapData op w hw0 hw1 N) :=
  wilsonTransferFormGap op w hw0 hw1 N rcScaleResidualPlus Rscalar
    (physicalCharacterDiagResolution op w t ht N M)

/-! ## 5. Tier 2 — the crux-(B) obstruction (named residual B, NOT inhabited)

The equality form of `schur_self` forces a RATIONAL class (`E_Λ : Q'`) to equal an
IRRATIONAL sum (`reflWeight = e^{−t·C₂}`).  This is satisfiable only if the
single-edge reference-weight moment is itself the `CReal`-valued heat kernel — a
`CReal`-valued reference weight whose single-edge moment equals `reflWeight`.  The
rational `ReferenceWeight.E_Λ` is the only inhabited instance, so this datum is
the load-bearing obstruction; it is deliberately NOT inhabited. -/

/-- **The heat-kernel reference weight (named residual B, NOT inhabited).**  A
`CReal`-valued single-edge reference weight whose spin-`(s+1)` moment `E s`
coincides with the genuine heat-kernel reflection coefficient
`reflWeight t ht (s+1) = e^{−t·C₂(s+1)}`, AND whose class agrees with the physical
rational finite-volume moment `physMoment s : Q'`.  The two fields are jointly
UNSATISFIABLE: `E s ≃ reflWeight (s+1)` is irrational while `E s ≃ ⟦physMoment s⟧`
is rational (a rational class cannot equal a nontrivial `e^{−·}`).  This records
the crux — the physical `cinner` must NOT be re-pointed at a `Q'`-valued `E_Λ` to
force the equality Parseval — as a named, deliberately-uninhabited Type-level
datum. -/
structure HeatKernelReferenceWeight (t : Q') (ht : (0 : Q') ≤ t) : Type where
  /-- The `CReal`-valued single-edge moment. -/
  E : Nat → CReal
  /-- The rational physical finite-volume moment it must ALSO match. -/
  physMoment : Nat → Q'
  /-- Heat-kernel identification: the moment is the irrational reflection weight. -/
  moment_heatKernel : ∀ s, CReal.Equiv (E s) (reflWeight t ht (s + 1))
  /-- Physical identification: the moment is the rational finite-volume value. -/
  moment_rational : ∀ s, CReal.Equiv (E s) (CReal.ofQ' (physMoment s))

end YMGap.Continuum.PhysicalWilsonBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PhysicalWilsonBridge.physicalWilsonPeterWeyl
#print axioms YMGap.Continuum.PhysicalWilsonBridge.physicalWilsonPeterWeyl_diagonal
#print axioms YMGap.Continuum.PhysicalWilsonBridge.physicalReflectionSchurBridge_of_primitive
#print axioms YMGap.Continuum.PhysicalWilsonBridge.cprod_congr
#print axioms YMGap.Continuum.PhysicalWilsonBridge.cprod_zero_of_factor
#print axioms YMGap.Continuum.PhysicalWilsonBridge.cprod_physPairing_diag
#print axioms YMGap.Continuum.PhysicalWilsonBridge.cprod_physPairing_offdiag
#print axioms YMGap.Continuum.PhysicalWilsonBridge.physicalCharacterDiagResolution
#print axioms YMGap.Continuum.PhysicalWilsonBridge.physicalWilsonFormGap
