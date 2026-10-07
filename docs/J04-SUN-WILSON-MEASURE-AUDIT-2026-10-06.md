# J04 audit: what a Wilson measure for SU(N), N ≥ 3, would need (2026-10-06)

Status: J04 OPEN.  This note is an inventory, not a result.

## 0. What "the Wilson measure" is in the repo today (SU(2) only)

`Continuum/WilsonConsistency.wilsonContinuumMeasure w hw` (used by
`MassGap/SimpleGroup.SU2WilsonOrigin`) is built from:

* `RGTransport.charAlg`: carrier = SU(2) spin labels `Nat`, `mul a b = |a−b|`
  (Clebsch–Gordan *lowest channel only*; documented as non-associative),
  `star = id`;
* `charFunc w`: `E χ_s = (s+1) · w^{s(s+2)}` — the single-link heat-kernel
  character moment with rational weight `w ≈ e^{−t/4}`;
* `wilsonSystem = stationaryTower charAlg` (identity coarse→fine inclusion) and
  the inverse-limit `ContinuumMeasure`.

Caveat for J04: this is a one-link character-moment functional, not a
lattice Wilson Gibbs measure over plaquettes.  The genuine lattice SU(2)
content lives separately in the quaternion/Haar stack
(`RationalQuaternion*`, `BF4GeometricHaarMehlerProjection.quaternionHaar`,
`SU2Quaternion*` heat/character/Casimir modules).  `SU2WilsonOrigin` is
therefore tied to the repo's *named* Wilson measure, which is weaker than a
lattice Wilson measure.

## 1. Pieces existing for SU(2) and their SU(N) status

| Layer | SU(2) module(s) | SU(N≥3) status |
|---|---|---|
| Group carrier | `RepTheory/RationalQuaternionAlgebra`, `RationalQuaternionUnitNormGroup` (rational points of S³, `ConstructiveGroup`) | **missing**: no rational unitary N×N matrices with det 1, no `ConstructiveGroup` instance |
| Centre / global forms | `RationalQuaternionSignQuotient`, `LocatedCentralQuotient` | generic quotient machinery exists (`ConstructiveGroup`, `CompactSimpleGlobalForm` centre codes ℤ_N); no SU(N) instance |
| Haar functional | `quaternionHaar` (exact S³ monomial moments `sphereMoment4`) | **missing**: no exact moments of matrix-entry monomials on SU(N) (Weingarten / Gelfand–Tsetlin integration) |
| Characters | `characterPolynomial` (Chebyshev-U), `SU2Realized.spinCharacter`, `relativeCharacter_eq_spinCharacter` | **missing as functions on the group**: only scalar data — `RepTheory/SU3` (dim, C₂ of (p,q)), `RG/SUNWeylData` (fundamental-weight C₂), `RG/WeylDimGeneral*`, `RG/WeylCharacterBound` (tail bounds) |
| Casimir eigen-identity | `SU2QuaternionRelativeCharacterCasimir` (angular Laplacian on S³) | **missing**: no Laplace–Beltrami/Casimir operator on SU(N) polynomial algebra |
| Orthonormality | `SU2Realized.selfPairing_one/_two` (finite s only) | **missing** |
| Character algebra / moments | `charAlg`, `charFunc` (lowest-channel) | would need full Littlewood–Richardson fusion `χ_λ χ_μ = Σ N^ν_{λμ} χ_ν` (a genuinely associative algebra) — missing even for SU(2) |
| Projective tower / continuum measure | `WilsonConsistency` (generic `stationaryTower`, `continuumMeasure`) | generic and reusable once a per-scale `ProbFunctional` on an SU(N) character algebra exists |
| Heat-kernel weight | `w^{s(s+2)}` | form `dim(λ)·e^{−t C₂(λ)}`; C₂ data exists (`SU3`, `SUNWeylData`), rationalized weight would need `w^{(rational C₂)}` — denominators `N` need a root or a rescaled `w` |

## 2. Minimal missing modules (in dependency order)

1. `RepTheory/RationalSUNGroup`: rational N×N matrices with `U U* = 1`,
   `det = 1` (over `Q'` or `Q'(i)`), group laws as a `ConstructiveGroup`;
   centre ℤ_N inclusion feeding `LocatedCentralQuotient`.
2. `RepTheory/SUNCharacters`: Schur-polynomial (Weyl) characters `χ_λ` as
   polynomials in matrix entries; `χ_λ(1) = dim λ` against `WeylDimGeneral`.
3. `Continuum/SUNHaarMoments`: exact Haar functional on polynomials in entries
   (Weingarten calculus or Weyl integration in eigenvalue coordinates);
   normalization and left/right invariance on the polynomial algebra.
4. `Continuum/SUNCasimirEigen`: Casimir operator on the polynomial algebra
   with `C χ_λ = C₂(λ) χ_λ`, matching `SU3`/`SUNWeylData` values.
5. `Continuum/SUNCharacterAlgebra`: associative fusion algebra on dominant
   weights and the heat-kernel `ProbFunctional`; positivity on `a*a`.
6. `Continuum/SUNWilsonConsistency`: tower + `ContinuumMeasure`, then an
   `SUNWilsonOrigin` predicate replacing the `R = su2` clause of
   `SU2WilsonOrigin` (lifting `GroupBoundGap.row_eq_su2`).

Items 1–4 correspond to ladder item (e) of work_plan "J04 parallel track";
items 5–6 to (d)/(f).  None of these exist; nothing in this note is proved.

## 3. SU(2) general-spin Schur orthonormality: why it is not cheap (2026-10-06)

Proved: `∫ χ_s χ_t = δ_st` for `s, t ≤ 2` only, by exact evaluation
(`SU2TorusSchurSmall.polySchurUpTo2`, `SU2Realized.selfPairing_one/_two`).
The general statement needs three lemmas that do not exist in the repo:

1. **Clebsch–Gordan for Chebyshev-U** as polynomials:
   `U_s · U_t = Σ_{j=0}^{min(s,t)} U_{|s−t|+2j}` (`characterPolynomial` level,
   induction on `min(s,t)` from the three-term recursion — moderate).
2. **Character mean**: `quaternionHaar 1 (U_n(x₀)) ≈ δ_{n0}`.  This needs the
   closed form of the one-coordinate sphere moment
   `sphereMoment4 2k 0 0 0 = Catalan(k)/4^k` (the S³ semicircle law) together
   with the monomial expansion of `U_n` — a coefficient identity
   `Σ_k (−1)^k C(n−k,k) 2^{n−2k} · Cat((n−2k)/2)/4^{(n−2k)/2} = δ_{n0}`, which is
   the real work.
3. **Haar linearity over `polyAdd`/`polyMul` reorganization** (exists:
   `quaternionHaar_append`, `quaternionHaar_polySmul`, `HaarCarrierEqv`).

With (1)–(2), orthonormality is a one-line sum.  The relative (two-block)
version additionally needs `relativeCharacter` mean `≈ δ_{n0}`, which reduces
to (2) by invariance of `quaternionHaar` under one-block translation (only
selected-degree translation lemmas exist).

## 4. `LinkHaar SU2` (in `SU2TorusWilsonGibbs`) is empty

It asks for an additive, positive, normalized, left-invariant functional on
*all* functions on the rational unit quaternions.  On `≈`-invariant indicator
functions it would be a left-invariant finitely additive mean on the group,
which is impossible because the group contains a rank-two free subgroup mod ±1
(classical; e.g. via the norm-5 integer quaternions `2+i, 2+j`, whose squares
give the rational unit quaternions `(3+4i)/5, (3+4j)/5`; cited, not
formalized).  `Continuum/SU2PolyLinkHaar.lean` gives the constructed
replacement on the polynomial coordinate algebra.  Changing the Gibbs layer's
hypothesis type is the Prover's call.

## 5. How much of the `LinkHaar SU2` emptiness argument is formalizable

Steps, with cost estimates:

1. *Restriction to ≈-closed indicators* — easy: `F x := if x ∈ A then 1 else 0`
   needs a decidable ≈-closed predicate; `h` then gives `μ(A)` with finite
   additivity and invariance from `add`/`left_inv` (≈-congruence of `G.mul`
   exists).  Small.
2. *Two explicit rational unit quaternions `a = (3+4i)/5`, `b = (3+4j)/5`
   generate a free group mod ±1* — the hard part.  Ping-pong on the
   5-adic valuation of reduced words (norm-5 Lipschitz quaternions, unique
   factorization of Hurwitz/Lipschitz quaternions at an odd prime) is a
   self-contained but substantial development (est. 1–2k lines).
3. *Paradoxical decomposition of the free group* — standard and
   constructive on reduced words (`F = {e} ∪ W(a) ∪ W(a⁻¹) ∪ W(b) ∪ W(b⁻¹)`,
   `F = W(a) ∪ a W(a⁻¹)`), moderate.
4. *Transfer from `F` to `G`* — classically needs a choice of right-coset
   representatives of `F` in `G`.  Constructively avoidable only by a different
   route: apply the mean to the indicator functions of the sets
   `{x | x ∈ W(·)}` *inside `F`* is not enough (μ(F) may be 0).  So step 4
   needs either choice or an explicit, decidable coset transversal of `⟨a,b⟩`
   in the rational unit quaternions (not known to us).

So steps 1–3 are formalizable with effort; step 4 is the genuine obstacle in a
choice-free development.  A cheaper, sufficient fix is to drop `LinkHaar` from
the Gibbs layer in favour of `PolyLinkHaar`, which the Prover has done
(`SU2TorusPolyGibbs`).

## Hand-off to YM Lean Prover: multi-plaquette activity bound (2026-10-07)

Files: `lean/YMGap/Continuum/SU2PolymerActivityBound.lean` (namespace
`YMGap.Continuum.SU2PolymerActivityBound`) and `SU2PlaqWeightedCharacterBound.lean`.
All axioms are `[propext, Quot.sound]`. The plaquettes may share links, and no independence is used.

### Exact signatures
```lean
-- YMGap.Continuum.SU2PolymerActivityBound   (section vars: links : List Z4Link, N : Nat)
def charSum (p : Z4Plaq) : List (Q' × Nat) → RatPoly      -- Σ c·χ_s(U_p)
  | [] => polyZero
  | t :: ts => polyAdd (polySmul t.1 (plaqCharacter links N p t.2)) (charSum p ts)
def bSum : List (Q' × Nat) → Q'                           -- Σ |c|·(s+1)
  | [] => 0
  | t :: ts => Q'.abs t.1 * Q'.ofInt ((t.2 : Int) + 1) + bSum ts
def polyProd : List (Z4Plaq × List (Q' × Nat)) → RatPoly  -- [] => polyOne; q::r => charSum q.1 q.2 * polyProd r
def bProd    : List (Z4Plaq × List (Q' × Nat)) → Q'       -- [] => 1;       q::r => bSum q.2 * bProd r
def PolymerOK (links : List Z4Link) (N : Nat) (X : List (Z4Plaq × List (Q' × Nat))) : Prop :=
  ∀ q ∈ X, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N q.1 ∧ ∀ t ∈ q.2, (0 : Q') < Q'.abs t.1
theorem polymer_activity_sq_le (X) (hX : PolymerOK links N X) :
    let h := (multiLinkHaar links.length).h; let F := polyProd links N X
    h (polyMul F F) ≤ bProd X * bProd X ∧ h F * h F ≤ bProd X * bProd X
theorem polymer_activity_abs_le (X) (hX : PolymerOK links N X) :
    let h := (multiLinkHaar links.length).h; let F := polyProd links N X
    (-bProd X) ≤ h F ∧ h F ≤ bProd X
theorem bProd_nonneg (X) : 0 ≤ bProd X
theorem two_sided_of_sq_le {x y : Q'} (h : x*x ≤ y*y) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y

-- YMGap.Continuum.SU2PlaqWeightedCharacterBound
def Bnd (n : Nat) (f : RatPoly) (B : Q') : Prop := ∀ G, SupportedCoordinates (4*n) G →
  H n (polyMul (polyMul f G) (polyMul f G)) ≤ (B*B) * H n (polyMul G G)
theorem plaq_weighted_le (links N p) (hc : LinksCover links N p) (s : Nat) :
  Bnd links.length (plaqCharacter links N p s) (Q'.ofInt ((s : Int) + 1))

-- YMGap.Continuum.SU2CharacterCauchySchwarz
theorem plaq_character_cs (links N p) (hc : LinksCover links N p) (s : Nat)
    (G : RatPoly) (hG : SupportedCoordinates (4 * links.length) G) (t : Q') (ht : 0 ≤ t) :
    let χ := plaqCharacter links N p s; let h := (multiLinkHaar links.length).h
    let B := t * (t * Q'.ofInt (((s:Int)+1)*((s:Int)+1))) + h (polyMul G G)
    Q'.ofInt 2 * (t * h (polyMul χ G)) ≤ B ∧ -(Q'.ofInt 2 * (t * h (polyMul χ G))) ≤ B

-- YMGap.Continuum.SU2PlaqRadius
theorem plaqWord_radius_carrier (links N p) (hc : LinksCover links N p) :
  HaarCarrierEqv links.length (Nq (plaqWord links N p)) polyOne
```

### Mapping onto the heat-kernel activity
**Correction (2026-10-07):** `fPoly` DOES exist. It is
`YMGap.Continuum.SU2HaarL1Activity.fPoly w links N p M = Σ_{s=1}^{M} coeffW w s · χ_s(U_p)` (`| 0 => []`,
appended at the end). `SU2PlaqSupport.plaqWeight_split` (dd850bbe) gives
`plaqWeight = [([], coeffW w 0 · 1)] ++ fPoly`, and `SU2PolymerIdentity.polyPartition_eq_Xi` uses
`z γ = quaternionHaar links.length (prodPoly (fun p => fPoly w links N p M) γ)`. The earlier claim that
`fPoly` was missing was wrong. The bridge is now proved in `SU2PolymerActivityHeat.lean` (see below).

* Pass `q = (p, cs w M)` with `cs w M := [(coeffW w 1, 1), …, (coeffW w M, M)]`.
  Then `charSum links N p (cs w M) ≅ fPoly p`. That needs one `RatPolyCoeffEqv` lemma against
  `plaqWeight`, which is still to be written.
* Drop s = 0 because the term is centred. A constant term would contribute `1·(0+1)` to `bSum`
  and break the `ε^{|γ|}` smallness.
* Filter out zero coefficients. `PolymerOK` needs `0 < |c|`. For `0 < w`, every
  `coeffW w s = (s+1)·w^{s(s+2)} > 0`, so nothing is filtered. If `w = 0`, use `cs = []`, which
  gives `charSum = 0` and `bSum = 0`.
* `bSum (cs w M) = Σ_{s=1}^{M} |coeffW w s|·(s+1) = Σ_{s=1}^{M} (s+1)²·w^{s(s+2)} = charEnv w M`,
  up to `≈`. Use `|coeffW| = coeffW` for `w ≥ 0` and `dimQ s = s+1`. That bridge lemma is open.
* So for a polymer γ with plaquette list X(γ), `|h(Π_{p∈γ} fPoly p)| ≤ charEnv w M ^ |γ| = zHeat M γ`
  at `w = wR1`, via `polymer_activity_abs_le`. You must supply `LinksCover links N p` for each p.
* Sharper option: for plaquettes on disjoint links, `haar_disj` (14c3f5a8) factorises
  `h(Π f_p) = Π h(f_p)`. For centred `f_p`, `h(f_p) = 0`. So a polymer containing a plaquette
  that shares no link with the others has zero activity. The present bound does not exploit this.

### Heat-kernel bridge (`YMGap.Continuum.SU2PolymerActivityHeat`)
```lean
def heatList (w : Q') : Nat → List (Q' × Nat)   -- 0 => []; M+1 => (coeffW w (M+1), M+1) :: heatList w M
theorem fPoly_eq_charSum (w links N p) : ∀ M, RatPolyCoeffEqv (fPoly w links N p M) (charSum links N p (heatList w M))
theorem bSum_heatList {w} (hw : 0 ≤ w) : ∀ M, (bSum (heatList w M)).eqv (charEnv w M)
theorem heatList_pos {w} (hw : 0 < w) : ∀ M, ∀ t ∈ heatList w M, 0 < Q'.abs t.1
theorem z_abs_le {w : Q'} (hw : 0 < w) (M : Nat) (links : List Z4Link) (N : Nat) (γ : List Z4Plaq)
    (hc : ∀ p ∈ γ, SU2PlaqWordHolonomy.LinksCover links N p) :
    let z := quaternionHaar links.length (prodPoly (fun p => fPoly w links N p M) γ)
    (-(charEnv w M ^ γ.length)) ≤ z ∧ z ≤ charEnv w M ^ γ.length
```
Here `(multiLinkHaar n).h` is `quaternionHaar n` by definition. `LinksCover` is the four explicit link memberships. The gas uses `Lk`
(`∀ ℓ ∈ plaqLinks N p, ℓ ∈ links`), and the `Lk → LinksCover` bridge is left to the Prover.
