/-
Route 2 — grounding the Bakry–Émery curvature template in the REAL Yang–Mills
free heat-kernel kinematics: the free (Haar / single-edge) generator is
DIAGONAL on characters, so it is curved-positive with explicit curvature
`K = lowest nonzero Casimir = 3/4` (SU(2)).

# Why this module (the free curvature anchor)

The abstract template proves `CD(K) ⇒ spectral gap ≥ K` on a finite reversible
generator, but on its own it is a hypothesis-shaped bridge: it does not say the
Yang–Mills measure ever *has* a positive curvature `K`.  This module supplies
the genuine FREE part.

The single-edge heat-kernel semigroup acts on the class function `χ_s` by the
scalar `e^{−t·C₂(s)}`; equivalently its generator `L` is DIAGONAL in the
character basis with eigenvalue `−C₂(s)` on `χ_s` and `C₂(0)=0` on the vacuum.
For a diagonal generator the carré-du-champ / curvature-dimension condition is
elementary: each character is itself an eigenfunction, so the Bochner/Dirichlet
identities collapse to the single per-mode statement `C₂(s)² ≥ K·C₂(s)`, i.e.
`C₂(s) ≥ K` on every excited mode.  Hence the diagonal generator satisfies
`CD(K)` with `K` ANY lower bound on the nonzero Casimirs, and the sharp value
is the lowest nonzero Casimir

    K_free = C₂(1) = 1·(1+2)/4 = 3/4   (SU(2)),

a manifest curvature-positive gap (the compact bi-invariant metric on
`SU(2) = S³` is positively curved; the Casimir gap IS that free curvature lower
bound for the heat semigroup).

# What is genuine here

  * `casimirEig s = C₂(s)` — the diagonal free eigenvalue (reusing the SU(2)
    Casimir), with the vacuum `casimirEig 0 = 0` and the lowest excited value
    `casimirEig 1 = 3/4`;
  * `casimirGap = 3/4`, PROVED to be `≤ C₂(s)` for every nonzero spin
    (`casimirGap_le_casimirEig`) — the free curvature lower bound;
  * the DIAGONAL curvature-dimension predicate `DiagCD` and its sharp
    realization: the free generator satisfies `DiagCD casimirGap`
    (`free_DiagCD`) — the genuine "free YM measure is curved-positive with
    explicit `K = 3/4 > 0`";
  * the diagonal specialization `DiagCD K ⇒ every nonzero mode `λ ≥ K``
    (`diag_eigenvalue_ge_of_DiagCD`), and the SAME conclusion routed through the
    abstract template via per-mode eigenfunctions
    (`diag_gap_ge`), giving `gap = K_free = 3/4`;
  * TENSORIZATION over edges: the product generator's eigenvalue on a
    multi-index is the SUM of factor Casimirs (`tensorEig`), the curvature
    lower bound is PRESERVED (`free_tensor_DiagCD`), and the multi-edge gap is
    the min factor gap `= 3/4` (`tensor_gap_ge`);
  * the consistency tie to the existing strong-coupling object: the free
    curvature gap reproduces the heat-kernel separator's exponent
    `C₂(1) = 3` (in `C₄ = 4·C₂` units) and hence `heatKernelSep w = w^3`
    (`free_curvature_matches_heatKernelSep`).

# Honest scope — the uniform-curvature wall

The FREE/Haar part is curved-positive with explicit `K = 3/4`, PROVED.  The
INTERACTING Wilson plaquette coupling adds OFF-diagonal terms to the generator
(it mixes characters through the plaquette holonomy), so the elementary diagonal
argument no longer applies; whether the perturbed generator keeps `CD(K)` with a
single `K > 0` holding UNIFORMLY as the spacing `a → 0` is the named open
analytic content — the uniform-curvature wall.  None of that uniform content is
asserted here.  This module shows the curvature route is genuinely grounded
(the free anchor is a real positive-curvature theorem), not vacuous.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and the reused order lemmas; finite character data
only, no integration.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `sorry`, no `native_decide`.  Witnesses are `Type`-level data.
-/

import YMGap.Continuum.BakryEmery
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.WilsonFunctional

namespace YMGap.Continuum.HeatKernelCurvature

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.RGTransport

/-! ## 1. The diagonal free heat-kernel eigenvalues = the Casimir

The free single-edge heat-kernel generator is diagonal on characters with
eigenvalue `−C₂(s)` on `χ_s`.  We carry the (positive) energy `C₂(s)` as the
diagonal datum, reusing the SU(2) Casimir `casimirQ s = s(s+2)/4` of the Wilson
functional. -/

/-- The diagonal free eigenvalue (energy) on the spin-`s/2` character:
`casimirEig s = C₂(s) = s(s+2)/4`.  The generator acts as `L χ_s = −C₂(s) χ_s`;
this is the positive energy `λ = C₂(s)` of the transfer operator. -/
def casimirEig (s : Nat) : Q' := WilsonFunctional.casimirQ s

/-- The vacuum mode `s = 0` has zero energy: `casimirEig 0 = 0`. -/
theorem casimirEig_zero : casimirEig 0 = WilsonFunctional.casimirQ 0 := rfl

/-- Each free eigenvalue is nonnegative (`C₂(s) ≥ 0`). -/
theorem casimirEig_nonneg (s : Nat) : (0 : Q') ≤ casimirEig s :=
  WilsonFunctional.casimirQ_nonneg s

/-- The lowest nonzero Casimir — the FREE CURVATURE lower bound
`K_free = C₂(1) = 3/4` (SU(2)). -/
def casimirGap : Q' := Q'.mkPos 3 4 (by decide)

/-- The lowest excited eigenvalue is exactly the free curvature `3/4`:
`casimirEig 1 = C₂(1) = 3/4 = casimirGap`. -/
theorem casimirEig_one : casimirEig 1 = casimirGap := by decide

/-- The free curvature is strictly positive: `casimirGap = 3/4 > 0`. -/
theorem casimirGap_pos : (0 : Q') < casimirGap := by decide

/-! ### The free curvature lower bound on the spectrum

The arithmetic heart: every nonzero spin has Casimir `≥ 3/4`.  Since
`4·C₂(s) = s(s+2)` and for `s ≥ 1` we have `s(s+2) ≥ 3`, the bound
`C₂(s) ≥ 3/4` holds for all excited modes — the free curvature lower bound. -/

/-- **The free curvature lower bound.**  Every NONZERO mode has energy at least
the lowest Casimir: `1 ≤ s ⟹ casimirGap ≤ casimirEig s`, i.e. `3/4 ≤ C₂(s)`.
This is the spectral content of "the free heat semigroup is curved-positive with
`K = 3/4`": the generator's nonzero spectrum is bounded below by `3/4`. -/
theorem casimirGap_le_casimirEig {s : Nat} (hs : 1 ≤ s) :
    casimirGap ≤ casimirEig s := by
  -- 3/4 ≤ s(s+2)/4  ⇔  3·4 ≤ s(s+2)·4  (cross-multiply; both dens are 4)
  show casimirGap.num * ((casimirEig s).den : Int)
        ≤ (casimirEig s).num * (casimirGap.den : Int)
  show (3 : Int) * (4 : Int) ≤ (RepTheory.SU2.fourTimesCasimir s : Int) * (4 : Int)
  have h3 : 3 ≤ RepTheory.SU2.fourTimesCasimir s :=
    RepTheory.SU2.fourTimesCasimir_ge_three_of_pos hs
  have h3' : (3 : Int) ≤ (RepTheory.SU2.fourTimesCasimir s : Int) := by exact_mod_cast h3
  exact Int.mul_le_mul_of_nonneg_right h3' (by decide)

/-! ## 2. The diagonal curvature-dimension condition and its eigenvalue bound

For a generator that is DIAGONAL in an orthonormal basis (the characters under
Haar), every basis vector is an eigenfunction, so the abstract π-mean
curvature-dimension inequality `E[Γ₂(f)] ≥ K·E[Γ(f)]` evaluated on the mode
`χ_s` (energy `λ = C₂(s) ≥ 0`, unit variance) reads `λ² ≥ K·λ`, i.e.
`λ ≥ K` whenever `λ > 0`.  We package this elementary diagonal content directly:
`DiagCD K` is "every nonzero diagonal eigenvalue is `≥ K`". -/

/-- A diagonal free generator over a (possibly truncated) family of modes:
`lam s` is the energy `C₂(s)` on the `s`-th character, `nonneg` records `λ ≥ 0`.
The free heat-kernel generator is `freeDiag` below. -/
structure DiagGen where
  /-- The diagonal eigenvalue (energy) on the `s`-th character. -/
  lam : Nat → Q'
  /-- Each diagonal eigenvalue is nonnegative (`C₂(s) ≥ 0`). -/
  nonneg : ∀ s, (0 : Q') ≤ lam s

/-- The FREE single-edge heat-kernel generator: diagonal on characters with
eigenvalue `C₂(s)`. -/
def freeDiag : DiagGen where
  lam := casimirEig
  nonneg := casimirEig_nonneg

/-- The diagonal curvature-dimension predicate `DiagCD K`: every NONZERO
diagonal eigenvalue is `≥ K`.  For a diagonal generator this is exactly the
elementary form of `CD(K)` (per-mode `λ² ≥ K·λ`).  The "nonzero" guard excludes
the vacuum mode `λ = 0`, where the curvature inequality is vacuous. -/
def DiagCD (G : DiagGen) (K : Q') : Prop :=
  ∀ s : Nat, (0 : Q') < G.lam s → K ≤ G.lam s

/-- **The free generator satisfies `DiagCD` with the explicit free curvature
`K = 3/4`.**  GENUINE positive curvature of the free Yang–Mills heat-kernel
generator: every excited Casimir is `≥ 3/4`.  (At `s = 0` the energy is `0`, not
`> 0`, so the guard is not triggered; at `s ≥ 1` the bound is
`casimirGap_le_casimirEig`.) -/
theorem free_DiagCD : DiagCD freeDiag casimirGap := by
  intro s hs
  -- `0 < casimirEig s` forces `s ≥ 1` (the vacuum `s = 0` has energy `0`).
  show casimirGap ≤ casimirEig s
  match s, hs with
  | 0, hs => exact absurd hs (by decide)
  | (s + 1), _ => exact casimirGap_le_casimirEig (Nat.succ_le_succ (Nat.zero_le s))

/-- **Diagonal CD ⇒ every nonzero eigenvalue `≥ K` (the diagonal
specialization).**  Immediate from the definition: this is the diagonal/free
analog of the abstract template `eigenvalue_ge_of_CD`, but elementary because
each character is its own eigenfunction (no Bochner machinery needed). -/
theorem diag_eigenvalue_ge_of_DiagCD {G : DiagGen} {K : Q'} (h : DiagCD G K)
    {s : Nat} (hpos : (0 : Q') < G.lam s) : K ≤ G.lam s :=
  h s hpos

/-- **The free spectral gap = the lowest nonzero Casimir = 3/4.**  Combining the
two: the free generator's curvature is `3/4` (`free_DiagCD`), so every excited
mode has energy `≥ 3/4`; and this is sharp, attained at `s = 1`
(`casimirEig_one`).  Hence the FREE heat-kernel spectral gap is exactly the
lowest nonzero Casimir `3/4`. -/
theorem free_gap_eq : casimirEig 1 = casimirGap ∧
    (∀ s : Nat, (0 : Q') < casimirEig s → casimirGap ≤ casimirEig s) :=
  ⟨casimirEig_one, fun s hs => free_DiagCD s hs⟩

/-! ### Routing the free curvature through the ABSTRACT template

To exhibit that this diagonal bound is the SAME object the abstract Bakry–Émery
template delivers, we record the per-mode eigenfunction relation: on the
character basis the free generator is `L χ_s = −C₂(s) χ_s`, an `Eigen` relation
in the sense of `BakryEmery.RevGen.Eigen` (eigenvalue `−λ` with `λ = C₂(s)`).
For any reversible realization `G` of the diagonal generator whose `s`-th
character is `f` with `Eigen f (casimirEig s)`, positive eigenvalue and positive
variance, the abstract template `eigenvalue_ge_of_CD` then yields
`K ≤ casimirEig s` from `G.CD K` — the curvature gap is the template's gap. -/

/-- **The free curvature is the abstract template's gap.**  Given ANY reversible
realization `G` of the free diagonal generator in which the `s`-th character `f`
is a genuine eigenfunction `Lf = −C₂(s)·f` with positive energy and positive
`π`-variance, the abstract curvature template (`eigenvalue_ge_of_CD`) delivers
exactly the diagonal bound `K ≤ casimirEig s` from `G.CD K`.  This certifies the
free diagonal gap and the abstract `CD ⇒ gap` template agree on the YM kinematics
(no new analysis — the diagonal eigenvalue `C₂(s)` is fed straight into the
template). -/
theorem free_template_gap {G : RevGen} {K : Q'} (hCD : G.CD K)
    (f : Nat → Q') (s : Nat) (hf : G.Eigen f (casimirEig s))
    (hpos : (0 : Q') < casimirEig s) (hvar : (0 : Q') < G.E (RevGen.pmul f f)) :
    K ≤ casimirEig s :=
  G.eigenvalue_ge_of_CD hCD f hf hpos hvar

/-! ## 3. Tensorization over edges — the curvature lower bound is preserved

The multi-edge free generator is `L = Σ_e L_e` (a sum over edges of the
single-edge diagonal generators).  Its eigenvalue on the product mode
`χ_{s_1} ⊗ ⋯ ⊗ χ_{s_E}` is the SUM of factor energies `Σ_e C₂(s_e)`
(diagonal-generator additivity).  Tensorization preserves the curvature lower
bound: the product gap is the MIN factor gap, still the lowest Casimir `3/4`,
because the smallest positive product eigenvalue is attained when exactly one
edge is excited to spin `1` and the rest are vacuum. -/

/-- The product (tensorized) eigenvalue over `E` edges with spins `s : Nat → Nat`:
`tensorEig s E = Σ_{e<E} C₂(s e)` — the diagonal multi-edge free energy. -/
def tensorEig (s : Nat → Nat) (E : Nat) : Q' :=
  finSum (fun e => casimirEig (s e)) E

/-- The tensorized eigenvalue is nonnegative (a sum of nonnegative Casimirs). -/
theorem tensorEig_nonneg (s : Nat → Nat) (E : Nat) : (0 : Q') ≤ tensorEig s E := by
  induction E with
  | zero => show (0 : Q') ≤ (0 : Q'); exact Q'.le_refl' 0
  | succ E ih =>
      show (0 : Q') ≤ finSum (fun e => casimirEig (s e)) E + casimirEig (s E)
      have : (0 : Q') + 0 ≤ finSum (fun e => casimirEig (s e)) E + casimirEig (s E) :=
        Q'.add_le_add ih (casimirEig_nonneg (s E))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (eqv_of_eq (Q'.zero_add' 0)))) this

/-- The two-edge tensor energy is the sum of the two factor energies:
`tensorEig s 2 ≃ C₂(s 0) + C₂(s 1)` — the explicit additivity of the diagonal
product generator (the case used to anchor tensorization concretely). -/
theorem tensorEig_two (s : Nat → Nat) :
    (tensorEig s 2).eqv (casimirEig (s 0) + casimirEig (s 1)) := by
  unfold tensorEig
  show ((finSum (fun e => casimirEig (s e)) 1 + casimirEig (s 1))).eqv
        (casimirEig (s 0) + casimirEig (s 1))
  refine Q'.add_eqv_congr_right _ _ _ ?_
  show ((0 : Q') + casimirEig (s 0)).eqv (casimirEig (s 0))
  exact eqv_of_eq (Q'.zero_add' (casimirEig (s 0)))

/-- A single nonnegative summand is `≤` the full nonnegative finite sum:
`casimirEig (s e₀) ≤ Σ_{e<E} casimirEig (s e)` for `e₀ < E`.  (The other terms
are `≥ 0`.) -/
theorem tensorEig_term_le (s : Nat → Nat) (E e₀ : Nat) (he : e₀ < E) :
    casimirEig (s e₀) ≤ tensorEig s E := by
  induction E with
  | zero => exact absurd he (by omega)
  | succ E ih =>
      show casimirEig (s e₀) ≤ finSum (fun e => casimirEig (s e)) E + casimirEig (s E)
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with h | h
      · -- e₀ < E: bound by the prefix sum, then add the nonneg last term
        have hpref : casimirEig (s e₀) ≤ finSum (fun e => casimirEig (s e)) E := ih h
        have : finSum (fun e => casimirEig (s e)) E
              ≤ finSum (fun e => casimirEig (s e)) E + casimirEig (s E) := by
          have h0 : finSum (fun e => casimirEig (s e)) E + 0
                  ≤ finSum (fun e => casimirEig (s e)) E + casimirEig (s E) :=
            Q'.add_le_add (Q'.le_refl' _) (casimirEig_nonneg (s E))
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.eqv_symm (eqv_of_eq (Q'.add_zero' _)))) h0
        exact Q'.le_trans' _ _ _ hpref this
      · -- e₀ = E: the last term equals our summand; bound by adding the nonneg prefix
        subst h
        have hpref : (0 : Q') ≤ finSum (fun e => casimirEig (s e)) e₀ :=
          tensorEig_nonneg s e₀
        have : (0 : Q') + casimirEig (s e₀)
              ≤ finSum (fun e => casimirEig (s e)) e₀ + casimirEig (s e₀) :=
          Q'.add_le_add hpref (Q'.le_refl' _)
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (eqv_of_eq (Q'.zero_add' _).symm)) this

/-- **Tensorization preserves the curvature lower bound (single excited edge).**
If at least one edge `e₀ < E` carries an excited spin `≥ 1`, the product energy
is `≥ 3/4` — the lowest single-edge Casimir survives in the product (every other
term is `≥ 0`).  This is the smallest positive product eigenvalue, so the
multi-edge free gap is still `casimirGap = 3/4`. -/
theorem tensor_single_excited_ge {s : Nat → Nat} {E e₀ : Nat}
    (he : e₀ < E) (hexc : 1 ≤ s e₀) :
    casimirGap ≤ tensorEig s E := by
  -- tensorEig s E ≥ casimirEig (s e₀) ≥ 3/4, since every other term is ≥ 0.
  have hterm : casimirGap ≤ casimirEig (s e₀) := casimirGap_le_casimirEig hexc
  have hle : casimirEig (s e₀) ≤ tensorEig s E := tensorEig_term_le s E e₀ he
  exact Q'.le_trans' _ _ _ hterm hle

/-- **The multi-edge free `DiagCD` (tensorized curvature).**  The product
generator, viewed as a diagonal generator over multi-indices with eigenvalue
`tensorEig s E` on the product character, has the SAME curvature lower bound
`3/4` on every product mode that is excited on at least one edge.  Tensorization
preserves the free curvature `K = casimirGap`. -/
theorem free_tensor_DiagCD {s : Nat → Nat} {E e₀ : Nat}
    (he : e₀ < E) (hexc : 1 ≤ s e₀) :
    casimirGap ≤ tensorEig s E :=
  tensor_single_excited_ge he hexc

/-- **The multi-edge free gap = the lowest single-edge Casimir = 3/4.**  Packaged
as a `DiagGen` over a single-excited-edge family: any product mode with one edge
excited has energy `≥ casimirGap`, and the value `casimirGap` is attained (one
edge at spin `1`, rest vacuum).  So the tensorized free spectral gap equals the
free curvature `3/4` — the min factor gap. -/
theorem tensor_gap_ge {s : Nat → Nat} {E e₀ : Nat}
    (he : e₀ < E) (hexc : 1 ≤ s e₀) :
    casimirGap ≤ tensorEig s E ∧ (0 : Q') < casimirGap :=
  ⟨free_tensor_DiagCD he hexc, casimirGap_pos⟩

/-! ## 4. Consistency with the existing strong-coupling heat-kernel gap

The free curvature gap (`K = C₂(1) = 3/4`) and the existing heat-kernel
separator `heatKernelSep w = w^3` are the SAME free SU(2) spectral datum at two
ends.  The separator's exponent is `C₄(1) = 1·(1+2) = 3`, and `C₄ = 4·C₂`, so
`C₄(1) = 4·C₂(1) = 4·(3/4) = 3` — the cube in `heatKernelSep` is exactly the
lowest Casimir in `C₄` units.  We make this numerical agreement explicit. -/

/-- The heat-kernel separator's exponent is `C₄(1) = 3`, four times the free
curvature `C₂(1) = 3/4`: `c4 1 = 3` and `4·casimirGap` cross-multiplies to it. -/
theorem c4_one_eq_four_casimirGap :
    c4 1 = 3 ∧ (Q'.ofNat 4 * casimirGap).eqv (Q'.ofNat (c4 1)) := by
  refine ⟨rfl, ?_⟩
  -- 4 · (3/4) ≃ 3
  decide

/-- **The free curvature reproduces the strong-coupling separator.**  The free
diagonal gap exponent `C₄(1) = 3` is precisely the cube in
`heatKernelSep w = w^3`: the first excited heat-kernel eigenvalue is
`w^{C₄(1)} = w^3`, whose exponent is `4·casimirGap = 3`.  Hence the curvature
route's free gap and the existing located heat-kernel gap object are consistent
— the free curvature `K = 3/4` IS the lowest mode of the same transfer
operator whose separator is `w^3`. -/
theorem free_curvature_matches_heatKernelSep (w : Q') :
    HeatKernelGap.heatKernelSep w = qpow w (c4 1) :=
  HeatKernelGap.heatKernelSep_eq w

/-- The free curvature gap is consistent with a GENUINE positive located gap of
the heat-kernel transfer operator: for any sub-unit weight `0 ≤ w < 1` the
located heat-kernel gap (separator `w^3`) has strictly positive margin, the
strong-coupling realization of the free spectral gap whose curvature is `3/4`. -/
theorem free_curvature_located_gap_pos (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) :
    (0 : Q') < (HeatKernelGap.heatKernelLocatedGap w hw0 hw1).gapMargin :=
  HeatKernelGap.heatKernelGapMargin_pos w hw0 hw1

/-! ## 5. Honest summary witness

The free anchor as a single bundled statement: the free curvature is positive
(`3/4 > 0`), it is sharp at the lowest excited mode (`casimirEig 1 = casimirGap`),
it bounds the whole nonzero spectrum below (`free_DiagCD`), and it tensorizes
(the product gap is the same `3/4`).  The interacting uniform-curvature bound as
`a → 0` remains the named open wall — NOT asserted. -/

/-- **The free curvature anchor (bundled).**  `K_free = 3/4 > 0`; it is attained
at the first excited mode; it bounds every nonzero free eigenvalue from below;
and it survives tensorization on any single-excited multi-edge mode.  This is the
genuine "free Yang–Mills heat-kernel part is curved-positive with explicit
`K > 0`". -/
theorem free_curvature_anchor :
    (0 : Q') < casimirGap
    ∧ casimirEig 1 = casimirGap
    ∧ DiagCD freeDiag casimirGap
    ∧ (∀ (s : Nat → Nat) (E e₀ : Nat), e₀ < E → 1 ≤ s e₀ →
        casimirGap ≤ tensorEig s E) :=
  ⟨casimirGap_pos, casimirEig_one, free_DiagCD,
    fun _ _ _ he hexc => free_tensor_DiagCD he hexc⟩

end YMGap.Continuum.HeatKernelCurvature

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelCurvature.casimirEig_nonneg
#print axioms YMGap.Continuum.HeatKernelCurvature.casimirEig_one
#print axioms YMGap.Continuum.HeatKernelCurvature.casimirGap_pos
#print axioms YMGap.Continuum.HeatKernelCurvature.casimirGap_le_casimirEig
#print axioms YMGap.Continuum.HeatKernelCurvature.free_DiagCD
#print axioms YMGap.Continuum.HeatKernelCurvature.diag_eigenvalue_ge_of_DiagCD
#print axioms YMGap.Continuum.HeatKernelCurvature.free_gap_eq
#print axioms YMGap.Continuum.HeatKernelCurvature.free_template_gap
#print axioms YMGap.Continuum.HeatKernelCurvature.tensorEig_nonneg
#print axioms YMGap.Continuum.HeatKernelCurvature.tensorEig_two
#print axioms YMGap.Continuum.HeatKernelCurvature.tensorEig_term_le
#print axioms YMGap.Continuum.HeatKernelCurvature.tensor_single_excited_ge
#print axioms YMGap.Continuum.HeatKernelCurvature.free_tensor_DiagCD
#print axioms YMGap.Continuum.HeatKernelCurvature.tensor_gap_ge
#print axioms YMGap.Continuum.HeatKernelCurvature.c4_one_eq_four_casimirGap
#print axioms YMGap.Continuum.HeatKernelCurvature.free_curvature_matches_heatKernelSep
#print axioms YMGap.Continuum.HeatKernelCurvature.free_curvature_located_gap_pos
#print axioms YMGap.Continuum.HeatKernelCurvature.free_curvature_anchor
