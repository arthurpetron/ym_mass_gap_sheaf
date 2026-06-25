/-
# The π-FREE Chebyshev-`U` ORTHOGONALITY MATRIX
# `∫_{−1}^1 U_c(x)·U_d(x)·√(1−x²) dx = semiInt·δ_{cd}`  (the Gram = `semiInt·I`, PSD)

This module assembles the full second-kind Chebyshev orthogonality *matrix* with
respect to the semicircle weight `√(1−x²)`, π-FREE, by a CLEAN reduction to the
already-built single-`U` Riemann integrals via POINTWISE FUSION + finite
linearity — NO new convergence machinery beyond the `ConvergesTo`-linearity
lemmas proved here.

## The math (clean reduction to single-`U` integrals)

* POINTWISE FUSION (rational `x`, Clebsch–Gordan):
    `U_c(x)·U_d(x) = Σ_{r ≤ min(c,d)} U_{|c−d|+2r}(x)`  (`Ufusion c d x`).
  We PROVE the GENERAL fusion `U_c·U_d ≈ Ufusion c d` (the repo only had the
  `j = 0,1` folds), by induction on the second index using the Dirichlet-kernel
  fold `twoX_U_fold` (`2x·U_{n+1} = U_{n+2}+U_n`).
* So the `U_cU_d`-weighted Riemann sum
    `orthSum2 c d n = (2/n)·Σ_k U_c(x_k)U_d(x_k)√(1−x_k²)`
  equals `Σ_{r ≤ min(c,d)} orthSum (|c−d|+2r) n` (pointwise fusion + finite-sum
  linearity of the Riemann functional).  This is `orthSum2_eq_fusion_sum`,
  UNCONDITIONAL (pure algebra/linearity).
* Hence the LIMIT
    `∫U_cU_d√ = Σ_{r ≤ min} ∫U_{|c−d|+2r}√ = Σ_{r ≤ min} (semiInt·δ_{·,0})`.
  Each off-diagonal single-`U` integral `∫U_e√ = 0` for `e ≥ 1` is CLOSED through
  `OffDiagClosed` (derivable from the single analytic atom `cellBoundExists`);
  the `e = 0` term is `∫U_0√ = ∫√ = semiInt` (the proved `semiInt`).  Since the
  lowest fusion index is `|c−d|`, the index `0` occurs iff `c = d`, giving the
  Kronecker `δ_{cd}`.
* DIAGONAL (`c = d`): `Ufusion c c` lists `{0, 2, …, 2c}`, so the `r = 0` term is
  `∫U_0√ = semiInt` and all `r ≥ 1` terms are `∫U_{2r}√ = 0` (even off-diagonal).
  Off-diagonal (`c ≠ d`): every fusion index is `≥ |c−d| ≥ 1`, all integrals `0`.

## What is PROVED here (axiom-clean, GENUINE new content)

* `convergesTo_congr_seq` / `convergesTo_add` / `convergesTo_csum` — the
  `ConvergesTo` linearity lemmas the reduction needs (termwise-`Equiv` transport,
  binary additivity, finite-sum additivity).  Proved from scratch (the substrate
  had none beyond `convergesTo_self`).
* `chebU_fusion` — the GENERAL pointwise fusion `U_c(x)·U_d(x) ≈ Ufusion c d x`,
  by two-step induction on the second index.
* `orthSum2` + `orthSum2_eq_fusion_sum` — the pointwise-fusion reduction of the
  bilinear Riemann sum to the fusion sum of single-`U` Riemann sums.
  UNCONDITIONAL (pure algebra/linearity).
* `OffDiagClosed` — the clean hypothesis `∀ e ≥ 1, ConvergesTo (seqOrth e) czero`.
* `offDiagClosed_of_cellBound` — derives `OffDiagClosed` from `cellBoundExists`
  for every even `e ≥ 2` (the single analytic atom; the odd case is
  UNCONDITIONAL).
* `orthMatrix` — the ORTHOGONALITY MATRIX `OffDiagClosed →
  ConvergesTo (orthSum2 c d) (if c = d then semiInt else czero)`, i.e. the Gram
  `[∫U_cU_d√]_{cd} = semiInt·I`, manifestly PSD (`semiInt ≥ 0`).  Includes the
  diagonal `= semiInt` and the off-diagonal `= 0`.

## What is NAMED-open (precisely — the single analytic atom)

* `ChebOrthoBudget.cellBoundExists e` for every even `e ≥ 2` — the summed
  midpoint-quadrature error estimate on the rational approximants of the even
  Riemann sums.  This is the ONE residual; the whole matrix is built CONDITIONAL
  on it (equivalently on the clean hypothesis `OffDiagClosed`), as an HONEST
  hypothesis, not hidden.

## Path to the moment-integral identity + `momentSquare ≥ 0`

The matrix `[∫U_cU_d√]_{cd} = semiInt·I` is the Gram of the `U`-basis w.r.t. the
semicircle weight.  Combined with the `R`-expansion `R = Σ_e r_e U_e` and the
interchange of the (finite) `R`-sum with the integral, it yields the moment-
integral identity `∫U_aU_bR√ = semiInt·G_ab` (next step), whence
`momentSquare = Σ_{ab} c_a c_b ∫U_aU_bR√ = semiInt·Σ_{ab}c_a c_b G_ab ≥ 0` (the
Wall-1 PSD), since `semiInt ≥ 0` and `G` is the proved-PSD fusion-moment Gram.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  Axiom-gate at the foot of the file (`[propext]` /
`[propext, Quot.sound]`).  The conditionality on `cellBoundExists`/`OffDiagClosed`
is an EXPLICIT hypothesis.
-/

import YMGap.Continuum.ChebOrthoBudget
import YMGap.Continuum.ChebOrthogonality
import YMGap.Continuum.SemicircleBoundClosed

namespace YMGap.Continuum.ChebOrthoMatrix

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.SemicircleIntegral

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. `ConvergesTo` linearity (proved from scratch)

The substrate carried only `convergesTo_self`; the reduction needs three
linearity facts: termwise-`Equiv` transport of a limit, binary additivity, and
finite-sum additivity.  All proved approx-wise, splitting `ε`. -/

/-- **Termwise-`Equiv` transport of a limit.**  If `s N ≃ t N` for every `N` and
`s` converges to `L`, then `t` converges to `L`.  (At scale `½ε`: `t_N` is
`½ε`-close to `s_N` (the termwise `Equiv`), which is `½ε`-close to `L`.) -/
theorem convergesTo_congr_seq {s t : Nat → CReal} {L : CReal}
    (hst : ∀ N, CReal.Equiv (s N) (t N)) (hs : CReal.ConvergesTo s L) :
    CReal.ConvergesTo t L := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := hs (HalfPow.half * ε) hhε
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napx1, hap1⟩ := hstage N hN
  -- termwise Equiv (s N) (t N) at scale ½ε
  obtain ⟨Napx2, hap2⟩ := hst N (HalfPow.half * ε) hhε
  refine ⟨max Napx1 Napx2, fun n hn => ?_⟩
  have hn1 : Napx1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Napx2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hs1, hs2⟩ := hap1 n hn1          -- s_N ≤ L+½ε , L ≤ s_N+½ε
  obtain ⟨he1, he2⟩ := hap2 n hn2          -- s_N ≤ t_N+½ε , t_N ≤ s_N+½ε
  refine ⟨?_, ?_⟩
  · -- t_N ≤ s_N + ½ε ≤ (L + ½ε) + ½ε = L + ε
    refine Q'.le_trans' _ _ _ he2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hs1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (L.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (L.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  · -- L ≤ s_N + ½ε ≤ (t_N + ½ε) + ½ε = t_N + ε
    refine Q'.le_trans' _ _ _ hs2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) he1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((t N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left ((t N).approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)

/-- `(a+h)+(b+k) ≃ (a+b)+(h+k)` — the 4-term reassociation/commutation. -/
theorem addSwap4 (a h b k : Q') : ((a + h) + (b + k)) ≈ ((a + b) + (h + k)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a h (b + k)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (h + (b + k)) ((h + b) + k)
      (Q'.eqv_symm (Q'.add_assoc_eqv h b k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a ((h + b) + k) ((b + h) + k)
      (Q'.add_eqv_congr_right (h + b) (b + h) k (Q'.add_comm_eqv h b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a ((b + h) + k) (b + (h + k))
      (Q'.add_assoc_eqv b h k)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a b (h + k))

/-- `(a+½ε)+(b+½ε) ≃ (a+b)+ε`. -/
theorem rearrange4 (a b ε : Q') :
    ((a + HalfPow.half * ε) + (b + HalfPow.half * ε)) ≈ ((a + b) + ε) := by
  refine Q'.eqv_trans _ _ _ (addSwap4 a (HalfPow.half * ε) b (HalfPow.half * ε)) ?_
  exact Q'.add_eqv_congr_left (a + b) (HalfPow.half * ε + HalfPow.half * ε) ε
    (ExpNeg.two_halves ε)

/-- **Binary additivity of `ConvergesTo`.**  If `s → A` and `t → B`, then
`(fun N => add (s N) (t N)) → add A B`.  Approx-wise at scale `½ε`. -/
theorem convergesTo_add {s t : Nat → CReal} {A B : CReal}
    (hs : CReal.ConvergesTo s A) (ht : CReal.ConvergesTo t B) :
    CReal.ConvergesTo (fun N => CReal.add (s N) (t N)) (CReal.add A B) := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨NstA, hstA⟩ := hs (HalfPow.half * ε) hhε
  obtain ⟨NstB, hstB⟩ := ht (HalfPow.half * ε) hhε
  refine ⟨max NstA NstB, fun N hN => ?_⟩
  have hNA : NstA ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hNB : NstB ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  obtain ⟨NapA, hapA⟩ := hstA N hNA
  obtain ⟨NapB, hapB⟩ := hstB N hNB
  refine ⟨max NapA NapB, fun n hn => ?_⟩
  have hnA : NapA ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnB : NapB ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨ha1, ha2⟩ := hapA n hnA          -- s_N ≤ A+½ε , A ≤ s_N+½ε
  obtain ⟨hb1, hb2⟩ := hapB n hnB          -- t_N ≤ B+½ε , B ≤ t_N+½ε
  -- (add (s N) (t N)).approx n = s_N + t_N ; (add A B).approx n = A_n + B_n
  show (s N).approx n + (t N).approx n ≤ (A.approx n + B.approx n) + ε
    ∧ (A.approx n + B.approx n) ≤ ((s N).approx n + (t N).approx n) + ε
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add ha1 hb1) ?_
    exact Q'.le_of_eqv (rearrange4 (A.approx n) (B.approx n) ε)
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add ha2 hb2) ?_
    exact Q'.le_of_eqv (rearrange4 ((s N).approx n) ((t N).approx n) ε)

/-- **Finite-sum additivity of `ConvergesTo`.**  If for each `i < L` the sequence
`S i` converges to `lim i`, then `fun N => csum (fun i => S i N) L` converges to
`csum lim L`.  By induction on `L` using `convergesTo_add` (base: the constant
`czero` sequence converges to `czero`). -/
theorem convergesTo_csum (S : Nat → Nat → CReal) (lim : Nat → CReal)
    (h : ∀ i, CReal.ConvergesTo (S i) (lim i)) :
    ∀ L, CReal.ConvergesTo (fun N => CReal.csum (fun i => S i N) L)
      (CReal.csum lim L)
  | 0 => by
      -- csum _ 0 = czero (constant sequence) converges to czero
      intro ε hε
      refine ⟨0, fun N _ => ⟨0, fun n _ => ?_⟩⟩
      show (CReal.csum (fun i => S i N) 0).approx n ≤ (CReal.csum lim 0).approx n + ε
        ∧ (CReal.csum lim 0).approx n ≤ (CReal.csum (fun i => S i N) 0).approx n + ε
      -- both sides are czero.approx n = 0
      have hz : (CReal.czero).approx n = (0 : Q') := rfl
      refine ⟨?_, ?_⟩
      · show (CReal.czero).approx n ≤ (CReal.czero).approx n + ε
        rw [hz]; exact Q'.add_le_self_of_nonneg (0 : Q') ε (Q'.le_of_lt hε)
      · show (CReal.czero).approx n ≤ (CReal.czero).approx n + ε
        rw [hz]; exact Q'.add_le_self_of_nonneg (0 : Q') ε (Q'.le_of_lt hε)
  | L + 1 => by
      -- csum (..) (L+1) N = add (csum (..) L N) (S L N)
      have ih := convergesTo_csum S lim h L
      -- the target sequence is fun N => add (csum (fun i => S i N) L) (S L N)
      have key := convergesTo_add ih (h L)
      -- rewrite both to the csum-succ form
      have hseq : (fun N => CReal.add (CReal.csum (fun i => S i N) L) (S L N))
          = (fun N => CReal.csum (fun i => S i N) (L + 1)) := by
        funext N; rfl
      have hlim : CReal.add (CReal.csum lim L) (lim L) = CReal.csum lim (L + 1) := rfl
      rw [hseq, hlim] at key
      exact key

/-! ## 1. The GENERAL pointwise fusion `U_c·U_d ≈ Ufusion c d`

The repo (`ChebOrthogonality`) proved only the `j = 0,1` folds.  We prove the
general fusion by two-step induction on the SECOND index, using the
Dirichlet-kernel fold `twoX_U_fold` (`2x·U_{n+1} = U_{n+2}+U_n`) and the bounded
recurrence `U_{n+2} = 2x·U_{n+1} − U_n`.  The fusion sum is the repo's
`Ufusion c d x = Σ_{r ≤ min(c,d)} U_{|c−d|+2r}(x)`. -/

open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOrthogonality
open YMGap.Constructive.RationalTail

/-- The explicit (un-`min`/`max`'d) fusion sum at base index `b`, length `L+1`:
`FS b L x = Σ_{r ≤ L} U_{b+2r}(x)`.  For `d ≤ c` we have
`Ufusion c d x = FS (c−d) d x` (`Ufusion_eq_FS`). -/
def FS (b L : Nat) (x : Q') : Q' :=
  finSum (fun r => Cheb.U (b + 2 * r) x) (L + 1)

/-- `Ufusion c d x = FS (c−d) d x` when `d ≤ c` (then `fusionLow c d = c−d`,
`min c d = d`). -/
theorem Ufusion_eq_FS (c d : Nat) (hdc : d ≤ c) (x : Q') :
    Ufusion c d x = FS (c - d) d x := by
  unfold Ufusion FS
  have hlow : fusionLow c d = c - d := by unfold fusionLow; omega
  have hmin : min c d = d := by omega
  rw [hlow, hmin]

/-- The general fold `2x·U_e = U_{e+1} + U_{e−1}` for `e ≥ 1` (i.e. `e = m+1`):
`2x·U_{m+1} = U_{m+2} + U_m`.  This is `twoX_U_fold`. -/
theorem twoX_fold_pos (m : Nat) (x : Q') :
    (2 : Q') * x * Cheb.U (m + 1) x ≈ Cheb.U (m + 2) x + Cheb.U m x :=
  twoX_U_fold m x

/-- **Distribution of `2x` over a positive-base fusion sum.**  For base
`b = m+1 ≥ 1`:
`2x·FS (m+1) L x ≈ FS (m+2) L x + FS m L x`.
Termwise `2x·U_{(m+1)+2r} = U_{(m+2)+2r} + U_{m+2r}`, then split the sum. -/
theorem twoX_mul_FS_pos (m L : Nat) (x : Q') :
    ((2 : Q') * x) * FS (m + 1) L x ≈ (FS (m + 2) L x + FS m L x) := by
  unfold FS
  -- 2x·Σ_r U_{(m+1)+2r} ≈ Σ_r 2x·U_{(m+1)+2r} ≈ Σ_r (U_{(m+2)+2r} + U_{m+2r})
  --   ≈ Σ_r U_{(m+2)+2r} + Σ_r U_{m+2r}
  -- Step A: pull 2x inside (finSum_const_mul-style, but we use mul_add over finSum).
  have hpull : ((2 : Q') * x) * finSum (fun r => Cheb.U (m + 1 + 2 * r) x) (L + 1)
      ≈ finSum (fun r => ((2 : Q') * x) * Cheb.U (m + 1 + 2 * r) x) (L + 1) := by
    -- (2x)·Σ f ≈ Σ (2x·f) : reverse of finSum_const_mul.  Build by induction.
    induction (L + 1) with
    | zero =>
        show ((2 : Q') * x) * (0 : Q') ≈ (0 : Q')
        exact Q'.mul_zero_eqv ((2 : Q') * x)
    | succ t ih =>
        show ((2 : Q') * x) * (finSum (fun r => Cheb.U (m + 1 + 2 * r) x) t
              + Cheb.U (m + 1 + 2 * t) x)
            ≈ (finSum (fun r => ((2 : Q') * x) * Cheb.U (m + 1 + 2 * r) x) t
              + ((2 : Q') * x) * Cheb.U (m + 1 + 2 * t) x)
        refine Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv ((2 : Q') * x)
            (finSum (fun r => Cheb.U (m + 1 + 2 * r) x) t)
            (Cheb.U (m + 1 + 2 * t) x)) ?_
        exact Q'.add_eqv_congr_right _ _ (((2 : Q') * x) * Cheb.U (m + 1 + 2 * t) x) ih
  refine Q'.eqv_trans _ _ _ hpull ?_
  -- Step B: termwise fold 2x·U_{(m+1)+2r} ≈ U_{(m+2)+2r} + U_{m+2r}
  have hterm : (finSum (fun r => ((2 : Q') * x) * Cheb.U (m + 1 + 2 * r) x) (L + 1))
      ≈ (finSum (fun r => Cheb.U (m + 2 + 2 * r) x + Cheb.U (m + 2 * r) x) (L + 1)) := by
    refine finSum_eqv_congr _ _ (fun r => ?_) (L + 1)
    -- 2x·U_{(m+1)+2r} = 2x·U_{(m+2r)+1} ≈ U_{(m+2r)+2} + U_{m+2r}
    have he : m + 1 + 2 * r = (m + 2 * r) + 1 := by omega
    have he2 : m + 2 + 2 * r = (m + 2 * r) + 2 := by omega
    rw [he, he2]
    exact twoX_fold_pos (m + 2 * r) x
  refine Q'.eqv_trans _ _ _ hterm ?_
  -- Step C: split the sum of a sum.
  exact finSum_add (fun r => Cheb.U (m + 2 + 2 * r) x) (fun r => Cheb.U (m + 2 * r) x) (L + 1)

/-- **Peel the BOTTOM term of `FS`** (base ≥ 0): `FS b (L+1) x = U_b x + FS (b+2) L x`.
The bottom term is `U_b`; the rest reindex to base `b+2`.  Via `finSum_peel_left`. -/
theorem FS_peel_bottom (b L : Nat) (x : Q') :
    FS b (L + 1) x ≈ (Cheb.U b x + FS (b + 2) L x) := by
  unfold FS
  -- FS b (L+1) = Σ_{r<L+2} U_{b+2r}.  peel-left: = U_{b+0} + Σ_{r<L+1} U_{b+2(r+1)}
  have hpl := ChebOrthoOffDiag.finSum_peel_left
    (fun r => Cheb.U (b + 2 * r) x) (L + 1)
  -- hpl : Σ_{r<L+2} U_{b+2r} ≈ U_{b+2·0} + Σ_{r<L+1} U_{b+2(r+1)}
  refine Q'.eqv_trans _ _ _ hpl ?_
  -- U_{b+0} = U_b ; U_{b+2(r+1)} = U_{(b+2)+2r}
  have h0 : b + 2 * 0 = b := by omega
  rw [h0]
  refine Q'.add_eqv_congr_left (Cheb.U b x) _ _ ?_
  refine finSum_eqv_congr _ _ (fun r => ?_) (L + 1)
  have hr : b + 2 * (r + 1) = (b + 2) + 2 * r := by omega
  rw [hr]
  exact Q'.eqv_refl _

/-- The pure additive rearrangement behind `FS_recurrence`:
`u + (a + t) ≈ ((a + t) + (u + a)) + (−a)`. -/
theorem rearrange_recur (a t u : Q') :
    (u + (a + t)) ≈ (((a + t) + (u + a)) + (-a)) := by
  refine Q'.eqv_symm ?_
  -- ((a+t)+(u+a))+(−a) ≈ (a+t)+((u+a)+(−a)) ≈ (a+t)+(u+(a+(−a))) ≈ (a+t)+(u+0) ≈ (a+t)+u ≈ u+(a+t)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (a + t) (u + a) (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a + t) ((u + a) + (-a)) (u + (a + (-a)))
      (Q'.add_assoc_eqv u a (-a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a + t) (u + (a + (-a))) (u + (0 : Q'))
      (Q'.add_eqv_congr_left u (a + (-a)) (0 : Q') (Q'.add_neg_self_eqv a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a + t) (u + (0 : Q')) u
      (by rw [Q'.add_zero']; exact Q'.eqv_refl u)) ?_
  exact Q'.add_comm_eqv (a + t) u

/-- **The fusion recurrence** at a positive base `c−d = m+2 ≥ 2`, i.e. `d+2 ≤ c`:
`FS (m) (d+2) x ≈ 2x·FS (m+1) (d+1) x − FS (m+2) (d) x` is recast as the form
that the induction consumes:  `2x·U_c·U_{d+1} − U_c·U_d = U_c·U_{d+2}` becomes,
after the IHs, a `FS` identity.  We package the precise `FS` algebra that turns
`2x·FS (m+1) (d+1) + (−FS (m+2) d)` into `FS m (d+2)`.

Concretely (base `m = c−d−2`):
  `2x·FS (m+1) (d+1) = FS (m+2) (d+1) + FS m (d+1)`   (`twoX_mul_FS_pos`)
  `FS (m+2) (d+1) = FS (m+2) d + U_{(m+2)+2(d+1)}`     (top peel = `finSum_succ`)
  `FS m (d+1)     = U_m + FS (m+2) d'`? — instead peel BOTTOM of `FS m (d+1)`:
                   `FS m (d+1) = U_m + FS (m+2) d`      (`FS_peel_bottom`)
So `2x·FS(m+1)(d+1) − FS(m+2)(d+1) = FS m (d+1) − U_{(m+2)+2(d+1)}`
  `= (U_m + FS(m+2) d) − U_{(m+2)+2(d+1)}`.  And `FS m (d+2) = U_m + FS(m+2)(d+1)`
  `= U_m + FS(m+2) d + U_{(m+2)+2(d+1)}`.  The `±U_{(m+2)+2(d+1)}` DON'T cancel —
so the correct combination is `2x·FS(m+1)(d+1) − FS(m+2)(d) = FS m (d+2)`, which
is what the polynomial recurrence `U_c U_{d+2} = 2x U_c U_{d+1} − U_c U_d` gives
(IH: `U_c U_{d+1} = FS(m+1)(d+1)`, `U_c U_d = FS(m+2) d`, since `c−(d+1)=m+1`,
`c−d = m+2`).  Verify:
  `2x·FS(m+1)(d+1) − FS(m+2) d = (FS(m+2)(d+1) + FS m (d+1)) − FS(m+2) d`
    `= (FS(m+2) d + U_{(m+2)+2(d+1)}) + (U_m + FS(m+2) d) − FS(m+2) d`
    `= U_m + FS(m+2) d + U_{(m+2)+2(d+1)}`
    `= U_m + FS(m+2)(d+1) = FS m (d+2)`.   ✓ -/
theorem FS_recurrence (m d : Nat) (x : Q') :
    (((2 : Q') * x) * FS (m + 1) (d + 1) x + (-(FS (m + 2) d x)))
      ≈ FS m (d + 2) x := by
  -- LHS via twoX_mul_FS_pos
  have h1 : ((2 : Q') * x) * FS (m + 1) (d + 1) x
      ≈ (FS (m + 2) (d + 1) x + FS m (d + 1) x) := twoX_mul_FS_pos m (d + 1) x
  -- FS (m+2) (d+1) = FS (m+2) d + U_{(m+2)+2(d+1)}   (top peel)
  have hTop : FS (m + 2) (d + 1) x
      = FS (m + 2) d x + Cheb.U ((m + 2) + 2 * (d + 1)) x := by
    unfold FS
    show finSum (fun r => Cheb.U (m + 2 + 2 * r) x) ((d + 1) + 1)
        = finSum (fun r => Cheb.U (m + 2 + 2 * r) x) (d + 1)
          + Cheb.U ((m + 2) + 2 * (d + 1)) x
    rfl
  -- FS m (d+1) = U_m + FS (m+2) d    (bottom peel)
  have hBot : FS m (d + 1) x ≈ (Cheb.U m x + FS (m + 2) d x) := FS_peel_bottom m d x
  -- FS m (d+2) = U_m + FS (m+2) (d+1)   (bottom peel)
  have hGoal : FS m (d + 2) x ≈ (Cheb.U m x + FS (m + 2) (d + 1) x) := by
    have := FS_peel_bottom m (d + 1) x
    -- FS m ((d+1)+1) = U_m + FS (m+2) (d+1)
    simpa using this
  -- Assemble.  Substitute h1, hTop, hBot into LHS; substitute hGoal into RHS.
  -- LHS = (FS(m+2)(d+1) + FS m (d+1)) − FS(m+2) d
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(FS (m + 2) d x)) h1) ?_
  -- now: (FS(m+2)(d+1) + FS m (d+1)) + (−FS(m+2) d) ≈ FS m (d+2)
  -- rewrite FS(m+2)(d+1) = FS(m+2)d + T  (T := U_{(m+2)+2(d+1)}), FS m (d+1) = U_m + FS(m+2)d
  rw [hTop]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(FS (m + 2) d x))
      (Q'.add_eqv_congr_left _ _ _ hBot)) ?_
  -- LHS now: ((FS(m+2)d + T) + (U_m + FS(m+2)d)) + (−FS(m+2)d)
  -- RHS: FS m (d+2) ≈ U_m + FS(m+2)(d+1) = U_m + (FS(m+2)d + T)   [via hGoal, hTop]
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ hGoal ?_
  rw [hTop]
  -- goal (symm): U_m + (FS(m+2)d + T) ≈ ((FS(m+2)d + T) + (U_m + FS(m+2)d)) + (−FS(m+2)d)
  exact rearrange_recur (FS (m + 2) d x) (Cheb.U ((m + 2) + 2 * (d + 1)) x) (Cheb.U m x)

/-- The fusion claim at order `d`: `∀ c ≥ d, U_c·U_d ≈ FS (c−d) d`. -/
def fusionClaim (x : Q') (d : Nat) : Prop :=
  ∀ c, d ≤ c → Cheb.U c x * Cheb.U d x ≈ FS (c - d) d x

/-- Base `d = 0`: `U_c·U_0 = U_c·1 ≈ U_c = FS c 0`. -/
theorem fusionClaim_zero (x : Q') : fusionClaim x 0 := by
  intro c _
  have h0 : Cheb.U c x * Cheb.U 0 x ≈ Cheb.U c x := by
    rw [Cheb.U_zero]; exact Q'.mul_one_eqv (Cheb.U c x)
  refine Q'.eqv_trans _ _ _ h0 ?_
  unfold FS
  show Cheb.U c x ≈ ((0 : Q') + Cheb.U (c - 0 + 2 * 0) x)
  have he : c - 0 + 2 * 0 = c := by omega
  rw [he, Q'.zero_add']
  exact Q'.eqv_refl _

/-- Base `d = 1`: for `c = m+1`, `U_{m+1}·U_1 ≈ U_{m+2}+U_m = FS m 1`. -/
theorem fusionClaim_one (x : Q') : fusionClaim x 1 := by
  intro c hc
  match c, hc with
  | (m + 1), _ =>
      have hfold : Cheb.U (m + 1) x * Cheb.U 1 x ≈ Cheb.U (m + 2) x + Cheb.U m x :=
        chebU_fusion_one m x
      refine Q'.eqv_trans _ _ _ hfold ?_
      unfold FS
      show (Cheb.U (m + 2) x + Cheb.U m x)
          ≈ (((0 : Q') + Cheb.U ((m + 1 - 1) + 2 * 0) x) + Cheb.U ((m + 1 - 1) + 2 * 1) x)
      have e0 : m + 1 - 1 + 2 * 0 = m := by omega
      have e1 : m + 1 - 1 + 2 * 1 = m + 2 := by omega
      rw [e0, e1, Q'.zero_add']
      exact Q'.add_comm_eqv (Cheb.U (m + 2) x) (Cheb.U m x)

/-- **The two-step recursion for fusion.**  `fusionClaim d` and `fusionClaim (d+1)`
imply `fusionClaim (d+2)`, via the polynomial recurrence and `FS_recurrence`. -/
theorem fusionClaim_step (x : Q') (d : Nat)
    (ih1 : fusionClaim x d) (ih2 : fusionClaim x (d + 1)) :
    fusionClaim x (d + 2) := by
      intro c hc
      -- c ≥ d+2.  Let m = c - (d+2), so c - (d+1) = m+1, c - d = m+2.
      have hd1c : d + 1 ≤ c := by omega
      have hdc : d ≤ c := by omega
      -- IHs
      have hIH1 : Cheb.U c x * Cheb.U (d + 1) x ≈ FS (c - (d + 1)) (d + 1) x := ih2 c hd1c
      have hIH2 : Cheb.U c x * Cheb.U d x ≈ FS (c - d) d x := ih1 c hdc
      -- index identities
      have em1 : c - (d + 1) = (c - (d + 2)) + 1 := by omega
      have em2 : c - d = (c - (d + 2)) + 2 := by omega
      rw [em1] at hIH1
      rw [em2] at hIH2
      -- polynomial recurrence: U_{d+2} = 2x·U_{d+1} − U_d, so
      -- U_c·U_{d+2} ≈ 2x·(U_c·U_{d+1}) − U_c·U_d
      have hrec : Cheb.U c x * Cheb.U (d + 2) x
          ≈ (((2 : Q') * x) * (Cheb.U c x * Cheb.U (d + 1) x)
              + (-(Cheb.U c x * Cheb.U d x))) := by
        -- U_{d+2} = (2x)·U_{d+1} + (−U_d)
        rw [Cheb.U_succ_succ d x]
        -- U_c · ((2x)·U_{d+1} + (−U_d)) ≈ U_c·((2x)·U_{d+1}) + U_c·(−U_d)
        refine Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv (Cheb.U c x) ((2 : Q') * x * Cheb.U (d + 1) x)
            (-(Cheb.U d x))) ?_
        refine Q'.add_eqv_congr' ?_ ?_
        · -- U_c·((2x)·U_{d+1}) ≈ (2x)·(U_c·U_{d+1})
          -- U_c·((2x)·U_{d+1}) ≈ U_c·(U_{d+1}·(2x)) ≈ (U_c·U_{d+1})·(2x) ≈ (2x)·(U_c·U_{d+1})
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv ((2:Q')*x) (Cheb.U (d+1) x))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv (Cheb.U c x) (Cheb.U (d+1) x) ((2:Q')*x))) ?_
          exact Q'.mul_comm_eqv (Cheb.U c x * Cheb.U (d+1) x) ((2:Q')*x)
        · -- U_c·(−U_d) ≈ −(U_c·U_d)
          exact Q'.mul_neg_eqv (Cheb.U c x) (Cheb.U d x)
      refine Q'.eqv_trans _ _ _ hrec ?_
      -- substitute IHs
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hIH1)
          (Q'.neg_eqv_congr _ _ hIH2)) ?_
      -- now: 2x·FS((c-(d+2))+1)(d+1) + (−FS((c-(d+2))+2) d) ≈ FS (c-(d+2)) (d+2)
      exact FS_recurrence (c - (d + 2)) d x

/-- Two-step induction packager: `fusionClaim d ∧ fusionClaim (d+1)` for all `d`. -/
theorem fusionClaim_pair (x : Q') :
    ∀ d, fusionClaim x d ∧ fusionClaim x (d + 1) := by
  intro d
  induction d with
  | zero => exact ⟨fusionClaim_zero x, fusionClaim_one x⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, fusionClaim_step x k hk hk1⟩

/-- **The `c ≥ d` explicit fusion** `U_c·U_d ≈ FS (c−d) d`. -/
theorem fusion_ge (x : Q') (d c : Nat) (hdc : d ≤ c) :
    Cheb.U c x * Cheb.U d x ≈ FS (c - d) d x :=
  (fusionClaim_pair x d).1 c hdc

/-- **GENERAL pointwise fusion** `U_c(x)·U_d(x) ≈ Ufusion c d x` for all `c, d`.
For `d ≤ c` it is `fusion_ge` transported through `Ufusion_eq_FS`; for `c < d`
use commutativity (`Ufusion` is symmetric, `fusionLow`/`min` symmetric). -/
theorem chebU_fusion (c d : Nat) (x : Q') :
    Cheb.U c x * Cheb.U d x ≈ Ufusion c d x := by
  rcases Nat.le_total d c with hdc | hcd
  · rw [Ufusion_eq_FS c d hdc]
    exact fusion_ge x d c hdc
  · -- c ≤ d : U_c·U_d ≈ U_d·U_c ≈ FS (d−c) c = Ufusion d c = Ufusion c d
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Cheb.U c x) (Cheb.U d x)) ?_
    refine Q'.eqv_trans _ _ _ (fusion_ge x c d hcd) ?_
    rw [← Ufusion_eq_FS d c hcd]
    -- Ufusion d c x = Ufusion c d x  (symmetry of fusionLow + min)
    unfold Ufusion
    have hlow : fusionLow d c = fusionLow c d := fusionLow_comm d c
    have hmin : min d c = min c d := Nat.min_comm d c
    rw [hlow, hmin]
    exact Q'.eqv_refl _

/-! ## 2. The bilinear Riemann sum `orthSum2` and its fusion reduction

`orthSum2 c d n = (2/n)·Σ_k U_c(x_k)·U_d(x_k)·√(1−x_k²)`.  The pointwise fusion
turns the per-node product `U_c·U_d` into `Σ_{r ≤ min} U_{|c−d|+2r}`, and
finite-sum linearity of the Riemann functional gives the fusion-sum reduction. -/

/-- The lowest fusion index of `(c,d)` = `|c−d|`. -/
def low (c d : Nat) : Nat := ChebOrthogonality.fusionLow c d

/-- The number of fusion terms = `min c d + 1`. -/
def fusLen (c d : Nat) : Nat := min c d + 1

/-- The bilinear per-node summand `(2/n)·U_c(x_k)·U_d(x_k)·√(1−x_k²)`. -/
def orthTerm2 (c d : Nat) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (lebW n hn))
    (CReal.mul (CReal.ofQ' (uNode c n hn k * uNode d n hn k)) (nodeWeight n hn k))

/-- **The bilinear orthogonality Riemann sum**
`orthSum2 c d n = (2/n)·Σ_{k<n} U_c(x_k)·U_d(x_k)·√(1−x_k²)`. -/
def orthSum2 (c d : Nat) (n : Nat) (hn : 0 < n) : CReal :=
  CReal.csum (orthTerm2 c d n hn) n

/-- **Per-node fusion of the product value** (as `CReal`):
`ofQ'(U_c(x_k)·U_d(x_k)) ≈ Σ_{r < min+1} ofQ'(U_{|c−d|+2r}(x_k))`.  From the
pointwise `Q'` fusion `chebU_fusion` plus `ofQ'`-additivity over the finite sum. -/
theorem ofQ'_uNode_fusion (c d : Nat) (n : Nat) (hn : 0 < n) (k : Nat) :
    CReal.Equiv (CReal.ofQ' (uNode c n hn k * uNode d n hn k))
      (CReal.csum (fun r => CReal.ofQ' (uNode (low c d + 2 * r) n hn k)) (fusLen c d)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- LHS approx = U_c(x_k)·U_d(x_k) ; RHS approx = Σ_r U_{low+2r}(x_k) (as Q')
  show (uNode c n hn k * uNode d n hn k)
      ≈ (CReal.csum (fun r => CReal.ofQ' (uNode (low c d + 2 * r) n hn k)) (fusLen c d)).approx p
  rw [CReal.csum_approx]
  -- = finSum (fun r => U_{low+2r}(x_k)) (min+1) = Ufusion c d (x_k)
  -- chebU_fusion : U_c(x_k)·U_d(x_k) ≈ Ufusion c d (x_k)
  have hfus := chebU_fusion c d (RiemannSOS.uniformMidpoint n hn k)
  -- unfold uNode and Ufusion to align the finSum
  show (Cheb.U c (RiemannSOS.uniformMidpoint n hn k)
        * Cheb.U d (RiemannSOS.uniformMidpoint n hn k))
      ≈ RationalTail.finSum
          (fun r => (CReal.ofQ' (uNode (low c d + 2 * r) n hn k)).approx p) (fusLen c d)
  refine Q'.eqv_trans _ _ _ hfus ?_
  -- Ufusion c d (x_k) = finSum (fun r => U_{low+2r}(x_k)) (min+1) ; matches RHS
  show ChebOrthogonality.Ufusion c d (RiemannSOS.uniformMidpoint n hn k)
      ≈ RationalTail.finSum
          (fun r => (CReal.ofQ' (uNode (low c d + 2 * r) n hn k)).approx p) (fusLen c d)
  unfold ChebOrthogonality.Ufusion fusLen low uNode
  -- both sides are finSum (fun r => U (fusionLow c d + 2r) (x_k)) (min c d + 1)
  exact Q'.eqv_refl _

/-- **The pointwise-fusion reduction of the bilinear summand to the fusion sum of
single-`U` summands.**  `orthTerm2 c d n k ≈ Σ_{r < min+1} orthTerm (|c−d|+2r) n k`.
Pulls `ofQ'`-fusion of the product through the weight `lebW·(_·nodeWeight)`. -/
theorem orthTerm2_eq_fusion (c d : Nat) (n : Nat) (hn : 0 < n) (k : Nat) :
    CReal.Equiv (orthTerm2 c d n hn k)
      (CReal.csum (fun r => orthTerm (low c d + 2 * r) n hn k) (fusLen c d)) := by
  unfold orthTerm2 orthTerm
  -- goal: lebW · (ofQ'(U_cU_d) · w) ≈ Σ_{r<L} lebW·(ofQ'(U_{low+2r}) · w)
  -- Step 1: ofQ'(U_cU_d) ≈ Σ_r ofQ'(U_{low+2r})  ⇒  lebW·(ofQ'(U_cU_d)·w) ≈ lebW·((Σ)·w)
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_right
      (CRealContinuumAlg.cmul_congr_left (ofQ'_uNode_fusion c d n hn k))) ?_
  -- Step 2: (Σ g)·w ≈ Σ_r (g r·w)  (right-distribute the constant w over the sum)
  have hdist : CReal.Equiv
      (CReal.mul (CReal.csum (fun r => CReal.ofQ' (uNode (low c d + 2 * r) n hn k)) (fusLen c d))
        (nodeWeight n hn k))
      (CReal.csum (fun r => CReal.mul (CReal.ofQ' (uNode (low c d + 2 * r) n hn k))
        (nodeWeight n hn k)) (fusLen c d)) := by
    -- (Σ g)·w ≈ w·(Σ g) ≈ Σ_r w·(g r) ≈ Σ_r (g r·w)
    refine CReal.Equiv.trans
      (CRealAlg.cmul_comm
        (CReal.csum (fun r => CReal.ofQ' (uNode (low c d + 2 * r) n hn k)) (fusLen c d))
        (nodeWeight n hn k)) ?_
    refine CReal.Equiv.trans
      (CReal.Equiv.symm (CRealContinuumAlg.csum_const_mul (nodeWeight n hn k)
        (fun r => CReal.ofQ' (uNode (low c d + 2 * r) n hn k)) (fusLen c d))) ?_
    exact CRealContinuumAlg.csum_congr
      (fun r => CRealAlg.cmul_comm (nodeWeight n hn k)
        (CReal.ofQ' (uNode (low c d + 2 * r) n hn k))) (fusLen c d)
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hdist) ?_
  -- Step 3: lebW·(Σ_r (g r·w)) ≈ Σ_r lebW·(g r·w)
  exact CReal.Equiv.symm
    (CRealContinuumAlg.csum_const_mul (CReal.ofQ' (lebW n hn))
      (fun r => CReal.mul (CReal.ofQ' (uNode (low c d + 2 * r) n hn k)) (nodeWeight n hn k))
      (fusLen c d))

/-- **`orthSum2_eq_fusion_sum` — THE POINTWISE-FUSION REDUCTION (UNCONDITIONAL).**
The bilinear Riemann sum is the fusion sum of single-`U` Riemann sums:
`orthSum2 c d n ≈ Σ_{r < min+1} orthSum (|c−d|+2r) n`.  Pure algebra/linearity:
per-node fusion (`orthTerm2_eq_fusion`) + finite-sum index swap
(`csum_swap_creal`). -/
theorem orthSum2_eq_fusion_sum (c d : Nat) (n : Nat) (hn : 0 < n) :
    CReal.Equiv (orthSum2 c d n hn)
      (CReal.csum (fun r => orthSum (low c d + 2 * r) n hn) (fusLen c d)) := by
  unfold orthSum2 orthSum
  -- Σ_k orthTerm2 c d n k ≈ Σ_k Σ_r orthTerm (low+2r) n k  ≈ Σ_r Σ_k orthTerm (low+2r) n k
  refine CReal.Equiv.trans
    (CRealContinuumAlg.csum_congr (fun k => orthTerm2_eq_fusion c d n hn k) n) ?_
  -- swap (k outer, r inner) ↔ (r outer, k inner)
  exact ChebOrthogonality.csum_swap_creal
    (fun k r => orthTerm (low c d + 2 * r) n hn k) n (fusLen c d)

/-! ## 3. The clean conditionality `OffDiagClosed` and its derivation

`OffDiagClosed` packages the single analytic atom in its cleanest usable form: the
off-diagonal single-`U` Riemann sums converge to `czero`.  It is derivable from
`ChebOrthoBudget.cellBoundExists` (for the even members; the odd members are
unconditional). -/

/-- **The clean conditionality hypothesis.**  Every off-diagonal single-`U`
Riemann sum converges to `czero`: `∀ e ≥ 1, ConvergesTo (seqOrth e) czero`. -/
def OffDiagClosed : Prop :=
  ∀ e : Nat, 1 ≤ e → CReal.ConvergesTo (seqOrth e) CReal.czero

/-- **`OffDiagClosed` from the single analytic atom.**  Given
`ChebOrthoBudget.cellBoundExists e` for every even `e ≥ 2`, the combined
off-diagonal orthogonality (`offdiag_closed_of_cellBound`, odd UNCONDITIONAL)
gives, for each `e ≥ 1`, a limit `L` with `ConvergesTo (seqOrth e) L` and
`L ≃ czero`; transporting the limit (`convergesTo_congr_seq` on the constant
relation, equivalently re-targeting the limit) yields `ConvergesTo (seqOrth e)
czero`. -/
theorem offDiagClosed_of_cellBound
    (hcb : ∀ (e : Nat), 2 ≤ e → e % 2 = 0 → ChebOrthoBudget.cellBoundExists e) :
    OffDiagClosed := by
  intro e he
  obtain ⟨L, hConv, hLzero⟩ := ChebOrthoBudget.offdiag_closed_of_cellBound hcb e he
  -- ConvergesTo (seqOrth e) L and L ≃ czero ⇒ ConvergesTo (seqOrth e) czero.
  -- Use convergesTo_congr_seq with the IDENTITY sequence transport is not the
  -- right tool; instead re-target the limit directly.
  exact convergesTo_retarget hConv hLzero
where
  /-- Re-target a limit along an `Equiv`: `s → L`, `L ≃ L'` ⇒ `s → L'`. -/
  convergesTo_retarget {s : Nat → CReal} {L L' : CReal}
      (hs : CReal.ConvergesTo s L) (hLL' : CReal.Equiv L L') :
      CReal.ConvergesTo s L' := by
    intro ε hε
    have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
    obtain ⟨Nstage, hstage⟩ := hs (HalfPow.half * ε) hhε
    obtain ⟨NL, hNL⟩ := hLL' (HalfPow.half * ε) hhε
    refine ⟨Nstage, fun N hN => ?_⟩
    obtain ⟨Napx, hap⟩ := hstage N hN
    refine ⟨max Napx NL, fun n hn => ?_⟩
    have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hn2 : NL ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    obtain ⟨hs1, hs2⟩ := hap n hn1            -- s_N ≤ L+½ε , L ≤ s_N+½ε
    obtain ⟨hL1, hL2⟩ := hNL n hn2            -- L ≤ L'+½ε , L' ≤ L+½ε
    refine ⟨?_, ?_⟩
    · -- s_N ≤ L+½ε ≤ (L'+½ε)+½ε = L'+ε
      refine Q'.le_trans' _ _ _ hs1 ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hL1) ?_
      refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (L'.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
      exact Q'.add_eqv_congr_left (L'.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
        (ExpNeg.two_halves ε)
    · -- L' ≤ L+½ε ≤ (s_N+½ε)+½ε = s_N+ε
      refine Q'.le_trans' _ _ _ hL2 ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hs2) ?_
      refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv ((s N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
      exact Q'.add_eqv_congr_left ((s N).approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
        (ExpNeg.two_halves ε)

/-! ## 4. The diagonal limit `∫U_0√ = semiInt` and the orthogonality matrix

The `e = 0` single-`U` Riemann sum IS the semicircle sum (`U_0 = 1`), so its limit
is the proved `semiInt`.  Combined with `OffDiagClosed` and the fusion reduction,
the bilinear limit is `semiInt·δ_{cd}`. -/

/-- `seqOrth 0` is termwise-`Equiv` to `seqSemi` (`U_0 = 1`, so the extra rational
factor is `1`). -/
theorem seqOrth0_equiv_seqSemi (N : Nat) :
    CReal.Equiv (seqOrth 0 N) (seqSemi N) := by
  -- seqOrth 0 N = orthSum 0 (N+1) ; seqSemi N = semiSum (N+1)
  show CReal.Equiv (orthSum 0 (N + 1) (Nat.succ_pos N)) (semiSum (N + 1) (Nat.succ_pos N))
  unfold orthSum semiSum
  refine CRealContinuumAlg.csum_congr (fun k => ?_) (N + 1)
  -- orthTerm 0 ... k = lebW·(ofQ'(U_0(x_k))·w) ; semiTerm = lebW·w.
  -- U_0(x_k) = 1, so ofQ'(1) ≈ cone and ofQ'(1)·w ≈ w.
  unfold orthTerm
  refine CRealContinuumAlg.cmul_congr_right ?_
  -- ofQ'(uNode 0 ...)·w ≈ w
  have h1 : uNode 0 (N + 1) (Nat.succ_pos N) k = (1 : Q') := by
    unfold uNode; rw [Cheb.U_zero]
  rw [h1]
  -- ofQ'(1)·w ≈ w
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_left ?_) (CRealAlg.cone_mul _)
  -- ofQ'(1) ≈ cone
  exact Pivot2.equiv_refl _

/-- **The `e = 0` single-`U` limit is `semiInt`.**  `ConvergesTo (seqOrth 0)
semiInt`, since `seqOrth 0 ≃ seqSemi` termwise and `seqSemi → semiInt`. -/
theorem seqOrth0_converges_semiInt :
    CReal.ConvergesTo (seqOrth 0) SemicircleBoundClosed.semiInt :=
  convergesTo_congr_seq (fun N => CReal.Equiv.symm (seqOrth0_equiv_seqSemi N))
    SemicircleBoundClosed.semiInt_converges

/-! ### The fusion sequence and its limit -/

/-- The resolution-indexed bilinear sum `seqOrth2 c d N = orthSum2 c d (N+1)`. -/
def seqOrth2 (c d : Nat) : Nat → CReal :=
  fun N => orthSum2 c d (N + 1) (Nat.succ_pos N)

/-- `seqOrth2 c d` is termwise-`Equiv` to the fusion `csum` of the single-`U`
sequences `seqOrth (|c−d|+2r)` (the resolution-indexed `orthSum2_eq_fusion_sum`). -/
theorem seqOrth2_eq_fusion (c d N : Nat) :
    CReal.Equiv (seqOrth2 c d N)
      (CReal.csum (fun r => seqOrth (low c d + 2 * r) N) (fusLen c d)) := by
  show CReal.Equiv (orthSum2 c d (N + 1) (Nat.succ_pos N))
    (CReal.csum (fun r => orthSum (low c d + 2 * r) (N + 1) (Nat.succ_pos N)) (fusLen c d))
  exact orthSum2_eq_fusion_sum c d (N + 1) (Nat.succ_pos N)

/-- The per-member limit of the single-`U` fusion sequence, GIVEN `OffDiagClosed`:
`semiInt` for the `r = 0` member when `low = 0` (diagonal), `czero` otherwise.
We record the limit as `if low c d + 2*r = 0 then semiInt else czero`. -/
def fusMemberLim (c d r : Nat) : CReal :=
  if low c d + 2 * r = 0 then SemicircleBoundClosed.semiInt else CReal.czero

/-- Each single-`U` fusion-member sequence converges to `fusMemberLim`, GIVEN
`OffDiagClosed`.  The `e = 0` member uses `seqOrth0_converges_semiInt`; the
`e ≥ 1` members use `OffDiagClosed`. -/
theorem fusMember_converges (h : OffDiagClosed) (c d r : Nat) :
    CReal.ConvergesTo (seqOrth (low c d + 2 * r)) (fusMemberLim c d r) := by
  unfold fusMemberLim
  rcases Nat.decEq (low c d + 2 * r) 0 with he | he
  · rw [if_neg he]
    have h1 : 1 ≤ low c d + 2 * r := Nat.one_le_iff_ne_zero.mpr he
    exact h (low c d + 2 * r) h1
  · rw [if_pos he, he]
    exact seqOrth0_converges_semiInt

/-- The fusion-`csum` of the limits.  `Σ_{r < min+1} fusMemberLim c d r`. -/
def fusLimSum (c d : Nat) : CReal :=
  CReal.csum (fun r => fusMemberLim c d r) (fusLen c d)

/-- **`seqOrth2 c d` converges to `fusLimSum c d`, GIVEN `OffDiagClosed`.**  By
`convergesTo_csum` (each member converges) transported through the termwise fusion
`seqOrth2_eq_fusion`. -/
theorem seqOrth2_converges (h : OffDiagClosed) (c d : Nat) :
    CReal.ConvergesTo (seqOrth2 c d) (fusLimSum c d) := by
  -- the fusion-csum sequence converges to the csum of limits
  have hcsum : CReal.ConvergesTo
      (fun N => CReal.csum (fun r => seqOrth (low c d + 2 * r) N) (fusLen c d))
      (CReal.csum (fun r => fusMemberLim c d r) (fusLen c d)) :=
    convergesTo_csum (fun r => seqOrth (low c d + 2 * r))
      (fun r => fusMemberLim c d r) (fun r => fusMember_converges h c d r) (fusLen c d)
  -- transport along termwise fusion (seqOrth2 N ≃ the csum sequence)
  exact convergesTo_congr_seq (fun N => CReal.Equiv.symm (seqOrth2_eq_fusion c d N)) hcsum

/-! ### Evaluating `fusLimSum` to `semiInt·δ_{cd}` -/

/-- `low c c = 0` (the diagonal lowest index `|c−c| = 0`).  Proved without `omega`
on `max`/`min` (which would pull `Classical.choice`): `max c c = c`, `min c c = c`,
`c − c = 0`. -/
theorem low_self_zero (c : Nat) : low c c = 0 := by
  unfold low ChebOrthogonality.fusionLow
  rw [Nat.max_self, Nat.min_self, Nat.sub_self]

/-- `0 < low c d` when `c ≠ d` (the off-diagonal lowest index `|c−d| ≥ 1`).
Proved by case analysis on `Nat.le_total` (avoids `omega` on `max`/`min`). -/
theorem low_pos_of_ne (c d : Nat) (hcd : c ≠ d) : 0 < low c d := by
  unfold low ChebOrthogonality.fusionLow
  rcases Nat.le_total c d with h | h
  · -- max = d, min = c, d − c > 0 since c < d
    rw [Nat.max_eq_right h, Nat.min_eq_left h]
    exact Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne h hcd)
  · -- max = c, min = d, c − d > 0 since d < c
    rw [Nat.max_eq_left h, Nat.min_eq_right h]
    exact Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne h (fun he => hcd he.symm))

/-- **Off-diagonal evaluation:** for `c ≠ d`, every fusion member has limit
`czero`, so `fusLimSum c d ≃ czero`. -/
theorem fusLimSum_offdiag (c d : Nat) (hcd : c ≠ d) :
    CReal.Equiv (fusLimSum c d) CReal.czero := by
  unfold fusLimSum
  -- every member is czero (low c d ≥ 1 since c ≠ d, so low+2r ≥ 1 ≠ 0)
  have hlow : low c d ≠ 0 := Nat.pos_iff_ne_zero.mp (low_pos_of_ne c d hcd)
  have hmem : ∀ r, CReal.Equiv (fusMemberLim c d r) CReal.czero := by
    intro r
    unfold fusMemberLim
    have hne : low c d + 2 * r ≠ 0 := by omega
    rw [if_neg hne]
    exact Pivot2.equiv_refl _
  -- Σ czero ≃ czero
  refine CReal.Equiv.trans (CRealContinuumAlg.csum_congr hmem (fusLen c d)) ?_
  -- csum (fun _ => czero) (fusLen) ≃ czero
  exact csum_czero_equiv (fusLen c d)
where
  /-- `csum (fun _ => czero) m ≃ czero`. -/
  csum_czero_equiv (m : Nat) : CReal.Equiv (CReal.csum (fun _ => CReal.czero) m) CReal.czero := by
    refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
    rw [CReal.csum_approx]
    -- finSum (fun _ => czero.approx p) m = finSum (fun _ => 0) m = 0 = czero.approx p
    show (RationalTail.finSum (fun _ => (CReal.czero).approx p) m) ≈ ((CReal.czero).approx p)
    have hz : (fun _ => (CReal.czero).approx p) = (fun _ : Nat => (0 : Q')) := rfl
    rw [hz, RationalTail.finSum_zero_seq]
    exact Q'.eqv_refl _

/-- **Diagonal evaluation:** for `c = d`, `low c d = 0`, the `r = 0` member has
limit `semiInt` and all `r ≥ 1` members have limit `czero`, so
`fusLimSum c c ≃ semiInt`. -/
theorem fusLimSum_diag (c : Nat) :
    CReal.Equiv (fusLimSum c c) SemicircleBoundClosed.semiInt := by
  unfold fusLimSum
  have hlow : low c c = 0 := low_self_zero c
  -- fusLen c c = c + 1.  The members: r=0 ↦ semiInt (low+0 = 0), r≥1 ↦ czero.
  have hfusLen : fusLen c c = c + 1 := by unfold fusLen; rw [Nat.min_self]
  rw [hfusLen]
  -- csum f (c+1) = csum (fun r => f (r+1)) c + f 0 ... use peel-left structure.
  -- Easier: members r≥1 are czero; member 0 is semiInt.  Build directly.
  -- csum f (c+1) ≃ semiInt where f r = fusMemberLim c c r.
  refine peel_first_semiInt c hlow
where
  /-- `csum (fusMemberLim c c) (c+1) ≃ semiInt` when `low c c = 0`. -/
  peel_first_semiInt (c : Nat) (hlow : low c c = 0) :
      CReal.Equiv (CReal.csum (fun r => fusMemberLim c c r) (c + 1))
        SemicircleBoundClosed.semiInt := by
    -- csum f (c+1) = add (csum f c) (f c).  All of csum f ... for r in [0,c]:
    -- f 0 = semiInt (low+0=0), f r = czero for r ≥ 1.
    -- Prove by induction: csum f (k+1) ≃ semiInt for all k, given f 0 = semiInt, f (j+1)=czero.
    have hf0 : CReal.Equiv (fusMemberLim c c 0) SemicircleBoundClosed.semiInt := by
      unfold fusMemberLim
      have : low c c + 2 * 0 = 0 := by omega
      rw [if_pos this]
      exact Pivot2.equiv_refl _
    have hfj : ∀ j, CReal.Equiv (fusMemberLim c c (j + 1)) CReal.czero := by
      intro j
      unfold fusMemberLim
      have hne : low c c + 2 * (j + 1) ≠ 0 := by omega
      rw [if_neg hne]
      exact Pivot2.equiv_refl _
    -- induction on c giving csum f (k+1) ≃ semiInt
    have key : ∀ k, CReal.Equiv (CReal.csum (fun r => fusMemberLim c c r) (k + 1))
        SemicircleBoundClosed.semiInt := by
      intro k
      induction k with
      | zero =>
          -- csum f 1 = add czero (f 0) ≃ f 0 ≃ semiInt
          show CReal.Equiv (CReal.add (CReal.csum (fun r => fusMemberLim c c r) 0)
            (fusMemberLim c c 0)) SemicircleBoundClosed.semiInt
          refine CReal.Equiv.trans ?_ hf0
          -- add czero (f 0) ≃ f 0
          refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
          show ((CReal.czero).approx p + (fusMemberLim c c 0).approx p)
              ≈ (fusMemberLim c c 0).approx p
          have hz : (CReal.czero).approx p = (0 : Q') := rfl
          rw [hz, Q'.zero_add']
          exact Q'.eqv_refl _
      | succ t ih =>
          -- csum f (t+2) = add (csum f (t+1)) (f (t+1)) ≃ add semiInt czero ≃ semiInt
          show CReal.Equiv (CReal.add (CReal.csum (fun r => fusMemberLim c c r) (t + 1))
            (fusMemberLim c c (t + 1))) SemicircleBoundClosed.semiInt
          refine CReal.Equiv.trans
            (Pivot2.add_congr ih (hfj t)) ?_
          -- add semiInt czero ≃ semiInt
          refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
          show ((SemicircleBoundClosed.semiInt).approx p + (CReal.czero).approx p)
              ≈ (SemicircleBoundClosed.semiInt).approx p
          have hz : (CReal.czero).approx p = (0 : Q') := rfl
          rw [hz, Q'.add_zero']
          exact Q'.eqv_refl _
    exact key c

/-! ### The orthogonality matrix -/

/-- **THE ORTHOGONALITY MATRIX `[∫U_cU_d√]_{cd} = semiInt·δ_{cd}`.**  GIVEN
`OffDiagClosed`, the bilinear Riemann sum `seqOrth2 c d` converges to
`if c = d then semiInt else czero`.  This is the Gram of the Chebyshev-`U` basis
w.r.t. the semicircle weight `√(1−x²)`, equal to `semiInt·I`, manifestly PSD
(`semiInt ≥ 0`, `SemicircleBoundClosed.semiInt_nonneg`).  π-FREE (`semiInt` an
abstract positive constant). -/
theorem orthMatrix (h : OffDiagClosed) (c d : Nat) :
    CReal.ConvergesTo (seqOrth2 c d)
      (if c = d then SemicircleBoundClosed.semiInt else CReal.czero) := by
  rcases Nat.decEq c d with hcd | hcd
  · rw [if_neg hcd]
    exact convergesTo_retarget (seqOrth2_converges h c d) (fusLimSum_offdiag c d hcd)
  · subst hcd
    rw [if_pos rfl]
    exact convergesTo_retarget (seqOrth2_converges h c c) (fusLimSum_diag c)
where
  /-- Re-target a limit along an `Equiv`. -/
  convergesTo_retarget {s : Nat → CReal} {L L' : CReal}
      (hs : CReal.ConvergesTo s L) (hLL' : CReal.Equiv L L') :
      CReal.ConvergesTo s L' := by
    intro ε hε
    have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
    obtain ⟨Nstage, hstage⟩ := hs (HalfPow.half * ε) hhε
    obtain ⟨NL, hNL⟩ := hLL' (HalfPow.half * ε) hhε
    refine ⟨Nstage, fun N hN => ?_⟩
    obtain ⟨Napx, hap⟩ := hstage N hN
    refine ⟨max Napx NL, fun n hn => ?_⟩
    have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hn2 : NL ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    obtain ⟨hs1, hs2⟩ := hap n hn1
    obtain ⟨hL1, hL2⟩ := hNL n hn2
    refine ⟨?_, ?_⟩
    · refine Q'.le_trans' _ _ _ hs1 ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hL1) ?_
      refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (L'.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
      exact Q'.add_eqv_congr_left (L'.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
        (ExpNeg.two_halves ε)
    · refine Q'.le_trans' _ _ _ hL2 ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hs2) ?_
      refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv ((s N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
      exact Q'.add_eqv_congr_left ((s N).approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
        (ExpNeg.two_halves ε)

/-- **The diagonal limit `= semiInt`.**  Specialization of `orthMatrix`. -/
theorem orthMatrix_diag (h : OffDiagClosed) (c : Nat) :
    CReal.ConvergesTo (seqOrth2 c c) SemicircleBoundClosed.semiInt := by
  have := orthMatrix h c c
  rwa [if_pos rfl] at this

/-- **The off-diagonal limit `= czero`.**  Specialization of `orthMatrix`. -/
theorem orthMatrix_offdiag (h : OffDiagClosed) (c d : Nat) (hcd : c ≠ d) :
    CReal.ConvergesTo (seqOrth2 c d) CReal.czero := by
  have := orthMatrix h c d
  rwa [if_neg hcd] at this

/-- **PSD witness:** the diagonal value `semiInt` is nonnegative (`semiInt ≥ 0`),
so the orthogonality matrix `semiInt·I` is manifestly PSD. -/
theorem orthMatrix_diag_nonneg : ExpPos.geRat SemicircleBoundClosed.semiInt 0 :=
  SemicircleBoundClosed.semiInt_nonneg

end YMGap.Continuum.ChebOrthoMatrix

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `convergesTo_congr_seq` / `convergesTo_add` / `convergesTo_csum` — the
    `ConvergesTo` linearity lemmas (termwise-`Equiv` transport, binary and
    finite-sum additivity), built from scratch.
  * `chebU_fusion` — the GENERAL pointwise fusion `U_c(x)·U_d(x) ≈ Ufusion c d x`
    for ALL `c, d` (the repo had only the `j = 0,1` folds), by two-step induction
    on the second index through the Dirichlet-kernel fold `twoX_U_fold` and the
    `FS`-recurrence telescope.
  * `orthSum2` + `orthSum2_eq_fusion_sum` — the POINTWISE-FUSION REDUCTION of the
    bilinear Riemann sum to the fusion sum of single-`U` Riemann sums,
    UNCONDITIONAL (pure algebra/linearity: per-node fusion + `csum` index swap).
  * `OffDiagClosed` (the clean hypothesis) + `offDiagClosed_of_cellBound` (derive
    it from `ChebOrthoBudget.cellBoundExists` for even `e ≥ 2`; odd UNCONDITIONAL).
  * `seqOrth0_converges_semiInt` — the `e = 0` single-`U` limit IS `semiInt`
    (`U_0 = 1`, so `seqOrth 0 ≃ seqSemi`), UNCONDITIONAL.
  * `orthMatrix` — THE ORTHOGONALITY MATRIX `OffDiagClosed → ConvergesTo
    (seqOrth2 c d) (if c = d then semiInt else czero)`, i.e. the Gram
    `[∫U_cU_d√]_{cd} = semiInt·I`, with `orthMatrix_diag` (`= semiInt`),
    `orthMatrix_offdiag` (`= 0`), and `orthMatrix_diag_nonneg` (PSD witness
    `semiInt ≥ 0`).  π-FREE.

**NAMED-open (the honest residual — the single analytic atom).**
  * `ChebOrthoBudget.cellBoundExists e` for every even `e ≥ 2` — the summed
    midpoint-quadrature error estimate on the rational approximants of the even
    Riemann sums.  The ENTIRE matrix is built CONDITIONAL on this (equivalently on
    the clean hypothesis `OffDiagClosed`), as an EXPLICIT hypothesis, not hidden.
    The odd off-diagonal members are UNCONDITIONAL; the `e = 0` member is the
    proved `semiInt`.

**Path to the moment-integral identity + `momentSquare ≥ 0`.**  The matrix
`[∫U_cU_d√]_{cd} = semiInt·I` is the Gram of the `U`-basis w.r.t. the semicircle
weight.  With the `R`-expansion `R = Σ_e r_e U_e` and the interchange of the finite
`R`-sum with the integral, it gives `∫U_aU_bR√ = semiInt·G_ab`, whence
`momentSquare = semiInt·Σ_{ab}c_a c_b G_ab ≥ 0` (Wall-1 PSD), since `semiInt ≥ 0`
(`orthMatrix_diag_nonneg`) and `G` is the proved-PSD fusion-moment Gram.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` not used. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoMatrix.convergesTo_congr_seq
#print axioms YMGap.Continuum.ChebOrthoMatrix.convergesTo_add
#print axioms YMGap.Continuum.ChebOrthoMatrix.convergesTo_csum
#print axioms YMGap.Continuum.ChebOrthoMatrix.chebU_fusion
#print axioms YMGap.Continuum.ChebOrthoMatrix.orthSum2_eq_fusion_sum
#print axioms YMGap.Continuum.ChebOrthoMatrix.offDiagClosed_of_cellBound
#print axioms YMGap.Continuum.ChebOrthoMatrix.seqOrth0_converges_semiInt
#print axioms YMGap.Continuum.ChebOrthoMatrix.orthMatrix
#print axioms YMGap.Continuum.ChebOrthoMatrix.orthMatrix_diag
#print axioms YMGap.Continuum.ChebOrthoMatrix.orthMatrix_offdiag
#print axioms YMGap.Continuum.ChebOrthoMatrix.orthMatrix_diag_nonneg
