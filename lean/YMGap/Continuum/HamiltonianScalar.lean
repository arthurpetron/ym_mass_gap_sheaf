/-
The SCALAR-LINEARITY brick on the completed GNS Hilbert space, and the
spectral-resolution bridge that turns the finite `SpectralModel` into an
operator-form gap for the transfer operator `T`.

# Which gaps this closes / reduces

`Continuum/SelfAdjointHamiltonian.lean` recorded three honest `Type`-level
residuals: `VectorScalingResidual` (the completion scalar action `cSmul`),
`RCScaleResidual` (the `RC`-by-`Q'` scaling), and `TransferFormGapResidual`
(the operator-form gap `⟨Tx,x⟩ ≤ sep·⟨x,x⟩`).  This module discharges the first
outright and reduces the third to a single irreducibly-new spectral DATUM.

## Target 1 — `cSmul` and scalar-linearity (GENUINE, discharged)

The obstruction to `cSmul` was that `GNSData` carries no module distributivity
of `smul` over the group.  `SmulGNSData` adds exactly ONE genuine vector law,
`smul_sub : s·(a−b) ≈ s·a − s·b`, as a *wrapper* over `GNSData` (so no existing
`GNSData` inhabitant has to re-discharge it).  From it:

  * `distSqQ_smul`   : `d²(s·a, s·b) ≃ s²·d²(a,b)` (via `B_smul_left/right`);
  * `cSmulCauchy`    : the pointwise scaling of a Cauchy rep is Cauchy, with the
    rescaled modulus `ε ↦ x.modulus (ε·oneOver1p(s²))` — the clamped reciprocal,
    NO division (`key_bound` : `s²·(ε·oneOver1p s²) ≤ ε`);
  * `cSmul`/`cSmul_embed`, and the payload `cSmul_cAdd`
    (`s·(x+y) = s·x + s·y`), descended through `CauchyNull` via the derived
    module laws `smul_zero`, `smul_neg`, `smul_add` (all consequences of
    `smul_sub` in the abelian group);
  * `vectorScalingResidual` : `VectorScalingResidual` is now INHABITED for any
    `SmulGNSData`, non-vacuously via the weighted `qWeightGNS` (whose `smul` is
    `Q'` multiplication, so `smul_sub` is `Q'` distributivity).

## Target 2 — the spectral-resolution bridge (HONEST reduction)

`⟨Tx,x⟩ ≤ sep·⟨x,x⟩` is genuinely NOT derivable from the three
`TransferOperator` axioms: the separator `sep` lives in the finite
`SpectralModel`, disconnected from `T`'s form.  The missing input is a finite
ONB coordinate resolution `TransferSpectralBridge` tying `T`'s quadratic form to
the located model.  `toFormGapResidual` is the GENUINE theorem that this finite
DATA suffices — a pure finite-dimensional chain
`⟨Tx,x⟩ = Σ lamᵢ|cᵢ|² ≤ Σ sep|cᵢ|² = sep·⟨x,x⟩`.  The DATA itself for the
physical Wilson `T` remains the open continuum input.

Prerequisites: `CReal.RCfinSum` (the `RC` finite sum) with `RCfinSum_mono`
(termwise `RCle` ⟹ summed `RCle`, via `RCadd_le_add`), and `RCScaleResidualPlus`
(the `RCScaleResidual` strengthened by the scale-over-sum law `RCscale_finSum`).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.WilsonGNS
import YMGap.Constructive.ExpUBInstance
import YMGap.Constructive.Soundness

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.GNSQuotient

/-! ## RC finite sums and their monotonicity (the `RC` analog of `finSum`) -/

namespace YMGap.Constructive.CReal

/-- **`leEv` is additive-monotone.**  `leEv a a' → leEv b b' → leEv (a+b) (a'+b')`.
`add.approx` is pointwise, so this is the `ε/2`-split addition of two eventual
bounds. -/
theorem leEv_add {a a' b b' : CReal} (ha : leEv a a') (hb : leEv b b') :
    leEv (add a b) (add a' b') := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, hN1⟩ := ha (HalfPow.half * ε) hhε
  obtain ⟨N2, hN2⟩ := hb (HalfPow.half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have h1 := hN1 n hn1
  have h2 := hN2 n hn2
  show (add a b).approx n ≤ (add a' b').approx n + ε
  rw [add_approx, add_approx]
  have hsum : a.approx n + b.approx n
      ≤ (a'.approx n + HalfPow.half * ε) + (b'.approx n + HalfPow.half * ε) :=
    Q'.add_le_add h1 h2
  have ereg : ((a'.approx n + HalfPow.half * ε) + (b'.approx n + HalfPow.half * ε)).eqv
      ((a'.approx n + b'.approx n) + (HalfPow.half * ε + HalfPow.half * ε)) :=
    Q'.regroup (a'.approx n) (b'.approx n) (HalfPow.half * ε)
  have etwo : ((a'.approx n + b'.approx n) + (HalfPow.half * ε + HalfPow.half * ε)).eqv
      ((a'.approx n + b'.approx n) + ε) :=
    Q'.add_eqv_congr_left (a'.approx n + b'.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))

/-- **`RCadd` is monotone.**  Descends `leEv_add` through `Equiv`. -/
theorem RCadd_le_add {a a' b b' : RC} (ha : RCle a a') (hb : RCle b b') :
    RCle (RCadd a b) (RCadd a' b') := by
  revert ha hb
  refine Quotient.inductionOn₂ a a' ?_
  intro x x'
  refine Quotient.inductionOn₂ b b' ?_
  intro y y' ha hb
  rw [RCle_mk] at ha hb
  rw [RCadd_mk, RCadd_mk, RCle_mk]
  exact leEv_add ha hb

/-- **Finite sum of `RC`-valued terms** (the `RC` analog of `SpectralGap.finSum`). -/
def RCfinSum : (k : Nat) → (Fin k → RC) → RC
  | 0, _ => RCzero
  | (k + 1), f => RCadd (RCfinSum k (fun i => f i.castSucc)) (f (Fin.last k))

/-- **Termwise `RCle` ⟹ summed `RCle`** (analog of `finSum_le_of_termwise`). -/
theorem RCfinSum_mono :
    {k : Nat} → {f g : Fin k → RC} → (∀ i, RCle (f i) (g i)) →
      RCle (RCfinSum k f) (RCfinSum k g)
  | 0, _, _, _ => RCle_refl _
  | (k + 1), f, g, h =>
      RCadd_le_add
        (RCfinSum_mono (f := fun i => f i.castSucc) (g := fun i => g i.castSucc)
          (fun i => h i.castSucc))
        (h (Fin.last k))

end YMGap.Constructive.CReal

/-! ## Clamped-reciprocal `Q'` facts for the scaled Cauchy modulus -/

namespace YMGap.Continuum.HamiltonianScalar

open YMGap.Constructive

/-- The clamped reciprocal `oneOver1p x = 1/(1+max(0,x))` is strictly positive
(its numerator is the positive `x.den`). -/
theorem oneOver1p_pos (x : Q') : (0 : Q') < ExpUBInstance.oneOver1p x := by
  show (0 : Int) * ((ExpUBInstance.oneOver1p x).den : Int)
      < (ExpUBInstance.oneOver1p x).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one, ExpUBInstance.oneOver1p_num]
  exact_mod_cast x.den_pos

/-- **The rescaling budget closes without division.**  For `t ≥ 0`, `ε ≥ 0`:
`t·(ε·oneOver1p t) ≤ ε`.  The heart is `t·oneOver1p t ≤ 1`, from
`oneOver1p t·(1+t) ≃ 1`. -/
theorem key_bound (t ε : Q') (ht : (0 : Q') ≤ t) (hε : (0 : Q') ≤ ε) :
    t * (ε * ExpUBInstance.oneOver1p t) ≤ ε := by
  have hE : (0 : Q') ≤ ExpUBInstance.oneOver1p t := ExpUBInstance.oneOver1p_nonneg t
  -- `t·E ≤ 1`
  have htE : t * ExpUBInstance.oneOver1p t ≤ 1 := by
    have hmul : (ExpUBInstance.oneOver1p t * (1 + t)).eqv 1 :=
      ExpUBInstance.oneOver1p_mul_oneAddX t ht
    have hdist : (ExpUBInstance.oneOver1p t * (1 + t)).eqv
        (ExpUBInstance.oneOver1p t * 1 + ExpUBInstance.oneOver1p t * t) :=
      Q'.mul_add_eqv (ExpUBInstance.oneOver1p t) 1 t
    have hE1 : (ExpUBInstance.oneOver1p t * 1).eqv (ExpUBInstance.oneOver1p t) :=
      Q'.mul_one_eqv (ExpUBInstance.oneOver1p t)
    have hEEt : (ExpUBInstance.oneOver1p t + ExpUBInstance.oneOver1p t * t).eqv 1 := by
      have a1 : (ExpUBInstance.oneOver1p t + ExpUBInstance.oneOver1p t * t).eqv
          (ExpUBInstance.oneOver1p t * 1 + ExpUBInstance.oneOver1p t * t) :=
        Q'.add_eqv_congr_right (ExpUBInstance.oneOver1p t) (ExpUBInstance.oneOver1p t * 1)
          (ExpUBInstance.oneOver1p t * t) (Q'.eqv_symm hE1)
      exact Q'.eqv_trans _ _ _ a1 (Q'.eqv_trans _ _ _ (Q'.eqv_symm hdist) hmul)
    have hle1 : ExpUBInstance.oneOver1p t * t
        ≤ ExpUBInstance.oneOver1p t * t + ExpUBInstance.oneOver1p t :=
      Q'.add_le_self_of_nonneg (ExpUBInstance.oneOver1p t * t) (ExpUBInstance.oneOver1p t) hE
    have heqv : (ExpUBInstance.oneOver1p t * t + ExpUBInstance.oneOver1p t).eqv 1 :=
      Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (ExpUBInstance.oneOver1p t * t) (ExpUBInstance.oneOver1p t)) hEEt
    have hEt1 : ExpUBInstance.oneOver1p t * t ≤ 1 := le_of_le_eqv hle1 heqv
    exact le_of_eqv_le (Q'.mul_comm_eqv t (ExpUBInstance.oneOver1p t)) hEt1
  -- `t·(ε·E) ≃ ε·(t·E) ≤ ε·1 ≃ ε`
  have hassoc : (t * (ε * ExpUBInstance.oneOver1p t)).eqv
      (ε * (t * ExpUBInstance.oneOver1p t)) := by
    have a1 : (t * (ε * ExpUBInstance.oneOver1p t)).eqv
        ((t * ε) * ExpUBInstance.oneOver1p t) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv t ε (ExpUBInstance.oneOver1p t))
    have a2 : ((t * ε) * ExpUBInstance.oneOver1p t).eqv
        ((ε * t) * ExpUBInstance.oneOver1p t) :=
      Q'.mul_eqv_congr_right (t * ε) (ε * t) (ExpUBInstance.oneOver1p t) (Q'.mul_comm_eqv t ε)
    have a3 : ((ε * t) * ExpUBInstance.oneOver1p t).eqv
        (ε * (t * ExpUBInstance.oneOver1p t)) :=
      Q'.mul_assoc_eqv ε t (ExpUBInstance.oneOver1p t)
    exact Q'.eqv_trans _ _ _ a1 (Q'.eqv_trans _ _ _ a2 a3)
  have hmul_le : ε * (t * ExpUBInstance.oneOver1p t) ≤ ε * 1 :=
    Q'.mul_le_mul_of_nonneg_left (t * ExpUBInstance.oneOver1p t) 1 ε htE hε
  exact le_of_eqv_le hassoc
    (Q'.le_trans' _ _ _ hmul_le (Q'.le_of_eqv (Q'.mul_one_eqv ε)))

/-- A `veq`-pair has vanishing squared distance: `veq p q → d²(p,q) ≃ 0`. -/
theorem rad_of_veq (D : GNSData) {p q : D.V} (h : D.veq p q) :
    (D.distSqQ p q).eqv 0 := by
  have hz : D.veq (D.sub p q) D.zero :=
    D.veq_trans (D.add_congr h (D.veq_refl (D.neg q))) (D.add_neg_self q)
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr hz) (D.B_zero_left D.zero)

/-! ## Target 1 — the module-scaling datum `SmulGNSData` -/

/-- A `GNSData` whose scalar action is a genuine module action:
`s·(a−b) ≈ (s·a) − (s·b)`.  The one vector law missing from `GNSData`, added as a
wrapper so no existing `GNSData` inhabitant has to re-discharge it. -/
structure SmulGNSData extends GNSData where
  /-- Module distributivity of `smul` over subtraction. -/
  smul_sub : ∀ (s : Q') (a b : toGNSData.V),
    toGNSData.veq (toGNSData.smul s (toGNSData.sub a b))
      (toGNSData.sub (toGNSData.smul s a) (toGNSData.smul s b))

namespace SmulGNSData

variable (D : SmulGNSData)

/-! ### The derived vector module laws (consequences of `smul_sub`) -/

/-- `s·0 ≈ 0`. -/
theorem smul_zero (s : Q') :
    D.toGNSData.veq (D.toGNSData.smul s D.toGNSData.zero) D.toGNSData.zero := by
  have h := D.smul_sub s D.toGNSData.zero D.toGNSData.zero
  have hsz : D.toGNSData.veq (D.toGNSData.sub D.toGNSData.zero D.toGNSData.zero) D.toGNSData.zero :=
    D.toGNSData.add_neg_self D.toGNSData.zero
  have h1 : D.toGNSData.veq
      (D.toGNSData.smul s (D.toGNSData.sub D.toGNSData.zero D.toGNSData.zero))
      (D.toGNSData.smul s D.toGNSData.zero) :=
    D.toGNSData.smul_congr s hsz
  have h2 : D.toGNSData.veq (D.toGNSData.smul s D.toGNSData.zero)
      (D.toGNSData.sub (D.toGNSData.smul s D.toGNSData.zero) (D.toGNSData.smul s D.toGNSData.zero)) :=
    D.toGNSData.veq_trans (D.toGNSData.veq_symm h1) h
  have h3 : D.toGNSData.veq
      (D.toGNSData.sub (D.toGNSData.smul s D.toGNSData.zero) (D.toGNSData.smul s D.toGNSData.zero))
      D.toGNSData.zero :=
    D.toGNSData.add_neg_self (D.toGNSData.smul s D.toGNSData.zero)
  exact D.toGNSData.veq_trans h2 h3

/-- `s·(−v) ≈ −(s·v)`. -/
theorem smul_neg (s : Q') (v : D.toGNSData.V) :
    D.toGNSData.veq (D.toGNSData.smul s (D.toGNSData.neg v))
      (D.toGNSData.neg (D.toGNSData.smul s v)) := by
  have hnv : D.toGNSData.veq (D.toGNSData.neg v)
      (D.toGNSData.sub D.toGNSData.zero v) :=
    D.toGNSData.veq_symm (D.toGNSData.zero_add (D.toGNSData.neg v))
  have h1 : D.toGNSData.veq (D.toGNSData.smul s (D.toGNSData.neg v))
      (D.toGNSData.smul s (D.toGNSData.sub D.toGNSData.zero v)) :=
    D.toGNSData.smul_congr s hnv
  have h2 := D.smul_sub s D.toGNSData.zero v
  have h3 : D.toGNSData.veq
      (D.toGNSData.sub (D.toGNSData.smul s D.toGNSData.zero) (D.toGNSData.smul s v))
      (D.toGNSData.neg (D.toGNSData.smul s v)) := by
    have hc : D.toGNSData.veq
        (D.toGNSData.add (D.toGNSData.smul s D.toGNSData.zero)
          (D.toGNSData.neg (D.toGNSData.smul s v)))
        (D.toGNSData.add D.toGNSData.zero (D.toGNSData.neg (D.toGNSData.smul s v))) :=
      D.toGNSData.add_congr (D.smul_zero s)
        (D.toGNSData.veq_refl (D.toGNSData.neg (D.toGNSData.smul s v)))
    exact D.toGNSData.veq_trans hc
      (D.toGNSData.zero_add (D.toGNSData.neg (D.toGNSData.smul s v)))
  exact D.toGNSData.veq_trans h1 (D.toGNSData.veq_trans h2 h3)

/-- `s·(u+v) ≈ s·u + s·v` — module distributivity over addition, derived from
`smul_sub`, `smul_neg` and `neg_neg`. -/
theorem smul_add (s : Q') (u v : D.toGNSData.V) :
    D.toGNSData.veq (D.toGNSData.smul s (D.toGNSData.add u v))
      (D.toGNSData.add (D.toGNSData.smul s u) (D.toGNSData.smul s v)) := by
  have h := D.smul_sub s u (D.toGNSData.neg v)
  have huv : D.toGNSData.veq (D.toGNSData.sub u (D.toGNSData.neg v))
      (D.toGNSData.add u v) :=
    D.toGNSData.add_congr (D.toGNSData.veq_refl u) (D.toGNSData.neg_neg v)
  have h1 : D.toGNSData.veq (D.toGNSData.smul s (D.toGNSData.add u v))
      (D.toGNSData.smul s (D.toGNSData.sub u (D.toGNSData.neg v))) :=
    D.toGNSData.smul_congr s (D.toGNSData.veq_symm huv)
  have h2 : D.toGNSData.veq
      (D.toGNSData.sub (D.toGNSData.smul s u) (D.toGNSData.smul s (D.toGNSData.neg v)))
      (D.toGNSData.add (D.toGNSData.smul s u) (D.toGNSData.smul s v)) := by
    have hn : D.toGNSData.veq
        (D.toGNSData.neg (D.toGNSData.smul s (D.toGNSData.neg v)))
        (D.toGNSData.smul s v) := by
      have hnn : D.toGNSData.veq
          (D.toGNSData.neg (D.toGNSData.smul s (D.toGNSData.neg v)))
          (D.toGNSData.neg (D.toGNSData.neg (D.toGNSData.smul s v))) :=
        D.toGNSData.neg_congr (D.smul_neg s v)
      exact D.toGNSData.veq_trans hnn (D.toGNSData.neg_neg (D.toGNSData.smul s v))
    exact D.toGNSData.add_congr (D.toGNSData.veq_refl (D.toGNSData.smul s u)) hn
  exact D.toGNSData.veq_trans h1 (D.toGNSData.veq_trans h h2)

/-! ### 1b. The scaled squared-distance law -/

/-- `d²(s·a, s·b) ≃ s²·d²(a,b)`. -/
theorem distSqQ_smul (s : Q') (a b : D.toGNSData.V) :
    (D.toGNSData.distSqQ (D.toGNSData.smul s a) (D.toGNSData.smul s b)).eqv
      ((s * s) * D.toGNSData.distSqQ a b) := by
  have hveq : D.toGNSData.veq
      (D.toGNSData.sub (D.toGNSData.smul s a) (D.toGNSData.smul s b))
      (D.toGNSData.smul s (D.toGNSData.sub a b)) :=
    D.toGNSData.veq_symm (D.smul_sub s a b)
  have h1 : (D.toGNSData.distSqQ (D.toGNSData.smul s a) (D.toGNSData.smul s b)).eqv
      (D.toGNSData.B (D.toGNSData.smul s (D.toGNSData.sub a b))
        (D.toGNSData.smul s (D.toGNSData.sub a b))) :=
    D.toGNSData.B_diag_congr hveq
  have h2 : (D.toGNSData.B (D.toGNSData.smul s (D.toGNSData.sub a b))
        (D.toGNSData.smul s (D.toGNSData.sub a b))).eqv
      (s * D.toGNSData.B (D.toGNSData.sub a b)
        (D.toGNSData.smul s (D.toGNSData.sub a b))) :=
    D.toGNSData.B_smul_left s (D.toGNSData.sub a b)
      (D.toGNSData.smul s (D.toGNSData.sub a b))
  have h3 : (D.toGNSData.B (D.toGNSData.sub a b)
        (D.toGNSData.smul s (D.toGNSData.sub a b))).eqv
      (s * D.toGNSData.B (D.toGNSData.sub a b) (D.toGNSData.sub a b)) :=
    D.toGNSData.B_smul_right s (D.toGNSData.sub a b) (D.toGNSData.sub a b)
  have h4 : (s * D.toGNSData.B (D.toGNSData.sub a b)
        (D.toGNSData.smul s (D.toGNSData.sub a b))).eqv
      (s * (s * D.toGNSData.B (D.toGNSData.sub a b) (D.toGNSData.sub a b))) :=
    Q'.mul_eqv_congr_left s
      (D.toGNSData.B (D.toGNSData.sub a b) (D.toGNSData.smul s (D.toGNSData.sub a b)))
      (s * D.toGNSData.B (D.toGNSData.sub a b) (D.toGNSData.sub a b)) h3
  have h5 : (s * (s * D.toGNSData.B (D.toGNSData.sub a b) (D.toGNSData.sub a b))).eqv
      ((s * s) * D.toGNSData.B (D.toGNSData.sub a b) (D.toGNSData.sub a b)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv s s
      (D.toGNSData.B (D.toGNSData.sub a b) (D.toGNSData.sub a b)))
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h4 h5))

/-! ### 1c. The scaled Cauchy lift and null-respect -/

/-- The pointwise scaling of a Cauchy representative.  Cauchy via `distSqQ_smul`
and the clamped modulus `ε ↦ x.modulus (ε·oneOver1p(s²))` (no division). -/
def cSmulCauchy (s : Q') (x : CauchyGNS D.toGNSData) : CauchyGNS D.toGNSData where
  seq := fun n => D.toGNSData.smul s (x.seq n)
  modulus := fun ε => x.modulus (ε * ExpUBInstance.oneOver1p (s * s))
  isCauchy := by
    intro ε hε p q hp hq
    have hE : (0 : Q') < ExpUBInstance.oneOver1p (s * s) := oneOver1p_pos (s * s)
    have hεE : (0 : Q') < ε * ExpUBInstance.oneOver1p (s * s) := Q'.mul_pos hε hE
    have hx := x.isCauchy (ε * ExpUBInstance.oneOver1p (s * s)) hεE p q hp hq
    have hss : (0 : Q') ≤ s * s := SumOfSquares.q_mul_self_nonneg s
    have hstep1 : (s * s) * D.toGNSData.distSqQ (x.seq p) (x.seq q)
        ≤ (s * s) * (ε * ExpUBInstance.oneOver1p (s * s)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ (s * s) hx hss
    have hstep2 : (s * s) * (ε * ExpUBInstance.oneOver1p (s * s)) ≤ ε :=
      key_bound (s * s) ε hss (Q'.le_of_lt hε)
    exact le_of_eqv_le (D.distSqQ_smul s (x.seq p) (x.seq q))
      (Q'.le_trans' _ _ _ hstep1 hstep2)

/-- `cSmulCauchy` respects `CauchyNull`. -/
theorem cSmulCauchy_null (s : Q') {x x' : CauchyGNS D.toGNSData}
    (hx : CauchyNull D.toGNSData x x') :
    CauchyNull D.toGNSData (D.cSmulCauchy s x) (D.cSmulCauchy s x') := by
  intro ε hε
  have hE : (0 : Q') < ExpUBInstance.oneOver1p (s * s) := oneOver1p_pos (s * s)
  have hεE : (0 : Q') < ε * ExpUBInstance.oneOver1p (s * s) := Q'.mul_pos hε hE
  obtain ⟨N, hN⟩ := hx (ε * ExpUBInstance.oneOver1p (s * s)) hεE
  refine ⟨N, fun n hn => ?_⟩
  have hxn : D.toGNSData.distSqQ (x.seq n) (x'.seq n)
      ≤ ε * ExpUBInstance.oneOver1p (s * s) := hN n hn
  have hss : (0 : Q') ≤ s * s := SumOfSquares.q_mul_self_nonneg s
  have hstep1 : (s * s) * D.toGNSData.distSqQ (x.seq n) (x'.seq n)
      ≤ (s * s) * (ε * ExpUBInstance.oneOver1p (s * s)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (s * s) hxn hss
  have hstep2 : (s * s) * (ε * ExpUBInstance.oneOver1p (s * s)) ≤ ε :=
    key_bound (s * s) ε hss (Q'.le_of_lt hε)
  exact le_of_eqv_le (D.distSqQ_smul s (x.seq n) (x'.seq n))
    (Q'.le_trans' _ _ _ hstep1 hstep2)

/-! ### 1d. The descended scalar action and embedding law -/

/-- **Scalar action on the completion** `s • ⟦x⟧ = ⟦s • x⟧`. -/
def cSmul (s : Q') :
    GNSCompletionSpace D.toGNSData → GNSCompletionSpace D.toGNSData :=
  Quotient.lift (fun x => Quotient.mk (cauchySetoid D.toGNSData) (D.cSmulCauchy s x))
    (fun _ _ hx => Quotient.sound (D.cSmulCauchy_null s hx))

/-- `cSmul` extends `smul` on the dense image. -/
theorem cSmul_embed (s : Q') (a : D.toGNSData.V) :
    D.cSmul s (embedV D.toGNSData a) = embedV D.toGNSData (D.toGNSData.smul s a) := by
  apply Quotient.sound
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ 0 ε
    (Q'.le_of_eqv (D.toGNSData.rad_refl (D.toGNSData.smul s a))) (Q'.le_of_lt hε)⟩

/-! ### 1e. Scalar-linearity over `cAdd` -/

/-- **Distributivity** `s • (x + y) = s • x + s • y`, descended from `smul_add`
through `cAddCauchy`/`CauchyNull`. -/
theorem cSmul_cAdd (s : Q')
    (x y : GNSCompletionSpace D.toGNSData) :
    D.cSmul s (D.toGNSData.cAdd x y)
      = D.toGNSData.cAdd (D.cSmul s x) (D.cSmul s y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : D.toGNSData.veq
      (D.toGNSData.smul s (D.toGNSData.add (u.seq n) (v.seq n)))
      (D.toGNSData.add (D.toGNSData.smul s (u.seq n)) (D.toGNSData.smul s (v.seq n))) :=
    D.smul_add s (u.seq n) (v.seq n)
  exact le_of_eqv_le (rad_of_veq D.toGNSData hva) (Q'.le_of_lt hε)

/-! ### 1f. Discharging `VectorScalingResidual` -/

/-- `VectorScalingResidual` is now inhabited for any `SmulGNSData`. -/
def vectorScalingResidual : VectorScalingResidual D.toGNSData where
  cSmul := D.cSmul
  cSmul_embed := D.cSmul_embed

end SmulGNSData

/-! ### Non-vacuity: the weighted GNS module is a `SmulGNSData` -/

/-- The weighted `qWeightGNS` (whose `smul` is `Q'` multiplication) satisfies
`smul_sub` by `Q'` distributivity — a free non-vacuity inhabitant. -/
def qSmulGNS (w : Q') (hw : (0 : Q') ≤ w) : SmulGNSData where
  toGNSData := qWeightGNS w hw
  smul_sub := fun (s : Q') (a b : Q') => by
    show Q'.eqv (s * (a + -b)) ((s * a) + -(s * b))
    have h1 : (s * (a + -b)).eqv (s * a + s * (-b)) := Q'.mul_add_eqv s a (-b)
    have h2 : (s * (-b)).eqv (-(s * b)) := Q'.mul_neg_eqv s b
    exact Q'.eqv_trans _ _ _ h1
      (Q'.add_eqv_congr_left (s * a) (s * (-b)) (-(s * b)) h2)

/-- The concrete completion scalar action fires on the weighted GNS module. -/
def qVectorScalingResidual (w : Q') (hw : (0 : Q') ≤ w) :
    VectorScalingResidual (qSmulGNS w hw).toGNSData :=
  (qSmulGNS w hw).vectorScalingResidual

/-! ### Optional wiring: the Wilson module is a `SmulGNSData` given its
vector `smul`-distributivity (a genuine law of the finite-volume algebra that
the minimal `WilsonGNSData` bundle does not carry, taken as named data). -/

/-- Promote a `WilsonGNSData` to a `SmulGNSData` given the vector module law
`s·(a−b) ≈ s·a − s·b` of the Wilson carrier. -/
def _root_.YMGap.Continuum.WilsonGNS.WilsonGNSData.toSmulGNSData
    {A : ObservableMeasure.ObsAlg} (W : YMGap.Continuum.WilsonGNS.WilsonGNSData A)
    (hsub : ∀ (s : Q') (a b : W.toGNSData.V),
      W.toGNSData.veq (W.toGNSData.smul s (W.toGNSData.sub a b))
        (W.toGNSData.sub (W.toGNSData.smul s a) (W.toGNSData.smul s b))) :
    SmulGNSData where
  toGNSData := W.toGNSData
  smul_sub := hsub

/-! ## Target 2 — the transfer spectral-resolution bridge -/

/-- **`RCScaleResidual` strengthened by the scale-over-sum law.**  `RCscale`
pulls out of a finite `RCfinSum`.  This is the extra field named in the residual
docstring; it is genuine for the concrete `RCscale = ofQ' sep · (·)` (linearity
of scalar multiplication over the completed inner product). -/
structure RCScaleResidualPlus extends RCScaleResidual where
  /-- `s·Σ fᵢ = Σ s·fᵢ`. -/
  RCscale_finSum : ∀ (s : Q') {k : Nat} (f : Fin k → CReal.RC),
    toRCScaleResidual.RCscale s (CReal.RCfinSum k f)
      = CReal.RCfinSum k (fun i => toRCScaleResidual.RCscale s (f i))

/-- **Transfer spectral-resolution bridge.**  A finite ONB coordinate resolution
of `T`'s quadratic form against the located model `G.model`:
`⟨Tx,x⟩ = Σ_{i<k} lamᵢ·|cᵢ(x)|²` and `⟨x,x⟩ = Σ_{i<k} |cᵢ(x)|²`, with the
surviving eigenvalues bounded by `sep` on `vac⊥`.  Finite ⇒ pure finite-dim
linear algebra, sidestepping the general located-spectrum no-go.  This is the
irreducibly-new spectral DATUM for the physical Wilson `T`. -/
structure TransferSpectralBridge {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) (R : RCScaleResidualPlus) : Type where
  /-- The squared coordinate weights `|cᵢ(x)|²`. -/
  coeffSq : H.hilbert.carrier → Fin G.model.k → CReal.RC
  /-- The coordinate weights are nonnegative. -/
  coeffSq_nonneg : ∀ x i, CReal.RCnonneg (coeffSq x i)
  /-- Resolution of the `T`-form: `⟨Tx,x⟩ = Σ lamᵢ·|cᵢ|²`. -/
  innerT_diag : ∀ x,
    H.hilbert.cinner (G.op.T x) x
      = CReal.RCfinSum G.model.k (fun i => R.RCscale (G.model.lam i.val) (coeffSq x i))
  /-- Resolution of the norm: `⟨x,x⟩ = Σ |cᵢ|²`. -/
  innerSelf_diag : ∀ x,
    H.hilbert.cinner x x = CReal.RCfinSum G.model.k (coeffSq x)
  /-- On `vac⊥` every surviving eigenvalue clears the separator. -/
  eigen_le_sep : ∀ {x}, G.vacPerp x → ∀ i,
    CReal.RCle (R.RCscale (G.model.lam i.val) (coeffSq x i))
               (R.RCscale G.gap.sep (coeffSq x i))

/-- **Operator-form gap from the spectral resolution** (discharges
`TransferFormGapResidual`).  Chain:
`⟨Tx,x⟩ = Σ lamᵢ|cᵢ|² ≤ Σ sep|cᵢ|² = sep·Σ|cᵢ|² = sep·⟨x,x⟩`. -/
def TransferSpectralBridge.toFormGapResidual
    {D : GNSData} {H : CompleteGNSHilbert D}
    {G : SpectralGapData H} {R : RCScaleResidualPlus}
    (Br : TransferSpectralBridge G R) :
    TransferFormGapResidual G where
  scaledInner := fun x => R.RCscale G.gap.sep (H.hilbert.cinner x x)
  form_gap := by
    intro x hx
    have hmono : CReal.RCle (H.hilbert.cinner (G.op.T x) x)
        (CReal.RCfinSum G.model.k (fun i => R.RCscale G.gap.sep (Br.coeffSq x i))) := by
      rw [Br.innerT_diag x]
      exact CReal.RCfinSum_mono (fun i => Br.eigen_le_sep hx i)
    have hrhs : CReal.RCfinSum G.model.k (fun i => R.RCscale G.gap.sep (Br.coeffSq x i))
        = R.RCscale G.gap.sep (H.hilbert.cinner x x) := by
      rw [Br.innerSelf_diag x, R.RCscale_finSum G.gap.sep (Br.coeffSq x)]
    rw [← hrhs]
    exact hmono

end YMGap.Continuum.HamiltonianScalar

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.leEv_add
#print axioms YMGap.Constructive.CReal.RCadd_le_add
#print axioms YMGap.Constructive.CReal.RCfinSum
#print axioms YMGap.Constructive.CReal.RCfinSum_mono
#print axioms YMGap.Continuum.HamiltonianScalar.oneOver1p_pos
#print axioms YMGap.Continuum.HamiltonianScalar.key_bound
#print axioms YMGap.Continuum.HamiltonianScalar.rad_of_veq
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.smul_add
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.distSqQ_smul
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.cSmulCauchy
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.cSmul
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.cSmul_embed
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.cSmul_cAdd
#print axioms YMGap.Continuum.HamiltonianScalar.SmulGNSData.vectorScalingResidual
#print axioms YMGap.Continuum.HamiltonianScalar.qSmulGNS
#print axioms YMGap.Continuum.HamiltonianScalar.qVectorScalingResidual
#print axioms YMGap.Continuum.HamiltonianScalar.TransferSpectralBridge.toFormGapResidual
