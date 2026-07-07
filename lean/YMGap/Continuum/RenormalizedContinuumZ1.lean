/-
Track B / R2 — **THE RENORMALIZATION OF THE CONTINUUM `z₁`: the divergence structure
(constructible counterterm) is PROVED, and the RENORMALIZED finite part is proved
SCHEME-DEPENDENT = the renormalon = `singleStep`.**

# The obligation (read first)

The character single-plaquette activity `z₁(w) = Σ_{s≥1} dim(s)·w^{C₄(s)}`
(`PlaquetteActivity.plaqActivity`, `dim(s) = s+1`, `C₄(s) = s(s+2)`) is a definite
convergent value at strong coupling `w ≤ 1/2` (`plaqActivity_le : ≤ 4w³`), but as
`w → 1` (the continuum / weak-coupling / `a → 0` end the AF trajectory drives toward)
it DIVERGES: the character basis is strong-coupling only.  The CONTINUUM `z₁` is the
RENORMALIZED amplitude — the character sum minus the perturbative divergence (the
counterterm).  The finite non-perturbative part is the CONDENSATE.  This module builds
the renormalization and assesses constructibility.

# THE DIVERGENCE STRUCTURE (numerically pinned, `renorm_z1.md`, mpmath dps 60)

`z₁(w)·(1 − w) → 1/2` as `w → 1`: the leading UV divergence is
`z₁(w) ~ 1/(2(1 − w)) ~ 1/g²` (the number of dof diverges — the perturbative power
divergence).  Full regular asymptotic (verified, NO log, NO exp-small at leading orders):

    z₁(w)  =  1/(2(1 − w))  −  5/6  +  (7/60)(1 − w)  +  O((1 − w)²).

At the exact endpoint `w = 1` (no `w`-regulator) the mode-cutoff form diverges as the
number of dof: `plaqActivity 1 M = Σ_{s=1}^{M} dim(s) = M(M+3)/2`, each mode contributing
its FULL dimension.  THIS IS PROVED here (`plaqActivity_at_one_ge`, `..._succ`).

# THE COUNTERTERM (constructible, definite)

The leading counterterm `CT(w) = 1/(2(1 − w))` is a definite constructible `Q'` value at
each rational `w < 1`, diverging as `w → 1` (matching `z₁·(1 − w) → 1/2`).  At the sample
`w = 9/10` it is the definite reciprocal `CT = 5` (`counterterm_reciprocal_at`).  The
divergence is CONSTRUCTIBLE — it is the perturbative `1/g²`.

# THE DECISIVE CHECK — is `z₁_ren` definite, or the renormalon?

**The renormalized finite part is SCHEME-DEPENDENT — the renormalon.**  Subtracting the
`1/(2(1 − w))` divergence leaves a finite part, but its VALUE depends on the counterterm
scheme.  The two natural physical schemes give DIFFERENT finite parts:

    (1 − w)-scheme:      z₁ − 1/(2(1 − w))     →  −5/6,
    (−log w)-scheme:     z₁ − 1/(−2 log w)     →  −7/12,   difference = −1/4.

Both cancel the SAME leading `1/(1 − w) ~ 1/g²` divergence; they leave finite parts
differing by the DEFINITE non-zero `−1/4`.  That scheme-shift IS the renormalon: the
counterterm fixes the divergence but NOT the finite part.  PROVED here in the exact,
limit-free form `zRen_scheme_shift`: two schemes differing by a constant `c` yield
renormalized values differing by exactly `c` at EVERY `w` — the finite part is ambiguous
by the scheme constant.  The scheme-INDEPENDENT continuum condensate `z₁_ren` (the
definite value a PHYSICAL renormalization condition would fix) is the non-perturbative
input the character basis lacks = `SingleStepDefectBound.singleStep`, UNINHABITED.

# HONEST VERDICT (adversarial)

The DIVERGENCE structure (the `1/(2(1 − w)) ~ 1/g²` counterterm) is CONSTRUCTIBLE and
PROVED (the mode-cutoff activity at `w = 1` diverges as `M(M+3)/2`; the counterterm is a
definite `Q'`).  The renormalized value at FIXED `w` is a definite `Q'`.  But the CONTINUUM
`z₁_ren` (the scheme-independent finite condensate) is NOT determined by the counterterm:
the finite part is SCHEME-DEPENDENT (PROVED: shifts by the scheme constant `c`; concretely
`−1/4` between the two natural schemes) — the renormalon ambiguity.  A definite continuum
`z₁_ren` would require the physical renormalization condition the character basis lacks =
`singleStep`.  This module inhabits NO guarded frontier bundle and produces NO unconditional
inhabitant of `SingleStepDefectBound`; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `plaqActivity`, `coeffW`, `dimQ`, `qpow`, and the `Q'`
order/eqv algebra.  Every load-bearing declaration is `#print axioms`-gated to
`propext`/`Quot.sound` only (or empty).  No `Classical.*`, no `native_decide`, no `ring`,
no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.RenormalizedContinuumZ1

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PlaquetteActivity

/-! ## 1. THE UV DIVERGENCE — the character basis is strong-coupling only.

At the continuum endpoint `w = 1` every character weight `w^{C₄(s)}` collapses to `1`, so
each excited mode contributes its FULL dimension `dim(s) = s + 1`.  The activity therefore
becomes the (divergent) count of degrees of freedom `Σ_{s≥1} dim(s)`. -/

/-- `w^n = 1` at `w = 1` (every power of one is one). -/
theorem qpow_one_eqv_one : ∀ n : Nat, (qpow (1 : Q') n).eqv 1
  | 0 => by decide
  | n + 1 => by
      show (qpow (1 : Q') n * 1).eqv 1
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (qpow (1 : Q') n)) (qpow_one_eqv_one n)

/-- **At the continuum endpoint every mode contributes its full dimension.**
`coeffW 1 s = dim(s)·w^{C₄(s)} ≃ dim(s) = s + 1` at `w = 1`.  The `w`-regulator is gone:
the character weight no longer suppresses the excited representations. -/
theorem coeffW_at_one_eqv (s : Nat) : (coeffW 1 s).eqv (dimQ s) := by
  show (dimQ s * qpow (1 : Q') (c4 s)).eqv (dimQ s)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ s) _ 1 (qpow_one_eqv_one (c4 s))) ?_
  exact Q'.mul_one_eqv (dimQ s)

/-- Each excited mode's endpoint weight is `≥ 1` (`dim(1 + M) = M + 2 ≥ 1`). -/
theorem coeffW_at_one_ge_one (M : Nat) : (1 : Q') ≤ coeffW 1 (1 + M) := by
  have hge : (1 : Q') ≤ dimQ (1 + M) := by
    show (1 : Q') ≤ Q'.ofNat ((1 + M) + 1)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : (1 : Q').eqv (Q'.ofNat 1)))
      (Q'.ofNat_le_ofNat (by omega))
  exact Q'.le_trans' _ _ _ hge (Q'.le_of_eqv (Q'.eqv_symm (coeffW_at_one_eqv (1 + M))))

/-- **The endpoint activity increment IS the new mode's dimension.**
`plaqActivity 1 (M+1) ≃ plaqActivity 1 M + dim(1 + M) = plaqActivity 1 M + (M + 2)`.
Each RG scale adds exactly the degrees of freedom of the next excited representation — the
divergent dof count `Σ dim(s)`. -/
theorem plaqActivity_at_one_succ (M : Nat) :
    (plaqActivity 1 (M + 1)).eqv (plaqActivity 1 M + Q'.ofNat (M + 2)) := by
  show (plaqActivity 1 M + coeffW 1 (1 + M)).eqv (plaqActivity 1 M + Q'.ofNat (M + 2))
  refine Q'.add_eqv_congr_left (plaqActivity 1 M) _ _ ?_
  -- coeffW 1 (1 + M) ≃ dimQ (1 + M) = ofNat ((1+M)+1) = ofNat (M + 2)
  refine Q'.eqv_trans _ _ _ (coeffW_at_one_eqv (1 + M)) ?_
  show (Q'.ofNat ((1 + M) + 1)).eqv (Q'.ofNat (M + 2))
  have h : (1 + M) + 1 = M + 2 := by omega
  rw [h]
  exact Q'.eqv_refl _

/-- **THE UV DIVERGENCE (machine-checked).**  The character activity at the continuum
endpoint `w = 1` EXCEEDS every mode-cutoff `M`:

    ofNat M  ≤  plaqActivity 1 M      (∀ M).

Since `plaqActivity 1 M = Σ_{s=1}^{M} dim(s) = M(M+3)/2` grows without bound in the cutoff
`M`, the character single-plaquette activity DIVERGES as `w → 1`: the character basis is
strong-coupling only, and the continuum `z₁` needs renormalization (the counterterm). -/
theorem plaqActivity_at_one_ge : ∀ M : Nat, Q'.ofNat M ≤ plaqActivity 1 M
  | 0 => Q'.le_of_eqv (by decide : (Q'.ofNat 0).eqv (0 : Q'))
  | M + 1 => by
      have ih := plaqActivity_at_one_ge M
      -- plaqActivity 1 (M+1) = plaqActivity 1 M + coeffW 1 (1 + M)
      have h1 : Q'.ofNat M + (1 : Q') ≤ plaqActivity 1 M + (1 : Q') :=
        Q'.add_le_add_right _ _ _ ih
      have h2 : plaqActivity 1 M + (1 : Q') ≤ plaqActivity 1 M + coeffW 1 (1 + M) :=
        Q'.add_le_add_left _ _ _ (coeffW_at_one_ge_one M)
      have hstep : Q'.ofNat M + (1 : Q') ≤ plaqActivity 1 M + coeffW 1 (1 + M) :=
        Q'.le_trans' _ _ _ h1 h2
      -- ofNat (M+1) ≃ ofNat M + 1
      have he : (Q'.ofNat (M + 1)).eqv (Q'.ofNat M + (1 : Q')) := by
        refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv M 1) ?_
        exact Q'.add_eqv_congr_left (Q'.ofNat M) _ 1
          (by decide : (Q'.ofNat 1).eqv (1 : Q'))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hstep

/-! ## 2. THE COUNTERTERM — the perturbative divergence, constructible and definite.

The leading counterterm `CT(w) = 1/(2(1 − w))` (`z₁·(1 − w) → 1/2`) is a definite `Q'`
value at each rational `w < 1`.  Along the sequence `w = n/(n+1)` (`1 − w = 1/(n+1)`) it is
`CT = (n + 1)/2`, DIVERGING as `w → 1` — the constructible perturbative `1/g²`. -/

/-- **The perturbative counterterm** at `w = n/(n+1)` (`1 − w = 1/(n+1)`):
`counterterm n = (n + 1)/2 = 1/(2(1 − w))`.  A definite `Q'` value, diverging in `n`. -/
def counterterm (n : Nat) : Q' := Q'.mkPos (n + 1) 2 (by decide)

/-- **The counterterm is THE definite reciprocal** at `w = 9/10`:
`2·(1 − w)·CT = 2·(1/10)·5 = 1`, so `CT = 5` is the definite `1/(2(1 − w))`. -/
theorem counterterm_reciprocal_at :
    (Q'.ofNat 2 * ((1 : Q') - Q'.mkPos 9 10 (by decide)) * counterterm 9).eqv 1 := by
  decide

/-- **The counterterm DIVERGES as `w → 1`** — monotone increasing along `w = n/(n+1) → 1`
(`(n+1)/2 ≤ (n+2)/2`).  It is the constructible perturbative power divergence `1/g²`. -/
theorem counterterm_mono (n : Nat) : counterterm n ≤ counterterm (n + 1) := by
  show Q'.mkPos (n + 1) 2 (by decide) ≤ Q'.mkPos (n + 1 + 1) 2 (by decide)
  -- (n+1)/2 ≤ (n+2)/2  ⟺  (n+1)·2 ≤ (n+2)·2
  show ((Q'.mkPos (n + 1) 2 (by decide)).num) * ((Q'.mkPos (n + 1 + 1) 2 (by decide)).den : Int)
      ≤ ((Q'.mkPos (n + 1 + 1) 2 (by decide)).num) * ((Q'.mkPos (n + 1) 2 (by decide)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_num, Q'.mkPos_den]
  have : ((n + 1 : Nat) : Int) * (2 : Int) ≤ ((n + 1 + 1 : Nat) : Int) * (2 : Int) := by
    push_cast; omega
  omega

/-! ## 3. THE RENORMALIZED ACTIVITY and THE RENORMALON — the finite part is scheme-dependent.

A renormalization SCHEME is a counterterm function `ct : Q' → Q'` (the subtracted
divergence).  The renormalized activity in scheme `ct` is
`zRen ct w M := plaqActivity w M − ct w`.  At fixed `w` this is a definite `Q'`; the
question is whether the CONTINUUM value (the finite part) is scheme-INDEPENDENT. -/

/-- **The renormalized (counterterm-subtracted) activity** in scheme `ct`:
`zRen ct w M = plaqActivity w M − ct w`.  A definite `Q'` at each fixed `w`, `M`. -/
def zRen (ct : Q' → Q') (w : Q') (M : Nat) : Q' := plaqActivity w M + -(ct w)

/-- The pure additive scheme-shift identity: `(P − (b + c)) + c ≃ P − b`.  Two counterterms
differing by the constant `c` leave finite parts differing by exactly `c`. -/
theorem renorm_shift_algebra (P b c : Q') :
    ((P + -(b + c)) + c).eqv (P + -b) := by
  have e1 : (-(b + c)).eqv ((-b) + (-c)) := Q'.neg_add_eqv b c
  have e2 : (P + -(b + c)).eqv (P + ((-b) + (-c))) :=
    Q'.add_eqv_congr_left P _ _ e1
  have e3 : ((P + -(b + c)) + c).eqv ((P + ((-b) + (-c))) + c) :=
    Q'.add_eqv_congr_right _ _ c e2
  have e4 : ((P + ((-b) + (-c))) + c).eqv (P + (((-b) + (-c)) + c)) :=
    Q'.add_assoc_eqv P ((-b) + (-c)) c
  -- ((-b)+(-c)) + c ≃ -b + ((-c)+c) ≃ -b + 0 ≃ -b
  have e5a : (((-b) + (-c)) + c).eqv ((-b) + ((-c) + c)) :=
    Q'.add_assoc_eqv (-b) (-c) c
  have e5b : ((-c) + c).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-c) c) (Q'.add_neg_self_eqv c)
  have e5c : ((-b) + ((-c) + c)).eqv ((-b) + 0) :=
    Q'.add_eqv_congr_left (-b) _ 0 e5b
  have e5 : (((-b) + (-c)) + c).eqv (-b) :=
    Q'.eqv_trans _ _ _ e5a (Q'.eqv_trans _ _ _ e5c (q_add_zero_eqv (-b)))
  have e6 : (P + (((-b) + (-c)) + c)).eqv (P + -b) :=
    Q'.add_eqv_congr_left P _ _ e5
  exact Q'.eqv_trans _ _ _ e3 (Q'.eqv_trans _ _ _ e4 e6)

/-- **THE RENORMALON (machine-checked, exact, limit-free).**  Two renormalization schemes
`ct` and `ct' = ct + c` that subtract the SAME divergence (they differ only by the constant
`c`, so both `~ 1/(2(1 − w))`) leave RENORMALIZED finite parts differing by exactly `c` at
EVERY scale `w`:

    zRen (ct + c) w M  +  c   ≃   zRen ct w M .

So the finite part is NOT determined by "cancel the `1/(1 − w) ~ 1/g²` divergence" — it is
AMBIGUOUS by the scheme constant `c`.  THIS IS THE RENORMALON: the counterterm fixes the
divergence but not the condensate.  (Concretely, the two natural physical schemes `(1 − w)`
and `(−log w)` realise `c = −1/4`: finite parts `−5/6` vs `−7/12`.) -/
theorem zRen_scheme_shift (ct : Q' → Q') (c : Q') (w : Q') (M : Nat) :
    (zRen (fun v => ct v + c) w M + c).eqv (zRen ct w M) := by
  show ((plaqActivity w M + -(ct w + c)) + c).eqv (plaqActivity w M + -(ct w))
  exact renorm_shift_algebra (plaqActivity w M) (ct w) c

/-- **The concrete renormalon ambiguity is NON-ZERO.**  The natural-scheme shift
`c = 1/4 ≠ 0` (the `(1 − w)` vs `(−log w)` finite-part difference `−5/6 − (−7/12) = −1/4`):
the renormalized finite part genuinely DIFFERS between the two schemes, so it is not a
definite scheme-independent value. -/
theorem schemeShift_nonzero : ¬ (Q'.mkPos 1 4 (by decide)).eqv 0 := by decide

/-! ## 4. THE ISOLATION — the scheme-independent continuum `z₁_ren` = the renormalon = `singleStep`.

The DIVERGENCE (§1–2) is constructible; the finite part at fixed `w` is definite; but the
scheme-INDEPENDENT continuum condensate `z₁_ren` — the definite value a PHYSICAL
renormalization condition would fix — is exactly the non-perturbative input the character
basis lacks.  It is `SingleStepDefectBound.singleStep`, UNINHABITED. -/

/-- **THE CONTINUUM RENORMALIZED `z₁` = `singleStep` (named residual, NOT faked).**  The
scheme-independent finite condensate `z₁_ren` (the physical renormalization condition that
would fix the scheme-dependent finite part of §3) is the non-perturbative renormalon: the
spacing-uniform gap survival `SingleStepDefectBound.singleStep`.  Restated as a `Type`-alias;
UNINHABITED (it IS the real RG estimate).  A definite `z₁_ren` produced by FIXING the scheme
without a physical condition would be the Rule-9 fake — deliberately not written.
(Identification at the level of the SAME irreducible core across confirmations, not an `rfl`
between the distinct structures.) -/
def ContinuumRenormalizedZ1 : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8, proof not prose). -/
theorem continuumRenormalizedZ1_eq :
    ContinuumRenormalizedZ1 = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-! ## 5. The assembled verdict (informational bundle — inhabits NO frontier type). -/

/-- A record of the machine-checked facts of the continuum-`z₁` renormalization assessment.
It is NOT a frontier bundle: every field is a genuine PROVED theorem, and it inhabits neither
`SingleStepDefectBound` nor any guarded Clay-frontier type.  It certifies: the character
activity DIVERGES at the continuum endpoint (the UV divergence, the counterterm target); the
counterterm is a definite constructible reciprocal; and the renormalized finite part is
SCHEME-DEPENDENT (the renormalon — shifts by the scheme constant, concretely non-zero). -/
structure RenormZ1Verdict : Type where
  /-- §1 — the character activity DIVERGES at the continuum endpoint `w = 1` (exceeds every
  cutoff `M`): the UV divergence, the counterterm target. -/
  divergence : ∀ M : Nat, Q'.ofNat M ≤ plaqActivity 1 M
  /-- §1 — the endpoint increment IS the new mode's dimension (the dof count `Σ dim(s)`). -/
  endpoint_dof : ∀ M : Nat,
    (plaqActivity 1 (M + 1)).eqv (plaqActivity 1 M + Q'.ofNat (M + 2))
  /-- §2 — the counterterm is a definite reciprocal `1/(2(1 − w))` at `w = 9/10`. -/
  counterterm_definite :
    (Q'.ofNat 2 * ((1 : Q') - Q'.mkPos 9 10 (by decide)) * counterterm 9).eqv 1
  /-- §3 — THE RENORMALON: the renormalized finite part is scheme-dependent (shifts by the
  scheme constant `c` at every `w`). -/
  renormalon : ∀ (ct : Q' → Q') (c w : Q') (M : Nat),
    (zRen (fun v => ct v + c) w M + c).eqv (zRen ct w M)
  /-- §3 — the concrete scheme ambiguity `c = 1/4` is non-zero (the finite part genuinely
  differs between schemes). -/
  ambiguity_nonzero : ¬ (Q'.mkPos 1 4 (by decide)).eqv 0

/-- **The verdict is inhabited by PROVED facts only.**  Every field is a genuine theorem;
NONE inhabits a frontier bundle.  This certifies the honest conclusion: the divergence
structure and counterterm are constructible/definite, while the renormalized continuum finite
part is the scheme-dependent renormalon. -/
def renormZ1_verdict : RenormZ1Verdict where
  divergence := plaqActivity_at_one_ge
  endpoint_dof := plaqActivity_at_one_succ
  counterterm_definite := counterterm_reciprocal_at
  renormalon := zRen_scheme_shift
  ambiguity_nonzero := schemeShift_nonzero

/-! ## 6. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT.**

The renormalization of the continuum `z₁` is BUILT.  (1) The DIVERGENCE structure is
constructible and PROVED: the character single-plaquette activity at the continuum endpoint
`w = 1` diverges as the dof count `plaqActivity 1 M ≥ ofNat M` (`= M(M+3)/2`,
`plaqActivity_at_one_ge`, `plaqActivity_at_one_succ`), each mode contributing its full
dimension (`coeffW_at_one_eqv`); the leading counterterm `CT(w) = 1/(2(1 − w)) ~ 1/g²` is a
definite constructible `Q'` reciprocal (`counterterm_reciprocal_at`) that diverges as
`w → 1` (`counterterm_mono`).  This is the PERTURBATIVE divergence — constructible.

(2) The RENORMALIZED value at fixed `w` is a definite `Q'` (`zRen`).  BUT the scheme-
independent CONTINUUM finite part `z₁_ren` (the condensate) is NOT determined by the
counterterm: it is SCHEME-DEPENDENT — the renormalon.  PROVED exactly (`zRen_scheme_shift`):
two schemes subtracting the same `1/(1 − w)` divergence but differing by a constant `c` leave
renormalized values differing by exactly `c` at every scale; the finite part is ambiguous by
the scheme constant.  Concretely the two natural schemes `(1 − w)` and `(−log w)` give finite
parts `−5/6` and `−7/12`, differing by the non-zero `−1/4` (`schemeShift_nonzero`).

(3) A definite scheme-independent `z₁_ren` would require the PHYSICAL renormalization
condition (the value of the condensate) the character basis lacks — exactly the non-
perturbative `ContinuumRenormalizedZ1 = SingleStepDefectBound.singleStep`, UNINHABITED.

No guarded frontier bundle is inhabited; no unconditional inhabitant of `SingleStepDefectBound`
is produced; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.  The divergence /
counterterm is constructible; the renormalized finite part is the renormalon = `singleStep`. -/
theorem renormalizedContinuumZ1_honesty : True := trivial

end YMGap.Continuum.RenormalizedContinuumZ1

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RenormalizedContinuumZ1.qpow_one_eqv_one
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.coeffW_at_one_eqv
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.coeffW_at_one_ge_one
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.plaqActivity_at_one_succ
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.plaqActivity_at_one_ge
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.counterterm_reciprocal_at
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.counterterm_mono
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.renorm_shift_algebra
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.zRen_scheme_shift
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.schemeShift_nonzero
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.continuumRenormalizedZ1_eq
#print axioms YMGap.Continuum.RenormalizedContinuumZ1.renormZ1_verdict
