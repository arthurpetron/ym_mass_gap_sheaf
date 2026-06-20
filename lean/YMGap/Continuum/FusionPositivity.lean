/-
Track B / R2 — the COEFFICIENTWISE MONOTONICITY of the SU(2) bond-moving map, the
positive-domination tool that replaces cancellation-based arguments in the
full-mode quadratic defect.

# Why this module exists — positive domination, not cancellation

One Migdal–Kadanoff bond-moving step raises the single-plaquette class function to
the power `p = b^{d−1}` pointwise and re-expands in characters; at the
character-coefficient level this is the `p`-fold Clebsch–Gordan FUSION CONVOLUTION
(`fusionProduct` / `fusionPow`).  Bounding the full-mode quadratic defect of this
map by hand runs into delicate cancellations.  The clean way is POSITIVE
DOMINATION: the SU(2) Clebsch–Gordan structure constants are NONNEGATIVE, so the
fusion map is MONOTONE in its coefficient arguments.  Consequently a coefficientwise
order `r ≤_c E` between a residual sequence `r` and an envelope `E` is PRESERVED by
the bond-moving map: `B_p(r) ≤_c B_p(E)`.  This is exactly the
"coefficientwise quadratic envelope ⇒ norm bound" tool.

# What is GENUINELY PROVED here (pure constructive order algebra, axiom-clean)

  * `leCoef` (notation `a ≤_c b`) — the coefficientwise order on coefficient
    sequences `Nat → Q'`, with `leCoef_refl` / `leCoef_trans`.
  * `fsum_mono` — termwise monotonicity of the finite partial sum: `(∀ i, f i ≤
    g i) → fsum f n ≤ fsum g n` (the minimal sum-monotonicity lemma, proved here
    by induction on the length).
  * `fusionProduct_mono_left` / `fusionProduct_mono_right` / `fusionProduct_mono`
    — monotonicity of the one-step fusion convolution in each (nonnegative)
    argument, termwise from the nonnegativity of the fusion indicator and the args.
  * `fusionPow_mono` — monotonicity of the `p`-fold bond-moving map, by induction
    on `p` (using the one-step monotonicity and `fusionPow_nonneg` to carry the
    nonnegativity side-conditions).
  * `bondMove_envelope` — the domination corollary: `0 ≤_c r ≤_c E` is preserved by
    the `p`-fold map, `B_p(r) ≤_c B_p(E)`.  This is the positive-domination tool.

This is pure constructive order algebra; the nonnegativity of the SU(2)
Clebsch–Gordan structure constants makes it clean and unconditional.  No open
content.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, and reused `Q'` order lemmas
(`mul_le_mul_of_nonneg_left/right`, `add_le_add`).  Every load-bearing declaration
is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.
No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level
data / decidable facts.
-/

import YMGap.Continuum.BondMovingStep

namespace YMGap.Continuum.FusionPositivity

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep

/-! ## 1. The coefficientwise order `≤_c` and its basic structure -/

/-- **The coefficientwise order on coefficient sequences.**  `a ≤_c b` means
`a s ≤ b s` for every spin index `s`.  This is the order in which the SU(2)
bond-moving (fusion) map is monotone. -/
def leCoef (a b : Nat → Q') : Prop := ∀ s, a s ≤ b s

@[inherit_doc] infix:50 " ≤_c " => leCoef

/-- `≤_c` is reflexive. -/
theorem leCoef_refl (a : Nat → Q') : a ≤_c a := fun s => Q'.le_refl' (a s)

/-- `≤_c` is transitive. -/
theorem leCoef_trans {a b c : Nat → Q'} (hab : a ≤_c b) (hbc : b ≤_c c) :
    a ≤_c c := fun s => Q'.le_trans' (a s) (b s) (c s) (hab s) (hbc s)

/-! ## 2. Termwise monotonicity of the finite partial sum

The fusion convolution is a finite double `fsum`, so its monotonicity reduces to
the termwise monotonicity of `fsum`.  This is the minimal sum-monotonicity lemma:
a sum of termwise-dominated terms is dominated. -/

/-- **Termwise `fsum` monotonicity.**  If `f i ≤ g i` for every `i`, then
`fsum f n ≤ fsum g n` for every length `n` (sum of dominated terms is dominated).
Proved by induction on `n` using `Q'.add_le_add`. -/
theorem fsum_mono {f g : Nat → Q'} (h : ∀ i, f i ≤ g i) :
    ∀ n, fsum f n ≤ fsum g n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show fsum f n + f n ≤ fsum g n + g n
      exact Q'.add_le_add (fsum_mono h n) (h n)

/-! ## 3. Monotonicity of the one-step fusion convolution

Each summand `fusionInd a b s · (c a · d b)` is monotone in `c` (resp. `d`)
because `fusionInd ≥ 0` and the other factor is `≥ 0`; `fsum_mono` lifts this to
the double sum. -/

/-- **Left monotonicity of the fusion product.**  For a nonnegative right factor
`d`, the fusion convolution is monotone in its left argument:
`a ≤_c a' → fusionProduct N a d ≤_c fusionProduct N a' d`. -/
theorem fusionProduct_mono_left (N : Nat) {a a' d : Nat → Q'}
    (hd : ∀ s, (0 : Q') ≤ d s) (haa : a ≤_c a') :
    fusionProduct N a d ≤_c fusionProduct N a' d := by
  intro s
  show fsum (fun p => fsum (fun b => fusionInd p b s * (a p * d b)) (N + 1)) (N + 1)
      ≤ fsum (fun p => fsum (fun b => fusionInd p b s * (a' p * d b)) (N + 1)) (N + 1)
  refine fsum_mono (fun p => ?_) (N + 1)
  -- inner sum: termwise, a p · d b ≤ a' p · d b  (multiply a p ≤ a' p by d b ≥ 0,
  -- on the right), then scale by fusionInd p b s ≥ 0 (on the left).
  refine fsum_mono (fun b => ?_) (N + 1)
  have hin : a p * d b ≤ a' p * d b :=
    Q'.mul_le_mul_of_nonneg_right (a p) (a' p) (d b) (haa p) (hd b)
  exact Q'.mul_le_mul_of_nonneg_left (a p * d b) (a' p * d b) (fusionInd p b s)
    hin (fusionInd_nonneg p b s)

/-- **Right monotonicity of the fusion product.**  For a nonnegative left factor
`a`, the fusion convolution is monotone in its right argument:
`d ≤_c d' → fusionProduct N a d ≤_c fusionProduct N a d'`. -/
theorem fusionProduct_mono_right (N : Nat) {a d d' : Nat → Q'}
    (ha : ∀ s, (0 : Q') ≤ a s) (hdd : d ≤_c d') :
    fusionProduct N a d ≤_c fusionProduct N a d' := by
  intro s
  show fsum (fun p => fsum (fun b => fusionInd p b s * (a p * d b)) (N + 1)) (N + 1)
      ≤ fsum (fun p => fsum (fun b => fusionInd p b s * (a p * d' b)) (N + 1)) (N + 1)
  refine fsum_mono (fun p => ?_) (N + 1)
  refine fsum_mono (fun b => ?_) (N + 1)
  -- a p · d b ≤ a p · d' b  (multiply d b ≤ d' b by a p ≥ 0 on the left),
  -- then scale by fusionInd p b s ≥ 0 on the left.
  have hin : a p * d b ≤ a p * d' b :=
    Q'.mul_le_mul_of_nonneg_left (d b) (d' b) (a p) (hdd b) (ha p)
  exact Q'.mul_le_mul_of_nonneg_left (a p * d b) (a p * d' b) (fusionInd p b s)
    hin (fusionInd_nonneg p b s)

/-- **Joint monotonicity of the fusion product.**  With nonnegativity of the inner
factors (`a`, `a'` for the left chain, `d`, `d'` for the right chain), the fusion
convolution is monotone in BOTH arguments:
`a ≤_c a' → d ≤_c d' → fusionProduct N a d ≤_c fusionProduct N a' d'`.
(Routed `a d → a' d → a' d'`: left-step with the nonneg right factor `d`, then
right-step with the nonneg left factor `a'`.) -/
theorem fusionProduct_mono (N : Nat) {a a' d d' : Nat → Q'}
    (ha' : ∀ s, (0 : Q') ≤ a' s) (hd : ∀ s, (0 : Q') ≤ d s)
    (haa : a ≤_c a') (hdd : d ≤_c d') :
    fusionProduct N a d ≤_c fusionProduct N a' d' :=
  leCoef_trans
    (fusionProduct_mono_left N hd haa)
    (fusionProduct_mono_right N ha' hdd)

/-! ## 4. Monotonicity of the `p`-fold bond-moving map

Induction on `p`.  At the step `fusionPow N · (p+1) = fusionProduct N (fusionPow N
· p) ·`, both arguments move (the `p`-fold prefix by the IH, the trailing factor by
the hypothesis); the joint one-step monotonicity applies once the nonnegativity
side-conditions are supplied by `fusionPow_nonneg`. -/

/-- **Monotonicity of the `p`-fold fusion power.**  For nonnegative coefficient
sequences `a`, `b`, the bond-moving map preserves the coefficientwise order:
`a ≤_c b → fusionPow N a p ≤_c fusionPow N b p`. -/
theorem fusionPow_mono (N : Nat) {a b : Nat → Q'}
    (ha : ∀ s, (0 : Q') ≤ a s) (hb : ∀ s, (0 : Q') ≤ b s) (hab : a ≤_c b) :
    ∀ p, fusionPow N a p ≤_c fusionPow N b p
  | 0 => leCoef_refl _
  | p + 1 => by
      show fusionProduct N (fusionPow N a p) a ≤_c fusionProduct N (fusionPow N b p) b
      -- left argument: fusionPow N a p ≤_c fusionPow N b p (IH);
      -- right argument: a ≤_c b (hypothesis).
      -- nonneg side-conditions: fusionPow N b p ≥ 0 (left'), a ≥ 0 (right factor d).
      exact fusionProduct_mono N
        (fusionPow_nonneg N hb p) ha
        (fusionPow_mono N ha hb hab p) hab

/-! ## 5. The domination corollary — the positive-domination tool

If a residual coefficient sequence `r` is dominated by an envelope `E`
(`0 ≤_c r ≤_c E`), then the `p`-fold bond-moving map preserves the domination:
`B_p(r) ≤_c B_p(E)`.  This is the tool that converts a coefficientwise quadratic
envelope into a norm bound on the bond-moved data, without any cancellation
argument. -/

/-- **The bond-moving envelope-domination tool.**  Given a nonnegative residual
sequence `r` dominated by a nonnegative envelope `E` (`r ≤_c E`), the `p`-fold
bond-moving map preserves the domination: `fusionPow N r p ≤_c fusionPow N E p`.
(Special case of `fusionPow_mono`; `E`'s nonnegativity follows from `r ≥ 0` and
`r ≤_c E`, but is taken as a hypothesis here for direct use.) -/
theorem bondMove_envelope (N : Nat) {r E : Nat → Q'} (p : Nat)
    (hr : ∀ s, (0 : Q') ≤ r s) (hE : ∀ s, (0 : Q') ≤ E s) (hrE : r ≤_c E) :
    fusionPow N r p ≤_c fusionPow N E p :=
  fusionPow_mono N hr hE hrE p

end YMGap.Continuum.FusionPositivity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionPositivity.leCoef_refl
#print axioms YMGap.Continuum.FusionPositivity.leCoef_trans
#print axioms YMGap.Continuum.FusionPositivity.fsum_mono
#print axioms YMGap.Continuum.FusionPositivity.fusionProduct_mono_left
#print axioms YMGap.Continuum.FusionPositivity.fusionProduct_mono_right
#print axioms YMGap.Continuum.FusionPositivity.fusionProduct_mono
#print axioms YMGap.Continuum.FusionPositivity.fusionPow_mono
#print axioms YMGap.Continuum.FusionPositivity.bondMove_envelope
