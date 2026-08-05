/-
# Frontier STATEMENT-drift guard (Clay-frontier anti-weakening check)

`YMGapGuard.lean` protects the Clay-frontier types against *inhabitation* (an
agent producing a vacuous/circular term that closes a fragment of the problem).
It does NOT protect against *statement drift*: someone silently WEAKENING the
frontier types themselves — loosening a field of `ClayTargetPinned`, dropping a
hypothesis from a `FrontierDAG` bundle, or gutting a shared parameter def such as
`RubricO4Restoration := True` — makes the type EASIER (possibly trivially
inhabitable), and the inhabitation guard would not fire because no offending
inhabitant is ever committed.  That is the exact attack the pinning exists to
prevent.

This module pins the STATEMENT (type signature + field structure) of each
Clay-frontier type and of the shared parameter defs those types are built from,
by computing a **stable structural hash** of each declaration and comparing it
against a hash literal recorded below.  On any mismatch the build FAILS.

## What the hash covers (HONESTY)

For each pinned declaration `d` the hash is a deterministic serialization of:

  * `d`'s **type** — the full `∀`-telescope (parameters + result universe),
    including binder names and binder domain types;
  * if `d` is a **structure / inductive**: the type of every constructor — whose
    `∀`-telescope binder names ARE the field names and whose binder domains ARE
    the field types.  So renaming a field, removing a field, changing a field
    type, loosening a bound, or turning a `∀` hypothesis into an `∃` all change
    the serialization → the hash;
  * if `d` is a **def / abbrev** (e.g. `RubricO4Restoration : Prop := …`): its
    **value** as well, so weakening the definiens (`:= True`) changes the hash.

The serialization is a pure structural fold over the elaborated `Expr` stored in
the environment (no pretty-printer, no `whnf`, no reduction), with metadata
(`.mdata`) stripped and macro scopes erased from every name, so it is
deterministic across builds (verified: two builds → identical hashes).  The
digest is FNV-1a/64 over that string, fully specified in this file (no reliance
on `Expr.hash`, whose treatment of binder names is not part of its contract).

## Scope (HONESTY, cont.)

Pinning is a CURATED, explicit list (`pinnedFrontierStatements`): the five
frontier structures plus the shared parameter defs/structures their fields
reference (one hop).  This is deliberate — a full transitive Merkle closure over
`YMGap.*` would trip on every unrelated refactor and drown the signal.  A
weakening reached only through a def NOT in the list (two hops away, via the
*value* of an already-listed def that itself references a further def) is out of
scope; the direct field-level and shared-param-level weakenings that are the
stated attack surface ARE covered.  Extend the list when a new shared parameter
becomes load-bearing.

## On drift

A mismatch means a pinned statement CHANGED.  If it is a deliberate
STRENGTHENING (adding a hypothesis, tightening a bound) that survived human
review, update the pinned hash below — deliberately, never by an agent
auto-syncing the guard.  If it is a WEAKENING it MUST be rejected: it is the
vacuous-weakening attack this pin exists to catch.

This guard is INDEPENDENT of `AXIOM_AUDIT.md` (it hashes the type, not the
axioms) and of `YMGapGuard.lean` (it hashes the statement, not its inhabitants),
so neither `make lean-audit-update` nor the absence of an inhabitant can silence
it.
-/
/- Import the exact pinned-statement dependency roots, rather than the `YMGap`
umbrella.  The guard is a structural environment query; importing unrelated
continuum certificates cannot strengthen its result and used to force every
repository-wide finite computation to replay before ten hashes were checked. -/
import YMGap.Rubric.ClayTargetPinned
import YMGap.Rubric.ClayScorecard
import YMGap.Rubric.FrontierDAG
import YMGap.Continuum.Tier0Scorecard
import YMGap.Continuum.UnifiedContinuumFloor
import Lean

open Lean Elab Command

namespace YMGapStatementGuard

/-! ## 1. Deterministic structural serialization of an `Expr` -/

/-- Canonical, deterministic rendering of a universe `Level`. -/
partial def canonLevel : Level → String
  | .zero       => "0"
  | .succ l     => "s(" ++ canonLevel l ++ ")"
  | .max a b    => "m(" ++ canonLevel a ++ "," ++ canonLevel b ++ ")"
  | .imax a b   => "i(" ++ canonLevel a ++ "," ++ canonLevel b ++ ")"
  | .param n    => "p[" ++ toString n.eraseMacroScopes ++ "]"
  | .mvar _     => "?u"

/-- Render a list of levels. -/
def canonLevels (ls : List Level) : String :=
  "{" ++ String.intercalate "," (ls.map canonLevel) ++ "}"

/-- **Canonical structural serialization of a closed environment `Expr`.**

A pure fold (no reduction, no instantiation).  Metadata is stripped; macro
scopes are erased from every binder/const/level name so the string is stable
across builds.  Binder NAMES are included (they carry structure-field names in a
constructor's telescope) alongside binder domain/body, so a field rename or a
field-type change both perturb the string. -/
partial def canon : Expr → String
  | .bvar i         => "B" ++ toString i
  | .fvar _         => "Fv"                       -- absent in closed env types
  | .mvar _         => "Mv"                       -- absent in elaborated types
  | .sort l         => "S(" ++ canonLevel l ++ ")"
  | .const n ls     => "C[" ++ toString n.eraseMacroScopes ++ "]" ++ canonLevels ls
  | .app f a        => "A(" ++ canon f ++ "," ++ canon a ++ ")"
  | .lam n t b _    => "L[" ++ toString n.eraseMacroScopes ++ "](" ++ canon t ++ "," ++ canon b ++ ")"
  | .forallE n t b _ => "P[" ++ toString n.eraseMacroScopes ++ "](" ++ canon t ++ "," ++ canon b ++ ")"
  | .letE n t v b _ => "E[" ++ toString n.eraseMacroScopes ++ "](" ++ canon t ++ "," ++ canon v ++ "," ++ canon b ++ ")"
  | .lit (.natVal k) => "N" ++ toString k
  | .lit (.strVal s) => "T\"" ++ s ++ "\""
  | .mdata _ e      => canon e                    -- STRIP metadata
  | .proj tn i e    => "J[" ++ toString tn.eraseMacroScopes ++ "." ++ toString i ++ "](" ++ canon e ++ ")"

/-! ## 2. FNV-1a/64 digest (fully specified — no reliance on `Expr.hash`) -/

/-- FNV-1a 64-bit over the UTF-8 bytes of `s`.  Deterministic; `UInt64`
arithmetic wraps mod 2^64. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

/-- Lowercase hex digit of the low nibble of `n`. -/
def hexDigit (n : UInt64) : Char :=
  let k := n.toNat % 16
  if k < 10 then Char.ofNat (48 + k) else Char.ofNat (97 + (k - 10))

/-- 16-character zero-padded lowercase hex of a `UInt64`. -/
def toHex16 (x : UInt64) : String :=
  (List.range 16).foldl
    (fun acc i => acc.push (hexDigit ((x >>> (UInt64.ofNat ((15 - i) * 4))) &&& 0xf))) ""

/-! ## 3. Per-declaration statement string + hash -/

/-- The full statement-serialization of a declaration: its type, plus (for a
structure/inductive) every constructor's type, or (for a def/abbrev) its value.
Returns `none` if the declaration is missing (a pinned name that vanished — which
is itself drift and is reported by the driver). -/
def constStatementString (env : Environment) (n : Name) : Option String :=
  match env.find? n with
  | none => none
  | some ci =>
    let tyS := "TY(" ++ canon ci.type ++ ")"
    let extra :=
      match ci with
      | .inductInfo iv =>
          let ctorStrs := iv.ctors.map (fun c =>
            match env.find? c with
            | some cci => toString c.eraseMacroScopes ++ "=" ++ canon cci.type
            | none     => toString c.eraseMacroScopes ++ "=<missing>")
          "|IND|" ++ String.intercalate ";" ctorStrs
      | .defnInfo dv    => "|DEF|" ++ canon dv.value
      | .opaqueInfo ov  => "|OPQ|" ++ canon ov.value
      | .thmInfo _      => "|THM|"          -- statement (type) only; proof irrelevant
      | .axiomInfo _    => "|AX|"
      | .ctorInfo _     => "|CTOR|"
      | .recInfo _      => "|REC|"
      | .quotInfo _     => "|QUOT|"
    some (toString n.eraseMacroScopes ++ "::" ++ tyS ++ extra)

/-- Stable statement hash of a declaration (16-hex FNV-1a/64), or `none` if the
declaration is missing. -/
def constStatementHash (env : Environment) (n : Name) : Option String :=
  (constStatementString env n).map (fun s => toHex16 (fnv1a64 s))

/-! ## 4. The pinned frontier statements

Each entry is `(fully-qualified declaration name, expected statement hash)`.  The
first five are the deliberately-uninhabited Clay-frontier structures; the rest
are the shared parameter defs/structures their fields are built from, whose
weakening would trivialize the frontier types WITHOUT changing those types'
constructor serialization (the shared-parameter attack). -/
def pinnedFrontierStatements : List (Name × String) :=
  [ -- ── frontier structures (type + all field/constructor signatures) ──
    (`YMGap.Rubric.ClayTargetPinned.ClayTargetPinned,            "a626368409b9a5a4"),
    (`YMGap.Rubric.ClayScorecard.ClayTarget,                     "cc27a2da027c4a06"),
    -- Reviewed 2026-08-05: `bulkCtrl` was repointed from the refuted bare
    -- localization interface to finite re-based control at the DAG's N,w,pΓ.
    (`YMGap.Rubric.FrontierDAG.FrontierDAG,                      "9a886b2ae801bdd0"),
    (`YMGap.Continuum.Tier0Scorecard.Tier0Scorecard,             "ce2b66cc5711b963"),
    (`YMGap.Continuum.UnifiedContinuumFloor.UniformSpacingFloor, "414cbe2aaf2c2d53"),
    -- ── shared parameter defs/structures (type + value/fields) ──────────
    (`YMGap.Rubric.ClayScorecard.RubricO4Restoration,            "55e2457c6dc7ecd4"),
    (`YMGap.Rubric.ClayScorecard.RubricUniformInCoupling,        "151c42424d3d51a7"),
    (`YMGap.Rubric.ClayScorecard.ClayFixedSpacingMet,            "ed4d40a75b442374"),
    (`YMGap.Rubric.ClayScorecard.ClayContinuumExistence,         "8e722e3552788163"),
    (`YMGap.Continuum.Tier0Scorecard.SubWallA,                   "d34770c151ca6430") ]

/-! ## 5. The build-time driver -/

run_cmd do
  let env ← getEnv
  let mut drift : Array String := #[]
  let mut missing : Array Name := #[]
  let mut report : Array String := #[]
  for (n, expected) in pinnedFrontierStatements do
    match constStatementHash env n with
    | none =>
        missing := missing.push n
    | some actual =>
        report := report.push s!"  {n}  {actual}"
        if expected != "PINME" && expected != actual then
          drift := drift.push
            s!"  {n}\n    pinned : {expected}\n    actual : {actual}"
  -- Always surface the computed hashes (so a deliberate re-pin can copy them).
  logInfo m!"statement-guard computed hashes ({report.size}):\n{String.intercalate "\n" report.toList}"
  unless missing.isEmpty do
    throwError m!"STATEMENT-GUARD FAILED — pinned frontier declaration(s) MISSING:\n  {missing.toList}\n\nA pinned Clay-frontier statement was renamed or deleted. If deliberate, update YMGapStatementGuard.pinnedFrontierStatements under review; a silent disappearance is drift."
  unless drift.isEmpty do
    throwError m!"STATEMENT DRIFT — a pinned Clay-frontier STATEMENT changed:\n{String.intercalate "\n" drift.toList}\n\nThe type signature / field structure (or a shared parameter def's value) of a deliberately-uninhabited frontier type was altered. If this is a deliberate STRENGTHENING that passed human review, update the pinned hash in YMGapStatementGuard.pinnedFrontierStatements after review. If it is a WEAKENING (loosening a field, dropping a hypothesis, `∀`→`∃`, gutting `RubricO4Restoration := True`, …) it MUST be rejected — it is the exact vacuous-weakening attack the pin prevents. This guard is independent of AXIOM_AUDIT.md and of YMGapGuard.lean's inhabitation check."
  logInfo m!"statement-guard OK: {pinnedFrontierStatements.length} frontier statements pinned (no drift)"

end YMGapStatementGuard
