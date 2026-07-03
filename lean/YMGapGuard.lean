/-
# Frontier uninhabitedness guard (Clay-frontier anti-vacuity check)

This module `import YMGap` and, at elaboration time (i.e. during `lake build`),
reflects over the whole `YMGap.*` environment and FAILS THE BUILD if any
declaration inhabits one of the Clay-frontier types:

  * `YMGap.Continuum.Tier0Scorecard.Tier0Scorecard`  — the a→0 gap-survival scorecard
  * `YMGap.Continuum.UnifiedContinuumFloor.UniformSpacingFloor` — the spacing-uniform floor
  * `YMGap.Rubric.ClayScorecard.ClayTarget` — the full Clay target

These types must remain UNINHABITED: an inhabitant would "close" (a fragment of)
the Clay problem, and the exact failure mode `lean/AGENTS.md` exists to prevent
is an agent producing a VACUOUS or CIRCULAR such term that still passes the
axiom gate (`propext`/`Quot.sound` only).  The axiom baseline (`AXIOM_AUDIT.md`)
cannot catch this — a vacuous term is axiom-clean — and a routine
`make lean-audit-update` would silently bless it.  This guard is INDEPENDENT of
the axiom baseline: it fails on the *type*, not the axioms, so it survives
baseline regeneration.

If a genuine (non-vacuous, human-reviewed, axiom-gated) closure is ever proved,
add its declaration name to `frontierAllowlist` below — deliberately, with
review, never by an agent auto-closing the loop.

Scanned only over `YMGap.*` (any closure of a `YMGap` frontier type would live
there); auto-generated constructors/recursors/projections are skipped.
-/
import YMGap
import Lean

open Lean Elab Command

namespace YMGapFrontierGuard

/-- The Clay-frontier types that MUST remain uninhabited. -/
def frontierTypeNames : List Name :=
  [`YMGap.Continuum.Tier0Scorecard.Tier0Scorecard,
   `YMGap.Continuum.UnifiedContinuumFloor.UniformSpacingFloor,
   `YMGap.Rubric.ClayScorecard.ClayTarget,
   -- Milestone 11.13/11.14: the pinned target and the unified frontier DAG
   -- (both deliberately uninhabited; the guard now protects them too).
   `YMGap.Rubric.ClayTargetPinned.ClayTargetPinned,
   `YMGap.Rubric.FrontierDAG.FrontierDAG]

/-- Human-reviewed allowlist of declarations permitted to have a frontier type
    in conclusion position.  EMPTY by design: the frontier is open.  Adding a
    name here asserts (under human review) that the term is either a genuine
    Clay closure or a deliberately-kept conditional producer — never a vacuous
    auto-closure. -/
def frontierAllowlist : List Name := []

/-- The head symbol of a type's conclusion, after stripping `∀`/`let` binders.
    Pure and syntactic (no unfolding) — robust and cheap. -/
partial def conclHead : Expr → Expr
  | .forallE _ _ b _ => conclHead b
  | .letE _ _ _ b _  => conclHead b
  | e                => e.getAppFn

/-- Auto-generated names (constructors, recursors, projections-machinery) that
    trivially mention their own type and are not agent-authored closures. -/
def isAuxName : Name → Bool
  | .str _ s => s ∈ (["mk", "rec", "recOn", "casesOn", "brecOn", "below",
      "binductionOn", "ibelow", "noConfusion", "noConfusionType", "injEq",
      "sizeOf_spec", "sizeOf_eq", "ofNat"] : List String)
  | _ => false

/-- Is `ci` an UNCONDITIONAL inhabitant of a frontier type — i.e. does its type
    telescope to `F args` (F a frontier type) where EVERY binder appears among
    `args` (so it is a bare parameter, not an open hypothesis)?  A conditional
    reduction `… (h : OpenHyp) … → F args` has a binder `h` that is not an
    argument of `F`, so it is NOT flagged: those are the legitimate reductions.
    A closure (0 hypotheses — whether concrete `F a b` or parametric
    `∀ params, F params`) IS flagged: that is the anti-vacuity target. -/
def isUnconditionalInhabitant (ci : ConstantInfo) : MetaM Bool :=
  Meta.forallTelescopeReducing ci.type fun xs body => do
    match body.getAppFn with
    | .const c _ =>
        if !frontierTypeNames.contains c then return false
        let argIds := body.getAppArgs.filterMap
          (fun a => if a.isFVar then some a.fvarId! else none)
        return xs.all (fun x => x.isFVar && argIds.contains x.fvarId!)
    | _ => return false

run_cmd do
  let env ← getEnv
  let mut offenders : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless (`YMGap).isPrefixOf n do continue
    if n.isInternal || isAuxName n || frontierAllowlist.contains n then continue
    -- cheap pure prefilter: only run the telescope check when the syntactic
    -- conclusion head is a frontier type.
    match conclHead ci.type with
    | .const c _ =>
        if frontierTypeNames.contains c then
          if ← liftTermElabM (isUnconditionalInhabitant ci) then
            offenders := offenders.push n
    | _ => pure ()
  unless offenders.isEmpty do
    throwError m!"FRONTIER GUARD FAILED — a Clay-frontier type is UNCONDITIONALLY inhabited by:\n  {offenders.toList}\n\nTier0Scorecard / UniformSpacingFloor / ClayTarget must remain UNINHABITED (the open Clay problem). An unconditional inhabitant is either a GENUINE closure (verify #print axioms + human review, then add to YMGapFrontierGuard.frontierAllowlist) or — the failure mode lean/AGENTS.md exists to prevent — a VACUOUS/circular term that must be removed. (Conditional reductions `… → F` are NOT flagged.) This guard is independent of AXIOM_AUDIT.md and cannot be silenced by `make lean-audit-update`."
  logInfo m!"frontier-guard OK: {frontierTypeNames.length} Clay-frontier types unconditionally uninhabited across YMGap.*"

end YMGapFrontierGuard
