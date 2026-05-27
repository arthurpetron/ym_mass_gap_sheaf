"""Sweep formal/*.tex for memory-rule violations.

Applies the two manuscript-prose rules saved to project memory on 2026-05-27:

  Rule 1: never reference `foo.tex` by name inside `foo.tex`.
  Rule 2: formal LaTeX must not reference outline.md / work_plan.md /
          notes/*.md / context.md / milestone numbers.

This script handles the *safe* mechanical patterns (parenthetical
.md citations, formal/*.tex → \\Cref{ch:*}, paper-level-deliverable
boilerplate sentences, etc.).  Anything ambiguous is left for manual
review; the script prints a "REMAINING" report at the end with line
numbers that need human attention.

Usage:
  python scripts/sweep_latex_rule_violations.py             # dry-run preview
  python scripts/sweep_latex_rule_violations.py --apply     # write changes

Idempotent: running twice produces no further changes.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


CHAPTER_FILES = [
    "sheaf-framework.tex",
    "inductive-state.tex",
    "block-spin-morphism.tex",
    "continuum-measure.tex",
    "os-axioms.tex",
    "os-reconstruction.tex",
    "mass-gap-theorem.tex",
]

# Map basename → chapter-label slug.  Used to turn \texttt{formal/X.tex}
# into \Cref{ch:X}.
FILE_TO_CHAPTER_LABEL = {
    "sheaf-framework.tex": "ch:sheaf-framework",
    "inductive-state.tex": "ch:inductive-state",
    "block-spin-morphism.tex": "ch:block-spin-morphism",
    "continuum-measure.tex": "ch:continuum-measure",
    "os-axioms.tex": "ch:os-axioms",
    "os-reconstruction.tex": "ch:os-reconstruction",
    "mass-gap-theorem.tex": "ch:mass-gap-theorem",
}


# --------------------------------------------------------------------------
# Mechanical replacements.  Order matters; earlier replacements run first.
# --------------------------------------------------------------------------


def make_replacements() -> list[tuple[re.Pattern[str], str, str]]:
    """Return a list of (pattern, replacement, comment) triples.

    `comment` is a short tag printed when the substitution fires; useful
    in the dry-run preview.
    """
    R: list[tuple[re.Pattern[str], str, str]] = []

    # ---- A. Parenthetical .md citations: drop entirely ----
    # "(\texttt{docs/outline.md} \S10.4)" → ""
    # "(\texttt{docs/context.md}, \S3.1)" → ""
    R.append((
        re.compile(
            r"\s*\(\\texttt\{(?:docs/|notes/)?[a-zA-Z0-9_./-]+\.md\}"
            r"(?:,?\s+\\S[0-9A-Za-z.\-]+)?\)"
        ),
        "",
        "drop md parenthetical",
    ))
    # Also handle \codepath{...md} parentheticals (introduced by the
    # earlier strip pass; same intent).
    R.append((
        re.compile(
            r"\s*\(\\codepath\{(?:docs/|notes/)?[a-zA-Z0-9_./\\-]+\.md\}"
            r"(?:,?\s+\\S[0-9A-Za-z.\-]+)?\)"
        ),
        "",
        "drop md parenthetical (codepath)",
    ))

    # ---- B. Milestone parentheticals: drop ----
    # " (Milestone~7.2)" → ""
    # "~(Milestone~7.2)" → ""
    R.append((
        re.compile(r"\s*\(Milestone~?\s*[0-9]+(?:\.[0-9]+)*(?:[a-z-]*)?\)"),
        "",
        "drop Milestone parenthetical",
    ))

    # ---- C. \texttt{formal/X.tex} → \Cref{ch:X} ----
    for filename, chap_label in FILE_TO_CHAPTER_LABEL.items():
        base = filename.replace(".tex", "")
        R.append((
            re.compile(
                rf"\\texttt\{{formal/{re.escape(base)}\.tex\}}"
            ),
            f"\\\\Cref{{{chap_label}}}",
            f"formal/{base}.tex → Cref",
        ))
        R.append((
            re.compile(
                rf"\\codepath\{{formal/{re.escape(base)}\.tex\}}"
            ),
            f"\\\\Cref{{{chap_label}}}",
            f"codepath formal/{base}.tex → Cref",
        ))

    # ---- D. Boilerplate sentences to drop entirely ----
    # "This chapter is the paper-level deliverable of Milestone~X.Y.\n"
    R.append((
        re.compile(
            r"(?:This (?:document|chapter) is the paper-level deliverable of "
            r"Milestone~?[0-9.]+\.\s*)"
        ),
        "",
        "drop paper-level-deliverable sentence",
    ))
    # "corresponds to Milestone~X.Y of \codepath{work_plan.md}."
    R.append((
        re.compile(
            r"(?:This (?:document|chapter) corresponds to Milestone~?[0-9.]+ "
            r"of \\(?:texttt|codepath)\{work\\?_plan\.md\}\.\s*)"
        ),
        "",
        "drop work-plan correspondence sentence",
    ))
    # "Companion Lean type signature: \codepath{...}\n" — kept (code anchor)
    # "Its scope corresponds to Milestone~X.Y of \codepath{work_plan.md}."
    R.append((
        re.compile(
            r"\s+Its scope corresponds to Milestone~?[0-9.]+ "
            r"of \\(?:texttt|codepath)\{work\\?_plan\.md\}\."
        ),
        "",
        "drop scope-corresponds sentence",
    ))

    # ---- E. Bare line-number citations (e.g., "L191--195") to drop ----
    R.append((
        re.compile(r"\s*\(work\\?_plan\.md L[0-9]+(?:--?[0-9]+)?\)"),
        "",
        "drop line-number citation",
    ))
    R.append((
        re.compile(r"work\\?_plan\.md L[0-9]+(?:--?[0-9]+)?"),
        "the work plan",
        "neutralize line-number citation",
    ))

    # ---- F. \texttt{notes/X.md} \S... drop standalone ----
    R.append((
        re.compile(
            r"\\texttt\{notes/[a-zA-Z0-9_.\-]+\.md\}"
            r"(?:\s+\\S[0-9A-Za-z.\-]+)?"
        ),
        "the supporting analysis",
        "neutralize notes/*.md mention",
    ))
    R.append((
        re.compile(
            r"\\codepath\{notes/[a-zA-Z0-9_.\\\-]+\.md\}"
            r"(?:\s+\\S[0-9A-Za-z.\-]+)?"
        ),
        "the supporting analysis",
        "neutralize codepath notes/*.md",
    ))

    # ---- G. \texttt{docs/context.md} / outline.md standalone ----
    R.append((
        re.compile(
            r"\\texttt\{docs/(?:context|outline)\.md\}"
            r"(?:\s+\\S[0-9A-Za-z.\-]+)?"
        ),
        "the development outline",
        "neutralize docs/(context|outline).md",
    ))
    R.append((
        re.compile(
            r"\\codepath\{docs/(?:context|outline)\.md\}"
            r"(?:\s+\\S[0-9A-Za-z.\-]+)?"
        ),
        "the development outline",
        "neutralize codepath docs/(context|outline).md",
    ))

    # ---- H. \texttt{work_plan.md} standalone (rare after F/G) ----
    R.append((
        re.compile(r"\\texttt\{work\\?_plan\.md\}"),
        "the work plan",
        "neutralize texttt work_plan.md",
    ))
    R.append((
        re.compile(r"\\codepath\{work\\?_plan\.md\}"),
        "the work plan",
        "neutralize codepath work_plan.md",
    ))

    # ---- I. Numbered Milestone references → chapter Cref or descriptive ----
    # Map each milestone tag to its replacement phrase.
    # Entries with `Cref` get \Cref{ch:foo}; the rest get plain descriptive.
    milestone_map = {
        "2.1": ("Cref", "ch:sheaf-framework"),
        "2.2": ("Cref", "ch:inductive-state"),
        "2.3": ("Cref", "ch:block-spin-morphism"),
        "3.1": ("text", "the small-field analysis"),
        "3.2": ("text", "the large-field analysis"),
        "3.3": ("text", "the buffer-overlap analysis"),
        "3.4": ("text", "the $\\widehat\\sigma$-trajectory analysis"),
        "3.5": ("text", "the inductive validator"),
        "6.4": ("text", "the long-trajectory analysis"),
        "6.5": ("text", "the chaining-estimate analysis"),
        "7.1": ("text", "the $\\sighinf$-positivity theorem"),
        "7.2": ("Cref", "ch:continuum-measure"),
        "7.3": ("text", "a constructive-reals layer"),
        "8.1": ("Cref", "ch:os-axioms"),
        "8.2": ("Cref", "ch:os-reconstruction"),
        "9.1": ("Cref", "ch:mass-gap-theorem"),
    }
    for tag, (kind, target) in milestone_map.items():
        # \Cref-form replacement.
        if kind == "Cref":
            repl_text = f"\\Cref{{{target}}}"
        else:
            repl_text = target
        # re.sub treats backslash specially in replacement strings;
        # use a lambda to bypass that and substitute the literal text.
        # Catch "Milestone~X.Y" with optional + or trailing context.
        R.append((
            re.compile(rf"Milestone~?\s*{re.escape(tag)}(?:\+|\-[a-z]+)?\b"),
            (lambda rt: lambda m: rt)(repl_text),
            f"Milestone {tag} → {repl_text}",
        ))

    # ---- I'. \Cref-of-\Cref idiom — collapse "\Cref{ch:foo} (\Cref{ch:foo})"
    # The Milestone-pass can produce this when text already had a chapter
    # reference next to a milestone tag.  Normalize to a single \Cref.
    R.append((
        re.compile(
            r"\\Cref\{(ch:[a-z-]+)\}\s+\(\\Cref\{\1\}\)"
        ),
        r"\\Cref{\1}",
        "collapse duplicate Cref",
    ))
    R.append((
        re.compile(
            r"\\Cref\{(ch:[a-z-]+)\},?\s+\\Cref\{\1\}"
        ),
        r"\\Cref{\1}",
        "collapse adjacent Cref",
    ))

    # ---- J. Phase references → descriptive ----
    # "Phase~3 of the inductive step" etc.  We pick the most common forms.
    phase_map = {
        "3":   "the inductive-step analysis",
        "6":   "the Lean-closure analysis",
        "7":   "the continuum-limit analysis",
        "7.1": "the $\\sighinf$-positivity analysis",
        "8":   "the OS analysis",
        "8.1": "the OS-axiom verification",
        "8.2": "the OS-reconstruction analysis",
        "9":   "the mass-gap chapter",
        "9.1": "the mass-gap chapter",
        "10":  "the SU(N) extension framework",
    }
    # Longer tags first, so "Phase 7.1" matches before "Phase 7".
    for tag in sorted(phase_map, key=lambda t: -len(t)):
        repl_text = phase_map[tag]
        R.append((
            re.compile(rf"Phase~?\s*{re.escape(tag)}\b"),
            (lambda rt: lambda m: rt)(repl_text),
            f"Phase {tag} → {repl_text}",
        ))

    # ---- K. Reflexive "the present document" / "this document" → "this chapter"
    R.append((
        re.compile(r"\bthe present document\b"),
        "this chapter",
        "the present document → this chapter",
    ))
    R.append((
        re.compile(r"\bThe present document\b"),
        "This chapter",
        "The present document → This chapter",
    ))
    R.append((
        re.compile(r"\bthis document\b"),
        "this chapter",
        "this document → this chapter",
    ))
    R.append((
        re.compile(r"\bThis document\b"),
        "This chapter",
        "This document → This chapter",
    ))

    # ---- L. SORRY_LEDGER.md and similar .md inside texttt/codepath ----
    R.append((
        re.compile(r"\\texttt\{SORRY[_\\]LEDGER\.md\}"),
        "the open-obligation ledger",
        "neutralize SORRY_LEDGER.md",
    ))
    R.append((
        re.compile(r"\\codepath\{SORRY[_\\]LEDGER\.md\}"),
        "the open-obligation ledger",
        "neutralize codepath SORRY_LEDGER.md",
    ))

    # ---- M. Cleanup: dangling "of the work plan." / "in the work plan."
    R.append((
        re.compile(r"\s+of the work plan\."),
        ".",
        "drop dangling 'of the work plan'",
    ))
    R.append((
        re.compile(r"\s+of the work plan,"),
        ",",
        "drop dangling 'of the work plan,'",
    ))
    R.append((
        re.compile(r"\s+in the work plan\."),
        ".",
        "drop dangling 'in the work plan'",
    ))
    R.append((
        re.compile(r"\s+in the work plan,"),
        ",",
        "drop dangling 'in the work plan,'",
    ))

    return R


# --------------------------------------------------------------------------
# Auditor: what remains after the mechanical pass.
# --------------------------------------------------------------------------


REMAINING_PATTERNS = [
    re.compile(r"Milestone~?\s*[0-9]+(?:\.[0-9]+)*(?:-[a-z]+)?", re.IGNORECASE),
    re.compile(r"\bPhase~?\s*[0-9]+(?:\.[0-9]+)*\b"),
    re.compile(r"\\texttt\{(?:docs|notes|formal|lean[^}]*)?[a-zA-Z0-9_./\\-]+\.md\}"),
    re.compile(r"\\codepath\{(?:docs|notes|formal|lean[^}]*)?[a-zA-Z0-9_./\\-]+\.md\}"),
    re.compile(r"\bwork[_\\]plan\.md\b"),
    re.compile(r"\boutline\.md\b"),
    re.compile(r"\bcontext\.md\b"),
    re.compile(r"\bnotes/[a-z-]+\.md\b"),
    re.compile(r"paper-level deliverable", re.IGNORECASE),
]


def remaining_violations(text: str, filename: str) -> list[tuple[int, str]]:
    """Return list of (line_number, line_content_excerpt) still violating."""
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        # Skip comment lines (dev navigation).
        if line.lstrip().startswith("%"):
            continue
        for pat in REMAINING_PATTERNS:
            if pat.search(line):
                # Skip the file's own \chapter / \label declaration.
                excerpt = line.strip()
                if len(excerpt) > 110:
                    excerpt = excerpt[:107] + "..."
                hits.append((lineno, excerpt))
                break
    return hits


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def process_file(path: Path, replacements: list, *, apply: bool) -> dict:
    """Apply replacements to one file; return summary stats."""
    text = path.read_text()
    new_text = text
    changes: dict[str, int] = {}
    for pat, repl, comment in replacements:
        before = new_text
        new_text = pat.sub(repl, new_text)
        n = len(pat.findall(before))
        if n > 0:
            changes[comment] = changes.get(comment, 0) + n

    remaining = remaining_violations(new_text, path.name)
    if apply and new_text != text:
        path.write_text(new_text)
    return {
        "changes": changes,
        "total_subs": sum(changes.values()),
        "remaining": remaining,
        "changed": new_text != text,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true",
                        help="write changes (default: dry run)")
    parser.add_argument("--root", default=".",
                        help="repository root (default: cwd)")
    args = parser.parse_args()

    formal_dir = Path(args.root) / "formal"
    replacements = make_replacements()

    print(f"{'APPLY' if args.apply else 'DRY-RUN'} mode\n")
    grand_total_subs = 0
    grand_total_remaining = 0
    for fname in CHAPTER_FILES:
        path = formal_dir / fname
        if not path.exists():
            print(f"  [skip] {fname} (not found)")
            continue
        result = process_file(path, replacements, apply=args.apply)
        grand_total_subs += result["total_subs"]
        grand_total_remaining += len(result["remaining"])
        print(f"=== {fname} ===")
        if result["total_subs"] > 0:
            print(f"  Substitutions: {result['total_subs']}")
            for comment, n in sorted(result["changes"].items(), key=lambda x: -x[1]):
                print(f"    {n:>3} × {comment}")
        else:
            print(f"  Substitutions: 0")
        if result["remaining"]:
            print(f"  REMAINING ({len(result['remaining'])}):")
            for lineno, excerpt in result["remaining"][:8]:
                print(f"    L{lineno}: {excerpt}")
            if len(result["remaining"]) > 8:
                print(f"    ... and {len(result['remaining']) - 8} more")
        else:
            print(f"  REMAINING: 0 — clean")
        print()

    print(f"TOTAL: {grand_total_subs} substitutions, "
          f"{grand_total_remaining} lines still need manual review.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
