#!/usr/bin/env bash
# Install docs/arthur_tex_style/ into MacTeX's local TEXMF tree so the class
# is available globally (i.e., so any `\documentclass{arthur-book}` works
# from any directory without setting TEXINPUTS).
#
# Usage:
#   scripts/install_arthur_tex_style.sh           # install (symlink)
#   scripts/install_arthur_tex_style.sh --copy    # install (copy, not symlink)
#   scripts/install_arthur_tex_style.sh --remove  # uninstall
#
# Behaviour
# ---------
# - Default action: symlink each .cls / .sty file under
#   $TEXMFHOME/tex/latex/arthur-book/, so future edits to the style files
#   in docs/arthur_tex_style/ are picked up immediately.
# - With --copy, the files are copied (no future edits picked up).
# - With --remove, the install directory is removed.
#
# This script does NOT require sudo: TEXMFHOME lives under your home
# directory (typically ~/Library/texmf on macOS / TeX Live 2025).
#
# After install you can drop `TEXINPUTS=...` from your Makefile.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STYLE_SRC="$REPO_ROOT/docs/arthur_tex_style"
TEXMFHOME="$(kpsewhich -var-value=TEXMFHOME)"
INSTALL_DIR="$TEXMFHOME/tex/latex/arthur-book"

if [[ ! -d "$STYLE_SRC" ]]; then
    echo "error: $STYLE_SRC does not exist" >&2
    exit 1
fi

case "${1:-}" in
    --remove)
        if [[ -d "$INSTALL_DIR" ]]; then
            rm -rf "$INSTALL_DIR"
            echo "Removed $INSTALL_DIR"
        else
            echo "Nothing to remove at $INSTALL_DIR"
        fi
        # Refresh the kpathsea database (mktexlsr) so removal takes effect.
        if command -v mktexlsr >/dev/null 2>&1; then
            mktexlsr "$TEXMFHOME" >/dev/null
            echo "Refreshed TEXMFHOME ls-R database."
        fi
        exit 0
        ;;
    --copy)
        MODE=copy
        ;;
    "")
        MODE=symlink
        ;;
    *)
        echo "unknown option: $1" >&2
        echo "usage: $0 [--copy|--remove]" >&2
        exit 2
        ;;
esac

mkdir -p "$INSTALL_DIR"
mkdir -p "$INSTALL_DIR/tex"

# Install the class.
if [[ "$MODE" == "symlink" ]]; then
    ln -sf "$STYLE_SRC/arthur-book.cls" "$INSTALL_DIR/arthur-book.cls"
else
    cp -f "$STYLE_SRC/arthur-book.cls" "$INSTALL_DIR/arthur-book.cls"
fi

# Install all support packages — preserve the `tex/` layout because
# arthur-book.cls loads them as \RequirePackage{tex/arthur-symbols}.
if [[ -d "$STYLE_SRC/tex" ]]; then
    for sty in "$STYLE_SRC/tex/"*.sty; do
        [[ -e "$sty" ]] || continue
        base="$(basename "$sty")"
        if [[ "$MODE" == "symlink" ]]; then
            ln -sf "$sty" "$INSTALL_DIR/tex/$base"
        else
            cp -f "$sty" "$INSTALL_DIR/tex/$base"
        fi
    done
fi

# Install asset files (e.g. TikZ definitions) so they resolve via kpsewhich.
if [[ -d "$STYLE_SRC/assets" ]]; then
    mkdir -p "$INSTALL_DIR/assets"
    for asset in "$STYLE_SRC/assets/"*; do
        [[ -e "$asset" ]] || continue
        base="$(basename "$asset")"
        if [[ "$MODE" == "symlink" ]]; then
            ln -sf "$asset" "$INSTALL_DIR/assets/$base"
        else
            cp -f "$asset" "$INSTALL_DIR/assets/$base"
        fi
    done
fi

# Refresh the kpathsea database so the new files are discoverable.
if command -v mktexlsr >/dev/null 2>&1; then
    mktexlsr "$TEXMFHOME" >/dev/null
    echo "Refreshed TEXMFHOME ls-R database."
fi

echo
echo "Installed arthur-book to $INSTALL_DIR ($MODE)"
echo "Verify with: kpsewhich arthur-book.cls"
