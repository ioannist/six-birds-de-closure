#!/usr/bin/env bash
# Whole-tree Lean trust-base disclosure + baseline diff.
#
# Trust base is expected (the corpus uses opacity-guarded axioms by design). The
# reviewable quantity is GROWTH: any NEW occurrence since the last accepted Lean
# package must be justified. Tracks per-OCCURRENCE records
# "<relpath>\t<keyword>\t<normalized-line-text>" — so a *second* axiom/sorry/etc.
# added to a file that already contained that keyword IS detected (not just new
# file/keyword classes). Normalizing the line text (whitespace-collapsed) avoids
# false positives from pure reformatting while still flagging genuinely new ones.
#
# Modes:
#   (default/report)  human-readable report
#   --occurrences     machine records (sorted, duplicates preserved = MULTISET), used by --baseline/--diff
#   --baseline        write --occurrences to ops/lean-trust-baseline.txt (commit on accept)
#   --diff            diff current occurrences vs baseline; exit 2 if any ADDED
# Optional 2nd arg = lean_root (default: dir containing the lakefile).
set -euo pipefail

MODE="${1:-report}"
ROOT_ARG="${2:-}"
REPO="$(git rev-parse --show-toplevel)"
BASELINE="$REPO/ops/lean-trust-baseline.txt"
PAT='\b(sorry|admit|axiom|constant|opaque|unsafe|native_decide|implemented_by)\b'
# NOTE: these are TRACKED (growth must be justified), NOT forbidden. `native_decide` is included
# deliberately — it trusts the compiler (bypasses the kernel), a genuine trust extension. The Lean
# plan (plan/05) therefore PREFERS `decide`, and treats each surviving `native_decide` as a justified
# baseline entry. So scanner and plan agree: track-and-justify, don't prohibit.

resolve_root() {
  if [[ -n "$ROOT_ARG" ]]; then printf '%s' "$ROOT_ARG"; return; fi
  local lf; lf="$(find "$REPO" -name 'lakefile.*' -not -path '*/.lake/*' 2>/dev/null | head -1 || true)"
  [[ -n "$lf" ]] && dirname "$lf" || printf ''
}

emit_occurrences() {
  local root="$1"
  [[ -n "$root" && -d "$root" ]] || return 0
  while IFS= read -r -d '' f; do
    local rel hits; rel="${f#"$root"/}"
    # `|| true`: grep exits nonzero on a no-match file, which under set -e+pipefail
    # would otherwise abort the whole scan.
    hits="$(grep -nE "$PAT" "$f" 2>/dev/null || true)"
    [[ -n "$hits" ]] || continue
    while IFS= read -r line; do
      local content norm kws
      content="${line#*:}"                                       # strip "<lineno>:"
      norm="$(printf '%s' "$content" | tr '\t' ' ' | tr -s ' ' | sed -E 's/^ +| +$//g')"
      kws="$(printf '%s' "$content" | grep -oE "$PAT" | sort -u || true)"
      while IFS= read -r kw; do
        if [[ -n "$kw" ]]; then printf '%s\t%s\t%s\n' "$rel" "$kw" "$norm"; fi
      done <<< "$kws"
    done <<< "$hits"
    # plain `sort` (NOT `sort -u`): duplicates are PRESERVED so --diff is a MULTISET
    # comparison — a 2nd identical trust line (same file+keyword+text) shows as an
    # extra record and is therefore caught.
  done < <(find "$root" -name '*.lean' -not -path '*/.lake/*' -print0 2>/dev/null) | LC_ALL=C sort
}

ROOT="$(resolve_root)"
case "$MODE" in
  --occurrences)
    emit_occurrences "$ROOT"
    ;;
  --baseline)
    [[ -n "$ROOT" ]] || { echo "no Lean project found — baseline not written" >&2; exit 0; }
    emit_occurrences "$ROOT" > "$BASELINE"
    echo "wrote baseline ($(wc -l < "$BASELINE") occurrences) → ops/lean-trust-baseline.txt  (commit it)"
    ;;
  --diff)
    cur="$(emit_occurrences "$ROOT")"
    base="$(cat "$BASELINE" 2>/dev/null || true)"
    added="$(comm -13 <(printf '%s\n' "$base" | LC_ALL=C sort) <(printf '%s\n' "$cur" | LC_ALL=C sort) | sed '/^$/d')"
    removed="$(comm -23 <(printf '%s\n' "$base" | LC_ALL=C sort) <(printf '%s\n' "$cur" | LC_ALL=C sort) | sed '/^$/d')"
    echo "# Lean trust-base diff vs ops/lean-trust-baseline.txt"
    echo "## ADDED (every new occurrence must be justified before acceptance):"
    [[ -n "$added" ]] && printf '%s\n' "$added" || echo "(none)"
    echo "## REMOVED:"
    [[ -n "$removed" ]] && printf '%s\n' "$removed" || echo "(none)"
    [[ -z "$added" ]] || exit 2
    ;;
  report|*)
    [[ -n "$ROOT" ]] || { echo "no Lean project (lakefile) found under $REPO — nothing to scan"; exit 0; }
    echo "# Lean trust-base scan: $ROOT"
    occ="$(emit_occurrences "$ROOT")"
    [[ -n "$occ" ]] && printf '%s\n' "$occ"
    echo "---"
    echo "total trust-base occurrences: $(printf '%s' "$occ" | grep -c . || true)"
    echo "(Run --diff to see what is NEW vs the committed baseline; --baseline to refresh on accept.)"
    ;;
esac
