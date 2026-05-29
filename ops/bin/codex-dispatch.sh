#!/usr/bin/env bash
# Dispatch a single work packet to a persistent codex role session. FAIL-CLOSED.
#
# Roles: cody (coder), ralph (mathematician + Lean), eddy (reviewer).
# First call per role BOOTSTRAPS a fresh thread via stdin (avoids the multi-KB
# argv hang) and records the thread UUID locally; later calls RESUME by UUID and
# VERIFY codex actually resumed THAT thread (a bad UUID otherwise silently spawns
# a fresh thread and loses continuity).
#
# Every run that reaches codex writes a COMMITTED manifest under ops/dispatches/:
#   <ts>.md         on success  (VERDICT: PENDING, for manager review)
#   <ts>.FAILED.md  on any failure after codex ran (VERDICT: FAILED-UNREVIEWED),
#                   recording rc, stderr tail, and the before/after file delta so
#                   aborted runs never leave silent, unaudited repo edits.
#
# Usage: codex-dispatch.sh <role> <prompt_file> [reasoning_effort]
#   reasoning_effort: optional; if omitted, inherits ~/.codex/config.toml (xhigh).
# Env: CODEX_TIMEOUT (seconds, default 1800); CODEX_ALLOW_MEMORY_WRITE=1 to allow
#      codex-memory mutations (default: fail closed).
set -euo pipefail

die() { echo "[dispatch] ERROR: $*" >&2; exit 1; }

# ---------- preflight (no trap yet; no repo edits possible) ----------
ROLE="${1:?usage: codex-dispatch.sh <cody|ralph|eddy> <prompt_file> [effort]}"
PROMPT_FILE="${2:?prompt file required}"
EFFORT="${3:-}"
TIMEOUT="${CODEX_TIMEOUT:-1800}"
UUID_RE='^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$'

case "$ROLE" in cody|ralph|eddy) ;; *) die "unknown role '$ROLE' (expected cody|ralph|eddy)";; esac
[[ -f "$PROMPT_FILE" && -s "$PROMPT_FILE" ]] || die "prompt file missing or empty: $PROMPT_FILE"
command -v codex >/dev/null || die "codex not on PATH"
command -v jq    >/dev/null || die "jq not on PATH"

REPO="$(git rev-parse --show-toplevel)" || die "not inside a git repo"
OPS="$REPO/ops"
THREAD_FILE="$OPS/threads/.codex_thread_id_$ROLE"
RUN_DIR="$OPS/runs/$ROLE"
DISP_DIR="$OPS/dispatches/$ROLE"
mkdir -p "$RUN_DIR" "$DISP_DIR" "$OPS/threads"
# Collision-resistant run id: 1-second wall-clock resolution is not enough (two
# same-role dispatches in the same second would overwrite each other's transcript
# and manifest). Append nanoseconds + PID, then refuse to proceed if any target
# path already exists.
TS="$(date +%Y%m%d-%H%M%S-%N)-$$"
OUT="$RUN_DIR/$TS.jsonl"
ERR="$RUN_DIR/$TS.err"
LAST="$RUN_DIR/$TS.lastmsg.txt"
for _p in "$OUT" "$ERR" "$LAST" "$DISP_DIR/$TS.md" "$DISP_DIR/$TS.FAILED.md" "$DISP_DIR/$TS.prompt.md"; do
  [[ -e "$_p" ]] && die "run-id collision: $_p already exists"
done

cd "$REPO"

# workspace-write + approval-never so agents run non-interactively and can edit
# the repo (deprecated --full-auto implied BOTH). resume has no --sandbox flag, so
# everything goes via -c. Reasoning inherits config unless overridden.
CFG=(-c 'sandbox_mode="workspace-write"' -c 'approval_policy="never"')
[[ -n "$EFFORT" ]] && CFG+=(-c "model_reasoning_effort=\"$EFFORT\"")
COMMON=(--json --skip-git-repo-check -o "$LAST" "${CFG[@]}")

# ---------- content-hash snapshots ----------
# CODEX_MEMDIR override exists only so the self-test can point this at a throwaway
# dir; in production it defaults to the real codex memory store.
MEMDIR="${CODEX_MEMDIR:-$HOME/.codex/memories}"
mem_hash() { find "$MEMDIR" -type f -exec sha256sum {} + 2>/dev/null | sort; }
wt_hash()  { git ls-files --cached --others --exclude-standard -z | xargs -0 -r sha256sum 2>/dev/null | sort; }
wt_delta() { comm -3 "$WT_BEFORE" <(wt_hash) | sed -E 's/^[[:space:]]*[0-9a-fA-F]{64}[[:space:]]+//' | sort -u; }

CODEX_RAN=0
MANIFEST_WRITTEN=0
MODE="?"
WT_BEFORE="$(mktemp)"; WT_AFTER=""
mem_before="$(mem_hash)"
wt_hash > "$WT_BEFORE"

write_failure_manifest() {
  local rc="$1"
  # Compute the worktree delta BEFORE copying the prompt, so the harness's own
  # prompt copy is never mis-reported as a file left behind by the failed run.
  local changed; changed="$(wt_delta 2>/dev/null || true)"
  cp "$PROMPT_FILE" "$DISP_DIR/$TS.prompt.md" 2>/dev/null || true
  {
    echo "# Dispatch FAILED — role=$ROLE  ts=$TS  mode=$MODE"
    echo
    echo "- exit code: $rc"
    echo "- prompt (committed): ops/dispatches/$ROLE/$TS.prompt.md"
    echo "- transcript (local): ops/runs/$ROLE/$TS.jsonl"
    echo "- stderr (local): ops/runs/$ROLE/$TS.err"
    echo
    echo "## stderr tail"
    echo '```'; tail -n 10 "$ERR" 2>/dev/null || true; echo '```'
    echo
    echo "## Files left in the worktree by this FAILED run (before/after hash delta)"
    echo '```'
    if [[ -n "$changed" ]]; then printf '%s\n' "$changed"; else echo "(none)"; fi
    echo '```'
    echo
    echo "- VERDICT: FAILED-UNREVIEWED   <!-- manager: inspect & revert leftover edits, then re-dispatch or escalate -->"
  } > "$DISP_DIR/$TS.FAILED.md"
  echo "[dispatch] FAILURE manifest: ops/dispatches/$ROLE/$TS.FAILED.md" >&2
}

finish() {
  local rc=$?
  if [[ "$rc" -ne 0 && "$CODEX_RAN" -eq 1 && "$MANIFEST_WRITTEN" -eq 0 ]]; then
    write_failure_manifest "$rc"
  fi
  rm -f "${WT_BEFORE:-}" "${WT_AFTER:-}" 2>/dev/null || true
}
trap finish EXIT

# ---------- thread state ----------
RESUMING=0; TID_SAVED=""
if [[ -s "$THREAD_FILE" ]]; then
  TID_SAVED="$(tr -d '[:space:]' < "$THREAD_FILE")"
  [[ "$TID_SAVED" =~ $UUID_RE ]] || die "saved thread id for $ROLE is not a UUID: '$TID_SAVED' ($THREAD_FILE)"
  RESUMING=1
fi
MODE="$([[ $RESUMING -eq 1 ]] && echo resume || echo bootstrap)"

# ---------- run ----------
set +e
if [[ "$RESUMING" -eq 1 ]]; then
  echo "[dispatch] RESUME role=$ROLE thread=$TID_SAVED timeout=${TIMEOUT}s effort=${EFFORT:-<config>}" >&2
  timeout "$TIMEOUT" codex exec resume "${COMMON[@]}" "$TID_SAVED" "$(cat "$PROMPT_FILE")" >"$OUT" 2>"$ERR"
  rc=$?
else
  echo "[dispatch] BOOTSTRAP role=$ROLE (fresh thread via stdin) timeout=${TIMEOUT}s effort=${EFFORT:-<config>}" >&2
  timeout "$TIMEOUT" codex exec "${COMMON[@]}" <"$PROMPT_FILE" >"$OUT" 2>"$ERR"
  rc=$?
fi
CODEX_RAN=1
set -e

# ---------- fail-closed validation (trap writes a FAILED manifest on any die) ----------
if [[ "$rc" -eq 124 ]]; then echo "----stderr tail----" >&2; tail -n5 "$ERR" >&2; die "codex TIMED OUT after ${TIMEOUT}s (role=$ROLE)"; fi
if [[ "$rc" -ne 0  ]]; then echo "----stderr tail----" >&2; tail -n5 "$ERR" >&2; die "codex exited $rc (role=$ROLE)"; fi
[[ -s "$OUT" ]] || die "empty transcript (role=$ROLE): $OUT"
jq -e . "$OUT" >/dev/null 2>&1 || die "transcript is not valid JSONL (role=$ROLE): $OUT"
jq -e -s 'any(.[]; .type? == "turn.completed")' "$OUT" >/dev/null 2>&1 || die "no turn.completed event (role=$ROLE): $OUT"
[[ -s "$LAST" ]] || die "no final agent message captured (role=$ROLE): $LAST"

# memory fail-closed
mem_after="$(mem_hash)"
if [[ "$mem_before" != "$mem_after" ]]; then
  echo "[dispatch] ~/.codex/memories changed (content hash differs):" >&2
  diff <(printf '%s\n' "$mem_before") <(printf '%s\n' "$mem_after") >&2 || true
  if [[ "${CODEX_ALLOW_MEMORY_WRITE:-0}" != "1" ]]; then
    die "agent wrote to codex memory store (forbidden). Set CODEX_ALLOW_MEMORY_WRITE=1 to override if this is codex's own bookkeeping."
  fi
  echo "[dispatch] WARNING: proceeding despite memory change (CODEX_ALLOW_MEMORY_WRITE=1)." >&2
fi

# thread-id verification
TID_RESP="$(jq -r 'select(.thread_id != null) | .thread_id' "$OUT" 2>/dev/null | head -1 || true)"
[[ "$TID_RESP" =~ $UUID_RE ]] || die "could not extract a valid thread_id (role=$ROLE): $OUT"
if [[ "$RESUMING" -eq 1 ]]; then
  [[ "$TID_RESP" == "$TID_SAVED" ]] || die "RESUME MISMATCH (role=$ROLE): asked $TID_SAVED, codex used $TID_RESP — continuity LOST. Thread file NOT updated. See recovery in ops/README.md."
else
  echo "$TID_RESP" > "$THREAD_FILE"
  echo "[dispatch] new thread=$TID_RESP saved to $THREAD_FILE" >&2
fi

# ---------- success manifest ----------
WT_AFTER="$(mktemp)"; wt_hash > "$WT_AFTER"
CHANGED_PATHS="$(comm -3 "$WT_BEFORE" "$WT_AFTER" | sed -E 's/^[[:space:]]*[0-9a-fA-F]{64}[[:space:]]+//' | sort -u || true)"
cp "$PROMPT_FILE" "$DISP_DIR/$TS.prompt.md"
{
  echo "# Dispatch — role=$ROLE  ts=$TS  mode=$MODE"
  echo
  echo "- thread: \`$TID_RESP\`"
  echo "- prompt (committed): ops/dispatches/$ROLE/$TS.prompt.md"
  echo "- transcript (local, gitignored): ops/runs/$ROLE/$TS.jsonl"
  echo "- final message (local, gitignored): ops/runs/$ROLE/$TS.lastmsg.txt"
  echo "- reasoning_effort: ${EFFORT:-<config default>}"
  echo
  echo "## Files changed by this dispatch (PRIMARY change evidence — before/after content hashes)"
  echo '```'
  if [[ -n "$CHANGED_PATHS" ]]; then printf '%s\n' "$CHANGED_PATHS"; else echo "(none — agent reported no file changes)"; fi
  echo '```'
  echo
  echo "## git status --short (supplementary; unreliable for new files pre-commit)"
  echo '```'; git status --short || true; echo '```'
  echo
  echo "## Manager review (fill in — see ops/review_rubric.md)"
  echo "- VERDICT: PENDING   <!-- ACCEPT | FIX-REQUIRED -->"
  echo "- fix iteration: 0/2"
  echo "- verification (exact commands run + result):"
  echo "- changed files confirmed against report:"
  echo "- follow-up / fix dispatched:"
} > "$DISP_DIR/$TS.md"
MANIFEST_WRITTEN=1

echo
echo "===== final agent message (role=$ROLE) ====="
cat "$LAST"
echo
echo "===== manifest: ops/dispatches/$ROLE/$TS.md | transcript: ops/runs/$ROLE/$TS.jsonl | stderr: ops/runs/$ROLE/$TS.err ====="
