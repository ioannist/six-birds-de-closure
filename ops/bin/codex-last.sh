#!/usr/bin/env bash
# Fallback: extract the FULL final agent message from a codex --json transcript.
# The primary capture path is `codex exec -o <file>` (used by codex-dispatch.sh);
# use this only when you have a transcript but no -o file. Preserves multi-line
# text (slurps and selects the last matching object — no tail -1 truncation).
# Usage: codex-last.sh <jsonl_file>
set -euo pipefail
F="${1:?jsonl file required}"
[[ -f "$F" ]] || { echo "transcript not found: $F" >&2; exit 1; }

msg="$(jq -rs '
  [ .[] as $e
    | ( $e.item    | select(type=="object" and .type=="agent_message") | (.text // .message) )
    , ( $e         | select(.type=="agent_message") | (.text // .message) )
    , ( $e.payload | select(type=="object" and .type=="agent_message") | (.text // .message // .last_agent_message) )
  ]
  | map(select(. != null and . != ""))
  | (last // "")
' "$F" 2>/dev/null || true)"

[[ -n "$msg" ]] || { echo "(no agent_message found in $F)" >&2; exit 3; }
printf '%s\n' "$msg"
