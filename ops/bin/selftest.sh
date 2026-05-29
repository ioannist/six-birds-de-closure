#!/usr/bin/env bash
# Hermetic self-test for the ops/ harness. Uses a fake `codex` on PATH and
# throwaway git repos — makes NO real codex/network calls. Run from anywhere:
#   ops/bin/selftest.sh
# Exits nonzero if any check fails.
set -uo pipefail
OPSDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # the real ops/
PASS=0; FAIL=0
ok(){ echo "  PASS: $1"; PASS=$((PASS+1)); }
no(){ echo "  FAIL: $1"; FAIL=$((FAIL+1)); }

# ---------- fake codex (honors `exec [resume] ... -o <file>`; CODEX_FAKE_SCENARIO) ----------
make_fakebin() {
  local d="$1"; mkdir -p "$d"
  cat > "$d/codex" <<'FAKE'
#!/usr/bin/env bash
set -uo pipefail
OFILE=""; argv=("$@")
for ((i=0;i<${#argv[@]};i++)); do [[ "${argv[i]}" == "-o" ]] && OFILE="${argv[i+1]:-}"; done
TID="${CODEX_FAKE_TID:-aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee}"
emit_head(){ echo "{\"type\":\"thread.started\",\"thread_id\":\"$TID\"}"; }
case "${CODEX_FAKE_SCENARIO:-ok}" in
  hang)        sleep 5;;
  exitfail)    emit_head; exit 7;;                                   # no agent edit, fails
  noturn)      emit_head; [[ -n "$OFILE" ]] && printf 'hi\n' > "$OFILE"; exit 0;;  # missing turn.completed
  mismatch)    TID="ffffffff-1111-2222-3333-444444444444";;
  invalidjson) printf 'this is NOT json\n'; [[ -n "$OFILE" ]] && printf 'x\n' > "$OFILE"; exit 0;;  # transcript not valid JSONL
  emptylast)   emit_head; echo '{"type":"turn.started"}'; echo '{"type":"item.completed","item":{"type":"agent_message","text":"hi"}}'; echo '{"type":"turn.completed"}'; exit 0;;  # never writes -o
  notid)       echo '{"type":"turn.started"}'; echo '{"type":"item.completed","item":{"type":"agent_message","text":"hi"}}'; echo '{"type":"turn.completed"}'; [[ -n "$OFILE" ]] && printf 'hi\n' > "$OFILE"; exit 0;;  # no thread.started
  memorywrite) mkdir -p "${CODEX_MEMDIR:?}"; printf 'sneaky\n' > "$CODEX_MEMDIR/sneaky.md";;  # then falls through to success emission
esac
printf 'agent wrote this\n' > agent_out.txt                       # simulate a repo edit
emit_head
echo '{"type":"turn.started"}'
echo '{"type":"item.completed","item":{"type":"agent_message","text":"did it\nsecond line"}}'
echo '{"type":"turn.completed","usage":{}}'
[[ -n "$OFILE" ]] && printf 'did it\nsecond line\n' > "$OFILE"
exit 0
FAKE
  chmod +x "$d/codex"
}

make_sandbox() {                  # echoes a fresh repo path with harness + fakebin
  local sb; sb="$(mktemp -d)"
  ( cd "$sb" && git init -q . && git config user.email t@t && git config user.name t )
  mkdir -p "$sb/ops/bin" "$sb/ops/bootstrap" "$sb/ops/threads" "$sb/ops/dispatches"
  cp "$OPSDIR/bin/codex-dispatch.sh" "$OPSDIR/bin/codex-last.sh" "$sb/ops/bin/"
  cp "$OPSDIR/.gitignore" "$sb/ops/.gitignore"
  printf 'bootstrap prompt\n' > "$sb/ops/bootstrap/cody.md"
  make_fakebin "$sb/.fakebin"
  printf '%s' "$sb"
}

manifest_block() {                # extract first fenced block after a header
  awk -v h="$2" 'index($0,h){g=1} g&&/^```$/{n++; next} g&&n==1{print} n==2{exit}' "$1"
}

echo "== unit: codex-last.sh preserves multiline =="
T="$(mktemp)"
printf '%s\n' \
 '{"type":"thread.started","thread_id":"12345678-1234-1234-1234-1234567890ab"}' \
 '{"type":"item.completed","item":{"type":"agent_message","text":"l1\nl2\nl3"}}' \
 '{"type":"turn.completed"}' > "$T"
out="$("$OPSDIR/bin/codex-last.sh" "$T" 2>/dev/null || true)"
[[ "$out" == *l1* && "$out" == *l3* && "$(printf '%s' "$out" | wc -l)" -ge 2 ]] && ok "multiline preserved" || no "multiline (got: $out)"
rm -f "$T"

echo "== unit: Lean trust diff catches a SECOND distinct axiom in the same file =="
LT="$(mktemp -d)"; mkdir -p "$LT/lean"; : > "$LT/lean/lakefile.lean"
printf 'axiom one : True\n' > "$LT/lean/A.lean"
b="$( cd "$OPSDIR/.." && "$OPSDIR/bin/lean-trust-scan.sh" --occurrences "$LT/lean" )"
printf 'axiom two : True\n' >> "$LT/lean/A.lean"
c="$( cd "$OPSDIR/.." && "$OPSDIR/bin/lean-trust-scan.sh" --occurrences "$LT/lean" )"
added="$(comm -13 <(printf '%s\n' "$b" | LC_ALL=C sort) <(printf '%s\n' "$c" | LC_ALL=C sort) | sed '/^$/d')"
[[ "$added" == *A.lean*axiom*two* ]] && ok "2nd distinct axiom detected as new occurrence" || no "2nd axiom missed (added=$added)"
rm -rf "$LT"

echo "== unit: Lean trust diff catches a DUPLICATE identical sorry line (multiset) =="
LT="$(mktemp -d)"; mkdir -p "$LT/lean"; : > "$LT/lean/lakefile.lean"
printf 'example : True := by\n  sorry\n' > "$LT/lean/D.lean"
b="$( cd "$OPSDIR/.." && "$OPSDIR/bin/lean-trust-scan.sh" --occurrences "$LT/lean" )"
printf 'example : True := by\n  sorry\n' >> "$LT/lean/D.lean"   # a SECOND, byte-identical "  sorry" line
c="$( cd "$OPSDIR/.." && "$OPSDIR/bin/lean-trust-scan.sh" --occurrences "$LT/lean" )"
added="$(comm -13 <(printf '%s\n' "$b" | LC_ALL=C sort) <(printf '%s\n' "$c" | LC_ALL=C sort) | sed '/^$/d')"
[[ -n "$added" && "$added" == *sorry* ]] && ok "duplicate identical sorry detected (multiset)" || no "duplicate sorry missed (added=$added)"
rm -rf "$LT"

echo "== e2e: bootstrap OK → thread saved, success manifest, agent file in delta, prompt NOT in delta =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=ok ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
tid="$(cat "$SB/ops/threads/.codex_thread_id_cody" 2>/dev/null || true)"
man="$(ls "$SB"/ops/dispatches/cody/*.md 2>/dev/null | grep -v FAILED | head -1 || true)"
[[ "$rc" -eq 0 ]] && ok "exit 0" || no "exit $rc"
[[ "$tid" == "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee" ]] && ok "thread UUID saved" || no "thread save ($tid)"
[[ -n "$man" && ! -e "${man%.md}.FAILED.md" ]] && ok "success manifest, no FAILED" || no "manifest state"
if [[ -n "$man" ]]; then
  blk="$(manifest_block "$man" "Files changed by this dispatch")"
  [[ "$blk" == *agent_out.txt* ]] && ok "agent file in delta" || no "agent file missing from delta ($blk)"
  [[ "$blk" != *prompt.md* ]] && ok "prompt copy NOT in delta" || no "prompt copy leaked into delta"
fi
rm -rf "$SB" "$ERRF"

echo "== e2e: RESUME MISMATCH → fails, thread file unchanged, FAILED manifest =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
echo "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee" > "$SB/ops/threads/.codex_thread_id_cody"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=mismatch ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
tid="$(cat "$SB/ops/threads/.codex_thread_id_cody")"
[[ "$rc" -ne 0 ]] && ok "nonzero exit on mismatch" || no "should have failed"
[[ "$tid" == "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee" ]] && ok "thread file NOT overwritten" || no "thread file clobbered ($tid)"
grep -q "RESUME MISMATCH" "$ERRF" && ok "mismatch reported" || no "no mismatch message"
ls "$SB"/ops/dispatches/cody/*.FAILED.md >/dev/null 2>&1 && ok "FAILED manifest written" || no "no FAILED manifest"
rm -rf "$SB" "$ERRF"

echo "== e2e: agent-no-edit failure → FAILED manifest leftover delta is (none), not the prompt copy =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=exitfail ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
fman="$(ls "$SB"/ops/dispatches/cody/*.FAILED.md 2>/dev/null | head -1 || true)"
[[ "$rc" -ne 0 && -n "$fman" ]] && ok "FAILED manifest on agent-no-edit failure" || no "expected FAILED manifest"
if [[ -n "$fman" ]]; then
  left="$(manifest_block "$fman" "Files left in the worktree")"
  [[ "$left" == "(none)" ]] && ok "leftover delta is (none) — prompt copy not counted" || no "leftover polluted: [$left]"
fi
rm -rf "$SB" "$ERRF"

echo "== e2e: timeout (hang) → FAILED manifest, no thread file =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=hang CODEX_TIMEOUT=1 ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
[[ "$rc" -ne 0 ]] && ok "nonzero exit on timeout" || no "should have timed out"
ls "$SB"/ops/dispatches/cody/*.FAILED.md >/dev/null 2>&1 && ok "FAILED manifest on timeout" || no "no FAILED manifest"
[[ ! -e "$SB/ops/threads/.codex_thread_id_cody" ]] && ok "no thread file from failed bootstrap" || no "thread file should be absent"
rm -rf "$SB" "$ERRF"

echo "== e2e: missing turn.completed → fails closed =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=noturn ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
[[ "$rc" -ne 0 ]] && ok "nonzero exit when turn.completed missing" || no "should fail without turn.completed"
ls "$SB"/ops/dispatches/cody/*.FAILED.md >/dev/null 2>&1 && ok "FAILED manifest" || no "no FAILED manifest"
rm -rf "$SB" "$ERRF"

echo "== e2e: invalid JSONL transcript → fails closed, FAILED manifest =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=invalidjson ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
[[ "$rc" -ne 0 ]] && ok "nonzero exit on invalid JSONL" || no "should fail on invalid JSONL"
ls "$SB"/ops/dispatches/cody/*.FAILED.md >/dev/null 2>&1 && ok "FAILED manifest (invalid JSONL)" || no "no FAILED manifest"
rm -rf "$SB" "$ERRF"

echo "== e2e: empty final message (-o not written) → fails closed =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=emptylast ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
[[ "$rc" -ne 0 ]] && ok "nonzero exit on empty final message" || no "should fail on empty -o"
ls "$SB"/ops/dispatches/cody/*.FAILED.md >/dev/null 2>&1 && ok "FAILED manifest (empty last)" || no "no FAILED manifest"
rm -rf "$SB" "$ERRF"

echo "== e2e: missing/invalid thread_id → fails closed =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=notid ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
[[ "$rc" -ne 0 ]] && ok "nonzero exit on missing thread_id" || no "should fail without thread_id"
[[ ! -e "$SB/ops/threads/.codex_thread_id_cody" ]] && ok "no thread file saved" || no "thread file should be absent"
rm -rf "$SB" "$ERRF"

echo "== e2e: forbidden codex-memory write → fails closed; allowed with override =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"; MEMD="$(mktemp -d)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_MEMDIR="$MEMD" CODEX_FAKE_SCENARIO=memorywrite ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
[[ "$rc" -ne 0 ]] && ok "nonzero exit on codex-memory write" || no "should fail on memory write"
ls "$SB"/ops/dispatches/cody/*.FAILED.md >/dev/null 2>&1 && ok "FAILED manifest (memory write)" || no "no FAILED manifest"
rm -rf "$SB"; SB="$(make_sandbox)"; rm -f "$MEMD"/* 2>/dev/null
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_MEMDIR="$MEMD" CODEX_ALLOW_MEMORY_WRITE=1 CODEX_FAKE_SCENARIO=memorywrite ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" ); rc=$?
[[ "$rc" -eq 0 ]] && ok "override (CODEX_ALLOW_MEMORY_WRITE=1) allows memory write" || no "override should allow (rc=$rc)"
rm -rf "$SB" "$ERRF" "$MEMD"

echo "== e2e: run-id collision resistance — two rapid same-second dispatches → 2 distinct manifests =="
SB="$(make_sandbox)"; ERRF="$(mktemp)"
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=ok ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" )
( cd "$SB" && PATH="$SB/.fakebin:$PATH" CODEX_FAKE_SCENARIO=ok ops/bin/codex-dispatch.sh cody ops/bootstrap/cody.md >/dev/null 2>"$ERRF" )
n="$(ls "$SB"/ops/dispatches/cody/*.md 2>/dev/null | grep -v prompt | grep -v FAILED | wc -l | tr -d ' ')"
[[ "$n" -ge 2 ]] && ok "two rapid dispatches → $n distinct manifests" || no "manifest collision (n=$n)"
rm -rf "$SB" "$ERRF"

echo
echo "==== selftest: $PASS passed, $FAIL failed ===="
[[ "$FAIL" -eq 0 ]]
