# Package manifest — <package name>

A package = a coherent cluster of already manager-ACCEPTED packets that completes
a meaningful unit (e.g. a full experiment with controls, or a proposition with
its proof + Lean mechanization). Author this BEFORE dispatching Eddy.

- package id: <slug>
- date: <YYYY-MM-DD>
- owner role(s): <cody | ralph>
- accepted packets (dispatch manifests):
  - ops/dispatches/<role>/<ts>.md — <one-line what it delivered>
- artifacts (exact files/dirs Eddy must verify):
- net claims / results being asserted:
- pass criteria this package must meet (quote idea.md §6 / §10):
- manager verification already done (commands + results):
- Eddy review (durable record): ops/dispatches/eddy/<ts>.md — verdict: <PASS | PASS-WITH-FIXES | FAIL>  (local transcript ops/runs/eddy/<ts>.jsonl is optional supporting detail)
- findings → fixes routed: <finding → role → dispatch ts>
- package status: <OPEN | CLOSED>
