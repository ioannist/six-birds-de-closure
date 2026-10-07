# Campaign statement-printer stack recovery

The aggregate-recovery campaign completed all 1734 individual module checks:
993 retained checks and 741 fresh compilations. Its repaired original-sample
aggregate compiled successfully with unchanged theorem statements. The subsequent
combined 20628-statement audit aborted with actual Lean exit code -6 and the
diagnostic `Stack overflow detected. Aborting.` while printing theorem types.
The campaign's terminal receipt records failure, rather than qualification
success. The axiom stage of that run did not execute.

All six prior recovery/integration drivers have stopped. Their actual error
logs remain intact. The integration controller stopped while waiting for its
proof parents, before registered source installation or build commands.
`results/native_campaign_statement_stack_failure_2026-10-06` preserves and
reads back fourteen original source, receipt, inventory and failure-log files,
with their SHA256 bindings. No successful terminal marker was added to the
failed run and no module compiler check was relabeled as a new compilation.

An isolated audit recovery is live at PID 2490922, exec session 45294:

```
python3 /tmp/de_native_campaign_stack_recovery_2026-10-06/run_audits.py
```

Its driver log is
`/tmp/de_native_campaign_stack_recovery_2026-10-06/driver.log`.
Before launching Lean it validates all 1734 module source/object/log bindings,
terminal-zero records, exact production inventory, retained-receipt bindings
and the prior source freeze. Its statement source is byte-identical to the
failed full source. It runs all 20628 ordered statement queries and then all
20628 ordered transitive-axiom queries, preserving actual command exits and log
hashes. The statement audit additionally requires every declared theorem's
printed heading in the exact query order; the axiom audit requires that same
order and only `propext`, `Classical.choice` and `Quot.sound`.

The only compiler resource change is a 65536-KiB thread stack (`lean -s 65536`)
and corresponding main-process stack allowance, with `LEAN_NUM_THREADS=4`.
There is no truncation option, theorem or proof change, omitted query, or
weakened mathematical claim. The completed compiler objects are reused through
their exact bindings, rather than recompiled or copied into registered Lean.

The complete unchanged statement audit has now returned actual exit0; all
20628 printed theorem headings matched the exact query order. The full
transitive-axiom audit is live. Successful completion of both audits, adoption
by the stopped downstream qualification/semantic/
integration drivers, genuine registered builds and cumulative audits, final
mathematical review, documentation reconciliation and commit remain pending.
This is an execution-resource repair, not a completed qualification claim.
The physical-frame bridge remains outside the user-authorized revised scope;
the paper and original runtime remain unchanged.
