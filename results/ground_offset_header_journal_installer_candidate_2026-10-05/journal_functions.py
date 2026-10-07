def install_target(row,raw,receipts,installed,attempted):
    p=ROOT/row['path']
    assert current_hash(p)==row['existing_target_sha256'],row['path']
    attempted.append(row['path'])
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_target=row['path'],phase='before_write',fresh_registered_build_pending=True,goal_complete=False))
    atomically_install(p,raw)
    assert sha(p)==row['sha256'],row['path']
    installed.append(row['path'])
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_target=None,phase='write_completed',fresh_registered_build_pending=True,goal_complete=False))

def observed_targets(plan):
    observations={}
    for row in plan['targets']:
        p=ROOT/row['path']
        item=dict(original_sha256=row['existing_target_sha256'],proposed_sha256=row['sha256'])
        try:
            assert p.resolve().is_relative_to(ROOT.resolve()),'Target resolves outside repository'
            value=current_hash(p)
            item.update(observed_sha256=value,matches_original=value==row['existing_target_sha256'],matches_proposed=value==row['sha256'],absent=value is None)
        except BaseException as e:item.update(observation_error=repr(e))
        observations[row['path']]=item
    return observations

def record_installation_failure(receipts,plan,installed,attempted,error):
    observed=observed_targets(plan)
    pending=[p for p in attempted if p not in installed]
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_targets=pending,phase='failed',observed_targets=observed,fresh_registered_build_pending=True,goal_complete=False))
    write(receipts/'terminal.json',dict(terminal_exit_code=1,installed=installed,attempted=attempted,pending_targets=pending,observed_targets=observed,error=repr(error),traceback=traceback.format_exc(),goal_complete=False))
