# Avenue-B feasibility scan — NOT a detection

Status: FEASIBILITY SCAN ONLY. No pi, Xi/Schur carrier, row-null normalizer, model comparison, LOFO, or controls were computed.

## Density split
- Verdict: **PASS**.
- Reason: the declared environment proxy spans slack to strong-binding within k<=0.2 at z_eff=0.30.
- Output table: `results/E5SP/avenueB_feasibility/H_density_split.csv`.
- H_slack=0.05; strong-binding threshold H>=0.3; z_eff=0.3; reliable k window=[0.01,0.2] h/Mpc proxy units.
- Proxy: peak-background-style local growth rescaling `sigma8_env=sigma8*max(0.05,1+delta)^0.55` plus local scale compression/expansion `k_env=k*max(0.05,1+delta)^(1/3)`.
- Disclosure: this is an approximate environment-conditioned nonlinearity proxy, not a public density-split data vector or covariance. It can de-risk support, not establish a closure observable.

## ISW availability / signature
- Public availability: feasible in principle via public Planck CMB temperature/lensing products and public LSS catalogues used in ISW cross-correlation work; this packet did not fetch or process ISW maps.
- Signal-to-noise: existing ISW detections are low, typically a few sigma. Planck 2015 reported ISW-lensing bispectrum detection at about 3 sigma and similar combined LSS cross-correlation significance; RACS x Planck reports about 2.8 sigma.
- ISW sources cited: Planck 2015 results XXI, arXiv:1502.01595; RACS x Planck ISW measurement, arXiv:2204.13436.
- Closure distinguishability: ISW is on-target for late-time potential decay, but distinguishing a closure/late-time-potential-decay model from LambdaCDM requires a signed model for potential evolution and cross-correlation shape. With only few-sigma public ISW signals, this is feasible as a model-comparison follow-up, not a standalone decisive route.

## Hashes
- `H_density_split.csv`: `095b679faa8ecb43d76435d1c760197face7add8188a2993a629cdadd4b92725`
- `results/provenance/decommissioned_plan_agent_sources.json`: `ce2f274086e19bea57145980bbf4afd4112fbcd10a4f1d135832e18ada6a6d19`
- `results/provenance/decommissioned_plan_agent_sources.json#de_avenues_map`: `0f84b5e81a896c0a54956c1ff73f9b9c4f687df02f29158775dda7a2e1bab3f0`
- `results/E5SP/EMPIRICAL_BOUNDARY_RESULT.md`: `96a6c8c5050af2d32488f9be3c82669d3bfa55c470903d9e9d67f916205f0dc8`
- script: `13569c5cd3d2523d30c4051aca5439fe2f399280829dcc51e6136772f05fc4b8`
