# Data Provenance

Large payloads are not tracked. In this workspace, `data/raw` and `data/processed` are symlinks to `/mnt/data-drive/sbt-de/data/raw` and `/mnt/data-drive/sbt-de/data/processed`. Each dataset below has a tracked manifest in `data/manifests/` with checksums marked `TODO-on-fetch` until the acquisition packet fetches and verifies real files.

Packet C-E1-data has provisioned the E1 inputs. The fetched raw and processed payloads live on the data drive; the tracked manifests record SHA-256 digests, sizes, access mode, and any fallback status. DESI DR2 BAO is currently the documented compressed-Gaussian fallback (`aor_status=budgeted`). Planck 2018 uses the native Cobaya/`clik` likelihood under `data/raw/planck_2018/cobaya-packages`.

| Dataset | Primary fetch handle | Fallback |
|---|---|---|
| DESI_DR2_BAO | DESI public release, arXiv:2503.14738 | compressed BAO-only Gaussian likelihood |
| DESI_RSD_FS | DESI DR2 compressed RSD summary; method control arXiv:2411.12026 | DR1 full-shape method control only |
| CC_HZ | Moresco compilation, arXiv:2201.07241 | diagonal-only H(z) Gaussian |
| KIDS_LEGACY_BAO | arXiv:2503.19441 | Gaussian published-ratio approximation |
| DES_Y6_BAO | arXiv:2601.14559 | compressed alpha_parallel/alpha_perp likelihood |
| DES_Y3_BAO | arXiv:2212.00091 | DES Y3 compressed BAO likelihood |
| PLANCK_2018 | Planck Legacy Archive / cobaya clik, arXiv:1807.06209 | compressed CMB distance priors |
| SPT_3G | D1 arXiv:2506.20707 and 2018 arXiv:2212.05642 | rebinned/subset band powers |
| ACT_DR6 | arXiv:2509.02945 | compressed distance priors |
| PANTHEON_PLUS | Pantheon+SH0ES public release, arXiv:2202.04077 | binned distance-modulus likelihood |
| UNION3 | Union3 public release, arXiv:2401.06956 | compressed five-bin likelihood |
| DES_SN5YR | Zenodo:13827844 / arXiv:2401.02929 | published fitted mu(z) summary |
| DES_Y3_SN_INTERNAL | arXiv:2212.00091 | standalone use out of scope |
| DES_Y6 | arXiv:2601.14559 | Gaussian 3x2pt vector/covariance |
| KIDS_LEGACY | arXiv:2503.19441 | shear-only Gaussian likelihood |
| HSC_Y3 | arXiv:2511.18134 | original photo-z comparison leg |
| DES_Y3_3X2PT | arXiv:2212.00091 | compressed DES Y3 3x2pt likelihood |
| CMB_LENSING | ACT/SPT lensing releases, arXiv:2509.02945 | Planck-only lensing |
| SH0ES | arXiv:2509.01667 | Gaussian prior if posterior samples unavailable |
| CCHP_TRGB_JAGB | arXiv:2408.06153 | quadrature Gaussian per calibrator |
| TDCOSMO | arXiv:2506.03023 (2110.00517 historical-control) | published model-variant posterior family |
| SIRENS_GW170817 | arXiv:1709.05895 | published asymmetric posterior; Gaussianization is budgeted |
| INVERSE_LADDER | derived from E1 committed posterior summaries | inherits upstream fallback status |

Fetch commands are intentionally deferred to the data-acquisition packet, where checksums and exact file lists will be recorded in the manifests.
