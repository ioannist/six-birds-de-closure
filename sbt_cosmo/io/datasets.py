"""Dataset loader contracts and manifest-backed data records."""

from __future__ import annotations

import json
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any

import numpy as np

from sbt_cosmo.io.checksums import sha256_file

DATASET_KEYS = (
    "DESI_DR2_BAO",
    "DESI_RSD_FS",
    "CC_HZ",
    "KIDS_LEGACY_BAO",
    "DES_Y6_BAO",
    "DES_Y3_BAO",
    "PLANCK_2018",
    "SPT_3G",
    "ACT_DR6",
    "PANTHEON_PLUS",
    "UNION3",
    "DES_SN5YR",
    "DES_Y3_SN_INTERNAL",
    "DES_Y6",
    "KIDS_LEGACY",
    "HSC_Y3",
    "DES_Y3_3X2PT",
    "CMB_LENSING",
    "SH0ES",
    "CCHP_TRGB_JAGB",
    "TDCOSMO",
    "SIRENS_GW170817",
    "INVERSE_LADDER",
)


@dataclass(frozen=True)
class ProbeData:
    """Internal representation for one normalized probe data product."""

    key: str
    data_vector: np.ndarray
    covariance: np.ndarray
    bins: dict[str, Any]
    scale_cuts: dict[str, Any]
    route: str | None
    source: str
    access: str
    aor_status: str
    sha256: dict[str, str]
    metadata: dict[str, Any] = field(default_factory=dict)
    integrity: dict[str, Any] = field(default_factory=dict)


def load_dataset_from_manifest(manifest_path: Path, *, verify_raw: bool = True) -> ProbeData:
    """Load a dataset by validating and honoring its tracked manifest."""
    manifest_file = _resolve_repo_path(manifest_path)
    manifest = json.loads(manifest_file.read_text(encoding="utf-8"))

    verified: dict[str, str] = {}
    if verify_raw:
        for raw_file in manifest.get("raw_files", ()):
            verified.update(_verify_manifest_file(raw_file))

    processed = manifest["processed"]
    metadata = _load_metadata(processed.get("metadata"), verified)

    if processed["data_vector"].get("path") == "native_clik":
        data_vector = np.empty((0,), dtype=np.float64)
        covariance = np.empty((0, 0), dtype=np.float64)
        integrity = {
            "native_likelihood": True,
            "covariance_applicable": False,
            "finite": True,
            "symmetric": None,
            "lambda_min": None,
            "condition_number": None,
            "chol_success": None,
        }
    else:
        data_vector = _load_array_product(processed["data_vector"], verified)
        covariance = _load_array_product(processed["covariance"], verified)
        integrity = covariance_diagnostics(covariance)
        if not integrity["finite"]:
            raise ValueError(f"{manifest['dataset']} covariance/data contain non-finite values")
        if not integrity["symmetric"]:
            raise ValueError(f"{manifest['dataset']} covariance is not symmetric")
        if not integrity["chol_success"]:
            raise ValueError(f"{manifest['dataset']} covariance is not positive definite")
        if integrity["condition_number"] >= 1.0e8:
            raise ValueError(f"{manifest['dataset']} covariance condition number exceeds 1e8")

    bins = metadata.get("bins", manifest.get("bins", {}))
    scale_cuts = metadata.get("scale_cuts", manifest.get("scale_cuts", {}))
    return ProbeData(
        key=manifest["dataset"],
        data_vector=data_vector,
        covariance=covariance,
        bins=bins,
        scale_cuts=scale_cuts,
        route=manifest.get("route"),
        source=manifest.get("release", ""),
        access=manifest.get("access", ""),
        aor_status=manifest.get("aor_status", ""),
        sha256=verified,
        metadata=metadata,
        integrity=integrity,
    )


def load_desi_dr2_bao() -> ProbeData:
    """Load the DESI DR2 compressed BAO data vector and covariance."""
    return load_dataset_from_manifest(_manifest("desi_dr2_bao.json"))


def load_planck_2018(*, verify_payload: bool = True) -> ProbeData:
    """Load Planck 2018 native likelihood metadata and verify installed payloads."""
    return load_dataset_from_manifest(_manifest("planck_2018.json"), verify_raw=verify_payload)


def load_pantheon_plus(z_min: float = 0.01) -> ProbeData:
    """Load Pantheon+ distances with the default low-redshift cut."""
    probe = load_dataset_from_manifest(_manifest("pantheon_plus.json"))
    return _apply_redshift_cut(probe, z_min=z_min)


def load_union3() -> ProbeData:
    """Load the Union3 binned SN distance-modulus data vector and covariance."""
    return load_dataset_from_manifest(_manifest("union3.json"))


def load_des_sn5yr() -> ProbeData:
    """Load DES-SN5YR distance moduli and covariance."""
    return load_dataset_from_manifest(_manifest("des_sn5yr.json"))


def covariance_diagnostics(covariance: np.ndarray) -> dict[str, Any]:
    """Return finite/symmetry/PD/conditioning diagnostics for a covariance."""
    covariance = np.asarray(covariance, dtype=np.float64)
    finite = bool(np.all(np.isfinite(covariance)))
    symmetric = bool(covariance.ndim == 2 and np.allclose(covariance, covariance.T, rtol=0.0, atol=1e-10))
    if not finite or not symmetric:
        return {
            "native_likelihood": False,
            "covariance_applicable": True,
            "finite": finite,
            "symmetric": symmetric,
            "lambda_min": None,
            "condition_number": None,
            "chol_success": False,
        }

    eigenvalues = np.linalg.eigvalsh(covariance)
    lambda_min = float(eigenvalues[0])
    lambda_max = float(eigenvalues[-1])
    condition_number = float(lambda_max / lambda_min) if lambda_min > 0.0 else float("inf")
    try:
        np.linalg.cholesky(covariance)
        chol_success = True
    except np.linalg.LinAlgError:
        chol_success = False

    return {
        "native_likelihood": False,
        "covariance_applicable": True,
        "finite": finite,
        "symmetric": symmetric,
        "lambda_min": lambda_min,
        "condition_number": condition_number,
        "chol_success": chol_success,
    }


def _apply_redshift_cut(probe: ProbeData, *, z_min: float) -> ProbeData:
    redshifts = np.asarray(probe.bins.get("z_cmb", probe.bins.get("z", ())), dtype=np.float64)
    if redshifts.shape != probe.data_vector.shape:
        raise ValueError(f"{probe.key} redshift bins do not match the data vector")
    mask = redshifts >= z_min
    data_vector = probe.data_vector[mask]
    covariance = probe.covariance[np.ix_(mask, mask)]
    bins = _slice_bins(probe.bins, mask)
    scale_cuts = dict(probe.scale_cuts)
    scale_cuts.update({"z_min": float(z_min), "n_after_z_min": int(mask.sum())})
    return replace(
        probe,
        data_vector=data_vector,
        covariance=covariance,
        bins=bins,
        scale_cuts=scale_cuts,
        integrity=covariance_diagnostics(covariance),
    )


def _slice_bins(bins: dict[str, Any], mask: np.ndarray) -> dict[str, Any]:
    sliced: dict[str, Any] = {}
    n = int(mask.shape[0])
    for key, value in bins.items():
        if isinstance(value, list) and len(value) == n:
            sliced[key] = np.asarray(value, dtype=object)[mask].tolist()
        else:
            sliced[key] = value
    return sliced


def _load_array_product(entry: dict[str, Any], verified: dict[str, str]) -> np.ndarray:
    path = _resolve_repo_path(Path(entry["path"]))
    _verify_file(path, entry, verified)
    return np.load(path)


def _load_metadata(entry: dict[str, Any] | None, verified: dict[str, str]) -> dict[str, Any]:
    if not entry:
        return {}
    path = _resolve_repo_path(Path(entry["path"]))
    _verify_file(path, entry, verified)
    return json.loads(path.read_text(encoding="utf-8"))


def _verify_manifest_file(entry: dict[str, Any]) -> dict[str, str]:
    path = _resolve_repo_path(Path(entry["path"]))
    verified: dict[str, str] = {}
    _verify_file(path, entry, verified)
    if entry.get("kind") == "file_index":
        index = json.loads(path.read_text(encoding="utf-8"))
        for item in index.get("files", ()):
            item_path = _resolve_repo_path(Path(item["path"]))
            _verify_file(item_path, item, verified)
    return verified


def _verify_file(path: Path, entry: dict[str, Any], verified: dict[str, str]) -> None:
    if not path.is_file():
        raise FileNotFoundError(path)
    digest = sha256_file(path)
    expected = entry.get("sha256")
    if expected and expected != digest:
        raise ValueError(f"sha256 mismatch for {path}: expected {expected}, got {digest}")
    expected_size = entry.get("bytes")
    if isinstance(expected_size, int) and expected_size != path.stat().st_size:
        raise ValueError(f"size mismatch for {path}: expected {expected_size}, got {path.stat().st_size}")
    verified[str(path)] = digest


def _manifest(name: str) -> Path:
    return _repo_root() / "data" / "manifests" / name


def _resolve_repo_path(path: Path) -> Path:
    return path if path.is_absolute() else _repo_root() / path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]
