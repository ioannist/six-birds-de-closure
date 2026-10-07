"""Standard deterministic artifact writers."""

from __future__ import annotations

import csv
import io
import json
from pathlib import Path
from typing import Any
from zipfile import ZIP_STORED, ZipFile, ZipInfo

import numpy as np


def write_json_artifact(payload: Any, path: Path) -> None:
    """Write a JSON artifact."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_table_artifact(rows: Any, path: Path) -> None:
    """Write a table artifact."""
    path.parent.mkdir(parents=True, exist_ok=True)
    rows_list = list(rows)
    if not rows_list:
        path.write_text("", encoding="utf-8")
        return
    fieldnames = list(rows_list[0].keys())
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows_list:
            writer.writerow(row)


def write_npz_artifact(path: Path, **arrays: Any) -> None:
    """Write a bitwise-reproducible NPZ file with fixed ZIP metadata."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("wb") as handle:
        with ZipFile(handle, mode="w", compression=ZIP_STORED) as archive:
            for name in sorted(arrays):
                buffer = io.BytesIO()
                np.lib.format.write_array(buffer, np.asarray(arrays[name]), allow_pickle=False)
                info = ZipInfo(f"{name}.npy", date_time=(1980, 1, 1, 0, 0, 0))
                info.compress_type = ZIP_STORED
                archive.writestr(info, buffer.getvalue())
