from pathlib import Path

def hoist(raw: bytes) -> bytes:
    lines=raw.splitlines(keepends=True)
    imports=[line for line in lines if line.startswith(b"import ")]
    assert all(line.endswith(b"\n") for line in imports)
    return b"".join(imports)+b"".join(line for line in lines if not line.startswith(b"import "))
