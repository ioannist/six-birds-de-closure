"""Verify every saved source file in one sequential pass through the archive."""
import argparse
import hashlib
import json
import tarfile
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(archive, expected):
    before = sha(archive)
    seen = set()
    with tarfile.open(archive, "r|gz") as stream:
        for member in stream:
            assert member.isfile() and member.name not in seen, member.name
            assert member.name in expected, member.name
            digest = hashlib.sha256()
            with stream.extractfile(member) as source:
                while chunk := source.read(1 << 20):
                    digest.update(chunk)
            assert digest.hexdigest() == expected[member.name], member.name
            seen.add(member.name)
    assert seen == set(expected)
    assert sha(archive) == before
    return {"archive_sha256": before, "files": len(seen),
            "sequential_hash_verification": True,
            "scope": "Saved source-byte identity only; not a Lean build or proof-completion judgment."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=Path(__file__).with_name("sources.tar.gz"))
    parser.add_argument("--expected", type=Path, default=Path(__file__).with_name("status.json"))
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    data = json.loads(args.expected.read_text())
    expected = data.get("files", data)
    result = verify(args.archive, expected)
    if args.receipt:
        assert not args.receipt.exists(), args.receipt
        args.receipt.write_text(json.dumps(result, indent=2)+"\n")
    print("Sequential archive verification passed:", result["files"], "files.")


if __name__ == "__main__":
    main()
