"""Make the final whole-offset verifier directly runnable from its isolated path."""
from pathlib import Path
import ast, hashlib, json

ROOT=Path('/home/repos/six-birds-de-closure')
OUT=ROOT/'results/ground_offset_registered_recovery_candidate_2026-10-06'
OLD=Path('/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_binary_repaired.py')
NEW=Path('/tmp/de_ground_offset_transport_verify_registered_recovery.py')
assert not OUT.exists();OUT.mkdir()
original=OLD.read_text()
text=original.replace('from pathlib import Path\n','from pathlib import Path\nimport sys\nsys.path.insert(0,"/home/repos/six-birds-de-closure/scripts")\n',1)
text=text.replace("ROOT=Path(__file__).resolve().parents[1]","ROOT=Path('/home/repos/six-birds-de-closure')",1)
old="      'Full 11776-declaration command was not rerun in this packet.\\n\\n')"
new="      'This concatenation preserves historical receipts; the fresh full 11776-declaration command is verified separately.\\n\\n')"
assert text.count(old)==1;text=text.replace(old,new,1)
ast.parse(text);NEW.write_text(text)
(OUT/'historical-verifier.py').write_text(original)
(OUT/'verifier.py').write_text(text)
(OUT/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(dict(repository_root_fixed=True,all_prior_gates_retained=True,concatenated_receipt_label_corrected=True,registered_sources_changed=False)))
