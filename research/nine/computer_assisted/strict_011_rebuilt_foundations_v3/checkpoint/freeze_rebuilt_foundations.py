"""Freeze freshly regenerated controls and repin the unchanged tree algorithm."""
from pathlib import Path
from hashlib import sha256
import ast
import difflib
import json

HERE = Path(__file__).resolve().parent

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True); f.write('\n')

origin = HERE/'SOURCE_RECONSTRUCTION.json'
assert digest(origin) == 'cfaad88a7008187f0ee857f027aac428a6ec1d7ff19364cc01ce74d061b6a5d6'
restored = json.loads(origin.read_text())
for rel, entry in restored['source_files'].items():
    p = HERE/rel
    assert p.stat().st_size == entry['bytes'] and digest(p) == entry['sha256']

model = HERE/'strict_011_full_root_v2'
model_report = json.loads((model/'FRESH_ROOT_CONTROLS.json').read_text())
assert model_report['status'] == 'PASS_FRESH_STRICT011_ROOT_LITERAL_AND_COVER_CONTROLS'
assert model_report['root_necessary_rows'] == 1757
assert model_report['whole_mask_credit'] == model_report['whole_original_credit'] == 0
assert model_report['conditional_terminal_installed'] is False
assert model_report['complete_open_covers'] == {'sat_unions':36, 'proxy_unions':36, 'angle_unions':9}
for path, expected in model_report['source_sha256'].items():
    assert digest(path) == expected

sym = HERE/'full_mask_symmetries_v1'
sym_report = json.loads((sym/'FRESH_SYMMETRY_CONTROLS.json').read_text())
assert sym_report['status'] == 'PASS_FULL_CALLER_SYMMETRY_POLYNOMIAL_CONTROLS'
assert sym_report['all_32_exact_masks_preserved'] is True
assert sym_report['rational_normalization_assignments'] == 200
assert sym_report['whole_mask_credit'] == 0
for path, expected in sym_report['source_sha256'].items():
    assert digest(path) == expected

def package_binding(folder, schema, scope):
    files = {}
    for path in sorted(folder.rglob('*')):
        if path.is_file():
            assert not path.is_symlink() and path.suffix in ('.py', '.md', '.json')
            files[str(path.relative_to(folder))] = dict(sha256=digest(path), bytes=path.stat().st_size)
    binding = dict(schema=schema, scope=scope, local_files=files,
        reconstruction_source_sha256=digest(origin),
        fresh_generated_json=True, recovered_lost_json_claimed=False,
        numerical_solver_called=False, original_cell_credit=0, whole_mask_credit=0)
    write(folder/'PREMISE_BINDINGS.json', binding)
    return digest(folder/'PREMISE_BINDINGS.json')

model_hash = package_binding(model, 'rebuilt_full_strict011_model_binding_v3',
    'Exact preserved v2 mathematical sources, newly generated full unnormalized root and controls; no closure.')
sym_hash = package_binding(sym, 'rebuilt_full_caller_symmetry_binding_v2',
    'Exact preserved whole-caller symmetry sources with newly generated polynomial controls; no normalized root installed by this packet.')

old = HERE/'preserved_sources/strict_011_complete_cover_v1'
new = HERE/'strict_011_complete_cover_v2'
new.mkdir(exist_ok=False)
old_binding = '6e8612b3da867ec5c16488ac4d129e578245f0e642dd46edb1bfc6f258f7e0cf'
before = (old/'verify_strict_011_complete_tree.py').read_text()
assert before.count(old_binding) == 1
after = before.replace(old_binding, model_hash)

def normalized(source):
    tree = ast.parse(source)
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(t,ast.Name) and t.id == 'MODEL_BINDING' for t in node.targets):
            node.value = ast.Constant('NEWLY_GENERATED_MODEL_BINDING')
    return ast.dump(tree, include_attributes=False)

assert normalized(before) == normalized(after)
for source in sorted(old.iterdir()):
    assert source.is_file() and not source.is_symlink()
    data = after.encode() if source.name == 'verify_strict_011_complete_tree.py' else source.read_bytes()
    with (new/source.name).open('xb') as f:
        f.write(data)
diff = ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
    fromfile='preserved_complete_cover_v1.py', tofile='repinned_complete_cover_v2.py'))
with (new/'MODEL_BINDING_REPIN.diff').open('x') as f:
    f.write(diff)
record = dict(status='PASS_EXACT_MODEL_AND_SYMMETRY_REGENERATION_AND_BINDING_ONLY_WRAPPER_REPIN',
    source_reconstruction_sha256=digest(origin), model_binding_sha256=model_hash,
    symmetry_binding_sha256=sym_hash, old_lost_model_binding_sha256=old_binding,
    original_wrapper_sha256=digest(old/'verify_strict_011_complete_tree.py'),
    new_wrapper_sha256=digest(new/'verify_strict_011_complete_tree.py'),
    difference_sha256=digest(new/'MODEL_BINDING_REPIN.diff'),
    normalized_AST_equal_after_model_binding_only=True,
    model_math_sources_byte_identical=True, symmetry_math_sources_byte_identical=True,
    source_script_sha256=digest(Path(__file__)),
    actual_observed_root_control_exit=0, actual_observed_symmetry_control_exit=0,
    no_lost_proof_suffix_reconstruction=True, whole_mask_credit=0, original_cell_credit=0)
write(HERE/'FRESH_FOUNDATION_RECONSTRUCTION.json', record)
print(json.dumps(record))
