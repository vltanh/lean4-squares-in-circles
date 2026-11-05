"""Freeze the new representative model and attach the unchanged cover walk."""
from pathlib import Path
from hashlib import sha256
import ast
import difflib
import json

HERE = Path(__file__).resolve().parent
MODEL = HERE/'strict_011_representative_root_v1'
OLD = HERE/'strict_011_complete_cover_v2'
NEW = HERE/'strict_011_representative_cover_v1'

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True); f.write('\n')

report = json.loads((MODEL/'FRESH_REPRESENTATIVE_CONTROLS.json').read_text())
assert report['status'] == 'PASS_REPRESENTATIVE_STRICT011_ROOT_AND_LITERAL_CONTROLS'
assert report['root_rows'] == 1757 and report['whole_mask_credit'] == 0
assert report['complete_open_covers'] == {'sat':36,'proxy':36,'angle':9}
for path, expected in report['source_sha256'].items():
    assert digest(path) == expected
files = {str(p.relative_to(MODEL)):dict(sha256=digest(p), bytes=p.stat().st_size)
         for p in sorted(MODEL.rglob('*')) if p.is_file()}
assert all(not (MODEL/p).is_symlink() for p in files)
binding = dict(schema='full_strict011_representative_root_binding_v1',
    scope='Whole-caller existence reduction with a separate new root; no complete mask exclusion.',
    local_files=files, source_dependencies=report['source_sha256'],
    base_model_binding_sha256='68fc9bdf42eae978da0a49acc003333a7c658a7fde90b91182ef93d2986891cb',
    symmetry_binding_sha256='19ae3cdfae702f93bc426bb7dd619ce91a487a7806ebaddc59674ec7031274fe',
    fresh_focused_control_exit=0, numerical_solver_called=False,
    existing_runtime_modified=False, original_cell_credit=0, whole_mask_credit=0)
write(MODEL/'PREMISE_BINDINGS.json',binding)
binding_sha = digest(MODEL/'PREMISE_BINDINGS.json')
adapter_sha = digest(MODEL/'independent_strict_011_adapter.py')
producer_sha = digest(MODEL/'representative_strict_011_root.py')
before = (OLD/'verify_strict_011_complete_tree.py').read_text()
after = before
def replace(old,new,count=1):
    global after
    assert after.count(old) == count, (old,after.count(old))
    after = after.replace(old,new)
replace("MODEL_BINDING = '68fc9bdf42eae978da0a49acc003333a7c658a7fde90b91182ef93d2986891cb'",
        "MODEL_BINDING = '"+binding_sha+"'")
replace("ADAPTER_SHA = 'de6942227f66cf3f6b979595af06ac5e794b903a5ce158d8b4c3e82e35ab4be7'",
        "ADAPTER_SHA = '"+adapter_sha+"'")
replace("    I = read_module('fresh_strict011_exact_adapter', adapter_path, ADAPTER_SHA)\n",
        "    I = read_module('representative_strict011_exact_adapter', adapter_path, ADAPTER_SHA)\n"
        "    for path, expected in I.dependency_hashes().items():\n        pin(path, expected)\n")
replace("'fresh_full_strict011_complete_tree_v1'", "'fresh_full_strict011_representative_complete_tree_v1'")
replace("'PASS_COMPLETE_STRICT011_PHYSICAL_TREE'", "'PASS_COMPLETE_STRICT011_REPRESENTATIVE_PHYSICAL_TREE'")
replace("'PASS_COMPLETE_STRICT011_COVER_WITH_OPEN_DOMAINS'", "'PASS_COMPLETE_STRICT011_REPRESENTATIVE_COVER_WITH_OPEN_DOMAINS'")
replace("root_ancestry='FRESH_FULL_CALLER'", "root_ancestry='FRESH_FULL_CALLER_MODULO_REVIEWED_WHOLE_CALLER_SYMMETRIES'")
replace("normalized_root=False, conditional_theorem_used=False,", "normalized_root=True, conditional_theorem_used=False,\n        normalization_exact_audit=I.verify_whole_caller_symmetry(),")
replace("parent.parent/'strict_011_full_root_v2'", "parent.parent/'strict_011_representative_root_v1'")
replace('No producer, optimizer, conditional theorem, or symmetry layer is imported.',
        'No producer, optimizer, or conditional terminal is imported. The source-bound\nwhole-caller symmetry identity is independently replayed by the new adapter.')

def function_ast(source,name):
    functions = [n for n in ast.walk(ast.parse(source)) if isinstance(n,ast.FunctionDef) and n.name == name]
    assert len(functions) == 1
    return ast.dump(functions[0],include_attributes=False)

unchanged = {}
for name in ('walk','local_file','digest','read_module'):
    assert function_ast(before,name) == function_ast(after,name), name
    unchanged[name] = sha256(function_ast(after,name).encode()).hexdigest()

control_before = (OLD/'check_complete_tree_controls.py').read_text()
controls = control_before
changes = [
    ("model = HERE.parent/'strict_011_full_root_v2'", "model = HERE.parent/'strict_011_representative_root_v1'",1),
    ("model/'strict_011_root.py'", "model/'representative_strict_011_root.py'",1),
    ('1912ce1b92f721127957158af83c30655ecc32a8f7a98e46fc801e327a936494',producer_sha,1),
    ("'fresh_full_strict011_complete_tree_v1'","'fresh_full_strict011_representative_complete_tree_v1'",1),
    ("cut='0'","cut='1/2'",2),
    ("P.angle_child(final_plus, 3, 0, side)","P.angle_child(final_plus, 3, F(1,2), side)",1),
    ("P.angle_child(root, 3, 0, 0)","P.angle_child(root, 3, F(1,2), 0)",1),
    ("P.angle_child(root, 3, 0, 1)","P.angle_child(root, 3, F(1,2), 1)",1),
    ("r['initial']['angles'].__setitem__(3, ['0', '1'])","r['initial']['angles'].__setitem__(3, ['1/4', '1'])",1),
    ("normalized_root_installed=False", "representative_root_fixture=True, existing_runtime_modified=False",1),
]
for old,new,count in changes:
    assert controls.count(old) == count, (old,controls.count(old))
    controls = controls.replace(old,new)
NEW.mkdir(exist_ok=False)
for name,data in [('verify_strict_011_complete_tree.py',after),('check_complete_tree_controls.py',controls)]:
    with (NEW/name).open('x') as f:
        f.write(data)
for name,a,b in [('WRAPPER_FROM_UNNORMALIZED.diff',before,after),
                 ('CONTROLS_FROM_UNNORMALIZED.diff',control_before,controls)]:
    with (NEW/name).open('x') as f:
        f.write(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),
                    fromfile='unnormalized',tofile='representative')))
record = dict(status='PREPARED_REPRESENTATIVE_COMPLETE_COVER_UNCHANGED_TRAVERSAL',
    model_binding_sha256=binding_sha,adapter_sha256=adapter_sha,producer_sha256=producer_sha,
    base_wrapper_sha256=digest(OLD/'verify_strict_011_complete_tree.py'),
    wrapper_sha256=digest(NEW/'verify_strict_011_complete_tree.py'),
    controls_sha256=digest(NEW/'check_complete_tree_controls.py'),
    unchanged_function_AST=unchanged,proof_arithmetic_sources_unchanged=True,
    complete_wrapper_controls_pending=True,numerical_solver_called=False,
    whole_mask_credit=0,original_cell_credit=0,source_script_sha256=digest(Path(__file__)))
write(NEW/'SOURCE_TRANSFORMATION.json',record)
print(json.dumps(record))
