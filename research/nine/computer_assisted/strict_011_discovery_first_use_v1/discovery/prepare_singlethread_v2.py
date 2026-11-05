"""Preserve v1 and create the immutable one-option HiGHS thread-limit variant."""
from pathlib import Path
from hashlib import sha256
import ast
import difflib
import json

HERE=Path(__file__).resolve().parent
old=HERE/'fresh_strict011_discovery.py'
assert sha256(old.read_bytes()).hexdigest()=='365d87c7784b114c5c5db2c49e1b479b2079044552003343451037f7d0995783'
before=old.read_text()
needle='dual_feasibility_tolerance=1e-9)'
assert before.count(needle)==1
after=before.replace(needle,'dual_feasibility_tolerance=1e-9, threads=1)')
new=HERE/'fresh_strict011_discovery_singlethread_v2.py'
with new.open('x') as f:f.write(after)
def normalized(source):
    tree=ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='dict':
            names={k.arg for k in node.keywords}
            if {'time_limit','primal_feasibility_tolerance','dual_feasibility_tolerance'}<=names:
                node.keywords=[k for k in node.keywords if k.arg!='threads']
    return ast.dump(tree,include_attributes=False)
assert normalized(before)==normalized(after)
diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile=old.name,tofile=new.name))
with (HERE/'SINGLETHREAD_V2_FROM_V1.diff').open('x') as f:f.write(diff)
report=dict(status='PASS_SINGLE_OPTION_THREAD_LIMIT_DELTA',
    v1_sha256=sha256(old.read_bytes()).hexdigest(),v2_sha256=sha256(new.read_bytes()).hexdigest(),
    diff_sha256=sha256(diff.encode()).hexdigest(),
    whole_module_AST_equal_after_removing_only_threads_option=True,
    mathematical_certificate_and_cover_and_storage_functions_unchanged=True,
    warning_suppression_added=False,numerical_solver_called=False,
    source_script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
with (HERE/'SINGLETHREAD_V2_SOURCE_REVIEW.json').open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(report))
