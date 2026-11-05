"""Inspect the installed forwarding path and HiGHS option values; never solve."""
from pathlib import Path
from hashlib import sha256
import argparse
import ast
import json
import os

for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    assert os.environ.get(key)=='1'
import scipy
import scipy.optimize._linprog_highs as L
from scipy.optimize._highspy import _core as H
import scipy.optimize._highspy._highs_wrapper as W

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('output',type=Path);a=p.parse_args()
    high_source=Path(L.__file__);wrapper_source=Path(W.__file__)
    text=high_source.read_text()
    assert 'options.update(unknown_options)' in text
    assert 'These will be passed to HiGHS verbatim.' in text
    body=wrapper_source.read_text()
    assert 'for key, val in options.items():' in body
    assert 'setattr(highs_options, key, val)' in body
    assert 'highs.passOptions(highs_options)' in body
    solver=H._Highs()
    options=H.HighsOptions()
    values=dict(threads=1,time_limit=2.0,primal_feasibility_tolerance=1e-9,dual_feasibility_tolerance=1e-9)
    audits={}
    for name,value in values.items():
        status,message=W.check_option(solver,name,value)
        assert status==0,(name,status,message)
        setattr(options,name,value)
        audits[name]=dict(requested=value,wrapper_validation_status=int(status))
    accepted=solver.passOptions(options)
    assert accepted==H.HighsStatus.kOk
    readback=solver.getOptions()
    for name,value in values.items():
        assert getattr(readback,name)==value
        audits[name]['read_back']=getattr(readback,name)
    # Inspect this control's own syntax to make the absence of a solve call
    # explicit; creating/configuring a backend is not an optimization run.
    own=ast.parse(Path(__file__).read_text())
    assert not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)
                   and n.func.attr in {'run','solve','linprog','_highs_wrapper'} for n in ast.walk(own))
    report=dict(status='PASS_INSTALLED_HIGHS_OPTION_FORWARDING_AND_READBACK_NO_SOLVE',
        scipy_version=scipy.__version__,option_validation=audits,
        pass_options_status=str(accepted),warnings_suppressed=False,
        expected_visible_warning='SciPy reports threads as an unrecognized front-end option and passes it verbatim; HiGHS validates and applies it.',
        actual_optimization_function_called=False,
        source_sha256={str(x):digest(x) for x in (Path(__file__).resolve(),high_source,wrapper_source)})
    with a.output.open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps(report))

if __name__=='__main__':main()
