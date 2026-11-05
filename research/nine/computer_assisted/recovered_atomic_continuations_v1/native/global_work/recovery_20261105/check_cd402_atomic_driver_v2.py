#!/usr/bin/env python3
"""Exercise the actual driver's two OSError escape paths without a solver.

Only the source-bound function definitions are executed. Geometry and solver
objects are explicit stubs; these disposable fixtures are I/O tests and are
never mathematical proof records.
"""
if not __debug__:
    raise RuntimeError('The controls require assertions.')
import argparse
import ast
from copy import deepcopy
import errno
from fractions import Fraction as F
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import shutil
import sys
import time
from types import SimpleNamespace

WORK = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
DRIVER = WORK/'d_work/cd402_work/resume_cd402_whole_original_atomic_tree_v2.py'
HELPER = WORK/'ac_work/tree/atomic_json_checkpoint.py'
SEED = WORK/'d_work/cd402_work/whole_original_complete_cover_seed'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run():
    assert sha(DRIVER) == 'ec645fe5aa26d7c6dfdcbd89cc43604d4c5cec60d186f20012c66ae41632b367'
    assert sha(HELPER) == '2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3'
    assert sha(SEED/'manifest.json') == '98ceec9da017f1ec4df7177e8dc7b0fefb0e9e9faf0c52d51f0ce74a7326acc9'
    spec = importlib.util.spec_from_file_location('cd402_control_atomic_helper', HELPER)
    atomic = importlib.util.module_from_spec(spec); spec.loader.exec_module(atomic)
    original_writer = atomic.write_json
    syntax = ast.parse(DRIVER.read_text())
    definitions = ast.Module(body=[node for node in syntax.body if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))], type_ignores=[])
    assert [node.name for node in definitions.body] == ['sha','dump','main']
    compiled = compile(definitions, str(DRIVER), 'exec')
    root = HERE/'cd402_atomic_driver_control_fixtures'; root.mkdir(exist_ok=False)
    marker = root/'stub_module.py'; marker.write_text('# Explicit I/O control stub; no mathematical premise.\n')
    cap_packet = root/'stub_cap_packet'; cap_packet.mkdir()
    (cap_packet/'PREMISE_BINDINGS.json').write_text('{}\n')
    source_hashes = {str(p):sha(p) for p in (DRIVER, HELPER, SEED/'manifest.json', SEED/'node_00000.json')}
    results = []
    for label in ('primary_checkpoint_write_ENOSPC','extra_parent_bound_ENOSPC'):
        folder = root/label; folder.mkdir()
        source, output = folder/'source', folder/'output'; source.mkdir()
        manifest = json.loads((SEED/'manifest.json').read_bytes())
        if label == 'extra_parent_bound_ENOSPC':
            # Synthetic incoming restriction activates the second error handler.
            # This object is not asserted to be a physical cover.
            manifest['nodes'][0]['restriction'] = dict(kind='physical_proxy', pair=[0,1], choice=[0,1])
        (source/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
        shutil.copyfile(SEED/'node_00000.json',source/'node_00000.json')
        seed_hashes = {p.name:sha(p) for p in source.iterdir()}
        calls = []
        def state_from_view(view):
            return dict(deepcopy(view), choices=[])
        def stateview(state):
            return {k:deepcopy(v) for k,v in state.items() if k != 'choices'}
        def search_node(context,state,rounds,checkpoint):
            calls.append(rounds)
            view = stateview(state)
            record = dict(status='OPEN',initial=view,rounds=[],final=deepcopy(view))
            if label == 'primary_checkpoint_write_ENOSPC':
                checkpoint(record)
                raise AssertionError('The injected checkpoint failure was swallowed.')
            if len(calls) == 1:
                return record, deepcopy(state), []
            raise OSError(errno.ENOSPC,'injected extra-parent-bound write failure')
        def writer(path,value):
            if label == 'primary_checkpoint_write_ENOSPC' and Path(path) == output/'node_00000.json':
                raise OSError(errno.ENOSPC,'injected atomic node checkpoint failure')
            return original_writer(path,value)
        atomic.write_json = writer
        stub = lambda **kw:SimpleNamespace(__file__=str(marker),**kw)
        context = SimpleNamespace(original=lambda:None)
        namespace = dict(__file__=str(DRIVER), Path=Path,F=F,deepcopy=deepcopy,product=product,
            argparse=argparse,hashlib=hashlib,json=json,shutil=shutil,time=time,sys=sys,
            WORK=WORK,HERE=DRIVER.parent,ATOMIC_CHECKPOINT_PATH=HELPER,ATOMIC_CHECKPOINT=atomic,
            Context=lambda:context,E=SimpleNamespace(search_node=search_node),
            stateview=stateview,state_from_view=state_from_view,
            SPLIT=stub(split_choice=lambda state,point:dict(kind='complete_physical_sat',pair=[0,1])),
            SEARCH=stub(),OFCTX=stub(),OFCTX2=stub(),WARN=stub(),OF=stub(),
            CAPCTX=stub(CAP=stub(),CAP_PACKET=cap_packet),PREFLIGHT=stub(search=lambda context,state:None),
            GRAM=stub(sources=lambda:{}),ALLGUARDS=stub(sources=lambda:{}),
            ORIGINAL=stub(TARGET=manifest['id'],ORIGINAL_PATH=manifest['original_path'],source_bindings=lambda:{}))
        exec(compiled,namespace)
        argv = sys.argv
        sys.argv = [str(DRIVER),str(source),str(output),'--rounds','1','--proxy-rounds','0','--extra-existing-rounds','0']
        try:
            try:
                namespace['main']()
            except OSError as error:
                assert error.errno == errno.ENOSPC
            else:
                raise AssertionError('The driver swallowed storage failure: '+label)
        finally:
            sys.argv=argv;atomic.write_json=original_writer
        expected_calls = 1 if label == 'primary_checkpoint_write_ENOSPC' else 2
        assert len(calls) == expected_calls
        assert not list(output.glob('discovery_error_*.json'))
        assert not list(output.glob('parent_propagation_error_*.json'))
        current = json.loads((output/'manifest.json').read_text())
        assert len(current['nodes']) == 1 and current['status'] == 'OPEN'
        assert not current['nodes'][0]['children']
        assert sha(output/'node_00000.json') == current['nodes'][0]['sha256']
        if label == 'primary_checkpoint_write_ENOSPC':
            assert sha(output/'node_00000.json') == seed_hashes['node_00000.json']
        assert {p.name:sha(p) for p in source.iterdir()} == seed_hashes
        results.append(dict(case=label,search_calls=len(calls),oserror_propagated=True,
            no_error_branch_continuation=True,no_children_added=True,
            output_node_manifest_hashes_agree=True,source_fixture_unchanged=True))
    assert all(sha(path)==value for path,value in source_hashes.items())
    report=dict(status='PASS_CD402_ATOMIC_DRIVER_FAILFAST_CONTROL_FLOW',cases=results,
        source_sha256=source_hashes,control_source_sha256=sha(__file__),
        actual_driver_function_definitions_executed=True,solver_and_geometry_explicitly_stubbed=True,
        mathematical_replay_performed=False,numerical_solver_called=False,
        frozen_source_or_seed_bytes_changed=False,lost_numerical_suffix_reconstructed=False,
        new_original_credit=0,new_mask_credit=0)
    target=HERE/'CD402_ATOMIC_DRIVER_FAILFAST_CONTROLS.json'
    with target.open('x') as stream:json.dump(report,stream,indent=2);stream.write('\n')
    print(json.dumps(dict(status=report['status'],cases=len(results),report_sha256=sha(target))))


if __name__=='__main__':
    run()
