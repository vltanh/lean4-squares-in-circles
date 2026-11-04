"""Replay unchanged D821 mathematics with manifest-bound filename aliases.

No predicate, coefficient, multiplier, interval, row checker, or complete
assembler byte is rewritten. Reads from the historical workspace are blocked.
"""
from pathlib import Path
import argparse
import builtins
import hashlib
import importlib.util
import json
import os
import pathlib
import runpy
import sys
import time
import types

REAL_PATH = type(Path())
REAL_IMPORT = builtins.__import__
REAL_SPEC = importlib.util.spec_from_file_location
TARGET = 'positive-821c9a2debeed0aa'
FORBIDDEN = {
    'numpy','scipy','highspy','physical_sat_engine_snapshot',
    'physical_sat_diagonal_engine','d_runtime','d_physical_sat','d_physical_sat_tight',
    'active_highs','active_highs_checked_warning_snapshot',
    'd821_runtime','d821_complement_runtime','d821_gram_runtime',
    'd821_ownerfree_gram_runtime','d821_safe_ownerfree_runtime',
    'd821_either_extra_runtime','d821_corner_runtime','d821_unit_corner_runtime',
    'd821_four_corner_runtime','d821_consequence_runtime',
}


def sha(path):
    return hashlib.sha256(REAL_PATH(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--controls-only', action='store_true')
    args = parser.parse_args()
    assert __debug__, 'Exact replay requires assertions.'
    started = time.monotonic()
    packet, output = args.packet.resolve(), args.output.resolve()
    assert packet != output and not output.is_relative_to(packet)
    assert not output.exists(), 'Use a fresh output directory.'
    manifest_path = packet/'INPUT_MANIFEST.json'
    assert manifest_path.resolve().is_relative_to(packet)
    assert REAL_PATH(__file__).resolve()==packet/'replay_portable_d821_packet.py'
    manifest_hash = sha(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    assert manifest['schema'] == 'D821_portable_frozen_inputs_v1'
    assert manifest['external_workspace_reads_forbidden'] is True
    assert manifest['numerical_imports_forbidden'] is True
    assert manifest['unchanged_strict_complete_original_assembler_required'] is True
    inventory = manifest['files']
    def check_packet_input(name, digest):
        path=(packet/name).resolve()
        assert path.is_relative_to(packet), ('packet input escapes packet', name)
        assert sha(path)==digest, ('changed input', name)
        return path
    allowed_packet_reads={manifest_path.resolve()}
    for name, digest in inventory.items():
        allowed_packet_reads.add(check_packet_input(name,digest))
    binding = json.loads((packet/'BINDINGS.json').read_text())
    aliases = {}
    for old, entry in binding['files'].items():
        path = (packet/entry['path']).resolve()
        assert path.is_relative_to(packet)
        assert inventory[entry['path']] == entry['sha256'] and sha(path) == entry['sha256']
        aliases[old] = str(path)
    for old, relative in binding['directories'].items():
        path = (packet/relative).resolve()
        assert path.is_relative_to(packet) and path.is_dir()
        assert old not in aliases
        aliases[old] = str(path)
    proof = json.loads((packet/'ORIGINAL_PROOF.json').read_text())
    assert proof['schema'] == 'D821_portable_unchanged_proof_inputs_v1'
    assert proof['original_id'] == TARGET and proof['mask'] == '001/00'
    assert proof['original_frames'] == 9 and proof['original_corners'] == proof['original_pairs'] == 36
    assert proof['original_actual_links'] == ['AB','BC','EF','FG']
    assert proof['original_strict_weak_links'] == ['CD']
    assert proof['mathematical_sources_unchanged'] is True
    assert proof['aliases_are_filename_transport_only'] is True
    output.mkdir(parents=True)
    os.chdir(output)

    class TransportPath(REAL_PATH):
        """Keep historical path identities; redirect only file access.

        Frozen continuation records compare literal historical filenames.
        Changing their string representation would change those identity
        comparisons.  The aliases therefore affect reads/stat only.
        """
        def _physical(self):
            return REAL_PATH(aliases.get(str(self), str(self)))

        def open(self, *args, **kwargs):
            return self._physical().open(*args, **kwargs)

        def stat(self, *args, **kwargs):
            return self._physical().stat(*args, **kwargs)

        def resolve(self, strict=False):
            logical = os.path.abspath(str(self))
            if logical in aliases:
                if strict:
                    REAL_PATH(aliases[logical]).resolve(strict=True)
                return type(self)(logical)
            return type(self)(REAL_PATH(self).resolve(strict=strict))

    facade = types.ModuleType('pathlib')
    facade.__dict__.update(pathlib.__dict__)
    facade.Path = TransportPath

    def restricted_import(name, globals=None, locals=None, fromlist=(), level=0):
        assert name.split('.')[0] not in FORBIDDEN, ('numerical import forbidden', name)
        result = REAL_IMPORT(name, globals, locals, fromlist, level)
        return facade if name == 'pathlib' and level == 0 else result

    def audit(event, values):
        def normalized(value):
            path=REAL_PATH(os.fsdecode(value))
            if not path.is_absolute():
                path=REAL_PATH.cwd()/path
            logical=REAL_PATH(os.path.abspath(str(path)))
            return logical,logical.resolve()
        if event == 'open' and isinstance(values[0], (str, bytes)):
            logical,actual=normalized(values[0])
            mode=values[1]if len(values)>1 else None
            flags=values[2]if len(values)>2 else 0
            writing=(isinstance(mode,str)and any(c in mode for c in 'wax+'))or(
                isinstance(flags,int)and bool(flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)))
            if logical.is_relative_to(packet)or actual.is_relative_to(packet):
                assert not writing, ('frozen packet write forbidden',str(logical))
                assert logical.is_relative_to(packet)and actual.is_relative_to(packet), (
                    'packet symlink or alias escape',str(logical),str(actual))
                assert actual in allowed_packet_reads, ('unlisted packet read forbidden',str(actual))
            elif logical.is_relative_to(output):
                assert actual.is_relative_to(output), ('output symlink escape',str(logical),str(actual))
            elif str(logical).startswith('/workspace/')or str(actual).startswith('/workspace/'):
                raise AssertionError(('external workspace read forbidden',str(logical),str(actual)))
        elif event in ('os.remove','os.rmdir','os.mkdir','os.rename','os.link','os.symlink','os.chmod','os.utime','os.truncate'):
            count=2 if event in ('os.rename','os.link','os.symlink')else 1
            for value in values[:count]:
                if isinstance(value,(str,bytes)):
                    logical,actual=normalized(value)
                    assert not(logical.is_relative_to(packet)or actual.is_relative_to(packet)), (
                        'frozen packet mutation forbidden',event,str(logical))
        elif event == 'import':
            assert values[0].split('.')[0] not in FORBIDDEN, ('numerical import forbidden', values[0])
        elif event in ('subprocess.Popen','os.system'):
            raise AssertionError('The D821 exact replay must not launch external programs.')

    sys.addaudithook(audit)
    builtins.__import__ = restricted_import
    def transported_spec(name, location, *positional, **keywords):
        # The unchanged scalar theorem loads its independent checker by a
        # historical filename. Transport that exact module location only.
        if location is not None:
            location=aliases.get(os.fspath(location), os.fspath(location))
        return REAL_SPEC(name, location, *positional, **keywords)
    importlib.util.spec_from_file_location=transported_spec
    sys.dont_write_bytecode = True
    # Import machinery may probe a nonexistent .pyc before reading source.
    # Keep such probes in the fresh output directory, away from frozen inputs.
    sys.pycache_prefix=str(output/'bytecode_probes')
    sys.path[:] = [p for p in sys.path if not str(p).startswith('/workspace/') or
                   REAL_PATH(p).is_relative_to(packet)]
    code = packet/'payload/global_work/d821_work'
    sys.path.insert(0, str(code))
    if args.controls_only:
        rejected=[]
        def reject(label,operation,reason):
            try:
                result=operation()
                if hasattr(result,'close'):
                    result.close()
            except AssertionError as error:
                assert reason in str(error), (label,str(error))
                rejected.append(label)
            else:
                raise AssertionError(('damaged transport control accepted',label))
        reject('external workspace read',lambda:REAL_PATH('/workspace/D821_UNBOUND_CONTROL').open('rb'),
               'external workspace read forbidden')
        reject('unlisted packet read',lambda:(packet/'D821_UNLISTED_CONTROL').open('rb'),
               'unlisted packet read forbidden')
        escape=output/'D821_ESCAPE_CONTROL'
        escape.symlink_to('/workspace',target_is_directory=True)
        try:
            reject('resolved output symlink escape',lambda:(escape/'D821_UNBOUND_CONTROL').open('rb'),
                   'output symlink escape')
        finally:
            escape.unlink()
        reject('frozen input write',lambda:(packet/'BINDINGS.json').open('ab'),
               'frozen packet write forbidden')
        reject('numerical import',lambda:__import__('numpy'),'numerical import forbidden')
        reject('bad input hash',lambda:check_packet_input('BINDINGS.json','0'*64),'changed input')
        missing=proof['theorem_binding']['path']
        old=aliases.pop(missing)
        try:
            reject('missing exact filename alias',lambda:TransportPath(missing).open('rb'),
                   'external workspace read forbidden')
        finally:
            aliases[missing]=old
        assert str(TransportPath(missing).resolve())==missing
        assert sha(TransportPath(missing)._physical())==proof['theorem_binding']['sha256']
        report_path=output/'TRANSPORT_CONTROLS.json'
        control=dict(status='PASS_D821_PORTABLE_TRANSPORT_CONTROLS',rejected=rejected,
                     historical_filename_identity_preserved=True,exact_alias_bytes_verified=True,
                     mathematical_checker_executed=False,new_original_cells=0,new_masks=0)
        report_path.write_text(json.dumps(control,indent=2)+'\n')
        status=control['status']
        detail=dict(transport_controls=control,new_original_cells=0,new_masks=0,
                    whole_original_coverage_not_claimed=True)
    elif proof['mode'] == 'OPEN_TREE_PROTOTYPE':
        from verify_D821_complete_original import theorem
        scalar_theorem=theorem(proof['theorem_binding'])
        assert scalar_theorem['fresh_scalar_domains']==28
        assert scalar_theorem['fresh_scalar_leaves']==103
        assert scalar_theorem['fresh_scalar_coefficients']==12875
        selected = REAL_PATH(aliases[proof['selected_tree']])
        assert sha(selected) == proof['selected_tree_sha256']
        report_path = output/'PROTOTYPE_TREE_REPLAY.json'
        script = code/'verify_d821_consequence_tree.py'
        sys.argv = [str(script), str(selected), str(report_path)]
        runpy.run_path(str(script), run_name='__main__')
        replay = json.loads(report_path.read_text())
        tree = replay['tree_report']
        assert tree['component'] == proof['selected_component']
        assert tree['nodes'] == proof['expected_nodes']
        assert tree['status'] in ('PASS_PARTIAL_PHYSICAL_TREE','PASS_COMPLETE_PHYSICAL_TREE')
        status = 'PASS_FRESH_PORTABLE_D821_TREE_PROTOTYPE'
        detail = dict(component=tree['component'], nodes=tree['nodes'], open_leaves=tree['open_leaves'],
                      accepted_scalar_theorem=scalar_theorem,
                      new_original_cells=0, new_masks=0, whole_original_coverage_not_claimed=True)
    else:
        assert proof['mode'] == 'COMPLETE_ORIGINAL'
        selected = REAL_PATH(aliases[proof['complete_plan']])
        assert sha(selected) == proof['complete_plan_sha256']
        report_path = output/'COMPLETE_ORIGINAL_REPLAY.json'
        script = code/'verify_D821_grafted_original.py'
        sys.argv = [str(script), str(selected), str(report_path)]
        runpy.run_path(str(script), run_name='__main__')
        replay = json.loads(report_path.read_text())
        assert replay['status'] == 'PASS_COMPLETE_ORIGINAL_CELL'
        assert replay['original_id'] == TARGET and replay['whole_original_proved'] is True
        assert replay['complete_closed_complement_domains'] == 5
        assert replay['all_nine_original_frames'] is True
        assert replay['original_corners'] == replay['original_physical_pairs'] == 36
        status = 'PASS_FRESH_PORTABLE_COMPLETE_ORIGINAL_D821'
        detail = dict(new_original_cells=1, new_masks=0, whole_original_coverage_not_claimed=False)
    for name, digest in inventory.items():
        assert sha(packet/name) == digest, ('packet changed during replay', name)
    assert sha(manifest_path) == manifest_hash
    assert not any(name.split('.')[0] in FORBIDDEN for name in sys.modules)
    receipt = dict(status=status, original_id=TARGET,
        packet_manifest_sha256=manifest_hash, exact_report_sha256=sha(report_path),
        input_files=len(inventory), input_bytes=sum((packet/name).stat().st_size for name in inventory),
        explicit_filename_aliases=len(binding['files']), explicit_directory_aliases=len(binding['directories']),
        exact_mathematical_sources_unchanged=True, external_workspace_reads_forbidden=True,
        numerical_imports_forbidden=True, all_inputs_rehashed_at_completion=True,
        lean_lake_ci_run=False, seconds=time.monotonic()-started, **detail)
    (output/'PORTABLE_RECEIPT.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
