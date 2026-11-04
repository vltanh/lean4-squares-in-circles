#!/usr/bin/env python3
"""Replay unchanged exact complete-A1 sources with manifest-bound path transport only.

Every isolated child installs the same transport and audit restrictions. No
certificate, row, multiplier, endpoint, predicate or checker byte is rewritten.
"""
from pathlib import Path
import argparse, builtins, hashlib, json, os, pathlib, runpy, subprocess, sys, tempfile, time, types

REAL_PATH = type(Path())
REAL_IMPORT = builtins.__import__
REAL_POPEN = subprocess.Popen
TARGETS = ('positive-c744bc031d40ee64',)
FORBIDDEN = ('numpy', 'scipy', 'highspy', 'physical_sat_engine_snapshot',
             'physical_sat_diagonal_engine', 'ac_physical_context',
             'v3_whole_parent_pass', 'active_highs', 'active_highs_checked_warning_snapshot')


def sha(path):
    return hashlib.sha256(REAL_PATH(path).read_bytes()).hexdigest()


def dump(path, value):
    REAL_PATH(path).write_text(json.dumps(value, indent=2) + '\n')


def install(packet, output):
    packet, output = REAL_PATH(packet).resolve(), REAL_PATH(output).resolve()
    manifest_path = packet / 'INPUT_MANIFEST.json'
    inventory = json.loads(manifest_path.read_text())['files']
    for name, digest in inventory.items():
        target = (packet / name).resolve()
        assert target.is_relative_to(packet) and sha(target) == digest, ('changed packet input', name)
    binding = json.loads((packet / 'BINDINGS.json').read_text())
    aliases = {}
    for old, entry in binding['files'].items():
        target = (packet / entry['path']).resolve()
        assert target.is_relative_to(packet) and sha(target) == entry['sha256']
        assert inventory[entry['path']] == entry['sha256']
        aliases[old] = str(target)
    for old, relative in binding['directories'].items():
        target = (packet / relative).resolve()
        assert target.is_relative_to(packet) and target.is_dir()
        assert old not in aliases
        aliases[old] = str(target)
    output.mkdir(parents=True, exist_ok=True)
    temporary = output / 'temporary'
    temporary.mkdir(exist_ok=True)
    tempfile.tempdir = str(temporary)
    os.chdir(output)
    # Unchanged archived checkers write diagnostic replay reports beside their
    # sources. These exact, non-input report names are transported into output.
    # This is output routing only: every packet mutation remains forbidden.
    report_folders = {'verify_joint_original.py': 'new_reviews',
                      'verify_diagonal_pass.py': 'diagonal_replay_reports',
                      'verify_arc_union.py': 'replay_reports'}
    output_aliases = {}
    for name in inventory:
        source = packet / name
        if source.name not in report_folders:
            continue
        old_folder = source.parent / report_folders[source.name]
        assert not any((packet / item).is_relative_to(old_folder) for item in inventory)
        tag = hashlib.sha256(name.encode()).hexdigest()[:24]
        target_folder = output / 'archived_diagnostic_reports' / tag
        target_folder.mkdir(parents=True, exist_ok=True)
        output_aliases[str(old_folder)] = str(target_folder)
        for original in TARGETS:
            output_aliases[str(old_folder / (original + '.json'))] = str(target_folder / (original + '.json'))
    assert len(output_aliases) == len(set(output_aliases.values()))

    class TransportPath(REAL_PATH):
        """Exact filenames/directories only; all other path semantics unchanged."""
        def __new__(cls, *parts, **kwargs):
            candidate = REAL_PATH(*parts, **kwargs)
            mapped = aliases.get(str(candidate), str(candidate))
            mapped = output_aliases.get(mapped, mapped)
            return REAL_PATH.__new__(cls, mapped)

        def __init__(self, *parts, **kwargs):
            # Python 3.12 moved path-part initialization from __new__ to
            # __init__; support both layouts without touching pathlib itself.
            if sys.version_info >= (3, 12):
                candidate = REAL_PATH(*parts, **kwargs)
                mapped = aliases.get(str(candidate), str(candidate))
                mapped = output_aliases.get(mapped, mapped)
                REAL_PATH.__init__(self, mapped)

    facade = types.ModuleType('pathlib')
    facade.__dict__.update(pathlib.__dict__)
    facade.Path = TransportPath

    # Frozen checkers compare manifest reference strings with their relocated
    # __file__-relative names. Relocate only exact inventory-bound path strings;
    # no numeric, predicate, label, index or mathematical data is transformed.
    assert len(set(aliases.values())) == len(aliases), 'Path aliases must be injective.'
    def relocate_references(value):
        if isinstance(value, str):
            return aliases.get(value, value)
        if isinstance(value, list):
            return [relocate_references(item) for item in value]
        if isinstance(value, dict):
            answer = {aliases.get(key, key) if key in binding['files'] else key:
                      relocate_references(item) for key, item in value.items()}
            assert len(answer) == len(value), 'Path transport collision.'
            return answer
        return value

    json_facade = types.ModuleType('json')
    json_facade.__dict__.update(json.__dict__)
    def relocated_loads(*args, **kwargs):
        return relocate_references(json.loads(*args, **kwargs))
    def relocated_load(*args, **kwargs):
        return relocate_references(json.load(*args, **kwargs))
    json_facade.loads = relocated_loads
    json_facade.load = relocated_load

    def restricted_import(name, globals=None, locals=None, fromlist=(), level=0):
        assert name.split('.')[0] not in FORBIDDEN, ('numerical import forbidden', name)
        module = REAL_IMPORT(name, globals, locals, fromlist, level)
        if level == 0 and name == 'pathlib':
            return facade
        if level == 0 and name == 'json':
            return json_facade
        return module

    def locate(value):
        return aliases.get(str(value), str(value))

    input_paths = {(packet / name).resolve() for name in inventory}
    input_paths.add(manifest_path)
    def normalized(value):
        path = REAL_PATH(os.fsdecode(value))
        if not path.is_absolute():
            path = REAL_PATH.cwd() / path
        logical = REAL_PATH(os.path.abspath(str(path)))
        return logical, REAL_PATH(os.path.realpath(logical))

    def audit(event, values):
        if event == 'open' and isinstance(values[0], (str, bytes)):
            logical, actual = normalized(values[0])
            mode = values[1] or ''
            flags = values[2]
            writing = any(letter in mode for letter in 'wax+') or bool(
                flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND))
            if logical.is_relative_to(packet) or actual.is_relative_to(packet):
                assert not writing, ('frozen packet write forbidden', str(logical))
                assert logical.is_relative_to(packet) and actual.is_relative_to(packet), (
                    'packet symlink or alias escape', str(logical), str(actual))
                assert actual in input_paths, ('unlisted packet read forbidden', str(actual))
            elif logical.is_relative_to(output):
                assert actual.is_relative_to(output), ('output symlink escape', str(logical), str(actual))
            elif str(logical).startswith('/workspace/') or str(actual).startswith('/workspace/'):
                raise AssertionError(('external workspace access forbidden', str(logical), str(actual)))
        elif event in ('os.remove', 'os.rmdir', 'os.mkdir', 'os.rename', 'os.link',
                       'os.symlink', 'os.chmod', 'os.utime', 'os.truncate', 'os.chown'):
            count = 2 if event in ('os.rename', 'os.link', 'os.symlink') else 1
            for value in values[:count]:
                if isinstance(value, (str, bytes)):
                    logical, actual = normalized(value)
                    assert not (logical.is_relative_to(packet) or actual.is_relative_to(packet)), (
                        'frozen packet mutation forbidden', event, str(logical))
        elif event == 'import':
            assert values[0].split('.')[0] not in FORBIDDEN, ('numerical import forbidden', values[0])
        elif event == 'exec':
            filename = values[0].co_filename
            if isinstance(filename, str) and filename.startswith(str(packet) + '/'):
                logical, actual = normalized(filename)
                assert logical.is_relative_to(packet) and actual.is_relative_to(packet)
                assert actual in input_paths, ('unlisted proof code forbidden', filename)

    worker = packet / 'replay_portable_a1_checkpoint_v1.py'
    def wrapped_popen(command, *args, **kwargs):
        assert isinstance(command, (list, tuple)) and command[0] == sys.executable
        command = list(command)
        position = 1
        while position < len(command) and command[position] in ('-B', '-S'):
            position += 1
        assert set(command[1:position]) == {'-B', '-S'}
        script = REAL_PATH(locate(command[position])).resolve()
        assert script.is_relative_to(packet) and str(script.relative_to(packet)) in inventory
        assert script.suffix == '.py'
        wrapped = [sys.executable, '-B', '-S', str(worker), '--packet', str(packet),
                   '--output', str(output), '--worker-script', str(script), '--',
                   *[str(x) for x in command[position + 1:]]]
        return REAL_POPEN(wrapped, *args, **kwargs)

    sys.addaudithook(audit)
    builtins.__import__ = restricted_import
    subprocess.Popen = wrapped_popen
    sys.dont_write_bytecode = True
    sys.pycache_prefix = str(output / 'bytecode_probes')
    sys.path[:] = [p for p in sys.path if not str(p).startswith('/workspace/') or
                   REAL_PATH(p).is_relative_to(packet)]
    sys.path.insert(0, str(packet / 'payload/ac_work/tree'))
    return inventory, aliases, locate, output_aliases


def run_checked(script, arguments, output, label):
    with (output / (label + '.log')).open('w') as log:
        result = subprocess.run([sys.executable, '-B', '-S', str(script), *map(str, arguments)],
                                stdout=log, stderr=subprocess.STDOUT)
    assert result.returncode == 0, ('exact child failed', label, result.returncode)



def assert_physical_scope(report, target):
    assert report['original_id'] == target
    assert report['new_original_cells'] == report['new_masks'] == 0
    assert report['closed_shared_faces_retained'] is True
    assert report['numerical_producer_imported'] is False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--worker-script', type=Path)
    parser.add_argument('--transport-controls', action='store_true')
    parser.add_argument('script_arguments', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    packet, output = args.packet.resolve(), args.output.resolve()
    started = time.monotonic()
    assert __debug__, 'Exact replay requires assertions.'
    assert packet != output and not output.is_relative_to(packet)
    # The archived sources retain their original strict /workspace audit hooks.
    # Neither a source hook nor any source byte is relaxed for relocation.
    assert not str(packet).startswith('/workspace/')
    assert not str(output).startswith('/workspace/')
    if args.worker_script is None:
        assert not output.exists(), 'Use a fresh replay output directory.'
    inventory, aliases, locate, output_aliases = install(packet, output)
    assert not (args.worker_script is not None and args.transport_controls)
    if args.worker_script is not None:
        script = REAL_PATH(locate(args.worker_script)).resolve()
        assert script.is_relative_to(packet) and str(script.relative_to(packet)) in inventory
        remaining = args.script_arguments
        if remaining[:1] == ['--']:
            remaining = remaining[1:]
        sys.argv = [str(script), *remaining]
        sys.path.insert(0, str(script.parent))
        runpy.run_path(str(script), run_name='__main__')
        receipt_kind = 'PASS_PORTABLE_ISOLATED_EXACT_A1_CHILD'
        detail = dict(script=str(script.relative_to(packet)))
    elif args.transport_controls:
        relocated_json = __import__('json')
        relocated_path = __import__('pathlib').Path
        bindings = json.loads((packet / 'BINDINGS.json').read_text())
        old_file = next(iter(bindings['files']))
        old_directory = next(iter(bindings['directories']))
        mathematical = dict(coefficients=[[1, '-1'], [7, '1']], rhs='23/100',
            name='c_original_closed_height_consequence_c887_7_binding',
            angles=[['-1', '0'], ['0', '1']], squared_radius='1105/256')
        fixture = dict(file=old_file, directory=old_directory, math=mathematical,
            unknown='/workspace/transport_control_unknown/missing.json',
            embedded='source=' + old_file, file_keys={old_file: 'literal'},
            directory_keys={old_directory: 'literal'})
        literal = json.dumps(fixture)
        moved = relocated_json.loads(literal)
        assert moved['file'] == locate(old_file)
        assert moved['directory'] == locate(old_directory)
        assert moved['math'] == mathematical
        assert moved['unknown'] == fixture['unknown']
        assert moved['embedded'] == fixture['embedded']
        assert moved['file_keys'] == {locate(old_file): 'literal'}
        assert moved['directory_keys'] == fixture['directory_keys']
        assert relocated_path(old_file).read_bytes() == REAL_PATH(locate(old_file)).read_bytes()
        report_folder = next(name for name in output_aliases if not name.endswith('.json'))
        routed_folder = relocated_path(report_folder)
        assert str(routed_folder) == output_aliases[report_folder]
        assert routed_folder.is_relative_to(output)
        report_name = report_folder + '/' + TARGETS[0] + '.json'
        routed_report = relocated_path(report_folder) / (TARGETS[0] + '.json')
        assert str(routed_report) == output_aliases[report_name]
        routed_report.write_text('diagnostic output control\n')
        assert routed_report.read_text() == 'diagnostic output control\n'
        assert not REAL_PATH(report_name).exists()
        blocked = []
        operations = (
            ('external_original_file', lambda: REAL_PATH(old_file).read_bytes()),
            ('unknown_workspace_path', lambda: relocated_path(fixture['unknown']).read_bytes()),
            ('unlisted_packet_file', lambda: REAL_PATH(packet / 'DELTA_MANIFEST.json').read_bytes()),
            ('frozen_input_write', lambda: REAL_PATH(packet / 'PUBLICATION_PROOF.json').open('w')),
            ('frozen_packet_new_file', lambda: REAL_PATH(packet / 'UNLISTED_NEW_FILE').open('w')),
            ('frozen_packet_unlink', lambda: REAL_PATH(packet / 'PUBLICATION_PROOF.json').unlink()),
            ('frozen_packet_rename', lambda: (packet / 'PUBLICATION_PROOF.json').rename(output / 'moved_input.json')),
            ('frozen_packet_directory', lambda: (packet / 'NEW_DIRECTORY').mkdir()),
            ('frozen_packet_symlink', lambda: (packet / 'NEW_SYMLINK').symlink_to('/tmp')),
            ('numerical_import', lambda: __import__('numpy')),
        )
        for label, operation in operations:
            try:
                operation()
            except AssertionError:
                blocked.append(label)
            else:
                raise AssertionError(('transport negative control accepted', label))
        assert len(blocked) == len(operations)
        for destination in ('/tmp', '/workspace'):
            escape = output / ('ESCAPE_' + destination.strip('/'))
            escape.symlink_to(destination, target_is_directory=True)
            try:
                try:
                    (escape / 'UNBOUND_CONTROL').open('rb')
                except AssertionError as error:
                    assert 'output symlink escape' in str(error)
                    blocked.append('resolved_output_symlink_to_' + destination.strip('/'))
                else:
                    raise AssertionError('Resolved output escape was accepted.')
            finally:
                escape.unlink()
        assert sys.dont_write_bytecode is True and sys.pycache_prefix == str(output / 'bytecode_probes')
        receipt_kind = 'PASS_A1_PORTABLE_EXACT_PATH_TRANSPORT_CONTROLS'
        detail = dict(exact_reference_controls=11, rejected_controls=blocked,
            dictionary_keys_transformed_only_for_explicit_file_aliases=True,
            mathematical_string_literals_unchanged=True,
            unknown_and_embedded_path_literals_unchanged=True,
            raw_input_bytes_and_hash_semantics_unchanged=True,
            new_original_cells=0, new_masks=0)
    else:
        proof = json.loads((packet / 'PUBLICATION_PROOF.json').read_text())
        assert proof['schema'] == 'complete_A1_original_consequence_portable_proof_v1'
        assert proof['original_id'] == TARGETS[0]
        assert proof['original_status'] == 'OPEN' and proof['component1_status'] == 'CLOSED'
        assert proof['new_original_cells'] == proof['new_masks'] == 0
        assert proof['all_nine_original_squares_retained'] is True
        assert proof['original_corner_predicates'] == proof['original_pair_predicates'] == 36
        assert proof['mask'] == '001/00' and proof['closed_shared_faces_retained'] is True
        reference = json.loads(REAL_PATH(locate(proof['reference_binding']['path'])).read_text())
        assert sha(locate(proof['reference_binding']['path'])) == proof['reference_binding']['sha256']
        assert reference['original_cell']['id'] == TARGETS[0]
        assert reference['original_cell']['path'] == proof['original_path']
        assert reference['original_cell']['status'] == 'OPEN'
        code = packet / 'payload/ac_work/tree'
        report_path = output / 'A3_ACTUAL_COMPLETE_A1_CONSEQUENCE_REPLAY.json'
        # This consumer first invokes the older A1 checker in a separate
        # guarded process. Its resulting complete source report is embedded
        # literally below, so the 757-node source arithmetic runs once here.
        run_checked(code / 'verify_a_c744_component3_a1_consequence_lazy_tree.py',
                    [locate(proof['actual_component3_probe']['folder']), report_path],
                    output, 'actual_A3_consumer_with_fresh_complete_A1_source')
        actual = json.loads(report_path.read_text())
        assert actual['status'] == 'PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE'
        assert actual['original_id'] == TARGETS[0] and actual['original_path'] == proof['original_path']
        assert actual['component'] == 3 and actual['open_leaves'] == 1
        assert actual['all_nine_originals_retained'] is True
        assert actual['mask'] == '001/00' and actual['closed_shared_faces_retained'] is True
        assert actual['numerical_producer_imported'] is False
        assert actual['new_original_cells'] == actual['new_masks'] == 0
        assert actual['node_payloads_replayed_lazily'] is True
        assert actual['completed_component1_row_scope'] == 'WHOLE_UNCHANGED_ORIGINAL_PARENT'
        assert actual['component3_shared_bounds_not_valid_on_whole_original'] is True
        for key, expected in proof['expected_actual'].items():
            assert actual[key] == expected, ('actual A3', key, actual[key], expected)
        fresh = actual['fresh_completed_component1_consequence_source']
        assert fresh['status'] == 'PASS_FRESH_COMPLETE_COMPONENT1_ORIGINAL_CONSEQUENCE'
        assert fresh['excluded_component'] == 1 and fresh['original_id'] == TARGETS[0]
        assert fresh['necessary_weak_row'] == proof['original_necessary_row']
        source_reference = fresh['source_report']
        source_path = REAL_PATH(source_reference['path']).resolve()
        assert source_path.is_relative_to(output)
        assert sha(source_path) == source_reference['sha256']
        source = json.loads(source_path.read_text())
        assert source == source_reference['report']
        assert source['status'] == 'PASS_COMPLETE_TWO_LINK_COMPLEMENT_TREE'
        assert source['original_id'] == TARGETS[0] and source['original_path'] == proof['original_path']
        assert source['component'] == 1 and source['open_leaves'] == 0
        assert source['all_nine_originals_retained'] is True and source['closed_shared_faces_retained'] is True
        assert source['numerical_producer_imported'] is False and source['node_payloads_replayed_lazily'] is True
        assert source['new_original_cells'] == source['new_masks'] == 0
        for key, expected in proof['expected_source'].items():
            assert source[key] == expected, ('complete A1', key, source[key], expected)
        source_manifest = locate(proof['complete_component1']['folder']) + '/manifest.json'
        assert source['input_sha256'][source_manifest] == proof['complete_component1']['manifest_sha256']
        print('PORTABLE_COMPLETE_A1_AND_ACTUAL_A3_USE', proof['expected_source'], proof['expected_actual'], flush=True)
        controls_path = output / 'A1_CONSEQUENCE_LITERAL_SCOPE_CONTROLS.json'
        controls_script = packet / 'payload/ac_work/a1_consequence_prepare/check_a_c744_component1_consequence_controls.py'
        run_checked(controls_script, ['--output', controls_path], output, 'literal_scope_controls')
        controls = json.loads(controls_path.read_text())
        assert controls['status'] == 'PASS_COMPLETE_A1_CONSEQUENCE_LITERAL_AND_SCOPE_CONTROLS'
        assert controls['positive_original_and_descendant_literals'] == 4
        assert len(controls['rejected_damages']) == 17
        assert controls['necessary_original_wide_row'] == proof['original_necessary_row']
        assert controls['original_wide_producer_emits_only_one_row'] is True
        assert controls['component3_only_derived_row']['requires_exact_component3_closed_domain'] is True
        receipt_kind = 'PASS_FRESH_PORTABLE_COMPLETE_A1_CONSEQUENCE_AND_ACTUAL_A3_USE'
        detail = dict(complete_component1={**proof['expected_source'], 'report_sha256': sha(source_path)},
            actual_component3_use={**proof['expected_actual'], 'report_sha256': sha(report_path)},
            repeated_literal_scope_controls=dict(positives=4, rejected_damages=17, report_sha256=sha(controls_path)),
            original_necessary_row=proof['original_necessary_row'],
            conditional_A3_order_not_claimed_on_whole_original=True,
            fresh_complete_source_repeated_once_by_guarded_consumer=True,
            native_saved_reports_used_as_arithmetic_premises=False,
            reference_commit=reference['commit'], new_original_cells=0, new_masks=0,
            original_status='OPEN', component1_status='CLOSED', whole_original_exclusion_not_claimed=True)
    for name, digest in inventory.items():
        assert sha(packet / name) == digest, ('packet changed during replay', name)
    assert not any(name.split('.')[0] in FORBIDDEN for name in sys.modules)
    receipt = dict(status=receipt_kind, original_ids=list(TARGETS),
        packet_manifest_sha256=sha(packet / 'INPUT_MANIFEST.json'),
        input_files=len(inventory), input_bytes=sum((packet / name).stat().st_size for name in inventory),
        exact_mathematical_sources_unchanged=True, explicit_path_aliases=len(aliases),
        filesystem_reference_transport_only=True,
        frozen_archived_read_guards_unchanged=True,
        all_packet_writes_and_mutations_forbidden=True,
        logical_and_resolved_paths_checked=True,
        bytecode_probes_redirected_to_output=True,
        explicit_archived_diagnostic_output_aliases=len(output_aliases),
        archived_diagnostic_outputs_disjoint_from_inputs=True,
        external_workspace_reads_forbidden_in_every_child=True, numerical_imports_forbidden=True,
        all_inputs_rehashed_at_completion=True, lean_lake_ci_run=False,
        seconds=time.monotonic() - started, **detail)
    if args.worker_script is None:
        target = output / 'PORTABLE_RECEIPT.json'
    else:
        folder = output / 'isolated_child_receipts'
        folder.mkdir(exist_ok=True)
        target = folder / f'{os.getpid()}.json'
    dump(target, receipt)
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
