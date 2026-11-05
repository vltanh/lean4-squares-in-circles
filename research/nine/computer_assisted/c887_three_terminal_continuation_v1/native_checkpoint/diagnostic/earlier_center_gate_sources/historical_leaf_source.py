"""Exact identity reuse of the published complete C887 91-node proof.

The accepted old proof certifies every node state. Its arithmetic is not run
again here. All retained child constructors are freshly checked, and only the
specified leaf state is supplied to the new unchanged arithmetic checker.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from itertools import product
import hashlib
import importlib.util
import json
import sys

PACKET_MANIFEST_SHA = '06115f494173bc344821932525d7a8522df8ea2ed80b400f735f3b68d4a1b58b'
PACKET_BINDING_SHA = 'e7706717cc9136d2327b2a76a65f5824dad385743757f860863a50d5373b6c10'
TRANSPORT_SHA = 'd7d9b17da9091cb7920e5964618303c93ae2689a8528381091b35f3ee4c2cb28'
REPORT_SHA = 'ec915e7153afab3fe1b674992f251dccde51e7901602db368c3530f08b278a08'
TREE_SHA = 'a091ad6716ef688cf001857a70f5058acfbb9601a87818de1edb4db4fa9bbe49'
NODE_SHA = '50a0583c3a925681c291fb9c2f56b64ba8f2ae482ef5994fd041d4aeb499edff'
ANCESTOR_SHA = '9a5c4af1e23964ee661e4e1ae427265a29303b2a6f6bd5a65c5ece14177040a3'
CORE_SHA = 'a96a5ea5890553a7db6a0d22fb6245ec5b9b98851d5afc039d154989aab21301'
CENTER_SHA = '9fafd523e0154fcb8aedb7ecf2f36aa6213a77c84ff619ae12cd5612fc1b2acc'
CENTER_BINDING_SHA = '8fb0b5dda2d0bb892236dac5825bec3c8824d4ba6f1440aee967c9b5aa1e1a82'
TARGET = 'negative-887236b78100baf3'
ORIGINAL_PATH = [['angle', 3, 0], ['angle_cut', [0, '0'], 1],
                 ['alternate_four_escape', [1, 7], [1]]]
REPORT_REL = 'payload/ac_work/tree/C887_FIRST_WEIGHTED_SHARED_HEIGHT_BOUNDS_REPLAY.json'
TREE_REL = 'payload/ac_work/tree/c887_first_weighted_shared_height_path'
PKG_REL = 'payload/ac_work/c887/c887_whole_eight_checkpoint_package'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def verify_gate_sources(here):
    if not __debug__:
        raise RuntimeError('Exact source assertions must be enabled')
    freeze = read(here / 'SOURCE_BINDING.json')
    assert freeze['schema'] == 'C887_direct_center_leaf_gate_sources_v1'
    for name, digest in freeze['files'].items():
        p = here / name
        assert p.resolve().is_relative_to(here.resolve()) and sha(p) == digest, name
    binding = read(here / 'center_family/BINDING.json')
    assert sha(here / 'center_family/BINDING.json') == CENTER_BINDING_SHA
    assert binding['status'] == 'PUBLISHED_PHYSICAL_AND_ACTUAL_WEIGHTED_USE_GATE_ACCEPTED'
    assert binding['squared_radius'] == '1105/256' and binding['center_radius_enclosure'] == '91/60'
    for name, digest in binding['files'].items():
        assert sha(here / 'center_family' / name) == digest
    assert sha(here / 'center_family/independent_physical_center_disk_rows.py') == CENTER_SHA
    return freeze


def validate_historical_proof(packet):
    assert sha(packet / 'INPUT_MANIFEST.json') == PACKET_MANIFEST_SHA
    assert sha(packet / 'BINDINGS.json') == PACKET_BINDING_SHA
    assert sha(packet / 'replay_portable_c_height_packet_v3.py') == TRANSPORT_SHA
    inventory = read(packet / 'INPUT_MANIFEST.json')['files']
    bindings = read(packet / 'BINDINGS.json')
    assert inventory[REPORT_REL] == REPORT_SHA and sha(packet / REPORT_REL) == REPORT_SHA
    assert inventory[TREE_REL + '/manifest.json'] == TREE_SHA
    assert sha(packet / TREE_REL / 'manifest.json') == TREE_SHA
    report = read(packet / REPORT_REL)
    assert report['status'] == 'PASS_PARTIAL_WHOLE_ORIGINAL_C887_COVER'
    assert report['original_id'] == TARGET and report['original_path'] == ORIGINAL_PATH
    assert report['original_mask'] == '001/00'
    assert report['all_nine_original_squares_retained'] is True
    assert report['original_corner_predicates'] == report['original_pair_predicates'] == 36
    assert report['closed_shared_faces_retained'] is True
    assert report['new_original_cells'] == report['new_masks'] == 0
    assert report['numerical_discovery_fields_used'] is report['numerical_producer_imported'] is False
    assert tuple(report[k] for k in ('nodes', 'leaf_domains', 'excluded_leaf_domains', 'rounds',
        'deductions', 'printed_rows_checked', 'complete_proxy_covers', 'complete_sat_covers',
        'closed_angle_covers')) == (91, 73, 0, 57, 8780, 39146, 9, 6, 3)
    assert report['ancestor_replay']['certificate_sha256'] == ANCESTOR_SHA
    inputs = {}

    def gather(value):
        if isinstance(value, list):
            for item in value:
                gather(item)
        elif isinstance(value, dict):
            for key, item in value.items():
                if key in ('input_sha256', 'checker_dependency_sha256', 'source_sha256') and isinstance(item, dict):
                    for path, digest in item.items():
                        if isinstance(digest, str) and len(digest) == 64:
                            assert path not in inputs or inputs[path] == digest
                            inputs[path] = digest
                gather(item)

    gather(report)
    assert len(inputs) == 543
    resolved = {}
    for path, digest in inputs.items():
        if path.startswith('opposite_tilt_theorem/'):
            relative = PKG_REL + '/' + path
        else:
            entry = bindings['files'][path]
            assert entry['sha256'] == digest
            relative = entry['path']
        assert inventory[relative] == digest and sha(packet / relative) == digest, path
        resolved[path] = dict(path=relative, sha256=digest)
    manifest = read(packet / TREE_REL / 'manifest.json')
    assert manifest['id'] == TARGET and manifest['original_path'] == ORIGINAL_PATH
    assert manifest['parent']['sha256'] == ANCESTOR_SHA
    assert manifest['status'] == 'OPEN' and manifest['new_original_cells'] == manifest['new_masks'] == 0
    entries = {}; records = {}
    for entry in manifest['nodes']:
        index = entry['index']
        assert type(index) is int and index >= 0 and index not in entries
        assert entry['file'] == f'node_{index:05d}.json'
        relative = TREE_REL + '/' + entry['file']
        p = packet / relative
        assert inventory[relative] == entry['sha256'] == sha(p)
        record = read(p)
        assert record['id'] == TARGET and record['original_path'] == ORIGINAL_PATH
        assert record['status'] == 'OPEN' and 'terminal' not in record
        assert record['final']['id'] == TARGET
        assert record['final']['path'][:len(ORIGINAL_PATH)] == ORIGINAL_PATH
        entries[index] = entry; records[index] = record
    assert len(entries) == len(records) == 91
    assert entries[0]['parent'] is None and entries[0]['depth'] == 0 and entries[0]['restriction'] is None
    assert records[0]['initial']['path'] == ORIGINAL_PATH
    assert entries[47]['sha256'] == NODE_SHA and entries[47]['children'] == []
    assert entries[47]['parent'] == 45 and entries[47]['depth'] == 18
    assert entries[47]['restriction'] == dict(kind='closed_angle', owner=4, cut='0', side=1)
    assert records[47]['rounds'] == [] and records[47]['initial'] == records[47]['final']
    assert F(records[47]['final']['positions'][8][1]) == F(-123053, 131072)
    assert F(records[47]['final']['positions'][9][1]) == F(168199132771425, 140737488355328)
    audited = {a['index']: a for a in report['audits']}
    assert set(audited) == set(entries)
    for index, entry in entries.items():
        audit = audited[index]
        assert audit['status'] == 'PASS_CERTIFIED_PHYSICAL_STATE_OPEN'
        assert audit['parent'] == entry['parent'] and audit['depth'] == entry['depth']
        assert audit['restriction'] == entry['restriction']
        assert audit['rounds'] == len(records[index]['rounds'])
    return report, manifest, entries, records, resolved


def restore_state(view, adapter, core):
    result = deepcopy(view)
    for key in ('angles', 'positions', 'scalar'):
        result[key] = tuple(tuple(map(F, interval)) for interval in view[key])
    for key in ('differences', 'diagonal'):
        result[key] = {tuple(row['pair']): tuple(tuple(map(F, interval)) for interval in row['intervals'])
                       for row in view[key]}
    result['choices'] = adapter.choices(result['path'])
    core.valid_state(result)
    assert core.state_view(result) == view
    return result


def validate_complete_parent_paths(entries, records, adapter, core, original):
    visited = set(); covers = []; lineage = []

    def visit(index):
        assert index not in visited; visited.add(index)
        entry = entries[index]; children = entry['children']
        assert isinstance(children, list) and len(children) == len(set(children))
        if not children:
            assert entry['status'] == 'OPEN' and 'split' not in entry
            return
        assert entry['complete_children'] is True and entry['status'] == 'OPEN'
        state = restore_state(records[index]['final'], adapter, core)
        split = entry['split']; kind = split['kind']
        if kind == 'complete_physical_proxy':
            pair = tuple(split['pair'])
            original.PROXY.check_choices([entries[k]['restriction']['choice'] for k in children])
            assert len(children) == 4
        elif kind == 'complete_physical_sat':
            pair = tuple(split['pair'])
            actual = [tuple(entries[k]['restriction']['choice']) for k in children]
            assert len(actual) == len(set(actual)) == 8
            assert set(actual) == set(product(pair, (0, 1), (-1, 1)))
        else:
            assert kind == 'closed_angle_bisection' and len(children) == 2
            assert sorted(entries[k]['restriction']['side'] for k in children) == [0, 1]
        for child in children:
            ce = entries[child]; restriction = ce['restriction']
            assert ce['parent'] == index and ce['depth'] == entry['depth'] + 1
            if kind == 'complete_physical_proxy':
                assert set(restriction) == {'kind', 'pair', 'choice'}
                assert restriction['kind'] == 'physical_proxy' and restriction['pair'] == list(pair)
                expected = original.PROXY.proxy_child(state, pair, restriction['choice'], adapter)
            elif kind == 'complete_physical_sat':
                assert set(restriction) == {'kind', 'pair', 'choice'}
                assert restriction['kind'] == 'physical_sat' and restriction['pair'] == list(pair)
                expected = core.sat_child(state, pair, restriction['choice'], adapter)
            else:
                assert set(restriction) == {'kind', 'owner', 'cut', 'side'}
                assert restriction['kind'] == 'closed_angle'
                assert restriction['owner'] == split['owner'] and F(restriction['cut']) == F(split['cut'])
                expected = original.angle_child(state, restriction['owner'], restriction['cut'], restriction['side'], adapter)
            assert core.state_view(expected) == records[child]['initial'], child
            visit(child)
        covers.append(dict(parent=index, kind=kind, children=children, all_closed_alternatives_checked=True))

    visit(0)
    assert visited == set(entries) and len(covers) == 18
    cursor = 47
    while cursor is not None:
        lineage.append(cursor); cursor = entries[cursor]['parent']
    lineage.reverse()
    assert len(lineage) == 19 and lineage[0] == 0 and lineage[-1] == 47
    return covers, lineage


def setup(packet, output, here):
    packet = Path(packet).resolve(); output = Path(output).resolve(); here = Path(here).resolve()
    verify_gate_sources(here)
    historical, manifest, entries, records, inputs = validate_historical_proof(packet)
    assert not output.exists()
    spec = importlib.util.spec_from_file_location('unchanged_c_portable_transport', packet / 'replay_portable_c_height_packet_v3.py')
    transport = importlib.util.module_from_spec(spec); spec.loader.exec_module(transport)
    inventory, aliases, locate, output_aliases = transport.install(packet, output)
    import verify_c887_ownerfree_physical_tree as original
    core = original.SAT
    assert sha(core.__file__) == CORE_SHA
    spec = importlib.util.spec_from_file_location('independent_center_for_c887_leaf', here / 'center_family/independent_physical_center_disk_rows.py')
    center = importlib.util.module_from_spec(spec); spec.loader.exec_module(center)
    checker = original.Checker()
    base_adapter = original.Adapter(checker)
    covers, lineage = validate_complete_parent_paths(entries, records, base_adapter, core, original)
    initial = restore_state(records[47]['final'], base_adapter, core)
    exact_path = deepcopy(initial['path'])

    class Adapter(original.Adapter):
        def rebuild(self, state, printed):
            assert state['id'] == TARGET and state['path'] == exact_path
            ordinary = [r for r in printed if not r['name'].startswith(center.PREFIX)]
            rows, bounds, propagated = super().rebuild(state, ordinary)
            assert self.K.V.Q == F(1105, 256)
            assert self.K.V.EDGES == ((0, 1, 0), (1, 2, 0), (2, 3, 1), (4, 5, 0), (5, 6, 0))
            for row in printed:
                if not row['name'].startswith(center.PREFIX):
                    continue
                literal = (tuple((i, F(v)) for i, v in row['coefficients']), F(row['rhs']), row['name'])
                center.verify_literal(literal)
                assert row['index'] not in rows
                rows[row['index']] = literal
            return rows, bounds, propagated

    adapter = Adapter(checker)
    evidence = dict(status='PASS_REUSED_PUBLISHED_COMPLETE_C887_PROOF_IDENTITIES_AND_FRESH_PARENT_PATHS',
        packet_manifest_sha256=PACKET_MANIFEST_SHA, packet_binding_sha256=PACKET_BINDING_SHA,
        published_consumer_report_sha256=REPORT_SHA, tree_manifest_sha256=TREE_SHA,
        leaf_node_sha256=NODE_SHA, original_id=TARGET, original_path=ORIGINAL_PATH,
        leaf_index=47, full_leaf_path=exact_path, lineage=lineage, complete_retained_covers=covers,
        historical_report_input_pins=inputs, historical_report_inputs_rehashed=len(inputs),
        historical_nodes_rehashed=91, historical_bound_arithmetic_repeated=False,
        original_source_and_parent_proof_reused_from_published_complete_report=True,
        raw_saved_intervals_alone_used_as_authority=False, all_91_parent_child_states_reconstructed=True,
        old_packet_bytes_unchanged=True, mathematical_scope='ONLY_THE_CERTIFIED_C887_LEAF_47_DOMAIN',
        new_original_cells=0, new_masks=0)
    return core, adapter, initial, evidence, inventory, transport


def recheck(packet, here, inventory):
    for name, digest in inventory.items():
        assert sha(Path(packet) / name) == digest, name
    verify_gate_sources(Path(here))
    assert not any(name in sys.modules for name in ('numpy', 'scipy', 'highspy',
        'physical_sat_engine_snapshot', 'physical_sat_diagonal_engine', 'ac_physical_context'))
