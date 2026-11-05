#!/usr/bin/env python3
"""Independent normalized-caller attachment to the frozen physical adapter.

The base adapter is used only after checking the new caller identity and its
two inherited representative bounds. No producer or numerical code is loaded.
"""
if not __debug__:
    raise RuntimeError('Representative-root exact replay rejects optimized Python.')

from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent/'strict_011_full_root_v2'
SYMMETRY = HERE.parent/'full_mask_symmetries_v1'
BASE_BINDING = '68fc9bdf42eae978da0a49acc003333a7c658a7fde90b91182ef93d2986891cb'
SYMMETRY_BINDING = '19ae3cdfae702f93bc426bb7dd619ce91a487a7806ebaddc59674ec7031274fe'
BASE_ROOT = 'e11fe83de71455d05ab58bcc12625050c1d37ef1aac4df5d2069299e566782a2'
BASE_ADAPTER = 'de6942227f66cf3f6b979595af06ac5e794b903a5ce158d8b4c3e82e35ab4be7'
SYMMETRY_CHECKER = '75c1cea019ca2aa0b09e259b29746ab3f22eab22ec238e590e7701fabacc4e41'
SYMMETRY_MAP = '5276b865fa7cde499927fba30989fbfb2319b0dcba20cc997a7c76edb748cf22'
IDENTITY = 'full-strict-01100-representative-root-v1'

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def dependency_hashes():
    answer = {}
    for folder, expected in ((BASE, BASE_BINDING), (SYMMETRY, SYMMETRY_BINDING)):
        binding = folder/'PREMISE_BINDINGS.json'
        assert digest(binding) == expected
        answer[str(binding)] = expected
        for name, entry in json.loads(binding.read_text())['local_files'].items():
            path = (folder/name).resolve()
            assert path.is_relative_to(folder) and path.is_file()
            assert path.stat().st_size == entry['bytes'] and digest(path) == entry['sha256']
            answer[str(path)] = entry['sha256']
    assert answer[str(BASE/'snapshots/ROOT_DOCUMENT.json')] == BASE_ROOT
    assert answer[str(BASE/'independent_strict_011_adapter.py')] == BASE_ADAPTER
    assert answer[str(SYMMETRY/'check_full_mask_symmetries.py')] == SYMMETRY_CHECKER
    assert answer[str(SYMMETRY/'full_mask_symmetry_maps.py')] == SYMMETRY_MAP
    return answer

def load(name, path, expected):
    assert digest(path) == expected
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

_FROZEN = dependency_hashes()
B = load('representative011_frozen_independent_base', BASE/'independent_strict_011_adapter.py', BASE_ADAPTER)
_SYMMETRY_AUDIT = None

def verify_whole_caller_symmetry():
    """Fresh exact polynomial proof on first root replay, cached within this run."""
    global _SYMMETRY_AUDIT
    assert dependency_hashes() == _FROZEN
    if _SYMMETRY_AUDIT is None:
        C = load('representative011_independent_symmetry_controls',
                 SYMMETRY/'check_full_mask_symmetries.py', SYMMETRY_CHECKER)
        assert Path(C.M.__file__).resolve() == SYMMETRY/'full_mask_symmetry_maps.py'
        assert digest(C.M.__file__) == SYMMETRY_MAP
        counts = {}
        for reflect in (False, True):
            for swap in (False, True):
                counts[f'{int(reflect)}{int(swap)}'] = C.check_transformation(reflect, swap)
        assert sum(x['owned_support_literals'] for x in counts.values()) == 4608
        assert all(x['mask_predicate_bijections'] == 32 for x in counts.values())
        _SYMMETRY_AUDIT = dict(status='PASS_FRESH_WHOLE_CALLER_SYMMETRY_POLYNOMIAL_IDENTITY',
            maps=4, counts=counts, symmetry_binding_sha256=SYMMETRY_BINDING,
            complete_target='all nine physical squares, 36 corners, 36 pairs, five exact mask links',
            strict_radius_preserved=True, shared_zero_faces_retained=True)
    assert dependency_hashes() == _FROZEN
    return deepcopy(_SYMMETRY_AUDIT)

def as_base(state):
    assert state['id'] == IDENTITY
    result = deepcopy(state)
    result['id'] = B.IDENTITY
    return result

def as_representative(state):
    assert state['id'] == B.IDENTITY
    result = deepcopy(state)
    result['id'] = IDENTITY
    return result

state_view, choices, analytic = B.state_view, B.choices, B.analytic

def expected_initial_state():
    state = as_representative(B.expected_initial_state())
    state['angles'] = tuple((F(0), F(1)) if i == 3 else (F(-1), F(1)) for i in range(9))
    state['differences'] = {(7, 8): ((F(0), F(91, 30)), (F(-91, 30), F(91, 30)))}
    validate_state(state)
    return state

def validate_state(state):
    B.validate_state(as_base(state))
    assert state['angles'][3][0] >= 0
    assert (7, 8) in state['differences'] and state['differences'][7, 8][0][0] >= 0
    return True

def verify_root(document):
    verify_whole_caller_symmetry()
    assert document['schema'] == 'full_strict_01100_representative_root_v1'
    assert document['status'] == 'IMPLEMENTED_REPRESENTATIVE_ROOT_REVIEW_REQUIRED_NO_CLOSURE'
    assert document['original_id'] == IDENTITY
    assert document['extra_normalizations'] == [
        'whole_caller_vertical_reflection_to_beta_D_nonnegative',
        'whole_caller_H_I_permutation_to_x_H_not_above_x_I']
    assert document['normalization_equivalence'] == dict(
        scope='Existence equivalence of the entire strict nine-square exact-mask caller',
        base_root_document_sha256=BASE_ROOT, symmetry_binding_sha256=SYMMETRY_BINDING,
        maps=['identity', 'vertical_reflection', 'swap_H_I', 'vertical_reflection_and_swap_H_I'],
        representatives=['beta_D >= 0', 'x_H <= x_I'],
        equality_faces_retained=True, all_32_exact_masks_preserved=True,
        proof_record_transport_claimed=False, registered_cell_transport_claimed=False)
    assert document['initial'] == state_view(expected_initial_state())
    # Removing only the explicitly proved representative layer must recover
    # the entire exact original caller, including all inventory and bits.
    original = deepcopy(document)
    original.pop('normalization_equivalence')
    original.update(schema='full_strict_01100_physical_root_v2',
        status='IMPLEMENTED_INDEPENDENT_REVIEW_REQUIRED_NO_CLOSURE', original_id=B.IDENTITY,
        initial=state_view(B.expected_initial_state()), extra_normalizations=[])
    assert B.verify_root(original) == B.expected_initial_state()
    assert original == json.loads((BASE/'snapshots/ROOT_DOCUMENT.json').read_text())
    return expected_initial_state()

class Adapter:
    choices = staticmethod(choices)
    analytic = staticmethod(analytic)
    infer_angles = staticmethod(B.Adapter.infer_angles)

    @staticmethod
    def rebuild(state, printed_rows):
        validate_state(state)
        rows, bounds, propagated = B.Adapter.rebuild(as_base(state), printed_rows)
        current = as_representative(propagated)
        validate_state(current)
        return rows, bounds, current

    @staticmethod
    def verify_early_terminal(state, terminal):
        validate_state(state)
        return B.Adapter.verify_early_terminal(as_base(state), terminal)

def angle_child(parent, original, cut, side):
    validate_state(parent)
    child = as_representative(B.angle_child(as_base(parent), original, cut, side))
    validate_state(child)
    return child
