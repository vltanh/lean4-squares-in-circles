#!/usr/bin/env python3
"""Separate representative strict011 root; unchanged physical row producer.

This is a whole-caller existence reduction, not two new unconditional rows
for the unnormalized root or a registered original cell.
"""
if not __debug__:
    raise RuntimeError('Representative-root construction requires assertions.')

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
PRODUCER_SHA = '1912ce1b92f721127957158af83c30655ecc32a8f7a98e46fc801e327a936494'
ROOT_ID = 'full-strict-01100-representative-root-v1'

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

for folder, expected in ((BASE, BASE_BINDING), (SYMMETRY, SYMMETRY_BINDING)):
    assert digest(folder/'PREMISE_BINDINGS.json') == expected
    for rel, entry in json.loads((folder/'PREMISE_BINDINGS.json').read_text())['local_files'].items():
        path = (folder/rel).resolve()
        assert path.is_relative_to(folder) and path.stat().st_size == entry['bytes']
        assert digest(path) == entry['sha256']
assert digest(BASE/'snapshots/ROOT_DOCUMENT.json') == BASE_ROOT
assert digest(BASE/'strict_011_root.py') == PRODUCER_SHA
spec = importlib.util.spec_from_file_location('representative011_base_producer', BASE/'strict_011_root.py')
P = importlib.util.module_from_spec(spec)
spec.loader.exec_module(P)

Q, RHO = P.Q, P.RHO
state_view, choices, analytic, infer_angles = P.state_view, P.choices, P.analytic, P.infer_angles

def to_base(state):
    assert state['id'] == ROOT_ID
    value = deepcopy(state)
    value['id'] = P.ROOT_ID
    return value

def from_base(state):
    assert state['id'] == P.ROOT_ID
    value = deepcopy(state)
    value['id'] = ROOT_ID
    return value

def validate_state(state):
    P.validate_state(to_base(state))
    assert F(0) <= state['angles'][3][0]
    assert (7, 8) in state['differences']
    assert F(0) <= state['differences'][7, 8][0][0]
    return True

def fresh_state():
    state = from_base(P.fresh_state())
    angles = list(state['angles']); angles[3] = (F(0), F(1))
    state['angles'] = tuple(angles)
    state['differences'] = {(7, 8): ((F(0), 2*RHO), (-2*RHO, 2*RHO))}
    validate_state(state)
    return state

def equivalence_document():
    return dict(scope='Existence equivalence of the entire strict nine-square exact-mask caller',
        base_root_document_sha256=BASE_ROOT, symmetry_binding_sha256=SYMMETRY_BINDING,
        maps=['identity', 'vertical_reflection', 'swap_H_I', 'vertical_reflection_and_swap_H_I'],
        representatives=['beta_D >= 0', 'x_H <= x_I'],
        equality_faces_retained=True, all_32_exact_masks_preserved=True,
        proof_record_transport_claimed=False, registered_cell_transport_claimed=False)

def root_document():
    doc = P.root_document()
    doc.update(schema='full_strict_01100_representative_root_v1',
        status='IMPLEMENTED_REPRESENTATIVE_ROOT_REVIEW_REQUIRED_NO_CLOSURE',
        original_id=ROOT_ID, initial=state_view(fresh_state()),
        extra_normalizations=['whole_caller_vertical_reflection_to_beta_D_nonnegative',
                              'whole_caller_H_I_permutation_to_x_H_not_above_x_I'],
        normalization_equivalence=equivalence_document())
    return doc

def parse_state(value):
    assert value['id'] == ROOT_ID
    base = deepcopy(value); base['id'] = P.ROOT_ID
    state = from_base(P.parse_state(base))
    validate_state(state)
    return state

def collect(state):
    validate_state(state)
    rows, bounds, propagated, terminal = P.collect(to_base(state))
    if propagated is not None:
        propagated = from_base(propagated)
        validate_state(propagated)
    return rows, bounds, propagated, terminal

def physical_child(parent, kind, pair, choice):
    validate_state(parent)
    child = from_base(P.physical_child(to_base(parent), kind, pair, choice))
    validate_state(child)
    return child

def angle_child(parent, original, cut, side):
    validate_state(parent)
    child = from_base(P.angle_child(to_base(parent), original, cut, side))
    validate_state(child)
    return child

class Context:
    collect = staticmethod(collect)
    child = staticmethod(lambda state, pair, choice: physical_child(state, 'sat', pair, choice))
    proxy_child = staticmethod(lambda state, pair, choice: physical_child(state, 'proxy', pair, choice))
    angle_child = staticmethod(angle_child)
    analytic = staticmethod(analytic)
    infer_angles = staticmethod(infer_angles)
