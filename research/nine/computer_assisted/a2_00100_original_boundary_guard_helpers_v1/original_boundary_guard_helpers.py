"""Portable source-bound validators for two existing strict-original terminals.

The consumer must independently reconstruct the full registered original
physical caller and supply its independently propagated state and geometry.
This module never attaches an original state, checks a cover, or grants cell
credit. Sharp-row and deep-cylinder uses are separate and must be reported
under their actual terminal kinds. No producer is imported by this module.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import importlib.util
import json
import sys
import independent_original_deep_boundary_terminal as DEEP
HERE = Path(__file__).resolve().parent
SHARP = HERE / "sharp_boundary"
SHARP_BINDINGS_SHA = "af92173feb7b2be3f2da561454cfda34e53e97c7f31ec9e1dd4e6709f6a38dc6"
SHARP_DECODER_SHA = "7adfa5221e9908b0806936e63e733ef7881ffabe5a3135093aeb19d83af61242"
_sharp_module = None


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_bindings():
    answer = DEEP.source_bindings()
    answer[str(Path(__file__).resolve())] = sha(__file__)
    manifest = SHARP / "SOURCE_BINDINGS.json"
    assert sha(manifest) == SHARP_BINDINGS_SHA
    answer[str(manifest)] = SHARP_BINDINGS_SHA
    bindings = json.loads(manifest.read_text())
    assert bindings["schema"] == "unchanged_original_sharp_boundary_reusable_sources_v1"
    assert bindings["strict_00100_original_caller_required"] is True
    for name,digest in bindings["files"].items():
        path = SHARP / name
        assert sha(path) == digest
        answer[str(path)] = digest
    return answer


def _sharp():
    global _sharp_module
    if _sharp_module is None:
        path = SHARP / "independent_shared_sharp_terminal.py"
        assert sha(path) == SHARP_DECODER_SHA
        spec = importlib.util.spec_from_file_location("frozen_original_shared_sharp_decoder", path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        _sharp_module = module
    return _sharp_module


def check_registered_caller(state, geometry):
    assert geometry.Q == F(1105,256)
    assert geometry.EDGES == ((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
    register = json.loads((DEEP.HERE / "original_register.json").read_text())
    assert sha(DEEP.HERE / "original_register.json") == "ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604"
    assert register["target_mask"] == "001/00" and register["target_q"] == "1105/256" and register["coverage_certified"] is True
    entries = [entry for entry in register["cells"] if entry["id"] == state["id"]]
    assert len(entries) == 1
    root = entries[0]["path"]
    assert state["path"][:len(root)] == root
    assert len(state["angles"]) == 9 and len(state["positions"]) == 18 and len(state["scalar"]) == 36
    return True


def verify_sharp_literal(guard, independently_propagated_state, geometry):
    before = source_bindings()
    check_registered_caller(independently_propagated_state, geometry)
    decoder = _sharp()
    proof = decoder.verify_binding(SHARP)
    assert proof["status"] == "PASS_SHARED_SHARP_ROW_PHYSICAL_BINDING"
    result = decoder.verify_literal(guard, independently_propagated_state)
    for path,digest in before.items():
        assert sha(path) == digest
    return dict(kind="accepted_shared_sharp_boundary_terminal", guard=result,
                physical_binding=proof, deep_cylinder_used=False)


def verify_deep_literal(terminal, independently_proved_state, geometry):
    before = source_bindings()
    check_registered_caller(independently_proved_state, geometry)
    assert DEEP.verify_guard(independently_proved_state, terminal, geometry)
    for path,digest in before.items():
        assert sha(path) == digest
    return dict(kind=DEEP.KIND, frozen_complete_144_identity_replay=DEEP.REPLAY,
                sharp_row_terminal_used=False)


def no_producers():
    DEEP.no_producers()
    assert not any(name in sys.modules for name in ("shared_strict_row_terminal", "ac_published_sharp_guard", "ac_physical_all_guards_runtime"))
