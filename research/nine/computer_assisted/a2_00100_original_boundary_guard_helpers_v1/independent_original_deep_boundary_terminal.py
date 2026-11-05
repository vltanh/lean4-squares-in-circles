"""Independent adapter for the already accepted original all-nine cylinder.

This adapter may be used only on an independently attached original strict
001/00 tree. It pins that caller's fixed register, Q and marked bits, checks
all nine slope and eight-center guards against the proved state, and freshly
replays every frozen signed-angle identity before accepting a terminal.
It imports no discovery guard, numerical runtime or optimizer.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import importlib.util
import json
import sys
HERE = Path(__file__).resolve().parent / "deep_boundary"
BINDING_SHA = "3887265c54e663e9cde32de02288b6e6a7ba0251c143dc5f55d65439a4101f67"
KIND = "accepted_original_all_nine_deep_boundary_cylinder"
COUNTS = {"original_all_nine_deep_boundary_cylinder": 0}
RADIUS = F(1,64)
CENTERS = ((F(-3,2),F(-1,16)),(F(-1,2),F(-17,16)),(F(1,2),F(-17,16)),
           (F(3,2),F(-1,16)),(F(-1),F(15,16)),(F(0),F(15,16)),
           (F(1),F(15,16)),(F(-1,2),F(-1,16)),(F(1,2),F(-1,16)))
REPLAY = None

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def source_bindings():
    assert sha(HERE / "BINDING.json") == BINDING_SHA
    binding = json.loads((HERE / "BINDING.json").read_text())
    assert binding["schema"] == "registered_original_all_nine_strict_deep_boundary_terminal_v1"
    assert binding["squared_radius"] == "1105/256" and binding["radius"] == "1/64"
    for field in ("all_nine_physical_frames_required", "all_36_corners_and_pairs_required", "actual_AB_BC_EF_FG_required", "strict_original_CD_required", "all_five_marked_cones_required"):
        assert binding[field] is True
    result = {str(Path(__file__).resolve()): sha(__file__), str(HERE / "BINDING.json"): BINDING_SHA}
    for name, entry in binding["files"].items():
        path = HERE / name
        assert sha(path) == entry["sha256"]
        result[str(path)] = entry["sha256"]
    return result

def replay_source():
    global REPLAY
    bindings = source_bindings()
    if REPLAY is None:
        path = HERE / "weak_outer_deep_boundary_verify.py"
        assert sha(path) == "08d913b7e9adc174e66e2225fe0a05e732cd6fa6fbacb794f39b23f61c6e2aef"
        spec = importlib.util.spec_from_file_location("frozen_original_deep_boundary_exact_replay", path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        certificate = HERE / "weak_outer_deep_boundary_angle_certificate.json"
        assert sha(certificate) == "0a64c08f0e7845a4bf6aa5d5ce43bcb80167a847101b36f903d10554e53a290c"
        result = module.verify(json.loads(certificate.read_text()))
        assert result["status"] == "PASS" and result["cases"] == 8 and result["signed_angle_identities"] == 144
        assert result["radius"] == "1/64" and result["maximum_K"] == "4234/69" and result["contraction_gap"] == "91/2208"
        assert result["unboxed_original_center"] == "F"
        REPLAY = result
    for path, digest in bindings.items():
        assert sha(path) == digest
    return REPLAY

def verify_guard(state, terminal, geometry):
    assert terminal == dict(kind=KIND, radius="1/64", proof_binding_sha256=BINDING_SHA)
    # Upstream original attachment reconstructs this registered strict caller.
    assert geometry.Q == F(1105,256)
    assert geometry.EDGES == ((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
    source_bindings()
    register = json.loads((HERE / "original_register.json").read_text())
    assert register["target_mask"] == "001/00" and register["target_q"] == "1105/256" and register["coverage_certified"] is True
    matches = [entry for entry in register["cells"] if entry["id"] == state["id"]]
    assert len(matches) == 1
    root = matches[0]["path"]
    assert state["path"][:len(root)] == root
    assert len(state["angles"]) == 9 and len(state["positions"]) == 18 and len(state["scalar"]) == 36
    for lo, hi in state["angles"]:
        assert -RADIUS <= lo <= hi <= RADIUS
    for owner, center in enumerate(CENTERS):
        if owner == 5:
            continue
        for axis in (0,1):
            lo, hi = state["positions"][2*owner+axis]
            assert center[axis]-RADIUS <= lo <= hi <= center[axis]+RADIUS
    # For each canonical slope t, theta=atan(t), so |theta|<=|t|.
    # The frozen nonlinear proof retains all corners, pairs and actual links;
    # its final aligned C/D contradiction uses the original strict weak bit.
    replay_source()
    return True

def extend_adapter(parent):
    class Adapter(parent):
        def verify_early_terminal(self, state, terminal):
            if terminal.get("kind") != KIND:
                return super().verify_early_terminal(state, terminal)
            assert verify_guard(state, terminal, self.K.V)
            COUNTS["original_all_nine_deep_boundary_cylinder"] += 1
            return True
    return Adapter

def no_producers():
    assert not any(name in sys.modules for name in ("numpy", "scipy", "highspy", "original_deep_boundary_discovery_guard", "c_relative_chord_boundary_runtime"))
