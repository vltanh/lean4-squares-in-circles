#!/usr/bin/env python3
"""Damaged-certificate controls for the original E/A order forest.

This is a rejection audit, not a substitute for a full exact replay.
The complete certificate must already exist before this file is run.
"""
import copy
import gzip
import hashlib
import json
from pathlib import Path

from extraction_search_E_order_verify import verify

HERE = Path(__file__).resolve().parent
CERT = HERE / "weak_outer_hand_E_order_certificate.json.gz"


def find(node, condition):
    if condition(node):
        return node
    for child in node.get("children", {}).values():
        result = find(child, condition)
        if result is not None:
            return result
    return None


def any_node(data, condition):
    for root in data["roots"]:
        result = find(root, condition)
        if result is not None:
            return result
    raise AssertionError("The genuine forest has no matching control node.")


def missing_root(data):
    data["roots"].pop()


def missing_angle_child(data):
    any_node(data, lambda node: node.get("kind") == "angle")["children"].pop("0")


def missing_pose_child(data):
    any_node(data, lambda node: node.get("kind") == "pose")["children"].pop("1")


def missing_separator_child(data):
    # Packing already removes every theorem-excluded alternative.  A
    # retained inset child, including the unique AE/BF vertical choice,
    # must therefore still be covered.
    node = any_node(data, lambda node: node.get("kind") == "sep" and node["pair"][0] == "inset")
    node["children"].pop(next(iter(node["children"])))


def invalid_pose_cut(data):
    # All coordinate and width/inset root intervals lie inside [-rho,rho].
    node = any_node(data, lambda node: node.get("kind") == "pose")
    node["cut_integer"] = 100 * (1 << 20)


def false_whole_root(data):
    data["roots"][0] = {"w": []}


def false_empty_interval(data):
    data["roots"][0] = {"empty_interval": ["coordinate", 0]}


def negative_weight(data):
    node = any_node(data, lambda node: "w" in node)
    node["w"][0][1] = -node["w"][0][1]


def main():
    with gzip.open(CERT, "rt") as handle:
        data = json.load(handle)
    controls = (
        ("missing_orientation_root", missing_root),
        ("missing_closed_angle_child", missing_angle_child),
        ("missing_closed_pose_child", missing_pose_child),
        ("missing_inset_separator_child", missing_separator_child),
        ("pose_cut_outside_parent", invalid_pose_cut),
        ("false_whole_root_leaf", false_whole_root),
        ("false_empty_interval", false_empty_interval),
        ("negative_multiplier", negative_weight),
    )
    reports = []
    for name, damage in controls:
        altered = copy.deepcopy(data)
        damage(altered)
        try:
            verify(altered)
        except (AssertionError, ValueError, KeyError, TypeError) as error:
            reports.append({"control": name, "status": "REJECTED", "reason": str(error)[:500]})
            print(name, "REJECTED", flush=True)
        else:
            raise AssertionError("Damaged certificate accepted: " + name)
    report = {
        "status": "PASS",
        "controls": reports,
        "certificate_sha256": hashlib.sha256(CERT.read_bytes()).hexdigest(),
        "verifier_sha256": hashlib.sha256((HERE / "extraction_search_E_order_verify.py").read_bytes()).hexdigest(),
        "exact_helper_sha256": hashlib.sha256((HERE / "weak_outer_hand_right_lower_verify.py").read_bytes()).hexdigest(),
    }
    (HERE / "weak_outer_hand_E_order_rejection_controls.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
