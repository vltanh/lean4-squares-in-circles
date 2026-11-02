#!/usr/bin/env python3
"""Small, deliberately invalid proof streams for the delivered exact checker.

These controls are separate from the full arithmetic replay. They exercise
strict rejection, both new shared-P terminal channels, and binary framing.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

BASE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--checker", type=Path, default=BASE / "verify_lower_side_exact")
    parser.add_argument("--report", type=Path, default=BASE / "lower_side_no_extra_negative_controls.json")
    args = parser.parse_args()
    controls = [
        ("false_whole_root_height_terminal", b"0 1 1\n" + bytes([255]), "nonnegative leaf"),
        ("false_whole_root_shared_P_terminal_21", b"0 1 1\n" + bytes([234]), "nonnegative leaf"),
        ("false_whole_root_cancellation_terminal_22", b"0 1 1\n" + bytes([233]), "nonnegative leaf"),
        ("unknown_split_axis", b"0 1 1\n" + bytes([7]), "unknown axis"),
        ("unknown_terminal", b"0 1 1\n" + bytes([232]), "unknown terminal"),
        ("missing_preorder_children", b"0 1 1\n" + bytes([0]), "missing preorder node"),
        ("truncated_binary_payload", b"0 3 2\n" + bytes([0, 255]), "truncated event stream"),
        ("trailing_binary_payload", b"0 1 1\n" + bytes([255, 255]), "trailing bytes"),
        ("invalid_binary_counts", b"0 2 1\n" + bytes([255, 255]), "invalid binary counts"),
        ("missing_fixed_root", b"128 1 1\n" + bytes([255]), "unrecognized fixed root"),
        ("negative_fixed_root", b"-1 1 1\n" + bytes([255]), "unrecognized fixed root"),
    ]
    results = []
    for name, payload, expected in controls:
        process = subprocess.run([str(args.checker.resolve())], input=payload,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        reason = process.stderr.decode(errors="replace").strip()
        if process.returncode == 0 or expected not in reason:
            raise RuntimeError(f"control {name} was not rejected as expected: {reason}")
        results.append(dict(name=name, result="REJECT", expected_reason=expected,
                            returncode=process.returncode,
                            payload_sha256=hashlib.sha256(payload).hexdigest(), reason=reason))
    report = dict(result="PASS", controls=len(results),
                  checker_source_sha256=hashlib.sha256((BASE / "verify_lower_side_exact.cpp").read_bytes()).hexdigest(),
                  checker_executable_sha256=hashlib.sha256(args.checker.read_bytes()).hexdigest(),
                  control_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  cases=results)
    text = json.dumps(report, indent=2) + "\n"
    args.report.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
