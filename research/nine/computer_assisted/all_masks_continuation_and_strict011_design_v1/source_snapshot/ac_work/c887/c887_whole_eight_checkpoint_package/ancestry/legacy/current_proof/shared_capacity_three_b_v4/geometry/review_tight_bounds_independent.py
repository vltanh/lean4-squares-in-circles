#!/usr/bin/env python3
"""Independent exact row-sum audit of complete original-cell bound proofs.

The physical row formulas are the accepted, hash-bound v14 verifier. This
reviewer does not import the bound producer or its replay wrapper. It collects
unweighted rows, independently sums rational multipliers, checks every derived
bound, and only then installs the next round's certified coordinate intervals.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import importlib
import json
from pathlib import Path
import sys
import time
from types import FunctionType

VERSION = "strict_bulk_2026_11_03_v14"
VERIFIER_SHA256 = "ec1b7de7b15bcc9d89d12087bff974c68e6d056bdaae26b482d514027ec97993"
RHO = F(91, 60)
SCALE = 1 << 40


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compact(value):
    return json.dumps(value, separators=(",", ":"))


def collect_rows(V, path, angles, positions, choices, cuts=(), analytic=None):
    """Collect each exact scalar row before any weighted sum is computed.

    An isolated globals dictionary injects already-proved intervals only into
    this invocation. The imported module and original path decoder are never
    modified. All rows are unweighted: the frozen routine receives no weights.
    """
    row_map = {}
    ending = {}
    expected_state = (angles, positions, choices)

    def certified_state(requested):
        assert requested == path
        return expected_state

    namespace = dict(V.replay_current_leaf.__globals__)
    namespace["reconstruct"] = certified_state
    routine = FunctionType(V.replay_current_leaf.__code__, namespace)
    source_filename = str(Path(V.__file__))

    def observe(frame, event, arg):
        if frame.f_code.co_filename != source_filename:
            return
        if event == "call" and frame.f_code.co_name == "add":
            local = frame.f_locals
            assert frame.f_back.f_code is routine.__code__ or frame.f_back.f_code.co_name == "product_rows"
            assert type(local["index"]) is int and local["index"] not in row_map
            co = {}
            for column, value in local["entries"]:
                assert type(column) is int
                co[column] = co.get(column, F(0)) + F(value)
            row_map[local["index"]] = (tuple(sorted((k, v) for k, v in co.items() if v)),
                                      F(local["rhs"]), str(local["name"]))
        elif event == "return" and frame.f_code is routine.__code__:
            ending.update({k: frame.f_locals[k] for k in ("index", "bounds", "dense_start", "dense_stop",
                                                        "contact_start", "contact_stop")
                           if k in frame.f_locals})

    leaf = {"path": path, "weights": [], "power": 40,
            "circle_cuts": list(cuts), "context_version": VERSION}
    if analytic:
        for key in ("analytic_terminal", "row_guard", "local_radius"):
            if key in analytic:
                leaf[key] = analytic[key]
    previous_profiler = sys.getprofile()
    assert previous_profiler is None
    sys.setprofile(observe)
    terminal = None
    try:
        try:
            value = routine(leaf)
            assert isinstance(value, tuple) and len(value) == 2
            assert value[0] is None and isinstance(value[1], str)
            terminal = value[1]
        except AssertionError as exc:
            detail = exc.args[0] if exc.args else None
            if not (isinstance(detail, tuple) and detail and
                    detail[0] == "nonpositive exact rational leaf"):
                raise
            # With zero weights the only arithmetic sum is zero. No failed
            # assertion except that precise final reserve check is accepted.
            assert detail[1] == "0"
            assert ending.get("index") and row_map
    finally:
        sys.setprofile(None)
    if not terminal:
        # The frozen verifier intentionally skips the unweighted dense and
        # exact-contact row families. Reconstruct these two families directly
        # from their explicit original-corner support formula, preserving their
        # observed immutable index ranges. All other rows were observed above.
        for stem, directions, rhs in (("dense", V.DENSE_DIRS, V.roots(F(1105, 256))[1]),
                                      ("contact", V.CONTACT_DIRS, F(1105, 16))):
            begin, end = ending[stem + "_start"], ending[stem + "_stop"]
            assert end - begin == 9 * len(directions) * 4
            for index in range(begin, end):
                assert index not in row_map
                original, rest = divmod(index - begin, len(directions) * 4)
                direction, corner = divmod(rest, 4)
                s, t = ((-1, -1), (-1, 1), (1, -1), (1, 1))[corner]
                p, q = map(F, directions[direction])
                assert p*p + q*q == (1 if stem == "dense" else 1105)
                coefficients = ((2*original, p), (2*original+1, q),
                                (18+original, (s*p+t*q)/2), (27+original, (s*q-t*p)/2))
                row_map[index] = (tuple((k, v) for k, v in coefficients if v), rhs,
                                  stem + "_original_corner_support")
        assert set(row_map) == set(range(ending["index"]))
    rows = [row_map[index] for index in sorted(row_map)]
    n = 54 + 6 * sum(kind == "sat" for _, kind, _ in choices)
    bounds = [RHO] * 18 + [F(1)] * 36
    bounds += [2 * RHO, 2 * RHO, F(1), F(1), F(1), F(1)] * ((n - 54) // 6)
    assert len(bounds) == n
    assert all(0 <= k < n for row, _, _ in rows for k, _ in row)
    if not terminal:
        assert ending["bounds"] == bounds
    return rows, tuple(bounds), terminal


def weighted_sum(rows, bounds, terms):
    co = [F(0)] * len(bounds)
    rhs = F(0)
    seen = set()
    assert isinstance(terms, list)
    for term in terms:
        assert isinstance(term, list) and len(term) == 2
        index, weight = term
        assert type(index) is int and 0 <= index < len(rows)
        assert type(weight) is int and weight > 0 and index not in seen
        seen.add(index)
        lam = F(weight, SCALE)
        row, bound, _ = rows[index]
        rhs += lam * bound
        for k, value in row:
            co[k] += lam * value
    return co, rhs


def printed_rows(rows, indices):
    return [{"index": i, "name": rows[i][2],
             "coefficients": [[k, str(value)] for k, value in rows[i][0]],
             "rhs": str(rows[i][1])} for i in sorted(indices)]


def verify_record(V, record, register, keep_table=True):
    ident = record["id"]
    original = register[ident]
    assert original["status"] == "OPEN"
    assert record["path"] == original["path"]
    path = record["path"]
    recomputed = original["sign"] + "-" + hashlib.sha256(compact(path).encode()).hexdigest()[:16]
    assert ident == recomputed
    angles, positions, choices = V.reconstruct(path)
    positions = tuple(tuple(v) for v in positions)
    deductions = []
    states = []
    least_slack = None
    checked_rounds = 0

    def finish(terminal, reserve=None, final_state=None):
        return ({"id": ident, "status": "PASS_COMPLETE_ORIGINAL_CELL",
                 "sign": original["sign"], "parent_path": path,
                 "rounds": checked_rounds, "verified_bound_deductions": len(deductions),
                 "minimum_bound_slack": str(least_slack), "final_reserve": str(reserve),
                 "final_terminal": terminal, "deductions": deductions},
                {"id": ident, "parent_path": path, "states": states,
                 "final_state": final_state, "conclusion": terminal or "positive_rational_reserve"})

    for rindex, round_record in enumerate(record["rounds"]):
        rows, bounds, terminal = collect_rows(V, path, angles, positions, choices)
        if terminal:
            return finish(terminal)
        next_positions = [list(v) for v in positions]
        state = {"round": rindex,
                 "certified_positions_before": [[str(a), str(b)] for a, b in positions],
                 "absolute_variable_bounds": [str(x) for x in bounds],
                 "deductions": []}
        used_rows = set()
        for pindex, proposal in enumerate(round_record["proposals"]):
            objective = proposal["objective"]
            assert isinstance(objective, list) and len(objective) == 1
            k, sign = objective[0]
            assert type(k) is int and 0 <= k < 18 and type(sign) is int and sign in (-1, 1)
            upper = F(proposal["upper"])
            co, rhs = weighted_sum(rows, bounds, proposal["weights"])
            error = list(co)
            error[k] -= sign
            correction = sum(M * abs(c) for M, c in zip(bounds, error))
            proven = rhs + correction
            assert proven <= upper, ("invalid derived bound", ident, rindex, pindex,
                                     str(proven), str(upper))
            slack = upper - proven
            least_slack = slack if least_slack is None else min(slack, least_slack)
            if sign == 1:
                next_positions[k][1] = min(next_positions[k][1], upper)
            else:
                next_positions[k][0] = max(next_positions[k][0], -upper)
            deduction = {"round": rindex, "index": pindex, "coordinate": k,
                         "sign": sign, "declared_upper": str(upper),
                         "proved_upper": str(proven), "slack": str(slack)}
            deductions.append(deduction)
            if keep_table:
                state["deductions"].append({**deduction, "weights": proposal["weights"],
                    "weight_denominator": SCALE, "summed_rhs": str(rhs),
                    "residual": [[j, str(c)] for j, c in enumerate(error) if c],
                    "residual_correction": str(correction)})
                used_rows.update(i for i, _ in proposal["weights"])
        positions = tuple(tuple(v) for v in next_positions)
        checked_rounds += 1
        if keep_table:
            state["rows"] = printed_rows(rows, used_rows)
            state["certified_positions_after"] = [[str(a), str(b)] for a, b in positions]
            states.append(state)
        if any(lo > hi for lo, hi in positions):
            return finish("contradictory_certified_coordinate_interval")
    final = record.get("candidate_terminal")
    assert isinstance(final, dict), "missing final contradiction"
    assert final.get("context_version", VERSION) == VERSION
    assert final.get("power", 40) == 40
    # Neither the untrusted producer's before_box/current_pos fields nor any
    # replacement path/context field may supply a premise to this verifier.
    assert "path" not in final
    rows, bounds, terminal = collect_rows(V, path, angles, positions, choices,
                                         final.get("circle_cuts", []), final)
    if terminal:
        return finish(terminal, final_state={"certified_positions": [[str(a), str(b)] for a, b in positions],
                                           "analytic_terminal": terminal})
    co, rhs = weighted_sum(rows, bounds, final.get("weights", []))
    correction = sum(M * abs(c) for M, c in zip(bounds, co))
    reserve = -rhs - correction
    assert reserve > 0, ("final contradiction fails", ident, str(reserve))
    final_state = None
    if keep_table:
        final_state = {"certified_positions": [[str(a), str(b)] for a, b in positions],
                       "absolute_variable_bounds": [str(v) for v in bounds],
                       "rows": printed_rows(rows, {i for i, _ in final.get("weights", [])}),
                       "weights": final.get("weights", []), "weight_denominator": SCALE,
                       "summed_coefficients": [[k, str(c)] for k, c in enumerate(co) if c],
                       "summed_rhs": str(rhs), "residual_correction": str(correction),
                       "reserve": str(reserve)}
    return finish(None, reserve=reserve, final_state=final_state)


def main(args):
    started = time.monotonic()
    payload = args.payload.resolve()
    sys.path.insert(0, str(payload))
    V = importlib.import_module("weak_outer_numeric_strict_bulk_v14_verify")
    assert Path(V.__file__).resolve() == payload / "weak_outer_numeric_strict_bulk_v14_verify.py"
    assert sha(Path(V.__file__)) == VERIFIER_SHA256
    source_hashes = {p.name: sha(p) for p in payload.glob("*.py")}
    rp = payload / "fixed_231_register.json"
    register_sha = sha(rp)
    register = {r["id"]: r for r in json.loads(rp.read_text())["cells"]}
    assert len(register) == 231 and sum(r["status"] == "OPEN" for r in register.values()) == 178
    results = []
    tables = []
    inputs = {}
    accepted = []
    rejected = []
    filenames = []
    for arg in args.inputs:
        filenames.extend(sorted(arg.glob("*.json")) if arg.is_dir() else [arg])
    seen_ids = set()
    for path in filenames:
        record = json.loads(path.read_text())
        if not isinstance(record, dict) or record.get("status") != "NUMERIC_CANDIDATE":
            continue
        ident = record["id"]
        assert ident not in seen_ids, "duplicate original cell"
        seen_ids.add(ident)
        before = sha(path)
        try:
            report, table = verify_record(V, record, register)
        except AssertionError as exc:
            rejected.append({"id": ident, "source": str(path), "source_sha256": before,
                             "status": "REJECTED", "reason": str(exc)[:1200]})
            print("REJECTED", ident, str(exc)[:200], flush=True)
            continue
        assert sha(path) == before
        inputs[str(path)] = before
        results.append(report)
        tables.append(table)
        accepted.append(record)
        print("PASS", ident, "deductions", report["verified_bound_deductions"],
              "rounds", report["rounds"], flush=True)
    controls = []
    if accepted:
        def reject(name, record):
            try:
                verify_record(V, record, register, keep_table=False)
            except (AssertionError, ValueError, IndexError, KeyError) as exc:
                controls.append({"name": name, "status": "REJECTED", "reason": str(exc)[:180]})
                return
            raise AssertionError("damaged control accepted: " + name)
        first = accepted[0]
        bad_bound = deepcopy(first)
        bad_bound["rounds"][0]["proposals"][0]["upper"] = "-100"
        reject("unproved_center_bound", bad_bound)
        bad_weight = deepcopy(first)
        bad_weight["rounds"][0]["proposals"][0]["weights"][0][1] *= -1
        reject("negative_bound_multiplier", bad_weight)
        bad_parent = deepcopy(first)
        bad_parent["path"][0][2] = 1 - bad_parent["path"][0][2]
        reject("different_original_parent", bad_parent)
        if first.get("candidate_terminal", {}).get("weights"):
            bad_final = deepcopy(first)
            bad_final["candidate_terminal"]["weights"] = []
            reject("erased_final_multiplier_table", bad_final)
    assert sha(rp) == register_sha
    assert all(sha(payload / name) == digest for name, digest in source_hashes.items())
    table_artifact = {"scope": "Explicit rational rows and complete acyclic bound deductions",
                      "physical_source_sha256": VERIFIER_SHA256, "cells": tables}
    args.table.write_text(json.dumps(table_artifact, indent=2) + "\n")
    report = {"status": "PASS" if not rejected else "PASS_WITH_REJECTED_CANDIDATES",
              "scope": "INDEPENDENT_ROW_SUM_CHECK_OF_COMPLETE_ORIGINAL_CELLS",
              "new_closed_original_cells": len(results),
              "bound_deductions": sum(r["verified_bound_deductions"] for r in results),
              "starting_open_original_cells": 178,
              "remaining_open_original_cells_from_these_proofs": 178 - len(results),
              "whole_mask_closed": False, "whole_mask_ledger": {"closed": 8, "open": 24},
              "row_formula_scope": "Accepted frozen physical formulas; row sums and state induction implemented independently",
              "input_sha256": inputs, "register_sha256": register_sha,
              "frozen_python_source_sha256": source_hashes,
              "table_sha256": sha(args.table), "reviewer_sha256": sha(Path(__file__).resolve()),
              "cells": results, "rejected_candidates": rejected, "damaged_controls": controls,
              "seconds": time.monotonic() - started}
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "new_closed_original_cells", "bound_deductions", "seconds")}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--payload", type=Path, required=True)
    parser.add_argument("--inputs", type=Path, nargs="+", required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--table", type=Path, required=True)
    main(parser.parse_args())
