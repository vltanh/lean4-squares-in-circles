#!/usr/bin/env python3
"""Exact diagnostic after unchanged physical propagation; no LP or proof credit."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import argparse
import json
import historical_leaf_source as H


def ceil_sqrt_grid(value, denominator):
    assert value >= 0
    scaled = (value.numerator * denominator * denominator + value.denominator - 1) // value.denominator
    number = isqrt(scaled)
    if number * number < scaled:
        number += 1
    result = F(number, denominator)
    assert result * result >= value
    assert result == 0 or (result - F(1, denominator)) ** 2 < value
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--screen', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--gate-sources', type=Path, required=True)
    args = parser.parse_args(); packet = args.packet.resolve(); output = args.output.resolve()
    screen_path = args.screen.resolve()
    assert H.sha(screen_path) == '922d89e23ee23a01a5f164995a4cc5f22186677f519820f6bf92f82beab33e98'
    screen = H.read(screen_path)
    assert screen['candidate_endpoint_count'] == len(screen['candidates']) == 63
    core, adapter, initial, evidence, inventory, transport = H.setup(packet, output, args.gate_sources)
    import verify_c887_ownerfree_physical_tree as ORIGINAL
    plain = ORIGINAL.Adapter(adapter.checker)
    current = {}; data = []; genuine = []
    for item in screen['candidates']:
        index = item['node']
        if index not in current:
            path = packet / H.TREE_REL / item['file']
            assert H.sha(path) == item['node_sha256']
            record = H.read(path)
            state = H.restore_state(record['final'], plain, core)
            _, _, propagated = plain.rebuild(state, [])
            current[index] = propagated
        state = current[index]; owner = item['owner']; axis = item['axis']; side = item['side']
        endpoint = state['positions'][2 * owner + axis][side]
        orthogonal = state['positions'][2 * owner + 1 - axis]
        minimum = max(F(0), orthogonal[0], -orthogonal[1])
        assert F(91, 60) >= minimum
        ideal_grid = ceil_sqrt_grid(F(91, 60) ** 2 - minimum ** 2, core.GRID)
        signed_endpoint = endpoint if side == 1 else -endpoint
        gain = signed_endpoint - ideal_grid
        row = dict(node=index, node_sha256=item['node_sha256'], owner=owner, axis=axis, side=side,
            saved_endpoint=item['endpoint'], propagated_endpoint=str(endpoint),
            propagated_orthogonal=list(map(str, orthogonal)), minimum_absolute_orthogonal=str(minimum),
            optimistic_best_center_coordinate_grid_upper=str(ideal_grid),
            signed_endpoint_minus_best_grid_upper=str(gain), genuinely_improves_current_box=(gain > 0))
        data.append(row)
        if gain > 0:
            genuine.append(row)
    genuine.sort(key=lambda row: F(row['signed_endpoint_minus_best_grid_upper']), reverse=True)
    H.recheck(packet, args.gate_sources, inventory)
    report = dict(status='PASS_EXACT_PROPAGATED_CENTER_CANDIDATE_DIAGNOSTIC',
        published_source_evidence=evidence, root_screen_sha256=H.sha(screen_path),
        diagnostic_source_sha256=H.sha(__file__), candidates_checked=len(data),
        distinct_certified_leaf_states_propagated=len(current),
        genuine_current_box_candidates=len(genuine), strongest_candidates=genuine[:10],
        all_candidates=data, signed_center_coordinate_rounding_grid=str(core.GRID),
        optimistic_bound_is_necessary_for_any_center_support_plus_only_orthogonal_interval=True,
        no_claim_to_exclude_more_general_combinations_of_premises=True,
        numerical_solver_called=False, weighted_arithmetic_replayed=False,
        new_original_cells=0, new_masks=0)
    path = output / 'PROPAGATED_CENTER_SCREEN.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(status=report['status'], report_sha256=H.sha(path),
        candidates_checked=len(data), distinct_states=len(current), genuine_candidates=len(genuine))), flush=True)


if __name__ == '__main__':
    main()
