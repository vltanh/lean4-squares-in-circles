#!/usr/bin/env python3
"""Produce one exact two-premise ordinary bound record, with no LP call."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from math import isqrt
import argparse
import json
import historical_leaf_source as H


def main():
    if not __debug__:
        raise RuntimeError('Exact source assertions must be enabled')
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); here = Path(__file__).resolve().parent
    packet = args.packet.resolve(); output = args.output.resolve()
    core, adapter, initial, evidence, inventory, transport = H.setup(packet, output, here)
    base, _, _, _, _, _ = adapter.K.rebuild(initial['path'], initial['angles'], initial['positions'],
        initial['choices'], initial['scalar'], initial['differences'])
    wanted = F(-123053, 131072)
    found = [(index, row) for index, row in enumerate(base)
             if tuple(row[0]) == ((8, F(1)),) and F(row[1]) == wanted]
    assert len(found) == 1, ('exact retained x_E upper row not unique', found)
    index, old_row = found[0]
    ratio = F(807, 1024); denominator = 1 << 40
    squared = F(8281, 3600) * (1 + ratio * ratio)
    scaled = (squared.numerator * denominator * denominator + squared.denominator - 1) // squared.denominator
    numerator = isqrt(scaled)
    if numerator * numerator < scaled:
        numerator += 1
    support = F(numerator, denominator)
    assert support == F(2123205927653, 1099511627776)
    new_row = (((8, -ratio), (9, F(1))), support,
        f'physical_center_disk_4_{-ratio}_1_{support}')
    printed = [dict(index=index, coefficients=[[k, str(v)] for k, v in old_row[0]],
                    rhs=str(old_row[1]), name=old_row[2]),
               dict(index=len(base), coefficients=[[k, str(v)] for k, v in new_row[0]],
                    rhs=str(new_row[1]), name=new_row[2])]
    rows, bounds, physical = core.validated_rows(adapter, initial, printed)
    weights = [[len(base), 1 << 40], [index, 807 * (1 << 30)]]
    rhs = support + ratio * wanted
    upper = core.ceiling_grid(rhs)
    assert rhs == F(1309709435621, 1099511627776)
    assert upper == F(1249037, 1048576)
    assert upper < initial['positions'][9][1] and upper < physical['positions'][9][1]
    positions = [list(interval) for interval in physical['positions']]
    positions[9][1] = min(positions[9][1], upper)
    scalar = physical['scalar']
    angles, terminal, identities = adapter.infer_angles(initial['angles'], scalar)
    assert terminal is None
    analytic = adapter.analytic(angles)
    scalar = tuple((max(a, c), min(b, d)) for (a, b), (c, d) in zip(scalar, analytic))
    after = dict(deepcopy(initial), positions=tuple(map(tuple, positions)), scalar=scalar,
                 differences=physical['differences'], diagonal=physical['diagonal'], angles=angles)
    core.valid_state(after)
    proposal = dict(kind='scalar', key=9, sign=1, objective=[[9, 1]],
        weights=weights, summed_rhs=str(rhs), residual_coefficients=[], residual_correction='0',
        proved_upper=str(rhs), upper=str(upper))
    rr = dict(round=0, before=core.state_view(initial), propagated=core.state_view(physical),
        printed_rows=printed, absolute_variable_bounds=list(map(str, bounds)), proposals=[proposal],
        physical_frame_inferences=identities, after=core.state_view(after))
    record = dict(id=H.TARGET, original_path=H.ORIGINAL_PATH, status='OPEN',
        initial=core.state_view(initial), rounds=[rr], final=core.state_view(after))
    candidate = dict(schema='C887_leaf47_direct_center_candidate_v1',
        scope='ONLY_THE_CERTIFIED_C887_LEAF_47_DOMAIN', source_leaf_node_sha256=H.NODE_SHA,
        complete_leaf_initial_matches_published_final=True, record=record,
        source_evidence=evidence, numerical_solver_called=False, new_original_cells=0, new_masks=0)
    path = output / 'CANDIDATE_DIRECT_CENTER_ROUND.json'
    path.write_text(json.dumps(candidate, indent=2) + '\n')
    H.recheck(packet, here, inventory)
    print(json.dumps(dict(status='PREPARED_SOLVER_FREE_C887_LEAF_BOUND_RECORD',
        candidate_sha256=H.sha(path), existing_row_index=index, center_row_index=len(base),
        old_y_upper=str(initial['positions'][9][1]), proposed_y_upper=str(upper),
        improvement=str(initial['positions'][9][1] - upper), numerical_solver_called=False)), flush=True)


if __name__ == '__main__':
    main()
