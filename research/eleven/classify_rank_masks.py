#!/usr/bin/env python3
"""Enumerate necessary n=11 rank masks, not physical packings.

Geometric justification is in COORDINATE_RANK_CASES.md. This finite enumeration
cannot prove feasibility or sharpness for any surviving mask.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path


def classify():
    dimensions = []
    total = [0, 0, 0, 0]
    for a, b in [(3, 4), (4, 3), (4, 4)]:
        raw, after_corner, after_double_four, residual = [], [], [], []
        profiles = Counter()
        profile_pairs = Counter()
        for chosen in combinations(range(a * b), 11):
            cells = {(k // b + 1, k % b + 1) for k in chosen}
            rows = [sum(r == i for r, s in cells) for i in range(1, a + 1)]
            cols = [sum(s == j for r, s in cells) for j in range(1, b + 1)]
            if not all(rows) or not all(cols):
                continue
            mask = sum(1 << k for k in chosen)
            raw.append(mask)
            if (4, 4) in cells:
                continue
            after_corner.append(mask)
            if rows.count(4) >= 2 or cols.count(4) >= 2:
                continue
            after_double_four.append(mask)
            if rows[0] == 4 and cols[0] == 4:
                continue
            residual.append(mask)
            row_key = ','.join(map(str, sorted(rows, reverse=True)))
            col_key = ','.join(map(str, sorted(cols, reverse=True)))
            profiles[row_key] += 1
            profile_pairs[row_key + ' / ' + col_key] += 1
        counts = [len(raw), len(after_corner), len(after_double_four), len(residual)]
        total = [x + y for x, y in zip(total, counts)]
        dimensions.append({
            'a': a, 'b': b,
            'nonempty_rank_masks': counts[0],
            'after_forbidden_rank_4_4': counts[1],
            'after_double_four_chain_exclusion': counts[2],
            'after_shared_start_corner_exclusion': counts[3],
            'residual_row_profiles': dict(sorted(profiles.items())),
            'residual_profile_pairs': dict(sorted(profile_pairs.items())),
            'residual_masks': sorted(residual),
        })
    return {
        'schema': 'eleven-coordinate-rank-masks-v1',
        'scope': 'Necessary masks only for a common separating coordinate frame; no realizability claim.',
        'window': 'q <= 49013/10000 < 5',
        'encoding': 'Bit b*(r-1)+(s-1) records rank pair (r,s), starting at bit 0.',
        'symmetry': 'No quotient: axes directed; ranks recomputed after any reflection.',
        'total_by_stage': total,
        'dimensions': dimensions,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', type=Path, help='Write the generated inventory.')
    parser.add_argument('--check', type=Path, help='Compare with a stored inventory.')
    args = parser.parse_args()
    result = classify()
    if args.check and json.loads(args.check.read_text()) != result:
        raise SystemExit('Inventory differs from exact enumeration.')
    if args.write:
        args.write.write_text(json.dumps(result, indent=2) + '\n')
    for item in result['dimensions']:
        print(f"{item['a']}x{item['b']}: "
              f"{item['nonempty_rank_masks']} -> "
              f"{item['after_forbidden_rank_4_4']} -> "
              f"{item['after_double_four_chain_exclusion']} -> "
              f"{item['after_shared_start_corner_exclusion']}")
    print('Total:', ' -> '.join(map(str, result['total_by_stage'])))
    print('Scope: conditional necessary rank masks; all residual geometry remains open.')
