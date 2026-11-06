"""Fresh standard-library replay of the complete leaf-480 physical table.

Default: check every arithmetic leaf, with no trusted saved PASS file.
--start/--count permit explicit partial replays; these never report completion.
The containing Cd402 original and the legacy ancestry are not proved here.
"""
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from pathlib import Path
import argparse, base64, json, lzma
from four_exact import Model, D, ROOT_P
from basis_integer import reconstruct, reserve

BASE = Path(__file__).resolve().parent
PACKED_SHA = '1d5bb687607de8ccdb56d425a6015632963666a204a61a30155347ff2d36e742'
RULES_SHA = '90fb9b21b2722288b57f4aa9484ac7e7ce92cf276680bd74fbc41c3868096cbf'
KERNEL_SHA = 'eddb33e2b483c198fd1bfdbd5e83a7352b65a7afbd7aa76e07edc099f3c2e68d'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def integer(x, lo, hi):
    return type(x) is int and lo <= x <= hi


def read_packet():
    need(digest(BASE / 'four_exact.py') == RULES_SHA, 'changed physical rule source')
    need(digest(BASE / 'basis_integer.py') == KERNEL_SHA, 'changed multiplier kernel')
    names = [f'leaf480_basis.b64.part{i:02d}' for i in range(1, 7)]
    parts = [BASE / name for name in names]
    need(all(p.is_file() for p in parts), 'incomplete certificate publication')
    encoded = ''.join(''.join(p.read_text().split()) for p in parts)
    packed = base64.b64decode(encoded, validate=True)
    need(sha256(packed).hexdigest() == PACKED_SHA, 'changed or mixed certificate parts')
    data = json.loads(lzma.decompress(packed, memlimit=256 << 20))
    need(data['format'] == 'cd402_leaf480_nested_v1', 'wrong certificate format')
    need(len(data['roots']) == 8, 'missing signed root')
    return data


def attachment():
    # Transcribed from saved leaf 480, archived blob
    # 12b58e41d467daeac461e246055ce7aca7aec421. Legacy proofs are reused.
    source = [('-674929/524288', '-47/64'), ('336577/524288', '1188497/1048576'),
              ('-1687/8192', '17/64'), ('-371679/1048576', '726305800585/70368744177664'),
              ('-428935/1048576', '531301/1048576'), ('213227/524288', '376139/524288'),
              ('-421201/1048576', '1079431/1048576'), ('1167909/1048576', '91/60')]
    for (lo, hi), (oldlo, oldhi) in zip(ROOT_P, source):
        need(lo <= F(oldlo) <= F(oldhi) <= hi, 'unsafe incoming-coordinate enlargement')
    need(F(17, 64)**2 + F(71, 200)**2 < F(29, 60)**2, 'F norm bound failed')
    need(F(29, 60) + F(91, 60) == 2, 'common-axis radius sum failed')
    return {'saved_leaf': 480, 'endpoint_containments': 16,
            'legacy_source_blob': '12b58e41d467daeac461e246055ce7aca7aec421',
            'fresh_legacy_ancestry_replay': False}


def replay(data, start=0, count=None):
    need(type(start) is int and start >= 0, 'invalid arithmetic start')
    need(count is None or (type(count) is int and count >= 0), 'invalid arithmetic count')
    stop = None if count is None else start + count
    stats = dict(roots=8, nodes=0, angle_splits=0, physical_splits=0,
                 arithmetic_leaves=0, common_axis_leaves=0, checked=0,
                 weighted_rows=0, skipped=0)
    minimum = None

    def visit(node, T, sats):
        nonlocal minimum
        need(isinstance(node, list) and node, 'invalid proof node')
        stats['nodes'] += 1
        tag = node[0]
        need(integer(tag, 0, 3), 'invalid node tag')
        if tag == 0:
            need(2 <= len(node) <= 4, 'invalid arithmetic terminal')
            k = stats['arithmetic_leaves']; stats['arithmetic_leaves'] += 1
            chosen = node[1]
            need(isinstance(chosen, list) and chosen and
                 all(type(i) is int and i >= 0 for i in chosen) and
                 len(chosen) == len(set(chosen)), 'invalid multiplier row selection')
            if k < start or (stop is not None and k >= stop):
                stats['skipped'] += 1
                return
            model = Model(T, sats); rows, names = model.with_bounds()
            need(all(-4 <= lo <= 4 and -4 <= hi <= 4 for lo, hi in model.bounds),
                 'unpaid variable exceeds absolute bound four')
            need(all(i < len(rows) and names[i] != 'unused imported row (zero)'
                     for i in chosen), 'invalid or imported theorem row')
            if len(node) == 4:
                need(node[2] is None and isinstance(node[3], list), 'invalid literal fallback')
                weights = [int(w) for w in node[3]]
            else:
                columns = None if len(node) == 2 else node[2]
                if columns is not None:
                    need(isinstance(columns, list) and all(type(j) is int for j in columns),
                         'invalid reconstruction equation list')
                weights = reconstruct(rows, chosen, columns)
            r = reserve(rows, chosen, weights)
            margin = F(r, D * sum(weights))
            minimum = margin if minimum is None else min(minimum, margin)
            stats['checked'] += 1; stats['weighted_rows'] += len(chosen)
            return
        if tag == 1:
            need(len(node) == 4 and integer(node[1], 0, 3), 'invalid angle split')
            owner = node[1]; lo, hi = T[owner]; middle = (lo + hi) / 2
            need(lo < middle < hi, 'empty angle child')
            stats['angle_splits'] += 1
            for side in (0, 1):
                child_T = [t[:] for t in T]
                child_T[owner] = [lo, middle] if side == 0 else [middle, hi]
                visit(node[2 + side], child_T, sats)
            return
        if tag == 2:
            need(len(node) == 4, 'invalid physical separator split')
            i, j, children = node[1:]
            need(integer(i, 0, 3) and integer(j, 0, 3) and i < j and
                 isinstance(children, list) and len(children) == 8, 'missing physical alternative')
            stats['physical_splits'] += 1
            for child, (owner, axis, sign) in zip(children, product((i, j), (0, 1), (-1, 1))):
                visit(child, T, sats + [[i, j, owner, axis, sign]])
            return
        need(len(node) == 3, 'invalid common-axis terminal')
        axis, path = node[1:]
        need(isinstance(axis, list) and len(axis) == 2 and integer(axis[0], 0, 3) and
             integer(axis[1], 0, 1), 'invalid common owned axis')
        need(isinstance(path, list) and len(path) == 3 and len(set(path)) == 3 and
             all(integer(i, 0, 3) for i in path) and 1 in (path[0], path[2]), 'invalid F-end chain')
        edges = set()
        for i, j, owner, local_axis, sign in sats:
            if [owner, local_axis] == axis:
                edges.add((i, j) if sign == 1 else (j, i))
        need((path[0], path[1]) in edges and (path[1], path[2]) in edges,
             'unrelated axes cannot be joined')
        stats['common_axis_leaves'] += 1

    for tree, bits in zip(data['roots'], product((0, 1), repeat=3)):
        T = [[F(-1), F(0)] if b == 0 else [F(0), F(1)] for b in bits[:2]]
        T += [[F(-1), F(0)], [F(-1), F(0)] if bits[2] == 0 else [F(0), F(1)]]
        visit(tree, T, [])
    need(stats['arithmetic_leaves'] + stats['common_axis_leaves'] ==
         8 + stats['angle_splits'] + 7 * stats['physical_splits'], 'incomplete finite union')
    need((stats['nodes'], stats['arithmetic_leaves'], stats['common_axis_leaves'],
          stats['angle_splits'], stats['physical_splits']) == (6462, 3539, 47, 2759, 117),
         'changed published cover')
    return stats, minimum


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start', type=int, default=0)
    parser.add_argument('--count', type=int)
    parser.add_argument('--output', type=Path, default=BASE / 'leaf480_fresh_replay.json')
    args = parser.parse_args()
    data = read_packet(); attached = attachment()
    stats, minimum = replay(data, args.start, args.count)
    complete = stats['checked'] == stats['arithmetic_leaves'] and stats['skipped'] == 0
    report = {'status': 'PASS_COMPLETE_LEAF480' if complete else 'PASS_EXPLICIT_PARTIAL_REPLAY',
              'complete': complete, 'scope': 'one saved leaf, not the Cd402 original',
              'arithmetic_start': args.start, 'arithmetic_count': stats['checked'],
              'cover': stats, 'minimum_normalized_reserve': str(minimum), 'attachment': attached,
              'bindings': {'packed': PACKED_SHA, 'rules': RULES_SHA, 'kernel': KERNEL_SHA,
                           'checker': digest(Path(__file__))}}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
