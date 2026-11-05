"""Exact saved-interval diagnostic only; no proof, narrowing, or solver call."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import argparse
import json


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('manifest', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    assert not args.output.exists()
    raw_manifest = args.manifest.read_bytes()
    assert sha256(raw_manifest).hexdigest() == 'a091ad6716ef688cf001857a70f5058acfbb9601a87818de1edb4db4fa9bbe49'
    manifest = json.loads(raw_manifest)
    hits, scanned = [], 0
    for node in manifest['nodes']:
        if node.get('children') or node['status'] != 'OPEN':
            continue
        path = args.manifest.parent / node['file']
        raw = path.read_bytes()
        assert sha256(raw).hexdigest() == node['sha256']
        record = json.loads(raw)
        state_field = 'final' if record.get('final') else 'terminal_state' if record.get('terminal_state') else 'initial'
        state = record[state_field]
        assert state['id'] == 'negative-887236b78100baf3'
        positions = [[F(v) for v in bounds] for bounds in state['positions']]
        assert len(positions) == 18 and all(len(b) == 2 and b[0] <= b[1] for b in positions)
        scanned += 1
        for owner in range(9):
            for axis in (0, 1):
                orthogonal = positions[2*owner + 1 - axis]
                minimum = max(F(0), orthogonal[0], -orthogonal[1])
                sign = 1 if orthogonal[0] > 0 else -1 if orthogonal[1] < 0 else 0
                for side, endpoint in enumerate(positions[2*owner + axis]):
                    excess = endpoint**2 + minimum**2 - F(91, 60)**2
                    if excess > 0:
                        hits.append(dict(node=node['index'], file=node['file'],
                                         node_sha256=node['sha256'], owner=owner,
                                         axis=axis, side=side, endpoint=str(endpoint),
                                         min_abs_orthogonal=str(minimum), orthogonal_sign=sign,
                                         excess_squared=str(excess), state_field=state_field))
    hits.sort(key=lambda row: F(row['excess_squared']), reverse=True)
    assert args.manifest.read_bytes() == raw_manifest
    report = dict(status='EXACT_INTERVAL_DIAGNOSTIC_ONLY_NO_BOUND_CERTIFICATE',
                  manifest_sha256=sha256(raw_manifest).hexdigest(),
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  open_leaf_records_rehashed=scanned, candidate_endpoint_count=len(hits),
                  candidates=hits, weighted_or_ancestry_replay_performed=False,
                  numerical_solver_called=False, new_original_cells=0, new_masks=0)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({**{k:v for k,v in report.items() if k != 'candidates'},
                      'top_candidates':hits[:5],
                      'report_sha256':sha256(args.output.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
