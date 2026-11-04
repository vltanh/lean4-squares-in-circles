"""Exhaustive coarse three-core/eight-ring gap occupancy words.

This finite enumeration retains continuous geometry; it is not a lower-bound
certificate for any listed word.
"""
from itertools import product
from math import comb
from pathlib import Path
import json


def orbit(word):
    return {w[i:]+w[:i] for w in (word, word[::-1]) for i in range(8)}


def main():
    counts = {}
    for word in product(range(4), repeat=8):
        if sum(word) > 3:
            continue
        representative = min(orbit(word))
        counts[representative] = counts.get(representative, 0)+1
    if sum(counts.values()) != comb(11, 3) or len(counts) != 17:
        raise RuntimeError('incorrect exhaustive word count')
    rows = []
    for word in sorted(counts, key=lambda x: (sum(x), x)):
        size = len(orbit(word))
        if size != counts[word]:
            raise RuntimeError('orbit not completely covered')
        rows.append({'word': list(word), 'active_cores': sum(word),
                     'inactive_cores': 3-sum(word), 'orbit_size': size})
    data = {'schema': 'three-core-eight-ring-interleavings-v1',
            'raw_count': sum(counts.values()), 'orbit_count': len(rows),
            'rows': rows}
    path = Path(__file__).with_name('THREE_CORE_INTERLEAVINGS.json')
    path.write_text(json.dumps(data, indent=2)+'\n')
    print('CLOSED finite occupancy cover: 165 words, 17 dihedral rows')
    for row in rows:
        print(''.join(map(str, row['word'])), row['active_cores'], row['orbit_size'])


if __name__ == '__main__':
    main()
