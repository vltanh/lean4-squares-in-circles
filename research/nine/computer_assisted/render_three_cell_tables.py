#!/usr/bin/env python3
"""Render the complete rational dual table as human-readable Markdown."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
from verify_three_cell_table import verify
HERE=Path(__file__).resolve().parent

def main():
    raw=(HERE/'three_cell_rational_table.json').read_bytes();cert=json.loads(raw)
    summary,counts=verify(cert)
    out=['# Complete rational tables for the three-cell obstruction','',
         'These tables accompany `THREE_CELL_HAND_PROOF.md`. All coordinates in this appendix',
         'are scaled by 1000. The arithmetic verifier has independently reconstructed every',
         'domain and separator alternative and checked every nonnegative linear identity.',
         'No fine position mesh or floating solver occurs in this proof.','',
         '**Certificate SHA-256:** `'+hashlib.sha256(raw).hexdigest()+'`.','',
         '## 1. Ten-row contradiction table','',
         '| Arc i | Direction e | Upper bound from cell 0 | Lower bound from cell 7 | Strict gap |',
         '|---:|---|---:|---:|---:|']
    for r in summary:out.append(f"| {r['arc']} | {tuple(r['direction'])} | {r['upper_left']} | {r['lower_right']} | {r['strict_gap']} |")
    out += ['', '## 2. Closed center-domain inequalities', '',
            'For every listed line number j, `L_j` denotes `a X + b Y <= c`.',
            'The line order is part of the exact dual-table indexing.','']
    domains={}
    for d in cert['domains']:
        key=d['cell'],d['arc'];domains[key]=d
        out += [f"### Cell {key[0]}, arc {key[1]}", '', '| Line j | a | b | c |','|---:|---:|---:|---:|']
        for j,(a,b,c) in enumerate(d['lines']):out.append(f'| {j} | {a} | {b} | {c} |')
        out += ['', 'Vertices: '+ '; '.join(f'({x}, {y})' for x,y in d['vertices'])+'.','']
    out += ['## 3. All merged separator alternatives and exact dual certificates','',
            'A branch with normal (a,b) and threshold B requires `a X + b Y >= B`.',
            'For kind **impossible**, the nonnegative weighted sum of center-domain lines',
            'has normal (a,b) and weighted bound strictly less than B.',
            'For kind **bound**, append the branch as line `N: -a X - b Y <= -B`,',
            'where N is the number of middle-domain lines. The displayed nonnegative',
            'sum has normal e (neighbor 0) or -e (neighbor 7), and its constant is at',
            'most the indicated target U or -L. Thus each row is two vector equalities,',
            'one nonnegativity check per multiplier, and one rational inequality.','']
    for r in cert['rows']:
        i=r['arc'];N=len(domains[3,i]['lines']);e=tuple(r['direction'])
        for neighbor in ('0','7'):
            target=r['upper_left'] if neighbor=='0' else -r['lower_right']
            obj=e if neighbor=='0' else tuple(-x for x in e)
            out += [f'### Middle arc {i}; neighbor cell {neighbor}', '',
                    f'For bound rows, objective normal is {obj}, target is {target}, and the branch line number is {N}.','',
                    '| # | a | b | B | Kind | Nonnegative weighted lines | Combined constant |',
                    '|---:|---:|---:|---:|---|---|---:|']
            for j,b in enumerate(r['branches'][neighbor]):
                a,c=b['normal'];terms=' + '.join(f'({w}) L_{n}' for n,w in b['dual']['terms'])
                out.append(f"| {j} | {a} | {c} | {b['rhs']} | {b['kind']} | {terms} | {b['dual']['weighted_bound']} |")
            out.append('')
    out += ['## 4. Scope','',
            f"There are {counts['impossible_duals']} impossible-branch identities and {counts['bound_duals']} objective-bound identities, {sum(counts.values())} in total.",
            'They prove only the stated three-cell exclusion, and therefore all physical',
            'nine-square roots containing a symmetry copy. Global n=9 optimality and',
            'the classification of all equality packings are not asserted.','']
    (HERE/'THREE_CELL_EXACT_DUAL_TABLES.md').write_text('\n'.join(out))
    print('Rendered',len(out),'lines')

if __name__=='__main__':main()
