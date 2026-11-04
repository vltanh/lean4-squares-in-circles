#!/usr/bin/env python3
"""Replay conditional A3 bounds from its stronger unsplit post-A1 source.

The frozen source checker precedes the new row family. All prior A1 and A3
dependencies retain their existing fresh replay; the new family is valid
only on the exact closed component3 domain.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, json, sys
import verify_a_c744_component3_a1_consequence_lazy_tree as BASE
import independent_a_c744_component3_post_a1_bound_rows as ROWS

_configuration = None
_checker = None


class Checker(BASE.Checker):
    def __init__(self):
        global _checker
        super().__init__()
        assert _configuration is not None
        self.post_a1_binding, self.post_a1_consumer = _configuration
        self.post_a1_bound_occurrences = 0
        _checker = self


class Adapter(BASE.Adapter):
    def rebuild(self, state, printed):
        ROWS.assert_caller(state)
        ordinary = [row for row in printed if not row['name'].startswith(ROWS.PREFIX)]
        answer, bounds, physical = super().rebuild(state, ordinary)
        for row in printed:
            if not row['name'].startswith(ROWS.PREFIX):
                continue
            literal = (tuple((i, F(v)) for i, v in row['coefficients']), F(row['rhs']), row['name'])
            ROWS.verify_literal(literal, state, self.checker.post_a1_consumer, self.checker.post_a1_binding)
            assert row['index'] not in answer
            answer[row['index']] = literal
            self.checker.post_a1_bound_occurrences += 1
        return answer, bounds, physical


def replay(tree, output):
    global _configuration
    tree, output = Path(tree).resolve(), Path(output).resolve()
    manifest = json.loads((tree / 'manifest.json').read_text())
    binding = ROWS.verify_binding()
    assert manifest['component3_post_a1_bound_state'] == dict(
        path=str(ROWS.BINDING), sha256=ROWS.BINDING_SHA, component=3)
    consumer = {key: manifest[key] for key in
        ('component', 'scope', 'parent', 'conditional_parent', 'closed_domain')}
    ROWS.assert_consumer(consumer['component'], consumer['scope'], consumer['parent'],
        consumer['conditional_parent'], consumer['closed_domain'], binding)
    source, repeated_binding = ROWS.replay_source(output.with_name(output.stem + '_POST_A1_ROOT_SOURCE'))
    assert repeated_binding == binding
    _configuration = binding, consumer
    BASE.Checker, BASE.Adapter = Checker, Adapter
    report = BASE.replay(tree, output)
    assert _checker is not None and report['component'] == 3
    assert report['node_payloads_replayed_lazily'] is True
    report.update(fresh_component3_post_a1_bound_source=source,
        component3_post_a1_bound_rows_checked=_checker.post_a1_bound_occurrences,
        component3_post_a1_bounds_valid_on_whole_original=False)
    for path in (__file__, ROWS.__file__, ROWS.BINDING, ROWS.LITERAL.__file__):
        report['checker_dependency_sha256'][str(Path(path).resolve())] = ROWS.sha(path)
    ROWS.verify_binding()
    assert not any(name in sys.modules for name in ('numpy', 'scipy', 'highspy',
        'ac_a_c744_component3_post_a1_bounds_runtime', 'a_c744_component3_post_a1_bound_rows'))
    output.write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('tree', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    replay(args.tree, args.output)
