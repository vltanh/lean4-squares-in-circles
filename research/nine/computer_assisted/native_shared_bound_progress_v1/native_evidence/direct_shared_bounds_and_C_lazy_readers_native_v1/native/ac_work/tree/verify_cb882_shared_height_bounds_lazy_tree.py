#!/usr/bin/env python3
"""Existing Cb882 shared-bound arithmetic with lazy exact cover payloads."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent/'d_work/cb882_shared_height_bounds'))
import verify_cb882_shared_height_bounds_tree as CURRENT
import verify_cb882_height_four_tree as FROZEN
import verify_cb882_height_four_lazy_tree as LAZY

FROZEN_SHA = '5f228ec256cb44c309d2a91f5c19130ae043b2d9b4bbeb4021192d657ce8df61'


def replay(tree, output):
    assert hashlib.sha256(Path(FROZEN.__file__).read_bytes()).hexdigest() == FROZEN_SHA
    previous = CURRENT.BASE.BASE
    assert previous is FROZEN
    CURRENT.BASE.BASE = LAZY
    try:
        result = CURRENT.replay(tree, output)
    finally:
        CURRENT.BASE.BASE = previous
    assert result['node_payloads_replayed_lazily'] is True
    for path in (__file__, FROZEN.__file__, LAZY.__file__):
        result['checker_dependency_sha256'][str(Path(path).resolve())] = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    Path(output).write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('tree', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    replay(args.tree, args.output)
