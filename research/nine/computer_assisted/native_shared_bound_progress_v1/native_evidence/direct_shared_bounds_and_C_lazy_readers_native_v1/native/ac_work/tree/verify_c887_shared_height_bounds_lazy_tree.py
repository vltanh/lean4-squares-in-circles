#!/usr/bin/env python3
"""Existing C887 source-bound arithmetic with lazy exact cover payloads."""
from pathlib import Path
import argparse
import hashlib
import json

import verify_c887_shared_height_bounds_tree as CURRENT
import verify_c887_ownerfree_physical_tree as FROZEN
import verify_c887_ownerfree_physical_lazy_tree as LAZY

FROZEN_SHA = '755f9ed05839e27c04e8687de2273f3bf415388c9ef6dbe9c96fb1c3b20cb7ad'


def replay(parent, tree, output):
    assert hashlib.sha256(Path(FROZEN.__file__).read_bytes()).hexdigest() == FROZEN_SHA
    assert CURRENT.BASE.BASE.OLD is FROZEN
    previous = FROZEN.replay

    def lazy_dispatch(parent, tree, output):
        # Outer row wrappers install their final physical adapter immediately
        # before calling this original cover entry point. Preserve that exact
        # dispatch while changing only node-payload storage.
        LAZY.Checker = FROZEN.Checker
        LAZY.Adapter = FROZEN.Adapter
        return LAZY.replay(parent, tree, output)

    FROZEN.replay = lazy_dispatch
    try:
        result = CURRENT.replay(parent, tree, output)
    finally:
        FROZEN.replay = previous
    assert result['node_payloads_replayed_lazily'] is True
    for path in (__file__, FROZEN.__file__, LAZY.__file__):
        result['checker_dependency_sha256'][str(Path(path).resolve())] = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    Path(output).write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('parent', type=Path)
    parser.add_argument('tree', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    replay(args.parent, args.tree, args.output)
