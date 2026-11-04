"""Prepend one ordinary source-row round and then request a fresh search.

The exact replay schema is unchanged. The supplied search callable accepts
(state, checkpoint) and must run a fresh phase even when its bound budget is
zero. No old numerical point is accepted or reused by this wrapper.
"""
from copy import deepcopy
import time

import direct_shared_bound_round as DIRECT
import direct_shared_bound_precheck as PRECHECK


def run(engine, context, state, source_rows, source_prefixes, search,
        checkpoint=None):
    if not PRECHECK.may_improve(engine, state, source_rows, source_prefixes):
        return search(state, checkpoint)
    started = time.monotonic()
    initial = engine.stateview(state)
    after, ordinary_round, terminal = DIRECT.bound_round(
        engine, context, state, source_prefixes)
    rounds = [] if ordinary_round is None else [ordinary_round]
    if terminal is not None:
        closed = dict(status='CANDIDATE_CLOSED', initial=initial, rounds=rounds,
                      terminal=terminal, seconds=time.monotonic()-started)
        if checkpoint is not None:
            checkpoint(closed)
        return closed, None, None
    if ordinary_round is None:
        assert after is state
        return search(state, checkpoint)
    prefix = dict(status='OPEN', initial=initial, rounds=rounds,
                  final=engine.stateview(after), seconds=time.monotonic()-started,
                  direct_shared_bound_rounds=1)
    if checkpoint is not None:
        checkpoint(prefix)

    def combine(new):
        assert new['initial'] == prefix['final']
        result = deepcopy(new)
        result['initial'] = deepcopy(prefix['initial'])
        result['rounds'] = deepcopy(prefix['rounds']) + deepcopy(new['rounds'])
        result['seconds'] = prefix['seconds'] + new.get('seconds', 0)
        result['direct_shared_bound_rounds'] = 1
        return result

    def saved(new):
        if checkpoint is not None:
            checkpoint(combine(new))

    # The ordinary prefix is already checkpointed before any numerical work.
    # The caller always starts a fresh phase from the independently replayable
    # final state; even a zero-round budget may close that state immediately.
    result, final_state, point = search(after, saved)
    return combine(result), final_state, point
