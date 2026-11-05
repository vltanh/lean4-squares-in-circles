"""Accepted center rows with exact caching of the unchanged area-moment rows.

Only the numerical discovery module is patched. The physical row decoder and
all independent arithmetic/cover checkers remain unchanged.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import hashlib
import importlib.util
import json
import b_accepted_center_disk_runtime_v1 as BASE

HERE = Path(__file__).resolve().parent
FAMILY = HERE / 'accepted_exact_area_moments_v1'
BINDING = FAMILY / 'BINDING.json'
BINDING_SHA = '903a18152fd47b0b0f38a7306711fb2db0abd7d992ea2d341ecbf7aa6173b7e4'
BASE_SHA = '8ffea381e4c9d9713344d81d4e7e6df15ffefe39cb2eb29469b16684720b78ca'
REFERENCE_SHA = 'd4d4b7a9bda2595693ea10e15821eedfb5681b9f1be32381179b20512d2700d1'
OPTIMIZER_SHA = '9afb26cad3032731902679f67a3ff166d44ba5d2a5684cf31f832da767edd071'
E = BASE.E
PAIRS = frozenset(combinations(range(9), 2))
COUNTS = (5, 6, 7, 8, 9)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify_sources():
    if not __debug__:
        raise RuntimeError('Exact source assertions must be enabled')
    assert digest(BASE.__file__) == BASE_SHA
    assert digest(BINDING) == BINDING_SHA
    binding = json.loads(BINDING.read_text())
    assert binding['status'] == 'ACCEPTED_EXACT_LITERAL_PRESERVING_DISCOVERY_OPTIMIZATION'
    assert binding['reference_sha256'] == REFERENCE_SHA
    assert binding['optimizer_sha256'] == OPTIMIZER_SHA
    assert binding['new_mathematical_row_families'] == 0
    for name, expected in binding['files'].items():
        path = FAMILY / name
        assert path.resolve().is_relative_to(FAMILY.resolve()) and digest(path) == expected
    return binding


class Context(BASE.Context):
    def __init__(self, packet):
        verify_sources()
        super().__init__(packet)
        module = self.AR
        assert digest(module.__file__) == REFERENCE_SHA
        assert not getattr(module.generate_linear, 'exact_moment_optimized', False)
        spec = importlib.util.spec_from_file_location('b_frozen_exact_area_moment_assembly',
            FAMILY / 'fast_exact_area_moments.py')
        fast = importlib.util.module_from_spec(spec); spec.loader.exec_module(fast)
        assert digest(fast.__file__) == OPTIMIZER_SHA
        helpers = tuple(getattr(module, name) for name in ('lower_bound', 'name', 'axes_matrices'))
        helper_codes = tuple(f.__code__ for f in helpers)
        matrices = tuple(tuple(tuple(row) for row in matrix) for matrix in self.default_matrices)
        axes = tuple(tuple(tuple(row) for row in matrix) for matrix in module.axes_matrices())
        self.default_matrices = matrices
        original = fast.install(module)
        optimized = module.generate_linear
        assert optimized.original is original
        self.original_area_moment_generator = original

        def guarded_generate(differences, counts=COUNTS, matrices=None):
            # These are the reviewed optimization's exact caller obligations.
            assert set(differences) == PAIRS
            assert all(type(box) is tuple and len(box) == 2 and
                       all(type(ab) is tuple and len(ab) == 2 and
                           all(type(v) is F for v in ab) and ab[0] <= ab[1] for ab in box)
                       for box in differences.values())
            current = tuple(getattr(module, name) for name in ('lower_bound', 'name', 'axes_matrices'))
            assert all(a is b for a, b in zip(current, helpers))
            assert tuple(f.__code__ for f in current) == helper_codes
            assert type(counts) in (tuple, list) and tuple(counts) == COUNTS
            if matrices is None:
                chosen = axes
            else:
                assert type(matrices) in (tuple, list)
                chosen = tuple(tuple(tuple(row) for row in matrix) for matrix in matrices)
                assert chosen == self.default_matrices
            assert all(len(matrix) == 2 and all(len(row) == 2 and all(type(v) is F for v in row)
                       for row in matrix) for matrix in chosen)
            return optimized(differences, counts=COUNTS, matrices=chosen)

        guarded_generate.exact_moment_optimized = True
        guarded_generate.original = original
        module.generate_linear = guarded_generate
        self.area_moment_optimization_contract = dict(
            reference_sha256=REFERENCE_SHA, optimizer_sha256=OPTIMIZER_SHA,
            full_pair_count=36, counts=COUNTS, matrix_count=len(matrices),
            exact_helper_functions_frozen=True, independent_checker_unchanged=True)


def source_bindings():
    binding = verify_sources()
    result = BASE.source_bindings()
    for path in (__file__, BINDING, *(FAMILY / name for name in binding['files'])):
        result[str(Path(path).resolve())] = digest(path)
    return result
