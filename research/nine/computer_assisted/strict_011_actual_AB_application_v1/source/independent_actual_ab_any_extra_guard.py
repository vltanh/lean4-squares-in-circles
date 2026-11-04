"""Direct independent quantitative guard, without the source guard producer."""
from fractions import Fraction as F


def intervals(raw):
    result = tuple(tuple(F(x) for x in ab) for ab in raw)
    assert all(len(ab) == 2 and ab[0] <= ab[1] for ab in result)
    return result


def evaluate(state, extra):
    assert type(extra) is int and extra in (7, 8)
    p = intervals(state['positions'])
    a = intervals(state['angles'])
    s = intervals(state['scalar'])
    assert (len(p), len(a), len(s)) == (18, 9, 36)
    raw = state['differences']
    d = ({tuple(x['pair']): intervals(x['intervals']) for x in raw}
         if isinstance(raw, list) else
         {tuple(pair): intervals(value) for pair, value in raw.items()})
    assert all(len(pair) == 2 and 0 <= pair[0] < pair[1] < 9
               and len(value) == 2 for pair, value in d.items())

    def gap(i, j, axis):
        lower = p[2 * j + axis][0] - p[2 * i + axis][1]
        upper = p[2 * j + axis][1] - p[2 * i + axis][0]
        pair = (min(i, j), max(i, j))
        if pair in d:
            lo, hi = d[pair][axis]
            if i > j:
                lo, hi = -hi, -lo
            lower, upper = max(lower, lo), min(upper, hi)
        assert lower <= upper
        return lower, upper

    dg_x, dg_y = gap(3, 6, 0), gap(3, 6, 1)
    orders = (gap(1, extra, 0), gap(extra, 3, 0))
    positive = a[3][0] >= 0 or s[12][0] >= 0
    reserve = 1 - max(abs(dg_x[0]), abs(dg_x[1]))
    premises = positive and dg_y[0] >= 0 and reserve > 0
    heights = (gap(1, 3, 1)[1], gap(3, 1, 1)[1],
               gap(1, extra, 1)[1] + gap(3, extra, 1)[1],
               gap(extra, 1, 1)[1] + gap(extra, 3, 1)[1])
    variation = max(heights)
    assert variation >= 0
    passed = premises and all(lo >= 0 for lo, hi in orders) and variation <= F(3, 5)
    return dict(
        status='PASS_ACTUAL_AB_ANY_EXTRA_TERMINAL_GUARD' if passed else 'GUARD_NOT_IMPLIED',
        theorem='actual_AB_full_angle_two_link_row_3_5_v1', variation_limit='3/5',
        premises_proved=bool(premises), D_nonnegative_angle_proved=bool(positive),
        D_angle_interval=list(map(str, a[3])), D_signed_beta_interval=list(map(str, s[12])),
        DG_x_interval=list(map(str, dg_x)), DG_y_interval=list(map(str, dg_y)),
        strict_DG_horizontal_reserve=str(reserve),
        B_extra_D_order_intervals=[list(map(str, v)) for v in orders],
        four_signed_height_upper_bounds=list(map(str, heights)),
        two_link_variation_upper=str(variation),
        original_actual_AB_EF_FG_required=True,
        all_nine_original_00100_ancestry_required=True,
        whole_original_cover_checked=False, new_original_cells=0, new_masks=0,
        extra_original=extra, physical_row=[0, 1, extra, 3],
        selected_distinct_originals=[0, 1, extra, 3, 4, 5, 6],
        literal_source_substitution={'I': 'H' if extra == 7 else 'I'})


def verify_literal(printed, state):
    actual = evaluate(state, printed['extra_original'])
    assert actual['status'] == 'PASS_ACTUAL_AB_ANY_EXTRA_TERMINAL_GUARD'
    assert printed == actual
    return actual
