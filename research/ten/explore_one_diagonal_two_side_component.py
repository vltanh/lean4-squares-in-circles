#!/usr/bin/env python3
"""Reproduce an exploratory six-body LSLSLD stress component.

This uses high-precision floating-point root finding. It is NOT an interval
certificate, a proof of an exact root, or a ten-square packing. The output
is research evidence that a completion bound should be sought, rather than
assuming every such six-body component is itself impossible.
"""
import json
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 80


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def scale(t, a):
    return tuple(t*x for x in a)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def cross(a, b):
    return a[0]*b[1]-a[1]*b[0]


def model(radius, u, z):
    v = 2+mp.sqrt(2)-u
    ha = mp.sqrt(radius**2-u**2)
    hb = mp.sqrt(radius**2-v**2)
    ta = (u*z-ha*(u-1))/(ha*(1-ha+z))
    tb = (v*z-hb*(v-1))/(hb*(1-hb+z))
    q = 1/mp.sqrt(1+ta**2)
    p = ta*q
    s = 1/mp.sqrt(1+tb**2)
    r = tb*s
    na, nb = (p, q), (-r, s)
    ea, eb = (q, -p), (s, r)
    pa, pb = (1-u, 1-ha), (v-1, 1-hb)
    pc, qc = add(pa, na), add(pb, nb)
    wc = add(sub(qc, ea), na)
    sa = 1/(u*q/ha-p)
    sb = 1/(v*s/hb-r)
    gc = add(scale(sa, na), scale(sb, nb))
    return dict(radius=radius, u=u, v=v, z=z, ha=ha, hb=hb,
                p=p, q=q, r=r, s=s, na=na, nb=nb, ea=ea, eb=eb,
                pa=pa, pb=pb, pc=pc, qc=qc, wc=wc, sa=sa, sb=sb, gc=gc)


def equations(radius, u, z):
    d = model(radius, u, z)
    return (dot(sub(d['qc'], d['pc']), d['na']),
            dot(d['wc'], d['wc'])-radius**2,
            cross(d['wc'], d['gc']))


def square(origin, e, f):
    return (origin, add(origin, e), add(origin, f), add(add(origin, e), f))


def separation(a, b):
    """Largest signed projection gap over both square frames."""
    gaps = []
    for body in (a, b):
        for axis in (sub(body[1], body[0]), sub(body[2], body[0])):
            aa, bb = [dot(x, axis) for x in a], [dot(x, axis) for x in b]
            gaps += [min(bb)-max(aa), min(aa)-max(bb)]
    return max(gaps)


def string(x):
    return mp.nstr(x, 65)


def vector(x):
    return [string(t) for t in x]


def main():
    radius, u, z = mp.findroot(
        equations,
        (mp.mpf('2.032529946878352'), mp.mpf('1.7976025298772544'),
         mp.mpf('0.6225256300649574')),
        tol=mp.mpf('1e-70'), maxsteps=100,
    )
    d = model(radius, u, z)
    u_slide, v_slide = mp.mpf(7)/9, mp.mpf(1)/7
    e1, e2 = (mp.mpf(1), mp.mpf(0)), (mp.mpf(0), mp.mpf(1))
    k = 1/mp.sqrt(2)
    dcenter = ((d['v']-u)/2, -z)
    squares = {
        'A': square((-u, -d['ha']), e1, e2),
        'B': square((d['v']-1, -d['hb']), e1, e2),
        'C': square(sub(d['qc'], d['ea']), d['ea'], d['na']),
        'D': square(sub(dcenter, (k, mp.mpf(0))), (k, k), (k, -k)),
        'S_A': square(sub(d['pa'], scale(u_slide, d['ea'])), d['na'], d['ea']),
        'S_B': square(sub(d['pb'], scale(v_slide, d['eb'])), d['nb'], d['eb']),
    }
    contacts = [
        ('A', 'D', (1-u, -z), e1, mp.mpf(1)),
        ('D', 'B', (d['v']-1, -z), e1, mp.mpf(1)),
        ('A', 'S_A', d['pa'], d['na'], d['sa']),
        ('S_A', 'C', d['pc'], d['na'], d['sa']),
        ('B', 'S_B', d['pb'], d['nb'], d['sb']),
        ('S_B', 'C', d['qc'], d['nb'], d['sb']),
    ]
    circle = {
        'A': ((-u, -d['ha']), d['sa']*d['q']/d['ha']),
        'B': ((d['v'], -d['hb']), d['sb']*d['s']/d['hb']),
        'C': (d['wc'], dot(d['wc'], d['gc'])/radius**2),
    }
    force = {name: (mp.mpf(0), mp.mpf(0)) for name in squares}
    torque = {name: mp.mpf(0) for name in squares}
    support_residual = mp.mpf(0)
    membership_residual = mp.mpf(0)
    contact_coordinates = []
    for a, b, point, normal, magnitude in contacts:
        f = scale(magnitude, normal)
        force[a] = sub(force[a], f)
        force[b] = add(force[b], f)
        torque[a] -= cross(point, f)
        torque[b] += cross(point, f)
        support_residual = max(support_residual,
            max(dot(sub(x, point), normal) for x in squares[a]),
            max(-dot(sub(x, point), normal) for x in squares[b]))
        coordinate_row = {'a': a, 'b': b}
        for name in (a, b):
            body = squares[name]
            offsets = tuple(dot(sub(point, body[0]), sub(body[j], body[0])) for j in (1, 2))
            coordinate_row[name] = vector(offsets)
            membership_residual = max(membership_residual,
                                      *(-t for t in offsets), *(t-1 for t in offsets))
        contact_coordinates.append(coordinate_row)
    for name, (point, coefficient) in circle.items():
        force[name] = sub(force[name], scale(coefficient, point))
    assert min(c for _, c in circle.values()) > 0
    assert min(c[-1] for c in contacts) > 0

    pair_rows = []
    names = list(squares)
    active = {frozenset((a, b)) for a, b, *_ in contacts}
    for i, a in enumerate(names):
        for b in names[i+1:]:
            pair_rows.append({'a': a, 'b': b,
                              'active_stress_contact': frozenset((a, b)) in active,
                              'largest_separating_projection_gap': string(separation(squares[a], squares[b]))})
    force_residual = max(mp.sqrt(dot(f, f)) for f in force.values())
    torque_residual = max(abs(t) for t in torque.values())
    maximum_vertex_excess = max(dot(x, x)-radius**2 for body in squares.values() for x in body)
    max_overlap_violation = max(mp.mpf(0), -min(mp.mpf(r['largest_separating_projection_gap']) for r in pair_rows))
    payload = {
        'status': 'exploratory_high_precision_candidate_not_a_proof',
        'case_id': 'C20-M06-L03-B02-T02', 'word': 'LSLSLD',
        'body_count': 6,
        'warning': 'No exact-root or interval existence certificate; not a ten-square packing or a completion bound.',
        'precision_decimal_digits': mp.mp.dps,
        'radius': string(radius), 'squared_radius': string(radius**2),
        'root_parameters': {key: string(d[key]) for key in ('u', 'v', 'z', 'ha', 'hb', 'p', 'q', 'r', 's')},
        'side_slide_parameters': {'S_A': '7/9', 'S_B': '1/7'},
        'equation_residuals': [string(x) for x in equations(radius, u, z)],
        'maximum_force_balance_residual': string(force_residual),
        'maximum_origin_torque_residual': string(torque_residual),
        'maximum_support_inequality_violation': string(support_residual),
        'maximum_contact_membership_violation': string(membership_residual),
        'maximum_vertex_squared_radius_excess': string(maximum_vertex_excess),
        'maximum_pair_overlap_projection_violation': string(max_overlap_violation),
        'squares': {name: {'vertices': [vector(x) for x in body],
                           'center': vector(scale(mp.mpf(1)/4, tuple(sum(x[j] for x in body) for j in range(2)))),
                           'minimum_squared_radius_slack': string(min(radius**2-dot(x, x) for x in body))}
                    for name, body in squares.items()},
        'contact_forces': [{'from': a, 'to': b, 'point': vector(point),
                            'unit_direction_from_to': vector(normal),
                            'positive_magnitude': string(magnitude)}
                           for a, b, point, normal, magnitude in contacts],
        'circle_loads': {name: {'point': vector(point), 'positive_coefficient': string(coefficient)}
                         for name, (point, coefficient) in circle.items()},
        'contact_square_coordinates': contact_coordinates,
        'pairwise_projection_checks': pair_rows,
    }
    out = ROOT/'one_diagonal_two_side_candidate.json'
    out.write_text(json.dumps(payload, indent=2)+'\n')
    print(f'Exploratory radius: {mp.nstr(radius, 20)}')
    print(f'Max force residual: {mp.nstr(force_residual, 8)}')
    print(f'Max torque residual: {mp.nstr(torque_residual, 8)}')
    print(f'Max pair overlap violation: {mp.nstr(max_overlap_violation, 8)}')
    print('Not an exact existence proof or a ten-square completion.')


if __name__ == '__main__':
    main()
