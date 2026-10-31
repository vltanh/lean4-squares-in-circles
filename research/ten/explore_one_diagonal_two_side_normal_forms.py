#!/usr/bin/env python3
"""Explore the whole unique-D-endpoint equation table numerically.

NOT a proof, root-isolation certificate, or exhaustive root enumeration.
The support table is exact; floating point roots merely guide subsequent
exact algebra/interval work. No transmitter placements or ten-square
completions are certified here.
"""
import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import least_squares

K = 2 + np.sqrt(2.)
LOW, HIGH = 79/40, 3/np.sqrt(2.)


def cross(a, b):
    return a[0]*b[1]-a[1]*b[0]


def model(x, endpoint_types, source_type):
    radius, fraction_u, fraction_z = x
    umax = np.sqrt(radius*radius-.25)
    u = K-umax+fraction_u*(2*umax-K)
    v = K-u
    ha = np.sqrt(max(.25, radius*radius-u*u))
    hb = np.sqrt(max(.25, radius*radius-v*v))
    zlo, zhi = max(0., ha-1, hb-1), min(ha, hb)
    z = zlo+fraction_z*(zhi-zlo)
    normals, contacts, magnitudes = [], [], []
    for distance, height, kind, sign in (
            (u, ha, endpoint_types[0], 1),
            (v, hb, endpoint_types[1], -1)):
        if kind == 'V':
            ratio = ((distance*z-height*(distance-1)) /
                     max(1e-14, height*(1-height+z)))
            vertical = 1/np.sqrt(1+ratio*ratio)
            horizontal = ratio*vertical
            contact = np.array([sign*(1-distance), 1-height])
        else:
            horizontal, vertical = 0., 1.
            contact = np.array([-sign*distance*z/height, 1-height])
        normal = np.array([sign*horizontal, vertical])
        normals.append(normal)
        contacts.append(contact)
        magnitudes.append(height/(distance*vertical-height*horizontal))
    na, nb = normals
    pa, pb = contacts
    qa, qb = pa+na, pb+nb
    delta = qb-qa
    if source_type == 'E_A':
        e, m = np.array([na[1], -na[0]]), na
        left = qb-e
        contact_equation = np.dot(na, delta)
    elif source_type == 'E_B':
        e, m = np.array([nb[1], -nb[0]]), nb
        left = qa
        contact_equation = np.dot(nb, delta)
    else:
        length = max(1e-14, np.linalg.norm(delta))
        e = delta/length
        m = np.array([-e[1], e[0]])
        left = qa
        contact_equation = length-1
    upper_left, upper_right = left+m, left+e+m
    g = magnitudes[0]*na+magnitudes[1]*nb
    return dict(radius=radius, u=u, v=v, ha=ha, hb=hb, z=z,
                normals=normals, contacts=contacts, magnitudes=magnitudes,
                qa=qa, qb=qb, delta=delta, e=e, m=m, left=left,
                upper_left=upper_left, upper_right=upper_right, g=g,
                contact_equation=contact_equation)


def equations(x, endpoint_types, source_type, circle_type):
    d = model(x, endpoint_types, source_type)
    ul, ur, radius = d['upper_left'], d['upper_right'], d['radius']
    if circle_type == 'radial':
        return [d['contact_equation'], np.dot(ul, ul)-radius*radius,
                np.dot(ur, ur)-radius*radius]
    w = ul if circle_type == 'left' else ur
    return [d['contact_equation'], np.dot(w, w)-radius*radius,
            cross(w, d['g'])]


def valid(d, endpoint_types, source_type, circle_type, tol=2e-7):
    na, nb = d['normals']
    if min(d['ha'], d['hb']) <= .5+1e-7:
        return False
    if not (0 <= na[0] < na[1] and 0 <= -nb[0] < nb[1]):
        return False
    if min(d['magnitudes']) <= 0 or d['e'][0] <= 0 or d['m'][1] <= 0:
        return False
    if not (na@d['e'] >= -tol and nb@d['e'] <= tol):
        return False
    if min(na@d['m'], nb@d['m']) <= 0:
        return False
    for point, distance, kind, sign in zip(d['contacts'],
            (d['u'], d['v']), endpoint_types, (1, -1)):
        alpha = 1-distance-sign*point[0]
        if not (-tol <= alpha < 1):
            return False
    delta_length = np.linalg.norm(d['delta'])
    if not (tol < delta_length <= 1+tol):
        return False
    if source_type == 'V_V' and min(na@d['e'], -nb@d['e']) <= tol:
        return False
    vertices = [d['left'], d['left']+d['e'],
                d['upper_left'], d['upper_right']]
    if max(w@w for w in vertices) > d['radius']**2+tol:
        return False
    if circle_type == 'radial':
        weights = np.linalg.solve(np.column_stack(
            [d['upper_left'], d['upper_right']]), d['g'])
        if min(weights) < -tol:
            return False
    else:
        w = d['upper_left'] if circle_type == 'left' else d['upper_right']
        if w@d['g'] <= 0:
            return False
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--starts', type=int, default=40)
    parser.add_argument('--seed', type=int, default=20261031)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    rows = []
    for endpoints in ('VV', 'EV', 'VE'):
        for source in ('E_A', 'E_B', 'V_V'):
            for circle in ('left', 'right', 'radial'):
                roots = []
                for _ in range(args.starts):
                    start = [rng.uniform(LOW, HIGH), rng.uniform(.05, .95),
                             rng.uniform(.1, .9)]
                    result = least_squares(equations, start,
                        bounds=([LOW, 1e-9, 1e-9], [HIGH, 1-1e-9, 1-1e-9]),
                        args=(endpoints, source, circle), max_nfev=200,
                        ftol=1e-11, xtol=1e-11, gtol=1e-11)
                    if max(abs(result.fun)) > 1e-7:
                        continue
                    d = model(result.x, endpoints, source)
                    if not valid(d, endpoints, source, circle):
                        continue
                    root = np.array([d['radius'], d['u'], d['z']])
                    if any(np.linalg.norm(root-r['parameters']) < 1e-5 for r in roots):
                        continue
                    roots.append(dict(parameters=root.tolist(),
                        residual=float(max(abs(result.fun))),
                        source_center=(d['left']+(d['e']+d['m'])/2).tolist(),
                        normals=[n.tolist() for n in d['normals']],
                        source_edge_length=float(np.linalg.norm(d['delta']))))
                rows.append(dict(endpoints=endpoints, source=source,
                                 circle=circle, roots=roots))
                print(endpoints, source, circle, len(roots), flush=True)
    payload = dict(status='exploratory_not_exhaustive_not_a_proof',
        warning='No exact roots, parameter coverage, nonoverlap, or completion certified.',
        seed=args.seed, starts_per_row=args.starts, rows=rows)
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2)+'\n')
    else:
        print(json.dumps(payload, indent=2))


if __name__ == '__main__':
    main()
