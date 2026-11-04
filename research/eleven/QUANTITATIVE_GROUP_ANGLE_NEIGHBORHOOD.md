# A quantitative angle terminal for the candidate contact class

This strengthens the fixed-orientation theorem. It permits the two group
angles to vary in an explicit closed neighborhood, with **arbitrary centers**.
It assumes the fourteen prescribed separating halfspaces, not merely the
three orientation groups. It does not supply global capture of a packing
into this contact class or prove the unrestricted n=11 lower bound.

Use the exact candidate `(qc, ta*)` and its derived `tb*=tan(beta*/2)` from
`CANDIDATE_CONTACT_SYSTEM.md`. The groups are squares 0 through 6 at angle
zero, squares 7 and 8 at angle alpha, and squares 9 and 10 at angle beta.
Put `ta=tan(alpha/2)` and `tb=tan(beta/2)`.

**Theorem.** Suppose every square vertex is in the disk of squared radius q,
and the fourteen signed owner halfspaces in `FIXED_ORIENTATION_STRESS.md`
hold. If

```
d = max(|ta-ta*|, |tb-tb*|) <= 1/2000,
```

then

```
q >= qc + (1/40 - 40d)d.
```

Consequently q >= qc, and q=qc forces both angles to equal the exact candidate
angles. For an actual packing, the fixed-orientation equality theorem then
forces precisely the established slider family.

The quantitative inequality applies at d=0 as well. The displayed expression
is strictly above qc whenever 0<d<=1/2000. No closeness hypothesis is imposed
on the centers, and no limiting-sequence argument is needed for this terminal.

## Weak dual valid for arbitrary centers

Assign nonnegative weights lambda to the ten listed disk corners, with sum
one, and nonnegative weights mu to the fourteen separator inequalities. For
square i, let `Li` be its total corner weight, `Vi` the weighted sum of its
corner offsets from its center, and `Ki` the net separator force: an outgoing
edge with signed normal n contributes `-mu*n`, and an incoming edge contributes
`+mu*n`. If `Li=0`, require `Ki=0`. Since every corner offset has squared norm
1/2, completing a square gives

```
q >= D(ta,tb)
D = 1/2 + sum_edges mu*support
            - sum_{Li>0} |Ki-2Vi|^2/(4Li).
```

Indeed the weighted sum of all assumed nonnegative slacks equals

```
q - D - sum_{Li>0} Li*|pi - (Ki-2Vi)/(2Li)|^2.
```

Only squares 1, 4 and 8 have zero disk weight. Their forces vanish at every
angle pair if the edge weights in the established edge order obey

```
mu01 = mu14 = mu45 = A,
mu34 = mu48 = B,
mu78 = B*cos(beta)/cos(beta-alpha),
mu89 = B*sin(alpha)/cos(beta-alpha).
```

All other edge weights can remain constant. These formulas follow by resolving
`B*ex = mu78*u_alpha - mu89*v_beta` into its coordinates. The entire certified
neighborhood has `0<alpha<beta<pi/2` and `cos(beta-alpha)>9/10`, so all adjusted
weights remain nonnegative. The eight positive disk totals belong to labels
0,2,3,5,6,7,9,10.

## Four exact stresses with opposite angular slopes

Let J be the previously certified 24 by 24 active-constraint Jacobian, with
columns: the twenty-one center coordinates other than square 1's horizontal
coordinate, ta, tb, and q. Reconstruct the same J directly from the exact
contact family. For each `k in {ta,tb}` and `s in {-1,+1}`, solve

```
J^T w(k,s) = e_q + (s/40)e_k.
```

Exact outward rational elimination proves J invertible and every component
of all four solutions greater than 1/1000. The q row gives sum(lambda)=1;
the center rows give force balance at the exact candidate. The omitted center
row is identically zero, because its square has no disk corner and its two
incident separator normals are vertical. Thus the symbolic relations above
hold for each exact stress at the candidate.

Extend each stress to nearby angles by the displayed force-balance formulas,
keeping A, B, the ten lambdas, and the other edge weights constant. This
produces four valid dual functions D(k,s). They obey the exact identities

```
D(k,s)(ta*,tb*) = qc,
grad D(k,s)(ta*,tb*) = -(s/40)e_k.
```

The first identity is the equality case of the weighted square completion.
For the second, differentiate the minimized quadratic weighted expression.
Center derivatives vanish by stationarity. Derivatives of the varying edge
weights multiply separator slacks, all of which vanish at the candidate.
The remaining derivative is minus the specified angular row of `J^T w`.
Thus no interval equality test or floating approximation is used for either
identity.

## Exact second derivative bound and Taylor inequality

`check_angle_neighborhood.py` uses two-variable automatic differentiation
through second order, with every arithmetic operation rounded outward to a
rational grid of denominator 10^30. It encloses the entire angle rectangle
formed by extending both exact root coordinate enclosures by 1/2000.
All Hessian entries of each D(k,s) have absolute value strictly below 20 on
that rectangle. The rectangle is convex and contains every segment from the
exact root to a point with d<=1/2000.

Choose a coordinate k for which the absolute coordinate displacement is d,
and choose s so the corresponding linear term is `d/40`. Taylor's theorem
with the integral remainder gives

```
D(k,s)(ta,tb) >= qc + d/40 - (20/2)(|delta_ta|+|delta_tb|)^2
             >= qc + d/40 - 40d^2.
```

The strict numerical comparison `40/2000 < 1/40` is rational. Combining the
chosen dual bound with q>=D proves the theorem.

## Reproduction and remaining gates

Run without optimization, using only the Python standard library:

```
python research/eleven/check_angle_neighborhood.py
```

The script imports the existing root certificate and rational interval solver.
Previously audited files are unchanged. Its auxiliary interval Hessian class
implements the product rule and the exact reciprocal formulas
`(1/f)'=-f'/f^2` and
`(1/f)''_ij=2 f'_i f'_j/f^3-f''_ij/f^2`.

Remaining tasks are to cover the rest of the grouped-angle domain and,
separately, to prove that every competing unrestricted packing enters an
already solved contact class or another solved finite terminal. The result
here closes an explicit contact-class terminal near the exact angles, not
those remaining global gates.
