# Unrestricted polynomial model and a sharp exact row-family certificate

**Scope:** the emitter represents the unrestricted nine-square problem; the
certificate proves only the stated continuous four-over-three row subfamily.
**The unrestricted lower bound and complete equality classification remain OPEN.**
The source proof below and separately implemented exact arithmetic checks were
completed in this continuation. No separate human reviewer, Lean, or CI was used.

## 1. Original physical predicate

Write Q=1105/256. For i=0,...,8 take real center c_i=(x_i,y_i), unit first axis
u_i=(a_i,b_i), a_i^2+b_i^2=1, and v_i=(-b_i,a_i). Define the closed unit square

    S_i = c_i + [-1/2,1/2]u_i + [-1/2,1/2]v_i.

Every physical unit square has such a representation: an orthonormal frame
with negative determinant can be made positive by reversing one axis, without
changing the square. The containing disk can be translated to have center zero.
No relative square orientation, contact graph, circle load, or force is assumed.

The variable-radius formula asserts q>=0, 256q<1105, all nine unit-frame
equations, all 36 vertex-in-disk inequalities, and all 36 pair separations.
The 288 named definitions in the SMT text are substitutions, NOT new variables.

## 2. Vertex containment

For signs s,t in {-1,+1}, define doubled vertices

    X_i(s,t) = 2x_i+s a_i-t b_i,
    Y_i(s,t) = 2y_i+s b_i+t a_i.

The original vertex is (X_i/2,Y_i/2). Therefore its disk condition is exactly
X_i^2+Y_i^2<=4q. A square is the convex hull of its four vertices and a closed
disk is convex, so these four inequalities are equivalent to containment of
the entire square. No interior point or disk-boundary tangency is omitted.

## 3. Complete pair separation: a geometric proof

For one pair let w=c_j-c_i, and K_i=S_i-c_i, K_j=S_j-c_j. These centered squares
are centrally symmetric. Their interiors intersect after translation exactly
when w belongs to the interior of the planar convex polygon

    Z=K_i+K_j = sum_{g in {u_i,v_i,u_j,v_j}} [-1/2,1/2]g.

Here is an explicit justification of the interior assertion. The image of the
open coefficient cube under the linear map (r_g)->sum r_g g is open because
u_i,v_i are independent and their coefficients can be varied slightly. It is
therefore inside int Z. Conversely, any w in int Z has (1+epsilon)w in Z for
some epsilon>0 (w=0 is immediate). Scaling a closed-cube representation of
(1+epsilon)w by 1/(1+epsilon) puts all coefficients strictly between -1/2 and
1/2. Thus int Z is exactly the image of the open cube. Grouping the first two
and last two coefficients gives precisely a difference of square-interior
points, proving the assertion.

For a nonzero direction n, the exposed face of Z maximizes each independent
coefficient separately. A coefficient is fixed at an endpoint whenever n.g
is nonzero. A positive-length exposed edge thus requires n.g=0 for some
generator g. Consequently every facet normal of Z is parallel to one of
u_i,v_i,u_j,v_j. This remains true when some directions coincide. Intersecting
the supporting halfplanes of all its edges recovers Z; one way to see this is
that a point outside a convex polygon is excluded by at least one oriented
edge halfplane. Hence w is outside int Z exactly when one of the eight
directed axes +/-u_i,+/-v_i,+/-u_j,+/-v_j has

    n.w >= h_Z(n)
        = (|n.u_i|+|n.v_i|+|n.u_j|+|n.v_j|)/2.

Equality is deliberately allowed: it is disjointness of OPEN interiors,
not disjointness of the closed squares, that is required. This establishes
the finite-axis theorem needed here, including corner, side, parallel and
coincident-direction limits.

## 4. Absolute-value-free quadratic branches

Let

    C = u_i.u_j = a_i a_j+b_i b_j,
    S = v_i.u_j = a_i b_j-b_i a_j.

The other cross-products are u_i.v_j=-S and v_i.v_j=C. On any of the four unit
axes n, the two-square total projection width is (1+|C|+|S|)/2. If P=n.w,
separation is therefore 2|P|>=1+|C|+|S|. The elementary identity

    |C|+|S| = max_{s,t in {-1,+1}} (s C+t S)

makes this equivalent to the following polynomial Boolean formula:

    OR over n in {u_i,v_i,u_j,v_j}, sign in {-1,+1}:
        AND over s,t in {-1,+1}:
            2 sign*(n.w) >= 1+s C+t S.

The reverse implication is exact: if all four bounds hold for one sign and
axis, their maximum gives 2 sign*P>=1+|C|+|S|, hence the original separator.
The forward implication chooses a sign realizing |P|. Zero C or S gives
duplicate bounds, not a missing branch. No sign of an actual physical contact
normal is selected, and no generic normal-cone condition is used.

Thus each pair needs EIGHT alternatives of FOUR inequalities, with no abs,
conditional term, or auxiliary real variable. All polynomials after expanding
named definitions have degree at most TWO. This is a full disjunctive cover;
it does not claim that all 8^36 branch products are physically distinct or
that they have been enumerated or solved.

**Equivalence theorem.** The variable-radius emitter is satisfiable iff there
exists an unrestricted packing of nine interior-disjoint unit squares in a
disk with squared radius q<Q. This follows by Sections 1-4 in both directions.
The SMT text uses quantifier-free nonlinear real arithmetic (QF_NRA): official
format reference, https://smt-lib.org/logics-all.shtml#QF_NRA. The source proof
above, not an unexplained solver answer, supplies the geometric equivalence.

## 5. Sharp elimination of the radius and optional rotation gauge

There are finitely many vertices. Existence of q<Q with every norm squared
<=q is equivalent to EVERY vertex norm squared being strictly below Q: in
one direction compare to q; in the other choose q to be the maximum of those
36 nonnegative norms. Therefore the `strict` mode removes q and instead
asserts 64(X_i^2+Y_i^2)<1105 for every vertex. This is an equivalence for all
q<Q, not a Q-epsilon approximation. The `closed` control mode uses <= and
must accept the known attaining packing.

Optionally apply the single global rotation

    (x,y) -> (a_0 x+b_0 y, -b_0 x+a_0 y).

It sends u_0 to (1,0), preserves disk norms and intersections, and transforms
all nine bodies together. Thus substituting a_0=1,b_0=0 is equisatisfiable,
though not literally equivalent for a fixed unrotated coordinate assignment.
It discards no packing and asserts no individual-square alignment.

| Mode | Independent reals | Unit equations | Corner tests | Pair disjunctions | Assertions |
|---|---:|---:|---:|---:|---:|
| Variable q, no gauge | 37 | 9 | 36 | 36 | 83 |
| Strict or closed Q, no gauge | 36 | 9 | 36 | 36 | 81 |
| Variable q, gauge | 35 | 8 | 36 | 36 | 82 |
| Strict or closed Q, gauge | 34 | 8 | 36 | 36 | 80 |

All modes have 288 named polynomial definitions, and no stress variables.

Two useful universal preprocessing facts can also be proved without stress.
The maximum squared vertex norm is

    |c_i|^2+1/2+|c_i.u_i|+|c_i.v_i| >= |c_i|^2+1/2+|c_i|.

Since (91/60)^2+91/60+1/2-Q=31/57600>0, every contained center at q<=Q has
|c_i|<91/60. Also each square contains an open disk of radius 1/2 centered at
c_i, so pairwise disjoint interiors imply |c_i-c_j|>=1. These are legitimate
bounded-domain/search inequalities, not a sufficient criterion for packing;
they have NOT been silently inserted into the current emitter.

## 6. Exact emitted-text controls

`test_unrestricted_nine.py` does NOT import the emitter or its expression
objects. It invokes the program, independently parses all six emitted SMT
variants, verifies all labels/indices, and evaluates the text using Fraction.
It compares separation with exact convex-polygon intersection AREA using
halfplane clipping, not with the emitter's support formula. Finite tests are
regression evidence, not the proof of universal equivalence in Sections 1-4.

The attaining witness is transcribed from `rational_record_witness` in the
preexisting `emit_full_triangle_system.py` at source commit
`7669e24f889872b7fba4b6fc756bb209fd99acf9`; NO force data are reused:

    centers 0..3: (k/2,1/16), k=-3,-1,1,3;
    centers 4..6: (k,-15/16), k=-1,0,1;
    centers 7,8: (+/-11/20,19/16);
    first axes 0..6: (1,0); axes 7,8: (99/101,20/101).

All 36 pairs have zero interior intersection area. The maximum norm squared
is exactly Q, attained at corner indices (0,1),(3,3),(4,0),(6,2) in emitter
sign order. Closed-Q accepts it. Strict-Q rejects exactly those four corner
constraints. The variable-q model at q=Q fails ONLY its strict radius bound.
Rational rotation, reflection, and reverse relabeling preserve closed-Q
acceptance. The tests also reject overlapped squares 7,8, an escaped corner,
a nonunit frame, omission of a pair predicate and replacing >= by >.

The saved report records 744 exact pair comparisons and 1,488 exact containment
comparisons, including aligned tangencies and rational oblique frames. There
was no separate human review. The general SMT solver was not installed; a
package-install attempt failed because network name resolution was unavailable.
No general SMT SAT/UNSAT result, timeout, or proof object is claimed.

## 7. First proof-producing pilot: an entire continuous row profile

Assume, AFTER one legal common rotation and relabeling, squares 0,...,3 have
axis (1,0), a common center height A, and x_{k+1}-x_k>=1 for k=0,1,2.
Squares 4,5,6 have the same axis, common center height B, and x_5-x_4>=1,
x_6-x_5>=1. Require A-B>=1. Squares 7,8 remain arbitrary actual contained,
interior-disjoint units. Horizontal gaps, row offsets, heights and the last
two independent frames are NOT fixed. This is a continuous proper subfamily,
not a proved root covering arbitrary nine-square configurations.

Put

    lambda=23/32, nu=9/32,
    X=(x_0+x_3)/2, Z=(x_4+x_6)/2,
    s=x_3-x_0-3 >=0, t=x_6-x_4-2 >=0, r=A-B-1 >=0,
    H=lambda*(A+1/2)+nu*(B-1/2).

Take four original disk slacks, each >=0:

    h01=q-(x_0-1/2)^2-(A+1/2)^2,
    h33=q-(x_3+1/2)^2-(A+1/2)^2,
    h40=q-(x_4-1/2)^2-(B-1/2)^2,
    h62=q-(x_6+1/2)^2-(B-1/2)^2.

The exact certificate is the polynomial identity

    q-Q = (lambda/2)*(h01+h33)+(nu/2)*(h40+h62)
          +lambda*X^2+nu*Z^2+H^2
          +(lambda/4)*s^2+(nu/4)*t^2+lambda*nu*r^2
          +2*lambda*s+(3*nu/2)*t+4*lambda*nu*r.

Every term on the right is nonnegative. Expanding s and t as sums of original
consecutive-gap slacks yields TEN nonnegative hypothesis multiples and SIX
positively weighted squares. Therefore this ENTIRE family satisfies q>=Q,
with no epsilon and no positive-force premise. The original two extra units
are retained; the necessary seven-body argument simply does not need their
constraints. It does not change their positions or claim the core cannot fit
at q=Q.

### How the exact weights are produced

The four upper/lower extreme corners have horizontal halfspans at least 2
and 3/2, and their vertical coordinates differ by at least 2. A weighted
variance bound with weight z gives

    4z+(9/4)(1-z)+4z(1-z) = 9/4+(23/4)z-4z^2.

Its exact maximum is at z=23/32 and equals 1105/256. The generator computes
these rational weights and serializes the identity. The independent checker
constructs the physical row hypotheses itself, reads only the coefficient
data, checks every weight is nonnegative, and expands the whole identity by
sparse rational polynomial arithmetic. The residual has ZERO monomials. It
imports neither the generator, the model emitter, nor a symbolic algebra
library. A changed coefficient and a stronger fake target are rejected.

### Equality within THIS row family

At q=Q every displayed nonnegative term vanishes. Thus X=Z=H=s=t=r=0.
Each individual consecutive-gap slack is zero since it is nonnegative and
its row sum is zero. Consequently

    (x_0,x_1,x_2,x_3)=(-3/2,-1/2,1/2,3/2),
    (x_4,x_5,x_6)=(-1,0,1), A=1/16, B=-15/16.

This forces the seven-row core within this chart. The two other squares may
have any poses satisfying their original disk and nonoverlap inequalities;
the witness above supplies one allowed oblique pair. This is NOT the complete
equality classification of all packings, nor a reduced parameterization of
every allowed pose of those two squares.

## 8. Files, reproduction and remaining work

Run from `research/nine/computer_assisted/`:

```sh
python emit_unrestricted_nine.py --radius variable --output /tmp/n9-variable.smt2
python emit_unrestricted_nine.py --radius strict --gauge --output /tmp/n9-strict.smt2
python test_unrestricted_nine.py
python make_row43_certificate.py > /tmp/row43.json
python verify_row43_certificate.py /tmp/row43.json
```

The two saved reports record the actual executions and source/certificate
hashes. This supplies the requested D.1 emitter/equivalence/controls and one
exact continuous-family pilot. It does NOT establish D.4, Q, or E. The next
active task is D.3.c: obtain a transferable bound that handles unrestricted
relative orientations, or give an explicit limitation/pivot of the direct
certificate approach. Do not subdivide the already solved exact row profile
into more checkboxes, and do not revive historical case-count progress.
