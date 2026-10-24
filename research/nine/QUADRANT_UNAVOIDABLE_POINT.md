# n=9 QCAP: a quadrant of D_(17/4) holds at most one unit square

**Status:** complete hand derivation of the stated all-orientation capacity theorem; independent audit and Lean verification pending. This is a terminal geometric tool, **not** a proof of P.ALL, Y.ALL, CYCLIC or unrestricted n=9 optimality. No radial terminal obstacles or common pairwise separating axes are assumed.

**Read base:** PR #11 head 59d0c95092a01a575a3fc078ab5c6db54107d4fc. The exact corner formula is the existing physical square model.

## 1. Theorem and stronger point statement

Let D be the disk centered at zero of squared radius 17/4. Every closed unit square T contained in D and in the closed first quadrant contains p=(1,1).

- If T is not axis-aligned, p belongs to its **open interior**.
- If T is axis-aligned, p-epsilon*(1,1) belongs to int(T) for all sufficiently small positive epsilon.

Consequently **at most one** unit square can lie wholly in that quadrant with pairwise disjoint open interiors. Rotation gives the same result for every closed right-angle cone with vertex at the disk center. It also applies to every smaller disk.

The one-square claim concerns an arbitrary individual orientation, not a preselected horizontal/vertical packing class. A square crossing a cone boundary is not covered by this capacity theorem.

## 2. Exact coordinates

Use square quarter-turn symmetry and, if needed, interchange the ambient x and y coordinates (which preserves the quadrant and p). The square's unit side vectors can then be written

    u=(a,b), v=(-b,a),  1>=a>=b>=0, a^2+b^2=1.

Write

    w=a+b, d=a-b, h=w/2,
    c=(x,y), t=c.u=a*x+b*y, z=c.v=-b*x+a*y.

Quadrant containment is exactly x>=h and y>=h. Thus t>=w*h=w^2/2>=1/2. Disk containment is exactly

    F=(t+1/2)^2+(|z|+1/2)^2 <= 17/4.                 (1)

In these side coordinates p has coordinates (w,d). Therefore p belongs to T exactly when

    w-1/2 <= t <= w+1/2,
    d-1/2 <= z <= d+1/2.                            (2)

We prove all four bounds, keeping track of strictness.

## 3. The two u-coordinate bounds

Since t>=w^2/2,

    w-t <= w-w^2/2 = 1/2-(w-1)^2/2 <= 1/2.          (3)

If b>0 then w>1 and this bound is strict.

For the other bound, suppose t>=w+1/2. Equation (1) would give

    F >= (w+1)^2+1/4 >= 17/4.

Equality in both inequalities would require w=1, t=3/2 and z=0. But w=1 implies a=1,b=0, hence z=y>=1/2, a contradiction. Thus in all orientations

    t < w+1/2.                                     (4)

## 4. The lower v-coordinate bound

If b=0, then a=1, d=1 and z=y>=1/2=d-1/2, as required.

Suppose b>0 and z<=d-1/2. Because y=b*t+a*z>=h,

    t >= (h-a*z)/b
      >= (h-a*(d-1/2))/b
       = 3/2 + b*(a-b)/(1+a).                       (5)

The final identity uses a^2+b^2=1. If a>b, (5) gives t>3/2, and (1) gives F>17/4. If a=b, (5) gives t>=3/2 and z<=-1/2, so F>=5. Both alternatives contradict (1). Therefore every non-axis-aligned square satisfies

    z > d-1/2.                                     (6)

## 5. The upper v-coordinate bound

Suppose z>=d+1/2. In particular z>0. From x=a*t-b*z>=h we obtain

    t >= (h+b*z)/a
      >= (h+b*(d+1/2))/a
       = 1/2+b+a*b/(1+b).                          (7)

Adding z>=d+1/2 gives

    t+z >= 1+a+a*b/(1+b) >= 2.                     (8)

Here the last inequality is exactly

    a*(1+2*b) >= 1+b.

Both sides are nonnegative, and its squared difference factors as

    a^2*(1+2*b)^2-(1+b)^2
       = 2*b*(1+b)*(1-2*b^2) >= 0,                 (9)

since a>=b and a^2+b^2=1 imply b^2<=1/2.

Equations (7)--(8) and the elementary sum-of-squares inequality give

    F=(t+1/2)^2+(z+1/2)^2
      >= (t+z+1)^2/2 >= 9/2 > 17/4,

a contradiction. Therefore

    z < d+1/2.                                    (10)

## 6. Interior and boundary conclusions

For b>0, all four inequalities (2) are strict by (3), (4), (6) and (10). Hence p is in int(T).

For b=0, the square is axis-aligned. We have x,y>=1/2 and x,y<3/2 by (1). Its two lower edges are strictly below/left of p, while its upper/right edges are at or beyond p. Thus p-epsilon*(1,1) is in int(T) whenever epsilon>0 is sufficiently small.

For any two squares satisfying the hypotheses, choose epsilon sufficiently small for both. In the tilted cases p itself is interior, so small perturbations also remain interior. In the aligned cases use the preceding boundary calculation. The same point p-epsilon*(1,1) lies in both open interiors, contradicting packing nonoverlap. This proves the capacity-one theorem. QED.

The conclusion is sharp as a count: [0,1]^2 is one admissible square. The point claim is stronger than the earlier radial right-pocket lemma in that it needs no radial boundary-terminal obstacles; unlike that earlier lemma, it does not claim the single square must equal [0,1]^2.

## 7. Global and family-specific scope

- **QCAP.1 CLOSED hand:** the one-square unavoidable-point statement and all four coordinate inequalities are proved over the entire angle range.
- **QCAP.2 CLOSED hand:** every origin-centered right-angle cone has physical unit-square capacity at most one in D_(17/4).
- **QCAP.3 CLOSED necessary consequence:** in any nine-square packing in D_(17/4), for every perpendicular frame at least five squares have open interiors meeting at least one of its two coordinate lines. Otherwise five squares avoid the two lines, each is wholly in one quadrant, and two occupy the same quadrant. This is a necessary condition, not a contradiction.
- **P.ALL and Y.ALL remain OPEN:** a unit square can cross the quadrant boundaries, and the current skeletons do not universally place each added square into one of a prescribed collection of quadrant cells. The missing routing/capacity argument must be proved; it is not implicit in QCAP.
- **CYCLIC remains OPEN:** no contact-graph applicability claim follows from the quadrant theorem alone.

## 8. Validation boundary

The proof is symbolic: equations (3), (5), (7) and (9), plus exact corner containment and a common interior-point argument. A separate exact regression script checks the displayed identities and representative rotated and boundary squares, but finite poses are not a premise of the all-angle theorem. No independent full audit, Lean compilation, CI or unrestricted n=9 lower bound is claimed.