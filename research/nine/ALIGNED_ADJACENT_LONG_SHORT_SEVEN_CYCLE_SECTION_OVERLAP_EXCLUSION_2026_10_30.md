# Aligned adjacent long/short cycles force overlapping actual sections

**Date:** October 30, 2026 UTC.
**Status:** complete proposed continuous family exclusion, awaiting full
independent review. The exact section-overlap argument was developed by
the root agent and reconstructed here. Tilted long endpoints remain open.

Put `Q=1105/256`, `z=5/4`, and `g(Y)=sqrt(Q-Y^2)`.
All squares and contacts below are the original actual objects.

## 1. A force-free asymmetric return-section obstruction

Let actual unit squares C,D have disjoint open interiors and be contained
in a centered disk with `2<=R<=sqrt(Q)`. Assume the following geometric
conditions for numbers `f_A,f_B,x`:

    3/8<=f_A,f_B<=1/2,
    f_A+f_B>=7/8,
    x<61/60.                                         (1)

The unit C physically touches the containing circle, and its center
direction lies in `(75 degrees,105 degrees)`. The line `y=z` lies
strictly between D's horizontal supporting lines, giving an actual
interior section with right endpoint r_D. Assume

    (c_D)_x<-1/2,
    r_D>=1-g(f_A+1).                                 (2)

Finally suppose one actual unit direction `n=(-alpha,beta)`, with
`alpha,beta>0`, satisfies the physical support inequality

    n.c >= n.(x,f_B)+1 for every actual point c in C.  (3)

No force equation, unit orientation, contact ownership, or location of
an intermediate square is assumed in this geometric statement.

**Theorem 1 (strict asymmetric section obstruction).** Conditions
(1)--(3) are impossible. They force the right endpoint of D's section
to exceed the left endpoint of C's section by more than `13/480`,
although the actual physical interval order requires the reverse.

### 1.1 Actual section width and order

The complete one-unit near-vertical calculation gives

    C subset {y>83/160},
    length(C intersect {y=z})>=1,
    (0,z) in int(C).                                 (4)

These statements hold for every physical-boundary unit in the stated
sector and radius window. They are proved in Sections 2--3 of
`THREE_BOUNDARY_RETURNS_FORCE_A_HIGH_MIDDLE_UNIT_AND_A_UNIT_SECTION_2026_10_30.md`
and are explicitly restated for one unit in Section 1 of the later
three-return ordering source. No three-return or graph hypothesis is
needed for (4). Its numerical inputs are
`31/24<|c_C|<91/60`, `sin(theta)>19/20`, and the exact incircle
bound `|c_C-(0,z)|^2<401/1800<(19/40)^2`.

For any actual unit square, a horizontal interior section contains a
point with x coordinate in `[c_x-1/2,c_x+1/2]`. Indeed join the
bottom and top support vertices; their horizontal offsets from the
center have magnitude at most one half, and the joining segment lies
in the square. For an aligned square use the supporting-side midpoints.
Thus (2) gives a negative point in D's actual section.

The section of C contains zero in its open interval by (4). The two
open section intervals are disjoint, because their points are in the
original square interiors. D's section therefore cannot lie to the
right of C's section. Hence its actual order is

    I_D on the left, I_C on the right,
    r_D<=ell_C.                                      (5)

This argument proves the interval order from actual contained points;
it does not infer it from center-angle order alone.

### 1.2 The actual short support puts the entire C section to the left

Put `k=z-f_B`, so `3/4<=k<=7/8`. For every section point `(X,z)`
of C, equation (3) gives

    -alpha*X+beta*z >= -alpha*x+beta*f_B+1,
    X<=x+(beta*k-1)/alpha.                            (6)

The exact identity

    (1-beta*k)^2-alpha^2*(1-k^2)=(beta-k)^2>=0

has positive quantities on both sides before squaring. Hence

    r_C<=x-sqrt(1-k^2).

By (4), the full section width `r_C-ell_C` is at least one.
Therefore

    ell_C<=x-sqrt(1-k^2)-1.                          (7)

Equation (7) is a statement about the actual full section. It does
not assign a floor or a guessed frame to C.

### 1.3 The coupled floors force an exact positive overlap

From (1),

    f_A+1>=15/8-f_B=k+5/8.

Since g decreases on this positive interval,

    g(f_A+1)<=g(k+5/8).

Consider the whole-interval function

    H(k)=g(k+5/8)-sqrt(1-k^2), 3/4<=k<=7/8.

Its derivative is strictly positive. Clearing its positive square-root
denominators and squaring is equivalent to

    Q*k^2>(k+5/8)^2,

which holds because `Q>4` and `k>5/8`. Thus

    H(k)<=H(7/8)=23/16-sqrt(15)/8
                 <23/16-77/160=153/160.              (8)

The strict radical bound uses `(77/20)^2<15`.
Combining (2), (7), and (8) yields

    r_D-ell_C
      >=2-x-g(f_A+1)+sqrt(1-k^2)
      >=2-x-H(k)
      >2-61/60-153/160
       =13/480>0.                                   (9)

This contradicts (5). Every floor endpoint, section-edge case and
actual normal direction in the stated domain is included. Theorem 1
is proved.

## 2. Complete aligned adjacent long/short seven-cycle exclusion

Retain one complete physical force-and-torque certificate containing
the original positive simple cycle

    A -- U -- V -- B -- W -- C -- D -- A.             (10)

The actual marked units A,B,C,D physically touch the containing circle.
The internal units U,V,W are unloaded and have full true positive degree
two in the same certificate. A and B also have full true positive degree
two. C,D may have arbitrary additional positive edges. The original
cycle has the compatible physical routing and circle spokes required
by the adopted marked-order theorem. Every other physical packing unit
and all its restrictions remain present.

Rotate about the unchanged disk center so the signed long normal is
e_x. **Assume both long endpoints A,B are aligned in this frame.**
No alignment is assumed at C,D,W, and no endpoint or internal mean is
identified with a center.

**Theorem 2 (whole aligned adjacent branch excluded).** There is no
such unchanged physical configuration with `q<=Q`. This excludes the
entire aligned-long-endpoint branch of run counts `(2,1,0,0)`, even
at the target radius, while retaining all completing physical units.

### 2.1 The imported adjacent reduction is literal

The complete frozen input is

`ADJACENT_LONG_SHORT_CYCLE_ORIGINAL_NORMAL_CONE_AND_ENDPOINT_VERTEX_REDUCTION_2026_10_30.md`,
SHA256 `9884cab15c74c2e15e44ad05c5d1665c93a46244aa7321c2b4a8c1675e65611b`.

It retains every original full star and proves the following facts in
exactly the domain (10). The actual long normal chords imply `R>=2`,
so the boundary-angle radius window is derived, not assumed. After one
common reflection both entire C,D lie in `y>1/120`, and their actual
center directions satisfy

    88 degrees<arg(c_C)<103 degrees,
    129 degrees<arg(c_D)<144 degrees.                 (11)

The original short normal from B through W to C has the strict global
form `n=(-alpha,beta)` with both components positive. Its actual B--W
mean is B's upper-inner vertex even though W may be circle-clear.
No physical boundary status is assigned to W.

The full endpoint equations give nonpositive endpoint center heights
in the aligned branch, retaining both physical circle corners when an
endpoint has zero center height. With their actual upper-side heights
`f_A=y_A+1/2`, `f_B=y_B+1/2`, the coupled long-pair bound gives

    f_A,f_B in [3/8,1/2], f_A+f_B>=7/8.               (12)

Write the unchanged long means as `(s-1,t),(s,t),(s+1,t)`.
The actual B--W point is

    p_B=(s+1,f_B), |s|<1/60.                         (13)

Thus `x=s+1<61/60` satisfies the last condition in (1).

### 2.2 C supplies its genuine section and D supplies the opposite profile

The first angle interval in (11) is inside `(75,105 degrees)`.
Consequently the actual C has all properties in (4), with no change
to its own frame or support data. It is its physical boundary contact,
not a hypothetical cap placement, that supplies this near-vertical
section.

For D, its physical boundary center radius is at least
`R-1/sqrt(2)>5/4`. Its angle is greater than 129 degrees, hence
greater than 120 degrees. Therefore

    (c_D)_x<-(1/2)*(5/4)=-5/8<-1/2.                  (14)

Its actual contact with aligned A is covered by the complete above-side
boundary contact locus. The complete unequal-floor profile and the
corner-wrapper theorem, reflected from the right endpoint to the left,
give a section strictly between D's horizontal supporting lines and

    r_D>=1-g(f_A+1).                                 (15)

If D passes below A's upper side the wrapper theorem supplies this
strictly, using its actual side parameter. If D stays above that side,
the full floor theorem applies. This step does not assume a vertical
original A--D normal or a common orientation of A,D.

### 2.3 W supplies the original whole-support gap

The original full unloaded degree-two equation at W propagates the
same n along B--W--C. Summing its two actual support equalities gives
the gap from B to C equal to the actual width of W in direction n.
That width is at least one, regardless of W's orientation. B's actual
support point in this normal is precisely (13). Thus every original
point c in C satisfies

    n.c>=n.p_B+width_W(n)>=n.p_B+1.                  (16)

This is exactly condition (3), with its unchanged normal. It does not
infer a common return frame or discard any original force at B or W.

Equations (11)--(16) supply every geometric premise of Theorem 1.
The strict overlap reserve `13/480` contradicts the actual nonoverlap
of C,D. This proves Theorem 2 over the entire aligned branch.

## 3. Scope, exact diagnostic and remaining work

The geometric obstruction in Section 1 can be reused whenever the
same one-unit sector, actual opposite section profile, coupled floor
budget and original support inequality are established. It is not
restricted to one short-normal angle or one side-owned contact type.

The cycle caller permits arbitrary positive degree at C,D and retains
every other actual packing square. Its conclusion is stronger than a
below-target obstruction: the aligned adjacent family is impossible
also at Q. No equality packing is removed from a different run orbit.

The six-unit diagnostic in the frozen adjacent input remains valid.
It supplies neither the missing boundary D with its actual contact
and section nor the complete remaining endpoint equations. The proof
here uses precisely that missing return geometry, so it does not
contradict the diagnostic or treat it as a complete seven-cycle.

The tilted long-endpoint branch is explicitly not covered by Theorem 2.
The original adjacent reduction proves its contact vertices and normal
cones, but does not align its endpoints. The section profile at the
other return must not be imported with a fictitious horizontal endpoint
side. No whole adjacent-C7 or unrestricted nine-square closure is claimed
from this aligned conditional theorem alone.

## 4. Additional frozen inputs and verification boundary

- `THREE_BOUNDARY_RETURNS_FORCE_A_HIGH_MIDDLE_UNIT_AND_A_UNIT_SECTION_2026_10_30.md`,
  SHA256 `99c6d7fc3bb50cf65f8ee36ef1e041dafb344671a5a09830e691746ef1f7f528`:
  the one-unit near-vertical calculation and full section width.
- `UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md`,
  SHA256 `abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94`:
  every above-floor orientation and exact right-section profile.
- `ALIGNED_ENDPOINT_CORNER_WRAPPERS_OBEY_THE_UNEQUAL_FLOOR_SECTION_BOUND_2026_10_30.md`,
  SHA256 `55607f2ab5a25c056fcc12e893b3d4c7e60814c6d2e607c21b806277d29de5bc`:
  actual below-floor returns and their complete contact cover.
- `LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md`,
  SHA256 `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`:
  the literal A--D boundary contact locus.

All interval, derivative, radical and support comparisons are exact.
The proof uses no numerical pose search, orientation grid, altered
certificate, removed physical unit, original ledger mutation, Lean
compilation, CI run or remote publication. Full independent review is
required before adoption.
