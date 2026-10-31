# Three-return section order and a sharp completion theorem for aligned long pairs

**Date:** October 30, 2026 UTC.
**Status:** complete proposed continuous geometric family theorem and full-
force caller, awaiting independent review. Tilted long endpoints remain
a separate obligation.

All squares are actual closed unit squares with pairwise disjoint open
interiors. Put `Q=1105/256`, `M=91/60`, and `z=5/4`.

## 1. Reusable one-unit consequence of the near-vertical sector

Suppose `2<=R<=sqrt(Q)` and an actual physical-boundary unit T has
center direction theta in `(75 degrees,105 degrees)`. The calculations
in Sections 2--3 of the frozen source

`THREE_BOUNDARY_RETURNS_FORCE_A_HIGH_MIDDLE_UNIT_AND_A_UNIT_SECTION_2026_10_30.md`
(SHA256 `99c6d7fc3bb50cf65f8ee36ef1e041dafb344671a5a09830e691746ef1f7f528`)
give the following implications directly:

    T subset {y>83/160},
    length(T intersect {y=z})>=1,
    the closed radius-1/40 disk about (0,z) is in int(T). (1)

The section length is strict if T is not axis aligned. These one-unit
conclusions need only the stated sector, physical boundary status and
radius bounds; the three-return hypothesis in the input is one way of
deriving the sector, not an additional hypothesis for (1).

For clarity, the numerical inputs are `31/24<|c_T|<91/60`,
`sin(theta)>19/20`, and then the stronger `sin(theta)>24/25` for
the incircle calculation. They give minimum height above `83/160` and
`|c_T-(0,z)|^2<401/1800<(19/40)^2`. The full unit-section formula
is proved over every actual unit wholly above height `3/8` in Section 1
of the cited source. No graph or force equation enters (1).

## 2. Every horizontal section has a point in the central vertical band

**Lemma 1.** If an actual unit square with center `(c_x,c_y)` has a
nondegenerate horizontal section with endpoints ell,r, then

    r>=c_x-1/2, ell<=c_x+1/2.                         (2)

To prove this, join its bottom and top supporting vertices. In any own
side description, their horizontal offsets from the center have absolute
value at most `|a-b|/2<=1/2`, where a,b are the nonnegative absolute
side coefficients. The joining segment lies in the square by convexity.
At every height strictly between the supporting heights it gives an
actual section point in `[c_x-1/2,c_x+1/2]`. In the axis-aligned
case use the midpoints of the bottom and top sides. The same conclusion
also holds on a horizontal supporting side, though only interior sections
are used below. This proves (2).

## 3. The order of three actual return sections

Suppose A,B are physical-boundary units with a signed support gap at
least two in the x direction, and `2<=R<=sqrt(Q)`. Suppose three
other actual physical-boundary units lie wholly in `y>0`. Label them
`S_R,S_0,S_L` by increasing center angle.

The frozen three-return lemma gives their respective angle intervals

    35<theta_R<65,
    75<theta_0<105,
    115<theta_L<145                                  (3)

in degrees. For the outer upper bounds, the two further forty-degree
separations fit before 145 degrees; the lower bounds are reflected.
Every center radius exceeds `31/24`. Strict concavity of sine on
`[0,30 degrees]` gives `cos(65 degrees)=sin(25 degrees)>5/12`.
Hence

    (c_(S_R))_x>155/288>1/2,
    (c_(S_L))_x<-155/288<-1/2.                        (4)

Assume y=z lies strictly between each outer unit's horizontal supporting
lines, so its section is nondegenerate and its relative interior is in
the actual open square interior. These are explicit hypotheses in this
section. The middle section
exists by (1) and contains zero in its open interval. By (2),(4), the
right return's section has a positive right endpoint, and the left
return's section has a negative left endpoint.

Open interiors of the three section intervals are disjoint: their points
are in the corresponding actual open square interiors. The right return's
section cannot lie to the left of the middle section, because that would
give its right endpoint at most the middle's strictly negative left
endpoint. Similarly the left return's section cannot lie to the right
of the middle section. Therefore their actual order is

    I_(S_L), I_(S_0), I_(S_R).                        (5)

This is a consequence of actual square points and interval disjointness,
not an inference from the center order alone. Writing r_L,ell_R for
the facing outer section endpoints, equations (1),(5) give

    ell_R-r_L>=length(I_(S_0))>=1.                    (6)

No lower bound on the Euclidean set distance between the two outer
return squares is asserted. A section gap is used exactly as a section
gap in the argument that follows.

## 4. A force-free sharp family with aligned long endpoints

**Theorem 2 (aligned long pair with three boundary returns).** Let
actual unit squares lie in a centered disk of squared radius `q<=Q`.
Suppose A,B are physical-boundary units aligned with the coordinate axes,
with signed x-support gap at least two and nonpositive center heights.
Suppose three other physical-boundary units lie wholly in `y>0`, labeled
as in Section 3. Assume the actual physical contacts

    A meets S_L, B meets S_R.                          (7)

Then `q=Q`, and the five actual boundary units are axis aligned with
centers

    c_A=(-3/2,-1/16), c_B=(3/2,-1/16),
    c_(S_L)=(-1,15/16), c_(S_R)=(1,15/16),
    c_(S_0)=(0,sqrt(1041)/16-1/2).                   (8)

No graph, force, moment, or degree premise is used in Theorem 2.
All other physical units remain present with arbitrary independent
orientations and restrictions.

### 4.1 Actual endpoint bounds and literal return contacts

The support gap at least two gives an endpoint center x separation
at least three. At least one endpoint center therefore has norm at
least `3/2`. The universal farthest-corner bound yields

    q>= (3/2)^2+3/2+1/2=17/4>4.                      (9)

Thus the radius assumptions of Sections 1--3 hold without an independent
lower-radius premise. The force-free long-pair estimates give

    c_A=(-X_A,y_A), c_B=(X_B,y_B),
    89/60<X_A,X_B<91/60,
    |y_A|+|y_B|<=1/8.                                (10)

Define `f_A=y_A+1/2,f_B=y_B+1/2`. The assumed nonpositive
heights and (10) give

    f_A,f_B in [3/8,1/2], f_A+f_B>=7/8.               (11)

The complete force-free contact-locus assertion in Sections 1--4 of
`LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md`
applies to the actual above-side boundary neighbors in (7). It uses
only the long support gap, physical boundary status and above-side
geometry for this conclusion. Thus the actual contact is on the
endpoint's upper side, excluding its outer vertex, with every original
physical vertex/side alternative retained.

### 4.2 Original sections, not artificial floors for wrappers

The complete unequal-floor profile and the complete corner-wrapper
theorem give nondegenerate sections for both outer returns and the
one-sided inequalities

    ell_R<=g(f_B+1)-1,
    r_L>=1-g(f_A+1), g(Y)=sqrt(Q-Y^2).                (12)

A return below its endpoint's upper side is covered by the strict
wrapper inequality, without imposing that side as a floor on it.
Any nonaligned above-floor return also makes its profile strict.
All hypotheses of the wrapper theorem come from (10),(11) and the
actual aligned endpoint's outer corner; no contact is moved.

Section 3 now supplies the actual order and the gap (6). Consequently

    1<=length(I_(S_0))<=ell_R-r_L
      <=g(f_B+1)+g(f_A+1)-2
      <=2*g(1+(f_A+f_B)/2)-2
      <=2*g(23/16)-2=1.                              (13)

Only an actual section gap occurs here. In particular the endpoint
alignment theorem requiring a whole-set gap is not invoked or applied
to (6).

### 4.3 All equality implications

Strict concavity and decrease in (13) give
`f_A=f_B=7/16`. Wrapper strictness and the complete above-floor
profile force the two outer returns to align, with centers
`(-1,15/16)` and `(1,15/16)`. Their outer upper corners force
`q=Q`. The physical boundary equations of A,B then give the first
two centers in (8), including exact support gap two.

The middle section has length exactly one, so the strict tilt clause
of the full-width theorem forces S_0 to align. The outer return
sections are now `[-3/2,-1/2]` and `[1/2,3/2]`. Its unit interval,
lying between them by (5), is exactly `[-1/2,1/2]`; hence its
center x coordinate is zero. Its center height is positive by (1).
Physical boundary contact therefore gives

    1/4+(y_(S_0)+1/2)^2=Q,
    y_(S_0)=sqrt(1041)/16-1/2.

This proves (8) and Theorem 2 in full. It does not classify any
additional physical completion squares.

## 5. Full-force use and the middle load consequence

In a genuine long four-body channel, suppose the endpoints are aligned,
have full true positive degree two, and their other actual positive
neighbors are the two outer boundary returns in (7). The force-free
contact locus gives both return normals positive y components. Their
other forces are horizontal, so full y-force equilibrium makes their
total circle y resultants negative. As in the already proved endpoint
argument, this forces both endpoint center heights to be nonpositive;
the zero-height case keeps both original circle weights. Thus the
geometric height hypothesis of Theorem 2 is literal in this caller.

In the equality geometry (8), the actual contacts of S_0 with the
outer returns lie on its vertical sides. The vertical overlap is the
positive interval

    [sqrt(1041)/16-1,23/16].

At each endpoint of either contact segment one unit has the point in
its side's relative interior, so every common normal there is horizontal.
If the complete positive star of S_0 consists of its two contacts with
S_L,S_R, its full y-force equation has no body contribution. Both of
its physical circle corners have positive y coordinate
`sqrt(1041)/16`. Nonnegative original circle weights therefore force

    total circle load at S_0 = 0.                     (14)

The same conclusion holds for any full star whose positive normals are
all horizontal. It is not asserted for an arbitrary star with additional
oblique forces.

Hence an aligned-long-endpoint caller in which the middle return has
exactly these two positive contacts and positive circle load is impossible
even at Q. A physically boundary middle unit with zero circle load is
preserved. Below Q the geometric family is already excluded regardless
of that middle load.

## 6. What remains and frozen inputs

This result covers a force-free family of five actual boundary anchors,
and arbitrary physical completions of that family. In a nine-square
caller all nine units retain their poses and restrictions. The long
internal center heights are not fixed. An all-nine equality packing
with a zero-loaded physical boundary middle return is not excluded.

Tilted long endpoints remain separate: Section 3's section gap does
not license the earlier alignment theorem that requires set distance
at least one. Outer section existence before alignment is also not
assumed. These distinctions prevent an incomplete argument from being
promoted to closure of every three-return configuration.

The exact imported profile and wrapper are:

- `UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md`,
  SHA256 `abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94`;
- `ALIGNED_ENDPOINT_CORNER_WRAPPERS_OBEY_THE_UNEQUAL_FLOOR_SECTION_BOUND_2026_10_30.md`,
  SHA256 `55607f2ab5a25c056fcc12e893b3d4c7e60814c6d2e607c21b806277d29de5bc`;
- the force-free contact locus in the source named in Section 4.1,
  SHA256 `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`;
- `TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md`,
  SHA256 `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6`.

The three-return input is pinned in Section 1. Every angle, section,
equality and full-force consequence is exact over its stated continuous
domain. No pose search, new stress, removed physical unit, original
ledger mutation, Lean compilation, CI run or publication is used.
