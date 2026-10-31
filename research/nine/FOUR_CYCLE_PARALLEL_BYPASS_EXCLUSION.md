# The parallel bypass/transmitter C4-with-leaf chart is excluded

**Status: complete exact hand argument; root and separate independent
hand audits passed.**
Let the selected positive component be the four-cycle A--B--U--D--A
with a pendant radial leaf L attached to A. Suppose B,D are loaded,
U has zero circle weight, and the frames of A and U are parallel.
Then this entire chart can be excluded in a compatible selected
physical certificate throughout

\[
                79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

Both S/D leaf types, every actual shared-side mean, all possible
point/shared contacts and all circle-corner masks are retained. The
only additional normal choice is a finite open-dense unequal-slope
condition at two distinct point-contact junctions, stated explicitly
in Section 4 before stress extraction. The strict point-normal,
nonradial and matched-junction conventions are preserved.

This does not exclude the whole opposite-loaded-pair C4 chart. Its
A/U-nonparallel poses, including parallel tip/transmitter frames and
contacts owned by A, remain separate obligations. All four completion
squares remain in that parent problem.

Write

\[
 h=\sqrt{R^2-1/4}-1,
 \quad r=R-\sqrt2,
 \quad s=1-r,
 \quad \varepsilon=\max(h-1,0).
\tag{2}
\]

The exact bounds used below are

\[
 9/10<h<61/60,\quad 1/2<r<7/10,\quad s<9/20,
 \quad 0\le\varepsilon<1/60.
\tag{3}
\]

The radial-leaf articulation estimate also gives
dist(0,A)<=epsilon, by `FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md`,
Lemma 2.1. It is independent of the cycle contacts.

## 1. Every physical tip frame is parallel as well

The unit-bypass theorem makes U side-normal, with reserve one, and
separates A and U transversely. Since their frames are parallel and
A's transmission projection covers U's entire unit interval, those
two projections coincide. Rotate and reflect, without moving the
circle center, so the complete domain is

\[
\begin{split}
 A&=[X,X+1]\times[Y,Y+1],\\
 U&=[X-g-1,X-g]\times[Y,Y+1],\qquad g\ge0.
\end{split}
\tag{4}
\]

B lies below y=Y and D above y=Y+1. If B were oblique to U,
it would have one unique top vertex p on y=Y. Its contact with A
would have to be this same p, since A lies above y=Y. Thus

\[
                      X\le p_x\le X-g.
\]

It follows that g=0 and p=(X,Y), a vertex of U as well. The positive
BU force is vertical, a side-axis direction of U. But a point-only
vertex/vertex contact has a normal strictly exposing the vertex in
both bodies under the existing selected convention. A side-axis
normal does not strictly expose U's vertex. This is a contradiction.

Therefore B is parallel to U. The same argument at the top proves
that D is parallel too. The BU and UD contacts have positive shared
length: a zero-length aligned contact with an axis force would again
violate the same strict convention. Their actual means are still
arbitrary and are not moved to midpoints.

Because B touches both U and A, its top side starts strictly to the
left of X. Hence its contact with A is either a positive horizontal
shared segment or just the corner (X,Y). In the corner case its
complete horizontal interval is [X-1,X]. The corresponding D
alternatives are a positive horizontal shared segment or just
(X,Y+1), again with horizontal interval [X-1,X]. These exhaust all
physical A-tip contacts in (4).

## 2. An A-tip shared side is impossible

Suppose AB is a positive horizontal shared side; reflect vertically
if necessary to put this tip below U. Both outward pair forces on
B point upward. Its circle force therefore points downward. The
parallel-force radial normal form makes B a radial S square:

\[
                 B=[-1/2,1/2]\times[-h-1,-h],
                       \qquad Y=-h.
\tag{5}
\]

This conclusion retains the two distinct shared-side means and follows
from their aggregate force and torque. In particular the two circle
weights of B are equal.

If AD were shared as well, the same argument would make D the
upward radial S square, whose inner side is y=h. But its inner
side is also y=Y+1=1-h, forcing 2h=1, contrary to (3).
Thus AD is a point contact, and

\[
       A=[X,X+1]\times[-h,1-h],\qquad
       Q:=A\cap D=(X,1-h).
\tag{6}
\]

The positive shared length between B and U gives

\[
                              X-g>-1/2,
                              \qquad X>-1/2.
\tag{7}
\]

Every point of the circle-touching square D has norm at least
r=R-sqrt(2). We show that every possible S/D leaf on A either
repeats B or forces |Q|<r.

### 2.1. A D leaf

Under the existing nonradial point-normal convention, its direction
is a side normal of A and its radial application is side-interior.
The downward support h exceeds r, the upward support 1-h is less
than r, and the left support -X is less than 1/2<r by (7).
Only the right side can carry the D leaf. It gives

\[
                     X+1=r,\qquad X=-s,
                     \qquad h<1.
\tag{8}
\]

The last inequality is necessary for (r,0) to lie in the relative
interior of A's vertical side. Consequently

\[
 |Q|^2=s^2+(1-h)^2
       <(9/20)^2+(1/10)^2<1/4<r^2,
\tag{9}
\]

contradicting Q in D.

### 2.2. An S leaf, including every vertex and side endpoint

Its radial application is a support point p=h e of A. Consider first
an axis direction, permitting the application to be a side endpoint.
The left support cannot equal h by (7). The upper support would
force 1-h=h, impossible. The downward direction gives exactly the
already occupied radial S square B, so cannot be a distinct leaf.
The right direction gives X=h-1 and requires h<=1. Then

\[
                        |Q|=\sqrt2(1-h)<\sqrt2/10<r.
\tag{10}
\]

Every nonaxis radial support occurs at a vertex. At a bottom vertex
the second coordinate is -h, so norm h forces first coordinate zero;
this is the downward axis case already treated. At a top vertex,
outward radiality requires 1-h>0; h>=1 either has the wrong vertical
sign or is an axis case. For h<1, radiality and norm h force its
first coordinate to have absolute value sqrt(2h-1).

At the upper-left vertex this gives
X=-sqrt(2h-1)<-sqrt(4/5)<-1/2, contradicting (7). At the upper-right
vertex it gives

\[
                  X=\sqrt{2h-1}-1\in(-1/5,0).
\]

Thus

\[
                 |Q|^2<(1/5)^2+(1/10)^2=1/20<r^2.
\tag{11}
\]

The axis, unique-vertex and endpoint alternatives are exhaustive.
They exclude the entire shared AB case. Reflection excludes shared
AD as well.

## 3. Two point contacts force one exact D geometry

Both A-tip contacts are now point-only aligned vertex contacts. Their
full poses are

\[
 B=[X-1,X]\times[Y-1,Y],\qquad
 D=[X-1,X]\times[Y+1,Y+2].
\tag{12}
\]

Since A meets the disk of radius epsilon,

\[
 X\le\varepsilon,\quad X+1\ge-\varepsilon,
 \quad Y\le\varepsilon,\quad Y+1\ge-\varepsilon.
\tag{13}
\]

These strict small bounds make both tips' center first coordinates
negative, B's center height negative, and D's center height positive.
Their unique physical circle corners are consequently

\[
                     (X-1,Y-1),\qquad(X-1,Y+2).
\]

Equality of their squared radii gives

\[
               Y=-1/2,\qquad M:=1-X=\sqrt{R^2-9/4}.
\tag{14}
\]

The radius window gives

\[
                         32/25<M<3/2.
\tag{15}
\]

For the lower bound, (79/40)^2-9/4=2641/1600>1024/625.
The upper follows from R^2<9/2. The farthest corner norm of A is
therefore

\[
 \max_{z\in A}|z|^2=(2-M)^2+1/4
       <(18/25)^2+1/4=1921/2500<81/100.
\tag{16}
\]

In particular no S leaf can have its application of radius h>9/10
on A. The leaf must be D. A's upper/lower supports are 1/2, and
its left support M-1 is less than 1/2. Since r>1/2, the only
possible D direction is east, with

\[
                               2-M=r.
\tag{17}
\]

Its circle force is a positive horizontal vector. The two other
circle forces are positive multiples of

\[
                    z_B=(-M,-3/2),\qquad z_D=(-M,3/2).
\tag{18}
\]

Their multipliers are equal by vertical component force balance of
the whole component. Write their common circle-force scale as k>0.

## 4. A finite compatible corner-normal choice excludes the last case

The two point applications are

\[
                         P_B=(X,-1/2),\qquad P_D=(X,1/2).
\tag{19}
\]

Their strictly exposing normals from A are respectively

\[
                 n_B=(-a,-b),\qquad n_D=(-c,d),
                   \qquad a,b,c,d>0.
\tag{20}
\]

They are independent free point-normal parameters at two distinct
physical junctions. Let mu,nu>0 be their magnitudes, and let gamma>0
be the common vertical transmission magnitude through U. The tip force
equations, using (18), give exactly

\[
 \mu a=kM=\nu c,\qquad
 \mu b=(3/2)k-\gamma=\nu d.
\tag{21}
\]

Thus a necessary condition for this positive component is

\[
                               bc-ad=0.
\tag{22}
\]

Neither actual BU/UD mean occurs in this condition. Both are retained
as arbitrary genuine shared-side applications; force balance alone
has supplied the obstruction.

Before the physical multiplier argument, prelist every physical
five-body candidate of this parallel chart. For each, choose the two
strict point normals away from (22). That equation is a nonzero
condition in two independent junction parameters and has empty
interior in every product of allowed open intervals. There are only
finitely many body assignments. Its complement can therefore be
imposed simultaneously with all earlier finite open-dense selections.

At a four-square junction, keep the mirrored opposite-pair parameter
used for planar uncrossing; the two distinct points in (19) still have
independent parameters. Nonradial and other strict restrictions remain
in force. Uncrossing preserves every surviving point-edge normal and
adds only shared-side forces, and thinning only deletes atoms. Every
possible final candidate was prelisted. Hence the same selected
certificate cannot contain this last positive chart.

## 5. Complete scope of the conclusion

The A/U-parallel domain first forces both tips parallel. A shared
A-tip side is excluded with every possible radial S/D support of A.
Two point contacts force the unique-corner geometry (14)--(18), which
the finite simultaneous choice in Section 4 excludes without fixing
the channel's means. This closes the entire parallel-bypass chart.

The parent C4 opposite-loaded-pair problem still retains A and U with
nonparallel frames. In that domain the separate
`FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md` removes both oblique tips
owning their point contacts with A, but A-owned contacts, shared means
and U-parallel tips must still be treated where they remain physically
possible. No whole cell or unrestricted nine-square closure follows
from either chart alone.

No Lean compilation, CI, numerical pose cover, or discarded completion
square is used in this argument.
