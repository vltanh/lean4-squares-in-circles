# Width-two paths exclude the central common-vertex and two-vertex forms

**Status:** independently reviewed exact conditional hand proofs (2026-10-29).

Use a three-loaded simple-cycle component whose two paths from C end at
touching loaded bodies A,B. The path widths are in `{1,sqrt(2),2}`, and at
least one is two. Work in `79/40<=R<=3/sqrt(2)` with the selected physical
certificate of [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md).
A width-two path consists of two side transmitters, each of whole-graph
degree two. Thus its first body at C is a side transmitter.

These arguments extend specified branches of the earlier three-loaded
five-cycle analysis. They do not on their own close the whole six-cycle
signatures `LLSLSS` and `LLDLSS`.

## 1. Coincident contacts at a central vertex are impossible

Suppose both path contacts on C coincide at a vertex P. Aggregate the
two contact forces at P. Force and torque balance give the ordinary
loaded-leaf classification, making C radial diagonal type. After rotating,

```text
P=(-b,0),       b=R-sqrt(2)>0.
```

The outgoing normal cone at P has directions in `[-pi/4,pi/4]`.
The aggregate outgoing force is horizontal. Reflect vertically if needed
so the SS path has direction `theta>=0`; the other path then has direction
`-eta<=0`, with `0<=theta,eta<=pi/4`. This also covers the parallel case,
where both angles are zero.

We claim `theta=pi/4`. Suppose otherwise. Let U be the first side
transmitter on the SS path. If P were in the relative interior of a
side of U, U would locally occupy the open half-plane with inward normal
`n_theta`. The other first path body has inward normal `n_(-eta)` at P,
and its interior contains directions arbitrarily close to that normal.
Since `theta+eta<pi/2`, those directions have positive dot product with
`n_theta`. The two bodies would overlap near P. Therefore P is a vertex
of U.

Because theta<pi/4, the normal strictly exposes P on C. Thus C and U
intersect only at P. But the selected positive normal is a side normal
of U, forbidden by the strict-normal convention at point-only
vertex/vertex contacts. Its precise source and boundary exception are
recorded in [COMMON_CORNER_MIXED_TRANSMISSIONS.md](COMMON_CORNER_MIXED_TRANSMISSIONS.md),
Section 1. This contradiction proves the claim.

The SS endpoint contact is `P+2n_theta`. Its endpoint square contains
`P+3n_theta` by the unit-normal-step lemma. At theta=pi/4 this point is

```text
(3/sqrt(2)-b, 3/sqrt(2)).
```

Its first coordinate is positive, while the absolute value of its second
is `3/sqrt(2)>=R`. It is strictly outside the containing disk. Hence
coincident contacts at a central vertex are impossible.

## 2. Distinct central vertex contacts: the projection proof extends

Suppose C has a unique circle vertex and its two path contacts are
distinct vertices. Use C's own frame, with center `(a,b)`, a,b>0, and
circle vertex `(a+1/2,b+1/2)`. The circle vertex cannot be a pair contact.

The force, torque, and one-sided endpoint support arguments in Sections
1--3 of [VERTEX_CONTACT_MIXED_FIVE_CYCLE.md](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md)
use only `W1,W2>=1` until their final equality cases. For clarity, their
adjacent-bottom-vertex calculation gives outward forces

```text
f_left=(-u,-v),    f_right=(w,-z),
v=lambda(a+1/2),   z=lambda(b-a),   u=v+w,
```

and therefore b>=a. If the unit outgoing directions are `(-p,-q)` and
`(r,-s)`, one has p>=q>0, r,s>=0, and

```text
max_x A<=a-1/2-W1*p+q<=a-1/2,
min_x B>=a+1/2+W2*r-s>=a-1/2.
```

Touching requires equality throughout. It forces `r=0`, `s=1`,
`W1=1`, and `p=q=1/sqrt(2)`. Thus, if one width is two, the only new
possibility has `W2=2`.

The same equality geometry as in the source fixes the endpoint centers:

```text
c_A=(a-1/2-1/sqrt(2), b-1/2-sqrt(2)),
c_B=(a, b-1-W2).
```

Loading B and C gives `b=(1+W2)/2=3/2`. Consequently

```text
R^2=(a+1/2)^2+4>17/4,
0<a<=1/sqrt(2)-1/2.
```

For A this gives

```text
|(c_A)_x|<5/4,
|(c_A)_y|=sqrt(2)-1<1/2,
|c_A|<sqrt(29)/4.
```

Every A vertex is within `1/sqrt(2)` of its center. The exact comparison

```text
sqrt(29)/4+1/sqrt(2)<sqrt(17)/2<R
```

follows on squaring from `4sqrt(58)<31`, in turn from `928<961`.
Thus every vertex of A is strictly inside the containing circle,
contradicting A's positive load. This handles the only new equality case.

Adjacent left contacts follow by interchanging axes. Adjacent top or
right contacts contradict force balance, as in the source. For the only
opposite noncircle pair, that source gives p>q>=0 and

```text
max_x A<=a-1/2-W1*p+q<a-1/2<=min_x B
```

for every W1,W2>=1. Hence that case is also impossible.

All distinct central vertex pairs are excluded when one path has width
two.

## 3. The other unique-circle contact reductions

If the two outgoing directions are nonparallel side normals of C, they
are perpendicular. Section 1 of
[SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md)
already treats arbitrary `W1,W2>=1`: contact between A and B forces
`W1=W2=1`. Thus this branch is immediately excluded when one width is two.
This includes a normal on the boundary of a vertex cone.

If exactly one contact is a relative side-interior point and the other a
strict support vertex, the nonincident vertex/side exclusion in the same
manuscript uses only the lower width bound one. Its force-balance sign
argument then identifies the opposite circle corner and an incident inner
side, giving exactly the normal form treated in
[SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md](SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md),
which excludes either placement of width two.

A common side-interior contact has parallel directions. Together with
Sections 1--2, these observations leave only the parallel-direction
reduction and the radial-side central body as classification work for the
two six-cycle signatures, with their width-two hypotheses still to be
checked explicitly.
