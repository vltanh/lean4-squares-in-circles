# A large outer-body corner forces a proper contact with an inner-side body

**Status:** complete hand selection argument; root and independent full
mathematical reviews passed on 2026-10-29, including the common midpoint
interval for both possible outer-body roles.

Use the selected physical certificate and loaded seven-ring of the
[outer-edge reduction](SEVEN_RING_OUTER_EDGE_REDUCTION.md), strengthening
its point-contact normal selection by the independent open intervals
below. Let a unique-circle U4/U5 body have the notation of
[LOADED_OUTER_MIXED_RESTRICTIONS.md](LOADED_OUTER_MIXED_RESTRICTIONS.md):

```text
C=[X-1,X] x [-Y,1-Y],       w=(X,-Y),
H=Y-1>X,       A=(X-1,-H),       B=(X,-H).
```

Here A is the strict opposite-corner V contact, and B is the extra corner
on the body's inner boundary.

**Theorem.** If `|B|^2>=83/50`, the pair at A cannot be VV in this selected
stress. It is a proper V/S pair, and its neighboring S body has a unique
circle vertex and row U1,U6 or U7.

This leaves proper opposite-corner contacts open. It is not a uniform
83/50 capacity bound for an outer-edge body.

## 1. The large-corner condition gives a narrow exact box

Since `q=X^2+(H+1)^2<=9/2` and `|B|^2=X^2+H^2>=83/50`,

```text
H<=23/25,
X^2>=83/50-(23/25)^2=1017/1250>(9/10)^2.
```

Put epsilon=1-X. Together with H>X this gives

```text
9/10<X<H<=23/25,
2/25<epsilon<1/10,
19/10<Y<=48/25,
0<H-X<1/50.                                          (1)
```

In particular

```text
|A|^2=epsilon^2+H^2<2141/2500<1.                     (2)
```

Let r=|A|. The identity `q-|A|^2=2(X+H)` gives

```text
q-(r+1)^2=2(X+H)-1-2r>18/5-3=3/5>0.                 (3)
```

Thus no circle vertex of any neighboring square can be at distance at
most one from A.

## 2. A VV neighbor must be a reflected opposite-corner square

Suppose the pair at A is VV. Then A is a vertex of its neighbor. Its two
adjacent vertices are at distance one from A, so (3) prevents either from
being a circle vertex. The neighbor is loaded, hence its opposite vertex
is its unique geometric circle vertex.

Both circle vertices are consequently at distance sqrt(2) from A and
have norm R. Their displacement vectors from A have equal scalar product
with A. They are distinct, because two packed squares cannot share a
point of the containing circle. Thus the neighbor's diagonal is the
reflection of C's diagonal through the line spanned by A. A square with
a specified contact vertex and opposite diagonal is uniquely determined,
so the whole neighbor is that reflection of C.

Write

```text
D=H^2-epsilon^2>0,       E=2epsilon*H>0,
r^2=H^2+epsilon^2.
```

The reflected unit edges from A are

```text
e=(-D/r^2,E/r^2),       f=(-E/r^2,-D/r^2).            (4)
```

The common strict normal into that neighbor can be written `(-c,s)`,
with c,s>0. Intersecting its open inward normal cone with the negative
of C's open inward cone gives exactly

```text
0<k:=s/c<E/D.                                        (5)
```

For example put beta=atan(epsilon/H) in (0,pi/4). The neighbor's edge e
has angle pi-2beta, so its common normal interval is `(pi-2beta,pi)`;
the slope parameter in (5) ranges from zero to tan(2beta)=E/D.

## 3. The loaded SS neighbor requires a very small application parameter

The generic VV restriction makes the other positive pair of C an SS
pair with its aggregate application in the shared segment's relative
interior. Write it as

```text
P=(X,-H-t),       t>0.
```

The exact shared-side calculation gives

```text
0<t<Z-H<(H-X)/H<1/45,
Z=sqrt(Y^2-2X-1).                                    (6)
```

The final inequality follows immediately from (1).

Normalize C's positive circle coefficient to one. Its actual V force
has direction `(c,-s)`, and its S force points horizontally left. Force
balance and torque therefore require

```text
h=Y/k-X>0,
h*t=Y-X,
t=(Y-X)*k/(Y-X*k).                                  (7)
```

Choose the midpoint direction of the common normal interval. In its
angle coordinate this is beta=atan(epsilon/H), so its slope is

```text
k_mid=epsilon/H>2/23.                                (8)
```

The denominator in (7) is positive there, since 0<k_mid<1 and Y>X.
Because Y-X>1 and Y-X*k_mid<Y<=48/25,

```text
t_mid>25/552>1/24>1/45.                              (9)
```

The strict comparison `25/552>1/24` is `600>552`.
This contradicts the actual overlap bound (6).

It is essential that the normal choice work whichever endpoint later
has the outer-edge mixed role. The reflection in Section 2 exchanges
the two squares. If one endpoint's slope is k, the other endpoint's
slope is

```text
k'=tan(2*beta-atan(k)).                               (10)
```

Reflection fixes the midpoint direction: k=k'=tan(beta). Both endpoints
have the same parameters X,Y,H,epsilon after choosing their own reflected
frames. Thus (9) holds for the required outer-body t at both endpoints
simultaneously. By continuity, there is a nonempty open interval around
the midpoint inside (5) on which both expressions for t exceed 1/24
and their denominators stay positive. Use that common interval.
Any endpoint that becomes an outer mixed body of the positive loaded
ring then contradicts (6).

## 4. Joint selection is possible before the positive graph is known

The construction can be imposed on every geometric point-only VV pair
with two geometric circle contacts for which one endpoint has the
opposite-corner geometry and large B described above. The reflection
argument shows that both endpoints have the same relevant geometry up
to an isometry. Section 3 prescribes one shared open interval that works
for both endpoints. No assumption about which endpoint will be outer
in the later selected stress is needed.

These pairs have opposite circle vertices at distance sqrt(2) from their
contact. They are disjoint from the circle-adjacent pairs whose open
intervals were restricted in the all-inner-face capacity theorem. Thus
there is one compatible open-interval prescription for each such pair. After
making these finitely many interval restrictions, perform all the existing
finite-polynomial, strict, nonradial and nondiagonal avoidance inside
the resulting open product. The nonzero-polynomial argument and physical
stress existence still apply unchanged.

The same compatibility with coherent four-square-junction choices holds:
two opposite quarters of a full 2x2 junction cannot both have geometric
circle vertices in this radius window. The proof and joint selection
order are recorded in
[PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md).

The exclusion is then applied to the newly selected positive graph.
It does not assert that an old graph remains unchanged under reselection.

## 5. The surviving proper neighbor has an inner side and unique circle vertex

If the pair at A is not VV, the strict V support on C makes it V/S.
Any point of the neighbor's contacted unit side is at distance at most
one from A. By (3), no circle vertex can lie on that side. Therefore its
circle vertex lies on the opposite parallel side: this is an inner S
incidence relative to the chosen circle vertex.

The neighbor cannot be radial. If its circle edge is perpendicular to
this S side, one circle vertex lies on the contacted side, already ruled
out. If its circle edge is the parallel opposite edge, the contacted
side is the radial body's inner face; its loaded neighbor C is then
forbidden by the reviewed radial inner-face clearance lemma.
Thus the neighbor has a unique geometric circle vertex.

The unique-circle alphabet allows an inner S incidence only in
U1,U2,U3,U6,U7. The incident mixed exclusion removes U2/U3, leaving
U1,U6,U7, as claimed.

The remaining proper contact retains continuous frame and force data.
No bound on its completion capacity or on the number of such large outer
corners is inferred from this local restriction.
