# A radial-side central body cannot join SS and D paths

**Status:** independently reviewed exact conditional hand proof (2026-10-29).
The certificate is selected by
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md)
before its components are classified. The strengthened normal selection
is used explicitly below.

Let the whole positive component have three loaded bodies A,B,C, a direct
A--B edge, an SS path from C to A, and a single D transmitter from C to B.
Suppose C has two circle vertices. Work in `79/40<=R<=3/sqrt(2)`.

**Theorem.** This radial-side central case of `LLDLSS` is impossible.

## 1. Contact positions on the central square

Rotate and reflect so

```text
C=[-L-1,-L] x [-1/2,1/2],
L=sqrt(R^2-1/4)-1,
R^2=(L+1)^2+1/4,
9/10<L<17/16.
```

Both transmission contacts lie on C's right side, including its corners.
The proof in [RADIAL_SIDE_MIXED_FIVE_CYCLE.md](RADIAL_SIDE_MIXED_FIVE_CYCLE.md),
Section 1, needs only path width at least one and therefore applies to
SS as well. Explicitly, a contact in the top side's relative interior
would put the endpoint contact at height at least `3/2`, and the endpoint
square then contains its inward normal step at height at least `5/2>R`.
The bottom side is excluded by reflection, and the left side likewise
puts an endpoint point beyond horizontal distance R. The left corners
are circle vertices, which cannot be shared by two squares.

At a right-side interior point the outgoing direction is horizontal.
At the upper-right corner it is `(p,q)`, with p,q nonnegative and
`p^2+q^2=1`. At the lower-right corner it is `(p,-q)`.

## 2. Any radial-side SS path forces L>=1

This section uses only containment of the SS endpoint square.

If the SS contact is in the relative interior of the right side, its
endpoint square lies in `x>=2-L`. The
[cap bound](TRANSMISSION_CAP_ANGLE_BOUND.md), Section 1, implies

```text
R^2 >= (3-L)^2+1/4.
```

Comparison with `R^2=(L+1)^2+1/4` gives L>=1.

If the SS contact is the upper-right corner, its endpoint contact is
`(-L,1/2)+2(p,q)`. The unit-normal-step lemma in
[SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md](SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md)
puts

```text
F=(-L,1/2)+3(p,q)
```

in the endpoint square. Direct expansion gives

```text
|F|^2-R^2
 = 8-2L-6Lp+3q
 = 8-8L+6L(1-p)+3q
 >= 8-8L.
```

Containment therefore again forces L>=1. Reflection handles the lower
corner. Consequently, in every possible case,

```text
1<=L<17/16,             R^2>=17/4.                  (1)
```

The same conclusion applies to SS joined to an S path; it does not
itself exclude that second pattern.

## 3. The D endpoint is strictly inside the circle

The generic normal-selection theorem, Section 4, makes both neighbors
of every degree-two D transmitter meet it in relative side interiors.
In particular, its contact on C is `(-L,h)` with `|h|<1/2`, and the
transmission direction is horizontal. Its far contact on B is

```text
Q=(sqrt(2)-L,h).
```

B also has relative side-interior support there, so its frame is parallel
to C. Its horizontal interval is exactly

```text
[sqrt(2)-L, sqrt(2)-L+1].
```

The first endpoint of that interval is positive, and (1) makes the second
at most `sqrt(2)`. Its vertical interval has length one and contains h;
every vertex consequently has vertical absolute coordinate at most
`|h|+1<3/2`. Every vertex of B therefore satisfies

```text
|v|^2 < 2+9/4=17/4<=R^2.
```

This contradicts the positive circle load on B and proves the theorem.
No completion-capacity estimate or numerical comparison is used.
