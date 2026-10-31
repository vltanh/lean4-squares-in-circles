# Independent review of the high-square and low-left-port circle barrier

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the entire force-free statement, including both closed
horizontal endpoints of V and equality at H's top.** The proof is about
the two actual contained squares and their actual points. Its auxiliary
separating axis is not introduced as a selected pair-force normal.

## 1. Exact reviewed object and input

Source: `HIGH_SQUARE_CORNER_AND_LOW_LEFT_PORT_CIRCLE_BARRIER.md`.

- Bytes: 6,881.
- SHA-256: `f69af5d923356a063c25b108586b9a1905acfa924d244cd25622bcc0273d4176`.
- Git blob: `df3cee44a5af43e44d8bcca4ab80e0547633ed4e`.

I read the whole source and independently rederived each geometric and
scalar step. Its sole displayed input is
`UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md`, current
SHA-256 `2b90b565591b3c9bbc30c2c1af48cf117771b96bbc58ad81441f9e99497067d6`.
That identity matches exactly. I reread its complete Section 1 cap proof,
which has only the upper radius bound, no lower-radius or roof premise.
The same cap was independently rederived in my earlier shared-horizontal
roof review. No force-dependent part of that source is imported here.

The new statement assumes actual H=[h-1,h] times [g-1,g], h<=0,
37/50<=g<=1, and an actual unit B disjoint from H in open interior,
both inside the original disk with R^2<=1105/256. The two points of B
satisfy P_x<h, P_y<7/10 and h-1<=V_x<=h, V_y>=g. Neither point
is assumed to be a selected application or a circle point. B need not
physically touch the containing circle, so the theorem also applies
to actual completing units when a caller supplies the stated geometry.

## 2. The initial chord and exhaustive physical separator

Put A0=1-h>=1 and U=(-A0,g). If P_x>-A0, the actual segment VP,
which is contained in the convex B, crosses H's top with x coordinate
strictly between its two vertical sides. If V_y=g and V is one of
the two top corners, an immediate positive step toward the strict
interior x coordinate of P has the same property. Just below height
g the chord is also above g-1, so it enters int(H). A closed B
point in int(H) would force open-interior overlap, since B is the
closure of its interior. Thus P_x<=-A0. This reasoning covers
V at either horizontal endpoint and at the top itself.

I checked the elementary rectangle separating-axis step also in the
touching case. For two rectangles with disjoint open interiors, their
Minkowski difference has the origin outside its interior. A supporting
edge direction of that polygon gives a separating normal parallel to
an own axis of one of the rectangles. If the origin is a boundary
vertex, either adjacent supporting edge is sufficient. Thus a weak
closed separation, rather than strict positive separation, is enough.

All four H-owned axes are excluded directly. Right and above conflict
with P; below conflicts with V. A wholly left B would lie in x<=-1,
where the complete cap theorem puts its entire height below 7/10,
contradicting V_y>=g. The cap's actual proof retains both aligned
frame endpoints and every actual point; no boundary-contact premise
is required.

Therefore a separating axis may be chosen from B's actual axes.
Orient it from H toward B. Its Northeast quadrant contradicts P
relative to H's top-right corner. Its Southwest quadrant contradicts
V relative to H's bottom-left corner, and its Southeast quadrant
contradicts V relative to H's bottom-right corner. The vertical
separation in the latter two is strict even when V_x is a horizontal
endpoint. The already excluded axial directions leave exactly

    n=(-s,c), s,c>0, s^2+c^2=1,
    t=(c,s).

This is an auxiliary physical axis only. No positive HB edge is
assumed or created, and no selected normal is changed.

## 3. Actual tangential interval and the whole separator-angle bound

Write the real B as [k,k+1]n+[ell,ell+1]t. Its weak separation
gives k>=H0=A0*s+g*c>0. Let T0=-A0*c+g*s be the actual U
coordinate along t. From P_x<=-A0, P_y<7/10<g and positive c,s,
one has P.t<T0. From V_x>=-A0 and V_y>=g, one has V.t>=T0.
Thus T0 belongs to B's actual closed tangential interval. Equality
V=U is explicitly allowed.

The actual point (k+1)n+T0*t lies on B's far n side. Its containment
gives

    R^2 >= (H0+1)^2+T0^2 = A0^2+g^2+2H0+1.

If H0>=9/10, the lower bound is at least
19/5+(37/50)^2, exceeding 1105/256 by 4991/160000.
Therefore H0<9/10 strictly. For s>=1/3, the concave function
s+(37/50)sqrt(1-s^2) has its minimum on [1/3,1] at an endpoint.
Its values are 1 at s=1 and strictly greater than 128/125 at
s=1/3. Since H0 is at least this function, that whole interval is
impossible. Consequently 0<s<1/3 and c>9/10. It also follows
that T0<-9/10+1/3<0, using the actual upper bound g<=1.

This argument treats the full continuous separator interval. It is
not a sampled orientation bound, and it does not infer that the
physical square H or B has moved.

## 4. The low original point forces a genuine far corner out of the disk

Put eta=g-7/10>=1/25. Resolving the actual P height in the n,t
frame gives

    P_y-g=c(P.n-H0)+s(P.t-T0)<-eta.

The first term is nonnegative because P.n>=k>=H0. Thus
ell<=P.t<T0-eta/s<0. The real corner
Z=(k+1)n+ell*t therefore satisfies

    |Z|^2>(H0+1)^2+(T0-eta/s)^2.

Both positive square roots in this lower bound increase with A0 and
g. For the second, the relevant expression is
A0*c+g*c^2/s-(7/10)/s; its value at A0=1,g=37/50 is positive
from 0<s<1/3,c>9/10. Thus replacing these two parameters by
their lower bounds has the correct direction. Direct expansion gives

    |Z|^2 > 6221/2500+2s+(37/25)c
                   +(2/25)(c/s)+1/(625s^2).

I independently checked the constant: it is
2+(37/50)^2-2(37/50)(1/25)=6221/2500. The mixed terms cancel
as printed. The positive-angle estimates give

    (37/25)c>333/250,
    2s+(2/25)c/s > 2s+9/(125s)
                   >=2sqrt(18/125)>3/4.

The last comparison has squared reserve 27/2000. Dropping only
the remaining positive term yields

    |Z|^2>5713/1250
          =1105/256+40639/160000.

This contradicts containment of an actual B corner. No original
point, side interval, or physical square was replaced in constructing
Z or the intermediate far-side point.

## 5. Exact approval limits and retained data

The whole force-free theorem is proved for every B orientation,
all allowed h,g, every P and V satisfying the statement, both closed
V abscissa endpoints, V_y=g, and V=U. There are no load, degree,
circle-mask, selected-normal or original-HB-edge premises. A graph
caller must still exhibit the same actual H and two actual points
in one unchanged B, with all the stated inequalities.

The theorem alone closes no whole original graph/load identifier.
No source was edited, no normal was selected for a stress, and no
mean or force was changed. All actual squares, full equations,
physical masks, zero individual coefficients and the original
2513/58 inventory remain. I performed no numerical pose search,
sampling, Lean compilation, CI, workflow, metadata edit, commit,
push, or publication. Root adoption and caller review are separate.
