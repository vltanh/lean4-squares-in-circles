# Independent full review of the radius-adapted three-unit cap theorem

Date: October 29, 2026 UTC. Reviewer: pentagon_global continuation.

**Verdict: PASS for the complete stated theorem and equality case.**
I read the entire 273-line source and independently derived its four
section-endpoint formulas, circle support inequalities, complete
orientation cover, interval clipping argument and equality geometry.
The proof is force-free and has no unproved graph, load, normal-owner,
physical-mask, side-mean or packing-completion premise. It is ready for
root's separate adoption decision.

## 1. Exact frozen source and scope

The reviewed source is

`ADAPTIVE_THREE_UNIT_CAP_RADIUS_OVER_SQRT_TWO_2026_10_29_CONTINUATION.md`,

with 9,573 bytes and SHA256

`7baa4831abdfa1ec97d3e504fa70a00b0b5763e371016a52b67e0b25b54cf6ae`.

The literal statement assumes `2<=R<=3/sqrt(2)`, and defines

    C=R/sqrt(2), s=C-1, z=C-3/16,
    I=[-C,C] x {z}.

Every actual unit contained in the disk and the whole closed cap
`y>=s` has a horizontal section through its open interior at z.
Its section clipped to I has length at least one, strictly greater
than one for every non-axis-parallel orientation. Hence three actual
interior-disjoint units in that cap force `R=3/sqrt(2)` and the exact
axis-parallel equality family stated in Section 6.

The older fixed-floor theorem is methodological provenance only. The
reviewed source reproduces all required new estimates, so no unstated
substitution into an older parameter range is needed.

## 2. Complete actual orientation and section range

The actual square can always be described by one of the two displayed
axis pairs `(a,b),(-b,a)` or `(a,-b),(b,a)`, with
`a>=b>=0`, `a^2+b^2=1`. This changes axis labels only; it does not rotate
the cap or replace the actual square by a representative pose.

With half-height `h0=(a+b)/2`, the actual center height obeys

    s+h0<=y<=R-h0.

The two exact upper gaps are `z-s=13/16<5/6` and
`R-z<=3/sqrt(2)-21/16<5/6`. They imply

    |z-y|<5/6-h0<h0.

Thus the section line passes strictly through the open square interior
for every actual orientation, including the axis-parallel endpoint.
No tangency case is silently assigned a positive section length.

For b>0, intersecting the four actual side inequalities gives the full
section length

    W=min(1/a,(h0-|z-y|)/(a*b)).

Both quantities are strictly greater than one. Indeed `a<1`, and

    a+b-a*b >= sqrt(2)-1/2 > 5/6.

The latter follows by writing `w=a+b` and observing that
`w-(w^2-1)/2` decreases on `[1,sqrt(2)]`. This verifies the section
length before clipping without an orientation subdivision.

## 3. Circle tangent and clipping criterion

The coupled radius and tangent point satisfy

    g(Y)=sqrt(R^2-Y^2), g(C)=C, g'(C)=-1.

Concavity gives both tangent estimates in the source. Their arguments
are nonnegative actual vertex lower heights and do not exceed R when
used. In particular the top vertex's lower height `C+delta` is within
the circle whenever the relevant square exists.

For `delta>=0`, the exact difference of squares gives

    C-g(C+delta)
      =(2*C*delta+delta^2)/(C+g(C+delta))
      >=delta+delta^2/(2*C)>=delta+delta^2/3.

The inequality includes delta=0 and uses exactly `C<=3/2`.

For an actual section with endpoints ell,r, the two strict bounds
`ell<C-1` and `r>1-C` suffice. If neither endpoint is clipped its
length is W>1. If one is clipped the appropriate endpoint inequality
still gives length greater than one. If both are clipped, the length
is `2*C>=2*sqrt(2)>1`. Reflection exchanges the two endpoint bounds
and the two displayed frame forms, so proving the left bound in both
forms is exhaustive.

## 4. Positive tilt: both actual side equations are covered

The exact left endpoint for the first frame is

    ell=max(ell1,ell2),
    ell1=x-(1/2+b*Delta)/a,
    ell2=x+(a*Delta-1/2)/b.

The source's identities with the actual top vertex are exact. Its
height is at least `C+delta`, strictly beyond the maximum height R*b
of `a*g(Y)+b*Y`, because

    s+a-(R-1)*b >= s+(2-R)*b
                   >sqrt(2)-1-1/8>0.

The decreasing-function and tangent bounds therefore apply on the
entire actual top-vertex height interval.

For ell1, the sufficient stronger whole-angle inequality has

    4*E=b*(3-a)-7*a*(1-a)
       =b/(1+a)*(3+2*a-a^2-7*a*b)>0.

The first identity uses `a^2+b^2=1`. The last bracket is at least
`1/4`, using `2*a-a^2>=3/4` and `a*b<=1/2`. The actual coefficient
of delta is one, stronger than the comparison's 3/4, and the actual
subtracted constant 13/16 is at least 3/4. Consequently ell1<C-1
with the claimed strictness.

The second side is active exactly when `Delta>=t0`. Actual cap
containment then gives `a<=13/16`, including equality, hence

    w>=w0=(13+sqrt(87))/16.

Monotonicity of `b*g(Y)-a*Y` and the exact tangent deficit give

    C-ell2 >= (w-1)+(w-1)^2/3+w-13/16.

The right side is increasing over the required interval. After
weakening the first coefficient to 23/24, its value minus one at
w0 is exactly `(44*sqrt(87)-405)/384>0`. This proves ell2<C-1
whenever ell2 is active. When it is inactive ell1 already controls
the actual maximum. Thus neither actual left edge is omitted.

## 5. Negative tilt: both complete left-edge bounds

Direct intersection gives

    ell=max(m1,m2),
    m1=x+(b*Delta-1/2)/a,
    m2=x+(-a*Delta-1/2)/b.

Using the actual rightmost vertex for m1 yields precisely

    a*(m1-(C-1)) <= b*(13/16-F(a)),
    F(a)=a+b*(1-a)/(1+a).

For `k=b/(1+a)`, the exact half-angle substitution gives

    F(a)-13/16=(3-29*k^2+32*k^3)/(16*(1+k^2)).

The function `k^2*(29-32*k)` increases on `[0,5/12]`, which
contains the entire actual interval `[0,sqrt(2)-1]`. The numerator
has the positive lower bound `121/432`. Hence m1<C-1 for every
b>0, with no omitted orientation endpoint.

Using the actual top vertex for m2 gives the full circle-support
inequality `b*m2<=R-a*z-1`. The concave function
`a*z+(C-1)*sqrt(1-a^2)` attains its minimum at an endpoint of
`[1/sqrt(2),1]`. Both endpoint values exceed R-1, by exactly the
two printed scalar estimates. Thus m2<C-1 on the whole interval,
whether or not this side is active. Reflection now completes the
right endpoint bound and the full rotated-square section theorem.

## 6. Parallel endpoint, capacity and equality

For b=0, actual axis-parallel containment gives

    (|x|+1/2)^2+(y+1/2)^2<=R^2,
    y+1/2>=C.

Since `R^2=2*C^2`, the complete unit section lies inside I. Its
length is exactly one, and the earlier strict vertical inequalities
place it through the open interior. This handles the endpoint where
the tilted formulas contain denominators b.

Sections of interior-disjoint squares have disjoint relative
interiors on this line. Clipping cannot create an interior overlap.
The sum of three section lengths is therefore at most `2*C<=3`.
The section theorem forces equality, hence `C=3/2` and all three
squares axis-parallel. Their closed unit intervals tile I, so their
center x coordinates are exactly -1,0,1. The cap gives center heights
at least one. Circle containment at either outer square forces its
height to be exactly one; at the middle square it gives precisely

    1<=h<=(sqrt(17)-1)/2.

Conversely every such middle height gives three contained squares
with disjoint open interiors and the stated cap floor. Thus the
equality classification is complete, including its endpoints.

## 7. Exact checks and caller boundary

The symbolic side identities were independently expanded modulo
`a^2+b^2=1`; only exact scalar arithmetic was used for reserves.

| Scalar check | Exact value |
| --- | --- |
| `(103/48)^2-9/2` | `241/2304` |
| `3-(5/12)^2*(29-32*(5/12))` | `121/432` |
| `44^2*87-405^2` | `4407` |
| `16^2*2-19^2` | `151` |
| `13/16-51/80` | `7/40` |
| `9/2-1105/256` | `47/256` |

The reviewed bytes prove the theorem only for their stated radius
range `2<=R<=3/sqrt(2)`. The same estimates appear extendable to
`sqrt(2)<=R<=3/sqrt(2)` by changing the lower scalar range and
handling the positive-tilt monotonicity separately for R<=2. That
extension has been sent to the author, but is not silently inserted
into this frozen-source review.

A caller still needs to prove containment of three entire actual
units in the specified cap. A force sign, center coordinate, selected
point, circle corner, or unproved pocket/crosscut assignment does not
supply that premise. This standalone theorem and its review do not
close any original house, hexagon, parent or global checkbox.

No old source was modified. No pose sampling, packing certificate,
Lean/Lake command, build, CI/workflow, ledger update, staging,
commit or remote action was performed.
