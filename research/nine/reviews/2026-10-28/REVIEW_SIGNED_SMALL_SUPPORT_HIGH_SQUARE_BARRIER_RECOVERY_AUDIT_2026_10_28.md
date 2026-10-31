# Independent review: the high-square barrier with signed small support

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the exact frozen source below.** I read the complete
new proof and its high-strip input, independently rederived the latter's
entire operative Section 1, and checked all actual-point, separator,
endpoint and scalar steps in the new barrier. The earlier h<=0 theorem
and its review are not being transferred to the enlarged domain without
this new verification.

Reviewed source:

`HIGH_SQUARE_LOW_LEFT_PORT_BARRIER_WITH_SIGNED_SMALL_SUPPORT.md`

* Length: 6,516 bytes.
* SHA256: `e2463dea33c2e66b97046c5727562be354e09f3f065e3dc04028e3a79a79dc58`.

The source remains unchanged. This is a force-free theorem about two
actual contained units, not a graph-family exclusion or a replacement
of an original force normal.

## 1. Exact accepted statement

The radius has the high/critical form

    R^2=(2+epsilon)^2+1/4<=1105/256,
    0<=epsilon<1/60.

The actual square H is

    H=[h-1,h] x [g-1,g],
    h<=epsilon, 37/50<=g<=1.

There is no actual unit B, with disjoint open interior from H and
contained in the same disk, containing both original points P,V with

    P_x<h, P_y<7/10,
    h-1<=V_x<=h, V_y>=g.

The V abscissa interval is closed, V_y=g is allowed, and V may equal
H's top-left corner. There is no positive HB edge, degree, force, circle
load, physical circle-contact or coefficient premise. Every normal used
for separation in the proof is auxiliary physical geometry, not a
reselected original stress normal. The proof retains the actual P,V.

## 2. Exact direct pins and the transitive LF identity

Both direct source pins match the current checkout bytes:

| Input | SHA256 | Operative use |
| --- | --- | --- |
| HIGH_VERTICAL_STRIP_AND_NEAR_EAST_UNIT_CENTER_EXCLUSION.md | `75def83e3a67168eb28014641ddfa3d53372028514facaab09529903ba6090f8` | Complete force-free Section 1 center bound; no Section 2 two-unit conclusion is imported. |
| HIGH_SQUARE_CORNER_AND_LOW_LEFT_PORT_CIRCLE_BARRIER.md | `f69af5d923356a063c25b108586b9a1905acfa924d244cd25622bcc0273d4176` | Predecessor comparison only; the new separator/corner proof is rederived with its new constants. |

The high-strip input prints historical center-bound digest
`6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb`.
I checked the exact reconciliation:

* Current `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` has 8,686 bytes and
  SHA256 `20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf`.
* Appending exactly one LF to those current bytes gives the printed
  historical digest `6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb`.

No source was edited to reconcile this identity. Only that input's
force-free Section 1 center estimate is needed: the farthest actual
corner gives |c|^2+|c|+1/2<=R^2, hence |c|<=3/2+epsilon. No loaded
triangle equation or resultant theorem is used by the barrier.

## 3. The complete high-strip center estimate

For an actual contained T in x>=1-epsilon, the directional half-width
bound and the center estimate give

    89/60<c_x<91/60.

I checked the full vertical bound |c_y|<3/25, rather than treating it
as a center heuristic. If T is aligned, its outer two actual corners
give

    |c_y|<=sqrt(1/4+8epsilon)-1/2<3/25.

The final strict comparison follows from epsilon<1/60 and
(31/50)^2-23/60=2/1875>0.

For an oblique square, reflection of y and interchange of its inward
axes give the actual minimum-x vertex (H,q), H>=1-epsilon, and axes

    (a,b), (b,-a), 0<a<=b, a^2+b^2=1.

Writing w=a+b and Delta=b-a, the center bound gives w<=1+4epsilon<16/15.
Monotonicity of a+sqrt(1-a^2) on this interval gives a<1/14, and then
b>199/200 and Delta>139/150. The exact positive squared comparisons
printed in the input verify all three strict bounds.

The actual opposite and lower-right corners give, with
Y=c_y=q+Delta/2,

    Y<=sqrt(R^2-(H+w)^2)-Delta/2,
    Y>=w/2-sqrt(R^2-(H+b)^2).

Replacing H by 1-epsilon weakens both inequalities. For the upper
expression, with X=1-epsilon+w and S=sqrt(R^2-X^2), its derivative
with respect to a is

    [-X*Delta/S+w/2]/b<0.

Here X>119/60, Delta>139/150, S<31/50 and w<16/15 give the strict
sign. The feasible interval is connected back to a=0 because X
increases with a. A zero radicand is included by continuity; a negative
one forbids containment outright.

For the lower expression put X0=1-epsilon+b and
S0=sqrt(R^2-X0^2). Then S0>=1/2, X0<=2, and the derivative is

    [Delta/2-X0*a/S0]/b
      >[139/300-2/7]/b>0.

Consequently its minimum and the upper expression's maximum are their
aligned a=0 values. These are respectively
1/2-sqrt(1/4+8epsilon) and its negative. This proves the complete
vertical center bound, with both signs of tilt, aligned limits, all
physical masks and epsilon=0 retained.

## 4. The new whole-unit transverse cap

The horizontal width w_T of a unit square is twice its directional
half-width. Since min_T x>=1-epsilon,

    w_T/2=c_x-min_T x
      <=(3/2+epsilon)-(1-epsilon)
      =1/2+2epsilon<8/15.

A square has the same width in two orthogonal coordinate directions:
both equal the sum of the absolute sine and cosine of its orientation.
Combining the full vertical half-width with the proved center bound
therefore gives, for every actual point of T,

    |T_y|<3/25+8/15=49/75<7/10.

Reflection gives the same cap for a unit in x<=-(1-epsilon). This is
a whole-square bound, so it applies to arbitrary original side means
and endpoints, regardless of whether the unit touches the circle.

## 5. Closed chord endpoints and the complete physical separator cover

Put A0=1-h>59/60 and U=(-A0,g), the actual top-left corner of H.
The actual chord PV is contained in B. If P_x>-A0, then P lies strictly
between the two vertical sides of H, while P_y<7/10<g. Its chord toward
V, whose abscissa is in the closed same strip and whose height is at
least g, enters int(H) immediately below height g. A strict convex
combination has interior abscissa even when V is at either strip
endpoint. The argument also applies when V_y=g. Hence P_x<=-A0.

For two rectangles with disjoint open interiors, the separating-axis
theorem gives a closed separator with an axis owned by one of the
rectangles. It follows, for example, by using the side normals of their
Minkowski difference; the touching case supplies a weak separator. It
is legitimate here as auxiliary geometry, with no stress modification.

All H-axis separations are excluded. P rules out B entirely to the
right or above. V rules out B entirely below. B entirely to the left
would be in x<=h-1<=-(1-epsilon), and the whole-unit cap would contradict
V_y>=g>=37/50.

For a B-owned separator directed from H to B, the Northeast cone is
excluded by P_x<h and P_y<g. The Southeast cone is excluded by
V_x<=h and V_y>=g>g-1; the Southwest cone is excluded by V_x>=h-1
and the same strict vertical inequality. Axis endpoints were already
covered. Thus the only possible direction is

    n=(-s,c), s,c>0, s^2+c^2=1,
    t=(c,s).

Because n is an actual own axis of B, its full occupied square is

    B=[k,k+1]n+[ell,ell+1]t,
    k>=H0=A0*s+g*c>0,
    T0=-A0*c+g*s.

The unchanged points satisfy P.t<T0<=V.t. The first strict inequality
uses P_x<=-A0 and P_y<7/10<g; the second uses both closed V coordinate
bounds. Thus T0 lies in B's actual t interval even if V=U. In particular
the actual far-side point (k+1)n+T0*t belongs to B.

## 6. Exact direction and actual far-corner contradiction

Containment of that real far-side point gives

    R^2>=(k+1)^2+T0^2
       >=A0^2+g^2+2H0+1.

Therefore H0<91/100, since

    (59/60)^2+(37/50)^2+1+2*(91/100)-1105/256
      =26119/1440000>0.

For s in [1/3,1], the concave function

    (59/60)s+(37/50)sqrt(1-s^2)

has its minimum at an endpoint. Its endpoint at 1 is 59/60>91/100;
at 1/3 it is greater than 4583/4500>91/100, using sqrt(8/9)>14/15.
This contradicts H0<91/100 throughout that interval. Hence s<1/3
and c>9/10. Also

    T0<-(59/60)(9/10)+1/3<0.

Set eta=g-7/10>=1/25. The exact conversion to physical y is

    P_y-g=c*(P.n-H0)+s*(P.t-T0)<-eta.

Since P.n>=k>=H0, this gives
ell<=P.t<T0-eta/s<0. Thus B's actual far corner
Z=(k+1)n+ell*t satisfies

    |Z|^2>(H0+1)^2+(T0-eta/s)^2.

Both positive roots on the right increase with A0 and g. The second
root can be written exactly as

    -T0+eta/s=A0*c+g*c^2/s-(7/10)/s.

Its comparison value at A0=59/60, g=37/50 is positive because
c>9/10 and s<1/3. Therefore replacing A0,g by these lower bounds
is valid before squaring. This yields

    |Z|^2>
      [1+(59/60)s+(37/50)c]^2
       +[(59/60)c-(37/50)s+1/(25s)]^2.

With

    K=1+(59/60)^2+(37/50)^2-2*(37/50)*(1/25),

independent expansion gives exactly

    K+(59/30)s+(37/25)c+(59/750)c/s+1/(625s^2).

Using c>9/10 and the arithmetic-geometric mean inequality,

    (59/30)s+(59/750)c/s
      >(59/30)s+177/(2500s)
      >=2sqrt((59/30)(177/2500))>37/50.

The last squared reserve is 117/12500>0. The other linear term is
greater than 333/250. Dropping only the positive final term gives

    |Z|^2>K+333/250+37/50
      =407461/90000
      =1105/256+303751/1440000,

contradicting containment of this actual corner. Every comparison is
uniform on the full remaining direction interval, without sampling.

## 7. Conclusion and exact limitations

The complete force-free barrier holds for all h<=epsilon, including
h=epsilon and epsilon=0, throughout its stated high/critical radius
domain. It retains both V horizontal endpoints, V_y=g, V=U, all actual
square orientations and every original application or mean supplied by
a caller.

No conclusion from the high-strip input's separate two-unit exclusion
is needed. No boundary load or original HB edge is assumed. No normal
is reselected, no square is moved, and no original equation is shortened.
A graph application must separately provide the actual P,V and the
height bounds. This review grants no original-family closure credit.

No Lean compilation, CI, pose search, numerical exclusion, metadata
edit, commit or remote action was performed. The frozen sources and
their original scopes remain unchanged.
