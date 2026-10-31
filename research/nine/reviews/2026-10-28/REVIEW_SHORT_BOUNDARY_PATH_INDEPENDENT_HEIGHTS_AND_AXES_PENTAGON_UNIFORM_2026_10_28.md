# Independent review of the short boundary path strengthening

Date: October 28, 2026. Reviewer: pentagon_uniform.

**Verdict: PASS for the complete stated theorem.** No source edit is
needed. Independent nonnegative endpoint heights and either or both
exact horizontal inward normals are valid throughout the entire printed
domain. No upper radius bound or force-equilibrium premise is needed.

## 1. Frozen reviewed source and scope

I read and independently rederived the complete source
`SHORT_BOUNDARY_PATH_OWNED_ENDPOINTS_INDEPENDENT_HEIGHTS_AND_AXES.md`,
SHA-256
`0bb8e0d45fc6f4e664e4fd9a58532d6db44d654ae3533231672556b4e41229cb`.

The preceding frozen source is
`FOUR_BOUNDARY_PATH_OWNED_ENDPOINT_TANGENT_SIGN_OBSTRUCTION.md`,
SHA-256
`5e8cba82367da03c15710cd6060c3a009323413465a78acaf965f4b07ff29536`.
I authored that preceding proof, but not this new strengthening. This
review checks the complete new statement and proof independently, with
special attention to its additional endpoints. It does not transfer a
review to altered old bytes. Both current source pins were checked.

The theorem concerns two through four actual boundary units on an
actual touching path with the explicitly assumed counterclockwise
center lift. The original circle origin is retained. The two owned-side
points have opposite strictly positive abscissa magnitudes whose sum
is at most sqrt(2), separately nonnegative heights, and the displayed
full-circle-resultant tangent signs. Both side parameters include the
closed interval [0,1]. All physical masks and zero individual corner
coefficients remain.

## 2. The complete endpoint and physical-mask calculation

At the right endpoint, the support coordinate

    N=bX+ah>0

is strict because b>0 and X>0, including a=0 or h=0. Thus every
physical circle corner is on the far normal face: the squared-norm
increase at fixed tangent coordinate is exactly 2N+1>0.

If the center tangent coordinate tau were negative, its only farthest
tangent coordinate would be tau-1/2<0. Every actual circle atom would
therefore have strictly negative tangent coordinate. A nonzero
nonnegative resultant would violate its assumed nonnegative tangent
projection. Consequently tau>=0. When tau=0, the two actual far-face
corners may both be physical; the argument permits either coefficient
to be zero and assumes only the original resultant inequality.

For every rho in [0,1], the center abscissa is at least
X+(b-a)/2>0. Its height is (N+1/2)a+tau b>=0. Since its normal and
tangent coordinates are N+1/2>0 and tau>=0, its normal-to-center angle
v is nonnegative. Its actual center and normal angles therefore obey

    0<=phi<=delta<pi/2,       v=delta-phi.

If a=tau=0, this yields delta=phi=v=0 exactly. This endpoint is
consistent with all formulas and is not discarded. Reflecting the
left endpoint in the vertical coordinate axis reverses its oriented
tangent and changes its nonpositive tangent sign into precisely the
right-endpoint nonnegative sign. Its center lies in the closed upper
left quadrant. The two endpoint calculations use their own heights
separately; no equation between those heights enters.

## 3. The path lift and the entire zero-angle boundary

For every boundary center, r>=R-1/sqrt(2)>5/4 follows from R>=79/40.
For a contacting pair, its center distance is at most sqrt(2), so
the cosine law gives

    cos(gamma)
      =1+((r-s)^2-|c_1-c_2|^2)/(2rs)
      >=1-1/(rs)>9/25.

The actual minor gap is therefore less than theta=acos(9/25). By
the source's successive-gap hypothesis, each positive lifted advance
is this minor gap. The first center has angle pi-delta_L and the last
has angle delta_K. Their strictly increasing lift of total advance
less than 2pi can only have advance

    pi+delta_L+delta_K.

This includes exactly pi if both deltas vanish. With at most three
edges, delta_L+delta_K<alpha=3theta-pi follows. With only one or two
edges, theta<pi/2 already contradicts the required advance at least
pi; no exceptional short path survives.

I checked the exact trigonometric constants:

    cos(alpha)=13959/15625>89/100,
    sin(alpha)=1204 sqrt(34)/15625<9/20.

Since pi/3<theta<pi/2, initially 0<alpha<pi/2. The positive comparison
4*13959^2>3*15625^2 then gives alpha<pi/6. These are strict constants
independent of any upper radius bound. Every actual delta lies in the
same closed-at-zero interval required by the later calculations.

## 4. The complete continuous scalar estimate

Put d=sqrt(R^2-1/4)-1 and r_0=d+1/2. The source's exact radius
comparison is

    (79/40)^2-1/4-(19/10)^2=13/320>0,

so d>9/10. Since both center own coordinates are nonnegative at the
endpoint, its actual farthest-corner identity is

    R^2=r^2+r(cos(v)+sin(v))+1/2.

This includes v=0 with both physical tangent corners. Subtracting
the identity r_0^2+r_0+1/2=R^2 gives the printed factorization.
Because 0<=v<pi/6, its right side is nonnegative and no more than
r sin(v). Also r_0+r+1>2r. It follows that

    r_0>=r>=r_0-sin(v)/2.

The original closed-side parameter implies

    X>=r cos(delta)-(cos(phi)+sin(phi))/2.

Writing c=cos(delta), s=sin(delta), I rederived the exact identity

    cos(phi)+sin(phi)+c sin(delta-phi)
      =(1+cs)cos(phi)+s^2 sin(phi).

Cauchy--Schwarz gives the norm bound sqrt(1+2cs+s^2). The next
squared excess is exactly

    (c+(6/5)s)^2-(1+2cs+s^2)
      =(2/25)s(5c-7s)>=0.

All terms being compared are nonnegative. On 0<=delta<pi/6, one
has 5c-7s>0; at delta=0 the displayed excess is zero, so that exact
axis endpoint is valid. Substitution yields, with no common-height
step,

    X>=g(delta)=d cos(delta)-(3/5)sin(delta).

On the full closed interval [0,alpha], g is positive by the stated
uniform rational reserve, strictly decreasing because
g'=-d sin(delta)-(3/5)cos(delta)<0, and strictly concave because
g''=-g<0. For nonnegative x,y with x+y<alpha, concavity on
[0,x+y] gives

    g(x)+g(y)>=g(0)+g(x+y)>g(0)+g(alpha).

When x+y=0, both x and y are zero; the first inequality is directly
equality and the second is still strict by monotonicity and alpha>0.
Thus neither the concavity proof nor the final strict contradiction
divides by a zero interval or silently assumes a positive delta.

The actual endpoint sum is therefore greater than

    d(1+cos(alpha))-(3/5)sin(alpha)
      >(9/10)(1+89/100)-(3/5)(9/20)
       =1431/1000>10/7>sqrt(2).

This contradicts the original abscissa-sum premise in every additional
axis and independent-height case. No upper bound on R was used at
any stage.

## 5. Exact acceptance and caller boundary

The full new theorem passes. It preserves actual endpoints, normal
ownership, all complete side parameters and physical circle masks.
It does not use force balance at an endpoint or an internal path unit,
and no degree is shortened. The center traversal and the two tangent
signs remain explicit caller obligations.

In particular, a normal that is an axis of a neighboring unit is not
automatically an owned side axis of the boundary endpoint. This
strengthening does not supply missing ownership. Likewise separate
nonnegative heights must hold about the original circle origin; a
translation of a local unit chart does not establish them.

No whole original fine family, coarse cell or new label is closed by
this generic theorem alone. This review changes neither source,
metadata nor graph/load flags. Only the two byte hashes were checked
by a script. All mathematical verification was by hand; no Lean,
CI, pose sampling, numerical exclusion, commit or publication was used.
