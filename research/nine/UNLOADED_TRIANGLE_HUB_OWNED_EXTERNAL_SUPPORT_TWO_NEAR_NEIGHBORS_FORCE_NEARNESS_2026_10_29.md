# Two actual near neighbors force an unloaded triangle hub near the origin when it owns the external normal

Date: October 29, 2026 UTC. Author: root_triangles continuation.

**Status: complete proposed uniform hand theorem, frozen for full
independent review.** The theorem has no genuine-leaf premise and no
load or degree assumption at its three neighboring units. Its nine-unit
corollary excludes the entire stated original motif, not an angle slice.

## 1. Exact full-star statement

Let U,Q,V,W be four distinct actual contained unit squares with
pairwise disjoint open interiors. Work in a circle about O with

    R^2<=1105/256,
    0<=delta<=1/60.                                        (1)

Assume U has zero total circle load and its entire positive pair
neighborhood is exactly Q,V,W. Retain the original positive magnitudes,
outward normals, applications and complete shared-side means:

    lambda*n + mu*g + nu*k = 0,
    lambda*det(P,n)+mu*det(Q_V,g)+nu*det(Q_W,k)=0,
    lambda,mu,nu>0.                                       (2)

The names Q and Q_V are respectively the actual external unit and the
original U--V application; they are not interchangeable.

Require the following actual physical hypotheses:

* the external normal n from U to Q is an own side axis of U;
* Q and V each meet the closed disk D_delta;
* V and W physically touch.

The last contact need not carry positive stress. Q,V,W retain arbitrary
true degrees, additional positive forces, total circle loads, physical
circle masks and zero coefficients. U itself may physically touch the
circle with zero total circle load. Every original support mean remains
unchanged, including each endpoint. No force equation is imposed at a
neighbor.

**Nearness theorem.** The same actual U meets the closed disk D_delta.

**Nine-unit corollary.** In the original nine-square problem, suppose
there is an additional actual unit Z, distinct from U,Q,V, meeting
D_(1/60). Then the entire motif above is impossible. Z need not have a
specified force, load, orientation or graph role. It may be W when that
unit meets the stated physical near disk.

## 2. Complete unit support facts

We record the elementary facts used in the exhaustive original normal
cover. They preserve all side means and need no containing circle.

### 2.1. Strict unit reach

Let P_0 be an actual minimum-f support point of a unit square S.
For a unit direction e with f.e<0,

    max_(z in S) e.(z-P_0)<1.                              (3)

At a vertex, the two inward orthonormal axes have nonnegative f
components. They cannot both have positive e components, since that
would give f.e>=0. The sole possible positive component is strictly
below one: equality would make e that inward axis and again give
f.e>=0. At a side-interior point, moving inward along f decreases
the e projection, while the entire original tangent interval contributes
at most |e.Jf|<1. Side endpoints are included by the vertex proof.

Also, for every such actual minimum-f point,

    P_0+f belongs to S.                                    (4)

At a vertex the inward-axis components of f belong to [0,1], so this
is an actual point of its unit coordinate box. At a side point, the
normal translate goes to the opposite actual side. Thus (4) retains
arbitrary side means and both endpoints too.

### 2.2. A physical triangle at one own normal

If V,W physically touch and an actual U-to-V normal g is an own
axis of U, then every original U-to-W normal k satisfies

    g.k>=0.                                               (5)

Normalize U=[0,1]^2 and g=East. If k had negative horizontal
component, its original U application would lie on x=0. Applying
(3) to W in the East direction would put its entire closed square
in x<1. But V lies in x>=1, so they could not touch. This proves
(5), including the perpendicular equality endpoint. It can be used
with either of the two return units as the owned one.

### 2.3. Opposite strict vertices cannot carry touching returns

For U=[0,1]^2, a return at (1,1) with strict Northeast normal lies
entirely in x>0,y>0 by (3). A return at (0,0) with strict Southwest
normal lies entirely in x<1,y<1. Any common point would belong to
int U, impossible for another actual square disjoint in open interior.
The other opposite-corner pair follows by reflection. This argument
does not assign a normal owner or special mean on either return.

## 3. The external own face is within delta of O

Apply the complete radius-free theorem
UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md
to the actual full U3 equations (2), external unit Q, and touching
returns V,W. Its entire original normal/mean cover gives

    n.z<h_U(n) for every actual z in V union W.             (6)

Let H=h_U(n). An actual point of Q in D_delta lies in its original
half-plane n.z>=H, so H<=delta. An actual point of V in D_delta
and (6) give H>-delta. Therefore

    -delta<H<=delta.                                      (7)

For delta=0 these two inequalities already contradict each other;
there is no such original configuration. We may therefore suppose
delta>0 for the rest of the proof.

Rotate the actual own axis n to West. Since it is genuinely owned
by U, its exact horizontal interval is [x,x+1], where x=-H and

    -delta<=x<delta.                                      (8)

No original transverse coordinate of the external mean P has been
fixed or moved. It remains on that complete actual West side.

Suppose, for contradiction, that U avoids closed D_delta. Its other
own interval cannot contain zero: otherwise the point on that interval
with transverse coordinate zero and horizontal coordinate nearest zero
would have norm at most |x|<=delta. Reflect vertically if necessary.
The complete actual U rectangle is then

    U=[x,x+1] x [y,y+1], y>0.                              (9)

The actual near point in V gives its unchanged support bound

    h_U(g)<=delta.                                        (10)

## 4. Exhaustive force and physical-return cover

In (9), East, North and strict Northeast are impossible for g by
(10). Indeed their respective heights are x+1>=59/60, y+1>1,
and a positive unit combination of those two heights, all greater
than delta. This excludes all three whole features, not only axes.

The remaining original g features are West, South, strict Northwest,
strict Southwest and strict Southeast. The full force equation is

    nu*k=lambda*East-mu*g.                                (11)

All classifications below concern this unchanged full third force.

### 4.1. West and South

If g=West, (11) makes k=East. Their owned normals are opposite,
contradicting (5) and the actual V--W contact.

If g=South, (11) makes k strictly Northeast. Its dot product
with the U-owned South axis is negative, again contradicting (5).
Both entire original axis-side mean intervals have been retained.

### 4.2. Strict Northwest and Southwest

For g=(-a,b), a,b>0, (11) has components
(lambda+mu*a,-mu*b), so k is strict Southeast. The original V
and W applications are U's upper-left and lower-right vertices,
contradicting Section 2.3.

For g=(-a,-b), a,b>0, (11) is strict Northeast. Its original
application is opposite V's lower-left application, giving the
same contradiction. These cases use no feature assumption at V,W.

### 4.3. Strict Southeast, including the force equality endpoint

Write g=(a,-b), a,b>0. Then

    nu*k=(lambda-mu*a,mu*b).                              (12)

If lambda-mu*a<0, k is Northwest and its actual U vertex is
opposite the Southeast V vertex. Section 2.3 excludes it.

If lambda-mu*a=0, k is North, an own U axis with k.g<0.
Use (5) with W as the owned return to exclude this equality case.

Finally suppose lambda-mu*a>0. Then k is strict Northeast,
and the actual U--W application is

    P_+=(x+1,y+1),
    (P_+)_x>=59/60, (P_+)_y>1.

It is the unchanged minimum-k support point of W. Formula (4)
puts P_++k in that actual unit. Since k has positive coordinates
and k_x+k_y>=1,

    |P_++k|^2
      >(59/60)^2+2+118/60
       =1105/256+35551/57600
       >R^2.                                             (13)

This contradicts containment of W. It does not use a boundary corner,
positive circle load, own W axis or specific W support mean.

These five features, together with the three excluded at (10), are
the complete original normal circle. Every axis and every equality
endpoint has been covered. The assumption (9) is impossible, proving
that U meets D_delta.

## 5. Whole nine-unit consequence and precise scope

The nearness theorem gives three distinct actual units U,Q,V meeting
D_delta, hence D_(1/60). With any distinct fourth actual near unit Z,
the complete force-free theorem FOUR_NEAR_ORIGIN_UNITS_CAPACITY.md
gives total physical unit capacity at most eight. This contradicts
the original nine actual units. The other five units are all retained
with arbitrary orientations, loads, masks and degrees.

The generic theorem uses the full true U3 force and torque through
the strict touching-return separation input. Its subsequent force
cover still uses the entire vector sum (11). An additional positive
force at U would change this cover and is not silently permitted.
In contrast, every neighbor degree is arbitrary throughout.

The external own-axis premise is essential to this stated theorem.
No claim is made here for an external normal strict at U. No normal
selection rule is used anywhere in the theorem: it holds for each
original choice satisfying the actual equations and hypotheses.

The closed values delta=0 and delta=1/60, original side mean endpoints,
the perpendicular return endpoint and lambda=mu*a have all been
included. Physical boundary status with zero circle weights is allowed.

| Complete input | SHA256 | Exact used scope |
| --- | --- | --- |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Entire radius-free original unloaded U3 separation with arbitrary touching returns and all actual means |
| FOUR_NEAR_ORIGIN_UNITS_CAPACITY.md | 63560c355c1b4c385618f412f6b6c01946f664684e843aa4fef85d78cba07190 | Force-free total capacity eight for four distinct actual units meeting closed D_(1/60) |

No physical square, force, torque, normal, mean or circle weight is
altered. No numerical pose search, angle mesh, parameter certificate,
Lean build, CI, metadata change or remote write is used.
