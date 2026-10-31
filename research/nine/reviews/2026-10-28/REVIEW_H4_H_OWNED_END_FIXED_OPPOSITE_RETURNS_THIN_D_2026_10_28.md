# Independent review: fixed opposite return vertices at an H-owned unloaded pentagon end

Date: October 28, 2026 UTC. Reviewer: thin_d continuation.

**Verdict: PASS for the complete stated radius-free necessary-domain
theorem and both literal H4 end-spoke joins. The residual domain is
not excluded, and no complete original family is credited.**

## 1. Frozen source and full original scope

I read and independently rederived the entire source
`INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md`
at SHA256

    bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c.

Its complete actual graph is HA,HB,HC,HD,AB,BC,CD,DE,EA. H remains
unloaded with all four positive forces to A,B,C,D; D remains unloaded
with all three positive forces to H,C,E. A,B,C,E keep arbitrary true
degrees, all additional forces, every circle mask and weight, and every
original application or shared mean. The new proof uses no circle or
radius assumption.

I checked the full starting domain against the complete current recovered
shared-end source at SHA256

    ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6

and the full opposite-horizontal-sign source at SHA256

    8a938f2d49f6307fbf2a21630d419693e675e2c5103b75a949cb0abaf6ceee09.

They supply precisely H=[0,1]^2, HD North, strict Southwest HA,
max_A y<1, and HC Northeast or East, while D's actual bottom
singleton is P=(p,1), 0<p<1, with complete tilted axes
u=(a,b), v=(-b,a), a,b>0, a^2+b^2=1. No order between a,b or
restriction on a remaining CD/DE owner is introduced.

## 2. Sharpened support span and the complete CD visibility argument

The sharpened bound is valid for every actual minimum-n support
point Q of a unit and every unit e with n.e<0:

    max_K e.(Z-Q)<=sqrt(1-(n.e)^2).

At a vertex, both inward own axes have nonnegative n projection.
At most one can have positive e projection, since n is their
nonnegative linear combination. Maximizing a positive e projection
on the permitted semicircle gives the displayed perpendicular bound.
At a side mean, the inward n displacement has nonpositive e projection
and the complete unchanged unit tangent interval contributes at most
|e.Jn|. Both side endpoints and zero axis components are included.

I independently checked the whole-set visibility proof, not merely its
eventual force application. For Northeast HC, the actual S=(1,1)
has D coordinates (a q,-b q), q=1-p in (0,1). Its first coordinate
is strictly between zero and one. Any CD point of positive second
coordinate would give, on the actual C segment from S, a point of
int(D). This remains true if the CD point lies on either vertical
edge or the top edge.

For East HC the entire C is in x>=1, and any proposed CD point
with positive v coordinate obeys a Z_u>=q+b Z_v>0. Its first
coordinate is therefore positive. The original HC point still has
u coordinate below one and v coordinate negative, so a segment point
sufficiently near Z lies in int(D), including all endpoint cases.
The excluded P itself violates the actual HC support, in both HC
types. Consequently the full physical intersection really is confined
to P+t u with 0<t<=1.

## 3. Every D-owned CD case and every top-DE case is excluded

On that actual D edge the only surviving D-owned normal could be
-v. The other axis u at P+u cannot evade the contact-set result:
a C-side interior there would create additional intersections in
positive v, while a point-only vertex/vertex axis violates the retained
strict point-normal convention. This checks the full ownership cover,
including shared segments and original endpoint means.

With original CD force (0,-mu), complete D force balance makes DE
(gamma b,gamma a+mu), supported at P+u+v. Its world vertical
component is gamma+mu a>0. The support-span bound gives
min_E y>a+b>1, contradicting the real AE contact and max_A y<1.

Thus CD strictly exposes the singleton P+u with original force
(xi,-eta), xi,eta>0. The full DE vector is

    (gamma b-xi,gamma a+eta).

If xi<gamma b, it again exposes P+u+v and has positive world
vertical component, since

    gamma-xi b+eta a>gamma(1-b^2)+eta a>0.

The same strict whole-E separation applies. The conclusion xi>=gamma b
therefore covers all genuinely positive and zero horizontal endpoints
without an equation at E or C.

## 4. Complete upper-side DE means and the exact torque identities

At xi=gamma b write Gamma=gamma a+eta. The actual DE application
is the whole original side mean (tau,1), 0<=tau<=1. Taking the
complete D torque about P gives exactly

    -eta+tau*Gamma=0,
    tau=eta/Gamma, 1-tau=gamma a/Gamma.

The strict range 0<tau<1 is derived, not imposed. The world contact
height is 1+a+tau b. Applying the sharpened support span with
minimum normal v=(-b,a) and e=South yields

    min_E y>=1+a+tau b-b
           =1+a*(1-gamma b/Gamma).

I checked both complete proofs of Gamma>gamma b:

* In the Northeast HC row, the actual S=(1,1) belongs to C. Its
  minimum-CD-support inequality is exactly b*(q Gamma-gamma)>=0.
  Hence Gamma>=gamma/q>gamma>gamma b.
* In the East HC row, the actual point P+u belongs to x>=1 and
  lies strictly above every original HC point (1,s), 0<=s<=1.
  The CD force has positive horizontal component b Gamma. Its
  minimum-support inequality therefore requires the vertical
  component gamma b^2-eta a to be nonpositive. This gives
  Gamma>=gamma/a>gamma b. Equality in that vertical inequality
  and both HC mean endpoints are retained.

Thus min_E y>1 in the entire original upper-side DE case, contradicting
AE. There is no lost shared-mean or external-owner endpoint.

## 5. Exact residual and literal original-family joins

The surviving DE support is the strict singleton P+v. Complete torque
about P is

    -eta-(gamma b-xi)=0,

so xi=eta+gamma b. I recomputed the resulting original force table:

    H at (0,0): (-gamma b,-gamma a),
    C at (1,0): (eta+gamma b,-eta),
    E at (0,1): (-eta,gamma a+eta).

The two return vertices (1,0),(0,1) are opposite D vertices. The
corresponding world vectors are (X,Y_C),(-X,Y_E), where

    X=eta(a+b)+gamma ab>0,
    Y_C=eta(b-a)+gamma b^2,
    Y_E=eta(a-b)+gamma a^2,
    Y_C+Y_E=gamma.

The Northeast HC necessary inequality is q X>=eta+gamma b. The East
HC inequality is Y_C<=0, which forces a>b and
eta>=gamma b^2/(a-b), including equality. These are exactly the
unchanged support comparisons, with no radius estimate or hidden
loaded-two equation.

For H4_D0.L124 and H4_D0.L0124 the substitution is
(A,B,C,D,E)=(0,1,2,3,4). The source's notation 'H3 end-spoke' means
the edge H-to-3 in this substitution: the central H remains true
degree four, and the unloaded end D=3 remains true degree three.
For L124 the graph-preserving reflection also applies at unloaded
end 0. The loaded end of L0124 is never assigned an unloaded star.

The CD and DE normals may still be owned by C,E or be free. Both
original H4_D0 families, all other owner interfaces, the true E2
equation in the literal callers, and every circle/completion obligation
remain. This source proves a complete necessary-domain reduction only.

No mathematical gap, missing mean endpoint or false degree reduction
was found. I changed no frozen source or metadata. No Lean compilation,
CI, numerical pose certificate, additional normal selection or remote
operation was used for this review.
