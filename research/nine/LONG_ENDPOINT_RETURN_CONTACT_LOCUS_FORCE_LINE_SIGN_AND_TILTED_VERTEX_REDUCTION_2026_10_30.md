# Long endpoints: the complete return-contact locus, force-line sign, and tilted vertex reduction

Date: October 30, 2026 UTC.

**Status: complete proposed hand family reductions, awaiting independent
full review. No sharp seven-body exclusion or original ledger change is
claimed.**

The first result is force-free: a physically boundary endpoint of a
support-gap-two pair can contact an above-side boundary unit only on
its upper transverse own side. Its inner endpoint vertex is retained,
with the entire actual common-normal cone. The second result uses full
endpoint moment balance and gives the sign of a genuine long-channel
force line, even for arbitrary endpoint degree under an explicit
full-star hypothesis. The final results use full true degree two at
the endpoints. If either endpoint is tilted relative to the long
normal, both actual direct return means must be the upper-inner endpoint
vertices. Both physical circle atoms, whenever present, remain in the
proof. No all-owned selection, neighbor-owned normal, or point-contact
genericity is assumed.

## 1. Geometry and exact endpoint constants

All actual unit squares have pairwise disjoint open interiors and lie
in a disk centered at the origin with squared radius

    q=R^2 <= Q=1105/256.

Put M=91/60 and L=89/60. Every unit center c has |c|<M: its maximum
squared corner norm is at least |c|^2+|c|+1/2, and the value of this
last expression at M exceeds Q by 31/57600.

Suppose actual squares A,B have a signed support gap of at least two
in direction e_x. Thus

    (c_B-c_A)_x >= 2+h_A+h_B,                            (1)

where h_i is the actual halfwidth of endpoint i in the x direction.
The force-free coupled endpoint theorem, Sections 2--3 of
`TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md`,
gives

    c_A=(-X_A,y_A), c_B=(X_B,y_B),
    L<X_A,X_B<M, |y_A|+|y_B|<=1/8.                       (2)

The positive x endpoint B will be analyzed explicitly. Reflection
in the y axis gives every corresponding assertion for A without
changing which halfplane is called above.

Choose a dominant outward side axis u of B and its upper transverse
side axis v so that

    u=(a,epsilon*b), v=(-epsilon*b,a),
    a>=b>=0, a^2+b^2=1, det(u,v)=1.                     (3)

Here b=0 is the aligned case; epsilon is relevant only when b>0.
Equation (1), the center bound and the other endpoint halfwidth at
least 1/2 give

    2h_B=a+b<16/15.

Consequently

    a-b>9/10, b<1/12<2/15.                              (4)

Indeed (a-b)^2=2-(a+b)^2>194/225>(9/10)^2, and
2b=(a+b)-(a-b)<1/6.

Write the actual own-frame center coordinates of B as

    P=c_B.u, T=c_B.v.

They satisfy

    P-|T| >= (a-b)X_B-(a+b)|y_B|
            > (9/10)(89/60)-(16/15)(1/8)
            =721/600>1,                                (5)
    |T| <= b X_B+a|y_B|
         < (2/15)(91/60)+1/8=589/1800<1/2.              (6)

In particular P-1/2>0 and T+1/2>0. No assumption that X_B or
|c_B| is at least 3/2 has been used.

We will also use the slightly sharper elementary orientation bounds

    b<7/100, a>399/400.                                 (7)

To verify them, b<1/12 gives a>99/100. Further,
ab=((a+b)^2-1)/2<31/450, so b<62/891<7/100; the last
comparison has reserve 37/89100. Finally
1-(7/100)^2-(399/400)^2=3/32000>0.

## 2. The actual contact lens, including support means

Let p be any common point of two actual units and let n be any actual
unit common support normal, directed from the first unit toward the
second. Then

    p-n is in the first unit, p+n is in the second unit. (8)

For completeness, in a unit square's own axes a nonzero component of
n exposes the corresponding coordinate endpoint. Moving inward by n
changes that coordinate by at most one and leaves it in the closed
unit interval; a zero component leaves the coordinate unchanged. This
works at a support vertex, at every point of a supporting side, and at
every actual weighted support mean.

Containment of both points in (8) gives the exact inequality

    |p|^2+1+2|p.n| <= q,
    |p|^2 <= q-1 <=849/256.                             (9)

This is the contact-lens argument independently written in
`EXACT_CONTACT_LENS_AND_FAR_ENDPOINT_POSITIVE_LOAD_AT_THIRTY_NINE_TWENTIETHS_2026_10_30.md`.
The elementary proof above is included so that every use here also
specifies the actual point and normal being retained.

Every point of B's outward own side has global x coordinate at least

    X_B+(a-b)/2 >89/60+9/20=29/15.

But (29/15)^2-849/256=24271/57600>0. Equation (9)
therefore shows that this entire closed outward own side, including
both vertices, cannot contact any other actual unit.

## 3. Complete reconstruction of the inward-owned-face lemma

We use precisely the local face assertion of
`C7_HIGH_CENTER_CONTACT_TYPES.md`, Section 1. Its proof is repeated
here; none of that source's all-owned C7 hypotheses is needed.

Suppose a physically boundary unit is written in an outward own frame
as

    S=[kappa-1,kappa] x [ell-1,ell],
    kappa>=ell>=1/2, kappa^2+ell^2=q,
    kappa-ell>1.                                       (10)

No unit contained in the disk and in x<=kappa-1 can both meet the
inner side of S and physically touch the containing circle.

Put x=kappa-1>ell. Such a unit would have a maximal-x vertex
p=(x,y) with ell-1<=y<=ell. If its maximal-x support is a side,
the two overlapping supporting intervals both have length one, so
an endpoint of the neighbor's interval lies in the interval of S.
This proves the vertex assertion even for a shared side or an endpoint
contact.

Write its two inward unit side directions at p as

    w_1=(-cos theta,sin theta),
    w_2=(-sin theta,-cos theta), 0<=theta<=pi/2.

The two adjacent corner norms obey

    |p+w_i|^2 <= x^2+ell^2+1+2ell
               =q-2kappa+2ell+2<q.                    (11)

For the opposite corner use

    p.(w_1+w_2) <= -x+|y| <=-x+ell.

It follows that

    |p+w_1+w_2|^2 <=x^2+ell^2+2-2x+2ell
                    =q-4kappa+2ell+5<q.              (12)

The final strict inequality follows from
4kappa-2ell-5>2ell-1>=0. The original corner also has
|p|^2<=x^2+ell^2<q. All four corners are strictly inside the
disk, proving the assertion.

Now suppose B itself physically touches the circle. Since P>0,
its outer-u corner with the sign of T is farthest. Reflecting its
transverse own axis if necessary, the parameters in (10) are

    kappa=P+1/2, ell=|T|+1/2.

Equation (5) gives kappa-ell>1. Therefore no physical-boundary
neighbor can have an actual common separator with outward normal
-u from B. This excludes the inward own face as a support face for
such a neighbor. It does not discard either endpoint vertex under a
different common normal.

## 4. Force-free return-contact locus and moment signs

Assume B physically touches the containing circle, and let C be any
other actual physical-boundary unit wholly in the open halfplane y>0.
Every actual common contact point and common normal of B,C has the
following alternatives.

The lower transverse own side of B has global height at most

    y_B-(a-b)/2 <=1/8-9/20=-13/40<0,

so cannot meet C. The outward own side is entirely contact-free by
Section 2. A relative-interior point of the inward own side has only
the actual outward support normal -u, excluded by Section 3. Its
lower endpoint is already excluded by the lower-side bound.

Thus every such contact point belongs to the upper transverse own
side, excluding its outward endpoint. More precisely:

* At a relative-interior point of that side the common normal from
  B into C is v. Its origin moment is p cross v=p.u>0.
* At the upper-inner vertex

      p=(P-1/2)u+(T+1/2)v,

  every original actual common normal has the form

      n=-alpha*u+beta*v, alpha>=0, beta>0,
      alpha^2+beta^2=1.                                (13)

  The strict beta follows because beta=0 is the inward-own-axis
  separator excluded in Section 3. Its origin moment is

      p cross n=(P-1/2)beta+(T+1/2)alpha>0.             (14)

The case alpha=0 is retained at this stage. Equation (13) is the
entire physically permitted cone, not a normal-ownership assertion.
In particular it includes an original vertex/vertex contact normal
whenever that normal belongs to both actual support cones. At a
shared-side mean the first alternative and its endpoint limits apply.

Reflection in the y axis proves the corresponding result for A: its
contacts with any above-side physical-boundary unit lie on its upper
transverse own side, and every outward contact force there has
strictly negative global origin moment. The upper-inner vertex and
its entire actual common-normal cone are again retained.

This proves a force-free contact-locus theorem for every boundary
neighbor in the indicated halfplane, independently of graph degree,
stress weight, normal ownership or contact-segment position.

## 5. Full-star moment balance fixes the force-line sign

Now let

    A -- U -- V -- B

be a genuine positive long channel. The two internal units are
unloaded of full true positive degree two, and their original force
and angular equations hold. The exact internal transmission argument
in `LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md`,
Sections 3--5, gives the original actual contact means

    q_A=(s-1,t), q_M=(s,t), q_B=(s+1,t),
    |s|<1/60, |t|<=9/16,                               (15)

with the common signed normal e_x and equal positive force magnitude.
The internal widths are both exactly one. In particular (1) holds,
without altering either endpoint pose or application point.

Use the following explicit **full-star hypothesis** at an endpoint:
every positive pair contact other than its long-channel edge goes
to an actual physical-boundary unit wholly in y>0, and there is at
least one such additional positive edge. The endpoint itself is
physically boundary. All of its full endpoint force and angular
equations, circle atoms and actual pair means are retained.

At B the long outgoing normal is -e_x, whose origin moment at q_B
is t. Every other positive pair contact has strictly positive origin
moment by Section 4. Every original circle force is radial and has
zero origin moment. Hence the full angular equation is

    mu_long*t + sum mu_j*(p_j cross n_j)=0,
    mu_long>0, every term in the nonempty sum positive.

It follows that

    t<0.                                                (16)

At A the long normal is e_x, with moment -t, and all the other
moments are strictly negative. Its full angular equation gives the
same conclusion. One endpoint satisfying this full-star hypothesis
already suffices for (16). Arbitrarily many other positive edges at
that endpoint are allowed, provided every one satisfies the stated
physical neighbor condition. No circle-clear or below-side additional
edge is silently omitted.

## 6. A tilted endpoint has a lower-inner long contact and forces t<-1/2

Suppose B satisfies the full-star hypothesis and is tilted: b>0.
By (16), its actual minimum-x long contact has negative height. If
epsilon=+1 in (3), that uniquely exposed vertex has height
y_B+(a-b)/2>-1/8+9/20>0, a contradiction. Thus

    u=(a,-b), v=(b,a),
    q_B=c_B-(u+v)/2=(s+1,t).                            (17)

In particular its upper-inner vertex is exactly q_B+v. All of its
return normals in (13) have global y component alpha*b+beta*a>0.
The y component of the full force equation therefore forces the
total circle resultant to have strictly negative y component.

If T>0, B has exactly one physical circle corner, the outer-upper
corner q_B+u+v. Its global y coordinate is

    t+a-b >=-9/16+9/10=27/80>0,

which is impossible. Hence

    T<=0.                                               (18)

If T<0, the only physical circle corner is q_B+u. If T=0,
both outer-u corners are physical circle corners and both may carry
positive circle weight. They are not discarded: their total
resultant alone is known to have negative global y component.

The identity c_B=q_B+(u+v)/2 gives

    T=b(s+1)+a*t+1/2.

Consequently

    t <= -(1/2+b(s+1))/a <-1/2.                        (19)

In particular y_B=t+(a-b)/2<0. The reflected conclusions hold
for a tilted A under its full-star hypothesis, with s+1 replaced
by 1-s in its reflected chart.

If both endpoints satisfy the full-star hypothesis and either is
tilted, the common line has t<-1/2. A possibly aligned other endpoint
has its actual long contact on its inward vertical side, so its center
height is at most t+1/2<0 as well. For a tilted other endpoint (18)
already gives its negative center height. Thus both long endpoints
have negative center heights in this tilted branch.

## 7. A true degree-two tilted endpoint cannot use its own upper-axis return normal

Assume now that B has exactly two positive pair contacts in its full
certificate: the long edge and one above-side physical-boundary return
edge. Its own full-star condition therefore holds. Suppose b>0 and
the actual return normal is v. Its original mean p is on the upper
own side and can be written

    p=q_B+v+zeta*u, 0<=zeta<=1.                         (20)

Let K=P+1/2<121/60. Normalize the positive total circle load so its
mean vector in the own frame is (K,eta), and scale both contact
magnitudes by twice that total load. The load is positive because
the return force has strictly positive y component and the long
force has zero y component.

If T<0 put w=1/2-T>=1/2. The only circle corner is (K,-w),
the long mean has own coordinates (K-1,-w), and (20) has own
coordinates (K-1+zeta,1-w). The u and v force equations give

    scaled_mu_long=K/a,
    scaled_mu_return=bK/a+w.

The angular equation about the actual q_B gives

    scaled_mu_return*zeta=w.

Therefore

    zeta=w/(w+bK/a) >= a/(a+2Kb).                       (21)

If T=0 the two actual circle corners have own coordinates
(K,+/-1/2), and their original weights give an arbitrary
eta in [-1/2,1/2]. The same full force and moment equations give

    scaled_mu_return=bK/a-eta>0,
    zeta=((K-1)eta+K/2)/(bK/a-eta).                     (22)

On the actual positive-denominator interval the last quotient is
strictly increasing in eta: its derivative numerator is
(K-1)bK/a+K/2>0. Its value at eta=-1/2 is
a/(a+2Kb), proving (21) also for every permitted two-corner
weight. No individual positive circle atom is assumed to point down.

In global coordinates (20),(21) and (7),(15) yield

    p_x=s+1+b+a*zeta
       >59/60+b+(399/400)^2/(1+(121/30)b).              (23)

Define g(b)=b+(399/400)^2/(1+(121/30)b). It is strictly
decreasing on 0<=b<=7/100. For an exact derivative check, the
largest squared denominator is less than (121/30)(399/400)^2
by 170554543/72000000. Its endpoint value satisfies

    g(7/100)=2603447/3077600,
    g(7/100)-21/25=18263/3077600>0.

Thus

    p_x>59/60+21/25=547/300,
    (547/300)^2-849/256=11719/1440000>0.                (24)

But p is an original contact mean, so (9) contradicts (24).
This excludes the own upper-axis return normal v completely,
including a mean at either endpoint of its permitted support side.

By Section 4, the remaining return mean is consequently exactly

    p_B=q_B+v,
    n_B=-alpha*u+beta*v,
    alpha>0, beta>0.                                   (25)

The statement retains every original common normal in this strict
cone. It does not assert that the neighbor owns the normal or that
the point lies in the relative interior of a neighbor side.

## 8. An aligned true degree-two endpoint cannot use its own upper-axis normal when t<=-1/2

This is a separate local assertion, needed when only one long endpoint
is tilted. Suppose the right endpoint is aligned, has exactly its long
edge and one above-side boundary return edge, and t<=-1/2. Put

    c_B=(X,y), K=X+1/2, w=1/2-y.

Because the actual long mean lies on its inward vertical side,
y<=t+1/2<=0. Equation (2) therefore gives

    1/2<=w<=5/8, K^2+w^2=q, K^2<=Q-1/4.               (26)

The lower outer corner (K,-w) lies on the containing circle. If y=0,
the other outer corner may carry a circle weight too; retain both.

Suppose the return normal is e_y. Its mean is p=(p_x,1-w).
The normalized circle mean is (K,eta), where -eta<=w. Force
balance requires eta<0 and gives the ratio
mu_long/mu_return=K/(-eta). Full origin-moment balance then gives

    p_x=(-t)K/(-eta) >= K/(2w).                         (27)

By the original normal-chord assertion (8), the neighbor contains
p+e_y=(p_x,2-w). Its squared norm minus q is at least

    K^2/(4w^2)+(2-w)^2-(K^2+w^2)
      =K^2*(1/(4w^2)-1)+4-4w
      >=-(9/25)K^2+3/2
      >=-(9/25)(Q-1/4)+3/2
      =231/6400>0.                                     (28)

Here w<=5/8 gives 1/(4w^2)>=16/25 and 4-4w>=3/2.
Equation (28) contradicts containment in the original disk.
Thus the aligned endpoint's upper-axis return normal is impossible
under t<=-1/2, with both radial circle weights explicitly allowed.

Section 4 now forces its actual return mean to be its upper-inner
vertex, with strictly positive inward and upward normal components.
The reflected assertion holds at the left endpoint.

## 9. Complete tilted-branch reduction for the opposite long/short seven-cycle

Consider the original seven-body positive cycle

    A -- U -- V -- B -- C -- W -- D -- A,

where U,V,W are unloaded of full true positive degree two and A,B,C,D
physically touch the containing circle. Suppose the cycle has the
compatible physical embedding, retained circle spokes and full force
and angular certificate used by the existing cycle reductions. In
the radius window 79/40<=R<=sqrt(Q), the already proved return-side
localization permits one common reflection so that the whole original
squares C,D lie in y>1/120. No common frame with C,D or W is implied.

If A,B themselves have true positive degree two, every endpoint
hypothesis above is met by its actual direct join to D or C. The
full endpoint torque equations give t<0. If either A or B is tilted
relative to the long normal, Sections 6--8 imply simultaneously:

1. The original common long force line has -9/16<=t<-1/2.
2. Both endpoint center heights are strictly negative.
3. Both original positive direct return means are the upper-inner
   vertices of A,B, with strictly inward and upward components in
   their respective own normal cones.
4. Every physical circle corner and its original weight is retained.
   A tilted endpoint may be radial in its own frame and have both
   outer-own-face corners active.
5. All other original packing units, including both units outside
   this seven-cycle, retain their poses, contacts and independent
   orientations.

If the right endpoint is tilted, its explicit actual vertices are

    q_B, q_B+(a,-b), q_B+(b,a), q_B+(a+b,a-b),
    q_B=(s+1,t), a^2+b^2=1, b>0,

and its direct return mean is q_B+(b,a). The left counterpart is
the x reflection with its own independent a,b. An aligned endpoint's
upper-inner return vertex is retained at its actual height; no equal
endpoint height or equality of internal center heights is asserted.

The moment-sign result in Section 5 remains available more broadly
with arbitrary endpoint degree under its full-star premise. The
two-edge conclusions of Sections 7--9 do not automatically extend to
endpoints with additional positive forces.

**Remaining sharp task:** the original short channel still gives
dist(C,D)>=1, or its larger actual reserve if applicable. A complete
seven-body exclusion or sharp q>=Q theorem must combine this gap
with the two actual vertex joins in the tilted branch, or handle the
entire aligned-endpoint branch. This manuscript proves the displayed
uniform reductions only. It does not infer a common short normal,
neighbor ownership, vertical separation of joined squares, a solid
row, a changed circle mask or full sharp optimality.

## 10. Frozen inputs and verification boundary

| Source | SHA256 | Exact content used |
| --- | --- | --- |
| `TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md` | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` | Full force-free support-gap-two endpoint and coupled-height estimates |
| `C7_HIGH_CENTER_CONTACT_TYPES.md` | `68e94d3f80274c07f3a4f6c0d01eab753733b1e808838c6abf6e4448cfc481b8` | Section 1 local inward-owned-face assertion only, completely reconstructed in Section 3 |
| `LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md` | `dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05` | Original true two-transmitter means, side-normal widths, |s|<1/60 and |t|<=9/16 |
| `LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md` | `c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e` | Common whole-return-square halfplane in the seven-cycle caller |
| `EXACT_CONTACT_LENS_AND_FAR_ENDPOINT_POSITIVE_LOAD_AT_THIRTY_NINE_TWENTIETHS_2026_10_30.md` | `3e9a96293ae14e5ed3e9f2952c396cbef82d44ddd6a9643e54ab597a63e951e3` | Contact lens, also proved directly here in Section 2 |

The arguments use unchanged actual support points and means, full
force and moment equations, exact unit-side geometry and explicit
rational inequalities. No numerical packing, finite pose grid, Lean
compilation, CI execution, original gate mutation or remote publication
is asserted or used as a proof premise.
