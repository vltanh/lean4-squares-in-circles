# Independent review: the complete adjacent C4 double-load mixed family

Date: October 27, 2026.

Reviewer: rooted-blocks agent, independently of the author and root reviewer.

**Verdict: ACCEPTED for the entire original mixed family.** I read the
complete frozen source, checked the topology and local prerequisite
scopes, recomputed every force/torque identity and all quantitative
corner estimates, and found no missing endpoint or required correction.

Reviewed source:

    ADJACENT_C4_TWO_LOAD_MIXED_LEAVES_EXCLUSION.md
    SHA-256 6ca883322c305d248ce9dbc4ef6902b5be8e62719c1b20b14e5a5e8ace8af013

Exact entire fine gate:

    M6.B4L2.C4.ADJACENT.LCD.SD.

The actual cycle is A--B--C--D--A, with a D leaf at A and an S leaf
at B. The true degrees remain A3,B3,C2,D2,L1,M1; C and D retain their
positive total circle loads. The reflection swapping A,B and C,D
exchanges the two mixed orders for precisely this double-load mask.
It does not identify the distinct single-load mixed representatives.

## 1. Shallow geometry, exterior order and full moment transport

The low/critical overlap argument uses the actual D-root origin
interior and the actual S-root closed origin containment. At high
radius the genuine small B point forces a shallow top side of the
original D root, with 0<h<=epsilon and b=1-h>59/60. All original
transverse endpoint restrictions are kept.

The support bound at AB gives |n_x|<1/20 and n_y>0. I rechecked the
force-free D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md statement: it
applies to D with arbitrary other contacts and no circle-resultant
concurrence hypothesis. Its m_y<=0 conclusion and the full A3 vertical
equation give m_y<0.

I reread Sections 2--3 of
D_LEAF_BOUNDARY_ROOTS_CYCLE_EDGE_EXCLUSION.md. The current source
uses their occupied exterior-access argument, not that theorem's
degree-two internal-vertex equation. The real A--L strand cuts the
cycle at the unshareable D-leaf port. The upward B port precedes the
downward D port in the actual counterclockwise A boundary order.
The disjoint exterior access strands at C,D and the real leaf preserve
this order on the containing circle. The minor C--D circle arc cannot
contain L. Thus the boundary moment lemma supplies the asserted
positive sign on the directed C--D edge, including the compatible
small-junction limits.

The current proof then explicitly uses the true B3 torque: its
additional genuine radial S-leaf force has zero origin moment.
Together with the actual A3/C2/D2 torques, this transports one common
nonzero weighted cycle moment. Therefore the original AB moment is
positive and the original AD moment is negative. No equation at B
has been replaced by a transmitter equation, and no mean has moved.

## 2. The actual positive intercept and its two strict bounds

The northwest AB intercept is negative from the original D margins,
contradicting the transported sign. North and northeast retain the
actual side mean or vertex, respectively, and give 0<kappa<=r.
The unchanged horizontal A3 equation makes AD strictly southwest.
Combining its full vertical and torque equations gives exactly

    c_D/t_D=(kappa+s)/b,
    g_D=(s(kappa+s)+b^2)/sqrt((kappa+s)^2+b^2).

The inequality g_D<=d is the sharp physical contained-unit support
bound and does not constrain or replace D's true pair equations.
I differentiated G directly: its s and b derivatives have positive
numerators as displayed, and its k derivative has numerator -k*b^2.
I also recomputed the two squared rational reserves exactly:

    6101297/12649824000,
    970619263/527076000000.

They prove kappa>1/4 and, for kappa<29/100, h>1/110. The supporting
radius comparison has reserve (187/90)^2-1105/256=391/518400, while
2-(140/99)^2=2/9801. Thus the lower bound s>37/110 is strict.

## 3. Complete strict northeast and north-aligned B cases

The small-upper-support lemma covers both actual owners: an aligned
maximum side, with every original mean and endpoint, and a strict
maximum vertex with the full inward diagonal range. Its opposite
corner estimate uses Sigma>=1 and z^2<=2z for 0<=z<=1/60, giving
the strict uniform bound 106/25<17/4. Adjacent and near-side corners
are also bounded, rather than inferred from a chosen far corner.

For northeast AB, I checked the pre-extraction determinant argument
against RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md, Section 3,
and the already reviewed local extension in the single-load source.
The actual applications (r,h),(-s,-b) are fixed distinct vertices,
both have nonzero transverse coordinates, and the other normal is
not parallel to the leaf. Hence the determinant is nontrivial on
each allowed free-normal interval, including two independent
distinct-junction parameters. The finite physical prelist is made
before extraction and survives uncrossing/thinning. This requires no
degree or load assumption at B or D. The strict point convention
retains all genuine side cases and removes the vertex/vertex owned
endpoint. Therefore AB is an actual relative B-side interior.

The D-leaf screen along P-lambda*k crosses the original inner upper
leaf edge at lambda=h/(u+v), at positive height below sigma. It yields
rho<=h/(u+v)<1/60 with the weak contact limit retained. I checked all
four B vertex norms and all four owned-axis supports. The only possible
genuine S direction is n, with g=epsilon. The full B3 equation then
makes BC point -n: its opposite would duplicate the real S leaf by
sharp support equality. B's unchanged torque puts the C mean in the
opposite, positive tangent interval, strictly below 3/5. The physical
small-support cap applies to C, without requiring a new owner choice.

For a north AB side contact on aligned B, the actual D-leaf exclusion
gives x+1<=r+h. Together with the genuine near point and kappa>1/4,
this produces -3/4<x<-3/10 and 1/4<x+1<7/10. The complete vertex/axis
cover forces the real B leaf north and h=epsilon. The unchanged B3
torque then gives -3/4<x_C<0 on C's actual upper support, again within
the uniform physical cap. The endpoint means are not made strict.

## 4. North AB at a tilted B vertex

For B=P+[0,1]u+[0,1]v with u=(-c,t),v=(t,c), the actual near point
gives t/c<1/14 and c>99/100. I checked the inequalities excluding all
four genuine-leaf application vertices; the upper-vertex squared
norm reserve over (61/60)^2 is 809/90000. The two u-axis supports and
the -v support exclude the other owned axes. Thus the real leaf is v
and kappa*t+h*c=epsilon, with its original application P+tau*u+v.

The full force toward C is mu*t*u+(mu*c-alpha)*v. Moment about the
actual BA point P excludes both nonnegative v components, including
the full mean interval for the zero component. The remaining port is
exactly Q=P+u, and the genuine B3 moment gives alpha/mu=c/(1-tau).
Consequently its actual southwest normal satisfies exactly

    a/b_C=c*t/(tau-t^2).

This identity retains the real leaf force and uses no equation or
circle-force restriction at C beyond the original ones.

## 5. Every remaining actual C frame and exact arithmetic

I verified both intercept splits. For kappa>=29/100 the denominator
bound is 25339/90000, yielding a/b_C<21/100 and a+b_C<6/5.
For kappa<29/100, the actual support consequence h>1/110 yields
t<23/750. The denominator is greater than 553609/2250000, exceeding
8*(23/750) by 1609/2250000. Thus a/b_C<1/8 and a+b_C<28/25.

The final all-frame estimate is valid without concurrence. With
Q=(-X,Y), X>Y>0 and a<b_C, one has Q.k_C>|Q.n_C|. At a vertex this
makes the diagonal scalar product strictly increase throughout the
full allowed angle interval [-pi/4,pi/4], so its maximum is the
endpoint n_C+k_C. At a relative side interior, convexity on the
unchanged tangent interval [-1,1] and Q.k_C>0 give the same maximum.
Every adjacent/near corner is bounded separately by |Q|+1<19/10.
Thus all actual corner and shared-mean endpoints are covered.

The two exact final squared-norm bounds are

    168549/40000 < 17/4, with reserve 1451/40000;
    849/200 < 17/4, with reserve 1/200.

They are strict throughout the original high domain, including the
kappa=29/100 split endpoint in its first branch. Hence C cannot be a
physical boundary unit. This completes every remaining B frame.

## 6. Accepted scope

The theorem closes the entire original double-load mixed family,
both mixed assignments under its exact reflection symmetry. It uses
the true root equations A3/B3, true C2/D2 moments, all original circle
masks and zero individual weights, and all nine actual squares.
The high S/S family remains separate. The review used hand algebra
and exact rational arithmetic to confirm displayed reserves; no
numerical pose, normal reselection, changed force, Lean compilation,
CI run, remote mutation or shared-metadata edit was used.
