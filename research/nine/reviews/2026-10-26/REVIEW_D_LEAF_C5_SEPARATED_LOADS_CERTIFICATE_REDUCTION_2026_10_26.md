# Independent full-source review of the D-leaf C5 load13 exclusion

Date: October 26, 2026.

**Verdict: PASS for the entire original obligation
M6.B5L.C5.L13.D.** This is a complete physical six-body core exclusion,
not merely a cap or scalar reduction. I reviewed
`D_LEAF_C5_TWO_SEPARATED_LOADS_EXCLUSION.md` end to end, rederived its
concurrence and turn signs and every later ordered-mask contradiction,
and checked the direct local prerequisites in the proper-concurrence,
unique-corner turn, parallel-load and radial-channel sources. The
companion original S-leaf gate is not included.

## 1. True root, width reduction and support signs

The D-leaf normal form keeps A's actual degree three and its nonzero
horizontal leaf force. Its true root face application is side-interior,
so a,b>0 and a+b=1, while A=[−s,rho]×[−b,a] contains the origin in
its open interior. Thus the root support h in every channel direction
is strictly positive.

The whole far square C is beyond h+w_U, and its center has both the
corresponding lower projection h+w_U+1/2 and the universal upper norm
d+1/2. Since d<61/60<sqrt(2), the full width alternative forces
w_U=1, h≤d−1 and d>1. This is a consequence of the actual physical
channel, not a deletion of U or a replacement of A's degree.

I checked the resulting strict radius and horizontal root bounds.
In particular R²>17/4 gives rho>3/5, while rho<3/4 and
1/4<s<sqrt(2)−1<1/2 hold throughout the contrary domain. Fresh
rational reconstruction gives reserves 19/400, 41/400 and 55/2304
for the convenient square comparisons used here, and 31/57600 for
d<61/60. The support bound therefore gives |n_x|<1/15 and
|n_y|>14/15. Reflecting across the horizontal axis preserves the
D-leaf direction and fixes n_y>0 without changing the original roles.

The complete root balance makes m_y<0 and the two cycle directions
nonparallel. Torque about their actual intersection places it on the
horizontal leaf line. Independently of its initial radial sign, its
proper-port coefficients are exactly a/n_y and b/(−m_y), both positive.

## 2. The positive sign of the genuine root concurrence

The external resultant F_A=lambda e_x is the original leaf resultant,
not a circle force assigned to A. The actual B,C resultants are
nonzero, their sum with F_A is zero, and the original three loaded-body
radial directions are distinct. Hence the three directions are
noncollinear. All three external origin moments vanish.

When both loaded pairs are nonparallel, the degree-two proper radial
concurrence lemma applies to B,C without a boundary-neighbor premise.
The two actual transmitter reserves and all three pairs of proper
ports supply nonnegative channel coefficients. The two reserved
coefficients are positive. A zero direct AB coefficient would equate
q_A and q_B; since q_B is nonzero and lies on an independent radial
resultant, this is impossible even before q_A's sign is known.

Substitution in the exact closed channel equations gives the genuine
root radial factor

    tau_A=ell_AC*ell_BA/(ell_AC+ell_CB+ell_BA)>0.

The coefficient calculation needs no physical triangle contact and
no pre-existing nonzero-moment assumption once these actual proper
channel equations have been established.

The one-parallel-body alternative is also complete. There can be only
one such body because the root cycle directions are nonparallel. The
local parallel-load classification makes both of its actual outward
normals point opposite its circle resultant; it does not assign a
concurrence to that body. Its unchanged torque gives opposite nonzero
transverse signs for the two original applications. Nonzero signs
follow from the other genuine loaded concurrence, whose resultant is
independent of the parallel direction. The remaining proper connection
has positive coefficient because the two transverse coordinates differ.
Its full endpoint force equations then put F_A and q_A on the same
transverse side. Their already known collinearity proves q>0.
All original means at the parallel body are retained.

## 3. Actual root ports and the complete force-turn sum

For n_x<0 the actual upper vertex would give
q=−s+a|n_x|/n_y<−1/4+1/14<0. Hence n_x≥0, and the actual root
balance makes m=(-c,-t) with c,t>0. Its strict root support is the
bottom-left vertex, giving

    p_AB=(-s,-b), q=−s+bc/t, 0<q≤rho.

The vertical support bound gives a<1/56 and b>55/56. Consequently
|p_AB|>rho and |p_AB|²<5/4<d²+1/4, with the required strict signs.

The cycle's positive common origin moment is mu*q*n_y. At A, the
determinant of incoming (c,t) and outgoing n is lambda*n_y/nu>0,
while their scalar product is positive. Thus its actual turn is
strictly between zero and 90 degrees. At every nonparallel loaded body,
positive radial concurrence and the same moment give a strictly positive
turn below 180 degrees. A parallel loaded body has directed turn
180 degrees, since its outward normals have the same sign. These three
positive turns have a positive sum below 3pi and make one full circuit;
the sum is exactly 2pi. This step neither invents a concurrence at the
parallel body nor bounds a radial concurrence by its own square.

## 4. Unique B with a direct neighbor: the local gap is genuinely filled

The unique-corner turn calculation at C uses its two true transmitter
neighbors and the original strict-normal/diagonal convention, so the
local bound theta_C≤135 degrees applies without a global C6 premise.

For B the source separately proves the missing direct-neighbor port
condition. A parallel unique B would be radial D and have zero origin
moment, contradicting the positive common moment. If its applications
coincided in a side interior, their normals would be parallel. If they
coincided at a vertex, that vertex would be its genuine concurrence.
The only non-circle vertex on a positive radial ray of its unique
circle corner is the opposite radial-D vertex, of norm rho. The
original point p_AB has strictly greater norm. Thus B's actual ports
are distinct in every remaining case.

I checked the complete remaining local support cover against Section 1
of `SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md`. Its owner cases require
no force equation at the neighbor A. Outer-axis and two-axis alternatives
have turn at most 90 degrees. The only single-inner-axis alternatives
with larger turn use the other vertex of the same inner side, with
all original side means and endpoint limits included. The non-axis
ordered vertex list has the stated dot-product/determinant identities;
the relevant sum is X(1−X)+Y(1−Y)≥0. Thus theta_B≤135 degrees, and
if theta_B>90 degrees its two actual applications lie on one inner
side, at separation at most one.

The actual turn sum and theta_A<90 degrees now exclude the entire
ordered unique/unique mask.

## 5. Radial B and the ordered radial C alternatives

For a physical radial B, every boundary point outside its inner-face
relative interior has norm at least sqrt(d²+1/4). The strict norm
comparison for p_AB therefore fixes its actual normal toward A to
the inner radial axis. This proves e=m and d=sc+bt without imposing
an equality or positivity restriction on the individual corner weights.
If its other channel has reserve one, the complete local radial support
cover makes that port an inner vertex, hence the B port separation is
at most one. The far endpoint in this application is physical boundary,
exactly the premise that the local support cover requires.

When C is radial, its channel toward the circle-clear root A must be
handled differently; the source correctly keeps its inner-axis case.
Outer and tangent supports are excluded by their actual containment
and far-square width, without assuming A is boundary. For n_x>0, the
inner-axis case puts the actual root point below radius 3/5, while the
strict-inner-vertex case makes the actual far port norm too large.
I independently obtained the displayed 11/144 squared reserve, and
79/720 for the other convenient squared norm comparison. Hence n_x=0.

The actual ports are then (q,a) and (q,a+1). In C's radial frame,
the inner-axis alternative gives u=0,v=1,y_A=−q<0. For a strict inner
vertex, the normal −e_y and the positive first coordinate q force
u>0 and the minus inner vertex; its height gives v>1/d>60/61.
Thus the unified u≥0,v>60/61,y_A<0 statement has the correct original
branch and includes the inner-axis mean interval.

For reserve-one V, positive common moment selects C's plus inner vertex
and normal -alpha e+beta f, alpha,beta>0. Its height is at least that
of C's actual A port, and its normal has vertical component greater
than -1. The actual B port therefore lies above height a; its A port
has height a−1. Their separation is strictly greater than one. This
contradicts either radial B's inner-face bound, or unique B's bound:
in the latter case C's two directions are nonparallel, so the exact
turn sum forces theta_B>90 degrees.

For diagonal V, the compatible endpoint convention supplies the
actual common e,f axes at B and C and strict side-interior diagonal
applications. Only C's inner radial axis remains. B's actual support
toward A has positive e-component, so both its diagonal port and A port
have e-coordinate d−sqrt(2). This forces the exact projection difference
sqrt(2). But the unchanged actual point difference is (q+s,2), whose
e-projection is greater than 120/61>sqrt(2). The latter squared reserve
is 6958/3721. This covers both physical masks of B and every original
diagonal mean.

Thus every physical-radial C case is excluded.

## 6. Unique C / radial B: both final widths

The last ordered mask has C unique and B radial. From d=sc+bt>1,
b>s and s+b<sqrt(2), the source's exact decomposition proves t>c.
If n_x>0, the actual root-coordinate equations instead give c/t>1,
a contradiction. Thus the original A-to-C channel is vertical here too.

For reserve-one V, B's actual radial center is below height
−3/(2sqrt(2)), while the whole actual C is beyond y=a+1 and its
center is above 3/2. Their center gap is therefore greater than
3/2+3/(2sqrt(2))>1+sqrt(2), contrary to the exact application reserve
and the two unit circumradii. The strict comparison has difference
(1−1/sqrt(2))/2.

For diagonal V, C's axes are the actual e,f axes of B, and its maximum
e-coordinate is d−sqrt(2). Its A-directed normal has both own-axis
components strictly positive. Its actual A port therefore maximizes
both coordinates. Since f_y<0, this puts that port no higher than its
original diagonal port. The latter has height
(sqrt(2)−d)t−cy<sqrt(2)−1/2<1, contradicting its actual A-channel
height a+1>1. This does not freeze the original diagonal application.

## 7. Accepted original scope

The ordered masks unique/unique, unique/radial, radial/unique and
radial/radial are all exhausted. Both actual widths for V are exhausted,
U's width was forced from its full original alternatives, and parallel
loaded forces were retained until the geometric contradictions applied.
The original D-root slider, every physical circle mask and individual
zero-weight endpoint, original side means, true degrees, extra physical
contacts and all three completion squares remain present throughout.

The theorem therefore closes precisely M6.B5L.C5.L13.D as an entire
core exclusion. It does not close M6.B5L.C5.L13.S or a larger rooted C5
cell. No fake leaf or circle force at A, degree-two reduction of A,
secondary normal choice, computational sign packet, Lean compilation
or CI was used. This review does not edit or independently tick the
shared gate ledger.
