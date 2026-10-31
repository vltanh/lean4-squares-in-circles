# Full two-terminal force direction excludes every multi-body three-cut terminal path

Date: October 31, 2026 UTC.

Author: loaded_joint. The new directional support theorem, unit-reach
lemma, and their complete original module join are this author's new
construction. Root requested this structural direction and a separate
complete freeze, but supplied no new mathematical step to this source.
The earlier accepted terminal-cluster theorem is disclosed below.

**Status: complete proposed hand theorem, frozen for a separate full
clean noncontributor review. No conclusion is adopted by this source's
freeze alone. The earlier cfee59ed source is unchanged.**

## 1. Original physical scope and complete operative boundary

Keep one unchanged finite packing of actual closed unit squares with
pairwise disjoint open interiors and its full original positive contact
certificate. For every positive original body pair retain its magnitude,
actual unit separating normal, actual application or full shared-side
mean, and both original force and origin-moment contributions. Every
physical contact and physical circle point remains, including those with
individual zero selected coefficients. An unloaded unit has total
selected circle coefficient zero; this does not say that the unit has
no physical circle point. All coefficients at circle points are
nonnegative, so an unloaded unit has no circle term in its translation.

All statements below concern full cuts in this unchanged positive graph.
Every positive pair leaving the indicated set is counted. Different pairs
to one outside body remain distinct summands. A physically shared side
remains one original pair with its complete original mean; its forces
are not replaced by fictitious endpoint forces. No positive pair is
omitted because its direction or application is inconvenient.

The results require only the complete translations and actual support
equations. The full moments remain satisfied and unchanged. There is
no containment radius premise, boundary-order premise, degree bound on
an outside terminal, normal-selector hypothesis, or physical motion.
Internal branches, chords, and cycles are permitted. In the original
nine-square problem all nine actual units and the same C* are retained.

The two complete accepted direct input bodies are:

| Complete source or gate | Bytes | LF | SHA-256 |
| --- | ---: | ---: | --- |
| `GLOBAL_UNLOADED_MODULE_TERMINAL_CONTACT_CLUSTER_FORCE_COMPENSATION_AND_COMPLETE_THREE_PORT_PATH_REDUCTION_2026_10_31.md` | 20527 | 446 | `cfee59edb03268bfc852c33c5d47e5ec701743630add3cb808fa797cc8032c94` |
| `REVIEW_GLOBAL_UNLOADED_TERMINAL_CLUSTER_FORCE_COMPENSATION_AND_COMPLETE_THREE_PORT_PATH_FULL_NONCONTRIBUTOR_2026_10_31.md` | 19039 | 419 | `aeaed004705bc48fb56de4c3c6d010d36d6f17841f6d919f4f254f27859ce4c6` |

The source and its complete independent gate have been read in full at
these pins. Their accepted full-cut work identity, one-terminal
obstruction, and complete three-cut host classification are the only
imported results. For a self-contained audit, every operative hand
calculation used here is reprinted in Sections 2 and 5. The earlier
source's remaining paired-end-terminal pattern was explicitly open;
Sections 3, 4, and 6 below supply its new exclusion.

No later theorem about packing capacity, arbitrary separators, circle
arcs, finite central rooms, or a moving PR head is an operative input.
No earlier tree cardinality bound or generic three-free-normal rule is
used. In particular a cyclic module is not treated as a tree.

## 2. Complete translations and support work

Let K be a nonempty entirely unloaded set. If i--j is a positive original
pair, orient n_ij from i toward j, and denote its positive magnitude by
mu_ij. For an actual unit S with center c_S and orthonormal own axes
u_S,v_S, extend its support halfwidth to every vector v by

    h_S(v)=(|v.u_S|+|v.v_S|)/2.

This function is even, positively homogeneous, and subadditive. For a
unit vector n it satisfies h_S(n)>=1/2. Actual contact and the full
unloaded translations give

    n_ij.(c_j-c_i)=h_i(n_ij)+h_j(n_ij),
    sum_(all original positive neighbors j) mu_ij n_ij=0
        for each i in K.                                      (2.1)

For the full cut orient each normal outward from K. Count every
internal undirected edge exactly once and put

    C_K=sum_cut mu,
    H_K=sum_cut mu h_internal(n),
    M_K=sum_internal mu,
    I_K=sum_internal mu [h_i(n)+h_j(n)].                       (2.2)

Thus H_K>=C_K/2 and I_K>=M_K>=0. If K is connected and has at least
two units, its positive induced graph has an internal edge and I_K>0.

Dot each full equation (2.1) with c_i-o and sum over i in K. The two
terms of each internal pair combine to its negative support work:

    0=-I_K+sum_cut mu n.(c_internal-o).                       (2.3)

For completeness, suppose a disk of radius delta centered at o meets
every distinct external terminal. Choose z_t in the actual terminal t
and in this disk. At any original cut application p, including a full
side mean, the internal unit maximizes n and the terminal minimizes n.
Consequently

    n.(c_internal-o)
      =n.(p-o)-h_internal(n)
      <=n.(z_t-o)-h_internal(n)
      <=delta-h_internal(n).

Equation (2.3) therefore gives the complete terminal-ball inequality

    I_K+H_K<=delta C_K.                                      (2.4)

If the full cut is nonempty and all its outside terminals have one
common actual point, take delta=0. Since C_K>0 and H_K>=C_K/2, (2.4)
is impossible. In particular an entirely unloaded positive component
cannot have a nonempty full cut only to one actual outside unit: choose
any point of that unit for the radius-zero hitting disk. This argument
uses the whole outside unit, not a common point of its cut applications.

These calculations do not require K to be connected. Connectivity is
used later only where a nonempty component cut or I_K>0 is asserted.

## 3. The full net force selects a whole terminal support gap

### 3.1 Statement and nonzero net force

Let L be a nonempty entirely unloaded set with nonempty full positive
cut whose set of distinct outside terminals is exactly {U,B}. The two
terminals are distinct actual units outside L. Either terminal may
have arbitrarily many cut pairs to L, arbitrary other positive pairs,
arbitrary total load, and any physical contact or circle mask.

Write F_U and F_B for the complete vector sums of cut forces oriented
from L toward the named terminals. Summing all original translations
over L gives

    F_U+F_B=0.                                               (3.1)

Use (2.3) with o=0, and then use the exact contact identity on every cut
pair to replace its internal center projection by the terminal center
projection. This yields

    c_U.F_U+c_B.F_B
      =I_L+sum_cut mu [h_internal(n)+h_terminal(n)].           (3.2)

By (3.1), its left side is F_B.(c_B-c_U). The right side is strictly
positive: the cut is nonempty, every cut magnitude is positive, and
both actual unit halfwidths are at least 1/2. Hence

    F_B!=0,       lambda=|F_B|>0,       e=F_B/lambda.          (3.3)

Thus a direction e is defined by the complete actual net force, without
choosing a distinguished individual cut normal or a path through L.

### 3.2 Convex support and the exact quantitative reserve

Let C_U,C_B be the sums of magnitudes at the two groups of cut edges.
The triangle inequality and (3.1) give

    C_U>=lambda,       C_B>=lambda,
    C_L=C_U+C_B>=2lambda.                                   (3.4)

Homogeneous subadditivity of each actual terminal halfwidth gives

    sum_(cut to U) mu h_U(n)>=h_U(F_U)=lambda h_U(e),
    sum_(cut to B) mu h_B(n)>=h_B(F_B)=lambda h_B(e).          (3.5)

Define the following four actual nonnegative reserves:

    E_width=H_L-C_L/2,
    E_force=C_L/2-lambda,
    E_U=sum_(cut to U) mu h_U(n)-lambda h_U(e),
    E_B=sum_(cut to B) mu h_B(n)-lambda h_B(e).               (3.6)

Substituting these definitions into (3.2) gives the exact identity

    min_(x in B) e.x - max_(x in U) e.x
      = e.(c_B-c_U)-h_B(e)-h_U(e)
      = 1+[I_L+E_width+E_force+E_U+E_B]/lambda.              (3.7)

In particular the full two-terminal force-direction theorem is

    min_B e - max_U e >= 1+I_L/lambda >= 1.                 (3.8)

If L is connected and has at least two units, the first gap is strictly
larger than 1 because I_L>0. Each reserve in (3.7) is printed rather
than discarded: cancellation within either terminal force group makes
E_force positive unless both total magnitudes are exactly lambda;
actual cut widths and the two fixed terminal frames contribute the
other reserves. No uniform lower bound on an individual force is used.

### 3.3 Scope of the directional conclusion

The theorem applies to arbitrary cut multiplicities at both actual
terminals and to internal cycles, branches, and chords. It says that
the whole actual terminal squares have the gap (3.8) in the actual net
force direction. It does not say that individual cut normals agree,
that all original applications are collinear, that L is a single
transmitter, or that its internal graph is a channel. Neither terminal
is duplicated when its cut has more than one edge.

## 4. A unit touching both sides of that gap has a weak forward normal

### 4.1 Complete point-to-unit reach lemma

Let X be an actual unit square, p an actual point of its minimum-n
support feature, and n,e unit vectors. An original full contact mean
is allowed for p. We claim

    n.e<0  ==>  max_(x in X) e.(x-p)<1.                     (4.1)

First suppose p is an actual vertex. Choose the two orthonormal inward
edge directions a,b, so

    X=p+[0,1]a+[0,1]b,
    n=Aa+Bb,       A,B>=0,
    e=xa+yb,       x^2+y^2=1.

The closed coefficients A=0 or B=0 are included. The inequality
Ax+By<0 prevents both x and y from being nonnegative. The exact
forward reach from p is x_++y_+, where r_+=max(r,0). With at most
one positive coordinate, this is at most 1. Equality would require
the positive coordinate to be 1 and the other to be 0, which makes
Ax+By nonnegative. Equality is therefore impossible and (4.1) follows.

Otherwise p is in the relative interior of an actual side. Its inward
own normal is n. For a tangential own unit direction j and the unchanged
actual mean coordinate t in (0,1),

    X-p=[0,1]n+[-t,1-t]j.

The negative coefficient e.n makes the maximum contribution from the
first segment zero. The second contributes at most |e.j|<1 because
e is a unit vector and e.n<0. This proves (4.1). Side endpoints were
already included in the vertex case; no open-mean premise is imposed.

This exhausts every support feature of a unit square, every closed
normal-cone endpoint, and every original shared mean. There is no
strict vertex/vertex selection assumption in this lemma.

### 4.2 Actual common-neighbor consequence

Suppose two actual units U,B obey

    min_B e-max_U e>=1.                                     (4.2)

Let a third actual unit X physically touch both. Retain an actual
U-to-X separating unit normal n and its original application or mean
p in U intersect X. Thus p minimizes n on X. Choose any actual
q in X intersect B. The second contact may have zero selected weight,
may be shared, and need not have any selected normal in this argument.
Since p belongs to U and q belongs to B,

    e.(q-p)>=min_B e-max_U e>=1.

Equation (4.1) excludes n.e<0. Therefore

    n.e>=0.                                                 (4.3)

The conclusion is deliberately weak: n.e=0 is retained. It is
sufficient for the positive-force contradiction below. No width is
charged to a branching vertex and no finite side is replaced by an
infinite separating line for the other contacts of X.

## 5. Reprinted complete three-cut host reduction

Let K be connected in the full original positive graph, entirely
unloaded, with exactly three positive cut edges to three distinct
terminal units A,B,C. Assume the actual physical contacts A--B and
B--C. These path contacts may have zero selected weight. A and C
may also touch. Every cut owner and full application mean is retained.

The center of the actual unit B supplies a hitting disk of radius
sigma=1/sqrt(2) for A,B,C: choose the physical A--B and B--C points
for A,C, and a point of B for B. Thus (2.4) holds with delta=sigma.
Classify the number of actual K bodies carrying the three cut edges.

### 5.1 Three distinct cut hosts

If each of the three cut hosts carries just one cut edge, its external
vector has magnitude equal to that edge's magnitude. The full internal
vector at that body is its negative. Summing the internal triangle
inequalities over every body in K gives

    C_K<=2M_K<=2I_K.

Together with H_K>=C_K/2 and (2.4), this would give

    sigma C_K>=I_K+H_K>=C_K,

which is impossible since C_K>0 and sigma<1. This is the accepted
terminal-anchor argument with every internal edge retained.

### 5.2 One cut host

If all three cut edges have one host U and K has at least two bodies,
each nonempty positive component of K-{U} has a nonempty full positive
cut only to U. Nonemptiness follows from connectedness of K; no
component has an original external edge because all three are at U.
The one-terminal consequence of (2.4) excludes each component.
Hence this host pattern forces K={U}.

### 5.3 Two hosts, with a physically touching paired terminal set

Let U carry two cut edges of magnitudes a,c and actual normals n_1,n_2,
and let V carry the singleton cut of magnitude lambda>0. Set S=a+c.
The full translation sum over K gives

    lambda=|a n_1+c n_2|,
    |F_U|=|F_V|=lambda.

The internal triangle inequalities give I_K>=M_K>=lambda. Hence

    sigma(S+lambda)>=I_K+H_K
                         >=lambda+(S+lambda)/2,
    lambda/S<=(2sqrt(2)-1)/7=:kappa.                         (5.1)

If the two paired terminal units touch, they both touch the actual U
and one another. Here is the full geometric lower bound. Let p_1,p_2
be their actual U applications, and choose an actual common point z
of the two paired units. If n_1.n_2>=0, their weighted resultant ratio
is at least 1/sqrt(2). Otherwise, in an actual own frame of U, some
normal-coordinate product is negative. The actual support points
p_1,p_2 lie on opposite U faces in that coordinate. With m=(p_1+p_2)/2,

    |p_1-p_2|>=1,       |m-c_U|<=1/2.

Both |z-p_1| and |z-p_2| are at most sqrt(2), since each pair lies
in one actual unit. The parallelogram identity gives

    |z-m|^2<=7/4,       |z-c_U|<=(1+sqrt(7))/2.

The actual supporting halfplanes give

    (n_1+n_2).(z-c_U)>=h_U(n_1)+h_U(n_2)>=1.

Thus |n_1+n_2|>=2/(1+sqrt(7)). For all a,c>0 the exact identity

    |a n_1+c n_2|^2/(a+c)^2
      =1-2ac(1-n_1.n_2)/(a+c)^2
      >=(1+n_1.n_2)/2
      =|n_1+n_2|^2/4

proves, also in the nonnegative-dot case,

    lambda/S>=1/(1+sqrt(7)).                                (5.2)

The bounds (5.1)--(5.2) conflict because

    1/(1+sqrt(7))-kappa
      =[7sqrt(7)-12sqrt(2)-1]/42>0.

Indeed sqrt(7)>21/8 and sqrt(2)<10/7, by the positive squared reserves
7/64 and 2/49, and the bracket is greater than
147/8-120/7-1=13/56>0. All compared radicals and denominators are
positive. Shared means and closed normal directions were retained
throughout this argument.

Consequently, if |K|>=2, the complete host cover leaves only the
following pattern: U has the A,C exits and another host V has the B
exit. Pairing A,B or B,C is excluded by their actual path contact.
If A,C also touch, that paired case is excluded as well. The new proof
below treats the remaining A,C pattern without assuming they touch.

## 6. Entire remaining multi-body pattern: a force-sign contradiction

Keep the remaining two hosts U,V. The A,C exits at U have magnitudes
a,c>0 and actual normals n_A,n_C. The unique B exit at V has magnitude
lambda>0 and actual normal n_B directed toward B.

Remove U from the positive induced graph of K. Any nonempty component
not containing V has no original external cut edge: the original full
cut consisted precisely of the two exits at U and the one B exit at V.
Its full positive cut can therefore go only to U. It is nonempty by
connectedness of K. Section 2 excludes every such unloaded component.

It follows that L=K-{U} is one connected nonempty component containing
V. There is a positive edge from L to U, again by connectedness of K,
and its original B edge remains. Its complete outside terminal set is
exactly {U,B}. All original pairs from L to U remain, with arbitrary
multiplicity, means, and normal directions. The full B group consists
of the single original vector lambda n_B. Therefore the net direction
e of Section 3 is precisely

    e=n_B,
    min_B e-max_U e>=1+I_L/lambda>=1.                       (6.1)

Both actual A and actual C physically touch both U and B. Their U
contacts are the two unchanged original cut applications, and their
B contacts are exactly the two physical terminal-path contacts.
Apply Section 4 separately to these two actual units. It gives

    n_A.e>=0,       n_C.e>=0.                               (6.2)

Finally sum every original translation over the original K, not only
over L. Its full cut-force sum is

    a n_A+c n_C+lambda e=0.                                 (6.3)

Taking the e projection in (6.3) gives a sum whose first two terms
are nonnegative by (6.2) and whose last term is lambda>0. This is
impossible. The proof includes I_L=0, which occurs when L is a single
body; strict inequality in (6.1) is unnecessary. Every zero projection
in (6.2), every side-mean endpoint, and every physical zero-weight
terminal-path contact is included.

Combining Sections 5--6 proves the complete theorem:

**Three-cut physical-path theorem.** In one unchanged full physical
certificate, a connected entirely unloaded set with exactly three
positive cut edges to three distinct outside terminals A,B,C that
physically touch along A--B--C has at most one actual body.

Equivalently, every such actual connected module with at least two
bodies contains a positive selected circle load. This conclusion
does not turn a zero-weight physical circle point into a positive
load. It follows from the original full force equations themselves.

## 7. Literal original graph callers across body orders

In the original nine-unit setting, let H be any connected set of at
least two actual unloaded units. Suppose exactly three original
positive pairs leave H, to three distinct terminal units A,B,C, and
the actual A--B and B--C physical contacts are retained. Then the
entire feature is excluded by Section 6. There is no restriction on
the distribution of those three exits among the hosts in H. In
particular two exits may share a host, and H may contain any branches,
chords, or internal cycles compatible with the original graph.

One concrete caller takes A,B,C as consecutive vertices of a retained
outside positive cycle. Those two positive cycle edges certainly
give the required physical path. The rest of the outside cycle and
all its other original forces, chords, loads, and circle masks remain.
The exact full-cut check is essential: an additional positive edge
leaving H cannot be dropped, even if it has a small magnitude.

For a single-block graph-family caller, let H be two-connected with
h>=3, and let the outside cycle have k>=3 distinct vertices. Put the
three joins at three distinct outside terminals and at at least two
distinct vertices of H; repeated internal hosts are now allowed.
The union is two-connected. After deleting a vertex of H, H minus
that vertex remains connected, the outside cycle remains connected,
and at least one join survives because no one H host carries all
three joins. After deleting a cycle vertex, the remaining outside
path and H remain connected, and at least two joins survive because
the three terminals were distinct. This proves the claimed graph
property without assuming the unloaded module is a tree.

| Entire unloaded module feature H | Outside cycle size k | Selected body orders h+k |
| --- | --- | --- |
| Two connected units, all three-cut host patterns | 3,4,5,6,7 | 5,6,7,8,9 |
| Triangle, all three-cut host patterns | 3,4,5,6 | 6,7,8,9 |
| Four-cycle or diamond, including repeated join hosts | 3,4,5 | 7,8,9 |
| Any five-vertex connected module, including two-connected K2,3 | 3,4 | 8,9 |
| Any six-vertex connected module | 3 | 9 |

The single-block assertion applies to the two-connected modules just
specified with at least two distinct join hosts. The general theorem
and the table also cover connected modules without that graph property.
None of these examples asserts that an actual packing with the listed
feature exists. When h+k<9, all 9-h-k actual completion units remain;
their contacts are still included when checking the full cut.

The directional theorem itself is broader than these three-cut
callers. It is an exact full-force result for every entirely unloaded
two-terminal module, at any cut multiplicities and any internal graph.
No outside terminal's full star is replaced by the force it receives
from the chosen module.

## 8. Endpoints, controls, and exact limits

The one-body case of the three-cut path theorem is explicitly retained.
This source does not exclude an unloaded singleton with three such
neighbors. Any independent theorem excluding that configuration needs
its own complete original entry and acceptance. If the three terminals
also form a physical triangle, the earlier accepted cfee59ed theorem
has a separate stronger conclusion, but that is not needed for the
multi-body exclusion proved here.

The full-cut hypothesis is not optional. The balanced central unit in
the five-square cross has four original exits and is not excluded by
selecting three of them. A positive-loaded module is outside the
unloaded hypothesis. An unloaded but physically circle-touching module
remains inside it. Repeated outside terminals are allowed in Section 3,
whereas Section 6 requires three distinct terminals and both actual
path contacts. Those different scopes are not interchanged.

The source neither removes cycle-rank corrections from a separate tree
budget nor charges an arbitrary branch one unit of circle-boundary gap.
It proves no central enclosure, exterior capacity, all-nine allocation,
complete coarse-parent closure, published count change, unrestricted
radius theorem, or equality classification. The exact original feature
excluded is every multi-body unloaded three-edge cut with the stated
physical terminal path, including its complete repeated-host pattern.

All mathematical arguments are printed hand proofs. No mathematical
script, numerical pose, angle or force sample, mesh, optimizer, finite
packing certificate, Lean/Lake build, CI, or remote write was used.
Metadata hashing and exact full-file copying are solely for immutable
provenance. The entire source and both complete direct input bodies
require a separate full clean gate before this new extension is adopted.
