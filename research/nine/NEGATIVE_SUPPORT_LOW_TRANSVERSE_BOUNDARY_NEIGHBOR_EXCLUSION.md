# A boundary unit cannot cross a near-origin negative support at low transverse height

Date: October 28, 2026 UTC. Author: return_scalar_assembly continuation.

**Status: complete new force-free hand theorem and exact original
strict-Northwest/South/West interface consequences, frozen for full root
and separate independent review.** The geometric theorem has no force,
degree, radial-leaf, upper-radius or selected-graph premise. Its two actual
points may be any physical contact points or full original side means.
Every support endpoint and every unit orientation is included.

The original fan application preserves both true degree-four bodies and
the loaded degree-three page. It closes the entire stated low-radius
strict-Northwest/South/West feature, whichever page has degree two. It
does not close the strict-Southwest common-hub feature or the whole
original fan. The separate house consequence uses an actual edge to its
lower short page; no missing long-branch edge is supplied.

## 1. A complete closed-domain physical statement

Use an orthonormal coordinate system about the unchanged circle origin.
Let V be any actual closed unit square. Suppose

    -1/15 <= epsilon <= 0,
    0 <= h <= 21/50,
    min_(z in V) z_y = h.                              (1)

Suppose its minimum-height support contains an actual point P=(x,h)
with x>=epsilon, and V contains an actual point M with M_x<=epsilon.
The two points may coincide. They need not be vertices, selected force
applications or relative-interior side points.

**Physical theorem.** Every point of V lies strictly inside the
origin-centered disk of radius two.

In particular V cannot physically touch any containing circle of radius
R>=2. No individual circle coefficient is used by this conclusion.
The theorem includes both closed endpoints of each interval in (1).
There is no additional upper bound on x in its statement.

For reference, write

    B=21/50,       E=1/15.

The proof below places every one of the actual four corners strictly
inside that radius. Convexity of the open disk then gives the whole
closed square, including every point of its support sides.

## 2. Every aligned frame and every original side point

If V is parallel to the displayed axes, write

    V=[z,z+1] times [h,h+1].

The actual minimum-height point P has x>=epsilon and belongs to V, so
z+1>=epsilon. The actual point M has M_x<=epsilon, so z<=epsilon.
Consequently

    epsilon-1 <= z <= epsilon,
    -16/15 <= z <= z+1 <= 1.

Every actual corner therefore satisfies

    |x_corner| <= 16/15,
    0 <= y_corner <= 71/50,
    |corner|^2 <= (16/15)^2+(71/50)^2
                 =70969/22500 < 4.                    (2)

The exact reserve is 19031/22500. This argument includes a shared
minimum side, either endpoint of that side, and coincident P,M. No
point is moved to a more convenient corner.

## 3. The entire tilted frame and the exact horizontal interval

Otherwise V has a unique minimum-height vertex, necessarily P itself.
Its actual full frame has the form

    V=P+[0,1]u+[0,1]v,
    P=(x,h),
    u=(p,q),       v=(-q,p),
    p,q>0,        p^2+q^2=1.                           (3)

The actual point M has some coefficients lambda,mu in [0,1], so

    M_x=x+lambda*p-mu*q <= epsilon.

Thus the complete original horizontal interval is

    epsilon <= x <= epsilon+q.                        (4)

In particular every support mean which supplied M remains untouched.
The argument uses neither its height nor any assertion that it is a
vertex. Both endpoints of (4) remain in every following comparison.

We will use two exact whole-frame inequalities:

    p+q <= sqrt(2) < 17/12,
    p^2+2pq < 13/8,       q^2+2pq < 13/8.             (5)

The radical comparison has squared reserve 1/144. The latter two
strict inequalities can be checked without a trigonometric maximum:

    13/8-(p^2+2pq)=((13q-8p)^2+p^2)/104 > 0,
    13/8-(q^2+2pq)=((13p-8q)^2+q^2)/104 > 0.

These use p^2+q^2=1 and hold over the entire closed nonnegative
quarter-circle as well. The actual aligned orientations were already
handled directly in Section 2.

## 4. Three actual corners have immediate strict bounds

At P, (4) gives -1/15<=x<=q<=1. Therefore

    |P|^2 <= 1+B^2 = 2941/2500 < 4.                    (6)

The left adjacent corner is P+v=(x-q,h+p). Its horizontal coordinate
lies in [epsilon-q,epsilon], contained in [-16/15,0]. Its height is
at most 71/50. Thus the entire corner satisfies the same strict bound
(2), with no sign change or omitted x endpoint.

The right adjacent corner is P+u=(x+p,h+q). By (4),

    epsilon+p <= x+p <= epsilon+p+q.

The lower endpoint is at least -1/15, the upper endpoint is at most
p+q, and p+q>=1. Hence |x+p|<=p+q, whether its original sign is
positive, zero or negative. It follows from (5) that

    |P+u|^2 <= (p+q)^2+(h+q)^2
             = 1+h^2+q^2+2pq+2hq
             < 1+B^2+13/8+2B
             = 18207/5000 < 4.                       (7)

The exact final reserve in (7) is 1793/5000. In particular no
assumption that the original right-corner coordinate is positive is
needed to square this bound.

## 5. Both actual horizontal endpoints control the last corner

The opposite corner is

    Z=P+u+v=(x+p-q,h+p+q).

For fixed h,p,q, its squared norm is a convex quadratic in the
unchanged x. Its maximum over the complete interval (4) is therefore
at one of its two endpoints. These are comparison endpoints only;
the actual point or unit is not repositioned.

### 5.1. The endpoint x=epsilon

Using (5), |epsilon|<=E and |p-q|<=1 gives

    |Z|^2
      =(epsilon+p-q)^2+(h+p+q)^2
      =2+h^2+epsilon^2+2h(p+q)+2epsilon(p-q)
      <=2+B^2+E^2+(17/6)B+2E
       =19711/5625 < 4.                              (8)

The exact reserve is 2789/5625. The estimate permits either sign of
p-q and retains epsilon=0 and epsilon=-1/15.

### 5.2. The endpoint x=epsilon+q

Here the horizontal corner coordinate is epsilon+p. Because epsilon
is nonpositive and p is nonnegative,

    (epsilon+p)^2 <= epsilon^2+p^2.

This inequality expressly includes the possible negative value of
epsilon+p; replacing its absolute value by p alone would not cover
that endpoint. Consequently

    |Z|^2
      <=E^2+p^2+(h+p+q)^2
       =E^2+1+h^2+p^2+2pq+2h(p+q)
       <E^2+1+B^2+13/8+(17/6)B
        =179813/45000 < 4.                            (9)

The exact remaining reserve is 187/45000. It is positive on the
entire enlarged closed rectangle (1), including its simultaneous
epsilon=-1/15 and h=21/50 endpoint.

Equations (8)--(9) and the convex x comparison bound the actual
opposite corner for every (3)--(4). Together with Sections 2 and 4,
all four physical corners have now been proved strictly inside radius
two. This completes the whole physical theorem.

## 6. A degree-free lower-neighbor consequence

Let X,W,K be distinct actual unit squares in a circle of radius R>=2.
Suppose in the same origin-centered frame

    X=[epsilon,epsilon+1] times [-b,a],
    -1/15<=epsilon<=0,
    a+b=1,       0<=b<=21/50,
    W subset {y<=-b},       X intersect W nonempty,
    K subset {x<=epsilon},  K intersect W nonempty.      (10)

No contact X--K, positive edge, force or degree is required by this
consequence. The actual X--W contact belongs to y=-b and has horizontal
coordinate at least epsilon. The actual K--W contact has horizontal
coordinate at most epsilon. Reflecting the whole frame vertically
puts W under the hypotheses of Section 1 with h=b. Hence W is wholly
inside the original radius-two disk and cannot be a physical boundary
unit at R>=2.

This excludes the complete physical arrangement (10) whenever W is
physically circle-touching. It retains all actual contact points and
all their possible aggregate means. The same conclusion holds after
reflecting the entire arrangement, with the corresponding upper/lower
roles interchanged.

## 7. Entire original low strict-Northwest/South/West fan feature

Keep the unchanged nine physical units and compatible selected
certificate in the original strict-low aligned S-root interval

    2<R<sqrt(17)/2,
    d=sqrt(R^2-1/4)-1,
    epsilon=d-1,       -1/15<epsilon<0,
    X=[epsilon,d] times [-b,a],
    a+b=1,            0<=a,b<=1,
    L=[d,d+1] times [-1/2,1/2].                        (11)

Suppose the two actual physical boundary page normals at X are strict
Northwest toward U and South toward W, and its actual normal to K is
West. Suppose also that the original W--K edge is present. The normal
names refer to the unchanged original normals; no new side owner is
chosen. There is no positive-degree premise at U,W or K.

The strict Northwest page has its actual X contact at

    P_U=(epsilon,a).

Since U physically touches the original circle, every point of U has
norm at least R-sqrt(2), by its actual diameter. Therefore

    epsilon^2+a^2 >= (R-sqrt(2))^2
                    >(2-sqrt(2))^2 >12/35.

The last strict comparison follows from sqrt(2)<99/70. Because
epsilon^2<1/225 and a>=0, this gives

    a>29/50,       0<=b<21/50,                        (12)

using the exact reserve

    12/35-1/225-(29/50)^2=317/157500>0.

The actual South normal supplies W subset {y<=-b} and its real
X--W contact. The actual West normal supplies K subset {x<=epsilon}.
The original positive W--K edge supplies their actual common point.
Every premise of (10) is now literal, and its conclusion contradicts
the physical boundary status of W.

Thus the entire strict-Northwest/South/West feature in (11) is
impossible. The argument does not use any root force equation at all;
in particular it does not replace the true X4 equation by X3 or make
an X3 singleton-normal selection. All four original root forces and
all other actual forces remain in their original certificate.

For the exact fan-inner 134.S family, the unchanged positive edges are

    J1, J2, J3, J4, 12, 23, 34, 2L,

and its original positively loaded block bodies are 1,3,4. Put

    X=2,       K=J,       {U,W}={1,3}.

Both possible page assignments have the actual required W--K edge.
Their true degrees remain 2(4), J4, 1(2), 3(3), 4(2), L1. In
particular W is not assumed to have degree two: the same theorem
excludes its degree-three assignment. All J4 and 34 forces and all
three arbitrary completion units remain.

The reflected strict-Southwest/North/West feature is excluded by one
reflection of the entire original physical chart. This is a proved
feature consequence, not an added symmetry quotient of the graph.

## 8. A literal house short-page consequence and the remaining boundary

For the original house-hub TCB.S family, keep the edges

    AT, DT, AD, AB, BC, CD, AL,

and positive block loads T,C,B. Put X=A and K=D. If its actual
long-branch first page B is strict Northwest at X, its actual short
page T is South, and the actual AD normal is West, then use

    U=B,       W=T.

The required W--K edge is the unchanged original TD. Thus Section 7
excludes this whole low aligned feature as well, preserving actual
A4, D3 and T2/B2/C2. Its reflected feature is included.

The reversed short/long assignment U=T,W=B has no original BD edge.
It is outside this caller unless an independent argument establishes
the required physical B--D contact. Nothing here supplies that missing
contact or contracts the actual B--C--D path.

For the fan, the already published complete tilted and high aligned
sources, and the separately published low North/West/South theorem,
have their own full scopes and reviews. They are not mathematical
premises of the new physical bound. This manuscript does not assert a
complete low normal cover or exclude the remaining strict-Southwest
K interface. It assigns no whole original S-family or parent credit.

## 9. Exact inputs, discovery disclosure and review boundary

The main physical theorem and Section 6 are proved entirely above.
They need only the defining orthonormal geometry of an actual unit
square. Their proof does not invoke any upstream stress or embedding
theorem.

The original applications use these complete sources at their stated
literal scopes:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | The unchanged genuine aligned S-leaf and root chart in (11), only. |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | The original R>2 conclusion on all nine retained physical units, only. |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | The exact original fan-inner134 and house-hubTCB graphs, positive loads, true degrees and actual missing-edge distinction. |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Only the original physical support convention and membership of actual aggregate means in both contacting squares. No force equation is imported. |

The author developed the new two-contact physical estimate while
investigating the aligned S-root remainder. Root suggested exporting
the full continuous physical statement and preserving both page-degree
assignments; root did not supply the corner inequalities. The already
published negative-support loaded-tip theorem at commit c58867a2956c
was read before this source was assembled. It uses a true loaded V2
equation and treats the low North/West/South interface. The present
theorem uses no force equation and has the different low-transverse
two-point hypothesis (1); neither proof is counted as a review of the
other. The new argument was not supplied by its future independent
reviewer.

The original exploratory work also considered a larger transverse
reach bound. It is not an input to this manuscript. Every bound
needed here is printed in Sections 1--5 and has been rederived
directly. The displayed rational identities and reserves were checked
with exact fraction arithmetic. No sampled orientation, pose search
or numerical geometric certificate is a premise of the proof.

Full independent and root review of these exact complete bytes remains
necessary before adoption at their explicit feature scopes. No old
gate, metadata, Lean file, build, CI, workflow, commit or remote state
is modified by this source.
