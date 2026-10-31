# A two-leaf root cannot feed an unloaded transmitter

**Status: complete hand nine-square completion theorem; root and separate independent full
hand audits passed.** Work with the common
selected certificate in

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1,   epsilon=max(d-1,0)<1/60.

Let A support two distinct genuine positive leaves L1,L2. Let U be
another positive neighbor of A, with zero total circle load and exact
positive degree two. Write V for U's other positive neighbor. A and V
may have arbitrary other positive neighbors and loads. All original
physical squares, shared means and zero-weight contacts are retained.

**Theorem.** Such a local pattern cannot occur in a nine-square packing
in the declared window. Away from the critical endpoint the pattern
itself is impossible. At the critical endpoint, the proof excludes its
completion to nine using an actual P or Y cage; it does not claim that
the corresponding isolated physical cage cannot exist.

## 1. The actual channel and the two-leaf central disk

A genuine leaf is loaded and radial S or D. The complete geometric
central-disk lemma in
TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Section1,
allows arbitrary other neighbors at A and says:

* If d<1, O belongs to the open interior of A.
* If d>1, the entire closed disk D_(d-1) belongs to the open interior
  of A.
* If d=1, either O is interior to A, or A has O at a vertex and
  L1,L2 are radial S leaves in its two perpendicular side directions.

No triangle equation is used in that lemma. Its full S/S,S/D,D/D
support-face proof therefore applies to the present actual root.

The true zero-load degree-two U is a normal transmitter. Let n be
its outward direction from A toward V, and let w be its reserve.
The original support and torque equations give w in{1,sqrt(2)} and

    A subset {n.x <= h},
    V subset {n.x >= h+w},      h=h_A(n).

Both actual U applications and their entire allowed shared-side mean
domains remain. The sharp contained-unit support theorem in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section1, applies to the
actual unit V and gives

    h+w <= d.                                      (1)

It needs no force or circle-mask premise at V.

## 2. Every noncritical alternative is excluded

If d<1, origin-interior containment gives h>0. Then h+w>1>d,
contradicting (1).

If d>1, strict containment of the closed central disk gives
h>d-1. Then h+w>d, again contradicting (1).

If d=1 and O is interior to A, the same strict inequality h>0
contradicts (1). Thus the only remaining physical alternative is

    d=1,   R^2=17/4,
    A={a u+b v:0<=a,b<=1},
    L1=S(u),   L2=S(v),

where u,v are perpendicular unit vectors and

    S(e)={t e+s Je:1<=t<=2, -1/2<=s<=1/2}.

This is the entire exceptional equality geometry from the central-
disk lemma, not a chosen symmetric subfamily.

## 3. The critical support equality identifies a physical third terminal

Since O belongs to A, h>=0. Equation(1), d=1 and w>=1 therefore give

    h=0,   w=1,   min_(x in V) n.x=1.                (2)

The full sharp support equality theorem identifies V exactly as
S(n). This is a geometric conclusion about V's actual occupied square.
It does not give V positive degree one, and none of its other forces
or circle weights is removed.

The five bodies A,U,V,L1,L2 are distinct. In particular V cannot
equal either genuine leaf, since its positive edge to U would then
give that leaf a second positive neighbor.

The equality h_A(n)=0 for A=[0,1]u+[0,1]v is equivalent to

    n.u<=0,   n.v<=0.                               (3)

There are precisely two whole geometric alternatives: both signs are
strict, or one is zero. They are treated separately below, with every
actual transmitter mean retained.

## 4. Strict negative quadrant: the actual complete Y cage

Suppose both inequalities in (3) are strict. The support face of A
in direction n is the unique vertex O, so the actual A--U application
is O. U has side reserve1, and its other application is n.

The origin lies in the relative interior of U's incoming side. If
it were a vertex of U, the A--U physical contact would be singleton
vertex/vertex, with its positive normal equal to U's side axis.
The existing strict point-normal convention excludes that endpoint.
There is no shared A--U segment because A's support face is a unique
vertex. No normal is selected again here.

Rotate n to (0,1), and reflect or exchange u,v if needed. For exactly
some theta in(0,pi/2) and alpha in(0,1), the five actual units become

    U=[-alpha,1-alpha] x [0,1],
    A=[0,1](cos(theta),-sin(theta))
      +[0,1](-sin(theta),-cos(theta)),
    V=S((0,1)),   L1=S(u),   L2=S(v).

These are exactly the full physical family of Y_ALL_COMPLETION.md.
That theorem permits every other square to have an independent frame,
and uses only the actual physical cage, not the degrees or force
weights of its terminals. It permits at most three other units.
A nine-square packing would require four, which is impossible.

The exact open alpha and theta domains follow from the original
physical interface and strict sign alternative. Their axis boundaries
are handled next and have not been discarded as generic cases.

## 5. Axis endpoints: the whole P slider follows from the other leaf

By exchange of u,v assume n=-u. Then V=S(-u), U is aligned with A,
and its complete actual domain has the form

    U=[-1,0]u + [t,t+1]v.                            (4)

The A--U mean need not be the origin. Physical contact with
A=[0,1]u+[0,1]v gives

    t<=1,   t+1>=0.                                 (5)

Now use the other genuine leaf, which remains the actual unit

    L2=S(v)=[-1/2,1/2]u+[1,2]v.

Its open u-projection overlaps that of U. Since these two squares
are aligned, physical interior disjointness forces

    t+1<=1   or   t>=2.

The second alternative contradicts t<=1 in (5). Consequently

    -1<=t<=0.                                       (6)

Thus U's interval contains zero even when the actual A--U mean is
not zero. This is why the other genuine leaf is needed at this axis
endpoint; merely setting the original mean to zero would be invalid.

The four actual units L1=S(u), V=S(-u), A and U now form precisely
P_ALL_COMPLETION.md after rotation, with middle sliders

    t_R=1/2,   t_L=t+1/2 in[-1/2,1/2].

The full closed slider interval and its shared-contact endpoints are
included in that theorem. The four-square cage admits at most four
other units. The actual nine-square packing has five other units,
including the genuine leaf L2, so it is impossible. The n=-v endpoint
is the reflected same proof.

## 6. Scope and the complete four-cycle consequence

Sections2,4,5 exhaust the full radius, leaf and channel domain.
Every noncritical case is a local geometric contradiction. At d=1
both complete physical capacity theorems count all original bodies,
including any other positive neighbors of A or V. No positive force
is deleted to claim a terminal has degree one.

In a four-cycle A--B--C--D--A with two genuine leaves at A, A is
physically circle-clear. The actual B,D have positive degree two.
The theorem therefore forces both B and D positively loaded. C may
still be unloaded and is not forced by this result. The exact remaining
block-load sets are consequently

    {B,D},   {B,C,D}.

The entire one-adjacent-load, one-opposite-load and two-adjacent-load
families are excluded, for all S/S,S/D,D/D leaf choices and every
physical mask and mean. These are full load-family exits; the whole
four-cycle/two-leaf attachment remains open because both displayed
families still require their complete sharp or three-extra exit.

The theorem is also available at larger two-leaf roots with their
actual positive degrees. It is never applied to a higher-degree body
by deleting its other forces, or to a leaf that is only an aggregate
resultant without its original occupied physical square.

No numerical pose, angle discretization, secondary minimizer, Lean
compilation or CI is used.
