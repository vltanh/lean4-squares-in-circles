# A southern boundary page has a uniform depth beyond an aligned S-root wall

Date: October 28, 2026 UTC. Author: current root continuation.

**Status: complete new force-free hand theorem, frozen for a separate
full independent review.** The first theorem treats every physical frame
and every contact mean of the southern page. The second is a radius-free
wall-span inequality for any actual unit square. Their combination excludes
an entire region of possible upper contacts for any actual common neighbor,
without a force, degree, circle-load or normal-owner premise at that neighbor.
No whole original family or fine/coarse flag is declared closed.

All units below are the original actual closed unit squares, with pairwise
disjoint open interiors. No unit is replaced, no application is moved and
no positive edge or force is removed. Physical boundary means actual contact
with the containing circle, independently of all individual coefficients.

## 1. Complete physical southern-page statement

Let the unchanged containing radius and genuine aligned S rectangle obey

    2<=R<=sqrt(17)/2,
    d=sqrt(R^2-1/4)-1,
    e=d-1,
    29/50<=a<=2/3,
    b=a-1,
    X=[e,d] times [b,a],
    L=[d,d+1] times [-1/2,1/2].                       (1)

Thus

    14/15<d<=1, -1/15<e<=0,
    -21/50<=b<=-1/3,
    R^2=(d+1)^2+1/4.                                (2)

The strict lower bound on d follows from R>=2 and
15/4-(29/15)^2=11/900>0. The two closed radius endpoints and both
closed a endpoints in (1) are included.

Let D be any other actual square with an actual South contact to X:

    D subset {y<=b},
    Q=(x,b) in D intersect X, e<=x<=d.               (3)

The point Q may be any unchanged original shared-side mean. Assume that
D physically touches the containing circle. Its degree, loads, other
neighbors and all their forces are unrestricted.

**Southern-page theorem.** D is genuinely tilted. Its full actual frame
at its unique highest point Q is

    D=Q+[0,1](r,-s)+[0,1](-s,-r),
    r,s>0, r^2+s^2=1,

and necessarily

    x>2/5, r/s>2/3.                                 (4)

Every point Y of the whole actual D with Y_x<=e then satisfies the
uniform strict depth bound

    Y_y<b-4/15.                                     (5)

In particular (5) applies to every actual point of D intersect K for
any unchanged unit K contained in x<=e. It is a statement about the
whole contact set, not just a selected mean. Sections 2--4 prove it
directly; no polynomial certificate or root force equation is an input.

## 2. Every actual top contact is strictly to the right of 2/5

Choose any physical circle corner Z of D. Both Z and the unchanged Q
belong to the same unit, so their distance is at most sqrt(2). Hence

    |Q|>=R-sqrt(2)>=2-sqrt(2).

The exact inequality sqrt(2)<99/70, whose squared reserve is 1/4900,
gives

    (2-sqrt(2))^2=6-4sqrt(2)>12/35.

Consequently

    x^2>12/35-(21/50)^2
        >4/25,

where the last strict reserve is 113/17500. Since x>=e>-1/15,
the negative alternative x<-2/5 is impossible. Thus x>2/5.
The argument uses any physical boundary corner and remains valid when
its individual circle multiplier is zero.

If D's highest support is a side, its whole frame is

    D=[z,z+1] times [b-1,b], x-1<=z<=x.

Because -1/2<b<0, its open vertical projection overlaps that of the
actual occupied L. Their horizontal open intervals must therefore be
disjoint. The alternative z>=d+1 contradicts z<=x<=d, so z+1<=d.
Together with x>2/5 this puts every D corner in

    -3/5<X_coordinate<=1,
    -71/50<=Y_coordinate<0.

All squared corner norms are at most

    1+(71/50)^2=7541/2500<4<=R^2.

This contradicts physical boundary contact. Thus the highest support
is a unique vertex Q, with the full tilted frame in Section 1. All
parallel frames and all actual side-mean endpoints have been handled.

## 3. Every tilt with r/s<=2/3 has all four corners strictly inside

Suppose r/s<=2/3 and write q=r/s. In this full continuous interval,

    r<=2/sqrt(13)<5/9,
    s-r>1/4,
    r+s<=5/sqrt(13)<7/5.                            (6)

For the last two comparisons, (1-q)/sqrt(1+q^2) decreases and
(1+q)/sqrt(1+q^2) increases on 0<=q<=2/3. At q=2/3 they are
1/sqrt(13)>1/4 and 5/sqrt(13)<7/5. The strict rational reserves
follow from 13<16 and 625<637. The comparison 2/sqrt(13)<5/9
follows from 324<325. The axis endpoints were already treated in
Section 2, while the enlarged closed comparisons in (6) are harmless.

The top corner Q has squared norm at most 1+(21/50)^2<4. The left
adjacent corner Q+(-s,-r) has horizontal absolute value less than one,
because 2/5<x<=1 and 0<s<1. Its vertical absolute value is at most
21/50+r<21/50+5/9<1. This corner is strictly inside radius two.

The opposite corner is

    Z_opp=(x+r-s,b-r-s).

By x>2/5, x<=d<=1 and (6),

    -3/5<(Z_opp)_x<3/4,
    |(Z_opp)_y|<21/50+7/5=91/50.

Thus

    |Z_opp|^2<(3/4)^2+(91/50)^2
                =38749/10000<4,                    (7)

with strict reserve 1251/10000. This covers the entire q<=2/3
range, without choosing which corner might carry a positive coefficient.

It remains to treat the right adjacent corner

    Z_right=(x+r,b-s).

For 0<q<=1/2, r<=1/sqrt(5)<9/20 and s<1 give

    |Z_right|^2<(d+9/20)^2+(71/50)^2.

After subtracting the exact R^2 in (2), the right side becomes

    -(11/10)d+9689/10000
        <-1733/30000<0.                             (8)

The lower bound d>14/15 supplies the strict final comparison.

Now retain the full closed interval 1/2<=q<=2/3. If x+r<=d,
then |Z_right|^2<=1+(71/50)^2<4. Otherwise the real downward
edge Q+u(r,-s) crosses the actual occupied leaf wall x=d before
u=1. At that crossing it must be at height at most -1/2; a higher
crossing would immediately enter int(L). With T=a-1/2>=2/25,
the full physical screen is

    x<=d-Tq<=d-1/25.                               (9)

Equality at the leaf's inner lower corner and at either parameter
endpoint remains allowed. On this same interval r<5/9 and
s<=2/sqrt(5)<9/10. Both coordinates of Z_right have known signs,
so (9) gives the strict comparison

    |Z_right|^2<(d+116/225)^2+(33/25)^2.

Subtracting the actual R^2 gives exactly

    -(218/225)d+30707/40500
        <-5917/40500<0.                             (10)

Again d>14/15 is used; no radius is held fixed independently of d.
The intervals in (8) and (10) overlap at q=1/2 and cover every
q<=2/3. Every one of the four actual corners is strictly inside
the containing circle. By convexity the whole square is strictly
inside. This contradicts D's physical boundary premise and proves
r/s>2/3, including exclusion of the equality q=2/3.

## 4. The depth bound holds on the complete actual left part of D

Write any actual Y in D in its unchanged frame as

    Y=Q+u(r,-s)+v(-s,-r), 0<=u,v<=1.

If Y_x=x+ur-vs<=e, then

    v>=(x-e+ur)/s.

Therefore its actual height satisfies

    Y_y=b-us-vr
        <=b-(r/s)(x-e)-u(s+r^2/s)
        =b-(r/s)(x-e)-u/s
        <=b-(r/s)(x-e).

The already proved x>2/5, e<=0 and r/s>2/3 imply

    Y_y<b-4/15.

This proves (5) for every actual point on or beyond the closed wall,
including every endpoint or aggregate mean of a real contact there.
No assertion that D has true degree two or a proper concurrence was used.

## 5. A radius-free wall-span inequality for an arbitrary actual unit

Let K be any actual unit square contained in the closed half-plane
x<=E, and let M be any actual point of K. Then

    min_K y>=M_x+M_y-E-1.                            (11)

To prove this, first use its actual maximum horizontal coordinate
E_K<=E. If K is axis-aligned, its vertical width one gives
min_K y>=M_y-1>=M_x+M_y-E_K-1, as M_x<=E_K.

Otherwise let its unique rightmost point be P=(E_K,t), and write
the complete tilted frame

    K=P+[0,1](-c,s)+[0,1](-s,-c),
    c,s>0, c^2+s^2=1,
    M=P+lambda(-c,s)+mu(-s,-c),
    0<=lambda,mu<=1.

The exact difference between min_K y=t-c and the proposed right
side using E_K is

    1-c-lambda(s-c)+mu(s+c).

If s>=c, it is at least 1-s>0. If s<=c, it is at least 1-c>0.
This includes s=c and all four parameter endpoints. It proves the
strict inequality in the tilted case. Finally E_K<=E gives (11).
No containing-circle, contact, degree, load or equilibrium premise is
needed for this separate theorem. The constant one is attained by an
aligned unit and its top-right vertex, so no hidden strictness is used
when applying it to every frame.

## 6. A complete forbidden upper-contact region for any common neighbor

Keep the actual X,L,D chart (1)--(3), and let K be any distinct
actual unit contained in x<=e that physically touches D. There cannot
be any point M in K satisfying

    M_x+M_y>=e+a-4/15.                              (12)

Indeed (11) would give min_K y>=a-1-4/15=b-4/15, whereas every
actual point of D intersect K has x<=e and hence y<b-4/15 by (5).
The closed-contact contradiction includes equality in (12). K may
have arbitrary true degree, all original forces and any physical
circle mask. It need not have a selected horizontal force or even
touch X for this implication; the actual whole half-plane and real
D contact are its explicit hypotheses.

One useful closed-parameter consequence is as follows. Let

    N=(e,a),
    M=N-v(s,c),
    c,s>=0, c^2+s^2=1, 0<=v<=11/60.                 (13)

Such an M cannot belong to K. By Cauchy--Schwarz and sqrt(2)<17/12,

    v(c+s)<=11sqrt(2)/60<187/720<4/15,

and the last rational reserve is 1/144. Thus M satisfies (12)
strictly. Both axis limits, v=0, v=11/60, and all actual intermediate
side means are included. A caller must prove that its unchanged
contact really has the form (13); no normal ownership or force
equation is inferred from this notation alone.

## 7. Literal caller boundary and provenance

The actual low aligned strict-Northwest fan chart has precisely the
physical quantities (1)--(3) after the whole packing has been reflected
to place the strict upper root vertex at N=(e,a). The present source
does not establish that entry, any upper-page return feature, or a
complete original fan exclusion. It supplies the degree-free full
southern-contact depth and a forbidden region for any actual unit
meeting that page from the left. The same implication applies to any
other original graph satisfying these literal physical hypotheses.

The actual radial rectangle and unchanged d relation are those of
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, SHA256
faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676.
No later force or graph equation from that source is imported.

The older ALIGNED_LOW_S_ROOT_LOWER_BOUNDARY_UNIQUE_CORNER_AND_CENTER.md,
SHA256 c32b99ad24da76907f2e3eaa4d4e7c88b9b2d2599a0eefe50234fae493441c48,
provided useful context while developing the new depth estimate. Its
root-degree entry, full unique-corner proof and later degree-two
concurrence conclusion are not operative inputs here. Sections 2--4
above give a complete independent four-corner exclusion of the entire
r/s<=2/3 domain with only elementary whole-interval inequalities.

Full separate independent review of these exact bytes is required
before adoption. All nine original units, true degrees, full equations,
selected normals, actual application sets and circle coefficients remain
available in any caller. No geometric pose search, sampled angle, new
computational exclusion certificate, Lean source or build, CI, workflow,
merge, metadata, ledger, commit or remote mutation is used by this proof.
