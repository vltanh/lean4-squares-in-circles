# An actual boundary contact respects the tangent sign of an outward owned side

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: complete new proposed force-free hand theorem and full-star
corollary, frozen for full independent review and root adoption.** The
physical theorem has no upper-radius bound, degree hypothesis or stress
equation. Its corollary retains an arbitrary complete original star.
All coordinates below are about the unchanged circle origin.

## 1. A positive inner corner cannot support another boundary unit inward

Let N,B>0 and let the actual unit K have own orthonormal coordinates

    K=[N,N+1] times [B,B+1],
    R^2=(N+1)^2+(B+1)^2.

Suppose an actual unit L contains P=(N,B), lies on the opposite side
of K's supporting line there, and has an inward unit support normal

    g=(-u,-v), u,v>0, u^2+v^2=1.

Then every point of L has norm strictly below R. In particular L
cannot physically touch the same circle.

First suppose P is a vertex of L. Write its two orthonormal inward
axes as r,s. The support condition is g dot r,g dot s>=0. Each axis
has at least one nonpositive displayed coordinate, since otherwise
its scalar product with the strict Southwest g would be negative.
Thus, with M=max(N,B),

    P dot r<=M, P dot s<=M.

Each adjacent L corner therefore has squared norm at most

    |P|^2+1+2*M<R^2,                                    (1)

whose strict reserve is 1+2*min(N,B)>0.

For the opposite L corner put w=r+s. We have |w|=sqrt(2), and

    g dot w=(g dot r)+(g dot s)>=1,

because the two nonnegative components of the unit g have squares
summing to one. Necessarily w_x+w_y<=0. Indeed, if their sum were
positive, at most one coordinate could be negative, and that negative
coordinate would have magnitude strictly below1 since |w|^2=2.
Then g dot w would be strictly below1: discard the nonpositive
contribution from the positive coordinate, and bound the other
contribution by that negative coordinate's magnitude. This contradicts
the preceding display.

On the radius-sqrt(2) semicircle w_x+w_y<=0, a positive-coordinate
vector P has maximal scalar product |N-B|. To see it explicitly,
write w=alpha*(1,1)/sqrt(2)+beta*(1,-1)/sqrt(2), with alpha<=0
and alpha^2+beta^2=2. Then

    P dot w=[(N+B)*alpha+(N-B)*beta]/sqrt(2)
             <=|N-B|.

It follows that

    |P+w|^2<=|P|^2+2+2*|N-B|<R^2,                        (2)

with strict reserve4*min(N,B)>0. P itself is also strictly inside.
This proves the complete vertex-support case.

If P lies on a side of L, retain its actual inward normal g and
write the full pose as

    L=P+[0,1]g+[-rho,1-rho]Jg, 0<=rho<=1.

For each corner its position is affine in the actual parameter rho.
At both endpoints rho=0,1 the preceding vertex proof applies, with
the same strict bounds (1)--(2). Convexity of squared norm gives the
same strict containment for every intermediate rho. Thus the whole
actual side interval, including either original mean endpoint, is
covered. No side point was replaced in a force equation.

## 2. Complete force-free boundary tangent theorem

Let R>1. In positively oriented own coordinates (n,j), j=Jn, let
an actual contained circle-touching unit K have pose

    K=[N,N+1] times [B,B+1], N>0, B>=-1/2.               (3)

Thus its actual center has nonnegative j coordinate. The farthest
physical corner is (N+1,B+1), and

    R^2=(N+1)^2+(B+1)^2.                                (4)

When B=-1/2 both far-normal-side corners physically touch the circle;
no choice of their individual weights is involved.

Let L be another actual contained circle-touching unit, disjoint in
open interior from K, with an actual common supporting application p
and actual unit normal g directed from K into L. The application may
be any original shared-side mean, including either endpoint. Assume
its original-circle moment satisfies

    det(p,g)>0.                                         (5)

**Theorem.** Then g dot j>=0.

Suppose instead g_j<0. There are exactly three cases for g_n.

### 2.1. g_n>0

Write g=(u,-v), u,v>0, u^2+v^2=1. Its actual K support is the
unique corner p=(A,B), A=N+1>1. The positive moment (5) gives

    -A*v-B*u>0,

so B<0 and q=v/u satisfies 0<q<-B/A. On that entire closed
comparison interval, the function

    (A-B*q)/sqrt(1+q^2)

is nondecreasing: its derivative is
(-B-A*q)/(1+q^2)^(3/2)>=0. Consequently the actual support value

    h_K(g)=p dot g>=A.                                 (6)

But -1/2<=B<0 and (4) imply

    A>sqrt(R^2-1)>R-1,

where the second inequality follows by squaring positive quantities
and using2*(R-1)>0. A real unit L beyond this common line has width
at least1 in direction g and lies in the radius-R disk. It therefore
requires h_K(g)<=R-1, contradicting (6).

### 2.2. g_n=0

Now g=(0,-1). Every actual support application has p_n>=N>0,
so det(p,g)=-p_n<0. This contradicts (5), including every side mean.

### 2.3. g_n<0

Write g=(-u,-v) with u,v>0. Its unique actual K support is
p=(N,B). Equation (5) says

    -N*v+B*u>0,

so B>0. The complete positive-inner-corner lemma of Section 1 now
places the entire actual L strictly inside the same radius-R circle.
This contradicts its physical boundary contact.

All three cases are impossible, proving the theorem. The equality
g_j=0 was deliberately retained. It does not follow that every
boundary contact has a strictly positive j component.

## 3. The physical corner resultant supplies the required mask sign

Let K have an actual owned inward side axis n with minimum support
N>0 about the original circle origin. In its own axes write

    K=[N,N+1] times [B,B+1].

Every physical circle corner is on its far normal side: for a fixed
j coordinate, increasing the normal coordinate from N to N+1 raises
squared norm by2*N+1>0. If the actual center's tangent coordinate
B+1/2 were negative, every physical circle corner would have tangent
coordinate B<0. Thus every nonzero nonnegative combination F of its
physical circle corners would satisfy F dot j<0.

Consequently F dot j>=0 implies B>=-1/2. This implication includes
both physical circle corners when B=-1/2 and allows either individual
circle coefficient to vanish. Combined with Section 2, it gives:

    N>0, F dot j>=0, det(p,g)>0
              imply g dot j>=0                          (7)

for every actual boundary neighbor at its original application.
No force balance or degree hypothesis is needed for (7).

## 4. Arbitrary full-star circle-force sign corollary

Retain an actual loaded K with an actual owned side axis n of positive
minimum support N>0, and put j=Jn. Partition its complete original
positive neighborhood into two actual sets, retaining every original
force, application and mean:

- incoming directions m_i, each directed from its actual neighbor
  into K, with m_i dot j<=0;
- outward directions g_k toward actual boundary neighbors, with
  det(p_k,g_k)>0 at their original applications.

Let lambda_i,mu_k>0 be all their original magnitudes. The full original
force equation is precisely

    F+sum_k mu_k*g_k-sum_i lambda_i*m_i=0.               (8)

The owned-side contact may be one of the incoming terms with m_i=n;
its tangent component is then zero. No restriction on the number of
original terms, their other scalar components, or their torque is
imposed. Every original torque equation remains available unchanged.

**Corollary.** Necessarily F dot j<=0.

If F dot j>0, (7) applies to each actual outgoing boundary contact
and gives g_k dot j>=0. Taking the j projection of the complete (8)
then yields

    F dot j=sum_i lambda_i*(m_i dot j)
               -sum_k mu_k*(g_k dot j)<=0,

a contradiction. This is a full-star projection, not a two-force
substitution or a fictitious contact at a grouped mean.

Reflection gives the complete reversed statement: if every incoming
m_i has nonnegative j component and every indicated boundary contact
has negative original moment, then F dot j>=0. The reflection changes
the signs of both displayed tangent coordinates and determinants;
it does not alter the physical packing or any original force.

## 5. Exact scope and applications

Sections 1--4 are self-contained. They use actual unit geometry,
the unchanged containing circle, the complete support faces and their
original-circle moments. The only radius requirement is R>1 in the
outer-support comparison. No upper radius bound, geometric sampling,
selected-normal change, computational exclusion packet, Lean run, CI,
ledger edit or remote mutation is used.

A caller must prove N>0 about the original circle origin; a local
coordinate translation to a contact would destroy that premise.
It must also establish the actual moment sign, for example from the
complete physical boundary-contact orientation theorem in its own
declared radius window. A third force cannot be omitted from (8).

The four-spoke pentagon application uses the true C3 with incoming
DC and HC and the actual boundary contact CB. The C-directed HC
tangent sign is proved geometrically from the real D-H-C triangle,
and N>0 comes from the true E2 and the actual opposite-port chart.
Those hypotheses are separate obligations of that caller.
