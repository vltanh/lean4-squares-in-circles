# Equality rigidity for the sharp two-aligned-end five-corner theorem

**Status.** A hand-proof equality classification under the explicit
six directed separator hypotheses of HUMAN_TWO_ALIGNED_ENDS.md.
This sharpens that result: **although B,D,G,H may be freely
oriented in the lower-bound statement, equality in its radius
forces B,D to align with A,E and G,H to align with e,f.**

The result is conditional on the chosen directed separators
and on A,E already having a common frame. It is not a proof
that an arbitrary eight-square minimizer satisfies the
hypotheses, and not a global classification of all eight
square positions or unused slider degrees of freedom.

## Theorem

Let A,B,D,E,G,H be unit squares inside a disk
`D_R` with pairwise disjoint open interiors.
Assume the two end squares A,E have the same
side frame `(a,b)`, and all six directed
support inequalities (1)--(2) of
HUMAN_TWO_ALIGNED_ENDS.md hold for one
tilt `0<=t<=pi/4` and
`e=cos t*a+sin t*b`, `f=-sin t*a+cos t*b`.

At the sharp conditional radius `R=R_hat`
the following are necessary:

1. All five disk points P1,...,P5 constructed
   in that theorem have **norm exactly R_hat**,
   and all five projected-chain inequalities
   are **equalities**.
2. B and D have sides parallel to a,b.
3. H and G have sides parallel to e,f.
4. All six directed support inequalities
   used in the reduction are **equalities**.
   If the B-D middle gap came from two
   separators via an intermediate unit
   square C, then C also has sides parallel
   to a,b, and both of its separators
   have equality.

The word 'equalities' in (4) refers to
**tight support projections**. A tight
support projection does not by itself
imply that two closed squares actually
intersect; that additionally requires
overlap of the corresponding support
faces. This theorem does not conflate
the two notions.

## 1. A five-corner chain at the least radius is entirely active

We prove the following auxiliary lemma, which
does not involve any square orientation.

**Five-point equality lemma.**
If five points P1,...,P5 in D_(R_hat)
satisfy all five projected inequalities
from FIVE_CORNER_REDUCTION.md,
then every inequality is an equality
and every point has norm exactly R_hat.

**Proof.** Work in the normalized a,b frame
and write `q=R_hat^2`,
`y=b dot P1`. The proof of the exact
scalar reduction, FIVE_CORNER_REDUCTION.md
section 1, defines the successive
positive radicals x1,x2,x3,y3,y4,x4
and the negative quantities h1,h2.
It establishes

    q >= |P5|^2 >= h1^2+h2^2 = q+F(q,y,t).       (1)

The complete analytic family-optimization
theorem HUMAN_FAMILY_CLOSURE.md proves
that `F(q,y,t)>=0` for every allowed
radical position and tilt at this sharp
radius, with equality only at the
unique minimizing position and tilt.
(The position variable is `u=-y` in
that note; the tilt is strictly
between 0 and arctan(1/5).)

Consequently (1) has equality everywhere.
In particular `|P5|=R_hat`, and because
its two frame projections are bounded
above by *strictly negative* h1,h2,
we must have

    e dot P5=h1,       f dot P5=h2.              (2)

The e chain then reads

    e dot P1 >= 2+cos t+h1
             =cos t*x1+sin t*y,

whereas disk containment yields the
opposite inequality. Since `cos t>0`,
equality forces `P1.x=x1`, hence
`|P1|=R_hat`, and makes the fifth
chain inequality tight.

Similarly the f chain and (2) force

    f dot P4=psi(y4),

where `psi(z)=sin t*sqrt(q-z^2)+cos t*z`
is strictly increasing on the
relevant negative ordinate interval.
The scalar reduction already has
`P4.y<=y4`, and its slice support
gives `f dot P4<=psi(P4.y)`.
Equality throughout implies
`P4.y=y4`. Because the optimizing
tilt satisfies `t>0`, the f
support in this horizontal slice
is attained only at
`P4.x=x4=-sqrt(q-y4^2)`.
Thus P4 is on the circle and the
fourth chain inequality is tight.

The third chain inequality gives
`P3.y>=P4.y+2=y3`.
The radical reduction gives
`P3.y<=y3`. Therefore `P3.y=y3`.
Also `P3.x<=x3<0`, while
`q=x3^2+y3^2`; disk containment
forces `P3.x=x3`. Thus P3 lies
on the circle and the third chain
inequality is tight.

The second chain inequality then gives
`P2.x>=P3.x+3=x2`, whereas
`P2.x<=x2`; hence `P2.x=x2`.
Its ordinate satisfies
`P2.y>=y+2>0`, and since
`q=x2^2+(y+2)^2`,
disk containment forces
`P2.y=y+2`. Thus P2 is on the
circle and the second chain is tight.
The first chain is now also tight
because `P2.y-P1.y=(y+2)-y=2`.

Every P_i is on the circle and
every projected inequality is
an equality, as claimed. QED.

No assumption that arbitrary packed
squares already touch the containing
circle was made here; the circle
contacts are conclusions of equality
in the conditional five-point
radius problem.

## 2. The two arbitrary middle square frames become aligned

HUMAN_TWO_ALIGNED_ENDS.md defines
for any rotated unit square S the number

    L_S=2*h_S(a)=2*h_S(b),  1<=L_S<=sqrt(2),

and canonical points with center
offset `(1-L_S/2)(+/-a+/-b)`.
It proves that the two local
coordinates in S's **own** edge
frame have absolute values at most

    (1-L_S/2)*L_S
       =1/2-(L_S-1)^2/2.                           (3)

If `L_S>1`, the strict inequality
in (3) puts every such canonical
point in the **open interior** of S.

The constructed P2 is a canonical
point of B. By section 1 it is on
the disk boundary. A point in the
open interior of B cannot lie on
that boundary, because a small
open disk around it belongs to B
but would extend outside D_(R_hat).
Therefore `L_B=1`. A unit square
has projected width one along
a precisely when one of its side
normals is parallel to a; its
other side normal is automatically
parallel to b. Thus B shares the
frame of A,E.

Apply exactly the same reasoning
to the canonical point P3 of D.
It forces `L_D=1`, so D also
shares the a,b frame.

## 3. The tilted pair is forced into one common frame

The point P5 was chosen in H as

    P5=p_H+(L_H/2-1)*(e+f),
    L_H=2*h_H(e)=2*h_H(f).

The canonical-point estimate (3),
now in the e,f coordinate frame,
makes P5 an **interior point** of
H whenever `L_H>1`.
Section 1 puts P5 on the disk
circle, so `L_H=1`. Thus H has
sides parallel to e,f.

For G, recall the exact chain
used in the earlier proof:

    e dot(p_A-p_H)
      >=h_A(e)+2*h_G(e)+h_H(e)
      >=h_A(e)+1+h_H(e).                          (4)

The first inequality is the sum
of A-G and G-H directed separators;
the second uses `h_G(e)>=1/2`.
The end point P1 is the bottom-right
vertex of the aligned A, and
P5 has `e dot(p_H-P5)=1-h_H(e)`.
Hence

    e dot(P1-P5)>=1+2*h_G(e)+cos t.                (5)

By section 1, the left side of
(5) is exactly `2+cos t`.
Therefore `h_G(e)<=1/2`.
Every unit square has `h_G(e)>=1/2`,
so equality holds: `h_G(e)=1/2`.
This can occur only if e is a
side normal of G. Thus G also
has the e,f frame.

This recovers **both tilted frames**
solely from the equality conditions
of the projection argument.

## 4. The separators and optional central square

Every inequality in the proof of
HUMAN_TWO_ALIGNED_ENDS.md was
added with a nonnegative residual:
the three original outer-chain
separations, two successive
e separations, and one f separation.
Their sums are the five sharp
five-corner projections. Section 1
forces equality of each sum.
Since each individual residual is
nonnegative, every used directed
support inequality must be tight.

If B-D's center projection gap was
obtained by summing B-C and C-D
separators with a third square C,
the derivation was

    a dot(p_B-p_D)
       >=h_B(a)+2*h_C(a)+h_D(a)
       >=h_B(a)+1+h_D(a).

Equality of the final B-D budget
forces `h_C(a)=1/2`, hence
C has the a,b frame, and both
individual separators are equalities.

These conclusions concern directed
support projections only. Checking
whether corresponding faces overlap
and whether any additional square
can be placed in the remaining
space is a separate issue.

## 5. Remaining n=8 obligation

The lower-bound statement of the
two-aligned-end theorem permits
arbitrary B,D,G,H frames; this
equality theorem proves that their
frames must **spontaneously
recover the candidate pattern at
R=R_hat**, with no equality
orientation hypothesis added.

It does NOT show that every
unrestricted radius-minimizing
packing possesses two aligned end
squares and the six required
coherent directed separators,
nor does it exclude other sharp
equality arrangements.

The unrestricted inequality
`R8>=R_hat` remains unproved.
