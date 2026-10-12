# Two-force contact transmission has only side or diagonal directions

## Theorem (rigid square, arbitrary surrounding orientations)

Let S be a unit square in a disk centered at zero, strictly inside
the containing circle. Suppose a normalized physical equilibrium stress
has **exactly two nonzero contact force resultants acting on S**,
at two distinct neighboring squares A and B. Let z_A,z_B be their
actual effective contact points, each belonging to the corresponding
common contact set. The disk exerts no nonzero circle reaction on S
because S is strictly interior.

Then there exists a unit vector n and a positive force magnitude
lambda such that the two forces on S are +lambda n and -lambda n, and

    z_A-z_B = 2 h_S(n) n.                              (1)

Here the direction n is chosen so that z_A supports S in
the +n direction, and z_B supports it in the -n direction,
and h_S denotes the support function of S centered at
its own center.

**Classification.** Relative to the orthonormal edge frame
(e,f) of S, the unit vector n must be either:

* one of the four signed side normals +/-e, +/-f, in
  which case h_S(n)=1/2 and the two contact points
  lie on opposite sides at identical transverse
  coordinate, precisely one unit apart; or
* one of the four signed diagonal directions
  (+/-e+/-f)/sqrt(2), in which case h_S(n)=1/sqrt(2),
  z_A and z_B are the opposite vertices of S,
  and their separation is sqrt(2).

**No other contact-force direction is possible.**
In particular a normal strictly inside a vertex normal cone
but different from its bisecting diagonal cannot support
a circle-free two-force equilibrium square.

The statement concerns the **two chosen positive stress
resultants**, not the count of actual neighboring squares:
S may have additional genuine contacts carrying zero chosen
stress weight. It applies to the central square whenever
its positive stress degree is two.

## 1. Force balance gives opposite normals

Let the two nonzero forces on S be F_A,F_B, applied at
z_A,z_B. Because S has no positive circle reaction,
the physical translation equation is

    F_A+F_B=0.

Neither force is zero by hypothesis. Choose a unit n so
F_A=lambda n, F_B=-lambda n with lambda>0.
The force at A acts inward or outward according to
contact orientation; choose the label A so that
**S is supported at z_A in direction n**.
Equivalently, define n as the outward support normal
from S toward A, so the force on S exerted by A
is -lambda n. Relabeling the signs consistently,
we may therefore write the actual forces as
-lambda n at z_A and +lambda n at z_B.

Their opposite normals are separating normals:
the nonoverlapping neighboring squares are on
the positive n and negative n sides of S
respectively. Hence

    n dot(z_A-p_S)=h_S(n),
    n dot(z_B-p_S)=-h_S(n).                           (2)

These are contact **support identities**, not
strict inequalities or a choice of frame.

## 2. Moment balance makes the contact points collinear

The moment about the disk origin of the two
forces on S is zero (circle reactions are absent):

    -lambda*(z_A cross n)+lambda*(z_B cross n)=0.

Thus

    (z_A-z_B) cross n=0.                             (3)

So z_A-z_B is parallel to n. Subtracting (2),

    n dot(z_A-z_B)=2 h_S(n)>0.

As n is unit, (3) implies the exact vector identity

    z_A-z_B=2 h_S(n) n,

which is (1). In particular the entire segment between
the two contact points lies on one force line.
No torque from another contact may be inserted:
we used the hypothesis that **exactly two
resultants are nonzero**.

## 3. Classify supporting faces of a unit square

Write S=p_S+[-1/2,1/2]e+[-1/2,1/2]f.

If n is a side normal (+/-e or +/-f), the two
opposite supports of S are parallel edges at
distance one. Equation (1) forces z_A-z_B=n,
so the contacts have the same coordinate
along the edge (the transverse coordinate).

If n is not a side normal, its two edge-frame
components are both nonzero. Its support faces
are then the unique pair of opposite vertices

    z_A=p_S+(sgn(n dot e)*e+sgn(n dot f)*f)/2,
    z_B=p_S-(sgn(n dot e)*e+sgn(n dot f)*f)/2.

Their difference is

    v=sgn(n dot e)*e+sgn(n dot f)*f,

which has length sqrt(2) and diagonal direction.
By (1), v is parallel to n with positive scalar,
so necessarily n=v/sqrt(2).
These are exactly the four diagonal directions
listed in the theorem.

The cases exhaust all unit vectors and preserve
vertex, edge and zero-weight-contact degeneracies.
This completes the proof.

## 4. Quantitative consequence for the n=8 sharp radius range

Suppose S is the central square of an eight-square
packing with squared radius q<=9789/2500.
Since S contains the origin in its open interior
and q is above 2, S has no disk-circle contact.
If precisely two positive stress forces meet S,
the theorem restricts them to its side or diagonal
directions. Applying the opposite-separator
angle theorem HUMAN_OPPOSITE_CENTRAL_ANGLE.md
to their two neighboring squares gives:

    Side-force transmission:  delta>pi/2-1/100.
    Diagonal transmission:    delta>5*pi/8.

In the diagonal case the two force application
points are exactly opposite central vertices.
In the side case their force line meets opposite
central edges at the same transverse coordinate.

This closes the *classification of the local
two-force directions*. It does not establish
that the central stress degree is two, exclude
the diagonal case using the remaining squares,
force the twin motif, or produce the five
projected inequalities required for R8>=Rhat.


## 5. Diagonal transmission needs an additional zero-stress actual contact

In a radius minimizer selected to have the fewest **actual**
contacting pairs, a square strictly inside the containing disk
with **actual contact degree two** has opposite *side*
contact normals, by the already proved
HUMAN_CYCLE_ANALYSIS.md, section 8. (That theorem uses
the minimum-contact choice and local deformations;
it does not follow merely from physical moment balance.)

Consequently, if the same square carries exactly two
positive-stress resultants and their common line is a
**diagonal** of the square, the square cannot have
actual contact degree two. Since its two positively
stressed neighbors are already actual contacts,
it must have at least one **additional actual neighbor**,
which necessarily carries zero multiplier in the
chosen two-edge physical stress.

This precise branch implication prevents using a
diagonal two-force member as an unsupported
degree-two actual transmitter. It does not
exclude the case: a zero-stress actual contact
can still constrain a minimizer's allowed motion.
