# The entire unique/unique opposite-load C4 mask is impossible

**Status: complete conditional hand exclusion; root and independent full
hand audits passed.** Work at the canonical radius minimizer chosen in
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, in the window
\[
                  79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The selected positive component is a four-cycle A--B--U--D--A
with a pendant radial leaf at A. The articulation A and transmitter U
have zero circle load, B and D have positive circle loads, and **each
of B,D has exactly one physical circle corner**.

**Theorem.** This entire physical unique/unique mask is impossible.
Every S/D leaf, singleton owner, U-parallel tip, actual channel mean,
and all four arbitrary completion squares are retained.

The theorem is conditional on the secondary minimizer used for the
radius lower-bound argument. It does not classify every noncanonical
packing, and it does not remove a physical two-circle-corner mask.

## 1. The exhaustive selected domain

Use the completed results

* UNIT_BYPASS_NORMAL_CHANNEL.md;
* FOUR_CYCLE_UNIQUE_LOAD_NORMAL_SELECTION.md;
* FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md;
* FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, Sections 1--6.

They give a common vertical force channel, a physical AU contact,
A oblique to U, and singleton AB and AD intersections. Neither AB
nor AD has a free vertex/vertex normal in the selected certificate.
Thus each is owned by A or its loaded tip. No shared-side mean on
BU or UD has been fixed.

Choose coordinates
\[
 \begin{split}
 U&=[X-1,X]\times[Y,Y+1],\\
 P&=(X,y_0),\qquad Y<y_0<Y+1,\\
 v&=(a,b),\quad w=(b,-a),\qquad a,b>0,\quad a^2+b^2=1,\\
 A&=P+[0,1]v+[0,1]w.
 \end{split}
\tag{2}
\]
Here P is the unique leftmost vertex of A. The actual two channel
applications are
\[
                       p=(x,Y),\qquad p+e_y=(x,Y+1),
                       \qquad X-1\le x\le X.
\tag{3}
\]
Their common x-coordinate follows from U's torque balance. Their
positive magnitudes are equal; denote that magnitude by gamma.
Also
\[
                   B\subseteq\{y\le Y\},\qquad
                   D\subseteq\{y\ge Y+1\}.
\tag{4}
\]
Since D has vertical width at least one and is contained in the disk,
\[
                              Y\le R-2<1.
\tag{5}
\]

A side axis at a singleton vertex/vertex intersection is not a strict
common normal. Consequently an owned singleton has its application
in the relative interior of the owner's side and at a vertex of
the other square. If the normal is a side axis of both bodies, the
same conclusion would instead give a positive-length shared side,
which has already been excluded.

## 2. An A-owned lower contact forces a>=b

Suppose A owns AB. The physical triangle AUB gives the owner sign
that its outward AB normal has nonpositive x-component. The only
A axes with that sign are -v and -w. The minimum-w face lies above
y_0 and cannot meet B. Thus
\[
             n_{AB}=-v,\qquad q=P+\tau w,\quad 0<\tau<1.
\tag{6}
\]
In particular q_x>X. Write the unique B circle force as a positive
multiple of its circle corner z. Its force balance is
\[
                           F_B=-\mu v-\gamma e_y,
                           \qquad \mu,\gamma>0.
\tag{7}
\]
Both global coordinates of z are therefore strictly negative.

We prove a>=b, with a strict inequality whenever B is oblique to U.

### 2.1. Every oblique B gives the strict inequality

If B is oblique to U, p is its unique top vertex. Write its inward
axes as
\[
                    r=(c,-s),\quad t=(-s,-c),
                    \qquad c,s>0,\quad c^2+s^2=1.
\tag{8}
\]
The A application q is a B vertex. It is not p, since q_x>X>=x.
It is not p+t, whose x-coordinate is smaller still. At the opposite
vertex p+r+t, the outward normal v would have to have nonnegative
scalar product with t; instead v dot t=-as-bc<0. Hence
\[
                    q=p+r,\qquad ac-bs>0.
\tag{9}
\]
The inequality is strict: equality would make v=-t, so the B support
side through q is parallel to and overlaps a positive segment of
A's side, since q is an A-side-interior point. That is excluded by
Section 1.

Suppose for contradiction b>=a, and put rho=b/a>=1. Then (9) gives
c>s. The contact lines through p and q meet at
\[
             Q=p-\eta e_y,\qquad \eta=s+\rho c>1.
\tag{10}
\]
Torque about Q makes Q a scalar multiple of z. By (5), Q_y=Y-eta<0;
also z_y<0 by (7). The proportionality is consequently positive:
\[
                               Q=\kappa z,\qquad \kappa>0.
\tag{11}
\]

Neither p nor q can be a circle point shared by a second contained
unit square. The only possible unique circle corners are therefore
p+t and p+r+t. These two masks are both impossible.

If z=p+r+t, its r-coordinate is p dot r+1>1/2. On the other hand,
\[
 Q\cdot r=p\cdot r+\eta s,
 \qquad \eta s=s^2+\rho cs<1,
\tag{12}
\]
since (9) gives rho<c/s. Thus (11) implies kappa<1. But z_x<0 and
z_x=x+c-s>x, so x<z_x<0. Equation x=kappa z_x is incompatible
with 0<kappa<1.

If z=p+t, uniqueness gives z dot r=p dot r<-1/2 and
z dot t=p dot t+1>1/2. Now Q dot r=z dot r+eta s>z dot r,
so (11) again gives kappa<1. Comparing the positive t-coordinate
then yields eta c<1. Instead
\[
                       \eta c=cs+\rho c^2\ge cs+c^2>1,
\tag{13}
\]
because c>s. This is the second contradiction. Therefore a>b for
every oblique B.

### 2.2. Every U-parallel B gives a>=b, with its exact equality case

Now suppose B is parallel to U. Its upper side lies on y=Y and
contains the genuine channel mean p. The outward B-to-A normal v
has both coordinates positive, so its A contact q is its upper-right
vertex. By (7), its unique circle corner is its lower-left vertex.
Write
\[
 z=(-\xi,-\zeta),\qquad \xi,\zeta>1/2,\qquad
 q=(1-\xi,1-\zeta),\qquad
 p=q-\ell e_x,\quad 0<\ell\le1.
\tag{14}
\]
The strict lower bound follows from p_x<=X<q_x. The upper bound
retains every mean, including the left endpoint of the shared side.

Normalize F_B=k z with k>0. The two force coordinates in (7) give
\[
        \mu a=k\xi,\qquad
        \gamma=k(\zeta-\xi\rho)>0,\qquad \rho=b/a.
\tag{15}
\]
The origin torque equation at B is
\[
                      \mu\det(q,v)+\gamma p_x=0.
\]
Substituting (14)--(15) and dividing by k gives exactly
\[
                   \zeta-\xi-\ell(\zeta-\xi\rho)=0.
\tag{16}
\]
Since the denominator in (15) is positive and 0<ell<=1,
\[
          0<\zeta-\xi\le\zeta-\xi\rho,
          \qquad \rho\le1.
\tag{17}
\]
Thus a>=b. Equality a=b forces ell=1, so the channel mean is
exactly B's upper-left corner. No mean was assumed in deriving it.

**Lemma 2.1.** If A owns AB and B has one physical circle corner,
then a>=b. Equality requires B parallel to U and the BU mean at
B's upper-left corner.

Reflection across the horizontal axis, with the lower/upper labels
exchanged, gives the exact companion statement:

**Lemma 2.2.** If A owns AD and D has one physical circle corner,
then b>=a. Equality requires D parallel to U and the UD mean at
D's lower-left corner.

## 3. Every mixed A-owner/tip-owner transition is impossible

Suppose A owns AB and D owns AD. Lemma 2.1 gives a>=b.

First D cannot be parallel to U. A horizontal D-owned AD normal
pointing left would expose A's leftmost vertex P, whose height lies
strictly inside the channel and cannot belong to D. A horizontal
normal pointing right would place all of D beyond A's right support
x=X+a+b>X, contradicting its contact with U. A downward vertical
normal exposes A's lowest vertex, again below D. The only remaining
axis is upward vertical. Then both forces into D are upward, making
its circle vector vertical. An axis-parallel square with a unique
physical circle corner cannot have that corner's horizontal
coordinate zero: the opposite horizontal endpoint would be farther
from the origin. This last axis is impossible too.

Thus D is oblique to U. Its bottom vertex is p+e_y, and write
\[
               r_D=(c,d),\quad t_D=(-d,c),\qquad
               c,d>0,\quad c^2+d^2=1.
\tag{18}
\]
The complete side-feature check in
FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md, Section 1, applies here:
it uses only A's position to the right of the channel and its other
application below Y. The two possible D-owned contacts and normals
are
\[
 \begin{array}{c|c}
 q_D=p+e_y+\sigma r_D & n_{AD}=t_D\\
 q_D=p+e_y+r_D+\sigma t_D & n_{AD}=-r_D
 \end{array}
 \qquad 0<\sigma<1.
\tag{19}
\]
Both normals have negative x-component. The A application is a
vertex. It cannot be P or P+w, which lie below D. It cannot be
P+v+w, whose outward normal cone consists of positive combinations
of v,w and has strictly positive x-component. Hence it is P+v.
At that vertex all nonzero support normals have positive y-component.
Only the first row in (19) survives, and its A normal-cone condition is
\[
                              bc-ad\ge0.
\tag{20}
\]

For clarity, the unique-circle consequence of this near-side feature
is recalled explicitly. The force into D is a positive combination
of t_D and e_y, so both its own coordinates are positive and its
unique circle corner is
\[
                         z_D=p+e_y+r_D+t_D.
\]
The two lines concur at
\[
                         Q_D=p+e_y+(\sigma/d)e_y.
\]
This is a positive multiple of z_D: at least one own coordinate
of z_D exceeds one because R^2>2, and the corresponding coordinate
of Q_D is obtained from that of p+e_y by a positive increment.
Both coordinates of the force are positive. Comparing their
r_D coordinates, which differ by sigma<1 versus1, gives a
proportionality strictly less than one. The global x-coordinate of
z_D is negative, since its force has negative x-component. Therefore
x=kappa_D(x+c-d), with x<0 and 0<kappa_D<1, forces
\[
                                    c<d.
\tag{21}
\]
Equations a>=b and c<d make bc<ad, contradicting (20).

Reflection excludes the other mixed transition. Every actual
channel mean was retained in both arguments.

## 4. The complete two-A-owner endpoint is incompatible with the leaf

Suppose A owns both AB and AD. Lemmas 2.1--2.2 force
\[
          a=b=1/\sqrt2,
\]
and both B,D are parallel to U. Their channel means are respectively
their upper-left and lower-left corners. Equation (3) therefore
makes their horizontal intervals identical, with A contacts
\[
                           q_B=p+e_x,
                           q_D=p+e_x+e_y.
\tag{22}
\]
Writing q_B=P+tau_B w and q_D=P+tau_D v, their unit vertical
difference gives
\[
        \tau_B=\tau_D=1/\sqrt2,\qquad
        P=p+(1/2,1/2).
\tag{23}
\]
The two unique circle corners are (x,Y-1) and (x,Y+2).
Their equal squared norms force Y=-1/2. Their x-coordinate is
negative, so
\[
 \begin{split}
 x&=-M,\qquad M=\sqrt{R^2-9/4},\\
 P&=(1/2-M,0),\qquad 5/4<M\le23/16<3/2.
 \end{split}
\tag{24}
\]

Let k_B,k_D be the positive scales of the two circle vectors.
The force coordinates at the lower and upper tips give
\[
                 \gamma=k_B(3/2-M)=k_D(3/2-M).
\tag{25}
\]
Thus k_B=k_D, and their A-edge magnitudes are equal as well.
The force balance at A consequently makes its pendant leaf direction
exactly east.

A radial D leaf is impossible here because its direction must be an
A side axis, whereas A's axes make angles of45 degrees with east.
A radial S leaf would require A's east support to be
\[
                           h=\sqrt{R^2-1/4}-1>9/10.
\]
Instead (23)--(24) give
\[
                  h_A(e_x)=1/2-M+\sqrt2
                         <\sqrt2-3/4<2/3.
\tag{26}
\]
This is the required contradiction. It excludes the full endpoint
family, not merely a generic or strictly oblique subcase.

## 5. Exhaustion of the unique/unique mask

Each singleton A-tip edge has a side owner by Section 1.
If both are A-owned, Section 4 excludes the configuration.
If exactly one is A-owned, Section 3 excludes it.

If both are tip-owned, neither loaded tip can be parallel to U:
the same complete axis check in Section 3, reflected for B, would
make its sole circle vector parallel to a side axis and contradict
its physical unique-corner mask. Both tips are therefore oblique
to U, and their two A applications are in their relative side
interiors. The complete theorem
FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md excludes this last case.

All owner possibilities, parallel endpoints, positive channel means,
and the two radial leaf types have now been exhausted. The entire
physical unique/unique opposite-loaded-pair C4 alternative is
impossible at the canonical radius minimizer.

The separate two/two and both mixed-mask leaf theorems now exhaust
the remaining physical masks, with every radial corner-weight split
and actual channel mean retained. FOUR_CYCLE_OPPOSITE_LOAD_BRANCH_CLOSED.md
assembles the complete opposite-loaded-pair closure at the canonical
minimizer. The all-three-loaded C4 and diamond domains remain separate
open branches; no whole parent-cell or unrestricted closure is asserted.

No numerical pose search, Lean compilation, CI, or change to the
strict selected point-normal convention is used.
