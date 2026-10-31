# An oblique loaded pair cannot own both contacts to a unit bypass

**Status: complete exact hand implication; root and separate independent
hand audits passed.**
Consider a positive four-cycle A--B--U--D--A in the radius window

\[
              79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

The degree-two body U has zero circle weight, and B,D are loaded
degree-two bodies. Suppose the two contacts AB,AD are point contacts
in the relative interiors of sides of B,D, respectively. Suppose also
that neither B nor D has its frame parallel to U's frame. Then this
configuration is impossible.

Every physical one/two-circle-corner mask and every positive circle
weight allocation at B,D is retained. There is no radial-leaf hypothesis
and no force or torque assumption at A. Thus the theorem applies to any
unit-square bypass of the normal channel B--U--D, including the stated
owner chart of the opposite-loaded-pair C4-with-leaf branch.

The U-parallel/shared-side charts and the contacts owned by A are outside
this theorem. They are not obtained by substituting a zero component into
the oblique chart below, because their actual shared-side means can vary.
No whole C4 or C1.4.b1 closure is claimed.

Put

\[
 h=\sqrt{R^2-1/4}-1,
 \qquad 9/10<h<61/60.
\tag{2}
\]

Both inequalities follow by squaring at the endpoints of (1).

## 1. The complete oblique side-owner chart

`UNIT_BYPASS_NORMAL_CHANNEL.md` proves that U is side-normal, with
reserve exactly one, and that A and U are separated transversely.
Rotate the axes so transmission is upward, and reflect horizontally
so A is on U's right. Keep the containing-circle center at zero.
Write the actual two transmission applications as

\[
                  p=(x,y),\qquad p+e_y=(x,y+1).
\tag{3}
\]

B lies below y, D above y+1, and every point of A has first
coordinate at least U's right support, hence at least x.

Because B's frame is oblique to U, p is B's unique top vertex.
Its inward unit axes are

\[
           u=(a,-b),\quad v=(-b,-a),\qquad
           a,b>0,\quad a^2+b^2=1.
\tag{4}
\]

Similarly D has unique bottom vertex p+e_y and inward axes

\[
           w=(c,d),\quad t=(-d,c),\qquad
           c,d>0,\quad c^2+d^2=1.
\tag{5}
\]

Let q_B,q_D be the AB,AD applications. Each is a vertex of A:
a point in the relative interior of a side of each of two squares
would give a positive-length shared side, contrary to the hypothesis.

Two of B's four sides cannot contain q_B. Its minimum-u side has
points p+tau v, 0<tau<1, with first coordinate less than x,
whereas A lies to the right of x. Its maximum-v side has points
q_B=p+v+tau u. If A lay on the outward side of this face, the point
q_D in A, whose height is at least y+1 and first coordinate at least
x, would have to satisfy v dot(q_D-q_B)>=0. Instead

\[
                    v\cdot(q_D-q_B)\le-a-1<0.
\tag{6}
\]

The remaining two complete possibilities are

\[
\begin{array}{c|c|c}
 &q_B&\text{normal from A to B}\\ \hline
 I&p+\tau u&v=(-b,-a)\\
 II&p+u+\tau v&-u=(-a,b),
\end{array}
\quad 0<\tau<1.
\tag{7}
\]

Reflection gives the corresponding complete D alternatives

\[
\begin{array}{c|c|c}
 &q_D&\text{normal from A to D}\\ \hline
 I&p+e_y+\sigma w&t=(-d,c)\\
 II&p+e_y+w+\sigma t&-w=(-c,-d),
\end{array}
\quad 0<\sigma<1.
\tag{8}
\]

In all four combinations, q_D has height strictly more than one above
q_B. Since both points are vertices of the unit square A, they must
be opposite vertices. Their distance is sqrt(2), and their outward
support normals have scalar product at most zero.

Mixed I/II types have both normals in the same open quadrant, which
violates this last condition. With two type-II contacts the height
gap exceeds 1+b+d, so b+d<sqrt(2)-1<1/2. Consequently a,c>
sqrt(3)/2 and ac-bd>0, again making the two normals acute.

Only type I at both tips survives. In particular

\[
 \begin{split}
 q_B&=p+\tau u,\qquad q_D=p+e_y+\sigma w,\\
 1+\tau b+\sigma d&\le\sqrt2,\\
 bd-ac&\le0,\qquad c\ge b.
 \end{split}
\tag{9}
\]

The last equivalence follows by squaring bd<=ac and using the two
unit-vector equations. No owner type was omitted from (7)--(8).

## 2. The force equations and all physical circle masks

Let gamma>0 be the common magnitude on BU and UD, and let
alpha_B,alpha_D>0 be the other two edge magnitudes. The actual circle
force sums are

\[
        F_B=\alpha_B v-\gamma e_y,\qquad
        F_D=\alpha_D t+\gamma e_y.
\tag{10}
\]

Their coordinates in their own inward side bases are all positive:

\[
\begin{array}{ll}
 F_B\cdot u=\gamma b>0,&F_B\cdot v=\alpha_B+\gamma a>0,\\
 F_D\cdot w=\gamma d>0,&F_D\cdot t=\alpha_D+\gamma c>0.
\end{array}
\tag{11}
\]

Thus the physical farthest corners

\[
                    z_B=p+u+v,\qquad
                    z_D=p+e_y+w+t
\tag{12}
\]

are actual positive-weight circle corners. To see this with two
physical circle corners, a nonzero center coordinate fixes the sign of
every farthest corner in that axis. A zero center coordinate permits
both signs, but the strictly positive coordinate of (11) forces the
positive-sign corner to carry positive weight. There cannot be two
zero center coordinates in this radius window.

The two nonparallel contact lines on each tip meet at

\[
              q'_B=p-\frac{\tau}{b}e_y,
              \qquad q'_D=p+e_y+\frac{\sigma}{d}e_y.
\tag{13}
\]

Torque about that intersection makes q'_i collinear with F_i. The
proportionality is positive. Indeed in B's own coordinates the
intersection is p+tau u+(tau a/b)v; in D's it is
p+e_y+sigma w+(sigma c/d)t. At least one own coordinate of each
circle corner (12) exceeds one, since R^2>2. That coordinate of its
opposite vertex p or p+e_y is positive, and is increased at the
intersection. The corresponding force coordinate is positive by (11).
This determines the sign of the proportionality without a
circle-touching-neighbor assumption.

Both world first coordinates of (10) are negative. Equation (13)
therefore gives

\[
                                  x<0.
\tag{14}
\]

If B has one physical circle corner, write q'_B=kappa z_B.
The u-coordinate and 0<tau<1 give 0<kappa<1. Its first coordinate
then gives a-b<0, hence a<b. Likewise a unique-circle-corner D
gives c<d. Thus two unique corners would make bd-ac>0, contrary
to (9). At least one tip must have two physical circle corners.

For a two-circle-corner B, exactly one own center coordinate is zero.
If its v-center coordinate were zero, then p dot v=-1/2 and
p dot u=h, so x=ha+b/2>0, contradicting (14). The only possibility
is therefore

\[
       p=-\tfrac12u+h v
           =(-a/2-hb,\ b/2-ha),\qquad \tau>\tfrac12.
\tag{15}
\]

The strict parameter bound follows from q'_B dot u=tau-1/2>0,
using the positive proportionality and (11). Similarly a two-circle
D must satisfy

\[
       p+e_y=-\tfrac12w+h t
           =(-c/2-hd,\ -d/2+hc),\qquad \sigma>\tfrac12.
\tag{16}
\]

These conclusions include both-positive and one-positive-corner masks
on every physical two-circle-corner body.

## 3. Two physical two-circle-corner tips are impossible

Suppose (15)--(16) both hold. Their two coordinate differences give

\[
 a-c=2h(d-b),\qquad h(a+c)-(b+d)/2=1.
\tag{17}
\]

Subtracting the two unit-vector equations and substituting (17) gives

\[
 0=(a-c)(a+c)+(b-d)(b+d)=-2(b-d).
\]

Thus a=c, b=d, and

\[
                              2ha-b=1.
\tag{18}
\]

But (9), tau>1/2, and sigma>1/2 give b<sqrt(2)-1<1/2.
Then a>sqrt(3)/2>5/6 and h>9/10 imply

\[
                         2ha-b>2(9/10)(5/6)-1/2=1,
\]

contradicting (18). The whole two-radial-tip mask is excluded.

## 4. One radial tip and one unique-corner tip are impossible

Reflect vertically and exchange the labels if necessary so that B
has two physical circle corners and D has one. Equations (9) and
the unique-corner conclusion above give

\[
          0<b\le c<1/\sqrt2,
          \qquad a\ge d,
          \qquad \tau>1/2.
\tag{19}
\]

Put

\[
 r=a/2+hb>0,\qquad y_0=1+b/2-ha,
 \qquad V=c+d,\qquad W=d-c>0.
\tag{20}
\]

The actual unique circle corner of D is

\[
                         z_D=(-r-W,\ y_0+V).
\tag{21}
\]

### 4.1. The circle equation forces b>2/15

For fixed a,b,h, consider the squared norm of (21) as a function of
c, with d=sqrt(1-c^2). Subtract R^2 and call the function F(c).
Its derivative is

\[
           F'(c)=2\left[y_0-r-(r+y_0)\frac c d\right]<0.
\tag{22}
\]

Here r-y_0>0 and r+y_0>0. For an elementary check, the inequality
a>=1-b/2 for b<1/sqrt(2) follows by squaring. Therefore

\[
 r-y_0=(h+1/2)a+(h-1/2)b-1
      >(7/5)a+(2/5)b-1
      \ge2/5-3b/10>0.
\]

Also r+y_0>=3/2-h>29/60, using (2).

Since c>=b and F(c)=0, equation (22) gives F(b)>=0. At c=b,
d=a, direct expansion gives

\[
                  F(b)=3-4h+3b-2(h-1)a.
\tag{23}
\]

Consequently

\[
        3b\ge4h-3+2(h-1)a
            >3/5-a/5\ge2/5,
            \qquad b>2/15.
\tag{24}
\]

### 4.2. Concurrence forces sigma d>7/20

The positive collinearity of (13) with (21), compared in the first
coordinate, gives the exact expression

\[
             \sigma d=d^2\frac{rV-y_0W}{r+W}.
\tag{25}
\]

By (19), (24), and h>9/10,

\[
      r>r_*:=d/2+3/25,
      \qquad y_0<y_*:=1+c/2-(9/10)d.
\tag{26}
\]

The expression in (25) decreases as y_0 increases. At y_*>0 it
increases as r increases, because its r derivative has the sign of
W(V+y_*). Thus it is strictly greater than the same expression with
r_*,y_* substituted.

We give the full one-variable estimate for that substituted expression.
After multiplying its positive denominator, the required inequality
is

\[
 d^2(r_*V-y_*W)-(7/20)(r_*+W)=P(c)-dQ(c)>0,
\tag{27}
\]

where exact expansion gives

\[
\begin{split}
 P(c)&=679/500+(147/100)c-(23/10)c^2
                         -(28/25)c^3+(9/10)c^4,\\
 Q(c)&=281/200+(9/10)c-(22/25)c^2-(9/10)c^3\\
     &=(1-c^2)((9/10)c+22/25)+21/40>0.
\end{split}
\tag{28}
\]

Use d=sqrt(1-c^2)<=1-c^2/2. The right side of (27) is bounded
below by

\[
 J(c)+c^4(23/50-9c/20),
 \qquad
 J(c)=-47/1000+(57/100)c-(287/400)c^2+(23/100)c^3.
\tag{29}
\]

Here 2/15<c<1/sqrt(2)<3/4, so the fourth-degree term is positive.
The cubic J is concave throughout [2/15,3/4], because

\[
                     J''(c)=-287/200+(69/50)c\le-2/5.
\]

Its two endpoint values are

\[
                  J(2/15)=11333/675000>0,
                  \qquad J(3/4)=1183/16000>0.
\tag{30}
\]

Concavity bounds J below by the positive chord between those values.
This proves (27) and hence

\[
                              \sigma d>7/20.
\tag{31}
\]

Finally (9), (19), (24), and (31) would give

\[
 \sqrt2\ge1+\tau b+\sigma d
     >1+1/15+7/20=17/12>\sqrt2,
\]

a contradiction. This excludes the entire remaining circle mask.

## 5. Exact scope

The four side-owner feature combinations were exhausted in Section 1.
Sections 2--4 then exhausted the unique/unique, two/two, and mixed
physical circle masks, including unequal and zero individual corner
weights. The announced oblique-tip-owner theorem is complete.

For the opposite-loaded-pair C4-with-leaf branch, the outstanding
owner domain consists of an A-owned contact, a shared-side A contact,
or a tip frame parallel to U (including its varying transmission mean
and its possible parallel pair forces). Freely chosen point normals
must still be removed only by a proved compatible selection theorem;
this manuscript does not choose or change them after a stress is found.
All four unstressed completion squares remain in the parent obligation.

No Lean compilation, CI, numerical pose cover, or optimizer certificate
is used in this proof.
