# The complete two-unique-tip opposite-load C4 attachment is excluded

**Status: complete whole physical-mask hand exclusion; root and separate
independent full hand audits passed.** Work at the common canonical
radius/center-norm minimizer in
\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The entire positive component is
\[
                  H-A-U-C-H,\qquad H-X-Y-H.
\]
Its block loads are exactly A,C. Assume both A,C have one physical
circle corner. The true degree-four H retains the whole X/Y triangle;
each of A,U,C,X,Y has exact degree two. All three completion units,
all unused physical contacts and every actual channel mean remain.

**Theorem.** This entire two-unique physical mask is impossible in one
compatible selected certificate at the canonical minimizer. Neither
the mixed unique/radial mask nor the whole AC orbit is claimed closed.

## 1. The full canonical physical domain

TRIANGLE_C4_OPPOSITE_LOAD_CANONICAL_CONTACT.md gives a real HU
contact, H oblique to U, and singleton HA and HC contacts. Normalize
the channel as
\[
 \begin{split}
 U&=[X_0-1,X_0]\times[Y_0,Y_0+1],\\
 P&=(X_0,y_0),\qquad Y_0<y_0<Y_0+1,\\
 v&=(a,b),\quad w=(b,-a),\quad a,b>0, a^2+b^2=1,\\
 H&=P+[0,1]v+[0,1]w.
 \end{split}
\tag{2}
\]
The two channel applications are p=(x,Y_0), p+e_y=(x,Y_0+1),
with x<=X_0 and the same positive magnitude gamma. They remain their
actual means. A is below Y_0 and C above Y_0+1.

P cannot belong to A or C. More generally neither channel application
can belong to H: a point of H at first coordinate <=X_0 would have
to be P, whose height is strictly inside the channel. Thus the two
applications on either loaded tip are distinct, even at every mean
endpoint.

An H-owned lower contact is on its -v side, and an H-owned upper
contact on its -w side. These are the complete negative-x owner
possibilities, using the physical HUA/HUC triangles and their heights.
Every owned singleton is in the relative interior of its owner's side.

## 2. Every free interface at an oblique unique tip is removable

If A is oblique to U, its AU contact is its fixed top vertex p.
Its other application at a free HA contact is a distinct vertex.
GENERAL_FIXED_TIP_NORMAL_SELECTION.md applies to this genuine
degree-two, unique-physical-corner body with two fixed applications.
It simultaneously removes the free normal. The coincident radial-D
exception is absent by Section 1. The same statement holds for C.

No boundary-neighbor premise, equation at H, or circle-force ratio
between different loaded bodies is used here.

## 3. One parallel unique tip: an actual shared-block virtual motion

Suppose A is parallel to U and HA is free. Its application is A's
upper-right vertex Q_A and H's lower vertex P+w. Hence
\[
                       (Q_A)_x=X_0+b>x.
\tag{3}
\]
Indeed A's top side contains the actual AU mean at x<=X_0, whereas
H has no point of first coordinate <=X_0 at height Y_0. A's upper-left
vertex cannot be the application. The free normal out of H has both
coordinates strictly negative. Therefore A's true circle force has
both coordinates negative, and its unique circle corner is
\[
                         z_A=Q_A-e_x-e_y,
                         \qquad (z_A)_x<0.
\tag{4}
\]

First suppose C is oblique to U. Its UC application p+e_y is a fixed
physical vertex, so x is fixed by the pose. Give A and U the same
infinitesimal rigid motion
\[
              V(r)=t+\omega Jr,\qquad
              t=xJz_A,\quad\omega=-(z_A)_x.
\tag{5}
\]
The unique A circle row has zero work, since z_A.t=0. Every AU
contact row has zero relative work because both units have the same
motion, regardless of its actual mean. The external UC vertical row
has zero work because
\[
                         t_y+\omega x=0.
\]
The velocity at Q_A is
\[
                    W=J\bigl(xz_A-(z_A)_xQ_A\bigr)\ne0.
\tag{6}
\]
Its nonvanishing follows from (3): the first coordinate inside J is
(z_A)_x(x-(Q_A)_x), which is nonzero. Summing the genuine A and U
wrench equations against (5), all terms except the HA row vanish.
Any positive HA edge would require n_A.W=0. At its free point contact
this excludes a nonzero linear condition on the strict normal interval.
It can be avoided before extraction, without freezing the shared AU mean.

## 4. Two parallel unique tips: the remaining free normal is also removable

Continue with A parallel to U and HA free, and now suppose C is
parallel to U as well. If HC were also free, its application would be
H's upper vertex P+v at height Y_0+1. The two applications would have
vertical difference a+b>1, although their actual heights differ by
exactly one. This is impossible.

Nor can C own HC. A leftward horizontal normal exposes P, below C;
a rightward normal would put C beyond H's right support, preventing
its U contact; a downward normal has the wrong owner sign. The only
remaining C axis is upward vertical. Both forces into C would then
be upward, so its unique circle corner would have horizontal coordinate
zero. An aligned unit cannot have such a unique farthest corner.
Thus HC is H-owned, with normal -w and application
\[
                   Q_C=P+\tau v,\qquad 0<\tau<1.
\]
Its force equation makes the unique circle corner
\[
                         z_C=Q_C-e_x+e_y,
                         \qquad (z_C)_x<0.
\tag{7}
\]

Because Q_A=P+w has height Y_0, we have y_0=Y_0+a. The upper
contact height gives
\[
              \tau=\frac{1-a}{b},\qquad
              (Q_C)_x-(Q_A)_x=\tau a-b=-\tau<0.
\tag{8}
\]
Write (z_A)_x=-s, s>0. Then (z_C)_x=-s-tau, and equality of their
circle radii gives
\[
         s^2+(Y_0-1)^2=(s+\tau)^2+(Y_0+2)^2,
         \qquad 6Y_0+3=-2s\tau-\tau^2<0.
\tag{9}
\]
In particular Y_0<-1/2. The vectors Q_A and z_A are not parallel.
Otherwise (4) would force both negative coordinates of z_A to equal
-R/sqrt(2), so Y_0=1-R/sqrt(2)>-1/2, since R<3/sqrt(2).

There is a two-parameter virtual-motion family for A,U,C which
retains the whole unknown means. Give all three the same angular
velocity omega, and give them constant translational velocities
\[
 \begin{split}
 t_A&=\left(-\frac{(z_A)_y}{(z_A)_x}t,\ t\right),\\
 t_C&=\left(-\frac{(z_C)_y}{(z_C)_x}t,\ t\right),\\
 t_U&=(0,t).
 \end{split}
\tag{10}
\]
Both unique circle rows have zero work. Every AU and UC vertical
contact row has zero relative work: the vertical translations agree
and the angular velocities agree. The fixed HC row imposes only
the homogeneous linear relation
\[
                  (-w)\cdot(t_C+\omega JQ_C)=0.
\tag{11}
\]
Choose a nonzero (t,omega) in its kernel. The velocity
\[
                        W_A=t_A+\omega JQ_A
\tag{12}
\]
is nonzero: the map in (12) is invertible precisely because Q_A and
z_A are not parallel. Thus all actual wrenches except HA have zero
work, and positive HA would again require the nontrivial equation
n_A.W_A=0. Its free normal can be selected away independently of
every actual AU and UC application mean.

The reflected arguments cover a free HC. Sections 2--4 exhaust all
parallel/oblique frames of both unique tips. Thus every root interface
has an actual side owner in one compatible selected certificate.

## 5. The full owner cover uses no leaf equation

The geometric and force calculations of FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md,
Sections 2--3 and the tip-owned part of Section 5, now apply with their
exact actual premises. For precision their dependency and outcome are:

* If H owns HA, its normal is -v. The true unique A force and torque
  imply a>=b; equality requires A parallel to U and the actual AU
  mean at its upper-left corner. The oblique case has a>b. This
  proof uses only Y_0<=R-2, the channel, singleton geometry and the
  unique A corner, all established here.
* If H owns HC, reflection gives b>=a, with the reflected equality
  condition.
* If H owns HA and C owns HC, C cannot be parallel to U by the
  complete axis check in Section 4. Its surviving near-side contact
  forces bc-ad>=0 in the notation of that source, while its unique
  circle and proper concurrence force c<d. Together with a>=b these
  contradict each other. The other mixed owner order is its reflection.
* If both A,C own their root contacts, neither can be parallel to U
  by the same complete axis check. FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md
  then excludes them. That theorem explicitly has no leaf or force
  equation premise at its unit bypass.

These imported parts use no radial-leaf position or direction. Only
the last two-H-owned endpoint in the old source used a leaf; we
replace that step below by the actual whole end-triangle pressure.

## 6. The exact two-H-owned endpoint contradicts the whole triangle

Both H-owned contacts force a=b=1/sqrt(2). Both tips are parallel
to U, and their channel means are respectively their upper-left and
lower-left corners. Their horizontal intervals are identical. The
exact geometry and circle equality, as derived in the old source's
Section 4 before any leaf use, give
\[
 \begin{split}
 m&=\sqrt{R^2-9/4}>5/4,\\
 P&=(1/2-m,0),\\
 z_A&=(-m,-3/2),\qquad z_C=(-m,3/2),\\
 c_H&=(1/2-m+1/\sqrt2,0).
 \end{split}
\tag{13}
\]
The two genuine force equations give
\[
                 \gamma=k_A(3/2-m)=k_C(3/2-m).
\]
Since m<3/2, k_A=k_C=k>0. Hence
\[
                 F_A+F_C=(-2km,0),\qquad
                 M=F_X+F_Y=(2km,0).
\tag{14}
\]
But
\[
                 (c_H)_x<\frac12-\frac54+\frac1{\sqrt2}<0,
\]
contrary to c_H.M>0 for the genuine whole end triangle. No leaf has
been inserted, no triangle force has been omitted and H was never
treated as degree two.

## 7. One preselection and the exact whole-mask conclusion

At the fixed canonical packing prelist every physical assignment,
transmitter axis and unique physical A/C corner. In Sections 2--4
all bad factors depend only on those physical data, fixed actual
side axes and the relevant open strict point-normal parameter.
The nonzero virtual-motion coefficients have been proved on their
whole domains, including all mean endpoints. The fixed other contact
in Section 4 is an H side axis, so it carries no second free variable.
Both-free parallel-tip cases are already geometrically impossible.

Impose these finite exclusions with the earlier generic and matched
four-junction selections before the physical multiplier theorem.
Uncrossing preserves surviving point normals and adds only actual
shared-side forces; root shared interfaces were excluded by the full
canonical geometry, while all channel means were retained throughout.
Thinning only deletes atoms. Every possible final candidate was
prelisted, so no later candidate escapes this proof.

All free normals, side owners, parallel endpoints and genuine means
of the complete unique/unique AC mask are now exhausted. The conclusion
has the canonical radius-lower-bound scope stated at the start and
keeps all three arbitrary extras. The remaining mixed physical mask
and the full C2.34.b0 cell remain separate. No Lean compilation, CI or
numerical premise is used.
