# The remaining D-leaf diamond hub has only one physical circle corner

**Status: complete hand exclusion of the entire central two-circle-corner
mask; root and separate independent full hand audits passed.** Work in
\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Consider the positive five-body diamond with hubs A,U, tips B,C,
and a radial D leaf L attached to A. Its positive pair edges are
\[
                         AL,\quad AU,\quad AB,\quad AC,\quad UB,\quad UC.
\tag{2}
\]
The tips B,C are loaded by the degree-two triangle obstruction.
The second hub U is loaded by NO_UNLOADED_DIAMOND_HUB.md.

**Theorem.** U cannot have two physical circle corners. This retains
every physical circle mask and weight split on B,C, every individual
zero weight on U's two physical corners, every contact owner and
free point normal, and all shared-side means. No degree-two force
or concurrence statement is applied to U.

The proof first makes all three A reactions horizontal. Its final
wall-pair contradiction is purely geometric, independent of the
force equations of either member of that pair.

## 1. The D articulation and the circle-load direction at U

Rotate the D leaf east and put
\[
 s=1+\sqrt2-R,\qquad r=1-s=R-\sqrt2,\qquad
 A=[-s,r]\times[H-1,H],\qquad0<H<1.
\tag{3}
\]
The leaf force on A has outward direction e_x and acts at (r,0),
by RADIAL_BRIDGE_AND_LEAF_REDUCTION.md. The local D articulation
argument in TRIANGLE_LEAF_CORE_REDUCTION.md, Section3, supplies
the strict range in (3), independently of the rest of that source's
triangle graph: the D leaf's inner vertex cannot also be an A vertex
under the selected nonradial point-normal convention, and its radial
diagonal is not a side normal of the leaf. The application must
therefore lie in the relative interior of A's vertical support side.
Its tangential coordinate0 gives exactly 0<H<1. In particular A
contains the origin in its interior and is physically circle-clear.
Convenient uniform bounds are
\[
             0<s<\frac9{20},\qquad r>\frac{11}{20},\qquad
             h:=\sqrt{R^2-1/4}-1>\frac9{10}.
\tag{4}
\]
For the bound on s use sqrt(2)<57/40; the bound on h follows by
comparing R^2-1/4 with (19/10)^2. The upper radius bound gives s>0.

Suppose U has two physical circle corners z_+,z_-. It is a radial
S unit. Each z_± has positive scalar product with every positive
circle atom of B and C, since U physically touches both tips.
It also has positive scalar product with both of its own circle
corners, whose mutual product is R^2-1/2>0.

Sum the component's force equations and take a scalar product
with z_±. The only other load is the D leaf's positive eastward
resultant. The preceding strict products force
\[
                              (z_+)_x<0,\qquad(z_-)_x<0.
\tag{5}
\]
This argument does not require both individual U corner weights
to be positive: its total load is positive, and each of the two
physical corners has the strict products just used.

The radial direction of U therefore has negative x-component.
Reflect in the horizontal axis if necessary and write
\[
 e=(-c,d),\qquad k=(d,c),\qquad
 c>0,\ d\ge0,\quad c^2+d^2=1,
\]
\[
                           U=[h,h+1]e+[-1/2,1/2]k.
\tag{6}
\]
Since U touches A, the maximum e-projection of A is at least h:
\[
                              sc+Hd\ge h.
\tag{7}
\]
The case d=0 would give s>=h, impossible by (4), so d>0.

## 2. U is entirely above the axis, and A's lower-left corner is too central

Cauchy's inequality in (7) gives
\[
                 s^2+H^2\ge h^2,
                 \qquad H^2>\frac{243}{400}>\frac9{16}.
\tag{8}
\]
Hence H>3/4. The lower-left corner of A has squared norm
\[
                 s^2+(1-H)^2
                    <\frac{81}{400}+\frac1{16}
                     =\frac{53}{200}<r^2.
\tag{9}
\]
Every point of a circle-touching unit has norm at least r=R-sqrt(2),
by the distance to its circle corner. Thus the corner in (9) cannot
belong to B or C.

We claim that every point of U has strictly positive y-coordinate,
or equivalently
\[
                               hd-c/2>0.
\tag{10}
\]
If not, t=d/c satisfies 0<t<=1/(2h). The function
(s+t)/sqrt(1+t^2) increases on that interval, because 1-st>0.
Therefore
\[
                 sc+d\le\frac{2hs+1}{\sqrt{4h^2+1}}<h.
\tag{11}
\]
Here the strict last inequality is exact throughout (4). Indeed,
\[
 \begin{aligned}
 h^2(4h^2+1)-(2hs+1)^2
  &>4h^4+\frac{19}{100}h^2-\frac95h-1\\
  &>0.
 \end{aligned}
\tag{12}
\]
The polynomial on the right is increasing for h>=9/10, since
its derivative is 16h^3+(19/50)h-9/5>0, and its value at9/10
is 1583/10000. Equation (11) contradicts (7), because H<1.
This proves (10), including all physical orientations of radial U.

The maximum x-coordinate of U is
\[
                              -hc+d/2<1/2<r.
\tag{13}
\]
In particular it cannot meet A's right support side.

## 3. The full A-normal cover forces three leftward reactions

Let n_U be the actual outward AU normal from A, retaining its
genuine application mean whenever there is a shared side. By (10),
the contact point has positive y-coordinate. An A support point
for a normal with negative y-component is on its bottom side
y=H-1<0. Therefore
\[
                                (n_U)_y\ge0.
\tag{14}
\]
By (13), n_U cannot have positive x-component either. There are
exactly three geometric alternatives:

- n_U=-e_x, in which case U lies in x<=-s;
- n_U=e_y, in which case U lies in y>=H;
- both components are nonzero, with negative x and positive y,
  and its A application is the upper-left vertex (-s,H).

In the last alternative, the actual supporting half-plane gives
\[
            x\ge-s\text{ for a point of U}\quad\Longrightarrow\quad y\ge H.
\]
Thus all three alternatives imply the common exclusion
\[
                       U\cap\{x>-s,\ y<H\}=\varnothing.
\tag{15}
\]

Now let T be either B or C, and let n_T be its actual outward
normal from A. We exclude every possibility (n_T)_y<0.

If (n_T)_x<0, its A application is the lower-left corner, forbidden
by (9). If (n_T)_x=0, the whole square T lies in y<=H-1<0,
so cannot touch U, which is above the axis. If (n_T)_x>0, its A
application is (r,H-1). The strict support-span lemma from
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, applied to -e_x and e_y,
gives respectively
\[
                              \min_Tx>r-1=-s,
                    \qquad \max_Ty<(H-1)+1=H.
\tag{16}
\]
This places all of T in the region excluded by (15), again preventing
its physical contact with U. These cases exhaust the normal signs,
including side-axis endpoints and every possible variable mean.

Consequently (n_B)_y,(n_C)_y are nonnegative as well. The positive
force balance on the unloaded articulation A, with its horizontal
leaf force, now forces all three y-components to vanish. Hence
n_U=-e_x. A positive horizontal normal from A to B or C would
put that tip in x>=r, disjoint from U by (13). Thus
\[
                              n_U=n_B=n_C=-e_x.
\tag{17}
\]

All three actual A applications lie on its left unit side. Write
their heights as y_U,y_B,y_C and their positive magnitudes as
mu_U,mu_B,mu_C. The leaf has zero origin torque. Equation (17)
therefore gives
\[
                           \mu_Uy_U+\mu_By_B+\mu_Cy_C=0.
\tag{18}
\]
By (10), y_U>0. At least one of y_B,y_C is consequently negative.
Call that tip T and its actual application height y_T. The two
applications lie on one unit side of A, so
\[
                   y_U>0>y_T,\qquad y_U-y_T\le1.
\tag{19}
\]
Both U and T have rightmost support x=-s and physically touch.
We finish by excluding this entire geometric wall configuration.

## 4. A radial upper unit cannot form the required wall pair

The following proof uses only (1), 0<s<=1/2, (19), containment,
and the physical contact of the two units. It uses no force,
moment, concurrence or circle-weight equation on U or T.

The radial upper unit U has a unique rightmost vertex. In (6) put
a=c,b=d. By (17), that vertex is
\[
             p_U=(-s,y_U)=he+k/2,
             \qquad ha-b/2=s,\quad y_U=hb+a/2.
\tag{20}
\]
Thus
\[
                       y_U^2=h^2+1/4-s^2>81/100,
                       \qquad y_U>9/10.
\tag{21}
\]
Its upper and left vertices are both circle corners. Equivalently,
their squared-radius difference gives
\[
                              1+2bs-2ay_U=0.
\tag{22}
\]
Since (19) gives y_U<1 and s>0, equation (22) implies
\[
                                      a>1/2.
\tag{23}
\]

If T were aligned with the wall, set
Y=sqrt(R^2-(s+1)^2)>1. Its negative wall application and its circle
contact would force
\[
                         T=[-s-1,-s]\times[-Y,1-Y].
\]
The alternative interval [Y-1,Y] is wholly positive and cannot
contain y_T<0. This T is entirely below the axis, disjoint from U.

Hence T has a unique rightmost vertex too. Write the two complete
vertex charts as
\[
 \begin{aligned}
 U&=(-s,y_U)+[0,1](-a,b)+[0,1](-b,-a),\\
 T&=(-s,y_T)+[0,1](-c,d)+[0,1](-d,-c),
 \end{aligned}
\tag{24}
\]
where a,b,c,d>0, a^2+b^2=c^2+d^2=1. The a,b in (24) are
those of (20); c,d now denote T's frame components.
Put a=cos(theta), b=sin(theta), c=cos(psi), d=sin(psi), and
Delta=y_U-y_T<=1.

The actual mutual separator from U to T has negative y-component:
its supporting inequalities at their wall points give that sign,
and a horizontal normal cannot separate two positive-width squares
with the same rightmost support. Thus the lower section of U is
at or above the upper section of T at every common horizontal depth,
with equality at a contact. The two section formulas are
\[
 \ell_U(x)=
 \begin{cases}y_U-(a/b)x&x\le b,\\
 y_U-1/a+(b/a)x&x\ge b,
 \end{cases}
\]
\[
 u_T(x)=
 \begin{cases}y_T+(d/c)x&x\le c,\\
 y_T+1/d-(c/d)x&x\ge c.
 \end{cases}
\tag{25}
\]
Both breakpoints lie in the common depth interval.

If b=c, these formulas give Delta=2a, contrary to (23). Suppose
b<c. If theta<=psi, their minimum gap occurs at depth c and
requires
\[
                          \Delta=(1+ad-bc)/a>1.
\]
Otherwise the minimum is at depth b and
\[
                         \Delta=a+bd/c\le1.
\tag{26}
\]
This implies tan(psi)<=tan(theta/2). Together with b<c, which
gives theta+psi<pi/2, it implies
\[
                                      \psi<\pi/6.
\tag{27}
\]
If b>c instead, reflect in the horizontal axis and interchange the
two units. The new upper/lower parameters are (d,c) and (b,a),
and the just-proved smaller-breakpoint case applies. Its lower
angle has sine a, so it gives a<1/2, again contrary to (23).
Therefore (26)--(27) are the complete surviving section alternative.

In this alternative T's left vertex
\[
                            z=(-s-c-d,\ y_T+d-c)
\tag{28}
\]
is strictly farther from the origin than either adjacent vertex.
The two squared-radius differences are
\[
                     1+2ds-2cy_T>0,
               \qquad 1+2cs+2dy_T>1-2d>0.
\tag{29}
\]
Here -1<y_T<0 by (19), and d<1/2 by (27). Its wall vertex is
strictly inside the circle, since s^2+y_T^2<5/4<R^2.
Consequently (28) is its unique physical circle corner.

Write v=-y_T. If v<=1/4, its circle equation and Cauchy's
inequality give
\[
 \begin{aligned}
 R^2&=(s+c+d)^2+(v+c-d)^2\\
    &\le s^2+v^2+2+\sqrt{8s^2+8v^2}\\
    &\le\frac{37}{16}+\sqrt{\frac52}
       <\frac{39}{10}<\left(\frac{79}{40}\right)^2.
 \end{aligned}
\tag{30}
\]
The strict comparison uses sqrt(5/2)<127/80. Thus v>1/4.
Together with (21), this gives
\[
                               y_U-y_T>9/10+1/4>1,
\]
contrary to (19). This excludes the entire wall pair.

## 5. Scope of the completed mask

Sections1--3 route every physical two-circle-corner U to the
geometric contradiction in Section4. Neither U corner weight was
assumed positive individually. B,C may have one or two physical
circle corners, any permitted weight split, free actual point normals
or shared-side means. The final proof did not borrow their tip force
equations, and in particular did not treat the degree-three U as a
degree-two body.

Combined with NO_UNLOADED_DIAMOND_HUB.md, every surviving D-leaf
hub-attachment diamond has a **loaded second hub U with exactly one
physical circle corner**. Its B,C masks and all four completion
squares remain unrestricted. This is the completed full central
radial mask, not yet the entire D-hub branch or C1.4.b1.

No numerical pose, radius subdivision, secondary minimizer,
post-extraction normal adjustment, Lean compilation or CI is used.
