# A selected positive C7 cannot have two free vertex edges

**Status: complete exclusion of the two-free-edge branch; independent full
hand audit passed.** In the remaining radius window

\[
                  \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16},
 \tag{1}
\]

a selected positive C7 satisfying the simultaneous normal choices in
`C7_PINNED_VERTEX_CONTACT_TYPES.md` cannot have two free vertex/vertex
edges. The proof retains both possible owners of the remaining point
contacts, arbitrary square orientations, every shared-side application
mean, and zero circle multipliers at the remaining bodies.

The block graph theorem leaves precisely the layouts with pinned block
lengths \(2,2,3\), or pinned block lengths \(2,2,2\) plus a unique-circle-
corner singleton. Both are excluded here. Consequently the remaining
C7 proof under these choices has at most one free vertex edge. The
companion radial- and mirror-vertex-edge selection theorems subsequently
exclude both one-free-edge types. The all-owned capacity problem remains
open; this manuscript supplies a separate complete geometric/stress
exclusion of the entire two-free-edge branch.

## 1. Notation and the complete two-edge layouts

Retain

\[
 q=R^2,\quad c=\sqrt{q-9/4},\quad
 a_0=\sqrt{q-1/4},\quad d=a_0-1,\quad
 b=\sqrt{4c-7/4},
\]

\[
 \eta=\arctan\frac1{2d},\quad \gamma=2\eta,\quad
 \phi=\arctan\frac{3}{2(c-1)},\quad L=\sqrt{d^2+1/4}.
 \tag{2}
\]

Useful bounds from the pinned-profile theorem are

\[
 \sqrt2\le c\le23/16,\qquad 1\le d<61/60,
 \qquad 39/20<b\le2,
\]

\[
                 \frac{\sqrt5}{2}\le L<\frac{17}{15}.
 \tag{3}
\]

For the upper d bound, \(a_0^2\le1041/256<(121/60)^2\), with exact
positive difference \(31/57600\). Then
\(L^2<4621/3600<4624/3600=(17/15)^2\).

Normalize the radial endpoint of the middle length-two block to have
center angle zero. Its unique-corner end meets the unique-corner end
of another length-two block at the free UU edge. The latter block's
radial endpoint therefore has angle \(2\phi\), by the exact mirror
module. The middle block's other free edge is the RR edge to the third
pinned block, whose radial endpoint has angle \(-\gamma\).

The third block extends backward from that last radial endpoint.
If its length is three, it ends at the reflected length-three profile.
If its length is two, its unique-corner end is followed backward by
the one additional singleton on the remaining owned path. This is the
exhaustive arrangement proved in
`C7_PINNED_VERTEX_CONTACT_TYPES.md`, Section 7.

## 2. The layout with block lengths 2,2,3 is geometrically impossible

The center of the length-three profile has angle

\[
 \theta_3=\frac\pi2+
    \arctan\frac{3/2-c}{b-1/2}.
\]

Thus the closing point contact in this layout would join the radial
center at angle \(2\phi\) to the far length-three center at angle
\(2\pi-\gamma-\theta_3\). Their positive gap is

\[
                     \Delta=2\pi-2\phi-\gamma-\theta_3.
 \tag{4}
\]

We have \(\phi<5\pi/12\). Indeed

\[
 c-1\ge\sqrt2-1>\frac32(2-\sqrt3),
\]

so \(\tan\phi<2+\sqrt3=\tan(5\pi/12)\). The strict intermediate
comparison follows, for example, from
\(\sqrt2>141/100\) and \(\sqrt3>173/100\).

Also

\[
 \theta_3<\frac\pi2+\arctan(1/10),\qquad
 \gamma\le2\arctan(1/2).
\]

The two added angles have tangent

\[
 \tan\bigl(2\arctan(1/2)+\arctan(1/10)\bigr)
                  =\frac{43}{26}<\sqrt3,
\]

and their sum is less than \(\pi/2\). Hence
\(\gamma+\theta_3<5\pi/6\). Together these bounds give
\(\Delta>\pi/3\). Conversely \(2\phi>\pi/2\),
\(\theta_3>\pi/2\), and \(\gamma>0\), so \(\Delta<\pi\).

Both closing centers have radius greater than \(\sqrt2\). The radial
one has radius \(a_0-1/2\ge3/2\). The other has squared radius

\[
 (c-3/2)^2+(b-1/2)^2=q+c-b-3/2
             >\frac{43}{20}>2.
\]

For their radii r and s, therefore,

\[
 |C-C'|^2=(r-s)^2+2rs(1-\cos\Delta)>rs>2.
\]

But touching unit-square centers have distance at most \(\sqrt2\).
This excludes the entire 2,2,3 layout without using a choice of
closing owner or a circle-load split.

## 3. A loaded radial endpoint has a fixed external vertex

We need a simple consequence of the pinned radial endpoint in the
remaining layout. Suppose

\[
 S=[d,d+1]\times[-1/2,1/2]
\]

has a positive shared-side force on its backward tangential face
\(y=-1/2\), and carries positive circle load. Its other positive
circle-touching contact must be at the forward inner vertex
\((d,1/2)\).

The outer radial face is impossible by the width bound, the inner
radial face by the shallow-contact lemma, and the outer circle
vertices cannot be shared. A second contact on the backward face or
at its inner vertex has the same strict origin-moment sign as the
shared-side force, so it cannot balance torque. A contact in the
relative interior of the forward face has the opposite tangential
normal, but both contact forces then have zero radial component.
Translation would force both circle multipliers to be zero, contrary
to positive load. This leaves only the stated forward inner vertex.
The reflected version holds when the shared side is forward.

This argument applies to the pinned radial endpoint at angle
\(2\phi\), whose two circle weights are both positive. Its contact
with the singleton E is therefore the fixed point

\[
                   p_0=\operatorname{Rot}(2\phi)(d,1/2).
 \tag{5}
\]

## 4. Both owners give the same segment for the other singleton contact

Work now in the radial frame of the third pinned block, whose angle
is \(-\gamma\). Its length-two unique-corner body B is the reflected
profile

\[
            B=[c-1,c]\times[-3/2,-1/2],
 \qquad z_B=(c,-3/2).
 \tag{6}
\]

Its shared-side application with its radial endpoint is
\((x,-1/2)\), with \(d\le x\le c\). Its other contact is with E.
The two-free-edge arrangement leaves that link owned and point-only.
We consider both genuine owners.

If E owns the contact, B supplies a vertex. Its circle corner cannot
be shared, its upper right vertex belongs to the incoming shared
segment and would give a three-boundary-body junction, and its upper
left vertex has norm below \(1/\sqrt2\), forbidden by the universal
contact-radius lemma. Hence the contact is exactly
\((c-1,-3/2)\).

If B owns the contact, its bottom face and right face cannot have a
unit neighbor in the disk: their outward support values are \(3/2\)
and c, respectively, both greater than \(R-1\). Its upper face
would have the same tangential normal as its shared-side force and
cannot balance the body. Thus the contact is on its left face, at
\((c-1,-t)\).

B's two contact normals are now \(e_y\) and \(-e_x\). Its unique
circle corner is \((c,-3/2)\). Translation forces a positive circle
load, and origin torque gives

\[
                           t=\frac{3x}{2c}.
\]

In either owner case, E therefore contains a point of the form

\[
                     p_1=(h,-t),\quad h=c-1,
 \qquad \frac{24}{23}\le t\le\frac32.
 \tag{7}
\]

For the lower endpoint use \(x\ge d\ge1\) and \(c\le23/16\).
The case E owns the contact is the allowed endpoint \(t=3/2\).
Every shared-side mean has been retained in this interval.

## 5. Uniform bounds for the first contact in this frame

In the frame of (6), equation (5) becomes

\[
             p_0=\operatorname{Rot}(2\phi+\gamma)(d,1/2)
                 =L e_\theta,
 \qquad       \theta=2\phi+3\eta.
 \tag{8}
\]

We establish the deliberately loose but uniform bounds

\[
              p_0=(-B_0,-A_0),\qquad
              0<A_0<\frac9{10},
\]

\[
              B_0+h>\frac{11}{10},
 \qquad       |B_0-h|<\frac{11}{25}.
 \tag{9}
\]

First, \(\theta>5\pi/4\). From (3),

\[
 \tan\phi\ge24/7,\qquad \tan\eta>30/61.
\]

For \(\delta=\phi+\eta-\pi/2\), the tangent addition formula gives

\[
             \tan\delta>\frac{293}{1674}>\frac16.
\]

Both \(\phi+\eta\) and \(\delta\) lie in their indicated positive
angle ranges. Therefore

\[
 \theta>\pi+2\arctan(1/6)+\arctan(30/61)>\frac{5\pi}{4},
\]

where the latter sum of three acute arctangents has tangent
\(1782/1775>1\) and is less than \(\pi/2\).

Both \(\phi\) and \(\eta\) decrease with R. Thus
\(\theta\le\theta_0\), its value at \(R=\sqrt{17}/2\). At that
endpoint \(c=\sqrt2\), \(d=1\). Direct angle addition gives

\[
 \sin\theta_0=
   \frac{9-64\sqrt2}{5\sqrt5(21-8\sqrt2)},
 \qquad
 \cos\theta_0=
   \frac{138-148\sqrt2}{5\sqrt5(21-8\sqrt2)}.
 \tag{10}
\]

In particular \(5\pi/4<\theta\le\theta_0<3\pi/2\).
The estimates \(\sqrt2<10/7\), \(\sqrt5>11/5\) give

\[
              -\sin\theta_0<\frac{577}{737}<\frac{79}{100}.
\]

Hence

\[
 A_0=-L\sin\theta
       <\frac{17}{15}\frac{79}{100}
       =\frac{1343}{1500}<\frac9{10}.
\]

For the other component, \(\sqrt2>7/5\) and \(\sqrt5<9/4\) give

\[
            -\cos\theta_0>\frac{1384}{2205}>\frac58.
\]

Consequently

\[
 B_0=-L\cos\theta
       >\frac{\sqrt5}{2}\frac58>\frac{11}{16}.
\]

Since \(h\ge\sqrt2-1>33/80\), this proves
\(B_0+h>11/10\). On the other hand,
\(\theta>5\pi/4\) implies

\[
 B_0<\frac{17}{15\sqrt2}<\frac{17}{21}.
\]

We have \(B_0>h\), since \(h\le7/16<11/16\), and

\[
 B_0-h<\frac{17}{21}-\frac25
        =\frac{43}{105}<\frac{11}{25}.
\]

This completes (9).

## 6. Two points more than one apart tightly constrain a unit-square center

Let a unit square contain two points p and q at distance
\(1\le\ell\le\sqrt2\), and let m be their midpoint. Its center C
satisfies

\[
                 |C-m|\le\frac{1-\sqrt{\ell^2-1}}2.
 \tag{11}
\]

Indeed, in the square's side frame let the absolute components of
q-p be s,t. Then \(0\le s,t\le1\), \(s^2+t^2=\ell^2\), and

\[
 |(C-m)_1|\le(1-s)/2,\qquad
 |(C-m)_2|\le(1-t)/2.
\]

The inequality \((1-s^2)(1-t^2)\ge0\) gives
\(st\ge\sqrt{\ell^2-1}\), and hence
\(s+t\ge1+\sqrt{\ell^2-1}\). Therefore

\[
 |C-m|^2\le\frac{(1-s)^2+(1-t)^2}{4}
       \le\frac{(1-\sqrt{\ell^2-1})^2}{4},
\]

proving (11). If \(\ell>\sqrt2\), no unit square contains both
points, which is already a contradiction.

## 7. The remaining singleton is strictly circle-clear

Apply (11) to the required points (7)--(9) in E. Their distance
\(\ell\) and midpoint m obey

\[
 \ell^2=(B_0+h)^2+(t-A_0)^2
       >\frac{121}{100}+(t-9/10)^2>1,
\]

\[
 |m|<\sqrt{\frac{121}{2500}+\frac{(t+9/10)^2}{4}}.
\]

Every corner z of E is at distance \(1/\sqrt2\) from its center.
If E contains both points, equations (11) and these bounds give

\[
 |z|<F(t):=
 \sqrt{\frac{121}{2500}+\frac{(t+9/10)^2}{4}}
 +\frac1{\sqrt2}+\frac12
 -\frac12\sqrt{\frac{21}{100}+(t-9/10)^2}.
 \tag{12}
\]

This function increases on \([1,3/2]\). The derivative of its first
square-root term is greater than \(2/5\) throughout this interval.
The derivative of the subtracted last term is at most
\(3/\sqrt{57}<2/5\), the last comparison being \(225<228\).
Thus \(F'(t)>0\).

At the upper endpoint,

\[
 F(3/2)=\frac{61}{50}+\frac12+\frac1{\sqrt2}
                  -\frac{\sqrt{57}}{20}
       <\frac{411}{200}<\frac{\sqrt{17}}2\le R.
 \tag{13}
\]

The first inequality uses \(1/\sqrt2<71/100\) and
\(\sqrt{57}>15/2\); the final strict comparison is obtained by
squaring. Therefore every corner of E lies strictly inside the
containing circle. This contradicts E's required physical circle
contact, even if its circle multiplier in the selected stress were
zero.

The entire 2,2,2-plus-singleton layout is excluded, with both contact
owners included. Together with Section 2, this proves that a selected
positive C7 has at most one free vertex edge after the stated choices.
\(\square\)
