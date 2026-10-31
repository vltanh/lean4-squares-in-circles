# Two original radial-incident shared means in the strict-turn C6 family

Date: October 26, 2026.

**Status: complete analytic physical-subfamily proof, accepted after root
and separate independent saved-source and physical-scope reviews.** See
REVIEW_C6_RADIAL_MEAN_FAMILIES_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_TWO_SHARED_MEANS_CERTIFICATE_REDUCTION_2026_10_26.md.
The separate scalar derivative inequality
has passed the independent review
[REVIEW_C6_RADIAL_TWO_MEAN_DERIVATIVE_C6_2026_10_26.md](REVIEW_C6_RADIAL_TWO_MEAN_DERIVATIVE_C6_2026_10_26.md).
This source introduces no coefficient packet or sampled sign premise.

Work in the original radius window

\[
 K_0:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad d=\sqrt{R^2-\frac14}-1.
\tag{1}
\]

The entire positive component is an alternating C6 with one physically
two-circle-corner loaded square S, two physically unique loaded squares
B,C, and three true unloaded degree-two side-normal transmitters. Keep
both original radial corner weights, all original contact means, all
three transmitter sliders, and the three remaining physical squares.

The additional premises are:

1. Both S-incident interfaces on B,C are genuinely shared sides.
2. Both unique-loaded turns satisfy \(\theta_B,\theta_C>\pi/2\).

There is no restriction to a midpoint or a side-interior mean. Every
original endpoint mean is included. The radial turn is automatically
at least \(\pi/2\); its equality case is included as well.

**Theorem.** Every core under these premises belongs to the complete
right-turn family of
[SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md).
Consequently

\[
 \theta_S=\pi/2,\qquad R^2=\frac52+\sqrt2,
\tag{2}
\]

and the full three-slider completion theorem excludes three additional
unit squares. In particular the entire subfamily with all three turns
strictly greater than \(\pi/2\) and both original S-incident interfaces
shared is already impossible as a six-body core.

The second premise is stated explicitly. At the end of this source
we identify the different lower-turn owner placements which are not
silently included.

## 1. The unchanged physical port chart

The complete local unique-loaded turn theorem in Section 1 of
[SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md](SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md)
gives \(\theta_B,\theta_C\le3\pi/4\), without a diagonal hypothesis.
The turn sum gives \(\theta_S\ge\pi/2\). Its equality case has the
complete classification and completion exclusion cited in Section 8.
It remains to exclude \(\theta_S>\pi/2\).

At each unique load the local strict-turn feature cover puts its two
distinct actual applications on one inner side, with at least one
vertex and at most one genuine share. Since its S-incident interface
is shared, its other application is the opposite-to-circle vertex.
The B-to-C transmitter has no loaded-axis owner at either endpoint.
Both of its original contacts are strict loaded-vertex features.
These are precisely the local conclusions, including the original
mean endpoints, of
[SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md](SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md)
and
[SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md](SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md).
Only their local strict-turn consequences are used, not their separate
all-unique global turn argument.

At S the complete radial support cover gives its two distinct strict
inner vertices. They are a unit distance apart and both have squared
norm

\[
                         r_0^2=d^2+\frac14.
\tag{3}
\]

This follows from the actual radial square and does not require its
concurrence to belong to the square or the disk.

Normalize the actual B-to-C channel horizontally, with its outward
side above the origin. Its two unchanged applications are

\[
 T_B=(l,H),\qquad T_C=(l+1,H),\qquad H>0.
\tag{4}
\]

The common positive moment and the actual force-polygon theorem give
this positive height. The unique concurrences \(q_B,q_C\) lie on
the same line, are positive multiples of their actual circle corners,
and have radial factors at most one.

At the left endpoint write the inward unit sides from the opposite
vertex as

\[
                 v=(-c,s),\qquad u=(-s,-c),\qquad
          c=\cos\eta>0,\quad s=\sin\eta>0.
\tag{5}
\]

The strict rightward opposite-vertex normal gives the negative
horizontal components of both sides. Proper radial concurrence gives
the circle-corner height at least H, hence \(s\ge c\). Thus

\[
                         \frac\pi4\le\eta<\frac\pi2.
\tag{6}
\]

The S-incident shared side has normal toward B equal to v, and its
tangent from \(T_B\) is u. Indeed the third concurrence is below
the line of (4), so the direction from S toward B has positive
vertical component. Of the two possible inward side axes in (5),
only v has this component.

Put

\[
 D=s-c,\quad C=s+c,\quad Z=H+D,\quad
 A=\sqrt{R^2-Z^2}>0.
\tag{7}
\]

The actual endpoint-center theorem fixes the left sign of the circle
corner; it is farther left than the center and therefore is

\[
                    z_B=(-A,Z),\qquad T_B=(-A+C,H).
\tag{8}
\]

The reflected right endpoint has the identical chart with its own
angle \(\eta_C\). The original reserve-one relation (4) is exactly

\[
                         A_B+A_C=1+C_B+C_C.
\tag{9}
\]

## 2. The true mean and its radial port norm

Define the actual positive own-axis corner coordinates

\[
                 a=cA+sZ,\qquad b=sA-cZ.
\tag{10}
\]

Physical uniqueness gives \(a,b>1/2\), and \(a^2+b^2=R^2\).
Since the concurrence has height H,

\[
       t=\frac D Z\in[0,1),\qquad q_B=(1-t)z_B.
\tag{11}
\]

Write the original shared mean as

\[
                  Q=T_B+\ell u,\qquad 0<\ell\le1.
\tag{12}
\]

The strict lower endpoint in (12) follows from the unchanged
distinct-port theorem; the upper endpoint is retained. Equality of
the u coordinates along the actual v-normal gives

\[
                     \ell=1-tb.
\tag{13}
\]

Set

\[
                            \lambda=C-tA.
\tag{14}
\]

Direct use of \(tZ=D\) in (10) gives the identities

\[
            \ell=s\lambda,\qquad 1-ta=c\lambda,\qquad
                         a-b=Z\lambda.
\tag{15}
\]

Because \(\ell>0\), we have \(\lambda>0\), \(a>b>1/2\), and
the proper distance from Q to \(q_B\) is \(1-ta>0\).
All these strict signs are consequences of the original mean, not
new selections of a normal or an endpoint.

The true reserve-one S-incident transmitter fixes S's actual port
as \(P=Q-v\). In the orthonormal basis \(v,u\) this is

\[
                       P=(a-2)v+(1-t)b\,u.
\tag{16}
\]

Consequently its squared norm is the single-variable function

\[
                F_M(\eta)=(a-2)^2+(1-t)^2b^2.
\tag{17}
\]

At each actual endpoint of the B-to-C channel it satisfies

\[
                              F_M=r_0^2.
\tag{18}
\]

No slider enters (16): the transmitter's actual reserve and its true
mean already fix its two force applications. Its full transverse
slider and physical square remain unchanged.

## 3. Every actual norm root has a uniform angle bound

The original radius window gives

\[
 d<\frac{61}{60},
\tag{19}
\]

because
\[
 \left(\frac{121}{60}\right)^2-\frac{1041}{256}
                        =\frac{31}{57600}>0.
\]

Expanding (17), using \(a^2+b^2=R^2\) and
\(r_0^2=R^2-2d-1\), transforms (18) into

\[
               4a+\{1-(1-t)^2\}b^2=5+2d.
\tag{20}
\]

The coefficient in braces is nonnegative. Thus every actual norm root
satisfies

\[
       a\le\frac{5+2d}{4}<\frac{211}{120}.
\tag{21}
\]

It follows that

\[
 b^2-\frac{a^2}{4}
   =R^2-\frac54a^2
   >\left(\frac{79}{40}\right)^2
       -\frac54\left(\frac{211}{120}\right)^2
   =\frac{2071}{57600}>0.
\tag{22}
\]

In particular \(b>a/2\). Also \(a>b\) gives
\(a>R/\sqrt2>4/3\); the last comparison follows by squaring,
since \(K_0^2-32/9=4969/14400>0\).

We claim that every actual root obeys

\[
                              \eta<\frac\pi3.
\tag{23}
\]

Suppose instead \(\eta\ge\pi/3\). With \(u_0=c/s\), we then
have \(u_0\le1/\sqrt3<7/12\). Equations (10) and (22) give
\(Z=sa-cb<a(s-c/2)\). The function
\((1-u_0)/(1-u_0/2)\) decreases in \(u_0\), so

\[
 t=\frac{s-c}{Z}
  >\frac{s-c}{a(s-c/2)}
  >\frac{k}{a},\qquad k:=\frac{10}{17}.
\tag{24}
\]

Here \(a>4/3>k\), and \(0\le1-t<1-k/a\). Hence

\[
 F_M<f(a):=(a-2)^2+(1-k/a)^2(R^2-a^2).
\tag{25}
\]

On \(a\ge R/\sqrt2\),

\[
 f'(a)=2k-4+\frac{2kR^2}{a^2}(1-k/a)
                       <6k-4=-\frac8{17}<0.
\tag{26}
\]

Therefore

\[
 \begin{split}
 F_M-r_0^2
 &<f(R/\sqrt2)-r_0^2\\
 &=2\sqrt{R^2-\tfrac14}
        -\sqrt2(2+k)R+3+k^2.
 \end{split}
\tag{27}
\]

The square-root bound
\(\sqrt{R^2-1/4}<R-1/(8R)\), and \(\sqrt2>140/99\), bound
the last expression above by

\[
 \left(2-\frac{140}{99}\frac{44}{17}\right)R
       -\frac1{4R}+3+\frac{100}{289}.
\tag{28}
\]

This function decreases for \(R\ge K_0\): its linear coefficient
is less than \(-3/2\), whereas \(1/(4R^2)<1/4\).
At \(R=K_0\), its exact value is

\[
 \left(2-\frac{140}{99}\frac{44}{17}\right)\frac{79}{40}
 -\frac{10}{79}+3+\frac{100}{289}
                  =-\frac{243779}{4109580}<0.
\tag{29}
\]

This contradicts (18), proving (23) over the whole physical root
domain. It does not depend on any force magnitude.

## 4. The full interval between the two original endpoint angles

Fix the actual R,H. Interpolate only the scalar angle between
\(\eta_B\) and \(\eta_C\); no interpolated packing is asserted or
needed. All the inequalities needed for the derivative proof hold
on this entire connected interval.

Indeed D increases with \(\eta\), so \(0<Z=H+D<R\) persists
between the actual endpoints. The proper inequality \(\lambda>0\)
has the equivalent form

\[
 CZ>DA
 \quad\Longleftrightarrow\quad
 H>D\left(\frac R{\sqrt2}-1\right).
\tag{30}
\]

The squaring in this equivalence has nonnegative sides, and C,Z
are positive. Since \(R>\sqrt2\), the last inequality persists
from the larger endpoint angle throughout the interval. Thus
\(a>b\) persists. Also \(a=cA+sZ>0\) throughout; positivity
of b will follow from its derivative and its actual endpoints.

Direct differentiation yields

\[
 (A-C)'=D-\frac{ZC}{A}<0,\qquad
 a'=-b(1-C/A),\qquad b'=a(1-C/A).
\tag{31}
\]

The strictly decreasing function \(A-C\) changes sign at most
once. Since \(a>0\), the identity for \(b'\) first shows that b
increases and then decreases, with either part possibly empty.
Its minimum is at an actual endpoint, so \(b>1/2\) throughout.
The identity for \(a'\) now shows that a first decreases and then
increases. Its maximum is at an endpoint, so (21) also holds on
the entire interval.
Equation (22) therefore gives \(b>a/2\) everywhere as well.
Finally (23) persists because both endpoint angles satisfy it.

We have proved on the whole connected interval

\[
 a>\frac43,\qquad
 \frac47<\frac cs\le1,\qquad
 \frac12<\frac ba<1.
\tag{32}
\]

For \(c/s>4/7\), use (23) and
\(1/\sqrt3>4/7\), whose squared reserve is \(1/147>0\).

## 5. The actual mean-port norm is strictly decreasing

From (11),

\[
                         t'=\frac{HC}{Z^2}>0.
\tag{33}
\]

Differentiate (17) using (31). The result is

\[
 F_M'=2b\left[
 (1-C/A)\{2-a(2t-t^2)\}-t'(1-t)b
 \right].
\tag{34}
\]

This identity retains the derivative of the original mean
\(\ell=1-tb\). No mean is frozen during the scalar interpolation.

Set \(u_0=c/s\), \(r=b/a\), \(D_0=1-u_0r>0\), and
\(k_0=(1-u_0)/D_0\). Then

\[
 A=as(u_0+r),\quad Z=asD_0,\quad C=s(1+u_0),
 \quad t=k_0/a,\quad
 t'=\frac{(a-k_0)(1+u_0)}{a^2D_0}.
\tag{35}
\]

The bracket in (34) is exactly the scalar expression proved negative
on \(a\ge4/3,\ 4/7\le u_0\le1,\ 1/2\le r<1\) in
[SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md](SIX_CYCLE_RADIAL_TWO_MEAN_DERIVATIVE_ANALYTIC.md).
Every premise of that theorem holds throughout (32). Its proof uses
one completed square and one cubic chord identity on whole intervals,
not angle cells or a finite coefficient certificate.

Since \(b>0\), we conclude

\[
                              F_M'<0
\tag{36}
\]

throughout the whole interval between the actual endpoints.
Their equal actual port norms (18) therefore force

\[
                              \eta_B=\eta_C.
\tag{37}
\]

## 6. Reflection symmetry and the original radial side

Drop endpoint subscripts after (37). Equation (9) gives

\[
                              A=C+\frac12.
\tag{38}
\]

The original radial ports are reflected:

\[
 P_B=(-x,y),\qquad P_C=(x,y),
\]
\[
 x=A-2c-tbs=D+\frac12-tbs,\qquad
 y=H-\ell c-s.
\tag{39}
\]

Since \(tb=1-\ell<1\),
\[
                    x>\frac12-c>-\frac12.
\tag{40}
\]
The true radial inner side has length one. Thus \(2|x|=1\);
the negative solution is excluded by (40), and

\[
                       x=\frac12,\qquad D=tbs.
\tag{41}
\]

If \(D=0\), then \(c=s=1/\sqrt2\), \(t=0\), and \(\ell=1\).
The two actual normals from S are perpendicular, so
\(\theta_S=\pi/2\). This is precisely the endpoint retained in
Section 8.

Suppose instead \(D>0\). Because \(t=D/Z\), equation (41) gives

\[
                        bs=Z,\qquad \ell=c/s.
\tag{42}
\]

The two actual S-outward normals are \((-c,s)\) and \((c,s)\).
With the actual horizontal radial side (39), their strict positive
vertical components place the square below that side. Its two
physical circle corners are on the lower opposite side. Thus the
actual radial frame has \(y=-d\), and (39)--(42) imply

\[
                          H=\frac1s-d.
\tag{43}
\]

This uses the actual physical two-circle-corner mask; it is not a
new assertion about the radial concurrence.

## 7. A single positive circle-identity obstruction

From \(b=sA-cZ\) and \(bs=Z\),

\[
                         Z=\frac{As^2}{1+sc}.
\tag{44}
\]

Put \(u_0=c/s\in(0,1)\), and write

\[
 W=1+u_0+u_0^2,\qquad
 s=\frac1{\sqrt{1+u_0^2}},\qquad
 A=\frac12+s(1+u_0),
\]
\[
                    M=1+s(2-u_0+u_0^2).
\tag{45}
\]

Equations (38), (43), and (44) give

\[
                      Z=A/W,\qquad d+1=M-Z.
\tag{46}
\]

The unique corner and the two radial circle corners have the same
original radius. Consequently

\[
 A^2+Z^2=(d+1)^2+\frac14=(M-Z)^2+\frac14,
\]
or
\[
                E:=W(A^2-M^2-\tfrac14)+2MA=0.
\tag{47}
\]

There is an elementary sign obstruction to this identity. Directly
substitute (45), multiply by \(1+u_0^2>0\), and use
\((\sqrt{1+u_0^2})^2=1+u_0^2\). The result is

\[
\begin{split}
 (1+u_0^2)E={}&2+u_0(5-3u_0)
             +6u_0^3(1-u_0)+u_0^5(1-u_0)\\
 &+(\sqrt{1+u_0^2}-1)
          (1-u_0)(1+u_0^2)(1+2u_0)>0.
\end{split}
\tag{48}
\]

Every term after the constant 2 is nonnegative on \(0\le u_0\le1\).
Thus (48) contradicts (47). The case \(D>0\) is impossible.

Only \(D=0\), and therefore the actual right turn at S, remains.
This establishes the classification without imposing any equation
on the original radial weight split.

## 8. Whole-family completion and precise remaining scope

The accepted
[SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md)
now applies to every core left by Sections 1--7. It fixes the radius
and all three loaded squares, and carries every actual transverse
slider to
[SIX_CYCLE_ONE_RADIAL_RIGHT_ANGLE_FAMILY_COMPLETION.md](SIX_CYCLE_ONE_RADIAL_RIGHT_ANGLE_FAMILY_COMPLETION.md).
That source proves capacity at most two for the remaining physical
squares, on the entire original three-slider domain. Three extras
are required here, so the whole stated subfamily has no nine-square
completion. The original endpoint means \(\ell=1\) have been retained.

For the unrestricted one-radial parent, a genuine S-incident shared
side is always an inner side at its unique neighbor. To see this,
normalize its radial channel as
\[
 P=(d,1/2),\quad g=(-\cos\alpha,\sin\alpha),\quad Q=P+g.
\]
If the shared side were the outer side in the direction \(-g\),
the circle corner's corresponding own-axis coordinate would be
\[
 (-g)\mathbin{\cdot}Q
       =d\cos\alpha-\tfrac12\sin\alpha-1
       \le d-1<\frac1{60}<\frac12,
\]
contrary to physical uniqueness. Reflection gives the other radial
channel. This useful fact does not by itself imply both unique
turns exceed \(\pi/2\).

Without the explicit second premise of this theorem, the local
owner cover still allows a unique load of turn at most \(\pi/2\)
to use its other adjacent-to-circle vertex, or a second side-axis
application, on the B-to-C channel. Its port chart is different
from (8)--(17). These lower-turn placements are retained as separate
obligations and are not excluded by the derivative lemma above.
At most one unique turn can be at most \(\pi/2\), because both
would contradict the strict force-polygon turn sum.

No original unrestricted one-radial gate is closed by this source
alone. No square or positive pair force is deleted, no physical mask
is relabeled, no mean is moved, and no Lean compilation or CI is used.
