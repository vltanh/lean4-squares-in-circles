# One normal-ratio argument excludes every high-radius upper-left triangle contact

**Status: complete hand proof; root and independent full saved-source/direct-prerequisite
review passed on October 25, 2026. See REVIEW_HIGH_RADIUS_2026_10_25.md.
The two existing HIGH upper-left diamond leaves are accepted as closed.
No Lean compilation or CI was run.**

Pinned parent: `87d2684e0e58afbc2b43424a254ab9436a739054`.

This argument covers all physical HK owners together, including a free
vertex junction, a positive-length shared side, zero-stress physical HK,
and every original HK mean. It uses no force equation at H or K. In
particular it does not turn a degree-three K into a degree-two body.
It does not use either parallel-HK return exclusion or its coefficient packet.

Let
\[
 q_0=6241/1600,\qquad Q=1105/256,\qquad q_0\le q=R^2\le Q.
\]
Let H,A,K be the original pairwise interior-disjoint, pairwise physically
touching units. A has exactly two positive pair neighbors H,K, one physical
circle corner z_A, and positive circle weight. K physically touches the
circle, with either physical mask and any original individual weights.
H and K may have arbitrary additional forces. Suppose
\[
 c_H\cdot z_A<0,
\]
HA is an H-owned singleton, and AK is a K-owned upper-left singleton in
the ordered negative-endpoint frame. All other packing bodies remain.

**Theorem.** The actual HA normal satisfies
\[
                         u/v>5/9.                         \tag{T1}
\]
Consequently this entire physical family is impossible when
\[
                         q\ge17/4.                        \tag{T2}
\]
In the high-radius interval the contradiction has the uniform reserve
\[
                 c_H\cdot z_A>7/8-9/\sqrt{106}>0.
\]
There is no return-contact, positive-HK-force, petal, or root-degree premise.

## 1. Original chart and two elementary identities

Section 1 of NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md gives,
before any radial-middle specialization,
\[
 z_A=(a,b),\quad a>b>3/5,\quad a^2+b^2=q,\quad x=a-1,
\]
\[
 P=(x,b-1),\quad T=(x,b),\quad n=(u,v),\quad j=(-v,u),
 \quad 0<u\le v,\quad u^2+v^2=1,
\]
\[
 H=P+[-1,0]n+[-(1-r),r]j,\qquad 0<r<1,
\]
\[
 g=(-c,s),\quad f=(s,c),\quad c,s>0,\quad c^2+s^2=1,
 \qquad K=T+[0,1]g+[-\delta,1-\delta]f,\quad0<\delta<1.
                                                               \tag{1}
\]
The coordinates and offsets are those of the original packing. In
particular delta here is K's geometric side offset, not A's radial
concurrence parameter. Always 0<x<1: a>R/sqrt(2)>1, whereas
\(a^2\le Q-b^2<Q-9/25<4\).

Put
\[
 \rho=u/v,\quad E=su+cv>0,\quad d=sv-cu,\quad E^2+d^2=1,
 \quad L=xs+bc,\quad h=-xc+bs.
\]
In the positively oriented (f,g) coordinates,
\[
 n=(E,d),\quad j=(-d,E),\quad P=(L-c,h-s),
 \quad K=[L-\delta,L+1-\delta]\times[h,h+1].       \tag{2}
\]
The true A2 proper concurrence is the intersection
\(P+(c/E)n=T-(u/E)g\) on A's actual positive radial line.
Taking its determinant with z_A gives
\[
 \frac ab=1+\frac{c(1-\rho)}{s\rho}.              \tag{3}
\]
Thus 0<rho<1. Only A's genuine degree-two equations enter (3).

First, negative pressure forces r>u. Indeed pressure decreases with r,
since \(j\cdot z_A=bu-av<0\). At r=u it equals \(q-aA_0-bB_0\), with
\[
 A_0=1+(u-v)/2+uv,\qquad B_0=1+(u+v)/2-u^2.
\]
The identity
\[
 A_0^2+B_0^2=5/2+u-u^2+2uv\le15/4
\]
and completing two squares imply
\[
 r\le u\quad\Longrightarrow\quad
 c_H\cdot z_A\ge(q-15/4)/2\ge241/3200>0.          \tag{4}
\]
This is incompatible with the actual negative pressure.

Second, at the other end of the full offset interval, r=1, define
\[
 C_1=1+(u+v)/2,\qquad C_2=1+(v-u)/2.
\]
Every original r<1 satisfies
\[
 c_H\cdot z_A\ge q-aC_1-bC_2
 \ge\tfrac12\{q-C_1^2-C_2^2\}
 =\tfrac12(q-5/2-2v).                              \tag{5}
\]
Both comparisons in this section are inequalities on the original
pose; they are not motions of H or changes to a contact mean.

## 2. The only geometric information needed from physical HK

The radius-free UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md says that,
in three pairwise touching interior-disjoint units, two separating
normals at a common unit have nonnegative dot product whenever one
is a side axis of that unit.

Choose an auxiliary side-axis separator M from H to K by the separating-axis
theorem. This describes the physical contact, not a replacement of the
selected HK force. Applying the triangle lemma at H and K gives
\[
                         n\cdot M\ge0,\qquad g\cdot M\ge0. \tag{6}
\]
For d>0 the possible axes are n,j,f,g. For d<0 only j,f remain.
The following direct support calculations exhaust these axes, including
endpoints. Set \(r_0=s/E\) and \(\delta_0=v/E=c+sd/E\).

For d>0, an n separator exposes K's near vertex V=(L-delta,h).
Equal support gives delta=delta0; membership in H's front side gives
r>=r0. A g separator exposes H's front/top vertex U=P+rj; equality gives
r=r0 and membership in K gives delta>=delta0. The j alternative is
impossible: its K support vertex (L+1-delta,h) has relative n-coordinate
v+E(1-delta)>0, whereas H has no positive relative n-coordinate.
The f alternative exposes P+(r-1)j, of g-coordinate h-s+(r-1)E<h,
so that point cannot belong to K. Consequently
\[
                    d>0\quad\Longrightarrow\quad\delta\ge\delta_0.\tag{7}
\]

For d<0, the j alternative gives r=u+d delta<u, contradicting (4).
The f alternative gives delta=c+rd. As r<1 and d<0, it follows that
\[
                    d<0\quad\Longrightarrow\quad\delta\ge c+d.   \tag{8}
\]
For d=0, E=1, n=f, j=g, u=s and v=c. Equation (4) gives r>s.
The g-coordinate intervals of H and K then overlap in the positive-length
interval [h,h+r-s]. Their disjoint interiors and physical contact force
delta=c. Hence (8) also holds at d=0, with the entire original shared
mean interval retained.

Only (7)--(8) will be used. They include every selected HK owner/free/shared
type without assigning any force magnitude, choosing a free normal,
or requiring a positive multiplier at HK.

## 3. Exclude rho<=5/9 when d>0

Assume rho<=5/9. Put
\[
 m=(1-c)/s,\quad c=(1-m^2)/(1+m^2),\quad s=2m/(1+m^2).
\]
By (7) and delta<1,
\[
 c+s\rho>1,\qquad0<m<\rho\le5/9,
\]
\[
 0<\tau:=1-\delta\le1-\delta_0
       =\frac{s(\rho-m)}{c+s\rho}<s(\rho-m).        \tag{9}
\]
Set
\[
 A=\frac ab=1+\frac{(1-\rho)(1-m^2)}{2m\rho},\qquad
 A_*(\rho)=1+\frac{(1-\rho)(1-\rho^2)}{2\rho^2}.
\]
For fixed rho, A decreases with m, so A>=A_*(rho).
Also
\[
 A_*'(\rho)=\frac{(\rho-1)(\rho^2+\rho+2)}{2\rho^3}<0,
 \quad A_*(5/9)=337/225>7/5.
\]
It follows that
\[
 a^2>q_0\frac{49}{74}>(8/5)^2,\quad x>3/5,
 \quad L=xs+bc>3/5>1/2.                            \tag{10}
\]
The second squared reserve is 541/23680. Thus K's maximum absolute
f-coordinate is its positive coordinate F=L+tau, because
L+1/2-delta>L-1/2>0. Every corner satisfies
\[
                   |z|^2\le F^2+\max\{h^2,(h+1)^2\}.            \tag{11}
\]

If h<=-1/2, then -1<h<=-1/2 since h>-x>-1, so the g contribution
in (11) is less than one. Moreover
\[
 \delta_0\ge\frac1{\sqrt{1+\rho^2}}\ge\frac9{\sqrt{106}}>6/7,
 \quad L^2\le|T|^2=q-2a+1<Q-11/5<9/4.
\]
Hence F<3/2+1/7=23/14, and
\[
                       |z|^2<725/196<q_0.                     \tag{12}
\]
The exact last reserve is 15809/78400. K cannot touch the circle.

Now let h>-1/2. Its far g-coordinate is h+1. The two original equations
\(x=a-1\) and \(q=a^2+b^2\) give
\[
 F^2+(h+1)^2-q=2(h-x)+2L\tau+\tau^2.             \tag{13}
\]
Write e=rho-m, so 0<e<1. The following identities are exact:
\[
 h-x=-(1+c)(x-bm),\quad L=b(s+c/\rho)-s,
\]
\[
 1-m(s+c/\rho)=\frac{(1-m^2)(\rho-m)}{\rho(1+m^2)}\ge0.
                                                               \tag{14}
\]
Using (9), s/(1+c)=m, and s^2/(2(1+c))=m^2/(1+m^2), the right
side of (13), divided by 2(1+c), is at most
\[
 -(x-bm)+Lme+\frac{m^2e^2}{1+m^2}.
\]
The negative of this expression has the lower bound
\[
\begin{aligned}
 x-bm-Lme-\frac{m^2e^2}{1+m^2}
 &=b\{A-m-me(s+c/\rho)\}-1
       +sme-\frac{m^2e^2}{1+m^2}\\
 &\ge a-b\rho-1+\frac{m^2e(2-e)}{1+m^2}
 \ge a-b\rho-1.                                  \tag{15}
\end{aligned}
\]

It remains to show a-b rho>1, uniformly. For fixed rho, the function
\((A-\rho)/\sqrt{1+A^2}\) increases with A, its derivative having
numerator 1+A rho>0. Define
\[
 J(\rho)=\frac{A_*^2+1}{(A_*-\rho)^2}
 =\frac{\rho^4+2\rho^3+2\rho^2-2\rho+1}
        {(1-\rho)^2(1+\rho^2)}.
\]
Here A_*-rho>0 and
\[
 J'(\rho)=\frac{4\rho^2(\rho^3+\rho^2-\rho+3)}
                {(1-\rho)^3(1+\rho^2)^2}>0,
 \quad J(5/9)=1549/424<q_0.                       \tag{16}
\]
The exact reserve in (16) is 20973/84800. Therefore
\[
 a-b\rho=\sqrt q\frac{A-\rho}{\sqrt{1+A^2}}
       \ge\sqrt{q/J(\rho)}>1.                    \tag{17}
\]
Equations (13)--(17) put every actual K corner strictly inside its
required circle, a contradiction. The two h alternatives exhaust
all physical far-corner masks, including the tie in (12).

## 4. Exclude rho<=5/9 when d<=0

Now d<=0 implies s<=c rho. From (3),
\[
 \frac ab\ge1+\frac{1-\rho}{\rho^2}\ge61/25.
\]
Since \(Q<(16/25)(1+(61/25)^2)\), this gives b<4/5.
The exact reserve for that comparison is 535591/4000000.
The unit identities and rho<=5/9 also give
\[
 u\le5/\sqrt{106}<1/2,\quad
 v\ge9/\sqrt{106}>13/15,\quad c\ge v>13/15,\quad s\le u<1/2.
                                                               \tag{18}
\]
Thus L>bc>(3/5)(13/15)=13/25>1/2, so once again K's far absolute
f-coordinate is F=L+1-delta>0.
By (8),
\[
\begin{aligned}
 F&\le L+1-c-d\\
  &=1+s(x-v)+c(b+u-1)\\
  &<1+(2/15)s+(3/10)c
  \le1+\sqrt{97}/30<4/3.                         \tag{19}
\end{aligned}
\]
Furthermore -1<h=-xc+bs<bs<2/5, so both |h| and |h+1| are below7/5.
Every corner of K consequently satisfies
\[
                  |z|^2<(4/3)^2+(7/5)^2=841/225<q_0,           \tag{20}
\]
with exact reserve 469/2880. This contradiction includes d=0 and
its full genuinely shared HK interface. It never uses a K2 equation.

Together Sections 3--4 prove (T1) over the entire original radius window.

## 5. One high-radius pressure contradiction for all HK types

By (T1), v<9/sqrt(106). If q>=17/4, (5) gives
\[
 c_H\cdot z_A>\frac12\left(\frac{17}{4}-\frac52-
                                 \frac{18}{\sqrt{106}}\right)
                 =\frac78-\frac9{\sqrt{106}}>0.                \tag{21}
\]
The last sign follows from
\[
                     49/64-81/106=5/3392>0.
\]
This contradicts negative pressure, proving (T2). Both original radius
endpoints, every actual H offset, both K circle masks, every selected
HK normal, and all original shared means remain.

## 6. Dependency and roadmap scope

The only inherited geometric inputs are the original negative-endpoint
chart/proper concurrence and the radius-free triangle side-normal lemma.
The support cover, scalar inequalities, derivative signs, and all exact
reserves are proved above. In particular this result bypasses the earlier
parallel-HK near/side return manuscripts and their outstanding review.

The exact symbolic supplement UNIFORM_TRIANGLE_HIGH_RADIUS_CHECK.py checks
identities and rational endpoint arithmetic only. It contains no pose mesh,
coefficient table, quantifier-elimination result, or geometric proof oracle.

This theorem supplies a full mathematical exit for both existing HIGH
upper-left diamond leaves
`M6.TB4.DIAMOND_HUB.NEGATIVE_OWNER.H_OWNED.UUS.HIGH.AK_K_OWNED` and
`M6.TB4.DIAMOND_HUB.NEGATIVE_OWNER.H_OWNED.UUU.HIGH.AK_K_OWNED`.
Its stronger degree-independent scope is assembled in
HIGH_RADIUS_TRIANGLE_TIP_PRESSURE_AND_DIAMOND_FAMILIES.md.

The LOW leaves remain open. Root and independent review passed the entire
saved proof and its direct prerequisite scopes; the two existing HIGH
checkboxes now close. The exact construction in
LOW_RADIUS_TRIANGLE_TIP_PRESSURE_OBSTRUCTION.md proves that nonnegative
tip pressure on LOW does not follow from these local hypotheses alone.
No Lean compilation or CI was run.
