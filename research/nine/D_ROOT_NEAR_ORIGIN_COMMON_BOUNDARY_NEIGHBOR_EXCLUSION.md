# A D-leaf root and a near-origin unit have no common boundary neighbor

Date: October 26, 2026.

**Status: complete uniform hand candidate, pending independent full review.**
The theorem is a geometric obstruction with arbitrary actual degrees.
It retains the actual D leaf, every physical contact, all support
features and all original bodies. It requires no positive force
equation at any of the three units in the obstruction.

## 1. Statement and accepted inputs

Work in the original true-origin disk, with
\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\qquad
 \epsilon=\max(d-1,0)<1/60.
 \tag{1}
\]
Let L be a genuine radial D leaf and H its actual root in the
common selected physical certificate. Let B be another actual
unit square, distinct from H,L, which meets the closed disk
\(\overline D_\epsilon\).

**Theorem 1.1.** No actual physically circle-touching unit K,
distinct from H,L,B, can physically touch both H and B.

Neither HB nor either of the two displayed K contacts is required
to carry a positive stress. The theorem in particular permits all
original positive degrees and all physical zero-stress contacts.
B need not touch H, need not be loaded and need not be a leaf root.

The direct accepted inputs are:

1. RADIAL_BRIDGE_AND_LEAF_REDUCTION.md: a genuine D leaf fixes the
   actual aligned root chart and contains the origin strictly.
2. CENTERED_INNER_ARC.md: any two physically boundary unit squares
   have minor center-angle separation strictly greater than
   \(2\pi/9\). This is physical circle contact, with no multiplier
   premise.
3. The elementary support-span lemma of
   UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, Section 1. Its short
   proof is recalled in Section 5 below.
4. For applications to a genuine second leaf root, only Lemma 2.1
   of FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md is needed: every genuine
   S or D leaf root meets \(\overline D_\epsilon\), regardless of
   its additional forces and degree.

All four inputs are present at the pinned comparison head
26d9e3042b733ff0796876a4607a7d834f4b630a. No newer force theorem,
quarter-disk completion theorem, canonical secondary minimizer or
computational coefficient packet is used.

## 2. The full near-origin geometry

Rotate the actual D leaf east. Its actual root is
\[
 H=[-s,r]\times[t-1/2,t+1/2],\qquad
 r=R-\sqrt2,\quad s=1-r,\quad |t|<1/2.
 \tag{2}
\]
The actual leaf L has the four vertices
\[
 (r,0),\quad (R-1/\sqrt2,1/\sqrt2),\quad
 (R,0),\quad (R-1/\sqrt2,-1/\sqrt2).
 \tag{3}
\]
In particular \(0\in\operatorname{int}H\), and the leaf center
has direction east.

If \(R^2\le17/4\), then \(\epsilon=0\), so B contains the
origin, contradicting its physical nonoverlap with H. A point
of a closed unit inside the open interior of another unit also
forces overlap of their open interiors. Thus the entire remaining
domain has
\[
 R>\sqrt{17}/2>41/20,\qquad
 \delta:=d-1=\epsilon\in(0,1/60).
 \tag{4}
\]

Choose any separating unit normal n from H toward B. Convex
separation is available even if H and B do not touch. Its actual
supporting half-planes give
\[
 h:=h_H(n)>0,\qquad
 B\subseteq\{x:n\cdot x\ge h\},\qquad h\le\delta.
 \tag{5}
\]
For the last inequality choose the actual point of B in
\(\overline D_\delta\). Strict positivity follows because the
origin is in the open interior of H.

Throughout (4) the following convenient bounds hold:
\[
 \frac58<r<\frac23,\qquad
 \frac13<s<\frac38,\qquad
 c:=\frac1{\sqrt2}<\frac{17}{24},\qquad R<\frac{25}{12}.
 \tag{6}
\]
For \(r>5/8\), use \(R>41/20\) and
\(\sqrt2<57/40\). To verify \(r<2/3\), the upper radius
bound and \(\sqrt2>113/80\) give
\[
 (\sqrt2+2/3)^2>
 \frac{779}{180}
 =\frac{1105}{256}+\frac{131}{11520}.
\]
The remaining bounds follow directly or by squaring.

Both horizontal support contributions of H are positive.
Consequently (5),(6) imply \(|n_x|<1/20\), and the vertical
component is nonzero. Reflect the whole packing vertically to
write
\[
 n=(n_x,v),\qquad
 a:=|n_x|<1/20,\qquad v=\sqrt{1-a^2}>19/20.
\]
Write H in the same common chart as
\[
 H=[-s,r]\times[-A,\beta],\qquad A=1-\beta.
\]
Its positive vertical support contribution gives
\[
 0<\beta<\frac1{57},\qquad
 A>\frac{56}{57},\qquad \frac av<\frac1{19}.
 \tag{7}
\]
In particular every point \((x,y)\in B\) satisfies
\[
 y\ge\frac{h-n_xx}{v}>
 -\frac av R> -\frac{25}{228}.
 \tag{8}
\]
All separating axes, positive gaps and contact mean endpoints remain
included. The normal n is used only to describe physical separation,
not substituted for any selected stress normal.

## 3. Every boundary neighbor of H is below the horizontal axis

For a physically circle-touching square with center C, its actual
circle corner gives
\[
 |C|\ge R-c>\frac43.
 \tag{9}
\]
Indeed \(R>41/20\) and \(c<17/24\) give
\(R-c>161/120>4/3\).

We use two elementary consequences of the angle
\(\vartheta=2\pi/9\):
\[
 \cos\vartheta<4/5,\qquad
 \sin\vartheta>3/5,\qquad \tan\vartheta>3/4.
 \tag{10}
\]
For the first, \(4x^3-3x\) increases for \(x>1/2\),
has value \(-44/125>-1/2\) at \(x=4/5\), and value
\(\cos(3\vartheta)=-1/2\) at \(x=\cos\vartheta>1/2\).
The other two follow.

Let K physically touch H, physically touch the circle, and be
distinct from the actual leaf L. Suppose first that its center
C has \(C_y\ge0\) and \(C_x\le0\). The nearest point P of
the actual rectangle H to C has
\[
 -s\le P_x\le0,\qquad 0\le P_y\le\beta.
\]
Since an actual H/K contact is at distance at most c from C,
\(\operatorname{dist}(C,H)\le c\). Hence
\[
 |C|\le\sqrt{s^2+\beta^2}+c<r+c=R-c,
\]
a contradiction. The strict comparison follows from
\(r^2-s^2=2r-1>1/4>\beta^2\).

If instead \(C_y\ge0,C_x>0\), contact with H gives
\(C_y\le\beta+c\). Its center angle \(\alpha\in[0,\pi/2)\)
therefore satisfies
\[
 \sin\alpha
 \le\frac{\beta+c}{|C|}
 <\frac34\left(\frac1{57}+\frac{17}{24}\right)
 <\frac35<\sin\vartheta.
\]
The minor center-angle separation from L is then less than
\(\vartheta\), contrary to CENTERED_INNER_ARC.md. Thus
\[
                         C_y<0.
 \tag{11}
\]

We will also need that K cannot contain a point of the top side
of H. If Q is such a point, then
\[
 |C_y|<c,\qquad C_x\ge-s-c>-13/12.
\]
Were \(C_x\le0\), these bounds would give
\[
 |C|^2<(13/12)^2+(17/24)^2
       =965/576<16/9,
\]
contradicting (9). Thus \(C_x>0\), and
\[
 \sin|\arg C|<\frac{c}{4/3}
 <\frac{17}{32}<\frac35<\sin\vartheta.
\]
Again this contradicts K/L angular separation. Therefore
\[
                  K\cap([-s,r]\times\{\beta\})=\varnothing.
 \tag{12}
\]
This conclusion includes both top vertices and every top-side mean.

## 4. The three remaining axis-normal cases are impossible

Assume toward a contradiction that K also physically touches B.
Choose any actual separating normal m directed from H toward K
at their physical contact. Its support point is an actual point
of both squares. Section 3 excludes all normals with positive
vertical component, including the upward axis.

### 4.1. The downward axis

If \(m=-e_y\), all of K has \(y\le-A<-56/57\).
Equation (8) makes K and B closed-disjoint. This is impossible.

### 4.2. The right axis

If \(m=e_x\), all of K has \(x\ge r\). Its center has
\[
 C_x\ge r+1/2>9/8.
\]
By (11), the center is in the southeast quadrant. Its strict
angular separation from L and (10) give
\[
 C_y<-(3/4)C_x<-27/32.
\]
Every point of K consequently has
\[
 y\le C_y+c<-27/32+17/24=-13/96<-25/228.
\]
This again contradicts (8) and the physical B/K contact. The
last positive gap is \(13/96-25/228=47/1824\).

### 4.3. The left axis: a uniform radius bound

If \(m=-e_x\), the actual right support of K is \(x=-s\).
Let \(u\ge w\ge0\), \(u^2+w^2=1\), be the absolute side
components of K, and put \(W=u+w\le\sqrt2\). Thus its
horizontal and vertical widths both equal W and
\[
 C_x=-s-W/2.
\]
A point \((x,y)\in B\cap K\), together with the exact
support value in (5), gives the following two alternatives.

If \(n_x\ge0\), then
\[
 y\ge\beta+(n_x/v)(r-x)\ge\beta>0.
\]
If \(n_x=-a<0\), then
\[
 y\ge\beta+(a/v)(x+s)
 \ge\beta-(a/v)W> -\sqrt2/19>-1/12.
\]
Thus the top support of K is greater than \(-\eta\), where
\(\eta=1/12\). By (11),
\[
                    -W/2-\eta<C_y<0.
\]

The two left/right extreme vertices have vertical offset at most
\((u-w)/2\) from C; their squared radii are therefore below
\[
 F_1=(s+W)^2+(u+\eta)^2.
\]
The top/bottom extreme vertices have horizontal magnitude at most
\(s+u\); their squared radii are below
\[
 F_2=(s+u)^2+(W+\eta)^2.
\]
These two vertex pairs cover every orientation, including w=0.
Moreover
\[
 F_1-F_2=2(s-\eta)w\ge0.
\]
The following continuous bound needs no angular partition:
\[
\begin{aligned}
 F_1
 &=1+s^2+\eta^2+(u^2+2uw)
      +2(s+\eta)u+2sw\\
 &<1+\frac9{64}+\frac1{144}+\frac{13}{8}+\frac65
 =4-\frac{79}{2880}<4.
\end{aligned}
 \tag{13}
\]
Here
\[
 u^2+2uw\le(1+\sqrt5)/2<13/8
\]
is the largest eigenvalue bound for the displayed two-variable
quadratic form, or follows by completing a square. Cauchy--Schwarz
also gives
\[
 2(s+\eta)u+2sw
 \le2\sqrt{(s+\eta)^2+s^2}
 <\frac{\sqrt{202}}{12}<\frac65.
\]
The last squared comparison is \(202/144<36/25\).
Every corner of K is therefore strictly inside the radius-two
disk, contrary to its physical contact with the radius R circle,
where R>2.

## 5. Strict lower-corner normals: the whole support-feature cover

It remains that \(m_y<0,m_x\ne0\). The H/K contact is at
the corresponding bottom H vertex Q. All possible K owners,
vertices, side interiors and mean endpoints are retained below.

Recall the support-span fact: if Q is a minimum-m support point
of a unit square and \(m\cdot n<0\), then
\[
                  \max_{x\in K}n\cdot(x-Q)<1.
 \tag{14}
\]
At a vertex at least one inward own-axis n component is negative,
so the positive span is at most the other component, strictly less
than one. At a side-interior point the inward normal component is
negative, and only a tangent interval of length at most one can
contribute; its unit n component is again strictly below one.
This proves (14), including all endpoint means.

If \(n_x=0\), the support gap from Q to B is one and
\(m\cdot n<0\), contradicting (14). If n_x and m_x have
opposite signs, the support gap is
\[
                         h-n\cdot Q=a+v\ge1
\]
and their dot product is negative. Equation (14) again makes the
two units closed-disjoint. Thus only the same-sign case remains,
with a>0.

Reflect only the coordinate notation horizontally for a left
corner, keeping the actual geometry fixed. In this auxiliary frame
write
\[
 n=(a,v),\quad m=(b,-f),\quad b,f>0,\quad
 Q=(q,-A),\quad
 q=\begin{cases}r&\text{right corner},\\s&\text{left corner}.
 \end{cases}
 \tag{15}
\]
The actual B/K contact implies
\[
                    \max_{x\in K}n\cdot(x-Q)\ge v,
 \tag{16}
\]
because the top and bottom root vertices on this same side differ
by exactly the unit vertical vector.

### 5.1. The actual K frame and its complete slider

The minimum-m support feature at Q gives the following exact
representation:
\[
 \begin{split}
 U&=(\sin\theta,\cos\theta),\
 V&=(\cos\theta,-\sin\theta),\
 K&=Q+[-\tau,1-\tau]U+[0,1]V,
 \qquad 0\le\theta\le\pi/2,\quad0\le\tau\le1.
 \end{split}
 \tag{17}
\]
Here is why no feature is omitted. If Q is a vertex and both
inward side vectors have nonpositive vertical component, their
whole positive n-span is at most \(a\sqrt2<v\), contrary
to (16). An upward inward axis cannot point left, since its dot
product with \(m=(b,-f)\) would be negative. It must be the
upward/right axis U in (17), whose orthogonal inward companion
is V, pointing right/down. In the vertex case \(\tau=0\).
If Q is side-interior, its inward normal m points right/down,
and its upward tangent points right/up; these are exactly V,U
in (17), with the arbitrary actual side parameter \(\tau\).
The side endpoints are included. More precisely \(\tau\)
can be nonzero only when \(m\cdot U=0\), but this additional
restriction is not needed.

Put \(\phi=\arcsin a\), so v=cos(phi). Formula (17) gives
the exact whole-support maximum
\[
 \max_K n\cdot(x-Q)
  =(1-\tau)\cos(\theta-\phi)
        +\max(0,\sin(\phi-\theta)).
 \tag{18}
\]
If \(\theta\ge\phi\), equations (16),(18) imply
\(\cos(\theta-\phi)\ge\cos\phi\), hence
\(\theta\le2\phi\). If \(\theta<\phi\), the same
bound is automatic. Therefore
\[
 \sin\theta\le2av<1/10,\qquad
 \cos\theta>99/100.
\]
Also (16),(18) imply \(v\le1-\tau+a\).
Since \(v>1-a^2\), the full slider obeys
\[
                  0\le\tau<1/20+1/400=21/400.
 \tag{19}
\]
These are continuous bounds for every actual support feature.

### 5.2. A left lower corner makes K too close to the origin

For q=s, equations (6),(7),(17),(19) put every point of K in
\[
 0<x<\frac38+1+\frac1{10}=\frac{59}{40},\qquad
 -\frac{461}{400}<y<\frac1{57}.
\]
For the lower x inequality use
\(s-\tau\sin\theta>1/3-21/4000>0\).
For the lower y inequality use
\(-A-\tau\cos\theta-\sin\theta>
 -1-21/400-1/10=-461/400\).
Consequently every point of K satisfies
\[
 |x|^2<
 \left(\frac{59}{40}\right)^2+
 \left(\frac{461}{400}\right)^2
 =\frac{560621}{160000}<4.
 \tag{20}
\]
The notation \(|x|\) in (20) denotes the Euclidean norm of
the point, not its first coordinate. Horizontal reflection preserves
that norm. Again K cannot physically touch the R>2 circle.

### 5.3. A right lower corner makes K overlap the actual D leaf

For q=r return to the original coordinates and fix the actual point
\[
                              Z=(r+1/4,-1/8).
\]
It is strictly inside L: its distance from the inner radial vertex
in the x direction is 1/4, greater than its vertical magnitude 1/8;
its distance from the far radial vertex is
\(R-r-1/4=\sqrt2-1/4>1/8\).

Relative to Q, \(Z-Q=(1/4,A-1/8)\), where
\(0<A-1/8<7/8\). Equations (17),(19) give
\[
 0<U\cdot(Z-Q)
 <1/40+7/8=9/10<379/400<1-\tau,
\]
and
\[
 0<\frac{99}{400}-\frac7{80}
 =\frac4{25}
 <V\cdot(Z-Q)\le1/4<1.
\]
Thus Z is strictly inside the actual K as well, contrary to
physical nonoverlap with L. This contradiction preserves the full
support slider and does not replace Q by a different contact point.

Sections 3--5 exhaust every actual H/K supporting normal. Therefore
a common boundary neighbor K cannot exist, proving Theorem 1.1.

## 6. Exact original mixed hub/tip diamond consequences

Use the original diamond with hubs H,K, tips B,C, and exact
positive edges
\[
                         HK,HB,HC,KB,KC.
\]
Attach the two genuine leaves at H and B. The complete load cover
FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md forces positive block
loads exactly K,C; its actual degrees are H4, B3, K3, C2.

If the genuine D leaf is at H, the genuine S root B meets
\(\overline D_\epsilon\), and the original loaded K
physically touches both H and B. Theorem 1.1 applies directly.

If the genuine D leaf is at B, rename that actual root as the
theorem's H, and use the original S root H as its near-origin B.
The same original loaded K is their common physical boundary
neighbor. The theorem again applies, with the original K3,
C2 and all root forces unchanged.

Thus, upon independent full acceptance, precisely these two existing
whole gates have a new complete exit:
\[
 \text{M6.B4L2.DIAMOND.HUB\_TIP.LKC.DH\_SB},\qquad
 \text{M6.B4L2.DIAMOND.HUB\_TIP.LKC.SH\_DB}.
\]
The entire physical masks, all individual zero corner weights,
shared means, positive force magnitudes, extra physical contacts
and all three completion units are included. The S/S gate and
the whole hub/tip parent are not asserted closed by this theorem.

More generally any two distinct genuine leaf roots, one of type D,
cannot have even one common physically boundary neighbor. The
other D-root alternative is already impossible from the two open
origin-containing roots; the mixed S/D case is the new geometric
implication. No positive degree is required at that common neighbor.
This re-proves several previously closed triangle or opposite-root
families, which must not be counted again.

No checklist or roadmap is changed by this source. No new gate IDs,
sampled poses, angular mesh, scalar certificate, force deletion,
post-extraction normal change, Lean compilation or CI is used.

