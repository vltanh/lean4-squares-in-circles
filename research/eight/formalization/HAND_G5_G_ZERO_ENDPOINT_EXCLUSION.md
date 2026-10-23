# The remaining positive-owner zero-transverse endpoint is impossible

## 1. Exact endpoint and containing radius

Put

\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad
 L=311/1000,\qquad h_0=107/1000.
\tag{1}
\]

Consider precisely the G-zero endpoint constructed in Section 7 of
`HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md`, at an actual
ceiling `q_L<=q<=Q`. Its H, A, B and D anchors have nonnegative
sorted own-frame coordinates and corner values at most q. E may
have either signed transverse coordinate: `a_E>=|b_E|` and
`(a_E+1/2)^2+(|b_E|+1/2)^2<=q`. A lies on its q-circle. Write

\[
 t,u,d,v\ge0,\qquad t+u=d+v=x\le7/10,
 \qquad z=t+h<2/5,
\tag{2}
\]

where h is the remaining positive HG error. The actual endpoint
inequalities are

\[
\begin{gathered}
 (a_A-1/2)\cos z-(b_A+1/2)\sin z=1/2,\\
 b_H\ge1/2+(1/2)\cos h-(\sqrt{q-1/4}-1)\sin h,\\
 b_A+b_B\ge1,\qquad
 a_B\cos u-b_B\sin u+b_D\ge1+W(u),\\
 a_D+a_E\sin d+b_E\cos d\ge W(d),\\
 a_H+a_E\sin v-b_E\cos v\ge W(v),
\end{gathered}
\tag{3}
\]

with `W(y)=(1+cos y+sin y)/2`. The endpoint still to be treated has

\[
                  67/200<b_A<1/2,\qquad b_B<133/200.
\tag{4}
\]

If `b_A>=1/2`, the preceding positive-owner theorem already aligns
the pair, with strict slack for h positive; that case is not needed
in (4). In particular this note uses the active GA contact and
the actual A circle supplied by that endpoint construction.

**Endpoint theorem.** No system (1)--(4) exists. Reflection gives
the corresponding T-zero exclusion when the H-side path is already
aligned; the allowed signed E coordinate absorbs its sign reversal.
There is no mismatch hypothesis in this statement.

## 2. Sorting H forces h greater than 107/1000

Positive squaring gives

\[
 \sqrt{Q-1/4}-1<183/200,
 \qquad \sqrt{Q/2}-1/2<89923/100000.
\tag{5}
\]

For the second comparison the squared reserve is
`445929/10000000000`. If `0<=h<=107/1000`, the second line of
(3), `cos h>=1-h^2/2`, and `sin h<=h` give

\[
\begin{split}
 b_H&\ge1-h^2/4-(183/200)h\\
 &\ge89923/100000+11/4000000.
\end{split}
\tag{6}
\]

This contradicts the sorted H circle and (5). Hence

\[
                              h>h_0.
\tag{7}
\]

## 3. Retain the two actual A/B caps

For a radius r and a constant D define

\[
 \mathcal L_{r,D}(y)=\cos y\sqrt{r-(D+\cos y)^2}
                            -\sin y(D+\cos y).
\tag{8}
\]

The first line of (3), together with A's actual circle equality,
gives exactly

\[
                         b_A+1/2=\mathcal L_{q,1/2}(z).
\tag{9}
\]

The positive rotated transverse coordinate selects the displayed
square root. The usual cap derivative is negative on the interval
in question; its radicand is positive since `q>=q_L>5/2`.
The B constraint gives

\[
 b_B+1/2\le\mathcal L_{q,D_B}(u),
                       \qquad D_B=3/2-b_D>3/5.
\tag{10}
\]

Caps increase with r and decrease with D. Thus the same actual
AB sum in (3) gives the necessary comparison

\[
       2\le\mathcal L_{Q,1/2}(z)+\mathcal L_{Q,3/5}(u).
\tag{11}
\]

There is also a useful lower bound on z. At `y=19/100`,

\[
 q_L>1+\left(1+\frac{1/2+y}{1-y^2/2}\right)^2,
\tag{12}
\]

with exact reserve `31374204217/1928451605000`. Since
`sin y<=y` and `cos y>=1-y^2/2`, the q_L cap at this angle
is greater than 1. Monotonicity and (4),(9) therefore imply

\[
                              z>19/100.
\tag{13}
\]

## 4. One cap comparison forces x+h less than 311/1000

Suppose `z+u>=L`. Decreasing z and u, if necessary, gives
`z'+u'=L`, with `19/100<=z'<=L`, and both caps in (11) no
smaller. It suffices to contradict (11) on this segment.

The cap with D=3/5 is strictly convex on its entire interval by
`HAND_G5_HARD_SPLIT_CONVEXITY_FULL_FEASIBLE_CAP_RANGE.md`.
The D=1/2 cap is strictly convex on `[19/100,L]`, as follows
directly from that note's second-derivative identity. To check
its scope explicitly, write

\[
 c=\cos z',\ s=\sin z',\ C=1/2+c,\ w=\sqrt{Q-C^2},
 \quad X=cC+sw,\ k=w-s,\ \mathcal L=cw-sC.
\]

On this interval, `c>19/20`, `47/250<s<311/1000`,
`w>129/100`, and `C<=3/2`, so `mathcal L>0`. Moreover

\[
\begin{split}
 X-k^2
 &=-207/1250+3s\left(w-s-\frac{s/2}{1+c}\right)\\
 &>17/50,
\end{split}
\tag{14}
\]

where the lower substitution has reserve `5137/3250000` above
17/50. Thus

\[
 \mathcal L''=
       \frac{\mathcal L w(X-k^2)+XkCs}{w^3}>0.
\tag{15}
\]

No convexity of the D=1/2 cap near zero is assumed. Convexity
of the sum in (11), on this one segment, reduces its maximum to
the two endpoints. Both are strictly below 2:

\[
\begin{aligned}
 \mathcal L_{Q,1/2}(.19)+\mathcal L_{Q,3/5}(.121)
                                  &<1.01+.98<2,\\
 \mathcal L_{Q,1/2}(.311)+\mathcal L_{Q,3/5}(0)
                                  &<.8356+1.1644=2.
\end{aligned}
\tag{16}
\]

Here is the exact arithmetic for these comparisons. For a
positive candidate cap bound r, the identity
`(X-1)cos y-r sin y=D`, `X^2+r^2=Q` shows that

\[
 \left(1+\frac{D+r\sin y}{\cos y}\right)^2+r^2>Q
             \quad\Longrightarrow\quad\mathcal L_{Q,D}(y)<r.
\tag{17}
\]

For the first line of (16), use respectively
`sin(.19)>.188`, `cos(.19)<.983`, and
`sin(.121)>.12`, `cos(.121)<.993`. The positive squared
reserves in (17) are

\[
              6376949/9662890000,
                  \qquad845858/68475625.
\tag{18}
\]

At .311 the cubic sine lower bound and quartic cosine upper
bound give `sin(.311)>.30598`, `cos(.311)<.95203`. Their
respective reserves are `39769/6000000000` and
`17048159/24000000000000`. The squared reserve in (17), with
r=.8356, is

\[
                  10083936203273/56647570056250000>0.
\tag{19}
\]

Finally `1.1644^2-(Q-(8/5)^2)=1421/6250000>0` supplies the
zero-angle B cap in (16). Thus (16) contradicts (11), proving

\[
                          x+h=z+u<L.
\tag{20}
\]

## 5. Apply the continuous five-circle stress

Equations (7) and (20) imply the whole scalar domain

\[
 0\le x<51/250,\qquad h_0<h<L-x,
 \qquad0\le t,d\le x.
\tag{21}
\]

The first line of (3) is equivalent to the ordinary G-zero GA
inequality `a_A cos z-b_A sin z=W(z)`. Its second line implies
the weaker Q-ceiling bound

\[
 b_H\ge1/2+(1/2)\cos h-(\sqrt{Q-1/4}-1)\sin h.
\]

Consequently every inequality in (10) of
`HAND_G5_G_ZERO_TWO_AFFINE_STRESS_SCALARS.md` holds at the
same five anchors. That theorem proves its positive stress
excess is greater than `13/50000` everywhere in (21), whereas
the actual five circles would give a nonpositive excess.
This contradiction proves the endpoint theorem.

The reasoning keeps the actual A/B cap coupling until it supplies
the domain of the final stress. It uses no original small-mismatch
premise, frame mesh, state table, sampled minimum, external
acceptance result, Lean compilation or CI.
