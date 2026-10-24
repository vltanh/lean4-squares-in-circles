# Two diagonal transmitters are impossible in the alternating three-load six-cycle

**Status: complete whole-width hand exclusion; root and separate independent
full hand audits passed.**
Work throughout
\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
                    \qquad Q=\frac{1105}{256}.
\tag{1}
\]
Suppose the exact positive component is the alternating six-cycle
\[
                          T-U-B-W-C-V-T,
\tag{2}
\]
with precisely \(T,B,C\) loaded. Retain all physical circle-corner
masks, all actual contact means, all three additional units, and the
existing compatible strict point normals and diagonal avoidance.

**Theorem.** At most one of \(U,V,W\) can be a diagonal transmitter.

This is the complete finite width class with at least two diagonals.
It does not close the side/side/side or side/side/diagonal classes,
and it does not apply to a cycle whose vertices have extra positive
edges.

## 1. The three loaded concurrences form a proper triangle

SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md gives nonparallel pair
forces at every loaded body, including loads with no boundary neighbor.
The all-mask proper-concurrence lemma of
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Section1, therefore applies:
\(q_i\) is a positive multiple of its circle resultant and
\[
                       p_i-q_i=\alpha_i n_i,\qquad\alpha_i\ge0
\tag{3}
\]
at every actual application.

Contracting each transmitter gives an edge in its force direction
with strictly positive length at least its reserve. The common origin
moment cannot vanish. Otherwise every consecutive pair of the three
positive radial concurrence vectors would be collinear. Distinct
loaded bodies have disjoint physical circle-corner direction intervals,
so their positive radial directions cannot agree. Each consecutive
pair would then have to be antipodal, which is impossible on an odd
three-cycle.

Orient the cycle to make its common moment positive. All three
successive radial increments lie strictly between zero and \(\pi\);
their sum is \(2\pi\). The force equations give positive turns exactly
as in FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Section3. Thus the three
concurrences form a strictly convex triangle containing the origin.
No bound on a physical two-corner concurrence is asserted.

## 2. Two diagonal channels fix the common loaded frame

If at least two transmitters are diagonal, relabel the three loads
so these are \(U,V\). Each diagonal transmitter has its two applications
at opposite vertices. Existing compatible diagonal avoidance excludes
a selected vertex/vertex contact there. Both applications consequently
lie in strict relative interiors of loaded sides. Its two endpoint
loaded units share a side axis along the channel.

It follows that \(T,B,C\) all have the same square frame. At \(T\)
the two actual force directions are side axes; nonparallelism makes
them perpendicular. Choose the common coordinates so the two
outward directions at \(T\) are \(-e_x,-e_y\), with \(B\) across the
first channel and \(C\) across the second.

The proper triangle then makes the directed \(B\)-to-\(C\) channel
strictly southeast. If \(W\) were diagonal, its normal would also be
a common loaded side axis, an impossibility. Thus \(W\) is side-normal.
Write its unit direction as
\[
                        n=(a,-b),\qquad
                        a,b>0,\quad a^2+b^2=1.
\tag{4}
\]
The true force equations imply that the circle resultants at
\(T,B,C\) lie respectively in the open northeast, northwest and
southeast quadrants.

For aligned boundary squares this gives the corresponding weak
center-coordinate signs, even when a center coordinate vanishes
and two physical circle corners have unequal weights. Hence we may
write their actual far circle corners as northeast for \(T\),
northwest for \(B\), and southeast for \(C\).

Put
\[
                A=2+\sqrt2,\qquad
                d=\sqrt2-b,\qquad e=\sqrt2-a.
\tag{5}
\]
Let the northeast circle corner of \(T\) be \((\alpha,\beta)\).
Then \(\alpha,\beta\ge1/2\) and
\[
                              \alpha^2+\beta^2=R^2.
\tag{6}
\]

The two diagonal channels have center projection gaps \(1+\sqrt2\).
The third channel has reserve1 and an oblique normal relative to
the common frame, so its endpoint support features are the actual
southeast/northwest vertices. Its exact center displacement is
\[
                              c_C-c_B=(1+a,-1-b).
\tag{7}
\]
Combining these three coordinate identities shows that the chosen
circle corners of \(B,C\) are exactly
\[
                         (\alpha-A,\beta-d),
                         \qquad(\alpha-e,\beta-A).
\tag{8}
\]
No transverse application mean on the two diagonal channels has
been prescribed.

The three equal circle radii give
\[
 \begin{split}
             A\alpha+d\beta&=\frac{A^2+d^2}{2},\\
             e\alpha+A\beta&=\frac{e^2+A^2}{2}.
 \end{split}
\tag{9}
\]

## 3. The physical quadrant signs force \(a,b>1/3\)

Let
\[
                           K=\sqrt{R^2-\frac14}<\frac{81}{40}.
\tag{10}
\]
The northwest corner of \(B\) has first coordinate \(\alpha-A<0\).
Its center has nonnegative second coordinate, so its circle corner
has second coordinate at least \(1/2\). Consequently
\[
                         \alpha\ge A-K,\qquad
                         \beta\ge d+\frac12.
\tag{11}
\]
Substitution into the first identity in (9) gives
\[
                             A^2-2AK+d^2+d\le0.
\tag{12}
\]

If \(b\le1/3\), then \(d\ge\sqrt2-1/3>0\). The left side of (12)
is strictly greater than
\[
 \begin{split}
 A^2-\frac{81}{20}A+
       \left(\sqrt2-\frac13\right)^2+\sqrt2-\frac13
             &=\frac{51\sqrt2-58}{180}>0.
 \end{split}
\tag{13}
\]
The last sign follows already from \(\sqrt2>7/5\).
This contradicts (12), so \(b>1/3\). Applying the reflected
argument at \(C\) gives \(a>1/3\).

Put \(s=a+b\). From
\((a-1/3)(b-1/3)>0\) and \(a^2+b^2=1\),
\[
                  s>\frac{1+2\sqrt2}{3}>\frac54,
                  \qquad s\le\sqrt2.
\tag{14}
\]
The final comparison uses \(\sqrt2>11/8\).

## 4. The summed circle equations exceed the target radius

Adding (9) and applying Cauchy's inequality gives
\[
 \begin{split}
 R^2
 &\ge
 \frac{(2A^2+d^2+e^2)^2}
      {4\bigl((A+e)^2+(A+d)^2\bigr)}\\
 &=f(s):=
 \frac{(17+8\sqrt2-2\sqrt2\,s)^2}
      {4\bigl(25+16\sqrt2-(4+4\sqrt2)s\bigr)}.
 \end{split}
\tag{15}
\]
Every denominator is positive because it is the displayed sum of
two squares. To check monotonicity directly, write
\[
       N=17+8\sqrt2-2\sqrt2\,s,\qquad
       D=25+16\sqrt2-(4+4\sqrt2)s.
\]
Then
\[
        f'(s)=\frac{N}{D^2}
                \bigl((1+\sqrt2)N-\sqrt2 D\bigr)
              =\frac{N}{D^2}\bigl(1+(4+2\sqrt2)s\bigr)>0
\tag{16}
\]
throughout (14). Therefore
\[
 R^2>f(5/4)
      =\frac{(34+11\sqrt2)^2}{16(20+11\sqrt2)}.
\tag{17}
\]
The exact difference from \(Q\) is
\[
 f(5/4)-\frac{1105}{256}
     =\frac{268-187\sqrt2}{256(20+11\sqrt2)}>0,
\tag{18}
\]
since \(\sqrt2<10/7\) makes its numerator greater than \(6/7\).
This contradicts (1) and proves the theorem.

The proof retains the zero-height endpoint cases of the physical
two-corner masks and every transverse side mean. The three completion
squares never move. There is no use of a sampled frame, a numerical
optimizer, a two-loaded exceptional cycle, Lean compilation or CI.

