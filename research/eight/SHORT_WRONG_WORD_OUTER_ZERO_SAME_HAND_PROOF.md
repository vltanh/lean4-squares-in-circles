# Wrong word 0010111: the four same-sign outer zero-quarter secondary cases

## Statement

All four remaining same-sign outer/outer secondary branches of the
zero-quarter edges have corrected cost

\[
 C>.898>\frac{17953}{20000}.
\]

They are \((0,++,1),(1,--,3),(3,++,1),(3,--,3)\).
The proof covers the whole continuous angle domain \(|\phi|\le.7\).
Together with the all-primary and opposite-secondary notes, it closes
every outer/outer zero-quarter branch.

The companion verify_short_outer_zero_same_hand.js verifies 56 fixed
strict rational comparisons. The continuous argument is the support
and curvature proof below; the checker performs no domain search.

## 1. The four rows and their necessary angle range

Use \(Q=9789/2500,\ R=\sqrt Q,\ d=\sqrt{Q/2}-1/2\), and

\[
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\quad
 0\le b\le d,\quad a_0=a(0),\quad
 r_b=\frac{b+1/2}{a(b)+1/2}.
\]

Reflect and reverse each original \((--)\), axis-3 case. This
preserves cost and \(\phi\) and produces signs \((++)\), axis 1.
The normalized cost and separator are

\[
 C=\phi+c_*+pa+qb-PA-tB,\qquad
 b+A\sin\phi-B\cos\phi\ge W,
\quad W=\frac{1+|\sin\phi|+\cos\phi}{2}.        \tag{1}
\]

The exact normalized coefficients are:

| Edge | Original signs, axis | \(c_*\) | \(p\) | \(q\) | \(P\) | \(t\) |
|---:|:---:|---:|---:|---:|---:|---:|
| 0 | ++, 1 | −.0613 | 0 | .94766 | 0 | .9994 |
| 1 | −−, 3 | .27086 | −.09133 | .88074 | .13422 | 1.03828 |
| 3 | ++, 1 | −.75097 | .51554 | 1.19909 | 0 | .71553 |
| 3 | −−, 3 | .74349 | −.19335 | .76744 | .33147 | 1.1336 |

No case is possible for \(\phi\le0\), because the separator
projection in (1) is at most \(b\le d<1\le W\). For positive
\(\phi\), that projection is at most \(d+a_0\sin\phi\).
Furthermore \(W-d-a_0\sin\phi\) decreases up to .107, and

\[
 W(.107)-d-a_0\sin(.107)>0.
\]

Consequently every pair considered here has

\[
 .107<\phi\le.7.                              \tag{2}
\]

## 2. Three elementary source supports

Fix \(\lambda>0\) and subtract \(\lambda\) times the separator
margin from the cost. With \(s=\sin\phi,c=\cos\phi\),

\[
 C\ge\phi+c_*+\lambda W+S+
              (-P-\lambda s)A+(\lambda c-t)B,                \tag{3}
\]

where \(S\) is a lower bound for \(pa+(q-\lambda)b\). We use

\[
 S_E=\min\{pa_0,d(p+q-\lambda)\}\quad(p\ge0),                  \tag{4}
\]
\[
 S_D=d(p+q-\lambda)
       \quad(p\le0,\ q-\lambda\le p),                       \tag{5}
\]
\[
 S_C=-\frac{p+q-\lambda}{2}
       -R\sqrt{p^2+(q-\lambda)^2}.                           \tag{6}
\]

For (4), the affine functional is concave in \(b\); for (5), its
derivative is \(-pr_b+q-\lambda\le-p+q-\lambda\le0\).
Formula (6) enlarges the outer arc to its full translated circle.
It remains a valid lower bound even if its circular minimizing
point is outside the physical arc.

The exact tests for (4)–(5) are immediate from the coefficient table.
For row 0 with \(\lambda=.94766\), the source functional is zero.

## 3. Axial and circular target supports

Put

\[
 X=-P-\lambda s<0,\qquad Y=\lambda c-t.
\]

The target functional \(XA+YB\) is convex in \(B\), and its
derivative at \(B=0\) is \(Y-Xr_0\), where
\(r_0=(1/2)/(a_0+1/2)\). If

\[
 \lambda(c+r_0s)+Pr_0-t\ge0,                 \tag{7}
\]

the target support is exactly axial. Its cost bound is

\[
 F_a=\phi+c_*+S+\frac{\lambda}{2}-Pa_0
               +\frac{\lambda}{2}c
               +\lambda(\tfrac12-a_0)s.     \tag{8}
\]

The left side of (7) is concave in \(\phi\) on (2), so checking
its two interval endpoints proves it on the entire interval.

Since \(a_0-1/2<.915\) and
\(\sqrt{.915^2+1/4}<1.043\),

\[
 F_a'>1-1.043\lambda.                        \tag{9}
\]

Also
\[
 F_a''=\lambda(a_0-\tfrac12)s-\frac{\lambda}{2}c<0
 \quad\hbox{for }0\le\phi\le.3,              \tag{10}
\]
by the single comparison
\((a_0-1/2)\sin .3<\frac12\cos .3\).

The full-circle target support gives

\[
 F_c=\phi+c_*+S+\frac{\lambda+P+t}{2}
                 +\lambda s-RN,            \tag{11}
\]
\[
 N^2=(P+\lambda s)^2+(t-\lambda c)^2
     =n^2+\lambda^2-2\lambda u,\quad
 n^2=P^2+t^2,\quad u=tc-Ps.                  \tag{12}
\]

The following two tests prove concavity of (11) on all of the
fixed intervals used below.

### 3.1. Norm test

The exact identity

\[
 N''+\frac N4=\frac{(n^2-\lambda^2)^2}{4N^3}\ge0              \tag{13}
\]

shows that \(N<2\lambda\sin\phi\), together with \(R<2\),
implies \(F_c''<0\).

Suppose \(t>\lambda\) and \(\phi\in[l,h]\subset(0,.7]\).
The positive function
\[
 v(\phi)=\frac{t-\lambda\cos\phi}{\sin\phi}
\]
has derivative
\((\lambda-t\cos\phi)/\sin^2\phi\). This derivative changes
sign at most once, from negative to positive. Thus
\(v(\phi)\le\max(v(l),v(h))\). Since \(P\ge0\), we obtain

\[
 \frac N{\sin\phi}\le
 \sqrt{\left(\lambda+\frac P{\sin l}\right)^2+
             \max\{v(l),v(h)\}^2}.           \tag{14}
\]

If the right side is less than \(2\lambda\), concavity follows
on the whole interval.

### 3.2. Direct curvature test

Differentiating (12) also gives

\[
 N''=\frac{\lambda(u-\lambda)(n^2-\lambda u)}{N^3}.           \tag{15}
\]

For our uses of this test, \(n>\lambda\), \(u\) decreases, and
\(N\ge P+\lambda\sin l=:N_0>0\).
Put \(u_0=t\cos h-P\sin h\).

If \(u_0\ge\lambda\), equation (15) makes \(N''\ge0\), so
\(F_c''<0\) directly. If \(u_0<\lambda\), the negative part of
(15) is at most

\[
 \frac{\lambda(\lambda-u_0)(n^2-\lambda u_0)}{N_0^3}.
\]

Therefore it suffices to check the single strict inequality

\[
 \sin l>
 \frac{2(\lambda-u_0)(n^2-\lambda u_0)}{N_0^3}.               \tag{16}
\]

For the three intervals using (16), the respective strict
reserves in (16) exceed .05538, .13532, and .11048.
There is no need to locate a stationary point of \(F_c\).

## 4. Complete interval table

The table lists every remaining interval. A source support is
\(E,D,C\) according to (4)–(6). A target is axial or circular.
The letter N means the norm test (14); D means the direct
curvature test (15) or (16). The two displayed values are
strict rational lower bounds at the interval endpoints.

| Edge, original signs | Angle interval | \(\lambda\) | Source | Target and continuous argument | Endpoint lower bounds |
|---|---|---:|:---:|---|---|
| 0, ++ | [.107,.2] | .98 | D | circle, N | .898050929936, .901125491024 |
| 0, ++ | [.2,.7] | .94766 | E | circle, N | .902599464256, .898110421444 |
| 1, −− | [.107,.3] | 1 | D | axial, (7) and concavity (10) | .898097672006, .899022816726 |
| 1, −− | [.3,.7] | .94 | C | circle, N | .903533161036, .898105707205 |
| 3, ++ | [.107,.7] | .90362 | E | axial, (7) and increasing (9) | .898077171496, .943273596164 |
| 3, −− | [.107,.16] | 1.025 | D | circle, \(u_0>\lambda\) in (15) | .898089215497, .898135905229 |
| 3, −− | [.16,.3] | 1 | D | circle, D | .898922123486, .898709289884 |
| 3, −− | [.3,.4] | .95 | C | circle, D | .902158367656, .903456209617 |
| 3, −− | [.4,.5] | .906 | C | circle, D | .899329670542, .901787522592 |
| 3, −− | [.5,.7] | .906 | C | circle, N | .901787522592, .898094700777 |

For the two axial rows, (7) is positive at both stated interval
endpoints; its concavity then proves the required target support
throughout. For the increasing row,
\(1-1.043(.90362)>0\).
Every source sign condition and every curvature test in the
table is a fixed scalar comparison.

All displayed bounds exceed .898. Equation (2) and the complete
table cover each of the four original branches. In particular the
close lower-angle endpoint is handled by an explicit rational
support bound; no near-contact limiting argument is omitted.

## 5. Relation to the other zero-quarter notes

SHORT_WRONG_WORD_OUTER_ZERO_PRIMARY_HAND_PROOF.md closes all
fourteen primary branches and the four unfavorable same-sign
secondary branches. SHORT_WRONG_WORD_OUTER_ZERO_OPPOSITE_HAND_PROOF.md
closes all six opposite-sign secondary branches. The four branches
proved here are precisely their complement:

\[
 14+4+6+4=28.
\]

This equality is a count of the allowed edge/sign/axis combinations,
not a discretization of the continuous geometric domain. The
quarter-one outer cases require their separate proof.

