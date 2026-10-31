# A genuine radial return owner and an adjacent endpoint cannot share the actual return channel

Date: October 26, 2026.

**Status: complete analytic whole-feature-family exclusion, accepted after root and separate full-source reviews in REVIEW_C6_RADIAL_ADJACENT_RETURN_OWNER_ROOT_2026_10_26.md and REVIEW_C6_RADIAL_ADJACENT_RETURN_OWNER_BLOCK_2026_10_26.md.** The local return-owner inequality below, joined to the adjacent endpoint bound, excludes the full strict-turn A/T family with all original means and endpoints. The A/O family and lower-turn placements remain separate.

Retain the original one-radial, all-side alternating C6 in
\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\qquad r_0^2=d^2+1/4,
\tag{1}
\]
with every original square, force, radial circle weight, shared mean, endpoint and transmitter slider unchanged.

The two unique loaded turns are strictly greater than \(\pi/2\). One actual S-incident application is its adjacent-to-circle vertex, possibly an original genuine mean already at that vertex. The other is the opposite-to-circle vertex and genuinely owns the normal at the B-to-C return channel. These are exactly the A/T feature premises of the accepted exhaustive strict-turn owner cover.

The actual A endpoint has return application \((-m,H)\). The actual T endpoint has reflected return application \((a-1,H)\), with \(H>0\). The unchanged reserve-one transmitter gives
\[
                              m+(a-1)=1.
\tag{2}
\]

**Theorem.** This entire original physical feature family is impossible as a six-body core.

The proof uses the whole local A inequality
\[
                         m+H>9/10
\tag{3}
\]
from SIX_CYCLE_RADIAL_ADJACENT_RETURN_DIAGONAL_BOUND.md and proves the complementary whole local T inequality
\[
                         \boxed{a-H>11/10.}
\tag{4}
\]
Their sum contradicts (2).

## 1. Exact T chart and two consequences of its actual radial-port norm

Use the actual return-owner chart
\[
 a>b>1/2,\qquad a^2+b^2=R^2,\qquad
 t=1-H/b\in[0,1),
\]
\[
 X=1-ta>0,\quad Y=1-tb=1-b+H\in(0,1],\quad
 L=\sqrt{X^2+Y^2},\quad x=X/L,\quad y=Y/L,
\]
\[
 r=1/\sqrt2,\qquad 0<x\le r\le y<1,\qquad
 P=(a-1-x,b-1-y),\qquad |P|^2=r_0^2.
\tag{5}
\]
This is the same unchanged physical mean chart as in SIX_CYCLE_RADIAL_RETURN_OWNER_HEIGHT_BOUND.md; its complete theorem supplies
\[
                                H<7/10.
\tag{6}
\]
No other endpoint feature is used in that height theorem.

First,
\[
                          (a-1)x+(b-1)y>b-1.
\tag{7}
\]
If \(b\ge1\), write the left side as
\((a-b)x+(b-1)(x+y)\), use \(x>0\), \(a>b\), and \(x+y\ge1\).
If \(b\le1\), use \(a>R/\sqrt2>1\), \(x>0\), and
\((b-1)y\ge b-1\). Thus (7) includes both cases. Subtracting the actual norm identity in (5) gives
\[
                                a+2b<3+d.
\tag{8}
\]

Second, (8) forces
\[
                                  a>8/5.
\tag{9}
\]
For completeness, on \(a>R/\sqrt2\) the function
\(a+2\sqrt{R^2-a^2}\) decreases strictly. If \(a\le8/5\), it would give
\[
 a+2b\ge\frac85+2\sqrt{R^2-\frac{64}{25}}>3+d.
\]
The last difference increases with R. At \(R=79/40\), it is
\[
                \frac{2\sqrt{2145}-\sqrt{5841}-16}{40}>0.
\tag{10}
\]
Its exact positive-square proof is
\[
 2483^2-32^2\cdot5841=184105>0,
\]
followed by
\[
 (2\sqrt{2145})^2-(\sqrt{5841}+16)^2
                       =2483-32\sqrt{5841}>0.
\]
This is the same pointwise comparison used in the accepted mean/return-owner exclusion, and it needs no partner span premise.

We will also use
\[
                                  b<7/6.
\tag{11}
\]
It is automatic if \(b\le1\). If \(b\ge1\), the positive inequality
\(a+2b-2<d+1=\sqrt{a^2+b^2-1/4}\) from (8) may be squared. It gives
\[
                 Q(a,b):=3b^2+(4a-8)b-4a+17/4<0.
\tag{12}
\]
For \(a\ge8/5,b\ge1\), Q is nondecreasing in a and strictly increasing in b. But
\[
                             Q(8/5,7/6)=1/15>0.
\]
Equations (9),(12) therefore exclude \(b\ge7/6\), proving (11).

## 2. One exact comparison normal for the full contrary diagonal premise

Suppose, contrary to (4), that \(a-H\le k:=11/10\). Equations (6),(9) give
\[
                         8/5<a<9/5,\qquad H\ge H_*:=a-k>0.
\tag{13}
\]
Define only for scalar comparison
\[
                    X_*=1-a+aH_*/b,\qquad
                    Y_*=1-b+H_*=a-b-1/10.
\tag{14}
\]
The actual configuration and original mean in (5) are not changed.

By (11),(13), \(Y_*>0\). At fixed a,b, the ratio \(X/Y\) increases strictly with H, as in the height source. At fixed a and \(H_*=a-k\), the comparison ratio decreases strictly with b. Indeed,
\[
 \frac{\partial}{\partial b}\left(\frac{X_*}{Y_*}\right)
   =\frac{N}{b^2Y_*^2},
\]
\[
 N=-(a-1)\left(b-\frac{aH_*}{a-1}\right)^2
                  -\frac{aH_*(k-1)}{a-1}<0.
\tag{15}
\]
All denominators are positive. In each complete b range below, the comparison at its largest b has \(X_*>0\). Equation (15) then proves positivity for the entire range as well. Consequently comparison of ratios legitimately compares the corresponding positive normalized first coordinates x.

## 3. The entire case b>=1 is impossible

By (11), the largest comparison b is \(7/6\). At that value, put \(u=a-8/5\in(0,1/5)\); the two comparison components are
\[
 \widehat X=\frac3{35}+\frac45u+\frac67u^2>0,\qquad
 \widehat Y=\frac13+u>0.
\tag{16}
\]
Set \(\lambda=a-34/25=6/25+u\in(0,1)\). Direct expansion gives
\[
 \begin{split}
 &(1-\lambda^2)\widehat X^2-\lambda^2\widehat Y^2\\
 &=\frac{401}{765625}
 +\frac{78056}{2296875}u
 +\frac{1238414}{6890625}u^2
 -\frac{169558}{459375}u^3
 -\frac{53681}{30625}u^4\\
 &\hspace{12mm}-\frac{2112}{1225}u^5-\frac{36}{49}u^6.
 \end{split}
\tag{17}
\]
Every negative higher power is at most its coefficient times
\(u^2(1/5)^{j-2}\). Thus the entire expression is bounded below by
\[
 \frac{401}{765625}
 +\frac{78056}{2296875}u
 +\frac{143471}{6890625}u^2>0.
\tag{18}
\]
This is a whole-interval algebraic bound, with no subdivision.

Positive squaring in (17), then the monotonicities in (15) and H, gives
\[
                              x>a-\frac{34}{25}.
\tag{19}
\]
Hence \(a-1-x<9/25\). Its lower bound is
\(a-1-x>8/5-1-5/7=-4/35>-9/25\), so
\[
                              |a-1-x|<9/25.
\]
The other coordinate is negative: \(b-1<1/6<r\le y\). For \(b\ge1\),
\[
                              |b-1-y|\le y.
\]
Therefore the actual radial-port norm obeys
\[
 \begin{split}
 |P|^2
 &<(9/25)^2+y^2\\
 &=(9/25)^2+1-x^2\\
 &<(9/25)^2+1-(6/25)^2
   =\frac{134}{125}<r_0^2.
 \end{split}
\tag{20}
\]
The last inequality uses \(d>91/100\); its exact reserve is
\[
 (91/100)^2+1/4-134/125=61/10000>0.
\]
This contradicts (5).

## 4. The entire case b<=1 is also impossible

In this case (1),(13) give
\[
                       17/10<a<9/5,\qquad4/5<b\le1.
\tag{21}
\]
The exact squared reserves are
\[
 (79/40)^2-1-(17/10)^2=17/1600>0,
\]
\[
 (79/40)^2-(9/5)^2-(4/5)^2=33/1600>0.
\]

### 4.1. Uniform first-coordinate bound

At the largest comparison value \(b=1\), (14) becomes
\[
                   \widehat X=a^2-\frac{21}{10}a+1>0,
                   \qquad\widehat Y=a-\frac{11}{10}>0.
\tag{22}
\]
Positivity follows directly from (21), or from the formulas below.

Put \(z=9/5-a\in(0,1/10)\) and
\[
 \lambda=a-\frac{313}{250}=\frac{137}{250}-z\in(0,1).
\]
The exact expansion is
\[
 \begin{split}
 &(1-\lambda^2)\widehat X^2-\lambda^2\widehat Y^2\\
 &=\frac{70837}{78125000}
 +\frac{699371}{3125000}z
 -\frac{11442173}{6250000}z^2
 +\frac{164101}{31250}z^3
 -\frac{211197}{31250}z^4
 +\frac{512}{125}z^5-z^6.
 \end{split}
\tag{23}
\]
Discarding the two positive higher terms and bounding each negative
\(z^j\) by \(z(1/10)^{j-1}\) gives the positive whole-interval lower bound
\[
               \frac{70837}{78125000}
                    +\frac{530557}{15625000}z>0.
\tag{24}
\]
Thus (15), the H monotonicity, and positive squaring imply
\[
                             x>a-\frac{313}{250}.
\]
It follows that \(a-1-x<63/250\). The lower bound from (21) and
\(x\le r<5/7\) is \(-1/70\), so
\[
                            |a-1-x|<63/250.
\tag{25}
\]

### 4.2. A coupled second-coordinate bound without any scalar subdivision

Return to the actual H and actual normal in (5). Put
\[
                   \epsilon=b-H\ge0,\qquad\delta=a-b>0.
\]
Then \(Y-X=\epsilon\delta/b\), and the same exact identity as in the height source yields
\[
                 y-r
   =\frac{\epsilon\delta}{b}
                   \frac{x+y}{2L(y+r)}
             \le\frac{\epsilon\delta}{2bL}.
\tag{26}
\]
We have \(L\ge Y=1-b+H\ge\delta-1/10>0\). Moreover,
\[
 \begin{split}
 \frac32 b(\delta-1/10)-\delta
 &=\delta(3b/2-1)-3b/20\\
 &>(17/10-b)(3b/2-1)-3b/20\\
 &=-\frac32b^2+\frac{17}{5}b-\frac{17}{10}>0.
 \end{split}
\tag{27}
\]
The coefficient \(3b/2-1\) is positive by (21). The last quadratic is concave on the entire interval \([4/5,1]\), with positive endpoint values \(3/50\) and \(1/5\). Thus \(\delta<(3/2)bL\), and (26) gives
\[
                            y-r\le\frac34(b-H).
\tag{28}
\]
The weak inequality correctly includes \(H=b\), where both sides vanish.

Since \(b\le1\), the actual second port coordinate is negative. Using (13),(28),
\[
 \begin{split}
 |b-1-y|
 &=1-b+y\\
 &\le1+r-b/4-3H/4\\
 &\le\frac{73}{40}+r-\frac{3a+b}{4}.
 \end{split}
\tag{29}
\]
For fixed R, along this entire range,
\[
 \frac{d}{da}\left(3a+\sqrt{R^2-a^2}\right)
                  =3-a/b>3-\frac{9/5}{4/5}=\frac34>0.
\]
Its smallest a with \(b\le1\) is \(\sqrt{R^2-1}>17/10\).
The full interval from that value to the actual a stays within \(b>4/5\). Consequently
\[
                         3a+b\ge3\sqrt{R^2-1}+1>61/10.
\]
Substitution in (29) proves
\[
                            |b-1-y|<\frac3{10}+\frac1{\sqrt2}.
\tag{30}
\]

The two coordinate estimates now contradict the exact radial norm:
\[
 |P|^2<(63/250)^2+\left(\frac3{10}+\frac1{\sqrt2}\right)^2
                         <r_0^2.
\tag{31}
\]
The final comparison is an exact fixed inequality. Use \(d>91/100\) and \(\sqrt2<99/70\); its remaining positive reserve is
\[
 \frac{10781}{10000}
 -\left(\frac{63}{250}\right)^2-\frac{59}{100}
 -\frac3{10}\frac{99}{70}
                         =\frac{543}{1750000}>0.
\tag{32}
\]

Both b ranges under (13) are impossible. This proves the whole local return-owner inequality (4).

## 5. Full actual-channel join and exact remaining scope

The adjacent bound (3) and the return-owner bound (4) apply to the same original R and the same original return-channel height H. They therefore give
\[
                    m+a-1=(m+H)+(a-H)-1>1,
\]
contradicting the actual reserve-one identity (2).

This excludes the entire A/T strict-turn feature family, including a genuine S-incident mean already at the A vertex and every genuine return mean \(Y\in(0,1]\) at T. Neither comparison in H or b moves a physical port or transmitter; both are scalar inequalities applied to the unchanged original chart. Both individual radial circle weights, all original masks and all three additional squares are retained. The contradiction already occurs in the original six-body core.

Together with the previously accepted A/A, A/M, M/M, O/O, O/T, T/T, O/M and T/M sources, this leaves only the A/O pair in the stated all-strict-turn owner cover. Root and separate independent reviews of this source and its new local dependencies passed. Cases with a unique turn at most \(\pi/2\) remain explicit separate obligations. No unrestricted one-radial parent or global nine-square gate is declared closed.

The scalar inputs are whole-interval identities, monotonicities, concavity and fixed positive rational reserves. There is no sampled pose, angular grid, new computational certificate packet, Lean compilation or CI.

