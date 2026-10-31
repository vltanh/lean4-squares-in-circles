# A radial-incident shared mean has a wide return span, excluding a shared-return partner

Date: October 26, 2026.

**Status: complete analytic local theorem and physical-family join,
accepted after root and separate independent saved-source and scope reviews.**
See REVIEW_C6_RADIAL_SHARED_MEAN_RETURN_SPAN_ROOT_2026_10_26.md and
REVIEW_C6_RADIAL_SHARED_MEAN_RETURN_SPAN_BLOCK_2026_10_26.md.
One convex tangent
and one monotone scalar bound improve the entire original mean domain.
No coefficient packet or angular subdivision is introduced.

Retain the original one-radial all-side alternating C6, with physical
two-circle-corner S, physical-unique B,C, three true unloaded degree-two
side transmitters, all three extra squares, and every original force,
circle weight, mean endpoint, and slider. Work throughout
\[
 K_0=79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1.
\tag{1}
\]
Both unique turns are strictly greater than \(\pi/2\).

**Local mean theorem.** At a unique endpoint whose S-incident interface
is genuinely shared, write its actual return channel horizontally and
use the mean chart below. Its angle and horizontal return span satisfy
\[
                  c>3/5,\qquad A-(c+s)>419/1000>2/5.
\tag{2}
\]

**Whole-family consequence.** Such an endpoint cannot pair with a
unique endpoint which genuinely owns the B-to-C return normal.
Thus the opposite/shared-return plus genuine-S-mean family is impossible.

## 1. The full original mean-root domain

Use only the local chart of
[SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md).
The return application is the opposite vertex and its height is \(H>0\):
\[
 c=\cos\eta,\quad s=\sin\eta,\quad \pi/4\le\eta<\pi/2,
\]
\[
 Z=H+s-c,\quad A=\sqrt{R^2-Z^2},\quad
 a=cA+sZ,\quad b=sA-cZ,\quad t=(s-c)/Z.
\tag{3}
\]
The actual original shared mean is \(\ell=1-tb\in(0,1]\).
Properness and the common moment give
\[
                         a>b>1/2,\qquad a^2+b^2=R^2.
\]
The unchanged radial port has squared norm
\[
 F_M=(a-2)^2+(1-t)^2b^2
                  =r_0^2:=d^2+1/4.
\tag{4}
\]
These local identities do not require a second mean endpoint.

Expanding (4), as in the accepted pointwise root proof, gives
\[
 4a+\{1-(1-t)^2\}b^2=5+2d.
\]
Consequently
\[
 a\le A_*:=\frac{5+2d}{4}<a_{\max}:=\frac{211}{120}<2,
 \qquad a>R/\sqrt2>139/100>64/49.
\tag{5}
\]
We will use \(d>91/100\), whose squared reserve at \(K_0\) is
\(101/40000>0\), and \(d<61/60\), whose upper squared reserve
is \(31/57600>0\).

## 2. A single tangent improves the whole mean-root angle

Put \(u=c/s\) and \(r=b/a\in(0,1)\). The exact mean parameter is
\[
                           t=\frac{1-u}{a-ub}.
\tag{6}
\]
For fixed \(a>b\), the right side decreases in u, its derivative
being \((b-a)/(a-ub)^2<0\).

Suppose \(u\le3/4\). Then
\[
 0<(1-t)b
 \le b-\frac14\,\frac{r}{1-3r/4}.
\tag{7}
\]
The right side is positive because the actual \(t<1\) and the
comparison value of t is no larger.

The function \(r/(1-3r/4)\) is convex for \(0<r<1\).
Its exact tangent at \(r=3/4\) is
\[
 \frac{r}{1-3r/4}\ge\frac{256}{49}r-\frac{108}{49}.
\tag{8}
\]
Thus, with \(K=64/49\),
\[
                    (1-t)b\le b(1-K/a)+27/49.
\tag{9}
\]
The coefficient \(1-K/a\) is positive by (5).

Let \(U=1105/256\). Since \(b^2=R^2-a^2\le U-a^2\), the
right side of (9) is at most
\[
                  q(a)+27/49,\qquad
 q(a)=\sqrt{U-a^2}(1-K/a).
\]
On the whole required a interval,
\[
 q'(a)=\frac{KU-a^3}{a^2\sqrt{U-a^2}}>0,
\]
because
\[
             KU-a_{\max}^3=\frac{17057381}{84672000}>0.
\tag{10}
\]
Also
\[
 (10/9)^2-(U-a_{\max}^2)=5131/518400>0.
\]
Therefore
\[
 (1-t)b<
     (1-K/a_{\max})\,\frac{10}{9}+\frac{27}{49}
                   <\frac{21}{25}.
\tag{11}
\]
The last exact reserve is \(7496/2326275>0\).
This bound applies to the entire assumed domain \(u\le3/4\);
the one tangent in (8) is supported by global convexity.

Equations (4)--(5) and (11) now give
\[
 F_M<(61/100)^2+(21/25)^2.
\]
But the actual radial norm satisfies
\[
 r_0^2>(91/100)^2+1/4,
\]
and the latter minus the preceding upper bound is exactly
\(1/2500>0\). This contradicts (4). Hence \(u>3/4\), or
\[
                              c>3/5,\qquad s<4/5.
\tag{12}
\]
The original endpoint \(\ell=1\) is retained and obeys this bound.

## 3. The original return span has a uniform lower bound

In the actual channel frame the horizontal coordinate of the
opposite return application is \(-m\), where
\[
                    m=A-(c+s)=c(a-1)+s(b-1).
\tag{13}
\]
For fixed R,c,s, increasing a from its actual value to \(A_*\)
decreases the right side of (13), because
\[
       \frac{d}{da}\{c(a-1)+s(\sqrt{R^2-a^2}-1)\}
                       =c-sa/\sqrt{R^2-a^2}<0.
\tag{14}
\]
Here \(a>b\) and \(c\le s\) throughout the comparison interval.

At this comparison endpoint let \(b_*=\sqrt{R^2-A_*^2}\).
The radius relation in (1) gives the exact expression
\[
                   b_*^2=\frac{12d^2+12d-5}{16}.
\]
In particular
\[
                       A_*>341/200,\qquad b_*>199/200.
\tag{15}
\]
For the latter bound, substituting \(d>91/100\) leaves the
positive squared reserve \(21/20000\). This also verifies that
the full interval used in (14) has positive radicals.

Using (12), (14), and (15),
\[
 \begin{split}
 m&\ge c(A_*-1)+s(b_*-1)\\
  &>\frac35\frac{141}{200}-\frac45\frac1{200}
   =\frac{419}{1000}>\frac25.
 \end{split}
\tag{16}
\]
If \(b_*\ge1\), its contribution is already nonnegative;
the displayed lower bound includes the possible \(b_*<1\) case.
This proves the full local mean theorem (2).

## 4. A genuine return owner cannot supply the other endpoint

Suppose the other unique endpoint genuinely owns the actual return
normal. Its S-incident application is then the opposite vertex.
In its reflected inward own axes let its circle corner coordinates
be \(a_T,b_T>1/2\), with
\[
                  a_T^2+b_T^2=R^2,\qquad a_T>b_T.
\tag{17}
\]
The last strict sign follows from the unchanged common moment,
exactly as in the shared-return chart. The actual return application
has horizontal distance \(a_T-1\) from the origin.

The original return reserve one therefore gives
\[
                     m+(a_T-1)=1,\qquad a_T=2-m<8/5.
\tag{18}
\]
By (1),
\[
 b_T^2=R^2-a_T^2>K_0^2-64/25=2145/1600>1.
\tag{19}
\]
Thus both coordinates of its actual opposite vertex Q,
\((a_T-1,b_T-1)\), are positive.

The S-incident unit normal G has strictly positive own-axis
coordinates. Since \(a_T>b_T\), we have
\[
                         Q\cdot G>b_T-1.
\]
Its unchanged reserve-one transmitter puts the radial port at
\(P=Q-G\). Comparing its norm to \(r_0^2=R^2-2d-1\) gives
\[
 \begin{split}
 R^2-2d-1
 &=|P|^2\\
 &<R^2+5-2a_T-4b_T,
 \end{split}
\]
or
\[
                           a_T+2b_T<3+d.
\tag{20}
\]

The opposite strict inequality follows uniformly from (18).
On \(a>R/\sqrt2\), the function
\(a+2\sqrt{R^2-a^2}\) decreases strictly. Thus
\[
                  a_T+2b_T>
                      \frac85+2\sqrt{R^2-\frac{64}{25}}.
\tag{21}
\]
The difference
\[
 \frac85+2\sqrt{R^2-\frac{64}{25}}-(3+d)
\]
increases with R, as is immediate from its two positive-root
derivatives. At \(R=K_0\), it equals
\[
                 \frac{2\sqrt{2145}-\sqrt{5841}-16}{40}>0.
\tag{22}
\]
For an exact comparison,
\[
                    2483^2-32^2\cdot5841=184105>0
\]
first gives \(2483>32\sqrt{5841}\), and then
\[
 (2\sqrt{2145})^2-(\sqrt{5841}+16)^2
                         =2483-32\sqrt{5841}>0.
\]
Both quantities squared are positive. This proves (22), so
(21) contradicts (20).

The whole genuine-return-owner plus genuine-S-mean physical family
is impossible, including every original mean endpoint at either
unique square.

## 5. Scope

The local angle and span bounds apply to every strict-turn
S-incident genuine mean, independently of the other endpoint's
feature. Their application in Section 4 excludes a full remaining
mixed owner family, with the original one-radial mask and both
individual radial weights unchanged.

The mixed opposite/adjacent families, with or without an owner on
the return at the opposite endpoint, still require their own
arguments. Cases with a unique turn at most \(\pi/2\) remain
separate. No unrestricted one-radial or global nine-square gate is
declared closed here. All additional physical squares are retained;
the contradiction occurs in the actual six-body core.

