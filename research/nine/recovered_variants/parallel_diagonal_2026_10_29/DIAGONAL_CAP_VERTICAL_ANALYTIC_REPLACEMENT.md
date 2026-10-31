# A monotonicity proof of the whole vertical diagonal-cap inequality

Date: October 27, 2026.

**Status: complete analytic replacement, pending independent acceptance.**
The original source is
`SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md` at PR11 head
`8680a4b9204c0d6fb82a8d052ece5bb52aa9b6c8`.
This note replaces its Certificate IV on the entire original closed
parameter rectangle. Its unchanged geometric reduction then proves the
complete vertical center-cap inequality, including the auxiliary
endpoint use in the source's Section 6.

The result removes the remaining 126 Bernstein coefficient comparisons.
Together with
`DIAGONAL_CAP_THREE_CERTIFICATES_ANALYTIC_REPLACEMENT.md`,
it replaces all 20+20+36+126=202 comparisons in that original packet.
The historical formulas, tables, scripts and reviews remain intact.

## 1. The exact target and a larger positivity domain

Put
\[
 r=\sqrt2,\qquad A=2+r,\qquad s=r/2,\qquad c=A-a,
\]
\[
 C=c(b+c),\qquad
 N=(c-1)\,[b(b+c)+A(a-c)].
\]
Retain exactly the original polynomial
\[
 \mathcal P(a,b)=
 \left(a+b+\frac3{16}+\frac{b^2}{4}-a^2\right)C^2
       +\left[(a-b+s-3/2)C+N\right]^2.
 \tag{1}
\]
Define
\[
 u(b)=2-\frac{b^2}{10},\qquad
 \ell(b)=\frac{41}{20}-\frac{3b}{10}.
\]

**Polynomial theorem.** The following two entire regions satisfy
\(\mathcal P>0\):
\[
 \left\{b\ge\frac23,\ a\le u(b)\right\},
 \tag{2}
\]
\[
 \left\{\frac12\le b\le\frac23,\quad
                   \ell(b)\le a\le u(b)\right\}.
 \tag{3}
\]
There is no lower bound on a, nor an upper bound on b, in (2).
Only the local interpretation of C and N will later require their
physical domain. The two-region polynomial theorem is an algebraic
statement independent of circle masks, means, radius or graph type.

As in the other three replacements, the only radical bracket used is
\[
 \frac{140}{99}<r<\frac{99}{70}.
 \tag{4}
\]
The two squared integer reserves are 2 and 1. In particular
\(7/5<r<3/2\). All differentiations and expansions below are exact
identities over \(\mathbb Q(r)\).

## 2. The whole upper region decreases in a

Set \(v=u(b)-a\ge0\). Direct differentiation of (1) gives
\[
 -\partial_a\mathcal P(u(b)-v,b)
                         =\sum_{j=0}^4D_j(b)v^j,
 \tag{5}
\]
where
\[
\begin{aligned}
D_0(b)={}&-4-\frac r2
 +\left(-\frac{83}{4}+14r\right)b
 +\left(\frac{61}{20}+\frac{43r}{40}\right)b^2\\
&+\left(14-\frac{83r}{40}\right)b^3
 +\left(\frac{851}{400}+\frac{1501r}{400}\right)b^4
 +\left(\frac{213}{800}+\frac{63r}{50}\right)b^5\\
&+\left(\frac{1463}{4000}+\frac{77r}{500}\right)b^6
 +\left(\frac3{40}+\frac r{125}\right)b^7
 +\left(\frac3{500}+\frac{3r}{2000}\right)b^8,\\[2mm]
D_1(b)={}&-\frac{219}{2}+12r
 +\left(100-\frac{203r}{4}\right)b
 +\left(\frac{1307}{40}+\frac{481r}{20}\right)b^2\\
&+\left(-\frac{27}{40}+\frac{111r}{5}\right)b^3
 +\left(\frac{3029}{400}+\frac{231r}{50}\right)b^4
 +\left(\frac{21}{10}+\frac{6r}{25}\right)b^5
 +\left(\frac{23}{100}+\frac{3r}{50}\right)b^6,\\[2mm]
D_2(b)={}&114-\frac{339r}{4}
 +\left(-\frac{267}{8}+96r\right)b
 +\left(\frac{1869}{40}+\frac{231r}{5}\right)b^2\\
&+\left(\frac{39}{2}+\frac{12r}{5}\right)b^3
 +\left(\frac{33}{10}+\frac{9r}{10}\right)b^4,\\[2mm]
D_3(b)={}&\frac{303}{4}+154r+(60+8r)b+(21+6r)b^2,\\
D_4(b)={}&50+15r.
\end{aligned}
\tag{6}
\]
For j=1,2,3 every nonconstant coefficient is positive already from
\(7/5<r<3/2\), so these polynomials are increasing for \(b\ge0\).
For \(D_0\), the linear coefficient exceeds \(-1\), the quadratic
coefficient exceeds 4, and all higher coefficients are positive.
Thus
\[
 D_0'(b)>-1+8b>0\qquad(b\ge2/3).
\]
The bounds in (4) give the following fixed endpoint values:
\[
\begin{aligned}
D_0(2/3)
 &=-\frac{6472201}{546750}+\frac{175279}{18225}r
   >\frac{44}{25},\\
D_1(2/3)
 &=-\frac{486946}{18225}-\frac{43949}{12150}r
   >-\frac{796}{25},\\
D_2(2/3)
 &=\frac{64231}{540}+\frac{121}{180}r>119,\\
D_3(2/3)
 &=\frac{1501}{12}+162r>354,\qquad D_4>0.
\end{aligned}
\tag{7}
\]
For example the first two rational lower gaps are
\(52727/18042750\) and \(14467/2551500\).
Monotonicity therefore gives, for every \(b\ge2/3,v\ge0\),
\[
 -\partial_a\mathcal P
 >\frac{44}{25}-\frac{796}{25}v+119v^2+354v^3.
 \tag{8}
\]
The one cubic supporting-line identity
\[
 v^3-\frac3{100}v+\frac1{500}
        =\left(v-\frac1{10}\right)^2\left(v+\frac15\right)\ge0
\]
turns (8) into
\[
 -\partial_a\mathcal P
 >\frac{263}{250}-\frac{1061}{50}v+119v^2>0.
 \tag{9}
\]
The last quadratic is positive on the entire real line, since
\[
 4\cdot119\cdot\frac{263}{250}
             -\left(\frac{1061}{50}\right)^2
          =\frac{126159}{2500}>0.
\]
Thus \(\mathcal P\) is strictly decreasing in a on the whole region
(2), and
\[
                \mathcal P(a,b)\ge U(b):=\mathcal P(u(b),b).
 \tag{10}
\]

## 3. One positive quadratic controls the entire upper boundary

Expansion of the exact boundary value in (10) gives
\[
\begin{aligned}
U(b)={}&\frac{47}{4}-6r
 +\left(-4-\frac r4\right)b
 +\left(\frac{19}{40}-\frac{61r}{20}\right)b^2\\
&+\left(-\frac{83}{40}+\frac{17r}{5}\right)b^3
 +\left(\frac{941}{400}+\frac{19r}{400}\right)b^4
 +\left(\frac9{10}+\frac{37r}{800}\right)b^5\\
&+\left(\frac{699}{8000}+\frac{907r}{4000}\right)b^6
 +\left(\frac{151}{8000}+\frac{47r}{1000}\right)b^7\\
&+\left(\frac{1983}{160000}+\frac{77r}{20000}\right)b^8
 +\left(\frac1{500}+\frac r{5000}\right)b^9
 +\left(\frac1{8000}+\frac{3r}{100000}\right)b^{10}.
\end{aligned}
\tag{11}
\]
Every coefficient of degree at least three is positive, so
\(U'''(b)>0\) for \(b\ge0\). The exact values at \(2/3\) are
\[
\begin{aligned}
U(2/3)
 &=\frac{1368778373}{147622500}
       -\frac{796734391}{123018750}r>\frac1{10},\\
U'(2/3)
 &=-\frac{29144642}{12301875}
       +\frac{8669813}{16402500}r>-\frac53,\\
\frac12U''(2/3)
 &=\frac{20452043}{3645000}
       +\frac{8794417}{1822500}r>12.
\end{aligned}
\tag{12}
\]
These follow by (4). Since \(U''\) is increasing, integration or
Taylor's formula with a nonnegative remainder gives, for
\(x=b-2/3\ge0\),
\[
 U(b)>\frac1{10}-\frac53x+12x^2
      =12\left(x-\frac5{72}\right)^2+\frac{91}{2160}>0.
 \tag{13}
\]
Equations (10)--(13) prove the polynomial theorem on the unbounded
region (2). No interval subdivision or root isolation is used.

We will also need U on the lower interval. The same exact values give
\(U'(2/3)<0\), and
\[
 U''(1/2)=\frac{21673549}{5120000}
                   +\frac{12412059}{2560000}r>0.
\]
Because \(U''\) is increasing, \(U'\) is increasing on
\([1/2,2/3]\). Its right endpoint is negative, so U is decreasing
there and
\[
                  U(b)\ge U(2/3)>\frac1{10}.
 \tag{14}
\]

## 4. The lower linear boundary has one uniform convexity bound

Put \(V(b)=\mathcal P(\ell(b),b)\). Its exact expansion is only degree
six:
\[
\begin{aligned}
V(b)={}&\frac{6045947}{512000}-\frac{19059933}{3200000}r\\
&+\left(-\frac{184861}{80000}-\frac{90671}{64000}r\right)b\\
&+\left(-\frac{8308477}{640000}+\frac{245077}{80000}r\right)b^2\\
&+\left(\frac{47391}{5000}-\frac{99217}{40000}r\right)b^3
 +\left(\frac{432037}{160000}+\frac{153359}{40000}r\right)b^4\\
&+\left(\frac{3081}{5000}+\frac{30849}{100000}r\right)b^5
 +\frac{1521}{40000}b^6.
\end{aligned}
\tag{15}
\]
Its coefficients of degree at least three are positive, so
\(V'''(b)>0\) for \(b\ge0\). In particular
\[
 V''(b)\ge V''(1/2)
       =\frac{121831}{10000}+\frac{27397}{2500}r>27
                 \qquad(1/2\le b\le2/3).
 \tag{16}
\]
The following exact fixed values use the same bracket (4):
\[
 V(3/5)=\frac{327817815931}{40000000000}
           -\frac{57183236451}{10000000000}r
                       >\frac{107}{1000},
\]
\[
 V'(3/5)=-\frac{4902662531}{1000000000}
           +\frac{618603509}{200000000}r,\qquad
                         |V'(3/5)|<\frac{27}{50}.
 \tag{17}
\]
For example the lower-value reserve in the first inequality is
\(1542740287/1400000000000\), so no narrow decimal sign is used.

Writing \(y=b-3/5\), integration of (16) in either direction gives
\[
\begin{aligned}
 V(b)&>\frac{107}{1000}-\frac{27}{50}|y|+\frac{27}{2}y^2\\
     &\ge\frac{107}{1000}-\frac{(27/50)^2}{54}
       =\frac{127}{1250}>\frac1{10}.
\end{aligned}
\tag{18}
\]
This proves the whole lower boundary in (3), including both endpoints.

## 5. A uniform upper-curvature estimate fills the whole lower strip

We now prove
\[
              \partial_a^2\mathcal P(a,b)<6
\quad\text{on}\quad
 37/20\le a\le2,\quad1/2\le b\le2/3.
 \tag{19}
\]
Two useful exact derivative identities from (1) are
\[
\begin{aligned}
\partial_a^4\mathcal P
 ={}&\frac{5709}{2}+1644r+(360+48r)b+6b^2
                   -(1200+360r)a,\\
\partial_b\partial_a^3\mathcal P
 ={}&-\frac{2613}{4}-288r-120b-9b^2
                         +a(360+48r+12b).
\end{aligned}
\tag{20}
\]
On the box in (19), the first is positive and the second is negative.
For the first, discard its positive b terms and use \(a\le2\) and
\(7/5<r<3/2\); the lower bound is \(16761/10>0\).
For the second, discard its negative b terms and use the same radical
bounds and \(b\le2/3\); the upper bound is \(-3529/20<0\).

Consequently \(\partial_a^3\mathcal P\) is increasing in a and
decreasing in b. Its maximum is bounded by
\[
 \partial_a^3\mathcal P(2,1/2)
                 =-207+\frac{147}{2}r<0.
\]
Thus \(\partial_a^2\mathcal P\) is decreasing in a.
Also \(\partial_b\partial_a^2\mathcal P\) is decreasing in a, and
at \(a=2\) it equals
\[
 100-\frac{203r}{4}
     +\left(\frac{79}{4}+82r\right)b
     +(18+9r)b^2+2b^3>0.
 \tag{21}
\]
Therefore \(\partial_a^2\mathcal P\) is increasing in b.
Its maximum on the box is attained at \(a=37/20,b=2/3\), where
\[
 \partial_a^2\mathcal P(37/20,2/3)
                  =\frac{363989}{129600}+\frac{7237}{3600}r<6.
 \tag{22}
\]
The last inequality already follows from \(r<3/2\).
This proves (19).

The two endpoints in (3) lie in this box. Their separation is
\[
 \Delta(b)=u(b)-\ell(b)
            =-\frac1{20}+\frac{3b}{10}-\frac{b^2}{10},
\]
which is positive and increasing on \([1/2,2/3]\); hence
\[
        0<\Delta(b)\le\Delta(2/3)=\frac{19}{180}<\frac{11}{100}.
 \tag{23}
\]
For fixed b, let \(L_b(a)\) be the affine interpolation of
\(\mathcal P(\ell(b),b)=V(b)\) and
\(\mathcal P(u(b),b)=U(b)\). The function
\[
 \mathcal P(a,b)-L_b(a)-3(a-\ell(b))(a-u(b))
\]
has negative second derivative by (19), and is zero at both endpoints.
Concavity makes it nonnegative throughout. Equations (14),(18),(23)
therefore give
\[
\begin{aligned}
 \mathcal P(a,b)
 &\ge L_b(a)-3(a-\ell(b))(u(b)-a)\\
 &>\frac1{10}-\frac34\Delta(b)^2
  >\frac1{10}-\frac34\left(\frac{11}{100}\right)^2
   =\frac{3637}{40000}>0.
\end{aligned}
\tag{24}
\]
This proves the whole lower strip (3). It is a single curvature
comparison on the entire strip, with both boundary functions covered
by their own whole-interval arguments.

## 6. The exact original rectangle is included

The source's Certificate IV uses
\[
 \frac12\le b\le\frac{61}{60},\qquad
 a_0(b)\le a\le u(b),\qquad
 a_0(b)=\frac{3947}{2000}-\frac4{15}b^2.
 \tag{25}
\]
This is exactly its affine rectangle map, because
\[
 a_0(b)+\frac{53}{2000}+\frac{b^2}{6}
                         =2-\frac{b^2}{10}=u(b).
\]
For \(b\ge2/3\), all of (25) is contained in (2).

For \(1/2\le b\le2/3\), the exact difference
\[
 a_0(b)-\ell(b)
                =-\frac{153}{2000}+\frac{3b}{10}-\frac4{15}b^2
\]
is concave in b. Its two endpoint values are
\[
 \frac{41}{6000}>0,\qquad\frac{269}{54000}>0.
\]
It is therefore positive throughout, so the rest of (25) is contained
in (3). This includes every original rectangle endpoint and every
point of its interior. No physical inequality has been strengthened,
and no part of the original balanced-cap parameter domain is omitted.

In fact (13),(24) give the explicit uniform bound
\[
                  \mathcal P(a,b)>\frac{91}{2160}>0
\quad\text{throughout the original rectangle.}
 \tag{26}
\]

## 7. Geometric caller and complete packet retirement

The source's original Section 5 has already proved, with its unchanged
balanced endpoint hypotheses, \(C>0\),
\[
 h\ge h_{\rm rat}=N/C,
\]
\[
 M^2\le a^2+\frac34b^2-a+\frac1{16},
 \qquad M=\sqrt{R^2-1/4}-1/2,
\]
and positivity of
\[
 a+h_{\rm rat}-b+s-\frac32.
\]
Dividing (1) by \(C^2>0\), applying these same estimates and then
increasing \(h_{\rm rat}\) to h proves exactly
\[
 \sqrt{M^2-(b+1/2)^2}
               <h+a-1+s-(b+1/2)
\]
whenever \(b\le\sqrt{R^2-1/4}-1\). Its right side is positive.
The source's Section 6 uses this same full scalar result both at the
actual endpoint tuple and at its auxiliary tuple. Both remain covered:
the proof above establishes the entire original rectangle, not only
tuples sampled from one physical configuration or \(R\ge2\) tuples.

Together with the unchanged horizontal-row proof and the separate
three-inequality replacement for Certificates I--III, this gives the
same complete diagonal exterior-pocket obstruction with no Bernstein
table dependency. The accepted current all-mask theorem
`FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md`, Section 2, imports
this balanced argument with its physical half-mask endpoints. It still
does so without any added restriction. Its other endpoint sectors are
unchanged. The current
`GENERAL_SIDE_CHANNEL_CAP_CENTRAL_INJECTION_BOUND.md`
therefore obtains the same diagonal-pocket input.

The count after independent acceptance of both analytic sources is:

| Original balanced-cap certificate | Former comparisons | Current Bernstein comparisons |
| --- | ---: | ---: |
| I, first E-owned sector | 20 | 0 |
| II, second E-owned sector | 20 | 0 |
| III, W-owned sector | 36 | 0 |
| IV, complete vertical cap | 126 | 0 |
| **Entire packet** | **202** | **0** |

The first replacement source records the intermediate 76-removal,
126-retained stage. This later theorem supplies precisely the
previously retained part; the two stages are not added to the packet
a second time. All displayed exact differentiation, expansion,
radical and rational comparisons remain part of the analytic proof.
The claim is removal of the old coefficient-table dependency, not
absence of finite arithmetic.

This does not retire any separate shared-T 1080 packet globally,
recount the old 1559/45/209/288 packets or the 12 matrix certificates,
or remove the five fixed charges and one derivative enclosure in
the same-nine-square \(R>2\) theorem. It closes no new graph gate by
itself and does not prove the unrestricted sharp bound or equality
classification. No historical file was altered, and no sampled pose,
numerical optimization, adaptive subdivision, Lean run or CI is used.
