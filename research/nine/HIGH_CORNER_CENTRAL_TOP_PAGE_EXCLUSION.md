# A high corner central contact excludes every top-side boundary return

**Status: complete new analytic candidate, freshly reconstructed and saved after the workspace rollback; independent full review is pending.** This file did not exist with a frozen hash before the rollback. It is not a claimed byte restoration of another manuscript. The five original inputs in Section 15 are present and their hashes were checked on the restored workspace. Recent continuation papers are provenance only, not logical premises of the proof below.

The theorem keeps the whole central side position, all angles, the actual positive two-force equations at the page body, both possible physical types of the top contact, and every actual shared-contact mean. It does not use any force equation at the central boundary body. In particular it makes no degree-two assumption at a true loaded hub.

## 1. Full local theorem and certificate convention

Let H,K,C be pairwise interior-disjoint physical unit squares contained in the same origin-centered disk of radius R. Assume

\[
 \frac{17}{4}\le R^2\le\frac{1105}{256},\qquad
 d=\sqrt{R^2-\frac14}-1<\frac{61}{60},\qquad
 R<\frac{25}{12}.
 \tag{1}
\]

Both K and C physically touch the circle. The root is

\[
 H=[h-1,h]\times[G-1,G],\qquad
 -\frac1{60}<h\le0,\qquad \frac{89}{120}<G<1.
 \tag{2}
\]

Its actual central application with K is its upper-right vertex

\[
 R_0=(h,G).
\]

For some actual orthonormal frame and actual side position,

\[
 \begin{split}
 U&=(c,s),\qquad V=(s,-c),\qquad c,s>0,\quad c^2+s^2=1,\\
 K&=R_0+[0,1]U+[-a_0,1-a_0]V,\qquad 0\le a_0<1.
 \end{split}
 \tag{3}
\]

The actual normal N from H to K satisfies

\[
 N\cdot U>0,\qquad N\cdot V\ge0.
 \tag{4}
\]

This includes a K-owned central side contact, with N=U and 0<a_0<1, and the free central endpoint a_0=0 with N strict in the K vertex cone. No side position or actual normal is changed in what follows.

C has exactly one physical circle corner z_C, with positive circle load, and has exactly the two positive pair forces HC and CK. The HC normal from H to C is E_2=(0,1), owned by the top side of H. The CK pair physically touches and has positive force. There are two HC possibilities:

* A singleton HC intersection is a strict lowest vertex of C in the relative interior of H's top side.
* A positive-length HC intersection has the full actual mean on its shared segment.

These are precisely the owned-contact conventions of the physical certificate. At a point-only vertex/vertex intersection the selected normal is strict in both vertex cones, so that case is not relabeled as an H-owned side contact. If both HC and CK intersections are singletons, assume the original compatible fixed-point unique-circle-corner selection has already been made before stress extraction. Equivalently, an application outside that certificate framework may supply the resulting actual CK side-owner premise directly. A shared CK is treated geometrically and does not require any selection of its mean.

**Theorem 1.1.** No such configuration exists.

The degrees and forces of H and K are arbitrary. Additional squares, positive contacts at H or K, circle weight endpoints at K, and the other units in an original nine-square configuration remain present. The only degree-two law used is the genuine one at C. The physical triangle used below is H-K-C. There is no additional neighbor edge or extra normal sign premise.

## 2. Actual proper concurrence and the first K corner reduction

Orient w from C to K, let T be the actual HC application, and let Z be the actual CK application. With the actual positive weights, the C force equation is

\[
 \kappa z_C=\omega E_2-\gamma w,
 \qquad \kappa,\omega,\gamma>0.
 \tag{5}
\]

The boundary-neighbor version of proper concurrence, Lemma 2.1 of `TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, applies because K touches the circle. Since C has a unique physical circle corner, its genuine concurrence lies in C. Thus

\[
 q_C=r z_C=T+\ell E_2\in C,\qquad
 Z-q_C=\ell_K w,\qquad
 0<r\le1,\quad\ell,\ell_K\ge0.
 \tag{6}
\]

The coefficient r is at most one because each own-frame circle-corner coordinate is strictly greater than one half; a positive dilation beyond that corner is outside C. Formula (6) uses the unchanged actual means, including endpoints of shared segments.

Set S=R_0-a_0V. The two minimum-U corners of K are R_0-a_0V and R_0+(1-a_0)V. Each lies at distance at most one from R_0. Since

\[
 |R_0|^2<1+\frac1{3600}<\left(\frac{61}{60}\right)^2,
\]

their norms are strictly below 121/60, and

\[
 \frac{17}{4}-\left(\frac{121}{60}\right)^2
   =\frac{659}{3600}>0.
 \tag{7}
\]

Consequently any physical circle corner of K must be one of

\[
 K_1=R_0+U-a_0V,\qquad
 K_2=R_0+U+(1-a_0)V.
 \tag{8}
\]

No uniqueness of K's circle corner is asserted or needed.

## 3. The entire shared HC contact is impossible

Write the actual C square and actual mean as

\[
 C=[l,l+1]\times[G,G+1],\qquad
 T=(x_0,G),\quad h-1\le x_0\le h\le0.
 \tag{9}
\]

A lower C corner cannot touch the circle: its positive height G would make the corner one unit above it farther from the origin. Thus the unique circle corner is on the top side. Equation (6) gives r(z_C)_x=x_0\le0. A unique circle corner has nonzero horizontal coordinate of magnitude strictly greater than one half. Hence x_0=0 is impossible, and the actual circle corner is

\[
 z_C=(l,G+1),\qquad l<-\frac12.
 \tag{10}
\]

The x component of (5) gives w_x>0. Since C owns its CH side with outward normal -E_2, the physical triangle side-normal theorem gives w_y\le0.

If w_y=0, then w=E_1. Its minimum point on K is S, while the maximum-x support of C is l+1. Therefore

\[
 l+1=h-a_0s.
 \tag{11}
\]

If w_y<0, the C application is its bottom-right corner at height G. Now w\cdot V>0. According as w\cdot U is positive, negative, or zero, K's minimum-w support is S, S+U, or the whole side S+[0,1]U. Every such point has height at least G+a_0c. For a_0>0 no contact at height G is possible. At a_0=0 the only point of these supports with height G is S=R_0; again (11) holds. This covers the entire actual normal cone and every original mean in (9).

Thus every surviving shared-HC row has the actual circle corner

\[
 z_C=(h-a_0s-1,G+1).
 \tag{12}
\]

Direct expansion, using c^2+s^2=1, gives

\[
\begin{split}
 D_1&:=|z_C|^2-|K_1|^2\\
 &=-2h(1+c)+1+2a_0s-a_0^2c^2
          +2G(1-s-a_0c),\\
 D_2&:=|z_C|^2-|K_2|^2\\
 &=-2h(1+c+s)+2G(1-s+c)
          +2a_0(1+s-Gc)-a_0^2c^2.
\end{split}
 \tag{13}
\]

Both are concave quadratics on the full a_0 interval [0,1]. At zero their displayed expressions are positive. At one,

\[
\begin{split}
 D_1(1)&\ge s^2+2s+2G(1-s-c)\\
       &>s^2+2s+2(1-s-c)=(1-c)(3+c)>0,\\
 D_2(1)&=-2h(1+c+s)+2G(1-s)+2+2s-c^2>0.
\end{split}
 \tag{14}
\]

The strict inequality in the first line uses c+s>1 and G<1; h=0 is retained. Concavity proves both differences positive at every actual a_0. The two other K corners were already inside the disk by (7). This contradicts K touching the circle. Shared HC is therefore completely excluded.

## 4. The complete singleton C circle chart

For singleton HC, the strict relative-interior application and the whole C frame can be written

\[
\begin{split}
 T&=(-z,G),\qquad 0<z<1-h,\qquad 0<z+h<1,\\
 e&=(-q,p),\qquad f=(p,q),\qquad p,q>0,\quad p^2+q^2=1,\\
 C&=T+[0,1]e+[0,1]f.
\end{split}
 \tag{15}
\]

The point T belongs to H and cannot be a circle point shared with C. The opposite C corner cannot be the circle corner either. Indeed, if z_C=T+e+f has height Z_y, (6) implies r\ge G/Z_y and r\le1. Its horizontal coordinate satisfies T_x=r(z_C)_x, so

\[
 2=|z_C-T|^2
 \le\left(1-\frac{G}{Z_y}\right)^2R^2
 \le(R-G)^2
 <\left(\frac{161}{120}\right)^2<2.
 \tag{16}
\]

The last reserve is 2879/14400. The remaining adjacent corner T+f cannot be a circle point: its minimum-e coordinate equals T\cdot e=zq+Gp>0, whereas a circle corner at a minimum side must have that own coordinate at most -1/2. Therefore the actual circle corner is

\[
 z_C=T+e=(-z-q,G+p).
 \tag{17}
\]

Define the actual own-frame coordinates

\[
 A=Gp+zq>0,\qquad B=zp-Gq.
\]

Physical uniqueness at the minimum-f circle corner gives B>1/2. The exact radius is

\[
 R^2=(A+1)^2+B^2=(z+q)^2+(G+p)^2,
 \qquad A<d<\frac{61}{60}.
 \tag{18}
\]

Equation (6) now determines the actual concurrence, without any alteration of a contact point:

\[
 q_C=\frac{z}{z+q}z_C,
 \qquad\ell=\frac{B}{z+q}>0.
 \tag{19}
\]

In particular the two C applications cannot coincide. Otherwise the two nonparallel contact lines in the proper-concurrence lemma would meet at T, contradicting (19). When CK too is singleton, the complete compatible fixed-application selection therefore makes CK side-owned. The radial-D coincident exception does not occur. When CK is shared it already has a physical side owner, and its full mean stays in place.

## 5. Uniform C angle and the full second-contact support cover

Since G=Ap-Bq and A<d, B>1/2,

\[
 G<dp-\frac q2.
 \tag{20}
\]

If q\ge39/100, then p\le\sqrt{8479/10000}<921/1000, and

\[
 dp-q/2<\frac{14827}{20000}<\frac{89}{120}.
\]

The two exact squared/height reserves are 341/1000000 and 19/60000. This contradicts (2). Hence

\[
 0<q<\frac{39}{100},\qquad p>\frac{23}{25}.
 \tag{21}
\]

For the latter inequality use 8479/10000-(23/25)^2=3/2000. Set

\[
 F=z(p-q)-Gq-q^2
   =B(1-pq)-(A+1)q^2.
 \tag{22}
\]

Using p\le1-q^2/2, equations (18) and (21) give

\[
\begin{split}
 F&>J(q):=\frac12-\frac q2+\frac{q^3}{4}-\frac{121}{60}q^2,\\
 J(q)&>J(39/100)=\frac{52379}{4000000}>0.
\end{split}
 \tag{23}
\]

The derivative J'=-1/2+3q^2/4-(121/30)q is negative on [0,39/100]; the crude upper bound -1/2+3(39/100)^2/4<0 suffices.

Taking the f component of (5), and using z_C\cdot f=-B, proves w\cdot f>0. Thus the actual maximum-w support of C has the exhaustive cover:

| Sign of w\cdot e | Actual C support |
|---|---|
| negative | the vertex T+f |
| positive | the vertex T+e+f, whose height exceeds G+1 |
| zero | w=f and the entire side T+f+[0,1]e |

In the first row, equation (19) gives the full proper-ray displacement

\[
 (T+f)-q_C=\left(p,-\frac{F}{z+q}\right).
 \tag{24}
\]

It is strictly rightward and downward. No force line is replaced by an auxiliary point.

## 6. Every C-owned CK, including shared CK, is excluded

If C owns CK, the only own-axis normal compatible with w\cdot f>0 is w=f. Also f\cdot U=pc+qs>0.

If f\cdot V<0, K's minimum-f support point is R_0+(1-a_0)V, strictly below height G. It cannot meet C, which lies at height at least G.

If f\cdot V\ge0, its entire minimum-f support lies on

\[
 f\cdot Z=f\cdot R_0-a_0(f\cdot V).
\]

This includes the whole tied K side when f\cdot V=0. On C the maximum-f support is f\cdot T+1. Equality therefore requires

\[
 p(z+h)=1+a_0(ps-qc)\ge1.
 \tag{25}
\]

But z+h<1 and p<1. This is a contradiction. The calculation uses only the actual supporting lines and covers every mean on a shared CK segment.

## 7. Every K-owned CK except one axis is excluded

At K the actual HK outward normal is -N and the actual CK outward normal is -w. Since the latter is K-owned, the physical H-K-C triangle theorem gives

\[
 w\cdot N\ge0.
 \tag{26}
\]

By (4), the exhaustive K-axis possibilities are U,V,-V; -U is excluded. In particular -V has not been discarded through an unrelated tip-edge sign.

If w=U, then w\cdot e=sp-cq=f\cdot V. If this is positive, C's application has height greater than G+1, whereas K's entire minimum-U side has maximum height G+a_0c<G+1. If it is zero, w=f, already excluded by the physical support calculation (25). If it is negative, (24) requires a strictly downward w, contradicting the positive height component of U.

If w=-V, then w\cdot e=sq+cp>0. The alternative w\cdot f\le0 is already impossible by Section 5. Otherwise C's application again has height greater than G+1. K's minimum-(-V) side has maximum height

\[
 G-(1-a_0)c+s<G+1,
\]

another contradiction.

Only w=V remains. Here w\cdot e=-sq-cp<0, so the actual C application is T+f. It lies on K's minimum-V side S+[0,1]U. Thus, with its actual side position \zeta,

\[
 T+f=S+\zeta U,\qquad
 \zeta s=q-a_0c,\qquad
 z+h=p-kq+\frac{a_0}{s},
 \quad k=\frac cs.
 \tag{27}
\]

The strict singleton owner convention gives 0<\zeta<1; the subsequent estimates also retain the closed endpoint inequalities. Equating the direction in (24) with V yields the essential actual C2 slope identity

\[
 k=\frac{F}{p(z+q)}>0.
 \tag{28}
\]

Moreover,

\[
 p(z+q)-F=q(z+G+p+q)>0.
\]

Consequently

\[
 0<k<1,\qquad c<s.
 \tag{29}
\]

## 8. The actual central offset is below one third

The whole relative-interior inequality z+h<1 and equation (27) imply

\[
 a_0<s(1-p)+cq
     =q\left(c+s\frac{q}{1+p}\right).
 \tag{30}
\]

Put r_0=q/(1+p)<13/64 by (21). On 0<c<1/\sqrt2, the function

\[
 c+r_0\sqrt{1-c^2}
\]

is increasing, since its derivative is 1-r_0c/s>0. Therefore

\[
 a_0<\frac{3003}{6400\sqrt2}<\frac13.
 \tag{31}
\]

The last comparison is exactly

\[
 2\cdot6400^2-9\cdot3003^2=757919>0.
\]

This is a restriction on the original actual side position, not a choice of another representative of the side.

Now |R_0|<601/600, because the squared reserve over 1+1/3600 is 367/120000. Since U,V are orthogonal,

\[
 |U-a_0V|<\frac{\sqrt{10}}3<\frac{19}{18}.
\]

Thus

\[
 |K_1|<\frac{3703}{1800}<\frac{\sqrt{17}}2\le R.
 \tag{32}
\]

The exact reserves are

\[
 (19/18)^2-10/9=1/324,\qquad
 17/4-(3703/1800)^2=57791/3240000.
\]

Only K_2 could still be a physical circle corner.

## 9. The actual slope is uniformly greater than one tenth

Suppose k\le1/10. Since a_0\ge0 and h\le0, (27) gives

\[
 z\ge p-kq-h\ge p-q/10,
 \qquad z+q\ge p+9q/10.
 \tag{33}
\]

First take 1/3\le q<39/100. The identity 1-p=q^2/(1+p), together with p>23/25, gives

\[
 p>1-\frac{25}{48}q^2.
\]

The actual radius in (18) is strictly greater than

\[
 (p+9q/10)^2+(p+89/120)^2>P(q),
\]

where the explicit concave cubic is

\[
 P(q)=2+\left(\frac{89}{120}\right)^2+\frac{89}{60}
      +\frac95q-\frac{28261}{14400}q^2-\frac{15}{16}q^3.
 \tag{34}
\]

Its second derivative is negative on the full interval. The endpoint reserves are

\[
 P(1/3)-\frac{1105}{256}=\frac{33287}{518400}>0,
 \qquad
 P(39/100)-\frac{1105}{256}=\frac{4671227}{72000000}>0.
 \tag{35}
\]

Concavity contradicts R^2\le1105/256 throughout this entire interval.

It remains to take 0<q<1/3. Solving the unchanged slope identity (28) for G gives

\[
 G=z\left(\frac{p(1-k)}q-1\right)-q-kp.
 \tag{36}
\]

The coefficient of z is positive: p(1-k)-q>(23/25)(9/10)-39/100>0. The expression decreases with k. Substitute (33) and k\le1/10, then use p\le1-q^2/2, to obtain

\[
 G>\frac9{10q}-\frac95q-\frac{119}{100}
            +\frac{119}{200}q^2.
 \tag{37}
\]

The right side is decreasing on (0,1/3]. Its endpoint is

\[
 \frac{1757}{1800}>\frac{39}{40},
 \qquad\frac{1757}{1800}-\frac{39}{40}=\frac1{900}.
\]

Also p>\sqrt{8/9}>14/15. Equations (18) and (33) then give

\[
 R^2>\left(\frac{14}{15}\right)^2+
          \left(\frac{229}{120}\right)^2
      >\frac{1105}{256},
 \tag{38}
\]

with exact reserve 2263/11520. This excludes the second whole interval as well. We have proved

\[
                         k>\frac1{10}.
 \tag{39}
\]

## 10. The high-G part is excluded at every smaller slope

Suppose k<7/20. If G\ge17/20, equation (27), a_0\ge0 and h\le0 give z>p-q/2. Hence

\[
 R^2>(p+q/2)^2+(p+17/20)^2>B(q),
\]

where, using p>23/25 in the pq term and p>1-25q^2/48 in the remaining positive p term,

\[
 B(q)=\frac{1769}{400}+\frac{23}{25}q-\frac{253}{96}q^2.
 \tag{40}
\]

This is a concave quadratic on [0,39/100]. Its endpoint reserves are

\[
 B(0)-\frac{1105}{256}=\frac{679}{6400}>0,
 \qquad
 B(39/100)-\frac{1105}{256}=\frac{4099}{64000}>0.
 \tag{41}
\]

The whole interval is impossible. Therefore

\[
             k<7/20\quad\Longrightarrow\quad G<17/20.
 \tag{42}
\]

## 11. The last possible K circle corner is strictly inside the disk

Put t_0=1-a_0\in(2/3,1]. The actual last corner is

\[
 K_2=(h+c+t_0s,\ G+s-t_0c).
 \tag{43}
\]

Both coordinates are positive. The second exceeds G because c<s. For the first, c+t_0s>c+(2/3)s\ge2/3, while h>-1/60. Consequently, if G<\gamma and h\le0,

\[
 |K_2|^2<1+t_0^2+\gamma^2+2\gamma(s-t_0c).
 \tag{44}
\]

The right side is convex in t_0, so it is bounded by the larger endpoint value at 2/3 and 1. For fixed t>0,

\[
 s-tc=\frac{1-tk}{\sqrt{1+k^2}},\qquad
 \frac{d}{dk}(s-tc)=-\frac{t+k}{(1+k^2)^{3/2}}<0.
 \tag{45}
\]

If k\ge7/20, use \gamma=1. At t_0=1,

\[
 3+2(s-c)\le3+\frac{26}{\sqrt{449}}<\frac{17}{4},
\]

because 25/64-169/449=409/28736>0. At t_0=2/3,

\[
 \frac{22}{9}+2(s-2c/3)
 <\frac{22}{9}+\frac{23}{15}
 =\frac{17}{4}-\frac{49}{180}.
 \tag{46}
\]

If 1/10<k<7/20, use \gamma=17/20 by (42). The monotonicity gives

\[
 s-c<\frac9{\sqrt{101}}<\frac{112}{125},
 \qquad s-2c/3<\frac{14}{15}.
\]

The squared reserve for the first comparison is 1319/1578125. The two endpoint bounds in (44) are now

\[
\begin{split}
 2+\frac{289}{400}+\frac{17}{10}\frac{112}{125}
     &=\frac{17}{4}-\frac{43}{10000},\\
 \frac{13}{9}+\frac{289}{400}+\frac{17}{10}\frac{14}{15}
     &=\frac{17}{4}-\frac{1787}{3600}.
\end{split}
 \tag{47}
\]

Thus |K_2|^2<17/4\le R^2 in both whole slope intervals. Together with (7) and (32), every vertex of K is strictly inside the disk. A convex square then has no point on the containing circle. This contradicts its physical boundary contact and proves Theorem 1.1.

## 12. Explicit exhaustive scope

The proof has covered both actual HC physical types; the full shared-HC mean and its zero-offset endpoint; singleton C with every possible circle corner; every C-owned CK, including the full shared side; and all three K-owned CK axes permitted by the actual H-K-C triangle. The extra -V axis was included explicitly. The remaining V axis was treated at its full actual central offset and C2 slope, with no sampling of angles, force weights, or means.

The proper C2 law in (6) is the boundary-neighbor version with a physically unique loaded C. It is not an H3 or K2 law. K may have either physical circle mask and any positive pair degree. Its circle corner was never selected to suit an inequality: all four physical vertices were bounded, including both possible corners in (8). H has arbitrary forces and any further physical neighbors. The true original H4/K3/B3/C2 equations, when this local theorem is called, are therefore unchanged.

The result is an analytic exclusion of a whole local feature. It is not yet an assertion that every remaining original hub-tip feature has this chart. In particular, proving the sign h\le0 and proving that HC is the H-owned top contact are caller obligations. An oblique HC return from the opposite upper root corner is outside the theorem.

## 13. Intended original-domain transfers and their current recovery status

For a B-owned HB normal form written in an H frame (v,u), a genuine K-owned central row may have

\[
 W=(x,G),\quad
 K=W+[0,1](-B,A)+[-\rho,1-\rho](A,B),\quad A,B>0.
\]

Reflection of the v coordinate sends this to (3) with

\[
 h=-x,\qquad U=(B,A),\qquad V=(A,-B),
                 a_0=1-\rho.
 \tag{48}
\]

The offset is **1-\rho**, because reflection sends (A,B) to -V. A caller must prove x>0, the stated height window, the actual strict/closed side ranges, and the genuine unique C2 premise from the original configuration. No general stress-preserving translation of the disk center is allowed; (48) is an origin-preserving orthogonal map.

For the remaining H-owned-HB/K-owned-central northwest chart, a separate caller may map its central frame by U=t, V=-m and a_0=1-\ell. That caller still has to prove h\le0. The two-genuine-leaf height lemma for the different northeast chart does not automatically give that sign.

Some recent source and review bytes that would justify these original transfers were missing after the workspace rollback. They are not assumed restored or accepted merely from remembered hashes. This local theorem is logically independent of those missing files; original-gate assembly must wait for the complete caller source and its byte-verified, full independent review.

## 14. Verification boundary

The argument uses exact identities, convexity or concavity on complete intervals, and rational comparisons. Its displayed checks are algebra validation, not a box subdivision or a new computational certificate. No Lean compilation, build, CI, ledger, remote edit, or original-gate closure is claimed.

The accompanying `check_high_corner_central_top_page_identities.py` independently expands 29 displayed polynomial identities and verifies 31 fixed exact rational values or reserves, using only integer arithmetic and `fractions.Fraction`. Its completed replay passes. The script does not encode interval boxes, pose samples, or an alternative geometric theorem.

Before assigning an acceptance status, the independent reader must reconstruct all physical support branches, the actual fixed-point selection join, both shared means, the full -V owner case, the exact slope identity (28), and the two full interval arguments (34)--(42). Checking only the final scalar bounds would not audit the theorem.

## 15. Exact present original inputs and provenance

These complete original files were read from `current_pr11/research/nine` and their current bytes checked after reconnection:

| File | SHA256 | Exact use |
|---|---|---|
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual forces, strict singleton convention, unchanged aggregated means |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1, genuine proper C2 with a boundary neighbor |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Unique-corner normal-line calculation used by that lemma; circle point cannot be shared |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual H-K-C side-owner sign, including zero dot products |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Distinct physical singleton applications at C; no selection on a variable mean |

The high-side and orthogonal-return work motivated the proof, but every needed geometric and scalar part was reproduced here. In particular the remembered continuation hashes 2339ea8c32771c3a605c5c1e1efb40ad62bc712e01e57424f177c6a232fc62b2 and 48222d15a195ca864177e5b6f2bd75cd3ede7c6500dda5d90a41f9803815251c are provenance references, not an assertion that their original bytes are currently present or that their narrower hypotheses may be extended without proof.
