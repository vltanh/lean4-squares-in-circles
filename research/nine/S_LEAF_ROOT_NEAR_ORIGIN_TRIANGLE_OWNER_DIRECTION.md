# An S-leaf root points away from an owned near-origin triangle interface

Date: October 26, 2026.

**Status: complete reusable physical hand candidate, pending fresh full independent review.** This extends the familiar degree-three triangle-root owner direction to a genuine S-leaf root of arbitrary degree. It uses the actual occupied leaf and a physical common boundary neighbor, not a shortened root force equation.

## 1. Exact local theorem

Use the original contained, interior-disjoint unit squares and radius window
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \epsilon=\max(d-1,0)<\frac1{60},\qquad
 \frac9{10}<d<\frac{61}{60}.
 \tag{1}
\]
Let H be a genuine radial S-leaf root with actual leaf L and outward leaf direction e. Its true leaf theorem gives
\[
 p_L=de,\qquad h_H(e)=d,\qquad
 L=[d,d+1]e+[-1/2,1/2]Je.
 \tag{2}
\]
Let B be a distinct actual unit meeting the closed disk \(D_\epsilon\). Assume H and B physically touch, with an actual separating unit normal n from H to B which is a side axis of H. The intersection may be shared or singleton; its actual mean is arbitrary.

Let K be a further physical circle-touching unit, distinct from L, which physically touches both H and B. The positive degrees of H,B,K and all forces other than the genuine leaf are unrestricted. HK and BK need not have positive force.

**Theorem 1.1.**
\[
                              e\cdot n<0.
 \tag{3}
\]
Consequently, writing \(h=h_H(n)\),
\[
 |h|\le\epsilon,\qquad
 d(e\cdot n)=h-1,\qquad
 |p_L\cdot Jn|^2=d^2-(1-h)^2.
 \tag{4}
\]
The actual domain of this physical triangle therefore has \(d\ge1\). For \(d>1\),
\[
                     |p_L\cdot Jn|^2\le4(d-1).
 \tag{5}
\]
For \(d=1\), (4) gives \(h=0\) and \(e=-n\).

Only the real radial leaf geometry, physical triangle, near-origin point and side ownership are used. In particular no H3 equation is assigned to H4, and no circle force or other neighbor is removed.

## 2. An elementary corner-support bound

The following physical bound is useful independently.

**Lemma 2.1.** Suppose a unit square T lies in \(y\le l\), contains a point \((x,l)\) with \(x\le h\), and contains some point whose first coordinate is at least h. Put \(Q=(h,l)\). Then
\[
                  \max_{z\in T}|z-Q|^2\le\frac83<\frac{25}{9}.
 \tag{6}
\]
There is no circle, degree, force or orientation assumption.

If T is aligned with the coordinate axes, its top side contains Q: its horizontal interval reaches both sides of h. Every point of T is then within \(\sqrt2\) of Q, so (6) holds.

Otherwise T has a unique top vertex \(q=(q_x,l)\), with \(q_x\le h\), and its inward orthonormal axes have the form
\[
                 (-c,-t),\quad(t,-c),\qquad
                 c,t>0,\quad c^2+t^2=1.
\]
Its maximum first coordinate is \(q_x+t\), so
\[
                        -t\le\kappa=q_x-h\le0.
\]
Relative to Q, its four actual vertices are
\[
 (\kappa,0),\quad(\kappa-c,-t),\quad
 (\kappa+t,-c),\quad(\kappa+t-c,-t-c).
 \tag{7}
\]
For each vertex its squared norm is convex in \(\kappa\), hence its maximum on the full interval occurs at \(0\) or \(-t\). The resulting squared norms are bounded by
\[
          2,\qquad c^2+(c+t)^2,\qquad t^2+(c+t)^2.
\]
Both latter expressions are at most \(8/3\). For example,
\[
 \frac83(c^2+t^2)-\bigl(c^2+(c+t)^2\bigr)
 =\frac23(c-\tfrac32t)^2+\frac16t^2\ge0,
 \tag{8}
\]
and exchange c,t for the other one. Norm convexity extends the vertex bound to all of T. This proves (6), with both limiting axis orientations covered by the aligned case.

## 3. The full nonnegative-leaf chart

The actual inward segment of a genuine S root contains \((d-1)e\) when \(d>1\), and contains O when \(d\le1\). Thus H meets \(D_\epsilon\). The actual H/B supporting half-planes and the small-disk point of each give
\[
                              |h_H(n)|\le\epsilon.
 \tag{9}
\]
Rotate so \(n=e_x\), and suppose for contradiction that \(e\cdot n\ge0\).

If \(e_x>0\), the true leaf point lies on the maximum-x side of H, so
\[
                     h=d e_x,\qquad0<h\le\epsilon.
\]
In particular \(d>1\). Its vertical component is nonzero: \(e_x=1\) would give \(h=d>\epsilon\). Reflect vertically to make \(e_y>0\). Both leaf components are then strict, so its actual application is H's upper-right vertex. Writing
\[
                T=d e_y=\sqrt{d^2-h^2},
\]
the complete actual chart is
\[
                       H=[h-1,h]\times[T-1,T].
 \tag{10}
\]
Since \(h\le d-1\),
\[
                 T^2\ge d^2-(d-1)^2=2d-1>1.
 \tag{11}
\]

If \(e_x=0\), reflect so \(e=e_y\). The genuine leaf application is \((0,d)\), possibly an interior side mean or either endpoint. The complete H chart is again (10), now with
\[
                            T=d,\qquad0\le h\le\epsilon.
 \tag{12}
\]
The lower bound for h follows from \((0,d)\in H\). No leaf mean endpoint is removed.

In either case, putting \(l=T-1\),
\[
      0\le h<\frac1{60},\qquad
      -\frac1{10}<l<\frac1{60},\qquad
      \frac9{10}<T<\frac{61}{60}.
 \tag{13}
\]
The lower-right root corner \(Q=(h,l)\) obeys
\[
          |Q|^2<\frac1{3600}+\frac1{100}
                 =\frac{37}{3600}<\frac1{81}.
 \tag{14}
\]
The last rational reserve is
\(1/81-37/3600=67/32400>0\).
Every point of a physical boundary unit has radius at least
\(r=R-\sqrt2>11/20\), so this actual corner cannot belong to K.

Choose any actual physical separating normal m from H to K. The physical triangle H-B-K and H's side ownership of n give
\[
                                m_x\ge0
 \tag{15}
\]
by UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md. No multiplier or force equation is needed for (15).

Thus the exhaustive possible directions of m are strict northeast, strict southeast, \(e_x\), \(e_y\), and \(-e_y\). We exclude all five with the actual physical bodies.

## 4. The two strict corner directions are impossible

A strict southeast m exposes precisely the lower-right H corner Q in (14). Since Q would also belong to K, its radius below \(1/9<r\) excludes this case.

For a strict northeast m, the actual H/K point is \(P=(h,T)\).

If \(e_x>0\), this is the actual genuine radial leaf application \(de\), in the relative interior of L's inner side. H's inward sector there is the southwest quadrant. L occupies a half-plane whose inward normal e has both components positive. The complement of those two sectors consists of two sectors, each of angle strictly less than \(\pi/2\). No further unit square's tangent sector, of angle at least \(\pi/2\), fits there. Hence K cannot contain P.

If \(e_x=0\), then \(P=(h,d)\), where \(0\le h<1/60<1/2\). P lies in the relative interior of the actual vertical radial S leaf's bottom side. L occupies the upper half-plane and H the southwest quadrant. A further unit at P would have to occupy exactly the southeast quadrant. It would therefore be the aligned unit
\[
                          [h,h+1]\times[d-1,d].
\]
It shares H's whole vertical side, so its separating normal from H is \(e_x\), not a strict northeast direction. This excludes the proposed strict m while retaining the axis case for the next section.

## 5. The right and upper side directions cannot reach a distinct boundary unit

We use the actual center bounds
\[
 R-\frac1{\sqrt2}\le |c_X|\le d+\frac12
 \tag{16}
\]
for a physical boundary unit X. The upper bound also holds for every contained unit. In the window (1),
\[
           |c_X|>\frac{19}{15},\qquad
           |c_X|<\frac{91}{60}.
 \tag{17}
\]
For the lower bound, \(R\ge79/40\) and \(1/\sqrt2<17/24\) give
\(79/40-17/24=19/15\).

### 5.1. The right side

Suppose \(m=e_x\). The actual K minimum-x support is h. Its center satisfies
\[
        \frac12\le (c_K)_x
             \le h+\frac1{\sqrt2}<\frac{29}{40}.
 \tag{18}
\]
An actual point of H/K contact has height at least l. Since every unit halfwidth is at most \(1/\sqrt2<17/24\),
\[
                   (c_K)_y>-\frac1{10}-\frac{17}{24}
                              =-\frac{97}{120}.
 \tag{19}
\]
But (17)--(18) give
\[
     (c_K)_y^2>
       \left(\frac{19}{15}\right)^2
        -\left(\frac{29}{40}\right)^2
       =\frac{15535}{14400}>1.
 \tag{20}
\]
Thus \((c_K)_y>1\). Its center direction is in the first quadrant and differs from the positive vertical axis by an angle \(\phi_K\) satisfying
\[
          \sin\phi_K
              =\frac{(c_K)_x}{|c_K|}
                  <\frac{87}{152}<\frac7{12}<\sin(\pi/5).
 \tag{21}
\]
For the last strict comparison,
\(\sin^2(\pi/5)=(5-\sqrt5)/8>49/144\) follows from
\(\sqrt5<41/18\), whose squared reserve is \(61/324>0\).
The other rational reserve is \(7/12-87/152=5/456>0\).
Therefore \(0<\phi_K<\pi/5\).

The actual S leaf center has direction e. In the positive branch,
\(0<e_x=h/d<1/54\), so its direction also lies strictly between the positive vertical axis and angle \(\pi/5\) to its right. In the zero branch it is the vertical axis itself. Consequently the two actual boundary center directions of K and L differ by strictly less than \(\pi/5\). This contradicts their strict separation greater than \(2\pi/9\) from CENTERED_INNER_ARC.md. K and L are distinct original units.

This excludes the entire right-side chart, including arbitrary contact means and either physical K circle mask.

### 5.2. The upper side

Suppose \(m=e_y\). If \(e_x=0\), then \(T=d\), and K lies beyond the support line \(y=d\). The sharp contained-unit support equality in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1, makes K the unique radial S square in direction \(e_y\). That is exactly the actual leaf L, contrary to distinctness.

If \(e_x>0\), then \(d>1,T>1\), so
\[
                 (c_K)_y\ge T+\frac12>\frac32.
\]
By the center upper bound,
\[
       |(c_K)_x|^2<
           \left(\frac{91}{60}\right)^2-\frac94
              =\frac{181}{3600}<\frac1{16}.
 \tag{22}
\]
The actual leaf center is \(c_L=(d+1/2)e\). Since
\(e_x=h/d<1/60\),
\[
                    |(c_L)_x|<\frac{91}{3600}<\frac1{30}.
 \tag{23}
\]
Also \(e_y=\sqrt{1-e_x^2}>1-e_x>59/60\) and \(d+1/2>3/2\), hence
\[
             \frac{59}{40}<(c_L)_y<\frac{91}{60}.
\]
The same lower and upper bounds hold for \((c_K)_y\). Thus
\[
 |c_K-c_L|^2<
      \left(\frac14+\frac1{30}\right)^2
       +\left(\frac{91}{60}-\frac{59}{40}\right)^2
     =\frac{1181}{14400}<1.
 \tag{24}
\]
Every actual unit contains the open disk of radius \(1/2\) about its center. Distance below one therefore contradicts disjoint open interiors. This excludes the upper chart without requiring K to have a unique circle corner.

## 6. The lower side is excluded by the complete corner-support bound

The remaining direction is \(m=-e_y\). Then the actual whole K lies in \(y\le l\) and contains an H/K contact point \((x,l)\) with \(x\le h\).

The actual whole B lies in \(x\ge h\) by the original H/B side separation. Since K physically touches B, it contains a point whose first coordinate is at least h. Every premise of Lemma 2.1 applies to the original K and \(Q=(h,l)\). Therefore every point \(z\in K\) satisfies
\[
            |z|\le |z-Q|+|Q|
                 <\frac53+\frac19
                  =\frac{16}{9}<\frac{79}{40}\le R.
 \tag{25}
\]
The final rational reserve is \(79/40-16/9=71/360>0\). This contradicts K's physical circle contact.

All directions allowed by (15) are impossible. The supposition \(e\cdot n\ge0\) is therefore false, proving (3).

Since \(e\cdot n<0\) and n is an H side axis, the genuine maximum-e leaf application lies on H's opposite n-face. Its n-coordinate is \(h-1\), giving (4). If \(d<1\), then \(\epsilon=0,h=0\) and \(|d(e\cdot n)|=1>d\), impossible. At \(d=1\) the asserted equality case follows. For \(d>1\), \(h\le d-1\) and \(1-h>0\) give
\[
 d^2-(1-h)^2\le d^2-(2-d)^2=4(d-1),
\]
which is (5). No actual endpoint or aligned leaf mean was omitted.

## 7. Reuse on the original hub/tip diamond

In the original graph
\[
                     HK,HB,HC,KB,KC,HL_H,BL_B,
\]
H has true degree four, K degree three, B degree three and C degree two. H and B are genuine S roots and therefore both meet \(D_\epsilon\). K is a physical common boundary neighbor of H and B.

Whenever the actual HB normal is owned by H, Theorem 1.1 gives its exact negative leaf-component relation (4), without deleting HC or HK. At the true degree-three B, the corresponding relation when B owns HB already follows from the genuine triangle/root force equation; the present theorem shows that the same owner direction survives at the higher-degree H for a physical reason.

If HB is shared, both actual owner directions obey their respective full relations. If it is a singleton owned only by H, that whole original owner family is still reduced by (4)--(5), with arbitrary K3/C2 loads and every physical mask retained. No force at H, B, K or C is replaced.

More generally this implication applies to arbitrary root degree and an arbitrary near-origin neighbor B with one physical common boundary unit K. It is not limited to a diamond or a selected positive triangle. Lemma 2.1 is radius-free and can be used separately for other physical corner-support charts.

The theorem does not assert that HB is shared or that every remaining negative-component owner chart is impossible. The original S/S hub/tip gate remains open under this source alone.

## 8. Frozen original inputs and verification boundary

The direct accepted inputs at comparison head
26d9e3042b733ff0796876a4607a7d834f4b630a are:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine radial S leaf, actual support application and inward unit segment |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Every physical HK normal has nonnegative projection on the H-owned HB side axis |
| CENTERED_INNER_ARC.md | fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5 | Strict angular separation of distinct physical boundary centers |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | Universal center bound and sharp support equality, Section 1 |

All geometric inequalities above concern full intervals and actual physical square corners; no sampled pose or orientation subdivision is used. The proof retains both radius endpoints, d=1, every actual shared mean, all individual circle weights, arbitrary neighboring degrees and every packing unit. It introduces no computational exclusion certificate, graph ID, checklist count, force deletion, post-extraction normal choice, Lean run, CI workflow, ledger edit or remote mutation.

