# Complete table-free quarter-owner rigidity

**Gate G6: closed on paper under its original hypotheses.** Assume the candidate frame, the signed tangent cuts, the previously proved zero owners, q <= Q0, and S <= 3/200. Then every originally feasible B-to-T and D-to-E axis belongs to the intended zero-based set {2,3}.

The conclusion does not assume the final mismatch bound, either mixed owner, positive tilt, or any owner-certificate table. The remaining eight quarter groups (345 quartics at the starting source snapshot) are mathematically unnecessary once this proof is used. Their Lean imports remain unchanged because the current execution is hand-proof-only.

## 1. Reduction to four intrinsically defined alternatives

The geometric theorem `D_quarter_owners`, proved in `OWNER_GEOMETRY.md`, Sections 6–10, already excludes every forbidden D axis under exactly the hypotheses above. Section 7 of that note excludes G axis 2 when B is forbidden; Section 11 excludes G axis 3 in the same situation, using the now-established D conclusion. These arguments use no quarter/mixed-owner tables.

Suppose therefore that an original forbidden B axis is feasible. Choose any actually feasible G axis. It must be 0 or 1. `HAND_FORBIDDEN_B_LOCALIZATION.md` proves, from this assumption,

\[
 -3/8<s=\sin t<1/10,\qquad c=\cos t>0,\qquad c^2+s^2=1,
\]

and excludes E axes 2 and 3. Thus an actually feasible E axis is 0 or 1. This leaves four geometric alternatives (G0/E0, G0/E1, G1/E0, G1/E1), not a numerical angular partition.

The same note provides the closed domains sufficient below:

\[
\begin{array}{ll}
 s\ge0:&0\le s\le1/10,\quad99/100\le c\le1;\\
 s=-r\le0:&0\le r\le3/8,\quad9/10\le c\le1,
 \quad1-c\le(4/7)r^2\le(3/14)r.
\end{array}
\tag{1}
\]

Every actual center satisfies its original corner-disk inequality

\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q_0=9789/2500<47/12.
\tag{2}
\]

We will also use b_E >=0, 447/800 <=a_E<=283/200, and 7/12<=a_G<=349/250. No radial contact equality or center proximity is needed.

## 2. One seven-edge stress, with exact cancellation

Put

\[
 p=7/10,\quad u=1/4,\quad d=3/10,\quad e=11/10,
 \qquad W=(1+c+|s|)/2.
\]

Use the following nonnegative edge weights, in cyclic order H,G,A,B,T,D,E:

\[
 (h,1,p,p,u,d,e),\qquad
 h=1\ \hbox{for G0},\quad h=c\ \hbox{for G1}.
\tag{3}
\]

These weights are the same for both E alternatives and for the entire relevant tilt range. The coefficient h cancels the G transverse term; the equal A/B weights cancel b_B. The demand before error is

\[
 D=h+39/20+(21/10)W.
\tag{4}
\]

The five aligned weights are at most one. Therefore their actual losses sum to at most (3/2)S. The E loss is at most 2eS. The **complete shared** error is

\[
 \mathcal L\le(37/10)S\le111/2000.
\tag{5}
\]

No independent copy of S is assigned to each aligned edge.

After summing the actual nominal projections, four center forces remain on A,T,D,H. On T and D they are always (p,u) and (d,u). On A they are

\[
 f_A=(c,p-s)\quad\hbox{for G0},\qquad
 f_A=(1,p)\quad\hbox{for G1}.
\]

For E0 the H force is (ec,h+es), and the leftover E term is (d-e)b_E <=0. For E1 the H force is (e,h), and the leftover E terms are

\[
 es a_E+(d-ec)b_E\le es a_E,
\]

because c >=3/4 implies d-ec <=3/10-33/40<0. In the G1 case there is additionally the term -s a_G.

For an upper bound on these leftovers, define A_E=283/200 when s>=0 and A_E=447/800 when s<=0; define A_G=7/12 when s>=0 and A_G=349/250 when s<=0. Then es a_E <=es A_E and -s a_G <=-s A_G. At s=0 either definition gives the same product.

The weighted necessary inequality is D-L <= F, where F is this sum of four forces and the leftovers. Each displayed force follows directly from the original four SAT formulas; no claimed polynomial from an owner table is used.

## 3. Four circle completions

For any real x,y and positive mu, (2) and a completed square give

\[
 xa_i+yb_i\le
 \mu q+\frac{x^2+y^2}{4\mu}-\frac{x+y}{2}.
\tag{6}
\]

Indeed, subtracting x(a_i+1/2)+y(b_i+1/2) from the right side before the final shift leaves

\[
 \mu\bigl(q-(a_i+1/2)^2-(b_i+1/2)^2\bigr)
 +\mu\left(a_i+1/2-\frac{x}{2\mu}\right)^2
 +\mu\left(b_i+1/2-\frac{y}{2\mu}\right)^2\ge0.
\]

Apply (6) on A,T,D,H with

\[
 (\mu_A,\mu_T,\mu_D,\mu_H)=(3/10,3/16,1/10,3/8).
\tag{7}
\]

These masses sum to 77/80. They are explicit circle-support choices, not numerical multipliers varying by subinterval. For reference, at c=1,s=0 their supporting test corners f/(2mu) are respectively

\[
 (5/3,7/6),\quad(28/15,2/3),\quad(3/2,5/4),\quad(22/15,4/3).
\]

The test corners need not themselves lie on the radius-q circle: the displayed square completion proves the inequality at every center and explains the choice geometrically.

Let B(q) be the gap between demand and these four circle bounds at c=1,s=0. Direct substitution gives

\[
 B(q)=\frac{9281}{2400}-\frac{77}{80}q
 \ge\frac{467}{4800}.
\tag{8}
\]

The last comparison uses only q<=47/12. To check the constant without an expansion table, the constant terms in the four bounds (6) at zero tilt are 47/120,157/600,17/160,127/300; their sum is 2839/2400. The demand is 101/20, hence (8).

Write Psi for demand minus the upper bound on F. Using c^2+s^2=1 gives the following four symbolic identities:

\[
\begin{aligned}
\Psi_{00}={}&B+\frac{21}{10}(c-1)+\frac{21}{20}|s|-\frac s4,\\
\Psi_{01}={}&B+\frac{31}{20}(c-1)+\frac{21}{20}|s|
                  +\left(\frac23-\frac{11}{10}A_E\right)s,\\
\Psi_{10}={}&B+\frac{31}{10}(c-1)+\frac23s^2+\frac{21}{20}|s|
                  +\left(\frac{11}{20}+A_G-\frac{22}{15}c\right)s,\\
\Psi_{11}={}&B+\frac{51}{20}(c-1)+\frac23s^2+\frac{21}{20}|s|
                  +\left(A_G-\frac{11}{10}A_E\right)s.
\end{aligned}
\tag{9}
\]

The subscripts are the actual G and E axes. These formulas are reproduced simply by inserting the four forces in (6). For example the varying A norm for G0 is c^2+(p-s)^2=1+p^2-2ps. The E0 H norms are e^2+1+2es for G0 and e^2+c^2+2ecs for G1. This accounts for every quadratic term in (9).

## 4. The complete nonnegative-sine domain

For s>=0 substitute A_E=283/200 and A_G=7/12. The respective coefficients of s in (9), including 21|s|/20, are

\[
 4/5,\qquad961/6000,\qquad131/60-(22/15)c,
 \qquad461/6000.
\]

All are nonnegative; the third is at least 43/60. The s^2 terms are nonnegative. Since (1) gives c>=99/100 and the largest coefficient of c-1 is 31/10, all four alternatives satisfy

\[
 \Psi\ge B-31/1000.
\tag{10}
\]

This is one estimate on the entire forced positive arc, including zero tilt.

## 5. The complete nonpositive-sine domain

Put s=-r and use A_E=447/800, A_G=349/250. The first formula becomes

\[
 \Psi_{00}=B+\tfrac{21}{10}(c-1)+\tfrac{13}{10}r\ge B,
\]

because 1-c <=3r/14 and 13/10-(21/10)(3/14)=17/20>0.

For the second formula the r coefficient is 23951/24000 >=9/10. Thus

\[
 \Psi_{01}\ge B+\left(9/10-(31/20)(3/14)\right)r\ge B.
\]

For the third, c>=9/10 gives

\[
 \Psi_{10}\ge B-\frac{116}{105}r^2+\frac{53}{125}r
 \ge B+\frac{17}{1750}r\ge B.
\]

The first inequality uses 1-c <=(4/7)r^2; the second uses r<=3/8 and 53/125-(116/105)(3/8)=17/1750.

For the fourth formula the r coefficient is 2149/8000. The same chord gives

\[
 \Psi_{11}\ge B-\frac{83}{105}r^2+\frac{2149}{8000}r
 \ge B-\frac3{100}r\ge B-\frac9{800}.
\]

Here 2149/8000-(83/105)(3/8)>-3/100. Since 9/800<31/1000, the uniform bound (10) holds throughout the negative arc as well. No angular interval mesh is involved.

## 6. Strict contradiction and complete owner conclusion

Equations (5), (8) and (10) imply

\[
 D-F-\mathcal L
 \ge\frac{467}{4800}-\frac{31}{1000}-\frac{111}{2000}
 =\boxed{\frac{259}{24000}}>0.
\]

This contradicts D-L<=F. Therefore none of the four residual G/E alternatives is possible with an originally feasible forbidden B axis.

To make the quantifiers explicit: retain the putative forbidden B witness, select any feasible G witness, apply the already proved G2/G3 exclusions, then select any feasible E witness. The localization note excludes E2/E3; the present four-circle stress excludes E0/E1. This is a contradiction for **every** originally feasible forbidden B witness, including a witness tied with an allowed B axis. Combining with the earlier all-axis D theorem proves the full quarter-owner restriction.

## 7. Dependency and verification status

This closes exactly the hand roadmap's G6. Its inputs still include S<=3/200, tangent cuts and zero owners; the earlier table-free mismatch/capture gates are not solved by this theorem. No final mixed owner or tilt-window assumption enters the argument. All centers remain their original admissible positions.

The proof is a finite classification by the four actual G/E possibilities, two forced sine signs, and one uniform stress. It contains no generated quartic row, Bernstein list, interval subdivision, or external acceptance assertion. Exploratory optimization suggested the stress; equations (3)–(10) and the positive reserve constitute the proof independently. Exact algebra was cross-checked symbolically, but that computation is not a premise. No Lean source, generator or existing table was changed; no Lean compilation or CI was run.
