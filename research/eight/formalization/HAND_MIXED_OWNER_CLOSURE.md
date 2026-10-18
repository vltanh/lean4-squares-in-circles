# Complete table-free mixed-owner rigidity

**Status: the mixed-owner component of G7 is closed on paper under its original hypotheses.** Assume the candidate frame, signed tangent cuts, zero owners, both intended quarter-owner sets, q<=Q0 and S<=1/1000. Then every originally feasible mixed G axis is 0 and every originally feasible mixed E axis is 1.

The preceding implication S<=3/200 => S<1/1000 is NOT proved here. It remains an open table-free gate. This theorem is conditional on its stated small-mismatch input, exactly like the original mixed-owner theorem.

Together with the two companion proofs below, all 15 bad mixed-owner patterns are excluded without their 729 quartic certificates. Those existing Lean/data files remain unchanged during the hand-proof-only pass.

## 1. Inputs, notation and complete geometric alternatives

Use `HAND_MIXED_OWNER_CHAIN_BOUNDS.md` for the exact original nominal projections, the aligned loss k=1001/1000, and the following consequences. Put

\[
 c=\cos t,\quad s=\sin t,\quad W=(1+c+|s|)/2,
 \quad L=447/800,\quad U=283/200,\quad U_G=349/250,
 \quad V_A=131/100.
\]

Every center has its original corner disk (a_i+1/2)^2+(b_i+1/2)^2<=q. We have a_A<=V_A, b_A>=3/10, 7/12<=a_G<=U_G and L<=a_E<=U. The oblique bound a_E+b_E/4<=U is also available.

For a nonnegative sine, feasibility of G0,G1,G2,G3 forces, respectively,

\[
 s\le3/10,\quad s\le13/50,\quad s\le1/5,\quad s\le3/20.
\tag{1}
\]

For s=-r<=0, feasibility of E0 and E1 forces respectively

\[
 r\le3/20,\qquad r\le4/25.
\tag{2}
\]

The full frame chart gives c>=3/4 and 1-c<=4s^2/7; on the negative arc c>=9/10. The chain note excludes every feasible E axis 2 or 3 independently of G. We therefore need only the pairs with E0 or E1, except the intended pair G0/E1.

Throughout, an edge multiplier on an aligned edge costs k times that multiplier times its actual |d_i|; E costs 2 times its multiplier times S. The five actual |d_i| sum to S. This shared budget is retained in every argument below.

## 2. The aligned four-circle stress

Put

\[
 \alpha=31/72,\quad\omega=1271/1728,\quad\varepsilon=41/48,
 \quad\mu=31/144,\quad\nu=41/144.
\]

Give the edges H,G,A,B,T,D,E the weights

\[
 (h,\omega,\alpha,\omega,\omega,\varepsilon,\varepsilon),
 \qquad h=\omega\text{ for G0},\quad h=\omega c\text{ for G1}.
\tag{3}
\]

Complete the circles A,B,D,H with masses mu,mu,nu,nu; their sum is one. As in the preceding hand proofs, for any force (x,y), the upper bound is

\[
 T_q(x,y;m)=mq+(x^2+y^2)/(4m)-(x+y)/2.
\tag{4}
\]

At zero sine the exact test corners are (41/24,1) on A/B and (3/2,31/24) on D/H. All have squared norm 2257/576. Thus the zero-sine demand-minus-bound gap is

\[
 \Delta=2257/576-q.
\]

The aligned weights in (3) are at most epsilon; hence the complete error is at most (k+2)epsilon S. At q<=Q0 and S<=1/1000 the baseline reserve is

\[
 \Delta-(k+2)\varepsilon S\ge
 \frac{2257}{576}-Q_0-\frac{3001}{1000000}\frac{41}{48}
 =\boxed{\frac{34477}{144000000}}>0.
\tag{5}
\]

We prove that the relevant angle-dependent gap is always at least Delta.

### 2.1. G0/E0, both signs

After canceling b_G,b_T,b_E, the four forces are

\[
 (\omega c,\alpha-\omega s),\quad
 (\omega,\alpha),\quad(\varepsilon,\omega),\quad
 (\varepsilon c,\omega+\varepsilon s).
\]

Their square completions and c^2+s^2=1 give

\[
 \Psi=\Delta+(\omega+\varepsilon)(c-1)
       +\tfrac12(\omega+\varepsilon)|s|
       +(\varepsilon/2-\omega)s.
\tag{6}
\]

For s>=0 its linear sine coefficient is epsilon-omega/2>12/25, while omega+epsilon<8/5. By (1), s<=3/10. Therefore the cosine loss is at most (32/35)s^2, less than the positive linear term. Thus Psi>=Delta.

For s=-r<=0 the linear coefficient is 3omega/2>1. By (2), r<=3/20, and the same quadratic cosine loss is again smaller. Equation (5) excludes G0/E0.

### 2.2. G1/E0, both signs

The four forces are (omega,alpha), (omega,alpha), (epsilon,omega) and (epsilon c,omega c+epsilon s). There is also the term -omega s a_G. Bound it using A_G=7/12 for s>=0 and A_G=U_G for s<=0. The resulting gap is

\[
\begin{aligned}
 \Psi={}&\Delta+(2\omega+\varepsilon)(c-1)
   +K s^2+\tfrac12(\omega+\varepsilon)|s|\\
 &+\bigl(\varepsilon/2+\omega A_G-(3\omega/2)c\bigr)s,
 \qquad K=\omega^2/(4\nu)\ge0.
\end{aligned}
\tag{7}
\]

For s>=0 the total linear sine coefficient is at least epsilon-(5/12)omega>1/2. Also 2omega+epsilon<5/2. The cosine loss is at most (10/7)s^2, and s<=13/50 makes it smaller than the linear gain.

For s=-r<=0, c>=9/10 gives the total coefficient at least omega(1/2-U_G+3c/2)>3/10. Since r<=3/20, the cosine loss is at most (10/7)r^2<(3/10)r. Thus Psi>=Delta for both signs, and (5) excludes G1/E0.

### 2.3. G1/E1 with nonpositive sine

Use (3) with h=omega c. The E leftovers are epsilon[-r a_E+(1-c)b_E], bounded above by epsilon[-Lr+(9/10)(1-c)]. The G leftover is at most omega U_G r. The exact four-circle gap is

\[
 \Psi=\Delta+C(c-1)+Kr^2+Jr,
\]

where

\[
 C=2\omega+(7/5)\varepsilon=11521/4320<11/4,
 \quad K=39401/82944>9/20,
 \quad J=423899/1728000>6/25.
\]

Using the circle chord gives Psi>=Delta-(157/140)r^2+(6/25)r. Since E1 forces r<=4/25, the nonconstant part is nonnegative. Equation (5) again contradicts feasibility.

### 2.4. G1/E1 with nonnegative sine

This entire arc is excluded in `HAND_MIXED_PRIMARY_ADAPTIVE_STRESS.md`. That proof uses the original oblique E support and one explicit rational family of four circle stresses on s in [0,13/50]. Its single degree-seven remainder is proved positive by a whole-interval polynomial inequality, not by subdivision. The uniform final reserve is 103431/317750000>0.

This settles all residual cases with G0 or G1 except the intended G0/E1.

## 3. A common stress for G2/G3 and E0/E1

Set

\[
 h=9/20,\quad b=4/3,\quad e=3/5.
\]

Take A-edge weight a=1 for G2 and a=c for G3. Take D-edge weight d=e for E0 and d=ec for E1. The complete edge weights are

\[
 (h,1,a,b,b,d,e).
\tag{8}
\]

The equal B/T weights cancel b_T; the A choice cancels the G mixed projection's b_A term. For E0, d=e cancels b_E; for E1, d=ec leaves only es a_E.

Complete the G,B,D,H circles, with masses

\[
 (m_G,m_B,m_D,m_H)=(7/25,5/12,7/20,3/16).
\tag{9}
\]

The G force is (c,h-s) for G2 or (1,h) for G3; B has force (b,a). H has force (ec,h+es) for E0 or (e,h) for E1.

The D force starts as (d,b). Since b>=d, add the nonnegative cone inequality ((b-d)/2)(a_D-b_D)>=0 to the weighted sum. It makes D's two force coordinates equal to (b+d)/2. Its circle completion is now centered on the canonical diagonal, instead of incorrectly maximizing outside a_D>=b_D.

For G3 the leftover -s a_A is bounded using A_A=L for s>=0 and A_A=V_A for s<=0. For E1 use A_E=U for s>=0 and A_E=L for s<=0 in es a_E.

The weighted demand is h+a+2b+d+(1+e)W. The shared error is at most

\[
 (kb+2e)S\le1901/750000.
\tag{10}
\]

At zero sine, the demand-minus-four-circle-bound gap is

\[
 B(q)=2063/50400+(1481/1200)(47/12-q)>1/25.
\tag{11}
\]

The inequality q<=Q0<47/12 is sufficient. Expanding the four quadratic norms in (9) gives the following four identities, after c^2+s^2=1:

\[
\begin{aligned}
\Psi_{20}={}&B+\tfrac85(c-1)+\tfrac45|s|-\tfrac{163}{1400}s,\\
\Psi_{21}={}&B+\tfrac{57}{35}(c-1)+\tfrac9{70}s^2+\tfrac45|s|
                   +(\tfrac{17}{56}-\tfrac35 A_E)s,\\
\Psi_{30}={}&B+\tfrac{13}{5}(c-1)+\tfrac35s^2+\tfrac45|s|
                   +(A_A-\tfrac{21}{50})s,\\
\Psi_{31}={}&B+\tfrac{92}{35}(c-1)+\tfrac{51}{70}s^2+\tfrac45|s|
                   +(A_A-\tfrac35 A_E)s.
\end{aligned}
\tag{12}
\]

These are four actual owner alternatives, all with the same stress formulas, not four numerical angle covers.

For G2/E0, the linear |s| coefficient is greater than 2/3 for positive sine and greater than 9/10 for negative sine. The cosine loss is at most (32/35)s^2. The arcs in (1)–(2) therefore give Psi20>=B.

For G2/E1, the total linear coefficient is greater than 1/4 for positive sine and greater than 4/5 for negative sine. Combining the s^2 term with the chord bounds the negative quadratic coefficient by 393/490<1. Since positive s<=1/5 and negative |s|<=4/25, Psi21>=B.

For G3/E0 and positive sine, the linear coefficient is 751/800>9/10, and the combined negative quadratic coefficient is 31/35<1. Since s<=3/20, Psi30>=B.

For G3/E0 and s=-r<=0, (12) gives

\[
 \Psi_{30}\ge B-(31/35)r^2-(9/100)r
 \ge1/25-(31/35)(3/20)^2-(9/100)(3/20)
 =23/3500.
\]

This is greater than the loss (10). For G3/E1 and positive sine, the linear coefficient is 2039/4000>1/2; its combined negative quadratic coefficient is 379/490<1. Since s<=3/20, Psi31>=B. These five sign regimes and the two G2 sign pairs are all strictly excluded by (10)–(11).

The remaining G3/E1 negative arc uses the next, still whole-domain, stress.

## 4. G3/E1 on its complete negative arc

Now s=-r, 0<=r<=4/25. In (8), keep a=c and d=ec but choose

\[
 h=11/20,\quad b=27/20,\quad e=17/20,
\]

and replace the G,B,D,H masses by 3/10,9/20,2/5,1/4. Retain the same nonnegative D cone correction and the same bounds a_A<=V_A, a_E>=L.

The gap again has the form

\[
 \Psi=B_1+C(c-1)+Kr^2+Jr,
\]

with

\[
 B_1=37/1440+(7/5)(47/12-q)>1/40,
\]

\[
 C=2+2e-be/(4m_D)<3,\quad
 K=1/(4m_B)+e^2/(8m_D)>3/4,
 \quad J=(1+e)/2+eL-V_A>2/25.
\]

Hence

\[
 \Psi\ge1/40+(2/25)r-(27/28)r^2.
\]

This is a concave quadratic. Its endpoint values on [0,4/25] are 1/40 and 459/35000, both greater than 1/100. The shared error is at most (kb+2e)/1000=61027/20000000<1/250. The strictly positive remaining reserve exceeds 3/500. This excludes the entire final negative arc, including its endpoints.

## 5. Universal owner quantifiers and conclusion

Retain any pair of originally feasible G and E witnesses. The chain note excludes E2/E3 for every G. For E0/E1, Sections 2–4 and the adaptive companion exclude all pairs except G0/E1. Therefore every feasible G witness is 0 and every feasible E witness is 1: a forbidden witness can always be paired with any feasible witness on the other edge and yields one of the contradictions above.

In particular, the proof does not just choose convenient owners and does not discard ties. Combining with the previously established zero and quarter restrictions gives exactly

\[
 (\{0,2\},\{0\},\{0,2\},\{2,3\},\{0,2\},\{2,3\},\{1\})
\]

for the seven original forward-axis owner sets.

## Dependency and verification status

This proof and its two companions replace the mathematics of all 15 mixed-owner groups. They do not establish S<1/1000 without the final affine mismatch table; that is still a separate input gate. Positive tilt-tail capture is also not concluded here.

The proof uses original SAT projections, explicit circle supports, one canonical cone correction, shared errors, elementary chords, and one analytically derived degree-seven remainder in the difficult positive primary case. It uses no numerical angle partition, generated owner quartic, Bernstein row list, or external success assertion. No Lean/table source was modified, no Lean compilation was attempted, and no CI was run.
