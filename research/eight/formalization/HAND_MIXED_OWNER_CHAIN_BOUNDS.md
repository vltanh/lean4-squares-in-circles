# Mixed-owner chains without angle tables

**Status: proved on paper under the original small-mismatch hypotheses.** Assume the candidate frame, signed tangent cuts, zero owners, both intended quarter-owner sets, q<=Q0 and S<=1/1000. This note proves that every feasible E axis belongs to {0,1}, for every possible original G axis. It does not assume either final mixed owner and does not prove the preceding contraction to S<1/1000.

Indices are zero based. Write c=cos(t), s=sin(t), W=(1+c+|s|)/2 and

\[
 L=447/800,\quad U=283/200,\quad V=29/25,
 \quad U_G=349/250,\quad V_A=131/100,
 \quad k=1001/1000.
\]

We use actual corner containment, L<=a_i<=U, 0<=b_i<=9/10, the H cone b_H>=a_H/2, and the G/T bounds 7/12<=a_i<=U_G with b_i>=a_i/20. The chart gives c>=3/4 and |s|<=7/10.

## 1. Improved aligned loss

For any originally feasible aligned axis and e_i=|d_i|<=1/1000, the projection Lipschitz bound and the width cusp give

\[
 P_i^{\rm nominal}\ge1-e_i-e_i^2/4-e_i^3/12
                \ge1-k e_i.
\]

The last step follows from e_i/4+e_i^2/12<1/1000. This applies to both zero and quarter aligned edges and to both originally feasible axes in each permitted set. G has no phase error, and E retains P_E>=W-2S.

Thus the seven nominal demands are

\[
\begin{aligned}
 b_H+b_G&\ge1-k e_H,\qquad G_j\ge W,\\
 b_A+b_B&\ge1-k e_A,\\
 a_B-b_T&\ge1-k e_B,\\
 b_T+b_D&\ge1-k e_T,\\
 a_D+b_E&\ge1-k e_D,\qquad E_j\ge W-2S.
\end{aligned}
\tag{1}
\]

The mixed projections are exactly

\[
\begin{aligned}
G_0&=ca_A-sb_A-b_G,&G_1&=a_A-sa_G-cb_G,\\
G_2&=ca_G-sb_G-b_A,&G_3&=a_G-sa_A-cb_A,\\
E_0&=ca_H+sb_H-b_E,&E_1&=a_H+sa_E-cb_E,\\
E_2&=ca_E+sb_E-b_H,&E_3&=a_E+sa_H-cb_H.
\end{aligned}
\tag{2}
\]

## 2. Uniform coordinate bounds from the quarter chain

Adding B and T in (1) and using b_D<=9/10 yields a_B>109/100. If b_B>=69/100, its farthest corner would have squared norm at least

\[
 (159/100)^2+(119/100)^2=39442/10000>Q_0.
\]

Hence b_B<69/100. The A row now gives b_A>1-k/1000-69/100>3/10. If a_A>=131/100, its corner would have squared norm at least

\[
 (181/100)^2+(4/5)^2=39161/10000>Q_0.
\]

Therefore b_A>=3/10 and a_A<=V_A. The H cone and containment give a_H<=V exactly as in `HAND_FORBIDDEN_B_LOCALIZATION.md`.

We also have the useful oblique support, valid for every center:

\[
 \boxed{a_i+b_i/4\le U.}
\tag{3}
\]

Indeed, Cauchy applied to (a_i+1/2,b_i+1/2) and (1,1/4) gives a_i+b_i/4+5/8 <= sqrt(17q/16). But 17Q0/16=4.160325 < (51/25)^2=4.1616 and U+5/8=51/25.

## 3. Forced whole arcs, not a numerical partition

The all-axis H/E argument in `HAND_FORBIDDEN_B_LOCALIZATION.md`, Section 2, uses no forbidden-B assumption. It therefore gives s>-3/8 here as well. For r=-s>=0,

\[
 r\le3/8,\quad c\ge9/10,\quad1-c\le(4/7)r^2.
\tag{4}
\]

For s>=0, the feasible G axis gives the following bounds directly from (1)–(2).

For G0, H+G0 and the coordinate bounds imply 3/5-(81/100)c+(4/5)s<=kS. Since c<=1, s<3/10.

For G1, cH+G1 gives -81/100+(3/5)c+(13/12)s<=kS. Using 1-c<=4s^2/7 and s<=7/10 yields -21/100+(253/300)s<=kS, hence s<13/50.

For G2, the G cone gives G2<=U_G(c-s/20)-3/10. Comparing with W yields s<=480/2849<1/5.

For G3, G3<=U_G-Ls-(3/10)c. The same chord gives -12/125+(L+9/50)s<=0, hence s<3/20.

Thus the positive arcs forced by G0,G1,G2,G3 are respectively s<=3/10,13/50,1/5,3/20. No unproved owner preference enters these implications.

There are also shorter negative arcs forced by an E owner. For E0, E0<=V(c-r/2), so feasibility and c<=1 give r<=3/20. For E1, E1<=V-Lr. Hence

\[
 1+(1/2+L)r-(2/7)r^2\le V+2/1000.
\]

The left side is strictly increasing on [0,3/8]. At r=4/25 it exceeds V+2/1000 by 3/35000. Consequently E1 implies r<4/25.

For E2, E2<=Uc-L/2. Feasibility implies

\[
 (183/200)c-r/2\ge1/2+L/2-2/1000.
\]

Since c<=1-r^2/2, it follows that (183/400)r^2+r/2<=1101/8000. The left side is increasing, and at r=1/4 equals 983/6400>1101/8000. Thus E2 implies r<1/4.

## 4. Exclusion of E2 for every G axis

Every three-edge sum below has H and E coefficients between zero and one. Its total nominal loss is at most

\[
 (k+2)S\le3001/1000000.
\tag{5}
\]

### G0/E2

H+G0+E2 has demand D=1+2W and force F=c(a_A+a_E)+s(b_E-b_A). Using a_A,a_E<=U and |b_E-b_A|<=9/10 gives D-F>=17/100.

### G1/E2

cH+G1+cE2 has D=c+(1+c)W and F=a_A-sa_G+c^2a_E+csb_E. For s>=0 its gap is at least

\[
 -81/100+2c-(183/200)c^2+s(13/12-(2/5)c).
\]

The s coefficient is positive and the c polynomial is increasing on [3/4,1]; at 3/4 it is 561/3200>3/400.

For s=-r<=0, E2 forces r<=1/4 and c>=19/20. The gap is at least

\[
 -81/100+2c-(183/200)c^2+
          r((1+c)/2-U_G).
\]

Using c>=19/20, monotonicity of the c polynomial, and r<=1/4 gives a lower bound greater than 3/400 (in fact 12717/80000).

### G2/E2

H+G2+E2 has D=1+2W and

\[
 F=ca_G+(1-s)b_G+ca_E+sb_E-b_A.
\]

Complete only the G circle, with mass 3/8. Its force norm satisfies c^2+(1-s)^2=2-2s, so

\[
 ca_G+(1-s)b_G\le(3/8)q+5/6-c/2-(5/6)s.
\]

Using a_E<=U, b_A>=3/10, and sb_E<= (9/10)max(s,0), the gap is at least

\[
 22/15+(17/200)c-(3/8)q+
          |s|+(5/6)s-(9/10)\max(s,0).
\]

The sine part is nonnegative for both signs. Since c>=3/4 and q<=47/12, the gap is at least 37/600.

### G3/E2

H+G3+E2 has D=1+2W and

\[
 F=a_G+b_G+ca_E+sb_E-sa_A-cb_A.
\]

The G disk gives a_G+b_G<=9/5, because q<98/25. For s>=0, the gap is at least 17/200+(1/10+L)s>=17/200. For s=-r<=0, use a_A<=V_A, b_A>=3/10 and the E2 bound r<=1/4. The gap is at least

\[
 1/5-(23/200)c-(31/100)r
 \ge17/200-31/400=3/400.
\]

All four cases contradict (5), which is strictly smaller than 3/400. Thus every feasible E2 witness is excluded, including a witness tied with another E axis.

## 5. Exclusion of E3 for every G axis

### G0/E3

cH+cG0+E3 has D=c+(1+c)W and F=c^2a_A-csb_A+a_E+sa_H. For s>=0 the gap is at least

\[
 -183/200+2c-(81/100)c^2+s((4/5)c-33/50).
\]

The c polynomial is increasing on [3/4,1]. Its value at 3/4 is 207/1600, and the sine term is at least -(3/50)(7/10)=-21/500. Their sum exceeds 3/400.

For s=-r<=0, the gap is at least -183/200+2c-(81/100)c^2+r(1/2-(2/5)c+L). The r coefficient is positive and c>=9/10, so the gap is at least 2289/10000.

### G1/E3

cH+G1+E3 has D=c+2W and F=a_A+a_E+s(a_H-a_G). For s>=0, G1 forces s<=13/50. Thus the chord gives

\[
 D-F\ge11/40+(127/300)s-(8/7)s^2\ge11/40.
\]

For s=-r<=0, (4) gives D-F>=11/40+(651/4000)r-(8/7)r^2. Using r<=3/8 shows this exceeds 3/400.

### G2/E3

cH+G2+E3 has D=c+2W and F=ca_G+(c-s)b_G+a_E+sa_H-b_A. Complete the G circle with mass 3/8. After c^2+s^2=1, the gap is bounded below by

\[
 19/30-U-(3/8)q+3c-(2/3)c^2+
   (4/3)cs+|s|-s/2-sA_H,
\]

where A_H=V for s>=0 and A_H=L for s<=0. At zero sine and q=47/12 the constant is B0=199/2400. The loss of the c polynomial relative to c=1 is at most 2(1-c).

For s>=0, G2 forces s<=1/5 and hence c>=97/100. The sine coefficient is nonnegative, so the gap is at least B0-3/50=11/480.

For s=-r<=0, the remaining r coefficient is at least 1/6+L. By (4), the c loss is at most (8/7)r^2 <=(3/7)r. Since 1/6+L>3/7, the gap is at least B0.

### G3/E3

cH+G3+E3 has D=c+2W and F=a_G+cb_G+a_E+s(a_H-a_A)-cb_A. Complete the G circle with mass 3/8. The zero-sine constant at q=47/12 is again B0=199/2400, the c polynomial is (14/5)c-(2/3)c^2, and its loss is at most 2(1-c).

For s>=0, G3 forces s<=3/20 and c>=49/50. The remaining sine coefficient is at least 1-V+L>0, so the gap is at least B0-1/25=103/2400.

For s=-r<=0, use a_A<=V_A and a_H>=L. The remaining coefficient is at least 1-V_A+L=199/800. Equation (4) therefore gives

\[
 D-F\ge B0+(199/800-3/7)r
       \ge B0-(19/100)(3/8)=7/600>3/400.
\]

Again every E3 witness contradicts (5). The common reserve for the eight G/E exclusions is at least

\[
 3/400-3001/1000000=4499/1000000>0.
\]

## Conclusion and trust boundary

Under the stated small-mismatch and quarter-owner hypotheses, **every** feasible E axis belongs to {0,1}, independently of the selected G axis and of all owner ties. The proof also gives explicit positive/negative arc bounds for the remaining mixed-owner work. These are whole-domain chain and disk arguments; no interval table is substituted for the omitted cases.

The contraction to S<1/1000 remains an earlier open table-free gate. This note does not assert that small mismatch has been obtained without the existing affine table. No Lean or table source was changed, no compilation or CI was run, and no numerical optimizer output is a premise of any displayed inequality.
