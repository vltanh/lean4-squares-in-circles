# The complete side return under parallel K-owned HK is impossible

**Status: complete hand argument; author, root and separate independent full
saved-source/direct-prerequisite review passed on October 25, 2026. The
independent rational reconstruction checked all 70 exact coefficients,
integer floors and inverse identities. See REVIEW_PARALLEL_HK_2026_10_25.md.
No existing roadmap checkbox is changed by this branch exclusion.**

**Pinned prerequisites:** `f99f0cc7e93e3d0c2d78dbffaf0198d1996cd1ca`.

This source continues
[NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_NEAR_EXCLUSION.md](NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_NEAR_EXCLUSION.md).
That source proves the complete KB support fan and excludes its strict
near vertex. The present argument excludes the other member of that fan:
the entire K-owned min-f side, including a shared KB segment and every
original application mean. Their union excludes the **whole strict
K-owned HK branch parallel to AK**, not every upper-left diamond.

Keep the original nine physical squares, the full radius interval
\(79/40\le R\le\sqrt{1105}/16\), true H5/K3/A2/B2, the intact HXY
petal and all three completion squares. A and K are physically unique,
\(c_H\cdot z_A<0\), HA is H-owned singleton, AK is K-owned upper-left
singleton, and HK is strict K-owned singleton with the same normal as AK.
B may have either physical circle mask and either zero individual weight.

**Theorem.** KB cannot have the actual K-owned side normal \(-f\).
Together with the pinned near-return theorem this excludes the entire
stated parallel-HK branch. No B force equation is used below.

## 1. The unchanged geometry and the genuine K3 side mean

Use positively oriented coordinates (f,g) from the prerequisite. Write
\(q=R^2,\ q_0=6241/1600,\ Q=1105/256\).
Its Sections 1--3 give, before specializing to a near return,
\[
 K=[F-1,F]\times[h,h+1],\qquad z_K=(F,h+1),\qquad
 F^2+(h+1)^2=q,
\]
\[
 F>L>1/2,\quad F>1,\quad h<x<1,\quad
 U=(L_U,h),\quad L_U>F-1,\quad x=a-1.
\tag{1}
\]
The two original incoming applications on K are T=(L,h) and U.
Put
\[
 E=A_0>0,\quad d=-D_0>0,\quad E^2+d^2=1,\quad
 n=(E,d),\quad j=(-d,E),\quad t=d/E,
\]
\[
 H=U+[-1,0]n+[-1,0]j,\qquad
 X=F-1,\qquad \Delta=L_U-X>0.
\tag{2}
\]
Here n is still the actual HA normal. The original AK normal is g.

Let \(\alpha,\eta,\gamma>0\) be the actual AK, HK, KB magnitudes.
In the side case the full K equation and its origin moment give
\[
 \gamma=\lambda F,\qquad \alpha+\eta=\lambda(h+1),\qquad
 \gamma y_*=\alpha L+\eta L_U.
\tag{3}
\]
Thus the **original** KB application is \((X,y_*)\), with
\[
 h\le y_*\le h+1,\qquad y_*>0.
\tag{4}
\]
Both incoming forces and their distinct applications remain in (3).

The endpoint chart also has \(c,s>0,\ c^2+s^2=1\), and
\[
 \tau=F-L=1-\delta\in(0,1),\qquad L_U=L-c-st.
\]
Consequently
\[
 \Delta=1-\tau-c-st>0,\qquad
 0<t<\frac{1-c}{s}=:m<1.
\tag{5}
\]
In particular \(0<d<E\). These are statements about the original pose.

## 2. Two elementary exits, including every aligned B

First suppose \(h\le0\). Since \(h+1>0\), (1) gives
\[
 F\ge\sqrt{q_0-1}>17/10,\qquad 7/10<X<11/10.
\]
Every point of B has first coordinate in \([X-\sqrt2,X]\).
Hence its absolute first coordinate is below 11/10.

For a tilted B its right supporting vertex is the actual KB point
\(Q_B=(X,y_*)\). Write its inward orthonormal edges as
\[
 e=(-C,S),\quad v=(-S,-C),\qquad C,S>0,\quad C^2+S^2=1.
\tag{6}
\]
Physical HB contact and \(\max_H y=h\) imply \(y_*-C\le h\).
Therefore B's maximum second coordinate is at most
\(h+C+S\le\sqrt2\), and its minimum is greater than -1 by (4).
All corners have squared norm below \(121/100+2=321/100<q_0\).

For an aligned B choose its *geometric top-right vertex* \((X,y)\);
this is not a replacement of the mean in (3).
Its actual KB overlap gives \(y\ge y_*>0\), and HB contact gives
\(y-1\le h\). The same strict norm bound follows. This excludes \(h\le0\).

Now let \(h>0\). Then \(F<\sqrt{Q-1}<2\), so \(0<X<1\).
If B is aligned, its x interval is \([X-1,X]\).
KB contact implies its top coordinate is at least h, and HB contact
puts that top coordinate at most \(h+1\). Its bottom coordinate is
therefore greater than -1. Since \(h+1>1\), every corner satisfies
\[
 |z|^2\le \max\{X^2,(1-X)^2\}+(h+1)^2
       <F^2+(h+1)^2=q.
\tag{7}
\]
This includes every shared KB side and every endpoint mean.

It remains to handle tilted B, with (6), and
\[
 B=Q_B+[0,1]e+[0,1]v,\quad Q_B=(X,y),\quad
 h\le y\le h+1,\quad y>0.
\tag{8}
\]

## 3. The complete geometric HB support cover

For two touching, interior-disjoint squares, the separating-axis theorem
supplies a separating direction along a side axis of one of them, with
equal supports. This is a **geometric auxiliary axis**, not a change of
the selected HB force or its original mean.

If H owns that auxiliary axis M, the radius-free
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md applied to H,K,B gives
\(M\cdot g\ge0\). Of H's four side normals this permits only n,j.
The n face has x-coordinate at least \(L_U>X\), so cannot touch B.

If B owns M, its four possibilities are e,-e,v,-v.

* M=-e is impossible because
  \((-e)\cdot(Q_B-U)=-C\Delta-S(y-h)<0\).
* The minimum-v face of B is \(Q_B+[0,1]e\), of height at least h.
  H reaches height h only at U, whose first coordinate is \(L_U>X\).
  Thus M=v is impossible, including y=h.
* For M=-v, its minimum on B is at \(Q_B+v\), and
  \[
   (-v)\cdot(Q_B+v-U)=-S\Delta+C(y-h)-1<0.
  \]
  Here \(y-h\le1\) and \(C<1\).
* Only M=e remains.

For M=j, \(j\cdot e=dC+ES>0\).
If \(j\cdot v>0\), the minimum is Q_B, which cannot lie on H.
If \(j\cdot v=0\), support equality would require
\(j\cdot(Q_B-U)=d\Delta+E(y-h)=0\), also impossible.
Thus \(j\cdot v<0\), and the common point is \(Q_B+v=U-\sigma n\)
for its actual geometric \(0\le\sigma\le1\). Equating coordinates gives
\[
 S\le E-\Delta,\qquad
 y=h+C-t(\Delta+S).
\tag{9}
\]

For M=e, its j component is positive. A positive n component would
expose U, which cannot be in B. A zero n component is already M=j.
Otherwise H's support is its actual vertex \(U-n\).
Writing \(U-n=Q_B+\theta v,\ 0\le\theta\le1\), gives
\[
 \theta=\frac{E-\Delta}{S},\quad S\ge E-\Delta>0,\quad
 y=h-d+\frac CS(E-\Delta).
\]
The inequality \(y\ge h\) gives \(C/S\ge d/(E-\Delta)>t\).
Consequently
\[
 h+C-t(\Delta+S)-y
 =(S-E+\Delta)(C/S-t)\ge0.
\tag{10}
\]
The support cover is exhaustive, including side endpoints.
Both cases therefore imply the single whole-orientation envelope
\[
                    y\le h+C-t(\Delta+S)<h+C-tS.
\tag{11}
\]
No force equation at B, fixed-tip selection at B, or circle mask was used.

## 4. All four B corners and the easy F range

Set \(k=1-t\in(0,1)\). The corners are
\[
 Q_B,\quad Q_B+v,\quad Z_1=Q_B+e,\quad Z_2=Q_B+e+v.
\]
The first has squared norm at most \(X^2+(h+1)^2<q\).
The second has both coordinates strictly between -1 and 1:
its second coordinate is \(y-C>-1\) and is below \(h<1\).
Its squared norm is below \(2<q\).

For the two remaining corners, (11) gives
\[
 |Z_1|^2\le (X-C)^2+(h+C+kS)^2,
\tag{12}
\]
and, when \(Z_2\)'s second coordinate is nonnegative,
\[
 |Z_2|^2\le(\sqrt2-X)^2+(h+k)^2.
\tag{13}
\]
If that coordinate is negative, its magnitude is below one and
\(|Z_2|^2<2+1=3<q\).

Put \(z=S/(1+C)\in(0,1)\). The exact difference in (12) is
\[
 q-(X-C)^2-(h+C+kS)^2=\frac{4P(F,h,k;z)}{(1+z^2)^2},
\]
\[
 P=h z^4+k(1-h)z^3+(X+h+2-k^2)z^2-k(h+1)z+X.
\tag{14}
\]
If \(F\ge4/3\), set \(W=h+1\). Then \(X\ge1/3,\ 1<W<8/5\), because
\(64/25-(Q-16/9)=1231/57600>0\). Since \(h<1\) and \(k<1\),
\[
 P\ge X-Wz+(X+W)z^2.
\]
Its discriminant is strictly negative:
\[
 4X(X+W)-W^2
 \ge\frac43\left(\frac13+W\right)-W^2
 >\frac4{225}>0.
\tag{15}
\]
Thus (12) is strictly below q.

For (13), \(X\ge1/3\) gives \(\sqrt2-X<X+1=F\), and
\(h+k<h+1=W\). This excludes every B orientation when \(F\ge4/3\).

## 5. A comparison covering the complete remaining parameter domain

Assume \(1<F<4/3\). Keep \(m=(1-c)/s\), so
\[
 c=\frac{1-m^2}{1+m^2},\qquad s=\frac{2m}{1+m^2}.
\]
The original A2 concurrence, and the two original circle equations,
give exactly
\[
 t=\frac{(s-c)L+s^2-sh}{c(L+s)},\qquad
 h=\frac{2L(s-\tau)-\tau^2}{2(1+c)}
   =Lm-\frac{(1+m^2)(2L\tau+\tau^2)}4<Fm.
\tag{16}
\]
For the first identity, the A concurrence has coordinates
\((L,L(h-c)/(L+s))\), while \(P=(L-c,h-s)\); their difference
is a positive multiple of \(n=(E,d)\).
No concurrence at K is asserted.

Let \(T(F,m,\tau)\) denote the first expression in (16), after
\(L=F-\tau\) and the second expression for h are substituted.
Define \(T_0(F,m)=T(F,m,0)\).
Throughout \(0\le\tau\le\tau_{\rm actual}<F\),
\[
 \partial_\tau T
 =\frac{m(1+m^2)^2\{(1+m^2)(F^2+(F-\tau)^2)
                  +4m(F-\tau)+4\}}
        {2(1-m^2)((F-\tau)(1+m^2)+2m)^2}>0.
\tag{17}
\]
Therefore \(t>T_0\). This is an algebraic comparison, not a motion
of the physical packing.

From (5) and (17), \(1-c-sT_0>0\). Its exact identity is
\[
 1-c-sT_0=
 \frac{2m\{F(1-m)(1+m^2)-2m^2\}}
 {(1-m^2)(F(1+m^2)+2m)}.
\tag{18}
\]
The function \(J(m)=2m^2/((1-m)(1+m^2))\) increases on (0,1), since
\[
 J'(m)=\frac{2m(m^3-m+2)}{(1-m)^2(1+m^2)^2}>0.
\]
Also \(J(61/100)-4/3=10236/178373>0\).
Thus \(m<61/100\).

Since \(q\le F^2+(1+Fm)^2\) and \(q\ge q_0\), it follows that
\[
 F>43/40,\qquad m>1/3.
\tag{19}
\]
The exact reserves proving these two implications at their respective
endpoints are
\[
 q_0-\left[(43/40)^2+(1+(61/100)(43/40))^2\right]
       =55871/16000000>0,
\]
\[
 q_0-\left[(4/3)^2+(1+4/9)^2\right]=4721/129600>0.
\]

The first exact polynomial packet in Section 8 proves
\[
 \partial_m T_0>2
 \quad\hbox{on }1\le F\le4/3,\quad1/3\le m\le61/100.
\tag{20}
\]
Moreover
\[
 \partial_F T_0=
 -\frac{2m(1+m^2)^2}
 {(1-m^2)(F(1+m^2)+2m)^2}<0,\qquad
 T_0(4/3,1/3)=-13/116.
\tag{21}
\]
In the actual domain \(T_0<t<m<1\). Hence
\[
 0<k_0:=1-T_0\le129/116,\qquad k<k_0.
\tag{22}
\]

## 6. The complete Z1 inequality reduces to one circle boundary

For fixed F put
\[
 h_b=\sqrt{q_0-F^2}-1>0,\qquad m_b=h_b/F.
\]
Then \(h\ge h_b,\ m\ge m_b>1/3\).

First, whenever \(z\ge k_0\), one also has \(z\ge k\).
The representation
\[
 P=X(1+z^2)+hz(1+z^2)(z-k)
      +(2-k^2)z^2-kz(1-z^2)
\]
is strictly positive: its last two terms are at least
\(z^2(1-k^2+z^2)\), and \(X>0\).

For \(z<k_0\), \(P\) decreases in k on the relevant domain, because
\[
 \partial_kP=z\{(1-h)z^2-2kz-(h+1)\}<0.
\]
After substituting k_0 it decreases in h, since
\(\partial_hP=z(1+z^2)(z-k_0)<0\).
Thus
\[
                P(F,h,k;z)\ge P(F,Fm,k_0;z).
\tag{23}
\]

The right side is nondecreasing in m on the whole comparison interval
\([m_b,m]\). Here is the full derivative argument.
Write \(h_0=Fm\) and
\(D=(h_0+1)-(1-h_0)z^2+2k_0z>0\).
For \(z\ge k_0\) both derivative contributions are nonnegative.
For \(0<z<k_0\), use
\[
 k_0D-(h_0+1)(1+z^2)(k_0-z)
 =z\{(h_0+1)z^2-2k_0z+2k_0^2+h_0+1\}>0.
\]
The quadratic in braces is positive by completing its square.
Equations (20)--(22) give
\(F k_0\le43/29<2\le(\partial_mT_0)(h_0+1)\).
Therefore
\[
 \partial_m P(F,Fm,k_0;z)
 \ge zD\left(\partial_mT_0-\frac{Fk_0}{h_0+1}\right)>0.
\]
At z=0 the derivative is zero. Consequently (23) is at least
\[
          P(F,h_b,1-T_0(F,m_b);z).
\tag{24}
\]

Parametrize this single circle boundary rationally:
\[
 R_0=79/40,\quad F_b(w)=\frac{2R_0w}{1+w^2},\quad
 W_b(w)=\frac{R_0(1-w^2)}{1+w^2},\quad h_b=W_b-1,\quad m_b=h_b/F_b.
\tag{25}
\]
Every actual boundary point in (24) has
\(w\in I=[29/100,7/18]\). Indeed \(F_b\) is increasing for \(0<w<1\),
and the exact endpoint reserves are
\[
 43/40-F_b(29/100)=7963/433640>0,\quad
 F_b(7/18)-4/3=11/11190>0.
\]
Define \(t_b=T_0(F_b,m_b),\ k_b=1-t_b\), and
\(P_b(z)=P(F_b,h_b,k_b;z)\).

Section 8 proves on all of I that \(-1/8<t_b<1\).
Thus \(0<k_b<9/8,\ 0<h_b<1,\ X_b>0\), and
\[
 a_2=X_b+h_b+2-k_b^2>47/64>0.
\]
Set \(z_0=3/8,\ a_0=P_b(z_0),\ a_1=P_b'(z_0)\).
Convexity of \(z^3,z^4\) on \(z\ge0\) gives
\[
 P_b(z)\ge a_0+a_1(z-z_0)+a_2(z-z_0)^2.
\tag{26}
\]
The 17-coefficient packet in Section 8 proves
\(4a_2a_0-a_1^2>0\) on the entire I.
The quadratic in (26) is therefore strictly positive for every real z.
This completes (24), (23), (14), and excludes Z1 on the entire original
low-F domain.

## 7. The complete Z2 inequality

For a nonnegative second coordinate, subtract the right side of (13)
from the actual q:
\[
 q-\{(\sqrt2-X)^2+(h+k)^2\}
   =2X(1+\sqrt2)+2ht-(1-t)^2.
\tag{27}
\]
If \(F\ge5/4\), then \(X\ge1/4,\ h,t>0\), and (27) exceeds
\((\sqrt2-1)/2>0\).

If \(F<5/4\), the circle boundary parameter of Section 6 lies in
\(J=[29/100,9/25]\), because
\(F_b(9/25)-5/4=25/2824>0\).
The final two packets in Section 8 prove, throughout J,
\[
 t_b>0,\qquad
 \frac{24}{5}(F_b-1)+2h_bt_b-(1-t_b)^2>0.
\tag{28}
\]
Equations (17),(20) give \(t\ge t_b>0\), and \(h\ge h_b\).
The function \(2ht-(1-t)^2\) increases in both h and t for
\(h>0,\ 0<t<1\). Since \(\sqrt2>7/5\), (27) is strictly greater
than the second expression in (28). This excludes Z2.

Every corner of the actual B is now strictly inside its required circle.
Convexity excludes any circle contact anywhere on B.
This contradicts its positive circle load, without using a B2 equation.
All physical one-/two-corner masks, zero individual weights, original
KB means, HB owners and weak contact endpoints have been included.

## 8. Exact finite arithmetic, with no sampled signs

The supplement
[NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_SIDE_CHECK.py](NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_PARALLEL_HK_SIDE_CHECK.py)
reconstructs all identities, **70 rational Bernstein coefficients**,
their displayed integer floors, and the inverse polynomial identities.
An optional `--write-certificate PATH` writes every exact coefficient.
The integer-floor lists below also specify a compact certificate in this
manuscript; the checker is an arithmetic supplement, not a geometric premise
or an independent reviewer.

For a polynomial N on a rectangle, substitute each variable
\(v=a+(b-a)x\) and write \(N=\sum_\alpha A_\alpha x^\alpha\).
At natural multidegree n its Bernstein coefficient is exactly
\[
 B_i=\sum_{\alpha\le i} A_\alpha
           \prod_j\frac{\binom{i_j}{\alpha_j}}{\binom{n_j}{\alpha_j}}.
\tag{29}
\]
All basis polynomials are nonnegative and sum to one.

Here are the precise polynomial definitions. Each N is the specified
rational expression multiplied by its displayed positive denominator.
Put
\[
 A(w)=119w^2-158w-39,\quad B(w)=119w^2+158w-39.
\]
On I, A<0<B; the other variable factors below are positive. The rational
boundary function is explicitly
\[
 t_b(w)=
 \frac{200533921w^4+174520164w^3+43077762w^2-57195684w+2313441}
 {4641A(w)B(w)}.
\]

| Packet | Rational expression | Positive denominator | Domain / degree |
|---|---|---|---|
| D | \(\partial_mT_0-2\) | \((1-m^2)^2(F(1+m^2)+2m)^2\) | \([1,4/3]\times[1/3,61/100]\), (2,8) |
| L | \(t_b+1/8\) | \(-37128AB\) | I, 4 |
| U | \(1-t_b\) | \(-4641AB\) | I, 4 |
| S | \(4a_2a_0-a_1^2\) | \(-873480818707660800(1+w^2)^2A^3B^3\) | I, 16 |
| T | \(t_b\) | \(-4641AB\) | J, 4 |
| G | \((24/5)(F_b-1)+2h_bt_b-(1-t_b)^2\) | \(2153888100(1+w^2)A^2B^2\) | J, 10 |

For each row the following lists are the exact floors of \(B_i/\sigma\).
They are all positive. Indices increase from 0 to the displayed degree;
in D, each row fixes the F index and increases the m index.

```
D, sigma=1:
  1 1 1 1 2 2 3 4 5
  1 1 1 1 2 2 3 4 5
  1 1 1 1 2 2 3 4 6

L, sigma=10^6: 45 41 33 21 3
U, sigma=10^5: 8 37 73 116 169
S, sigma=10^26:
  2 6 10 14 20 26 32 38 45 51 55 59 59 56 47 31 5
T, sigma=10^6: 4 4 3 2 1
G, sigma=10^15: 5 5 6 6 7 7 8 8 8 9 9
```

These are one rectangle and two complete intervals, not a covering by
sampled physical poses. The identities in (16)--(29) supply every domain
map and denominator sign. The saved checker verifies the full reverse
Bernstein identity, not just coefficient sign or a floating-point minimum.

## 9. Assembly and precise remaining status

The pinned near-return source exhausts the full original KB fan under
strict K-owned HK parallel to AK. Its near-vertex theorem and the present
whole-side theorem therefore exclude that **entire HK owner branch** for
both physical B masks and throughout the original radius interval.

This branch exclusion alone does not close either original LOW gate
`M6.TB4.DIAMOND_HUB.NEGATIVE_OWNER.H_OWNED.{UUS,UUU}.LOW.AK_K_OWNED`:
they also contain H-owned HK, free HK and the f-owned/shared HK family.
The corresponding HIGH gates are separately closed by the uniform
triangle-tip theorem. Root and independent review passed this whole
manuscript, its direct prerequisites and all 70 coefficient identities;
see REVIEW_PARALLEL_HK_2026_10_25.md. No further ID or checkbox changes,
and the full older dependency-chain audit remains open.

No Lean compilation or CI was run. This result does not close the
upper-left ABC family, either remaining alternating C6 family,
the coarse C2.34.b0 cell, the unrestricted n=9 theorem, or equality.
