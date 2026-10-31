# A whole-domain circle-coordinate bound in the f-interface diamond

**Status: complete hand scalar implication; author and independent root
saved-source/geometric/algebra review passed. See REVIEW_STRUCTURAL_INPUTS_2026_10_25.md.
No full diamond gate is closed by this input.**

Keep the original upper-left K-owned AK chart, every physical square,
true H5/K3/A2/B2, every original force and mean, and the intact petal. Let
q0=6241/1600. The result below uses A's true degree two, the real HAK
contact geometry, the original negative A pressure and K's actual positive
g circle coordinate. It does not use a K2 concurrence or change a mean.

## 1. Precise theorem

Use the original coordinates

    zA=(a,b), a>b>3/5, a^2+b^2=q>=q0,
    n=(u,v), j=(-v,u), 0<u<=v, u^2+v^2=1,
    g=(-c,s), f=(s,c), c,s>0, c^2+s^2=1,
    E=su+cv, d=sv-cu=-p<=0, E^2+p^2=1.

Write x=a-1>0, L=xs+bc, h=-xc+bs. The actual f-owned HK branch,
including its d=0 shared endpoint, has

    delta=c-rp, 0<delta<1, r>u,
    K=[L-delta,L+1-delta] x [h,h+1]

in its positively oriented (f,g) frame. The strict r>u is the original
negative-pressure consequence proved in the complete HK fan and in the
high-radius triangle manuscript; it uses no H/K/B equation.

Set tau=1-delta, F=L+tau and X=F-1. Suppose the actual K circle corner is

    zK=(F,W), W=h+1>0, F^2+W^2=q.                         (1)

Then

    F>1+p, or equivalently X>p.                          (2)

The hypothesis (1) is automatic in the original KB side branch k=-f:
K's full genuine force equation has g component kappa W=alpha>0,
where alpha is the original positive AK force. The f coordinate of K's
center is positive: delta<=c and L>(3/5)c give
L+1/2-delta>1/2-(2/5)c>1/10. Thus its physical far f coordinate is F.
The g force sign rules out the negative far g corner. This is a K3 use,
and retains the third HK force and every KB side mean.

The theorem itself applies whenever (1) is independently known. It does
not assign this circle corner in the other KB features without proof.

## 2. Reduction of the contrary case to one scalar estimate

The inverse unit-vector identities are

    u=Es+pc, v=Ec-ps.

As u<=v, one has E(c-s)>=p(c+s), hence c>=s and E>=p. Consequently

    0<=p<=1/sqrt(2)<5/7.

Put w=Ev. From r>u,

    delta=c-rp<=c-up=Ev=w,
    tau>=1-w.                                            (3)

The weak inequality includes p=0 and its genuine shared-HK endpoint.
Because x>0 and b>0, L>0. Assume F<=1+p. Then

    L=F-tau<=p+w.                                        (4)

In the K frame, zA=(L+s,h-c). Subtracting its squared radius from (1)
gives the exact identity

    h={L(s-tau)-tau^2/2}/(1+c).                          (5)

For fixed positive L the expression in (5) strictly decreases with tau.
If s-1+w>=0, (3)--(4) therefore give

    h <= {(p+w)(s-1+w)-(1-w)^2/2}/(1+c).                 (6)

If s-1+w<0, the same comparison and L>0 give instead

    h < -(1-w)^2/[2(1+c)].                               (7)

Section 4 proves the following single scalar inequality on the entire
unit-vector domain c>=s>=0, E>=p>=0:

    {(p+w)(s-1+w)-(1-w)^2/2}/(1+c)+p/3 < 1/5,
    w=E(Ec-ps).                                          (8)

Thus (6) implies h+p/3<1/5. The alternative (7) has the same consequence
by an even shorter bound. Indeed v=Ec-ps<=E, so 1-w>=p^2. Hence

    h+p/3 < p/3-p^4/4 <= (p+4)/27 <= 5/27 < 1/5.         (9)

The middle comparison is the exact tangent inequality

    p^4-(32/27)p+16/27
      =(p-2/3)^2(p^2+(4/3)p+4/3)>=0.

No subdivision of angles or poses is used in (8)--(9).

## 3. The circle contradiction

Both alternatives give 0<W=h+1<6/5-p/3. Consequently

    q=F^2+W^2 < (1+p)^2+(6/5-p/3)^2.

The last expression increases with p>=0, since its derivative is
6/5+(20/9)p>0. As p<5/7,

    q < (12/7)^2+(101/105)^2
      =42601/11025 <6241/1600=q0.                        (10)

The last strict reserve is exactly 25817/705600. This contradicts the
original radius window and proves (2). All r and delta endpoints allowed
by the original branch were retained. The d=0 shared-HK means do not enter
the scalar comparison and are unchanged.

## 4. A table-free proof of the one scalar inequality

Put

    m=s/(1+c), z=p/(1+E),
    c=(1-m^2)/(1+m^2), s=2m/(1+m^2),
    E=(1-z^2)/(1+z^2), p=2z/(1+z^2).

The full physical domain is contained in the single rectangle
0<=m,z<=5/12, since c>=s and E>=p imply m,z<=sqrt(2)-1<5/12.
Let M=1+m^2, T=1+z^2, D=MT^2, and define the explicit polynomials

    A=(1-z^2)[(1-z^2)(1-m^2)-4zm],
    B=2zMT, C=2mT^2,
    G=12MT^4-40zMT^3-30(B+A)(C-D+A)+15(D-A)^2.           (11)

Their exact identity is

    G/(30D^2)
      =(1+c)(1/5-p/3)
        -(p+w)(s-1+w)+(1-w)^2/2,
    w=A/D.                                              (12)

All denominators are positive. It remains to prove G>0 on that one
rectangle. Here is a direct completion-of-squares proof, without a
Bernstein table or a generated sign certificate.

Expand G=sum_{i=0}^8 P_i(m) z^i. The nine ordinary coefficients are

    P0=P8=12-60m+72m^2+60m^3,
    P1=-40+320m^2-240m^3+120m^4,
    P2=168+240m-192m^2+240m^3+120m^4,
    P3=120-720m+480m^2+120m^4,
    P4=72+120m+912m^2-120m^3,
    P5=120-720m^3+120m^4,
    P6=168-240m-192m^2-240m^3+120m^4,
    P7=-40-240m-160m^2+120m^4.                            (13)

First P0>2 throughout 0<=m<=5/12. With h0=m-1/3 in [-1/3,1/12],

    P0=20/9+8h0+(132+60h0)h0^2
       >=20/9+8h0+112h0^2
       >=20/9-1/7=131/63>2.

Also P4,P5,P6>0 directly; respective lower bounds obtained by dropping
positive terms are 4559/72,815/12,623/36. Furthermore

    P1>=-40+220m^2,
    P2>=168+160m,
    P3 z^3>=-720m z^3>=-300m z^2,
    P7 z^7>=-(1510/9)z^7>-3z^2  for z>0.                (14)

For z=0 the last inequality is read weakly. Its coefficient comparison
is (1510/9)(5/12)^5<3. Dropping only nonnegative terms in (13), (14)
gives

    G>=P0+(-40+220m^2)z+(165-140m)z^2.                  (15)

Set A0=165-140m>=320/3. The discriminant of the quadratic on the right
is strictly negative because

    4A0 P0-(-40+220m^2)^2
      =80[79-579m+1234m^2-9m^3-1025m^4].                (16)

To check its sign without an interval table, put x0=m-1/4 in
[-1/4,1/6]. The polynomial in brackets is exactly

    1851/256-(111/4)x0
      +[6743/8-1034x0-1025x0^2]x0^2.                   (17)

The bracket multiplying x0^2 is concave in x0, and its two endpoint
values exceed640. At the smaller endpoint value the excess is149/72.
Thus (17) is at least

    1851/256-(111/4)x0+640x0^2
      >=1851/256-(111/4)^2/2560
      =283839/40960>0.                                 (18)

Equations (16)--(18) make (15) positive for every real z. This proves
G>0, then (12) gives (8), completing the entire scalar proof.

## 5. Exact scope retained

The conclusion F>1-d holds for the full f-owned/shared HK interval with
the genuine positive-g K circle corner. In particular it holds for every
original KB=-f side mean and both physical B masks. It supplies a uniform
geometric coordinate bound while retaining K3; it does not exclude the
KB side or any HB owner by itself.

In particular, when HB is B-owned, its B2 force signs can select the
opposite B corner rather than the upper adjacent corner. No different
corner is substituted to turn (2) into a return exclusion. The remaining
full force/torque and H5/petal join is still required.

The author reconstructed the polynomial identity (11)--(13), every
coefficient bound and all endpoint reserves with exact rational
arithmetic. No numerical minimizer, pose mesh, coefficient certificate,
Lean compilation or CI is a proof premise. Root independently reconstructed
the entire polynomial, its discriminant and shifted form, all coefficient
bounds and every exact reserve, and checked the full geometric scope.
No roadmap checkbox or gate ID changes here.
