# Independent full review of the radial-pair contact and transverse barrier

Date: October 28, 2026. Reviewer: recovery_audit.

**Verdict: PASS for the complete general physical lemmas and the entire
stated two-circle-B negative-return feature.** I read and independently
rederived the full source, including the continuous North-domain bounds
used by its caller. No change to the frozen source was required.

Reviewed exact source:

    TWO_RADIAL_BOUNDARY_UNITS_EXACT_CONTACT_AND_TRANSVERSE_RETURN_BARRIER.md
    bytes: 11811
    SHA-256: a0a4f1f25dd4ae6658be21bddcca75b21a851c7fc6696672f8c8ac8426478aac
    Git blob: 8047ca4915e0ea6329bfff5915a89b80ed8a09ff

The exact contact theorem needs d>=1 and no upper-radius bound. The
transverse barrier has its explicit compact scalar domain
1<=d<=61/60, 0<=q<=9/40. Neither general lemma uses a force or degree
equation. The final caller excludes physical-two-circle B with G.w<0
in the original North interface; it does not close the whole interface
or roof ABC.S.

## 1. Complete physical two-radial contact

For C=[d,d+1]n+[-1/2,1/2]e and R^2=(d+1)^2+1/4, the exact
angular shadow about n is [-phi,phi], phi=atan(1/(2d)). On a strict
interior ray of relative angle psi, its open radial interval is

    d/cos(psi)<r<min((d+1)/cos(psi),1/(2|sin(psi)|)).

At psi=0 the second upper bound is omitted. The interval is nonempty
for |psi|<phi and depends only on |psi|. For two such units whose
minor axis gap theta is less than 2phi, the bisector ray gives identical
nonempty open intervals, contradicting interior disjointness. A gap
greater than 2phi leaves disjoint closed shadows, contradicting actual
contact. Equality is therefore forced.

At theta=2phi their sole common ray meets each unit only at its inner
corner, of radius sqrt(d^2+1/4). The source's exact positive-e formula
is consequently correct:

    U=d^2+1/4,
    c=(d^2-1/4)/U, s=d/U,
    n_B=c n+s e, e_B=-s n+c e,
    P_CB=d n+(1/2)e=d n_B-(1/2)e_B.

I checked both components of the point identity and c^2+s^2=1.
Reflection covers the negative-e side. The actual physical intersection
is one point; the conclusion makes no choice of its original normal
inside the legitimate common support cone. Both physical circle
corners of each unit remain, regardless of later zero coefficients.

## 2. Every original supporting mean in the transverse barrier

For w=-q n+p e, p>0, p^2+q^2=1, and 0<=q<=9/40,
one has p>=sqrt(1519)/40>97/100. On 1<=d<=61/60,
U<13/10, s>10/13 and 0<c<1. Hence

    n_B.w=s p-c q>271/520>0,
    e_B.w=s q+c p>0.

Let the nonzero original normal G point from actual A into B, with
G.w<=0. If G's B-normal component G_n were negative, the actual
minimum-G support of B would be an outer circle corner when G_e!=0,
or its whole outer radial side when G_e=0. The first cannot be shared.
The second would put an actual unit beyond radial height d+1 with
width at least one, requiring d+2<=R, impossible. Thus G_n>=0.
The two positive w projections above force G_e<0.

Consequently the entire original support face, including every actual
mean when G_n=0, has e_B coordinate 1/2 and n_B coordinate at least d.
Its w projection is at least that of P'=d n_B+(1/2)e_B. I verified

    P'=N n+E e,
    N=d(d^2-3/4)/U=d(1-1/U),
    E=3/2-1/(2U),
    0<N<61/260<1/4, E>=11/10.

Therefore every such original support point has

    P_AB.w>=p E-q N
              >(97/100)(11/10)-(9/40)(1/4)
               =4043/4000>1.

The strict comparison remains at q=0, q=9/40 and G.w=0; it does
not discard a mean endpoint or require a singleton. A can have
arbitrary degree and need not itself be boundary. This is the full
printed general barrier, not merely a sampled normal subset.

## 3. Original North caller and its actual negative-return point

I separately reviewed both exact new inputs in full. Their unchanged
North domain has F=1-a in(59/60,1), F^2+b^2=d^2,
k=Ft/b in(1/2,1), the two full H3 rows, and

    A=Q+[0,1]j+[0,1]w,
    Q=(k,1-b), j=(-C_A,S_A), w=(S_A,C_A),
    Z_A=Q+w,
    D C_A=alpha+a+k, D S_A=beta-1+b-t,
    0<D<1, G.j>0, G.w<=0.

The present strict-negative feature has the actual AB vertex
V=Q+j, and B is assumed physically two-circle. C already has its
full physical two-circle mask. Their real CB point lies on the
positive-e side of C, so Section 1 fixes the actual B pose and contact.
It does not impose equal circle weights on either unit.

## 4. Entire continuous k and b estimates

From D C_A>k one has D>k; from D S_A<b-t one obtains

    S_A<(b-t)/k=b/k-b/F<b,
    W:=Q.w<k S_A+1-b<1-t<1.

If k>=3/4, this strengthens to S_A<b/3<1/10 and C_A>99/100.
The actual V then satisfies -1/4<V_x<0 and
0<V_y<1-2b/3. Every point of physical radial B has norm at least
d>1. Thus V in B would give

    1<|V|^2<1/16+(1-2b/3)^2,
    1-2b/3>sqrt(15)/4>29/30,
    b<1/20.

But then Z_A has x>3/4 and y>97/50, so its squared norm exceeds
1105/256 by 1551/160000. This contradicts actual containment and
proves 1/2<k<3/4 in the entire feature.

Using W<1-t, t=kb/F>kb and the exact A circle equation gives

    R^2<4-2b+b^2+(k^2-2bk)
        <73/16-(7/2)b+b^2.

The last quadratic in k is increasing on the whole relevant interval
k>1/2>b. Since R^2>17/4, one gets (7/2)b-b^2<5/16.
This expression is increasing on 0<b<31/120 and at b=1/10 exceeds
5/16 by 11/400. Hence b<1/10. None of these inequalities assumes
a discrete pose, an owner, a circle coefficient or a chosen mean.

## 5. Full two-row strip inequality and the real relative angle

For the side row set zeta=0; the radial support gives a_H=epsilon.
For the opposite row keep its actual zeta>0. The exact support and
the unchanged weak HC moment imply, in both cases,

    d^2>=(1+a_H)^2(1+zeta^2),
    a_H>=t alpha, 0<=zeta<t.

In the opposite row this uses c_H>=(1+a_H)zeta and the exact
d=(1+a_H+c_H zeta)/sqrt(1+zeta^2); it does not transfer the side
row's equality a_H=epsilon. Combining with d^2=(1-a)^2+b^2 and
a>0 gives zeta^2+2t alpha<b^2. Therefore

    alpha+zeta
      <b^2/(2t)+t/2-(t-zeta)^2/(2t)
      <=b^2/(2t)+t/2
      <b(F+1/(4F))<5b/4.

I checked the continuous monotonicity in t on t<b, the actual lower
bound t>b/(2F), and the exact final factorization
F+1/(4F)-5/4=(F-1)(F-1/4)/F<0. It follows that S_n<5b/4
for both complete original H3 rows, including the physical shared-HC
side row with its unchanged mean.

The actual w has C-frame coordinates

    w=-q n+p e,
    q=S_n C_A+C_n S_A>0,
    p=C_n C_A-S_n S_A=j.n>0.

Thus q<S_n+S_A<9b/4<9/40, and p^2+q^2=1. This checks every
general barrier premise using the actual frames, not an independently
selected comparison direction.

## 6. Complete contradiction and exact limits

The actual negative-return AB point V=Q+j has V.w=W<1. Section 2,
applied to the unchanged physical radial B,C and original normal G,
requires V.w>4043/4000>1. This is a strict contradiction over the
entire physical-two-circle-B/G.w<0 feature.

The proof keeps both B and C physical circle coefficients independent,
including either individual coefficient zero. It uses neither a false
leaf equation at C nor a shortened star at A. The original AB normal,
CB normal, actual contact points and all nine units remain.

The feature estimates k<3/4 and b<1/10 were proved using G.w<0.
The source correctly does not transfer them to the remaining G.w=0
side-mean row. Unique-circle B with negative G.w also remains outside
this source's own final contradiction and needs the separate all-mask
theorem. No whole original fine or coarse gate is closed here.

Both direct current pins match:

| Source | SHA-256 |
| --- | --- |
| OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md | 74fa5a6ffc854cf1f04e230baa77495c49debb570ef80c9f40c9bf6a25c2ab94 |
| BOUNDARY_CORNER_RETURN_AND_RADIAL_SIDE_TWO_PORT_DIAMETER_EXCLUSION.md | 40b4d692d48b172bca4320a9da98a34239007a61ebcff1fa7811291548086974 |

Their separate complete reviews are
REVIEW_NORTH_RADIAL_RETURN_UNIQUE_A_CORNER_RECOVERY_AUDIT_2026_10_28.md
and REVIEW_BOUNDARY_RETURN_RADIAL_SIDE_DIAMETER_RECOVERY_AUDIT_2026_10_28.md.
No inherited review was assigned to these new bytes. No source, gate,
metadata, original degree or mean was edited; no Lean, CI, numerical
pose certificate or remote write was used.
