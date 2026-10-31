# A shared unique-C side return requires negative root-normal projection

Date: October 25, 2026.

**Status: complete hand implication; independent root full-source and
scope review passed on October 25, 2026. See
REVIEW_ABC_UNIQUE_REFINEMENTS_2026_10_25.md.** The entire genuinely shared side return with cn>=0 is
excluded below. The full cn<0 domain is now independently excluded by
ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md. This source supplies only
the stated sign implication and changes no original gate.

Retain the original H--A--B--C--H component and intact HXY petal, true
H4/A2/B2/C2, all nine physical squares, all three completion squares,
every original force and application mean. A and B are physically unique,
A has negative H-pressure, HA is H-owned, and AB is its original B-owned
upper-left singleton. BC has the minimum-f side normal and is genuinely
shared with a physically unique C. Work on the entire original interval
q in [6241/1600,1105/256].

Use the unchanged chart

    zA=(a,b), a>b>3/5, a^2+b^2=q,
    x=a-1, P=(x,b-1), T=(x,b),
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    n=(u,v), j=(-v,u), 0<u<=v, u^2+v^2=1,
    H=P+[-1,0]n+[r-1,r]j, 0<r<1,
    E=n dot f=su+cv>0, D=n dot g=sv-cu,
    L=T dot f=xs+bc, h=T dot g=-xc+bs.

The true B2 force and moment equations for k_BC=-f give

    zB=beta f+Wg, beta^2+W^2=q, W>1/2,
    B=[beta-1,beta]f+[W-1,W]g,
    h=W-1, 0<tau=beta-L<1,
    Q=(beta-1)f+eta g, eta=L W/beta>0.

Q is the original shared mean. The endpoint-owned/shared reflection
theorem ABC_RETURN_OWNER_NONNEGATIVE_ENDPOINT_PRESSURE.md applies to this
actual unique B/C pair and gives c_H dot F_C>=0, with every HC owner and
mean retained. No C-pressure sign is assumed before this accepted input.

The beta>3/2 physical C-corner alternative is excluded by the complete
corrected theorem ABC_UNIQUE_SHARED_SIDE_POSITIVE_CORNER_EXCLUSION.md.
At beta=3/2, C is physically radial, outside the present mask and already
covered by its complete radial side theorem. Thus it remains to consider
the entire alternative beta<3/2 below.

**Theorem.** Every actual surviving shared unique-C return has

    cn=c_H dot n<0.

The proof does not use a fixed-tip selection at the variable BC mean.

## 1. Complete shared negative-f C geometry

Positive g coordinate eta of the proper C concurrence forces the actual
circle corner to have positive g coordinate. The actual unique C is

    U=beta-2<0, V=sqrt(q-U^2)>0,
    C=[U,U+1]f+[V-1,V]g, zC=U f+Vg,
    qC=kappa zC, kappa=eta/V in (0,1],
    Delta=V-W.

The mean remains in the actual shared interval, hence

    max(W-1,V-1)<=eta<=min(W,V).

The original circle identities give

    a=W+(beta^2-L^2)/2>W, b<beta.

Because beta<3/2, W>sqrt(q-9/4)>1 and h>0. The original c>0 says
Lb>hx. Squaring the two positive sides and using
L^2+h^2=x^2+b^2 gives

    (b^2-h^2)(x^2+b^2)>0,
    b>h=W-1.

Therefore W<beta+1. If beta<=4/5, then
q=beta^2+W^2<beta^2+(beta+1)^2<=97/25<6241/1600,
a contradiction. Thus

    4/5<beta<3/2, 0<-U<6/5,
    V>3/2>-U.

The last comparison follows by squaring, since
q-U^2>6241/1600-36/25>9/4.

We also have the useful complete sign

    Delta+s>0.                                      (1)

If beta>=1, Delta>=0. If beta<1, then W>17/10 and V>3/2, while

    -Delta=4(1-beta)/(V+W)<1/4.

Moreover h=bs-xc<bs and b<beta<1 give s>h>7/10. Hence
Delta+s>9/20 in this entire second alternative. No angle interval is
discarded in proving (1).

## 2. The full actual HC support fan

Let m be the actual H-to-C unit normal, and nu,mu_C,lambda_C>0 the
unchanged BC,HC and circle magnitudes. The true C equations are

    lambda_C zC=-nu f+mu_C m,
    mu_C det(R,m)=-nu eta<0.                         (2)

Their g component gives m_g>0. Thus the complete possible HC feature
is C's lower-g side or one of its endpoints. Its original side mean is
retained when m=+g, including either mean endpoint.

At the strict right endpoint R=(U+1)f+(V-1)g, proper concurrence makes
m a positive multiple of qC-R. The vector is nonzero: coincidence would
force V=-U, contrary to Section 1. Its exact moment is

    det(R,qC-R)=kappa(U+V)>0,

contradicting (2). This excludes that entire strict endpoint.

At the strict left endpoint R=Uf+(V-1)g, the actual ray is

    qC-R=(-U)(1-kappa)f+[1-(1-kappa)V]g.

Its two components are strictly positive by its actual strict vertex
feature and m_g>0. Every remaining actual HC is therefore either

    m=g, or a strict left-endpoint ray with m_f,m_g>0. (3)

No claim that the latter ray is H-owned or nonfree has been made.

## 3. Every surviving actual return has positive j component

For the side row m=g, m dot j=E>0. For the strict left endpoint, if
D<=0, then

    m dot j=-D*m_f+E*m_g>0.

Suppose D>0 in that endpoint row. Its actual displacement from P is

    R-P=(tau-2+c)f+(Delta+s)g.

The first coefficient is negative because tau,c<1, and the second is
positive by (1). Consequently

    (R-P) dot j=(2-tau-c)D+(Delta+s)E>0.             (4)

If m dot j<0, its H support is the bottom j side, whose original
coordinates satisfy (R-P) dot j=r-1<0, contradicting (4). If m dot j=0,
then m is one of the two H axes parallel to n, excluded by the accepted
whole TRIANGLE_C4_THREE_LOAD_PARALLEL_EXCLUSION.md at precisely this
actual H4/intact-petal scope. Hence in every remaining row,

    m_j=m dot j>0.                                  (5)

This is a complete physical normal-cone argument; it includes free HC
and uses no new generic condition.

## 4. The entire cn>=0 domain contradicts true block pressure

Suppose cn>=0. The original unique A has zA dot n>0 and zA dot j<0.
Its actual negative H-pressure therefore implies cj=c_H dot j>0.

If m_n=m dot n>=0, (5) gives c_H dot m>0. The genuine H4 equation is

    mu n+mu_C m+Mpetal=0,

where mu,mu_C>0 and the intact petal satisfies c_H dot Mpetal>0 by
BOWTIE_CELL_CLOSED.md Section 2. Its scalar product with c_H is strictly
positive, a contradiction.

If m_n<0, (3) forces D<0: this is immediate for m=g, and otherwise
m_n=E*m_f+D*m_g with E,m_f,m_g>0. Thus

    c_H dot f=E*cn-D*cj>0.

The true A and B force equations, with the unchanged positive
magnitudes, cancel only their common AB force and give

    F_A+F_B=mu n+nu f.

Their whole block therefore has strictly positive H-pressure. The
accepted reflected-owner result gives c_H dot F_C>=0; the intact petal
has strictly positive pressure. This contradicts the genuine component
equation F_A+F_B+F_C+Mpetal=0.

Both signs of m_n and every actual HC feature have been exhausted.
Hence cn<0 on the entire surviving shared unique-C side family.

## 5. Precisely retained unresolved statement

The remaining complete scalar domain retains all original restrictions,
including a>b>3/5, c,s>0, 0<beta-L<1, the actual shared interval for eta,
proper A concurrence, negative A pressure and cn<0. All containment and
nonoverlap hypotheses, actual H offset and three completion squares remain.

A sufficient whole-domain geometric exit would be

    V-W+s > E+max(0,-D).                            (6)

Indeed the unchanged H has

    max_H(g dot x)=W-1-s+max(0,-D)+rE
                 <W-1-s+max(0,-D)+E,
    min_C(g dot x)=V-1.

Thus (6) would strictly separate the actual H and C for every HC owner
and mean. Inequality (6) is not proved by this source. The entire actual shared
family is now excluded by the separate complete distance/separator
argument in ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md. Numerical
diagnostics of it are not proof premises or certificates. No full shared
side family, unique-C return family, UUU gate, or coarse parent is claimed
closed here. No Lean compilation or CI was run.
