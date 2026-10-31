# The complete adjacent-circle fan after a strict B-owned side return

Date: October 25, 2026.

**Status: complete hand owner/feature reduction; independent root
full-source, direct-prerequisite, analytic and exact-identity review
passed on October 25, 2026. See
REVIEW_ABC_ADJACENT_FAN_AND_FAR_COORDINATE_2026_10_25.md.** Subsequent
complete independently reviewed sources now exclude the entire HC
side and R1 endpoint for every beta. Only the original R0/j equations
in Section 6 remain unresolved. No original gate or checkbox changes.

Retain the original H--A--B--C--H component, true H4/A2/B2/C2, intact HXY
petal, all nine physical squares and all three completion squares, every
original positive force, application mean, physical mask and offset.
Assume the unchanged negative unique A, H-owned HA, B-owned upper-left
AB chart, with B and C physically unique. BC is a strict B-owned
singleton on B's minimum-f side. Work on the entire declared interval
q in [6241/1600,1105/256].

## 1. The original side point and exhaustive C circle-corner cover

Use the original notation from
ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md:

    zA=(a,b), a>b>3/5, a^2+b^2=q,
    P=(a-1,b-1), T=P+e_y,
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    n=(u,v), j=(-v,u), 0<u<=v, u^2+v^2=1,
    H=P+[-1,0]n+[r-1,r]j, 0<r<1,
    E=n dot f>0, D=n dot g, j=-D f+E g,
    L=T dot f, h=T dot g, W=h+1,
    zB=beta f+Wg, beta,W>0, beta^2+W^2=q,
    tau=beta-L in (0,1), delta_B=1-tau,
    eta=L W/beta>0,
    Q=(beta-1)f+eta g, h<eta<W.

These are the actual B2 force and moment consequences. Strict B
ownership makes Q an interior point of B's side, and a strict maximum-f
vertex of C. Consequently every tilted C is uniquely represented by

    X=beta-1, Y=eta,
    e=-S f+C0 g, t=-C0 f-S g,
    S,C0>0, S^2+C0^2=1,
    C=Q+[0,1]e+[0,1]t.                          (1)

Q cannot be a circle point because a physical circle point cannot be
shared by distinct contained units. The corner Q+t cannot be the
circle point either. If beta<1, then Q dot e=-SX+C0Y>0, so
|Q+e+t|^2>|Q+t|^2. If beta>=1, then Q dot t=-C0X-SY<0 and

    |Q+t|^2<|Q|^2+1
              <q-2beta+2<=q,

where |Q|^2=X^2+eta^2<q-2beta+1 uses eta<W. Thus the actual unique
C circle corner is exactly one of

    Q+e, or Q+e+t.                               (2)

The entire second alternative is excluded by
ABC_UNIQUE_SINGLETON_SIDE_OPPOSITE_CORNER_EXCLUSION.md. Hence all
remaining strict B-owned singleton returns use the first alternative.

## 2. Exact actual C2 geometry in the adjacent alternative

Put

    d=Q dot e=YC0-XS, w=-Q dot t=XC0+YS,
    aC=d+1,
    zC=Q+e=aC e-wt,
    aC,w>1/2, aC^2+w^2=q.                      (3)

The strict coordinate bounds follow from physical uniqueness. The
original proper C2 concurrence is fixed by its circle ray and BC
line, whose g coordinate is Y:

    kappa=Y/(Y+C0) in (0,1),
    qC=kappa zC=Q-theta f,
    theta=w/(Y+C0)>0,
    qC-Q=theta S e+theta C0 t.                  (4)

Proper concurrence keeps qC in the actual C. In particular
0<theta C0<=1. We also have the strict comparison

    0<theta S=1-(1-kappa)aC<1.                  (5)

Every force and application mean in (4) is original. A subsequently
identified HC side mean is not treated as a fixed physical point for
generic selection.

The true C equations, with nu,mu_C,lambda_C>0, read

    lambda_C zC=-nu f+mu_C m,
    mu_C det(R,m)=-nu eta<0,                    (6)

where m is the actual H-to-C normal. Equation (6) gives m_g>0 because
zC dot g=Y+C0>0.

## 3. The complete actual HC support fan

The inward C side normals t and -e have negative g component, so they
are excluded. The side normal e is excluded by the t component of
(6): it would require -lambda_C w=nu C0>0. The circle vertex Q+e
is unshareable. A coincident HC application at Q is impossible because
(4) has theta>0: the BC and HC lines would meet at Q, whereas their
actual radial concurrence is qC!=Q. Equivalently, the original C2
torque would require Q collinear with zC, but det(Q,zC)=w>0.

The complete remaining actual HC feature list is therefore:

* the side m=-t=C0 f+Sg, with its original mean
  R_S=Q+theta S e+t;
* the strict endpoint R_0=Q+t;
* the strict endpoint R_1=Q+e+t.

The side formula follows because its t coordinate is 1 and its e
coordinate must agree with the actual concurrence (4). Every genuine
shared-HC mean and either endpoint of its actual overlap interval
remain included. No fixed-tip normal selection is used for this row.

At R_0 the actual inward ray is

    qC-R_0=(C0-theta)f+Sg.                      (7)

Its origin moment is exactly

    det(R_0,qC-R_0)=kappa(w-aC).

Thus the original positive C equation additionally forces

    aC>w.                                       (8)

This essential positive-force condition is stronger than concurrence
alone and remains in the unresolved domain below.

At R_1 the actual inward ray is

    qC-R_1=(S+C0-theta)f+(S-C0)g.                (9)

Its g component must be positive, so S>C0. By (5),
theta<1/S<S+C0, since S>C0. Therefore both f and g components in (9)
are strictly positive.

For either strict endpoint, BC and HC are distinct singleton physical
applications of the true unique C2. GENERAL_FIXED_TIP_NORMAL_SELECTION.md
therefore excludes an original free HC normal in the selected
certificate. A strict C-vertex application cannot be C-owned, so HC is
H-owned. TRIANGLE_C4_THREE_LOAD_PARALLEL_EXCLUSION.md excludes the two
H axes parallel to n at the actual H4/intact-petal scope. The negative
endpoint norm bound makes H physically circle-clear, as required by
that source. Since m_g>0 and j_g=E>0, the actual endpoint normal is

    m=j                                             (10)

at either remaining strict endpoint. No new normal is chosen after
the force certificate is obtained.

## 4. Complete prefix bounds when beta<=3/2

Sections 2--3 of ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md prove,
without any C owner or circle-mask premise,

    r>u, delta_B>c, D>0                         (11)

throughout the entire beta<=3/2 prefix. The D sign uses the actual
physical nonoverlap of H and B, with all four separating axes kept.

The original prefix calculations in Section 5 of that source also
use no C equation: W>1, h>0, b>h, x=a-1>h and b<beta give
beta>4/5 and L>4/5. Since W>sqrt(q0-9/4)>5/4, we obtain

    4/5<beta<=3/2, eta=L W/beta>1/beta.          (12)

These statements include beta=3/2 for the present tilted C. That
value is not called radial for a tilted singleton C.

## 5. The whole HC side and upper endpoint are excluded at beta<=3/2

First, the upper endpoint R_1 is impossible. Its actual normal has
strictly positive f component by (9), whereas (10)--(11) give
j_f=-D<0.

For the entire side m=-t, put

    F=X S^2+eta(1-SC0)+C0-S.

The exact scalar identity is

    C0+theta S^2-S=C0 F/(eta+C0).                (13)

We prove F>0 over the entire enlarged domain (12) and all S,C0>0 on
the unit quadrant.

If S<C0, then S^2<1/2, X>-1/5, eta>2/3 and
1-SC0>=1/2. Thus F> -1/10+1/3>0.

Suppose S>=C0. If beta>=1, then X>=0 and
eta>1/beta>=2-beta=1-X. Hence

    F>(1-S)(1+C0)+X C0(S-C0)>0.                 (14)

If beta<1, write k=1-beta in (0,1/5). Multiplying the lower bound
eta>1/beta by beta gives

    beta F>A-kB+k^2 S^2,
    A=(1-S)(1+C0)>0,
    B=C0-S(1-S).

Here 0<B<C0. Moreover S^2>=1/2, so

    B^2<C0^2=(1-S)(1+S)
       <2(1-S)<=4S^2(1-S)(1+C0)=4S^2 A.

The displayed quadratic in k has negative discriminant and positive
leading coefficient. It is strictly positive for every k, proving
F>0 also in this whole remaining case. Equation (13) therefore yields

    C0+theta S^2>S.                             (15)

Now retain the actual application R_S. Since D>0, its normal
m=C0 f+Sg has m dot n=C0 E+SD>0. Thus R_S belongs to H's front n
side and can be written R_S=P+t_H j with
t_H in [r-1,r], in particular t_H<1. Its exact f displacement is

    (R_S-P) dot f=c-delta_B-C0-theta S^2<0.

Hence t_H>0 and

    t_H D=delta_B-c+C0+theta S^2.                (16)

If m dot j<0, the actual H support would have t_H=r-1<0, already
contradicting t_H>0. Otherwise

    m dot j=SE-C0D>=0  => S>=D.

Equations (11), (15)--(16) give t_H D>D, contrary to t_H<1. This
also includes m dot j=0 and the entire shared-HC mean interval; no
parallel-normal exclusion or generic selection is needed for this
side argument.

Thus at beta<=3/2 both the whole side row and the whole R_1 endpoint
are excluded. The only remaining feature there is the strict R_0/j
endpoint with the true positive-force condition (8).

## 6. Precisely retained unresolved domain

The following is the complete necessary domain for the remaining
strict endpoint R_0, without dropping any actual equation:

    aC>w>1/2,
    E(C0-theta)+DS=0,
    R_0=P+alpha n+rj, -1<=alpha<=0, 0<r<1,
    alpha=E(c-delta_B-C0)+D(s+eta-h-S),
    r=D(delta_B-c+C0)+E(s+eta-h-S).

All original A/B/C radius identities, negative A pressure, true C2
force magnitudes, actual H/B nonoverlap, containing-disk constraints,
intact petal and three completion squares remain required. For
beta<=3/2 it additionally has the proved (11)--(12). This source has
not proved those endpoint equations impossible.

The complete later source
ABC_UNIQUE_SINGLETON_SIDE_FRONT_RETURN_REDUCTION.md excludes R_1
for every beta and forces every surviving C-side mean onto H's
front n face. ABC_UNIQUE_SINGLETON_ADJACENT_SIDE_EXCLUSION.md then
excludes the whole side when beta>3/2; Section 5 above covers the
full beta<=3/2 interval. Their full saved-source and original-scope
reviews are REVIEW_ABC_ADJACENT_FRONT_RETURN_2026_10_25.md and
REVIEW_ABC_COMPLETE_ADJACENT_SIDE_2026_10_25.md.

Only the original R_0/j endpoint remains throughout the full beta
domain, with aC>w and all equations above. No unproved extension
of (11) or (12) is asserted at beta>3/2.

The complete genuine shared BC owner feature and the opposite-C-corner
strict singleton feature are excluded by their accepted whole sources.
The adjacent-C-corner strict singleton feature is not yet closed by
this reduction. No original UUU or coarse parent gate is claimed
closed. No numerical sample, coefficient diagnostic, Lean compilation
or CI is a premise.
