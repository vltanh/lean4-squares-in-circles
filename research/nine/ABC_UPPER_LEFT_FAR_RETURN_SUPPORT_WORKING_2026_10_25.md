# Original upper-left far-return domain and complete accepted exclusion

**Status: the entire original far feature is CLOSED.** Both physical C
masks, both B circle corners, every HC owner and mean, k_y=0 and the
whole k_j=0 shared-H interval are covered in
REVIEW_ABC_COMPLETE_FAR_RETURN_2026_10_25.md. The exact original
equations below remain recorded; Section 4 gives the complete join.
This does not close the distinct adjacent-circle strict singleton
R0/j residue or any whole ABC gate.

Keep the original H--A--B--C--H cycle, intact H--X--Y--H petal, selected
certificate, genuine H4/A2/B2/C2 equations, both physical C masks and all
original weights. Work at q in [6241/1600,1105/256]. This note concerns
only the strict far BC vertex with k_y<0. The distinct strict B-owned
minimum-f BC singleton retains its adjacent-circle R0/j endpoint.

## 1. Exact prefix domain

Use the original negative endpoint chart from
NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md, Section 1, and
NEGATIVE_H_OWNED_UPPER_LEFT_NEAR_VERTEX_EXCLUSION.md:

    a>b>3/5, a^2+b^2=q, x=a-1, P=(x,b-1), T=(x,b),
    c,s>0, c^2+s^2=1, f=(s,c), g=(-c,s),
    rho=c/(c+s*(a/b-1)), v=1/sqrt(1+rho^2), u=rho*v,
    n=(u,v), j=(-v,u), 0<rho<1,
    H=P+[-1,0]n+[r-1,r]j, 0<r<1.

Here the displayed rho is the true A2 concurrence identity, not a new
choice of normal. Write p_H=P.n and t_H=P.j. The actual negative pressure is

    (P-n/2+(r-1/2)j).(a,b)<0.

In particular the original endpoint comparison at r=1 gives the necessary
strict inequality

    N=q-a-b-((a-b)*u+(a+b)*v)/2<0.                 (1)

All actual original poses satisfy (1); replacing actual negativity by
(1) is only an enlargement of the parameter domain. Also t_H<0:
t_H=-(a-1)v+(b-1)u, and a>b with 0<u<=v.

The complete original B circle/concurrence data are

    L=x*s+b*c, h=-x*c+b*s,
    epsilon=1 if h>-1/2, and epsilon=0 if h<-1/2,
    H_B=h+epsilon, beta=sqrt(q-H_B^2),
    tau=beta-L, delta=1-tau, 0<tau<1,
    ell=L*H_B/beta-h, 0<=ell<1.

The excluded equality h=-1/2 is the physical two-corner B mask; B is
physically unique in the present remaining family. The strict far vertex,
normal, incoming C coordinates, and moment are

    W=T+g-delta*f,
    D=sqrt(delta^2+(1-ell)^2),
    k=(-delta*f+(1-ell)*g)/D, Jk=(-k_y,k_x),
    k_x<0, k_y<0, w=W.k, M=det(W,k)>0.

BC is C-owned by the previously compatible fixed-tip selection at true
unique B2. Its point W is in the relative interior of C's minimum-k side.
Put k_n=k.n and k_j=k.j. Then

    k_n<0.                                        (2)

No sign of k_j or w is available. In particular the negative far-k
alternative and the physical radial-C boundary must not be discarded.

## 2. Physically unique C: complete remaining HC feature cover

The original C chart is

    C=[w,w+1]k+[-V,1-V]Jk,
    U=w if w<-1/2, and U=w+1 if w>-1/2,
    U^2+V^2=q, |U|>1/2, V>1/2,
    delta_C=V-M in (0,1), kappa=M/V in (0,1),
    z_C=U*k-V*Jk, q_C=kappa*z_C.

The true C2 equation makes the C-to-H normal have positive Jk component.
Thus HC uses C's maximum-Jk side or one of its endpoints. The original
incoming BC moment is M>0, so every actual outgoing HC moment is positive.

### 2.1. The C-owned/shared maximum-Jk side

Its actual original mean, fixed by true C concurrence, is

    Q0=kappa*U*k+(1-V)*Jk.

Its moment is kappa*U, hence this whole row requires U>0. The H-to-C
normal is -Jk; its j component is -k_n>0. Therefore its actual H support
has j coordinate t_H+r, including either H vertex, any genuinely shared
H side, and every original mean endpoint. In particular

    r=J0:=kappa*U*k_j+(1-V)*k_n-t_H<1.             (3)

If k_j>0 the actual H vertex is P+r*j; if k_j<0 it is P-n+r*j.
At k_j=0 the full original top-j H side remains. No mean is replaced.

### 2.2. The strict left endpoint

Put QL=w*k+(1-V)*Jk. Its proper outgoing ray is

    QL-q_C=(w-kappa*U)k+(1-delta_C)Jk.

The exact moment before multiplying by its positive ray-normal factor is

    det(QL,QL-q_C)=kappa*(w*V+U*(1-V)).

For U=w<0 this is kappa*U<0, so that complete alternative is impossible.
For U=w+1 it is kappa*(U-V), so the remaining strict left endpoint requires

    U>V>0.                                        (4)

The actual C is unique and its two singleton applications W,QL are
distinct. The common fixed-tip selection excludes a free HC. Its strict
C-vertex normal is not a C axis, so H owns HC. The actual H4/petal
parallel-root theorem excludes both H normals parallel to n.
By (2), positive Jk component leaves exactly H-to-C normal +j.
The strict left normal then requires k_j>0. Its genuine alignment is

    (w-kappa*U)*k_n-(1-delta_C)*k_j=0.             (5)

Actual H contact requires

    r=JL:=w*k_j+(1-V)*k_n-t_H<1,
    -1 <= (QL-P).n <= 0.                          (6)

The endpoints of H's side coordinate are left in this necessary domain.

### 2.3. The strict right endpoint

Put QR=(w+1)k+(1-V)Jk. Its proper outgoing ray is

    QR-q_C=(w+1-kappa*U)k+(1-delta_C)Jk.

The moment is kappa*U when U=w+1, and kappa*(U+V) when U=w.
Thus U=w<0 retains its necessary condition U+V>0. The same fixed-tip
and actual parallel-root inputs give H-to-C normal +j, now with k_j<0.
The genuine alignment and physical H support are

    (w+1-kappa*U)*k_n-(1-delta_C)*k_j=0,            (7)
    r=JR:=(w+1)*k_j+(1-V)*k_n-t_H<1,
    -1 <= (QR-P).n <= 0.                          (8)

These three rows are the original complete unique-C cover. The entire
left row (4)--(6) is now excluded by the separate full positive-C
coordinate comparison; the other current boundaries are in Section 4.

## 3. Physically radial C: all original circle-weight endpoints

The radial axis parallel to k is excluded by the original outer/inner
radial-face boundary-neighbor obstructions. Therefore put

    K=sqrt(q-1/4), d=K-1,
    C=[-1/2,1/2]k+[-K,-d]Jk,
    w=-1/2, d<M<K,
    F_C=lambda*(eta*k-K*Jk), lambda>0, -1/2<=eta<=1/2,
    kappa=M/K, q_C=kappa*(eta*k-K*Jk).

Again the true equation makes the outgoing normal have positive Jk
component. At the left inner vertex the unchanged proper-ray moment is

    -kappa*(K/2+d*eta)<0,

because K/2+d*eta >= (K-d)/2=1/2. This excludes that whole feature,
including eta=+/-1/2.

On the inner radial side the actual outgoing normal is Jk and its mean
is Q=xi*k-d*Jk, with xi=kappa*eta. Positive moment forces xi>0, and
the original eta interval gives xi<=kappa/2<1/2. At the right inner
vertex, Q=k/2-d*Jk. That vertex may have a free HC normal: a unique-C
fixed-tip theorem has NOT been imported at radial C.

Both remaining physical features therefore satisfy the uniform bound

    (Q-P).j >= Jrad:=-d*k_n+min(0,k_j)/2-t_H.     (9)

Every actual Q in H satisfies (Q-P).j<=r<1. Hence Jrad>=1 would exclude
the whole radial-C far-return family, with every original weight endpoint
and without any HC normal selection.

## 4. Complete original feature join and remaining ABC obligation

The original equations above retain every actual mean and selected
normal. The entire far feature is excluded by the following complete
sources and the separate full assembly review.

| Original far domain | Complete source |
| --- | --- |
| k_y>=0, both B corners, both C masks and all HC features | NEGATIVE_H_OWNED_UPPER_LEFT_NONNEGATIVE_VERTICAL_RETURN_EXCLUSION.md |
| k_y<0, physical radial C, both B corners and all weight endpoints | ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md |
| k_y<0, unique C, epsilon_B=0, all HC features | ABC_FAR_UNIQUE_LOWER_B_CORNER_EXCLUSION.md |
| epsilon_B=1, C-owned HC side with k_j>0 | ABC_FAR_UNIQUE_SAME_SIDE_RADIUS_OBSTRUCTION.md |
| epsilon_B=1, strict-left HC endpoint | ABC_FAR_UNIQUE_POSITIVE_C_COORDINATE_COMPARISON.md, with negative-U moment exclusion |
| epsilon_B=1, k_j<=0 C-side/shared HC or either strict-right endpoint | ABC_FAR_UNIQUE_NONPOSITIVE_TANGENT_RETURN_EXCLUSION.md |

The last source proves b>9/10, 1/4<N<1/2 and a strict 13/16 norm
bound for every point of the actual H top-j face. The unchanged
C-side mean and positive-U right endpoint violate that bound.
The negative-U right endpoint violates the true positive-moment
proper-ray ratio. The entire k_j=0 mean interval is included.

REVIEW_ABC_COMPLETE_FAR_RETURN_2026_10_25.md records the independent
full saved-source, exact five-coefficient/inverse, analytic and
original mask/owner/mean/radius assembly. It includes k_y=0 and
physical radial transitions. No new gate or count change follows.

The distinct strict B-owned minimum-f BC singleton retains only its
adjacent-circle R0/j endpoint with aC>w. The whole adjacent HC side
and R1 endpoint now have complete independently reviewed exclusions;
see ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md, Section 6.
The genuinely shared BC feature and opposite-circle C singleton
are also closed. The full ABC gate, C4_EXIT, coarse C2.34.b0,
unrestricted radius theorem and original equality remain OPEN.

No Lean compilation or CI was run. No new ID is introduced.
