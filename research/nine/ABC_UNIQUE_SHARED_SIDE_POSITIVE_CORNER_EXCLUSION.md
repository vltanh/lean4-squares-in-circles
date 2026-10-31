# The positive-f unique corner cannot follow the shared B-side return

Date: October 25, 2026.

**Status: complete corrected hand proof; independent root full-source
and scope review passed on October 25, 2026. See
REVIEW_ABC_UNIQUE_REFINEMENTS_2026_10_25.md.**
The initial ray-sign error has been corrected and the invalid concavity
argument replaced by the direct uniform inequality in Section 3.
This source treats one complete physical corner alternative of
the original shared BC side. It does not close the whole unique-C side
return, a new gate, or the UUU mask.

Retain the original negative H-owned HA / B-owned upper-left AB chart,
true H4/A2/B2/C2, the intact HXY petal, all nine physical squares and all
three completion squares. The actual A contacts are P and T with
T=P+e_y and |e_y|=1. The unchanged B axes are
f=(s,c), g=(-c,s), with c,s>0 and det(f,g)=1. In those axes,

    B=[beta-1,beta]f+[W-1,W]g,
    zB=beta f+Wg, beta^2+W^2=q,
    T=L f+(W-1)g,
    0<tau:=beta-L<1,
    Q=(beta-1)f+eta g, eta=L W/beta.

For the actual side normal k_BC=-f, the true B2 force equation is
lambda_B zB=gamma g+nu f with all three magnitudes positive. Thus
beta=nu/lambda_B>0 and W=gamma/lambda_B>0; physical uniqueness gives
W>1/2. The original moment equation is gamma L=nu eta, which fixes
eta=L W/beta>0. Thus Q is the unchanged actual shared mean, also
obtained from true B2 concurrence, rather than a chosen side point.
The full original radius interval is q in [6241/1600,1105/256]. Assume
BC is genuinely shared with a physically unique C, and beta>3/2.

**Theorem.** This entire alternative is impossible, including every
original shared mean and every HC owner, free normal or shared mean.
No selection theorem is applied to a varying shared BC mean.

## 1. The complete C geometry and its actual HC ray

Because the common BC axis is f, the actual C has f interval
[beta-2,beta-1]. Proper true C2 concurrence has g coordinate eta>0,
so the actual unique circle corner has positive g coordinate. Its far
f coordinate is U=beta-1>1/2. Thus

    C=[U-1,U]f+[V-1,V]g,
    zC=U f+Vg, V=sqrt(q-U^2),
    Delta=V-W>0.

Positive shared overlap gives Delta<1. The original mean satisfies
V-1<=eta<=W. In particular

    0<tau<=tau_max:=beta(1-Delta)/W.

The genuine C force equation is

    lambda_C zC=-nu f+mu_C m,

where m is the actual H-to-C normal and all three magnitudes are
positive. Since U,V>0, both f and g components of m are strictly
positive. Hence HC is the singleton at the actual lower-left C vertex

    R=(U-1)f+(V-1)g.

Proper C concurrence gives qC=kappa zC with kappa=eta/V in (0,1).
The original m is a positive multiple of

    m0=qC-R=A(tau)f+B(tau)g,
    A(tau)=1-U Delta/V-(UW/(beta V))tau,
    B(tau)=1-Delta-(W/beta)tau.

The actual B(tau)>0. Retaining its zero comparison endpoint at
tau_max only enlarges the estimate. Both A and B are affine in tau.

## 2. Uniform scalar geometry on the complete interval

First Delta>1/2. Indeed W<=sqrt(q-9/4)<=23/16, and

    V^2-(W+1/2)^2=2beta-W-5/4>5/16>0.

Also Delta<1 implies U=beta-1<W. If beta>=2, this would give
q=beta^2+W^2>5, contrary to the original upper radius. Thus U<1,
and

    V^2=W^2+2U+1>(U+1)^2>4U^2,
    V>2U.

The complete offset bound is tau_max<1/2. Put r0=W/beta>0. Squaring
the two positive expressions gives

    V^2-[1+W-W/(2beta)]^2
      =beta[(r0-1)^2+1]-2+r0-r0^2/4
      >=1-2r0+(5/4)r0^2
      =(5/4)(r0-4/5)^2+1/5>0.

Consequently Delta>1-W/(2beta), which is exactly tau_max<1/2.
These comparisons retain the whole original q and beta intervals.

## 3. One uniform comparison excludes every actual HC owner

Define on the single full interval [0,tau_max]

    F(tau)=(2-tau)A(tau)-Delta B(tau)
             -sqrt(A(tau)^2+B(tau)^2).

Put alpha=U/V in (0,1/2) and T0=beta/W>1; the last sign uses
W<=23/16<3/2<beta. For every point of the full comparison interval,

    0<=B<=1-Delta<1/2,
    A=1-alpha+alpha B>(1+B)/2>0.

Consequently r=B/A satisfies 0<=r<2/3 and

    B>=r/(2-r).

The weak inequality includes B=r=0. The original offset relation gives

    tau=tau_max-T0 B<1/2-B<=1/2-r/(2-r).

Using Delta<1 now yields the uniform bound

    2-tau-Delta r
      >3/2+r/(2-r)-r
      =3/2-r(1-r)/(2-r)>5/4.

For the last strict inequality, the complete exact identity is

    1/4-r(1-r)/(2-r)
      =[4(r-5/8)^2+7/16]/[4(2-r)]>0.

On the other hand sqrt(1+r^2)<sqrt(13)/3<5/4; the final squared reserve is
25/16-13/9=17/144>0. Therefore

    F(tau)/A=2-tau-Delta r-sqrt(1+r^2)>0

on the entire closed interval, including both comparison endpoints.

Now R-T=(tau-2)f+Delta g and P=T-e_y with |e_y|=1. It follows that

    (R-P) dot m0
      =(tau-2)A+Delta B+e_y dot m0
      <=-(2-tau)A+Delta B+sqrt(A^2+B^2)
      =-F(tau)<0.

But m is a positive multiple of m0 and is the actual H-to-C separating
normal at R. Every point of H, in particular its unchanged HA point P,
must satisfy P dot m<=R dot m. This contradicts the strict inequality.

No H support side or HC owner was selected in this argument. It therefore
includes a free HC singleton. No fixed-tip claim at the shared BC mean,
negative C-pressure assumption, fictitious H/B contact, force deletion,
or replacement of an original square or application is used.

The shared unique-C alternative beta<3/2 is now separately excluded by
ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md. The strict B-owned singleton
BC with tilted unique C and the unique-C far return retain their remaining
original domains. The tie beta=3/2 is physical radial C and was already
excluded by its complete shared-side theorem. No numerical sample, Lean
compilation or CI is a premise of this proof.
