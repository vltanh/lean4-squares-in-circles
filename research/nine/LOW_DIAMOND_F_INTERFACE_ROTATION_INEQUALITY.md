# A uniform rotation comparison for the f-interface diamond

**Status: complete hand scalar implication; author, root and separate independent
review passed. See REVIEW_LOW_F_INTERFACE_2026_10_25.md. This scalar source alone
closes no diamond gate.**

This lemma is an input to the original f-owned/shared HK branch of
NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_HK_CONTACT_FAN.md. It is a scalar
comparison of the unchanged original coordinates. No physical square,
normal, force or application mean is replaced, and no degree-two equation
is assigned to K. The full H5/K3/A2/B2, petal and three completion squares
remain in every intended application.

## 1. Statement on one enlarged domain

Let

    u^2+v^2=1, 0<u<=v, u/v>=8/15,
    0<=p<=u, E=sqrt(1-p^2),
    s=Eu-pv, c=Ev+pu.

Thus E>=v>0, s>=0, c>0 and c^2+s^2=1. Define

    deltaRot=(1-E)(1+p)+ps,
    Z=p(1-c)+E(1-E).

Then

    deltaRot^2+Z^2+(14/5)Z-2deltaRot <= 0.                (1)

Equality occurs only at p=0; the inequality is strict for every p>0.
The root comparison that motivates this lemma has the stronger
u/v>5/9, so its whole domain is included here.

The symbol deltaRot is a displacement used only in this scalar comparison.
It is not the original geometric offset delta of K.

## 2. An exact cubic identity

Put

    w=u/(1+v), z=p/(1+E).

The rational half-angle identities are

    u=2w/(1+w^2), v=(1-w^2)/(1+w^2),
    p=2z/(1+z^2), E=(1-z^2)/(1+z^2).

The entire domain of Section 1 satisfies

    1/4<=w<=sqrt(2)-1<5/12, 0<=z<=w.                    (2)

Indeed u/v=2w/(1-w^2) increases with w in [0,1), and its value at
w=1/4 is 8/15. The upper w bound follows from u<=v. Finally p<=u
and E>=v directly give z<=w. The strict rational comparison in (2)
follows by squaring sqrt(2)<17/12.

Define the single cubic in z

    Q(w,z)=w(5-7w)+(14w-6-6w^2)z
             +(5w-2-5w^2)z^2+(1+w^2)z^3.              (3)

The exact identity is

    deltaRot^2+Z^2+(14/5)Z-2deltaRot
       = -4p Q(w,z)/[5(1+w^2)(1+z^2)].                 (4)

Here is a direct expansion route that fixes the signs and coefficients.
Write a0=1-E. Using p^2+E^2=1 and s^2+c^2=1, the left side of (4)
first becomes

    2a0(1+7E/5)+14p/5
       -2p[(E-a0p)s+(p+Ea0+7/5)c].                    (5)

The inverse frame identities s=Eu-pv and c=Ev+pu give

    (E-a0p)s+(p+Ea0+7/5)c
       =u(1+7p/5)+v(1+2E/5).                          (6)

For p>0, a0/p=z. Substituting (6) in (5), followed by the displayed
half-angle expressions, gives (4). At p=0 both sides of (4) are zero
directly. Equivalently, the numerator expansion used in the last step is

    2Q=(1+w^2){u(5+14z+5z^2)+v(7+3z^2)
                         -7-12z-7z^2+2z^3}.

All denominators are strictly positive. No parameter subdivision or
coefficient certificate is involved.

## 3. A single monotonicity comparison proves Q positive

On 1/4<=w<=5/12,

    B(w):=5w-2-5w^2 <= B(5/12)=-113/144<0,             (7)

because B'(w)=5-10w>0 there. Consequently, for every 0<=z<=w,

    Q_z=14w-6-6w^2+2B(w)z+3(1+w^2)z^2
        <=14w-6-3w^2+3w^4
        <=-1/6+3(5/12)^4
        =-527/6912<0.                                  (8)

Thus Q decreases with z on the complete triangular domain, so

    Q(w,z)>=Q(w,w)
             =w(1-w^2)(5w-1-w^2)>0.                   (9)

For the final strict sign, w>=1/4 and w<1 give positivity of the first
two factors. The third factor increases on this interval and has value
3/16 at w=1/4. Every equality endpoint z=0 and z=w has been included.

Equations (4) and (9) prove (1), strictly for p>0. At p=0 the actual
deltaRot and Z both vanish, giving exactly the stated equality case.

## 4. Exact role in the pending center-projection proof

Suppose a separate argument has established C>=1 and G<=7/5,
with Z>=0 and deltaRot>=0, and writes an enlarged K corner
in the original (n,j) frame as (C-deltaRot,G+Z). Then (1) gives

    (C-deltaRot)^2+(G+Z)^2 <= C^2+G^2.

Indeed the difference equals deltaRot^2+Z^2-2C deltaRot+2GZ and is
at most the left side of (1). This corollary uses the stated bounds on
C,G explicitly; this manuscript does not assert or prove those bounds,
the subsequent comparison with q, or the entire cn>0 theorem.

No numerical maximizer, pose mesh, Lean compilation or CI is a premise.
No roadmap checkbox or accepted gate count is changed by this source.
