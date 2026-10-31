# Full-angle positive pressure for the original ABC R0 return

Date: October 25, 2026.

**Status: independently reviewed full-angle pressure theorem with a
complete table-free scalar proof.** The small-ratio proof is Section2 of
`ABC_R0_WEIGHTED_CAUCHY_REDUCTION.md`; the entire large-ratio proof is
`ABC_R0_ANGULAR_ENDPOINT_REDUCTION.md` with
`ABC_R0_POSITIVE_ENDPOINT_ANALYTIC.md`. Their full independent review is
`REVIEW_ABC_R0_TABLE_FREE_2026_10_25.md`. Both the original1,559-sign
packet and its270-sign successor are superseded. The original strict
pressure reserve and physical scope are unchanged. Historical certificate
arguments below are retained solely for provenance.
The complete physical and ABC/C4 assembly review is
`REVIEW_ABC_R0_AND_COMPLETE_ASSEMBLY_2026_10_25.md`. This remains a
hand argument with exact arithmetic, not Lean checked. The older full
prerequisite-chain audit remains open. No new gate is introduced.

This source supplies a whole-domain exit for the last R0/j endpoint in
ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md. In particular it does NOT
assume the previously proposed restriction |D|<=1/2. The actual middle
square's torque supplies the term that makes that restriction unnecessary.

## 1. Original physical scope and theorem

Retain the actual H--A--B--C--H block. A,B,C each have true positive pair
degree two and a positive load at their unique physical circle corner.
They lie on the same circle of radius R>=79/40. H is a unit square and
may retain arbitrary additional forces and neighbors. We use exactly the
strict R0 chart of the accepted adjacent-return fan; no normal, magnitude,
application or square is changed.

In B's positively oriented orthonormal frame (f,g), write

    n=E f+D g,  j=-D f+E g,  E>0, E^2+D^2=1.

The original H-to-A and H-to-C normals are n and j. Their original positive
magnitudes are mu and eta. The A-to-B normal is g with magnitude gamma;
the B-to-C normal is -f with magnitude nu. All four magnitudes are positive.
Thus the original equations, with lambda_A,lambda_B,lambda_C>0, are

    lambda_A z_A = mu n-gamma g,
    lambda_B z_B = gamma g+nu f,
    lambda_C z_C = eta j-nu f.                         (1)

The lambdas absorb any common factor two in the circle-load convention.
Let c_H be the original center of H and put

    F_block=lambda_A z_A+lambda_B z_B+lambda_C z_C
           =mu n+eta j,
    Bmag=|gamma g+nu f|=sqrt(gamma^2+nu^2)>0.

**Theorem.** In the entire original strict R0 chart,

    c_H dot F_block > Bmag/640 > 0.                    (2)

This theorem uses no balance equation at H and no completion-capacity
premise. It retains H's true external degree. It holds throughout the
original closed radius window, and in fact needs only R>=79/40.

For the original H4 block with its intact HXY petal, the accepted
end-triangle theorem in BOWTIE_CELL_CLOSED.md, Section 2, gives
c_H dot M_petal>0. The original H4 equation is
F_block+M_petal=0, contradicting (2). Thus the ENTIRE original R0 return
is excluded, with all three completion squares still present.

## 2. The endpoint torques give the complete angle interval

Use the unchanged A axes

    p=s f-c g,  t_A=c f+s g,  s,c>0, s^2+c^2=1,
    T=z_A-p,   P=z_A-p-t_A.

P is the actual HA application and T the actual AB application. In A's
frame n has coordinates

    u=E s-D c,  v=E c+D s.

The actual A torque about its circle corner gives

    mu(u-v)+gamma s=0,
    [mu(E-D)+gamma]s=mu(E+D)c.                       (3)

For the unchanged C chart write

    e=-S f+C0 g,  t=-C0 f-S g,
    S,C0>0, S^2+C0^2=1,
    z_C=Q+e,  R0=Q+t=z_C-e+t.

Q and R0 are the original BC and HC applications. The actual C torque
about z_C gives

    eta(E-D)S=[eta(E+D)+nu]C0.                       (4)

Equation (3) first forces E+D>0: otherwise E-D>0, so its left side is
positive while its right side is nonpositive. Equation (4) then forces
E-D>0. Hence the complete physical interval is

    -1/sqrt(2)<D<1/sqrt(2).                         (5)

No part of (5) is omitted. In particular both |D|>1/2 tails remain.
Define

    A=sqrt(mu^2+gamma^2-2mu gamma D),
    B=sqrt(gamma^2+nu^2),
    C=sqrt(eta^2+nu^2+2eta nu D),
    U=sqrt(2mu^2+gamma^2+2mu gamma(E-D)),
    V=sqrt(2eta^2+nu^2+2eta nu(E+D)).                 (6)

All five quantities are positive. Equations (3),(4), and the positive
unit coordinates give exactly

    s=mu(E+D)/U,       c=[mu(E-D)+gamma]/U,
    C0=eta(E-D)/V,     S=[eta(E+D)+nu]/V.             (7)

They imply the endpoint support identities

    mu(u+v)+gamma c=U,
    eta[E(C0+S)+D(S-C0)]+nu S=V.                    (8)

These are identities for the original forces, not maximizing replacements.

## 3. Exact block pressure and the indispensable B2 torque

Set

    Tsum=A+B+C,
    Ssum=(mu+eta)/2+gamma+nu+U+V.

Then

    pressure := c_H dot F_block = R*Tsum-Ssum.       (9)

Here is a direct derivation. Multiply each equation (1) by its actual
circle corner and sum; each corner has norm R. Subtract c_H dot F_block.
The HA and HC support conditions give

    (P-c_H) dot n=1/2,  (R0-c_H) dot j=1/2.

B owns the adjacent contact sides, so

    g dot(z_B-T)=1,  f dot(z_B-Q)=1.

Consequently the support-work sum is

    mu[u+v+1/2]+gamma[1+c]
       +nu[1+S]+eta[E(C0+S)+D(S-C0)+1/2],

which equals Ssum by (8). Also lambda_A R=A, lambda_B R=B,
lambda_C R=C. This proves (9) without a derivative or deformation argument.

Now write B's unchanged circle corner as z_B=beta f+W g and its two
original contact coordinates as

    T=L f+(W-1)g,  Q=(beta-1)f+Y g.

Equation (1) and the physical contact relations give

    L=R mu E/A-s,
    Y=R eta E/C-C0.

The true B2 origin torque is gamma L=nu Y, hence

    R E(mu gamma/A-eta nu/C)=gamma s-nu C0.          (10)

For bookkeeping only, differentiate the functions in (6) with respect
to the scalar D, holding the four original magnitudes fixed and setting
E=sqrt(1-D^2). A prime below means this formal derivative. It does NOT
assert that D can be varied through physical packings. Direct calculation
using (7),(10) gives

    Tsum'=-mu gamma/A+eta nu/C,
    Ssum'=(-gamma s+nu C0)/E,
    R*Tsum'=Ssum'.                                 (11)

Thus the actual middle torque supplies the exact corrected identity

    pressure=R*(Tsum-(D/2)Tsum')
                     -(Ssum-(D/2)Ssum').            (12)

All original B forces are essential in (10). No H2 equation, dropped
middle force, or additional HB contact has been used.

## 4. One scalar inequality covers every force ratio and every angle

Put K=79/40. The following lemma has an elementary proof on0<=x<=1
in Section2 of `ABC_R0_WEIGHTED_CAUCHY_REDUCTION.md`, and on every x>=1
in `ABC_R0_ANGULAR_ENDPOINT_REDUCTION.md` and its positive-endpoint
companion. `REVIEW_ABC_R0_TABLE_FREE_2026_10_25.md` accepts the complete
join. Sections6--8 below preserve the superseded certificate as history.
For x>=0 and -1/sqrt(2)<=d<=1/sqrt(2), set

    e=sqrt(1-d^2),
    a=x^2+1-2dx,
    b=2x^2+1+2x(e-d),
    p=a+(d/2)x,
    q_s=b+(d/2)*x*(e+d)/e,
    h(d)=(8+16d)/25.

Then

    K*p/sqrt(a)-q_s/sqrt(b)-x/2 > -h(d).            (13)

The denominators are strictly positive. The closed d interval includes
both endpoints of the actual strict interval (5); x=0 is also an allowed
enlargement. There is no bound on the original positive force ratios.

Apply (13) first with x=mu/gamma and d=D, multiplying by gamma. Apply
it again with x=eta/nu and d=-D, multiplying by nu. The two conclusions,
using precisely the derivatives in (11), add to

    K*(Tsum-(D/2)Tsum')-(Ssum-(D/2)Ssum')
       > K*B-[1+h(D)]gamma-[1+h(-D)]nu.             (14)

Cauchy's inequality and D^2<=1/2 give

    [1+h(D)]^2+[1+h(-D)]^2
      =2(33/25)^2+2(16/25)^2 D^2
      <=2434/625.

Therefore the right side of (14) is at least

    [K-sqrt(2434)/25]*B > B/640,                    (15)

where the final strict comparison is exact:

    K-1/640=1263/640>0,
    (1263/640)^2-2434/625=569/10240000>0.

The corrected total Tsum-(D/2)Tsum' is positive. Its A term has numerator
mu^2+gamma^2-(3/2)D mu gamma over A, and the C term has numerator
eta^2+nu^2+(3/2)D eta nu over C. Both numerators are positive by
x^2+y^2>=2xy and |D|<1; B>0 as well. Since R>=K, equations
(12)--(15) prove the claimed uniform pressure bound (2).

## 5. Extension to larger attachments: exact scope, not a blanket reduction

Suppose the same actual R0 block occurs in a larger positive component,
with A,B,C still having exactly the degree-two equations (1). H may have
any number of further incident forces. If their total outward resultant
M satisfies c_H dot M>=0 and H has zero circle load, its balance equation
F_block+M=0 contradicts (2).

In particular M may be a sum of any number of intact end-triangle
resultants to which the previously selected complete pressure theorem
applies. Every triangle tip must retain its true degree two. The argument
has no six-body restriction and keeps every additional physical square.

This extension is NOT permission to delete an attachment force at A, B
or C, or to infer this R0 contact chart at a different root degree. The
older H4 owner/parallel reductions are used only at their stated scope.
Other owners, multi-force junctions, and all remaining C6 completion
problems retain their separate obligations.

## 6. Historical alternative: scalar reduction to exact polynomial signs

Use the definitions in (13) and put

    t_s=x/2-h(d),
    H=K^2*p^2*b-q_s^2*a-t_s^2*a*b,
    P=H^2-4*q_s^2*t_s^2*a^2*b,
    Z=K^2*p^2*b-q_s^2*a.                           (16)

The scalar a,b,p,q_s are positive on the declared domain. For example
b>=1 since e>=|d|, p=x^2+1-(3/2)dx>0, and

    q_s=2x^2+1+x[2e-(3/2)d+d^2/(2e)]>0.

If H>0 and P>0, then

    H>2q_s |t_s| a sqrt(b),
    K p sqrt(b)>sqrt(a)[q_s+|t_s|sqrt(b)].

Only positive quantities were squared. Dividing gives
K p/sqrt(a)-q_s/sqrt(b)>|t_s|>=t_s, proving (13).
Alternatively, if Z>0 and t_s<0, then
K p/sqrt(a)>q_s/sqrt(b)>q_s/sqrt(b)+t_s, also proving (13).

Rationalize the whole angle interval by

    z=d/(1+e), den=1+z^2, en=1-z^2, dn=2z,
    d=dn/den, e=en/den.

The actual |z|<=sqrt(2)-1 is contained in [-5/12,5/12]; the exact
reserve (17/12)^2-2=1/144>0 proves this enlargement. On the larger
interval en>0 and den>0. Define the explicit rational polynomials

    aa=den*(x^2+1)-2dn*x,
    bb=den*(2x^2+1)+2x*(en-dn),
    pp=den*(x^2+1)-(3/2)dn*x,
    qq=en*bb+(dn*x*(en+dn))/2,
    tt=(x*den)/2-(8den+16dn)/25,
    Hnum=K^2*pp^2*bb*den*en^2
                -qq^2*aa*den-tt^2*aa*bb*en^2,
    Pnum=Hnum^2-4qq^2*tt^2*aa^2*bb*den*en^2,
    Znum=K^2*pp^2*bb*en^2-qq^2*aa.                 (17)

The complete normalization identities are

    a=aa/den, b=bb/den, p=pp/den,
    q_s=qq/(den*en), t_s=tt/den,
    Hnum=den^4*en^2*H,
    Pnum=den^8*en^4*P,
    Znum=den^3*en^2*Z.                             (18)

Every factor in (18) is positive on the actual domain. The identities
were independently checked by direct symbolic rational simplification;
they are not inferred from values at selected parameter points.

## 7. Complete finite coefficient certificate

The degrees of Hnum,Pnum,Znum in (x,z) are (6,12),(12,24),(6,10).
For x>=1 put u=1-1/x and define the exact polynomials

    Hlarge(u,z)=(1-u)^6 Hnum(1/(1-u),z),
    Plarge(u,z)=(1-u)^12 Pnum(1/(1-u),z).            (19)

For every finite x>=1 the normalizing factors are positive. Including
u=1 in the polynomial comparison is harmless. The checker reconstructs
both entire inverse substitutions, not merely their endpoint values.

For each rectangle below, make the affine change to the unit square and
write its polynomial as sum c_ij v^i w^j, with degrees (n,m). Define

    b_ij=sum_(k<=i,l<=j) c_kl
                 binom(i,k)/binom(n,k) * binom(j,l)/binom(m,l).

The following strict bounds hold for EVERY coefficient in the specified
row, not just its minimum sampled at some poses:

| Polynomial | First interval | z interval | Degrees | Count | Every coefficient exceeds |
| --- | --- | --- | --- | ---: | ---: |
| Hnum | 0<=x<=1 | -5/12<=z<=1/4 | (6,12) | 91 | 2 |
| Pnum | 0<=x<=1 | -5/12<=z<=1/4 | (12,24) | 325 | 2 |
| Znum | 0<=x<=1 | 1/4<=z<=5/12 | (6,10) | 77 | 1 |
| Hlarge | 0<=u<=1 | -5/12<=z<=5/12 | (6,12) | 91 | 7/10 |
| Plarge | 0<=u<=1/2 | -5/12<=z<=5/12 | (12,24) | 325 | 1/2 |
| Plarge | 1/2<=u<=3/4 | -5/12<=z<=5/12 | (12,24) | 325 | 9/100 |
| Plarge | 3/4<=u<=1 | -5/12<=z<=5/12 | (12,24) | 325 | 9/100 |

There are exactly 1,559 coefficients. All defining polynomials and every
coefficient are reconstructed from (17) using Python Fraction arithmetic
in ABC_R0_TORQUE_CORRECTION_CHECK.py. No stored sign table is trusted as an
input. Its optional --json PATH writes every exact ordinary coefficient
and Bernstein coefficient for inspection.

The full inverse identity, checked coefficient by coefficient, is

    polynomial(v,w)=sum b_ij binom(n,i)binom(m,j)
                       v^i(1-v)^(n-i) w^j(1-w)^(m-j).

In particular each ordinary c_kl is recovered by the exact sum

    sum_(i<=k,j<=l) b_ij binom(n,i)binom(n-i,k-i)
                       binom(m,j)binom(m-j,l-j)(-1)^(k+l-i-j).

The nonnegative Bernstein basis sums to one on the entire closed unit
square. The displayed exact coefficient bounds thus prove strict
positivity on every listed whole rectangle. This is a finite
exact-arithmetic certificate, not an angle mesh or numerical sign test.

## 8. Exhaustiveness of the scalar domain and validation limits

For 0<=x<=1 and z<=1/4, the first two rows give H,P>0. For x>=1,
the last four rows cover every u in [0,1), again giving H,P>0.
The first implication of Section 6 proves (13) in both cases.

The only remaining scalar domain is 0<=x<=1 and z>=1/4. Here

    d=2z/(1+z^2)>=8/17,
    h(d)-1/2>=8/25+(16/25)(8/17)-1/2=103/850>0.

Thus t_s<0. The Znum row gives Z>0, so the second implication in
Section 6 proves (13). All interface equalities x=1,z=1/4 and all
angle endpoints are included. Every nonnegative x and every actual d
is covered. There is no unassigned positive-force-ratio tail.

Validation performed in this continuation:

- A complete rational sparse-polynomial implementation generated and
  checked all 1,559 strict signs, all Bernstein inverses, both reciprocal
  inverses, the half-angle identity, and the endpoint/Cauchy reserves.
- A separately written symbolic implementation reconstructed all 85,
  313, and 61 nonzero ordinary coefficients of Hnum,Pnum,Znum and
  compared them with the rational implementation. All matched.
- The three global denominator identities (18) were checked symbolically.
- The geometric derivation retains all original equations and true
  degrees. The derivative notation only repackages the actual B2 torque.

No separate independent reviewer or Lean kernel check is claimed.
A shorter table-free proof of the scalar lemma and the older full
prerequisite-chain audit remain separate tasks. No Lean compilation,
CI or workflow dispatch was run; publication uses [skip ci].

The old conditional |D|<=1/2 candidate is superseded by (12)--(15),
not assumed. The unrestricted nine-square theorem and its equality
classification are NOT proved by this endpoint result.


