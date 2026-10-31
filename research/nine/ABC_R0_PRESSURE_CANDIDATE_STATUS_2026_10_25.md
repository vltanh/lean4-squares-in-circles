# ABC R0 candidate — superseded by the reviewed full-angle theorem

The earlier provisional note below is retained as provenance. `ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md` now proves the entire original R0 domain without the `|D|<=1/2` condition. `REVIEW_ABC_R0_AND_COMPLETE_ASSEMBLY_2026_10_25.md` independently verifies the proof and the complete original ABC/C4/coarse-cell join. The bounded-angle candidate is no longer an open proof obligation. The full-angle scalar remains exact-arithmetic-assisted; a short table-free replacement is still being sought.

## Historical candidate note

# ABC strict R0 — bounded-angle pressure route, unverified working note

Date: 2026-10-25. **Status: PROVISIONAL, NOT AN ACCEPTED THEOREM.** This note commits the last discussed partial direction so a future session can resume without misreporting proof closure. It adds **zero checked gate IDs**.

## Genuine original physical system

Read `ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md` (Sections 2, 3, 6) before any reduction. We are in the actual negative-A H--A--B--C--H/HXY configuration, with H4/A2/B2/C2 degrees and positive forces. All nine unit squares remain, including three arbitrary completion units.

The coordinates are
```
P=(a-1,b-1),  a>b>3/5,  a²+b²=q,
f=(s,c), g=(-c,s),      s,c>0, s²+c²=1,
n=E*f+D*g, j=-D*f+E*g, E>0, E²+D²=1,
Q=(beta-1)*f+eta*g, X=beta-1, Y=eta,
e=-S*f+C0*g, t=-C0*f-S*g, S,C0>0, S²+C0²=1,
zC=Q+e=aC*e-w*t,       aC>w>1/2, aC²+w²=q,
kappa=Y/(Y+C0), theta=w/(Y+C0), qC=Q-theta*f,
R0=Q+t,  m=j,  6241/1600<=q<=1105/256.
```
The original C2 force equation is
```
lambda_C*zC = -nu*f + mu_C*j,   lambda_C,nu,mu_C>0.
```
The original proper-ray alignment and actual contact support are
```
E*(C0-theta)+D*S=0,
R0=P+alpha*n+r*j, -1<=alpha<=0, 0<r<1,
alpha=E*(c-delta_B-C0)+D*(s+eta-h-S),
r=D*(delta_B-c+C0)+E*(s+eta-h-S).
```
The exact C2 torque is `det(R0,qC-R0)=kappa*(w-aC)<0`: retain `aC>w` (do not infer C2 positivity from concurrence alone).

## Exact elementary deductions, independently checkable from the accepted equations

Since `E,S>0`, the alignment gives
```
theta-C0 = D*S/E.
```
Thus `D>0 iff theta>C0`, `D=0 iff theta=C0`, `D<0 iff theta<C0`. The accepted `beta<=3/2` prefix has `D>0`, hence `theta>C0` there; this says nothing yet about `beta>3/2`.

Comparing the f/g components of the unchanged true C2 force equation gives
```
lambda_C/mu_C=E/(Y+C0)>0,
nu/mu_C=E*(S-X)/(Y+C0)-D>0.
```
This is a necessary positive force ratio for the strict R0 contact, not a new selection. Along with the true A2/B2 force/moment equations it is a promising input to the original H4 pressure balance. The root center is `cH=P-n/2+(r-1/2)*j`, so its pair-force pressure depends on the *actual* positive HA and HC magnitudes through `cH·n=P·n-1/2` and `cH·j=P·j+r-1/2`. The intact HXY-petal contribution must remain in H4.

Because `aC>w>1/2` and `aC²+w²=q`, one also has `aC>sqrt(q/2)`. This is only a circle-coordinate restriction; it is not by itself a contact exclusion.

## Unpublished candidate and missing obligations

During the preceding investigation a candidate exact certificate was reported for a proposed block-pressure inequality **conditional on `|D|<=1/2`**. Neither its defining polynomial, complete exact coefficient list, checker, nor independent review was preserved in the published repository. Its mathematical correctness is therefore **unverified here**. A proposed H/B geometric argument covered one separation branch, not every H/B separating axis or the complementary `|D|>1/2` region.

To certify that route, one must (1) reconstruct the proposed pressure expression from the *original* HA/HC magnitudes and genuine A2/B2/C2/H4 equations, without replacing the positive forces; (2) save a complete symbolic identity and exact whole-interval coefficient/inverse proof; (3) review all positivity and nonzero denominator assumptions; (4) prove that the actual full R0 domain either satisfies the condition or exhaustively exclude both `D>1/2` and `D<-1/2` by independent physical arguments; (5) retain all four H/B separation axes, shared/endpoint boundaries, circle corners, q endpoints and three extras; (6) separately audit the complete ABC owner/mask/load join before changing any gate checkbox.

Potential alternative: use the circle equations and actual `aC>w` to exclude R0 geometrically, avoiding a strong blanket C-pressure conjecture. Do not reuse the C-owned-far return pressure lemma at this B-owned BC contact.

## Publication status

The complete diamond orbit, ABC far feature, adjacent HC side and R1 are accepted and published before this note. This **R0 route remains OPEN**. No Lean compilation, CI or workflow dispatch; commits use `[skip ci]`.

