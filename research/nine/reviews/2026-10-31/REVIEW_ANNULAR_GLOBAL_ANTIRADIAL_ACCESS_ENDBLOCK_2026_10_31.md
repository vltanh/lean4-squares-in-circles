# Independent review of the full-angle anti-radial boundary-access theorem

October 31, 2026. Reviewer: parallel endblock agent.

Reviewed source:

    ANNULAR_GLOBAL_CENTRAL_UNIT_ANTIRADIAL_ACCESS_THEOREM_2026_10_31.md.

**Result: the new mathematical arguments pass independent hand review at their printed scope.** No original fine or coarse gate is closed by this review. No Lean, CI, mathematical script, numerical angle mesh, or generated certificate was used.

## 1. Exact reviewed domain and conclusion

The source retains all nine actual interior-disjoint unit squares in

    2<R<=sqrt(1105)/16.

The actual origin-containing square H has its own reflected/ordered center coordinates

    0<=y<=x<=1/2,
    q=x^2+y^2, u=x+y, v=x-y,
    k=R-sqrt(2),
    t=401/100-(9/5)R.

The inherited radius-dependent closed-central-disk obstruction implies the stronger own-coordinate fact x>t, not merely |c_H|>t. Indeed x<=t and y<=x would place every own side at distance at least 1/2-t from O, contrary to that obstruction. Also t>13/50 follows from sqrt(1105)/16<25/12.

For any physical neighbor B of H and any actual circle corner z of B, the source proves that

    c_H dot z<=0

requires both

    q>v/2,
    sin(2 atan(y/x))>=4(R-sqrt(2))^2-1.

All physical corners are included regardless of their original individual circle weights.

## 2. Exact support optimization

The piecewise anti-radial support maximum was independently reconstructed.

For northwest directions e=(-a,b), the unconstrained support-maximizing vector is proportional to (1/2-x,1/2+y). It satisfies the anti-radial constraint precisely when q<=v/2. The maximum is then

    A=sqrt((1/2-x)^2+(1/2+y)^2).

Otherwise the maximum occurs on c_H dot e=0 and is

    S=(x+y)/(2sqrt(q)).

The southeast constrained maximum is always S. For southwest directions the unrestricted value is

    B=sqrt((1/2-x)^2+(1/2-y)^2).

In the shallow regime B<=A. In the deep regime, direct expansion gives

    q(B^2-S^2)=q^2-uq+v^2/4.

Since q<=u/2, the right side decreases as a function of q up to the actual q. Comparing with q=v/2 gives the upper bound -vy<=0. Hence B<=S. The quadrant endpoints, x=1/2, y=0, and q=v/2 are covered by the same formulas. The northeast quadrant contributes only already included axis endpoints.

Thus the printed two-regime support formula is correct.

## 3. Physical access inequality

For an actual contact p in H intersect B and any actual circle corner z of B,

    |z-p|<=sqrt(2).

Projecting on e=z/R gives

    h_H(e)>=R-sqrt(2)=k.

This is a statement about the actual physical corner and contact. It neither replaces a contact mean nor assumes a positive circle coefficient.

## 4. Whole-interval scalar proof

The source sets

    w=1-2k^2,
    f(R)=t^2+(t-w)^2-w/2.

The signs w>0 and t>w were independently checked. The derivative

    (t-w)'=-9/5+4k>13/25

uses k>29/50. At R=2, t=41/100 and w<1/3 give t-w>23/300.

The derivatives and initial values were recomputed directly:

    f''(R)=174/25+8t-(144/5)k+48k^2,
    f(2)=1319281/5000-(4664/25)sqrt(2),
    f'(2)=34001/125-(4812/25)sqrt(2).

The lower bounds t>13/50 and k>29/50 yield

    f''(R)>5302/625>8.

The rational enclosure sqrt(2)<577/408 follows from

    577^2-2*408^2=1.

Substituting it into the decreasing affine expressions for f(2) and f'(2) gives the stated strict bounds

    f(2)>1/50,
    f'(2)>-1/4,

with exact reserves 31/255000 and 423/8500, respectively.

Integrating the curvature bound twice with d=R-2>=0 yields

    f(R)>1/50-d/4+4d^2
         =4(d-1/32)^2+103/6400>0.

Every coefficient and displayed reserve in this chain checks.

If q<=v/2 and A>=k, then v<=w. The already established x>t>w gives

    y=x-v>t-w>0,
    q>t^2+(t-w)^2>w/2>=v/2,

a contradiction. Thus the entire shallow regime has A<k. Combining this with the physical access inequality forces the deep regime and S>=k. The final conversion

    4S^2=1+sin(2theta)

gives the asserted angular obstruction. The inverse-sine argument is strictly between zero and one because 1/2<k<1/sqrt(2).

## 5. Whole-load scope and limitations

The resultant corollary is valid only for an actual collection whose every positively circle-loaded unit physically touches H. Outside the allowed anti-radial-access domain, every such unit's positively weighted circle corner has positive c_H projection, so the original nonnegative weighted sum has strictly positive projection.

For a genuine articulation cut, the cut-force identity can identify that same original circle-load sum with the resultant. It does not establish the required physical adjacency for remote loaded vertices. Arbitrary private degrees, chords, individual zero weights and original means remain allowed once that adjacency premise is present.

The theorem retains a deep diagonal exception and the possibility of loaded units not adjacent to H. It therefore gives a genuine uniform geometric restriction, not a complete two-block exclusion or global nine-square theorem. The stated negative control and known equality configurations are consistent with this restriction.

No scope error, omitted endpoint, or mathematical defect was found in the reviewed new arguments. The inherited central-disk theorem retains its existing prerequisite and audit status; this review does not claim a fresh audit of that entire transitive source chain.

