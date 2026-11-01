# An isosceles contact triangle with two owned exits has radius greater than 13/6

November 1, 2026. New complete hand argument at the explicitly stated feature scope; independent review pending. Original nine-square parent counts are unchanged.

## Exact physical feature

Retain the same nine actual interior-disjoint unit squares in a disk, and the same original physical contact-force-and-torque certificate. Three entirely unloaded squares A,B,C have exactly the positive internal triangle and one positive outside exit each. Their outside terminals may repeat and all their other original equations and physical constraints remain.

Assume the three original internal applications P_AB, P_AC, P_BC are distinct; each of A and B has its two applications at adjacent own vertices; the two original normals from C to A and B are the SAME own side direction of C; and the original outside exit at each of A and B is an own side direction of that square. No shared-side mean, even at an endpoint, is moved.

Then R>13/6, so this full feature is impossible at R^2<=1105/256. Indeed 169/36-1105/256=871/2304>0.

This theorem applies in particular to the corresponding no-common-point singleton feature when one free internal AB normal forces shared exterior contacts at A and B under the existing common selector, and C owns AC and BC on one common side. That conditional selector reduction is not needed for the proof below and is not asserted for other contact patterns.

## 1. Complete coordinates for the stated feature

The contact triangle has the two side lengths |P_AB-P_AC|=|P_AB-P_BC|=1. Its third side lies on the actual common support side of C, so write its length as 0<d<=1. After one rigid motion and relabeling A,B, set

    P_AC=(-d/2,0), P_BC=(d/2,0), P_AB=(0,h),
    h=sqrt(1-d^2/4), sqrt(3)/2<=h<1.

The reflection placing P_AB above the common C side is harmless. C must lie below that side: if it lay above, the midpoint of P_AC,P_BC would be in the relative interior of its horizontal side, and P_AB would be in its interior because 0<h<1. This would contradict the packing.

The actual A and B squares must extend outwards from their respective contact-triangle sides. For A, the projection of P_BC onto the side from P_AC toward P_AB has coordinate d^2/2 in (0,1), and its perpendicular distance is dh in (0,1). Choosing the inward square would therefore place P_BC in int(A), impossible. The reflected statement treats B. Consequently, with

    u_A=(d/2,h), v_A=(-h,d/2),
    u_B=(-d/2,h), v_B=(h,d/2),

the actual squares are

    A=P_AC+[0,1]u_A+[0,1]v_A,
    B=P_BC+[0,1]u_B+[0,1]v_B.

Their outside own-axis normals must be v_A and v_B respectively. To see this without a strict singleton assumption, both internal force normals have nonpositive projection on v_A, since both applications are on A's v_A=0 side. The A-to-C force has strictly negative v_A component -a*d/2. Hence the full outside force has positive v_A component; among the four A own axes only v_A qualifies. The same argument gives v_B. In particular it covers all original side-boundary applications allowed by the stated domain.

## 2. Every original force and mean is retained

Write the original A-to-C and B-to-C forces as (0,-a) and (0,-b), with a,b>0. Write the A and B exit magnitudes as z_A,z_B>0. C's full outside force is (0,-a-b), so summing the three complete force equations gives

    z_A v_A+z_B v_B-(0,a+b)=0.

The horizontal component yields z_A=z_B=z>0; the vertical component yields

    a+b=zd.

The original A-to-B force is therefore

    f=(zh,a-zd/2).

Let the original A exit application be q_A=P_AC+v_A+t_Au_A, with 0<=t_A<=1. Its complete moment equation about P_AC is

    det(u_A,f)+det(v_A+t_Au_A,zv_A)=0,
    ad/2-z+zt_A=0.

Thus t_A=1-ad/(2z). The full B equation similarly gives t_B=1-bd/(2z). These are consequences for the unchanged means, not replacements of them.

The actual lower side of C has height -1. Write its original exit application as q_C=(m,-1). Its full torque equation about the origin gives

    -ad/2+bd/2-(a+b)m=0,
    m=(b-a)/(2z).

The original C mean must therefore have exactly this tangent coordinate. No assumption on C's horizontal placement or unused contacts is introduced.

## 3. Three actual outside points

If q minimizes a unit direction e on an actual unit square, q+e belongs to that same square: each own-coordinate component moves from its minimizing endpoint inward by at most one. This includes an arbitrary side mean. Apply this fact to the three unchanged outside neighbors.

Define r=(b-a)/z, so -d<r<d. The original disk contains

    w_A=P_AC+2v_A+t_Au_A,
    w_B=P_BC+2v_B+t_Bu_B,
    w_C=(r/2,-2).

Writing M=(w_A+w_B)/2 and V=(w_B-w_A)/2, direct substitution gives

    M=(rd^2/8,h^3+d),
    V=(D,-rdh/4),     D=2h+d^3/8,
    M-w_C=(-rh^2/2,H), H=h^3+d+2.

In particular |V|^2>=D^2 and |M-w_C|^2>=H^2.

## 4. A uniform three-point variance bound

For any 0<t<1, give w_A,w_B weights t/2 each and w_C weight 1-t. The weighted variance of these three actual disk points is

    t|V|^2+t(1-t)|M-w_C|^2.

It is at most R^2, since the weighted mean squared distance to the actual disk center equals that variance plus a nonnegative squared distance. Consequently

    R^2>=tD^2+t(1-t)H^2.

Here H>=3 and D<=17/8<3, so

    t=(D^2+H^2)/(2H^2)

lies strictly between zero and one. Substitution yields

    R >= (D^2+H^2)/(2H).

It remains to bound this expression uniformly on the whole closed range 0<d<=1.

First D^2>=4h^2=4-d^2. Also

    h^3=(1-d^2/4)^(3/2)>=1-3d^2/8,
    H>=3+d-3d^2/8>=3+5d/8.

The first inequality is the tangent inequality for the convex function x^(3/2). Alternatively put x=d^2/4 and compare the positive squares: (1-x)^3-(1-3x/2)^2=x^2(3/4-x)>=0.

The function H^2-(13/3)H is increasing for H>=3. Thus

    D^2+H^2-(13/3)H
      >= 4-d^2+(3+5d/8)^2-(13/3)(3+5d/8)
       = 25d/24-39d^2/64
      >= 83d/192 > 0.

Therefore R>13/6, as claimed. The strictness uses d>0; a zero contact gap is a common-junction feature, already separately excluded, and is not silently deleted here.

## Scope and remaining alternatives

The proof uses all three original internal forces and all three full outside exits, the actual torque at each hub, and actual points in the original outside squares. Repeated terminals are harmless. Every other real square remains in the original packing.

This is a complete exclusion at its stated geometric and owner hypotheses. It does not assume all distinct-contact triangles have this structure. In particular, two different C-owned side axes, non-owned exterior exits, and other vertex/side owner patterns are not covered by this manuscript. No original coarse or fine gate closes from this feature alone.
