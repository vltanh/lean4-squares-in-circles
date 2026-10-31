# Independent hand review: universal boundary-contact margin and common-side pressure

October 31, 2026. Reviewer: annular agent.

**Result: PASS at the source's stated scope.** Reviewed ENDBLOCK_GLOBAL_CONTACT_POINT_MARGIN_AND_COMMON_SIDE_PRESSURE_2026_10_31.md, especially Sections 1 and 3, with additional checks of the cut and witness-pair interfaces. No mathematical script, numerical sampling, Lean or CI was used.

## 1. The contact-point inequality

Independently reconstructed the three original geometric bounds:

    |c_H|>t=401/100-(9/5)R,
    |p|>=R-sqrt(2),
    |p-c_H|²<=1/2.

These imply the claimed strict lower bound for 2*c_H dot p, including shared-side means and individual zero circle weights. The physical circle corner and actual contact point belong to the same boundary unit, so the diameter estimate is legitimate.

Re-expanded the scalar expression:

    t²+(R-sqrt(2))²-1/2
      =(106/25)R²-(3609/250+2sqrt(2))R+175801/10000.

Replacing sqrt(2) by 99/70 has the stated strict direction for R>0. The resulting linear coefficient is 30213/1750, the square center is 30213/14840, and the residual denominator is 51940000. Independently multiplied

    175801*5194=913110394,
    30213²=912825369,
    913110394-912825369=285025.

Thus the completed-square residual is 11401/2077600, and halving gives exactly

    c_H dot p>11401/4155200.

The source correctly distinguishes this positive contact-point projection from a statement about contact normals or remote circle corners.

## 2. Common-side theorem, including every degenerate height

The force into the branch is in the outward normal cone of H at its actual application. Thus the own-side normal components alpha_e are nonnegative; zero components are tangent endpoint normals with the correct upper/lower sign. Summing the original zero origin moments gives a*B=sum alpha_e*y_e exactly.

For A=sum alpha_e>0, the identity

    a*(c_H dot F)=sum alpha_e*(c_H dot p_e)>delta*A

is correct. It first excludes a=0 and only then permits division by a. Tangential forces remain in B and the full moment identity.

For A=0,a>0, the same full moment equation forces B=0 and hence F=0. For A=a=0, the contact-point margin becomes Y*y_e>delta. A positive tangential force can occur only at the upper endpoint, forcing Y>0, while a negative one can occur only at the lower endpoint, forcing Y<0. They cannot coexist. Every surviving tangent force has the sign of Y, giving strict positive pressure. Origin-at-vertex cases are included because an endpoint at O cannot satisfy the strict contact margin.

Therefore the source's conclusion

    c_H dot F>=0, with equality only if F=0,

holds on the full printed domain.

## 3. Cut and extraction scope

The force and moment cut sums retain the common original applications, so internal actions cancel without deleting any required root equation. The support-minimality argument is explicitly conditional; with a zero branch force and zero branch origin moment, retaining that branch preserves the root balance, while the existing positive circle mass is still required.

The opposite-moment decomposition in Section 5 is an exact finite algebraic identity. A zero-moment atom has p=s*f with s>0: outward root support is nonnegative because O is in H, and p cannot vanish by its boundary-contact norm. The contact margin then gives positive pressure. Rescaled opposite-moment pairs inherit the same physical applications and cone membership. Applying the common-side algebra to such a pair is valid; the source correctly does not claim that the pair is an actual independent subcertificate.

Mixed-side interfaces and circle-clear cut neighbors remain outside the common-side theorem. No all-ten-parent closure or unrestricted n=9 result is inferred.

