module

public import SquaresInCircles.Eight.ExactFamily.PerturbationBounds

/-!
# Eight squares: the quantitative terminal inequality

For arbitrary centres, frame errors with total at most `1/1000`, the tilt `t = 2 arctan z` in
`[1/10, 4/25]`, and the owners of the edges, `quantitative` bounds the squared radius `q` below by
`qStar + (μ_H/8)(z - z*)²` plus the completed squares at the centres plus `terminalReserve` times
the total error. Its hypotheses are the containment of the five anchored corners, nonnegative gaps
along the owner normals, the small frame errors and the intervals for the coordinates of the two
slider centres; it assumes no lower bound on the radius and nothing about the equality case.
`Rigidity/Terminal.lean` applies it to a boundary cycle.

The weights are those of the adaptive chain at the tilt `z`. At zero error the reduced dual is
`qStar` plus `μ_H` times the defect of that chain (`adaptive_zero_reduced`), which is at least
`(z - z*)²/8`; the first-order terms are the linear combination of
`linear_variation_identity`, and the owner reserves and the remainder bounds along the adaptive
chain absorb them and the remainders.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily.Perturbation
open Coordinates

theorem zero_force (d : Coordinates) (t : ℝ) (htc : Real.cos t=d.c) (hts : Real.sin t=d.s)
    (o : Owners) (i : Fin 7) : force d t (fun _=>0) o i=d.forces i := by
  fin_cases i <;> ext <;>
    simp [force,forces,rawForces,ownerB,ownerU,ownerV,ownerD,ownerH,
      edgeAlpha,edgeBeta,edgeDelta,edgeEpsilon,edgeOmega,lam,rawLambda,
      ex,ey,sub,scale,add,htc,hts] <;> ring

theorem zero_offset (d : Coordinates) (t : ℝ) (htc : Real.cos t=d.c) (hts : Real.sin t=d.s)
    (i : Fin 5) : offset t (fun _=>0) i=d.anchorOffsets i := by
  fin_cases i <;> simp [offset,anchorOffsets,R,inFrame,htc,hts]

theorem zero_gap (d : Coordinates) (hw : d.WeightDomain) (t : ℝ)
    (htc : Real.cos t=d.c) (hts : Real.sin t=d.s) (o : Owners) (p : Positions) (i : Fin 7) :
    actualGap t (fun _=>0) o p i=OriginalDual.gap d p i := by
  fin_cases i <;>
    simp [actualGap,OriginalDual.gap,normal,support,phases,tails,heads,
      ownerB,ownerU,ownerV,ownerD,ownerH,ex,ey,Coordinates.e,Coordinates.f,
      dot,sub,htc,hts,Real.cos_neg,Real.sin_neg,abs_neg,
      abs_of_pos hw.c_pos,abs_of_pos hw.s_pos]

theorem adaptive_zero_reduced {d : Coordinates} (hd : d.IsChain) (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) (t : ℝ) (htc : Real.cos t=d.c) (hts : Real.sin t=d.s)
    (o : Owners) (p : Positions) :
    reduced d t (fun _=>0) o p=d.q+d.mu 4*d.defect := by
  let r := OriginalDual.reference d 0 0
  have hslide : ∀ v : Positions, sliderTerm d t (fun _=>0) o v=0 := by
    intro v
    simp [sliderTerm,zero_force d t htc hts,slider_forces_zero,dot]
  have hreduced : reduced d t (fun _=>0) o p=reduced d t (fun _=>0) o r := by
    simp [reduced,hslide]
  have hcomplete : completed d t (fun _=>0) o r=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hforce := d.force_balance hw hy i
    have hcent : r i.castSucc.castSucc=d.anchorCenters i := by fin_cases i <;> rfl
    rw [zero_force d t htc hts,zero_offset d t htc hts,hcent,hforce,d.anchor_vertex]
    have hm := ne_of_gt (hw.mu_pos i)
    dsimp [normSq,add,scale]
    field_simp [hm]
    ring
  have hgap (i : Fin 7) : actualGap t (fun _=>0) o r i=0 := by
    rw [zero_gap d hw t htc hts]
    exact OriginalDual.reference_gap d 0 0 i
  have hvertex (i : Fin 5) :
      normSq (add (r i.castSucc.castSucc) (offset t (fun _=>0) i))=
        d.q+(if i=4 then d.defect else 0) := by
    rw [zero_offset d t htc hts]
    have hcent : r i.castSucc.castSucc=d.anchorCenters i := by fin_cases i <;> rfl
    rw [hcent,d.anchor_vertex]
    fin_cases i <;> simp [anchorPoints,normSq,inFrame,defect]
    · linarith only [hd.first_circle]
    · linarith only [hd.second_circle]
    · linarith only [hd.third_circle]
    · linarith only [hd.fourth_circle]
    · linear_combination (d.h₁^2+d.h₂^2)*d.unit
  have hdual : dual d t (fun _=>0) o r=d.q+d.mu 4*d.defect := by
    simp [dual,hgap,hvertex,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hw.mu_sum]
  have hid := exact_completion hw t (fun _=>0) o r
  rw [hreduced,hdual,hcomplete,zero_add] at *
  exact hid.symm

/-- The first-order terms of the force, support and slider parts add up to a combination of the
errors along the tree of aligned edges, with the coefficients `coefficient`. -/
theorem linear_variation_identity {d : Coordinates} (hw : d.WeightDomain)
    (hstation : d.positionDerivative=0) (a : Errors) (o : Owners) (Z η : ℝ) :
    forceLinear d a o+supportLinear d a o+
      sliderLinear d a o Z (d.h₂+1/2+η)=
        ∑ i : Fin 5, coefficient d o Z η i*tree a i := by
  obtain ⟨hKA,hKB,hKD,hKE,hKH⟩ := coefficient_identities hw
  obtain ⟨hK,hL,hδ⟩ := cut_identities hw hstation
  have hc := ne_of_gt hw.c_pos
  have hs := ne_of_gt hw.s_pos
  have hβ : d.edgeBeta≠0 := ne_of_gt (hw.lam_pos 1)
  have hx₃ := ne_of_lt hw.x₃_neg
  have hx₄ := ne_of_lt hw.x₄_neg
  have hh₁ := ne_of_lt hw.h₁_neg
  have hM := ne_of_gt hw.weightMass_pos
  have hαβ : d.edgeBeta*(d.y+2)=d.edgeAlpha*d.x₂ := by
    dsimp [edgeBeta,edgeAlpha,lam,rawLambda,rawBeta]
    field_simp [ne_of_gt hw.y_add_two_pos,hM]
  have hεh : d.edgeEpsilon*d.h₁=d.edgeOmega*d.h₂ := by
    dsimp [edgeEpsilon,edgeOmega,lam,rawLambda,rawEpsilon]
    field_simp [hh₁,hM]
  have hR1 : KA d*d.c=d.edgeAlpha*d.x₁ := by rw [hKA]; field_simp
  have hR4 : KE d*d.s=-d.edgeDelta*d.x₄ := by rw [hKE]; field_simp
  have hRJ : d.edgeBeta*d.cutJ=d.edgeEpsilon*d.c+d.edgeDelta*d.x₄ := by
    dsimp only [cutJ]
    field_simp
    linear_combination (-d.x₄)*hδ
  have hRL : d.edgeEpsilon*d.s*d.y₄=d.edgeDelta*d.x₄-d.edgeEpsilon*d.c*d.x₄ := by
    dsimp only [cutL] at hL
    field_simp at hL
    linear_combination hL
  have e1 := congrArg (fun x => ownerB a o*x) hR1
  have e4 := congrArg (fun x => (a 4-ownerD a o)*x) hR4
  have eJ := congrArg (fun x => a 2*x) hRJ
  have ed := congrArg (fun x => (ownerV a o-a 2)*x) hδ
  have eab := congrArg (fun x => ownerB a o*x) hαβ.symm
  have eeh := congrArg (fun x => ownerH a o*x) hεh.symm
  have eL := congrArg (fun x => a 4*x) hRL
  rw [Fin.sum_univ_five]
  have c0 : coefficient d o Z η 0=
      -d.edgeAlpha/2+d.cutX+(if o 0 then d.edgeAlpha*d.cutY else 0) := rfl
  have c1 : coefficient d o Z η 1=
      if o 1 then -d.edgeBeta*(Z+d.cutJ) else -d.edgeBeta*(d.y+3/2+d.cutJ) := rfl
  have c2 : coefficient d o Z η 2=
      if o 2 then d.edgeBeta/2-d.cutK else -d.edgeBeta*(Z+d.cutJ) := rfl
  have c3 : coefficient d o Z η 3=
      d.edgeDelta/2-d.edgeEpsilon*d.c-(if o 3 then d.edgeDelta*(d.x₄-d.x₃) else 0) := rfl
  have c4 : coefficient d o Z η 4=
      -d.edgeOmega/2+d.cutN-(if o 4 then d.edgeOmega*η else 0) := rfl
  have t0 : tree a 0=-a 0 := rfl
  have t1 : tree a 1=a 1-a 0 := rfl
  have t2 : tree a 2=a 2-a 1 := rfl
  have t3 : tree a 3=a 3-a 2 := rfl
  have t4 : tree a 4=a 4 := rfl
  rw [c0,c1,c2,c3,c4]
  simp only [forceLinear,supportLinear,sliderLinear,t0,t1,t2,t3,t4,hKB,hKD,hKH,
    cutX,cutK,cutN,h₂tilt,cutY]
  -- Interpolate between the two owners. The identity is linear in each choice,
  -- so no enumeration of the 32 owner assignments is needed.
  have choose_linear (b : Bool) (x y : ℝ) :
      (if b then x else y) = y + (b.toNat : ℝ)*(x-y) := by
    cases b <;> simp
  simp only [ownerB,ownerU,ownerV,ownerD,ownerH,choose_linear] at e1 e4 ed eab eeh ⊢
  linear_combination -e1-e4+eJ-ed-eab-eeh-eL

theorem adaptive_order_bounds {z : ℝ} (hz : z ∈ tiltBox) :
    0<(adaptiveData z hz).cutY ∧ (adaptiveData z hz).cutY<1 ∧
    (adaptiveData z hz).edgeAlpha<(adaptiveData z hz).edgeBeta ∧
    (adaptiveData z hz).x₄-(adaptiveData z hz).x₃<0 := by
  have hb := radical_local_bounds (adaptive_local_mem hz)
  have hy := adaptiveY_mem hz
  have hw := adaptive_weightDomain hz
  have hα := hw.lam_pos 0
  have hM := hw.weightMass_pos
  change 17428/10000 ≤ (adaptiveData z hz).x₁ ∧ (adaptiveData z hz).x₁ ≤ 17649/10000 ∧
    16414/10000 ≤ (adaptiveData z hz).x₂ ∧ (adaptiveData z hz).x₂ ≤ 16691/10000 ∧
    14387/10000 ≤ (adaptiveData z hz).y₃ ∧ (adaptiveData z hz).y₃ ≤ 14643/10000 ∧
    -19049/10000 ≤ (adaptiveData z hz).x₄ ∧ (adaptiveData z hz).x₄ ≤ -18974/10000 ∧
    -14263/10000 ≤ (adaptiveData z hz).h₁ ∧ (adaptiveData z hz).h₁ ≤ -13198/10000 ∧
    -15316/10000 ≤ (adaptiveData z hz).h₂ ∧ (adaptiveData z hz).h₂ ≤ -13202/10000 at hb
  have hyy : (adaptiveData z hz).y=adaptiveY z hz := rfl
  have hβ : (adaptiveData z hz).edgeBeta=
      (adaptiveData z hz).edgeAlpha*(adaptiveData z hz).x₂/((adaptiveData z hz).y+2) := by
    simp only [edgeBeta,edgeAlpha,lam,rawLambda,rawBeta]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  dsimp only [Coordinates.cutY]
  refine ⟨by linarith only [hb.1, hb.2.2.2.1, hz],by linarith only [hb.2.1, hb.2.2.1, hz],?_,?_⟩
  · rw [hβ,lt_div_iff₀ hw.y_add_two_pos]
    have hx : (adaptiveData z hz).y+2<(adaptiveData z hz).x₂ := by
      rw [hyy]
      linarith only [hb.2.2.1, hy.2, hz]
    exact mul_lt_mul_of_pos_left hx hα
  · dsimp only [Coordinates.x₃]
    linarith only [hb.2.2.1, hb.2.2.2.2.2.2.2.1, hz]

theorem quantitative {q z t : ℝ} (hz : z ∈ tiltBox)
    (ht : t=2*Real.arctan z) (htw : 1/10≤t ∧ t≤4/25)
    (a : Errors) (o : Owners) (p : Positions) (hS : errorSum a≤1/1000)
    (hv : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (offset t a i))≤q)
    (hg : ∀ i : Fin 7, 0≤actualGap t a o p i)
    (hX : |(p 5).1|≤3/2) (hZabs : |(p 5).2|≤3/2)
    (hU : |dot (ex t) (p 6)|≤3/2) (hV : |dot (ey t) (p 6)|≤3/2)
    (hZ : 557/1000≤(p 5).2 ∧ (p 5).2≤1417/1000)
    (hη : -515/1000≤dot (ey t) (p 6)-(adaptiveData z hz).h₂-1/2 ∧
      dot (ey t) (p 6)-(adaptiveData z hz).h₂-1/2≤392/1000) :
    qStar+((adaptiveData z hz).mu 4/8)*(z-sharpData.z)^2+
      completed (adaptiveData z hz) t a o p+terminalReserve*errorSum a≤q := by
  let d := adaptiveData z hz
  have hw : d.WeightDomain := adaptive_weightDomain hz
  have hchain : d.IsChain := adaptive_chain hz
  have hstation : d.positionDerivative=0 := adaptive_position_stationary hz
  have hframe := atan_frame z
  have htc : Real.cos t=d.c := by rw [ht]; exact hframe.1
  have hts : Real.sin t=d.s := by rw [ht]; exact hframe.2
  have hdual := dual_le (d:=d) hw hv hg
  rw [exact_completion hw] at hdual
  have hzero := adaptive_zero_reduced hchain hw hstation t htc hts o p
  have hforce := force_term_lower hw htc hts a o
  have hsupport := support_term_lower hw htw htc hts hS o
    (w:=4209/5000) (by norm_num) (adaptive_edge_weight_bound hz)
  have hslider := slider_term_lower hw t a o p (w:=4209/5000) (by norm_num)
    (adaptive_edge_weight_bound hz 1) (adaptive_edge_weight_bound hz 4) hX hZabs hU hV
  have hlin := linear_variation_identity hw hstation a o (p 5).2
    (dot (ey t) (p 6)-d.h₂-1/2)
  have hVeq : d.h₂+1/2+(dot (ey t) (p 6)-d.h₂-1/2)=dot (ey t) (p 6) := by ring
  rw [hVeq] at hlin
  obtain ⟨hY0,hY1,hαβ,hxx⟩ := adaptive_order_bounds hz
  have hreserve := linear_cusp_lower hw hstation ⟨hY0,hY1⟩ hαβ hxx
    (adaptive_owner_bounds hz) hZ hη a o
  have hb := adaptive_remainder_bounds hz
  have hS0 := errorSum_nonneg a
  have hpow₂ := mul_le_mul_of_nonneg_right hb.1 (sq_nonneg (errorSum a))
  have hpow₃ := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg hS0 3)
  have hcurve := mul_le_mul_of_nonneg_left (adaptive_curvature hz) (hw.mu_pos 4).le
  have hp₂ : (errorSum a)^2≤errorSum a/1000 := by
    have h := mul_le_mul_of_nonneg_left hS hS0
    linarith only [sq (errorSum a), h]
  have hp₃ : (errorSum a)^3≤(errorSum a)^2/1000 := by
    have h := mul_le_mul_of_nonneg_right hS (sq_nonneg (errorSum a))
    have h3 : (errorSum a)^3=errorSum a*(errorSum a)^2 := by ring
    linarith only [h]
  have hq : d.q=qStar := rfl
  have hslide0 : sliderTerm d t (fun _=>0) o p=0 := by
    simp [sliderTerm,force,ownerU,ownerV,ownerH,ex,ey,dot,sub,scale]
  dsimp only [reduced] at hzero hdual
  dsimp only [quadraticCoefficient,cubicCoefficient] at hpow₂ hpow₃
  rw [hslide0,hq] at hzero
  have hρ : terminalReserve=10293/5000000 := rfl
  rw [hρ]
  linarith only [hdual,hzero,hforce,hsupport,hslider,hlin,hreserve,hpow₂,hpow₃,hcurve,
    hp₂,hp₃,hS0]

end SquaresInCircles.Eight.ExactFamily.Perturbation
