module

public import SquaresInCircles.Eight.ExactFamily.Stationary
public import SquaresInCircles.Eight.ExactFamily.Generated.EqualityBox
public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Common.SeparatingAxes

/-!
# The exact equality domain and its geometric converse

Uncompiled draft.  The seven central conditions are the four-axis SAT
conditions.  The exterior conditions are proved for their full closed slider
intervals, including contacts and endpoint ties.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily
open Coordinates EqualityParameters Arithmetic

def boxEnv (p : EqualityParameters) : Fin 8 → ℝ :=
  ![qStar,sharpPose.1,sharpPose.2,p.x,p.y,p.w,p.z,p.eta]

theorem boxEnv_mem {p : EqualityParameters} (hp : p.InBox) : EqualityGenerated.box.Mem (boxEnv p) := by
  have hs := sharpBox_mem
  intro i; fin_cases i
  · simpa [EqualityGenerated.box,boxEnv,Generated.sharpBox] using hs 0
  · simpa [EqualityGenerated.box,boxEnv,Generated.sharpBox] using hs 1
  · simpa [EqualityGenerated.box,boxEnv,Generated.sharpBox] using hs 2
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · exact hp.2.2.2.1
  · exact hp.2.2.2.2

def sampleParameters : EqualityParameters := ⟨7/50,0,1/10,27/20,-8/25⟩
theorem sampleParameters_inBox : sampleParameters.InBox := by
  norm_num [sampleParameters,EqualityParameters.InBox]

theorem sharp_exterior_bounds :
    0<sharpData.x₁-sharpData.x₂ ∧ sharpData.x₁-sharpData.x₂<1 ∧
    0<sharpData.x₂-3/2 ∧ sharpData.x₂-3/2<1/2 ∧
    0<sharpData.h₁+3/2 ∧ sharpData.h₁+3/2<1/2 ∧
    sharpData.x₄-sharpData.x₃<0 ∧
    0<sharpData.y+1 ∧ 0<sharpData.y₃-1 ∧
    sharpData.s*(sharpData.h₁+1)+sharpData.c*(sharpData.h₂+1)<0 ∧
    sharpData.s*(sharpData.h₁+2)-sharpData.c/12<0 ∧
    -(355/1000)<sharpData.c*(sharpData.h₁+1)+sharpData.s/12 := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hy := sharp_y
  have henv := boxEnv_mem sampleParameters_inBox
  have hH := (EqualityGenerated.topH_bound _ henv).2
  have hG := (EqualityGenerated.topG_bound _ henv).2
  have hL := (EqualityGenerated.leftG_bound _ henv).1
  have eH : EqualityGenerated.topHExpression.eval (boxEnv sampleParameters)=
      sharpData.s*(sharpData.h₁+1)+sharpData.c*(sharpData.h₂+1) := by
    norm_num [EqualityGenerated.topHExpression,ScalarExpr.eval,boxEnv,sharpData,
      radicalCoordinates,c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv] <;> ring
  have eG : EqualityGenerated.topGExpression.eval (boxEnv sampleParameters)=
      sharpData.s*(sharpData.h₁+2)-sharpData.c/12 := by
    norm_num [EqualityGenerated.topGExpression,ScalarExpr.eval,boxEnv,sharpData,
      radicalCoordinates,c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv] <;> ring
  have eL : EqualityGenerated.leftGExpression.eval (boxEnv sampleParameters)=
      sharpData.c*(sharpData.h₁+1)+sharpData.s/12 := by
    norm_num [EqualityGenerated.leftGExpression,ScalarExpr.eval,boxEnv,sharpData,
      radicalCoordinates,c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv] <;> ring
  rw [eH] at hH; rw [eG] at hG; rw [eL] at hL
  dsimp [x₃]
  repeat' constructor <;> linarith

theorem separated_by_normal {K L : UnitSquare} {n : Point} (hn : n≠(0,0))
    (hsep : width K n+width L n≤dot n (sub L.center K.center)) :
    ∀ p, ¬(openSquare K p ∧ openSquare L p) := by
  intro p hp
  have hK := (abs_lt.mp (dot_open_bound_of_ne K hn hp.1)).2
  have hL := (abs_lt.mp (dot_open_bound_of_ne L hn hp.2)).1
  have hid : dot n (sub L.center K.center)=dot n (sub p K.center)-dot n (sub p L.center) := by
    dsimp [dot,sub]; ring
  linarith

theorem separated_by_unsigned {K L : UnitSquare} {n : Point} (hn : n≠(0,0))
    (hsep : width K n+width L n≤|dot n (sub L.center K.center)|) :
    ∀ p, ¬(openSquare K p ∧ openSquare L p) := by
  rcases le_total 0 (dot n (sub L.center K.center)) with h | h
  · rw [abs_of_nonneg h] at hsep
    exact separated_by_normal hn hsep
  · apply separated_by_normal (n:=scale (-1) n)
    · intro hh
      apply hn
      ext <;> have h₁ := congrArg Prod.fst hh <;>
        have h₂ := congrArg Prod.snd hh <;> dsimp [scale] at h₁ h₂ <;> linarith
    · rw [width_neg,width_neg,dot_scale_left]
      rwa [abs_of_nonpos h] at hsep

theorem sat_max_iff (K L : UnitSquare) :
    (∀ p, ¬(openSquare K p ∧ openSquare L p)) ↔
      SAT.threshold K L≤max
        (max |frameX K (sub L.center K.center)| |frameY K (sub L.center K.center)|)
        (max |frameX L (sub L.center K.center)| |frameY L (sub L.center K.center)|) := by
  constructor
  · intro hd
    have h := SAT.separating_axes K L hd
    simpa only [le_max_iff] using h
  · intro hh
    simp only [le_max_iff] at hh
    rcases hh with (h | h) | (h | h)
    all_goals
      first
      | apply separated_by_unsigned (n:=(K.cosine,K.sine))
      | apply separated_by_unsigned (n:=(-K.sine,K.cosine))
      | apply separated_by_unsigned (n:=(L.cosine,L.sine))
      | apply separated_by_unsigned (n:=(-L.sine,L.cosine))
    all_goals
      first
      | intro hn
        have hx := congrArg Prod.fst hn
        have hy := congrArg Prod.snd hn
        nlinarith [K.unit,L.unit]
      | simpa [width,frameX,frameY,dot,SAT.threshold,relativeC,relativeS,
          abs_neg,add_comm,K.unit,L.unit] using h

theorem frame_parameter_bounds {p : EqualityParameters}
    (hl : 1-Real.sqrt 2≤p.w) (hu : p.w<Real.sqrt 2-1) :
    7/10<p.C ∧ |p.S|<18/25 ∧
      0<sharpData.c*p.C+sharpData.s*p.S := by
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hw : |p.w|<21/50 := by rw [abs_lt]; constructor <;> nlinarith
  have hpden := halfAngle_den_pos p.w
  have hC : 7/10<p.C := by
    dsimp [C,halfAngleCos]
    rw [lt_div_iff₀ hpden]
    have hb := abs_lt.mp hw
    nlinarith
  have hU := halfAngle_unit p.w
  have hS : |p.S|<18/25 := by
    dsimp [C] at hC
    dsimp [S]
    rw [abs_lt]
    constructor <;> nlinarith
  have hb := sharp_coordinates
  have hsp := abs_lt.mp hS
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  have hcc := mul_lt_mul_of_pos_left hC hc
  have hss := mul_lt_mul_of_pos_left hsp.1 hs
  refine ⟨hC,hS,?_⟩
  nlinarith [hb.2.2.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.2.2.2.2.1]

theorem central_axis_sat {p : EqualityParameters}
    (hframe : 1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1) (v : Point) :
    (∀ x, ¬(openSquare p.centralSquare x ∧ openSquare (axisSquare v) x)) ↔
      p.W₀≤p.M₀ (sub v p.center) := by
  have hc := (frame_parameter_bounds hframe.1 hframe.2).1
  rw [sat_max_iff]
  simp [SAT.threshold,relativeC,relativeS,centralSquare,axisSquare,frameX,frameY,
    W₀,M₀,abs_of_pos (by linarith : 0<p.C),abs_neg,max_comm,max_left_comm,max_assoc]

theorem central_tilted_sat {p : EqualityParameters}
    (hframe : 1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1) (v : Point) :
    (∀ x, ¬(openSquare p.centralSquare x ∧ openSquare (sharpData.tiltedSquare v) x)) ↔
      p.Wₜ sharpData≤p.Mₜ sharpData (sub v p.center) := by
  have hc := (frame_parameter_bounds hframe.1 hframe.2).2.2
  rw [sat_max_iff]
  simp [SAT.threshold,relativeC,relativeS,centralSquare,tiltedSquare,frameX,frameY,
    Wₜ,Mₜ,abs_of_pos hc,abs_neg,max_comm,max_left_comm,max_assoc,mul_comm]

theorem axis_containment (q : ℝ) (v : Point) : SqContained q (axisSquare v) ↔
    (|v.1|+1/2)^2+(|v.2|+1/2)^2≤q := by
  simp [SqContained,phi,alpha,beta,localX,localY,axisSquare,abs_neg]

theorem tilted_containment (d : Coordinates) (q a b : ℝ) :
    SqContained q (d.tiltedSquare (d.inFrame a b)) ↔
      (|a|+1/2)^2+(|b|+1/2)^2≤q := by
  have hx : localX (d.tiltedSquare (d.inFrame a b)) (0,0)= -a := by
    dsimp [localX,tiltedSquare,inFrame]
    linear_combination -a*d.unit
  have hy : localY (d.tiltedSquare (d.inFrame a b)) (0,0)= -b := by
    dsimp [localY,tiltedSquare,inFrame]
    linear_combination -b*d.unit
  simp [SqContained,phi,alpha,beta,hx,hy,abs_neg]

theorem exterior_contained {p : EqualityParameters} (hp : p.Admissible sharpData)
    (i : Fin 7) : SqContained qStar (sharpData.exteriorSquares p.z p.eta i) := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hy := sharp_y
  have hchain := sharpData_stationary
  have hq := qStar_limits.1
  have htopRad : 0≤sharpData.q-(sharpData.x₂-1)^2 := by
    change 0≤qStar-(sharpData.x₂-1)^2
    nlinarith
  have hGRad : 0≤sharpData.q-(sharpData.h₁+2)^2 := by
    change 0≤qStar-(sharpData.h₁+2)^2
    nlinarith
  have htop : p.z+1/2≤Real.sqrt (sharpData.q-(sharpData.x₂-1)^2) := by
    have h := hp.top_upper
    dsimp [zMax] at h
    linarith
  have hG : -Real.sqrt (sharpData.q-(sharpData.h₁+2)^2)≤sharpData.h₂+p.eta := by
    have h := hp.tilted_lower
    dsimp [etaMin] at h
    linarith
  have hGupper : sharpData.h₂+p.eta≤ -13/12 := by
    have h := hp.tilted_upper
    dsimp [etaMax] at h
    linarith
  fin_cases i
  · rw [exteriorSquares,pH,tilted_containment]
    rw [abs_of_neg (by linarith : sharpData.h₁+1/2<0),
      abs_of_neg (by linarith : sharpData.h₂+1/2<0)]
    dsimp [Coordinates.defect] at hchain.zero_defect
    nlinarith [hchain.zero_defect]
  · rw [exteriorSquares,pG,tilted_containment]
    rw [abs_of_pos (by linarith : 0<sharpData.h₁+3/2),
      abs_of_neg (by linarith : sharpData.h₂+1/2+p.eta<0)]
    nlinarith [Real.sq_sqrt hGRad,Real.sqrt_nonneg (sharpData.q-(sharpData.h₁+2)^2)]
  · rw [exteriorSquares,axis_containment]
    simp [pA,abs_of_pos (by linarith : 0<sharpData.x₁-1/2),
      abs_of_neg (by linarith : sharpData.y+1/2<0)]
    nlinarith [hchain.first_circle]
  · rw [exteriorSquares,axis_containment]
    simp [pB,abs_of_pos (by linarith : 0<sharpData.x₂-1/2),
      abs_of_pos (by linarith : 0<sharpData.y+3/2)]
    nlinarith [hchain.second_circle]
  · rw [exteriorSquares,axis_containment]
    simp [pT,abs_of_pos (by linarith : 0<sharpData.x₂-3/2),
      abs_of_pos (by linarith [hp.top_lower] : 0<p.z)]
    nlinarith [Real.sq_sqrt htopRad,Real.sqrt_nonneg (sharpData.q-(sharpData.x₂-1)^2)]
  · rw [exteriorSquares,axis_containment]
    simp [pD,x₃,abs_of_neg (by linarith : sharpData.x₂-3+1/2<0),
      abs_of_pos (by linarith : 0<sharpData.y₃-1/2)]
    nlinarith [hchain.third_circle]
  · rw [exteriorSquares,axis_containment]
    simp [pE,y₄,abs_of_neg (by linarith : sharpData.x₄+1/2<0),
      abs_of_neg (by linarith : sharpData.y₃-2+1/2<0)]
    nlinarith [hchain.fourth_circle]

def exteriorNormal (d : Coordinates) (i j : Fin 7) : Point :=
  if (i=0 ∧ j=1) ∨ (i=0 ∧ j=2) ∨ (i=1 ∧ j=2) then d.e
  else if i=0 ∧ j=6 then d.f
  else if (i=0 ∨ i=1) ∧ (j=3 ∨ j=4 ∨ j=5) then (0,1)
  else if (i=2 ∧ j=3) then (0,1)
  else if i=5 ∧ j=6 then (0,-1)
  else (-1,0)

theorem exterior_separator {p : EqualityParameters} (hp : p.Admissible sharpData)
    (i j : Fin 7) (hij : i<j) :
    exteriorNormal sharpData i j≠(0,0) ∧
      width (sharpData.exteriorSquares p.z p.eta i) (exteriorNormal sharpData i j)+
      width (sharpData.exteriorSquares p.z p.eta j) (exteriorNormal sharpData i j)≤
        dot (exteriorNormal sharpData i j)
          (sub (sharpData.exteriorCenters p.z p.eta j) (sharpData.exteriorCenters p.z p.eta i)) := by
  obtain ⟨hY0,hY1,hTx,hTxu,hGx,hGxu,hED,hyB,hyD,hHtop,hGtop,hGleft⟩ := sharp_exterior_bounds
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hη : sharpData.h₂+p.eta≤ -13/12 := by
    have h := hp.tilted_upper
    dsimp [etaMax] at h
    linarith
  have hηc := mul_le_mul_of_nonneg_left hη (by linarith : 0≤sharpData.c)
  have hηs := mul_le_mul_of_nonneg_left hη (by linarith : 0≤sharpData.s)
  have hunit := sharpData.unit
  have hHG := sharpData.HG_contact p.eta
  have hHA := sharpData.HA_contact
  have hGA := sharpData.GA_contact p.eta
  have hHE := sharpData.HE_contact
  have hst := sharpData.standard_contacts p.z
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    constructor
    · simp [exteriorNormal,Coordinates.e,Coordinates.f]
      first | norm_num | intro h; nlinarith [hc,hs]
    · simp [exteriorNormal,exteriorSquares,exteriorCenters,axisSquare,tiltedSquare,
        width,frameX,frameY,Coordinates.e,Coordinates.f,dot,sub,
        pA,pB,pD,pE,pH,pT,pG,inFrame,x₃,y₄,
        abs_of_pos (by linarith : 0<sharpData.c),
        abs_of_pos (by linarith : 0<sharpData.s),abs_neg] at *
      first | linarith | nlinarith [hp.top_lower]

theorem exterior_disjoint {p : EqualityParameters} (hp : p.Admissible sharpData) :
    InteriorDisjoint (sharpData.exteriorSquares p.z p.eta) := by
  intro i j hij x hx
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨hn,hs⟩ := exterior_separator hp i j hij
    exact separated_by_normal hn hs x hx
  · obtain ⟨hn,hs⟩ := exterior_separator hp j i hji
    exact separated_by_normal hn hs x ⟨hx.2,hx.1⟩

theorem model_sqPacking {p : EqualityParameters} (hp : p.Admissible sharpData) :
    SqPacking (p.model sharpData) (0,0) qStar := by
  refine ⟨by linarith [qStar_limits.1],?_,?_⟩
  · intro i x hx
    fin_cases i
    · have hq : 121/72<sharpData.q := by change 121/72<qStar; linarith [qStar_limits.1]
      have hc : SqContained qStar p.centralSquare := (central_containment hp hq).le
      simpa [sub] using ((SqContained.iff_points _ _).mp hc) x hx
    all_goals
      first
      | simpa [model,exteriorSquares,sub] using
          ((SqContained.iff_points _ _).mp (exterior_contained hp 0)) x hx
      | simpa [model,exteriorSquares,sub] using
          ((SqContained.iff_points _ _).mp (exterior_contained hp 1)) x hx
      | simpa [model,exteriorSquares,sub] using
          ((SqContained.iff_points _ _).mp (exterior_contained hp 2)) x hx
      | simpa [model,exteriorSquares,sub] using
          ((SqContained.iff_points _ _).mp (exterior_contained hp 3)) x hx
      | simpa [model,exteriorSquares,sub] using
          ((SqContained.iff_points _ _).mp (exterior_contained hp 4)) x hx
      | simpa [model,exteriorSquares,sub] using
          ((SqContained.iff_points _ _).mp (exterior_contained hp 5)) x hx
      | simpa [model,exteriorSquares,sub] using
          ((SqContained.iff_points _ _).mp (exterior_contained hp 6)) x hx
  · have hax := central_axis_sat ⟨hp.frame_lower,hp.frame_upper⟩
    have hti := central_tilted_sat ⟨hp.frame_lower,hp.frame_upper⟩
    have hA := (hax sharpData.pA).2 hp.A_sep
    have hB := (hax sharpData.pB).2 hp.B_sep
    have hD := (hax sharpData.pD).2 hp.D_sep
    have hE := (hax sharpData.pE).2 hp.E_sep
    have hT := (hax (sharpData.pT p.z)).2 hp.T_sep
    have hH := (hti sharpData.pH).2 hp.H_sep
    have hG := (hti (sharpData.pG p.eta)).2 hp.G_sep
    have hext := exterior_disjoint hp
    intro i j hij x hx
    by_cases hi : i=0
    · subst i
      fin_cases j <;> simp [model] at hx hij <;> first
        | exact hH x hx | exact hG x hx | exact hA x hx | exact hB x hx |
          exact hT x hx | exact hD x hx | exact hE x hx
    · by_cases hj : j=0
      · subst j
        fin_cases i <;> simp [model] at hx hij hi <;> first
          | exact hH x ⟨hx.2,hx.1⟩ | exact hG x ⟨hx.2,hx.1⟩ |
            exact hA x ⟨hx.2,hx.1⟩ | exact hB x ⟨hx.2,hx.1⟩ |
            exact hT x ⟨hx.2,hx.1⟩ | exact hD x ⟨hx.2,hx.1⟩ |
            exact hE x ⟨hx.2,hx.1⟩
      · obtain ⟨i,rfl⟩ := Fin.exists_eq_succ_of_ne_zero hi
        obtain ⟨j,rfl⟩ := Fin.exists_eq_succ_of_ne_zero hj
        apply hext i j (by simpa using hij) x
        simpa [model,exteriorSquares] using hx

end SquaresInCircles.Eight.ExactFamily
