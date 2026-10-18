module

public import SquaresInCircles.Eight.Arithmetic.AnglePolynomial

/-!
# The continuous theorem behind a fixed affine table row

`NumericValid` contains only finite rational computations.  Its soundness
theorem proves the strict charged inequality on the full two-state and angle
domain.  The original-axis adapter is in `PreparedRow`.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic

def ArcData.signQ (a : ArcData) : ℚ := if a.positive then 1 else -1
theorem ArcData.signQ_cast (a : ArcData) : (a.signQ : ℝ)=a.sign := by
  cases a.positive <;> simp [signQ,sign]
theorem ArcData.sign_sq (a : ArcData) : a.sign^2=1 := by
  cases a.positive <;> norm_num [sign]

structure CoreRow where
  source : PreparedArc
  target : PreparedArc
  axisFour : Bool
  quarter : ℕ
  positiveHalf : Bool
  angle : QInterval
  multiplier : ℚ
  charge : ℚ
  lowerTarget : ℚ
  mode : SupportMode
  radicalParameter : ℚ
  sourceNormRoot : QInterval
  deriving DecidableEq, Repr

namespace CoreRow
open AnglePolynomial

def axis (r : CoreRow) : ForwardAxis := if r.axisFour then .four else .one
def phi (r : CoreRow) (u : ℝ) : ℝ := AnglePolynomial.phi r.quarter r.positiveHalf u
def Xs (r : CoreRow) : ℚ :=
  if r.axisFour then r.source.data.label.p-r.multiplier else r.source.data.label.p
def Ys (r : CoreRow) : ℚ :=
  if r.axisFour then r.source.data.label.q
  else r.source.data.label.q-r.multiplier*r.source.data.signQ
def sourceSupport (r : CoreRow) : SourceSupport :=
  ⟨r.source,r.Xs,r.Ys,r.sourceNormRoot⟩
def sinPhi (r : CoreRow) : ParamPoly 10 := shiftedSine r.quarter r.positiveHalf
def cosPhi (r : CoreRow) : ParamPoly 10 := shiftedCosine r.quarter r.positiveHalf
def X (r : CoreRow) : ParamPoly 10 :=
  if r.axisFour then .add (.constant (-r.target.data.label.p)) (.scale r.multiplier r.cosPhi)
  else .sub (.constant (-r.target.data.label.p)) (.scale r.multiplier r.sinPhi)
def Y (r : CoreRow) : ParamPoly 10 :=
  .add (.constant (-r.target.data.label.q))
    (.scale (r.multiplier*r.target.data.signQ) (if r.axisFour then r.sinPhi else r.cosPhi))

/-- The squared norm is simplified using sin²+cos²=1 before compilation. -/
def V (r : CoreRow) : ParamPoly 10 :=
  .add (.constant (r.target.data.label.p^2+r.target.data.label.q^2+r.multiplier^2))
    (if r.axisFour then
      .add (.scale (-2*r.multiplier*r.target.data.label.p) r.cosPhi)
        (.scale (-2*r.multiplier*r.target.data.label.q*r.target.data.signQ) r.sinPhi)
    else
      .add (.scale (2*r.multiplier*r.target.data.label.p) r.sinPhi)
        (.scale (-2*r.multiplier*r.target.data.label.q*r.target.data.signQ) r.cosPhi))

def base (r : CoreRow) : ParamPoly 10 :=
  .sub
    (.add
      (.add (.add (.scale ((r.quarter : ℚ)/2) (variable 0))
        (.constant (r.source.data.label.c-r.target.data.label.c)))
        (.add (.scale (signQ r.positiveHalf) .angle)
          (.scale (r.multiplier/2) (.add (.constant 1) (.add cosine sine)))))
      (.constant r.sourceSupport.lower))
    (.add (.scale (r.charge/2) (.sub (.add sine cosine) (.constant 1)))
      (.constant r.lowerTarget))

def targetLo (r : CoreRow) : ParamPoly 10 :=
  .add (.mul r.X (variable 3)) (.mul r.Y (variable 4))
def targetHi (r : CoreRow) : ParamPoly 10 :=
  .add (.mul r.X (variable 5)) (.mul r.Y (variable 6))
def slopeLo (r : CoreRow) : ParamPoly 10 := .sub r.Y (.mul r.X (variable 7))
def slopeHi (r : CoreRow) : ParamPoly 10 := .sub r.Y (.mul r.X (variable 8))
def majorant (r : CoreRow) : ParamPoly 10 :=
  .add (.constant (5*r.radicalParameter/16))
    (.add (.scale (15/(16*r.radicalParameter)) r.V)
      (.add (.scale (-5/(16*r.radicalParameter^3)) (.pow r.V 2))
        (.scale (1/(16*r.radicalParameter^5)) (.pow r.V 3))))
def targetCircle (r : CoreRow) : ParamPoly 10 :=
  .sub (.scale r.target.data.shift (.add r.X r.Y)) (.mul (variable 9) r.majorant)

def PremiseCheck (r : CoreRow) : Prop :=
  match r.mode with
  | .lower => r.slopeLo.weakCheck (boxes r.target) r.angle ∧
      r.slopeHi.weakCheck (boxes r.target) r.angle
  | .upper => (.neg r.slopeLo).weakCheck (boxes r.target) r.angle ∧
      (.neg r.slopeHi).weakCheck (boxes r.target) r.angle
  | .endpoints => r.target.data.side=true ∨ r.X.weakCheck (boxes r.target) r.angle
  | .circle => r.target.data.side=false ∧ 0<r.radicalParameter

def CostCheck (r : CoreRow) : Prop :=
  match r.mode with
  | .lower => (.add r.base r.targetLo).strictCheck (boxes r.target) r.angle
  | .upper => (.add r.base r.targetHi).strictCheck (boxes r.target) r.angle
  | .endpoints => (.add r.base r.targetLo).strictCheck (boxes r.target) r.angle ∧
      (.add r.base r.targetHi).strictCheck (boxes r.target) r.angle
  | .circle => (.add r.base r.targetCircle).strictCheck (boxes r.target) r.angle

def NumericValid (r : CoreRow) : Prop :=
  r.sourceSupport.Valid ∧ r.target.NumericValid ∧ r.quarter≤1 ∧
  0≤r.angle.lo ∧ r.angle.lo≤r.angle.hi ∧ r.angle.hi≤4/5 ∧
  0≤r.multiplier ∧ r.PremiseCheck ∧ r.CostCheck

instance (r : CoreRow) : Decidable r.PremiseCheck := by
  unfold PremiseCheck; split <;> infer_instance
instance (r : CoreRow) : Decidable r.CostCheck := by
  unfold CostCheck; split <;> infer_instance
instance (r : CoreRow) : Decidable r.NumericValid := by unfold NumericValid; infer_instance

theorem source_coefficients (r : CoreRow) (u : ℝ) :
    (r.Xs : ℝ)=sourceX r.axis r.source.data.label r.multiplier (r.phi u) ∧
    (r.Ys : ℝ)=sourceY r.axis r.source.data.label r.multiplier r.source.data.sign (r.phi u) := by
  cases r.axisFour <;>
    simp [Xs,Ys,axis,sourceX,sourceY,ArcData.signQ_cast]

theorem target_coefficients {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hs : Real.sin u=sin7 u+es*u^9) (hc : Real.cos u=cos8 u+ec*u^10) :
    r.X.eval (env r.target es ec) u=targetX r.axis r.target.data.label r.multiplier (r.phi u) ∧
    r.Y.eval (env r.target es ec) u=targetY r.axis r.target.data.label r.multiplier r.target.data.sign (r.phi u) := by
  have htr := shifted_eval (t:=r.target) (r:=r.positiveHalf) hk hs hc
  cases r.axisFour <;>
    simp [X,Y,axis,targetX,targetY,sinPhi,cosPhi,ParamPoly.eval,
      ParamPoly.scale,ParamPoly.constant,ParamPoly.sub,ScalarExpr.eval,
      ArcData.signQ_cast,phi,htr.1,htr.2]

theorem norm_identity {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hs : Real.sin u=sin7 u+es*u^9) (hc : Real.cos u=cos8 u+ec*u^10) :
    r.V.eval (env r.target es ec) u=
      (r.X.eval (env r.target es ec) u)^2+(r.Y.eval (env r.target es ec) u)^2 := by
  have htr := shifted_eval (t:=r.target) (r:=r.positiveHalf) hk hs hc
  have hsc := Real.sin_sq_add_cos_sq (r.phi u)
  have hscmul := congrArg (fun z : ℝ => (r.multiplier : ℝ)^2*z) hsc
  cases hax : r.axisFour <;> cases hsign : r.target.data.positive <;>
    simp only [V,X,Y,hax,if_true,if_false,sinPhi,cosPhi,ParamPoly.eval,
      ParamPoly.scale,ParamPoly.constant,ParamPoly.sub,ScalarExpr.eval] <;>
    simp only [ArcData.signQ,hsign,if_true,if_false] <;> push_cast <;>
    simp only [htr.1,htr.2,← phi] <;>
    nlinarith only [hscmul]

theorem base_eval {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hu : 0≤u ∧ u≤4/5) (hs : Real.sin u=sin7 u+es*u^9)
    (hc : Real.cos u=cos8 u+ec*u^10) :
    r.base.eval (env r.target es ec) u =
      lagrangianBase r.source.data.label r.target.data.label r.multiplier r.charge (r.phi u)+
        r.sourceSupport.lower-r.lowerTarget := by
  have ha := absolute_sum (r:=r.positiveHalf) hk hu
  simp only [base,ParamPoly.eval,ParamPoly.scale,ParamPoly.constant,ParamPoly.sub,
    variable,ScalarExpr.eval,sine_eval hs,cosine_eval hc,env,Fin.isValue,
    Matrix.cons_val_zero]
  unfold lagrangianBase frameWidth frameCharge
  rw [show |Real.sin (r.phi u)|+|Real.cos (r.phi u)|=Real.sin u+Real.cos u from ha]
  dsimp [phi,AnglePolynomial.phi]
  push_cast
  ring

theorem targetCircle_eval {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hs : Real.sin u=sin7 u+es*u^9) (hc : Real.cos u=cos8 u+ec*u^10) :
    r.targetCircle.eval (env r.target es ec) u =
      (r.target.data.shift : ℝ)*(r.X.eval (env r.target es ec) u+r.Y.eval (env r.target es ec) u)-
      r.target.radiusExpr.value*radicalMajorant r.radicalParameter
        ((r.X.eval (env r.target es ec) u)^2+(r.Y.eval (env r.target es ec) u)^2) := by
  simp only [targetCircle,majorant,ParamPoly.eval,ParamPoly.scale,ParamPoly.constant,
    ParamPoly.sub,variable,ScalarExpr.eval,env,Matrix.cons_val_succ,Matrix.cons_val_zero]
  rw [norm_identity hk hs hc]
  unfold radicalMajorant
  push_cast
  ring

/-- Finite coefficient proofs imply the actual strict Lagrangian bound. -/
theorem lagrangian_positive {r : CoreRow} (hr : r.NumericValid)
    {a b A B u : ℝ} (hsarc : r.source.data.Contains r.source.radius a b)
    (htarc : r.target.data.Contains r.target.radius A B) (hu : r.angle.Mem u) :
    (r.lowerTarget : ℝ) <
      lagrangianBase r.source.data.label r.target.data.label r.multiplier r.charge (r.phi u)+
      sourceX r.axis r.source.data.label r.multiplier (r.phi u)*a+
      sourceY r.axis r.source.data.label r.multiplier r.source.data.sign (r.phi u)*b+
      targetX r.axis r.target.data.label r.multiplier (r.phi u)*A+
      targetY r.axis r.target.data.label r.multiplier r.target.data.sign (r.phi u)*B := by
  have hsrc := hr.1
  have htar := hr.2.1
  have hk := hr.2.2.1
  have hu0 : 0≤u := (by exact_mod_cast hr.2.2.2.1).trans hu.1
  have hu4 : u≤4/5 := hu.2.trans (by exact_mod_cast hr.2.2.2.2.2.1)
  obtain ⟨es,hes0,hes1,hS⟩ := sin_remainder_coefficient hu0
  obtain ⟨ec,hec0,hec1,hC⟩ := cos_remainder_coefficient hu0
  let e := env r.target es ec
  have he : (boxes r.target).Mem e := env_mem htar ⟨hes0,hes1⟩ ⟨hec0,hec1⟩
  have hbase := base_eval hk ⟨hu0,hu4⟩ hS hC
  have hsource := r.sourceSupport.sound hsrc hsarc
  have hxs := r.source_coefficients u
  have hxt := target_coefficients hk hS hC
  have hprem := hr.2.2.2.2.2.2.2.1
  have hcost := hr.2.2.2.2.2.2.2.2
  have htarget : 0 < r.base.eval e u+r.X.eval e u*A+r.Y.eval e u*B := by
    cases hm : r.mode with
    | lower =>
        have hp : r.slopeLo.weakCheck (boxes r.target) r.angle ∧
            r.slopeHi.weakCheck (boxes r.target) r.angle := by simpa [PremiseCheck,hm] using hprem
        have hc : (.add r.base r.targetLo).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have hL := ParamPoly.weakCheck_sound hp.1 he hu hu0
        have hU := ParamPoly.weakCheck_sound hp.2 he hu hu0
        have ht := PreparedArc.lower_endpoint htar htarc
          (by simpa [slopeLo,ParamPoly.sub,ParamPoly.eval,variable,ScalarExpr.eval,e,env] using hL)
          (by simpa [slopeHi,ParamPoly.sub,ParamPoly.eval,variable,ScalarExpr.eval,e,env] using hU)
        have hcpos := ParamPoly.strictCheck_sound hc he hu hu0
        simp only [ParamPoly.eval,targetLo,variable,ScalarExpr.eval,e,env,
          Matrix.cons_val_succ,Matrix.cons_val_zero] at hcpos
        linarith
    | upper =>
        have hp : (.neg r.slopeLo).weakCheck (boxes r.target) r.angle ∧
            (.neg r.slopeHi).weakCheck (boxes r.target) r.angle := by simpa [PremiseCheck,hm] using hprem
        have hc : (.add r.base r.targetHi).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have hL := ParamPoly.weakCheck_sound hp.1 he hu hu0
        have hU := ParamPoly.weakCheck_sound hp.2 he hu hu0
        have ht := PreparedArc.upper_endpoint htar htarc
          (by simpa [slopeLo,ParamPoly.sub,ParamPoly.eval,variable,ScalarExpr.eval,e,env] using hL)
          (by simpa [slopeHi,ParamPoly.sub,ParamPoly.eval,variable,ScalarExpr.eval,e,env] using hU)
        have hcpos := ParamPoly.strictCheck_sound hc he hu hu0
        simp only [ParamPoly.eval,targetHi,variable,ScalarExpr.eval,e,env,
          Matrix.cons_val_succ,Matrix.cons_val_zero] at hcpos
        linarith
    | endpoints =>
        have hp : r.target.data.side=true ∨ r.X.weakCheck (boxes r.target) r.angle := by
          simpa [PremiseCheck,hm] using hprem
        have hc : (.add r.base r.targetLo).strictCheck (boxes r.target) r.angle ∧
            (.add r.base r.targetHi).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have hmX : r.target.data.side=true ∨ 0≤r.X.eval e u :=
          hp.imp_right (fun hh => ParamPoly.weakCheck_sound hh he hu hu0)
        have hL := ParamPoly.strictCheck_sound hc.1 he hu hu0
        have hU := ParamPoly.strictCheck_sound hc.2 he hu hu0
        simp only [ParamPoly.eval,targetLo,targetHi,variable,ScalarExpr.eval,e,env,
          Matrix.cons_val_succ,Matrix.cons_val_zero] at hL hU
        let m := min (r.X.eval e u*r.target.aLo.value+r.Y.eval e u*r.target.bLo.value)
          (r.X.eval e u*r.target.aHi.value+r.Y.eval e u*r.target.bHi.value)
        have ht := PreparedArc.endpoints_lower htar htarc hmX
          (min_le_left _ _) (min_le_right _ _) (m:=m)
        have hpos : 0 < r.base.eval e u+m := by
          dsimp [m]
          rw [add_min]
          exact lt_min hL hU
        linarith
    | circle =>
        have hp : r.target.data.side=false ∧ 0<r.radicalParameter := by
          simpa [PremiseCheck,hm] using hprem
        have hc : (.add r.base r.targetCircle).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have ht := PreparedArc.circle_majorant_lower htar hp.1 htarc
          (by exact_mod_cast hp.2 : (0:ℝ)<r.radicalParameter)
          (X:=r.X.eval e u) (Y:=r.Y.eval e u)
        have hcpos := ParamPoly.strictCheck_sound hc he hu hu0
        change 0 < r.base.eval e u+r.targetCircle.eval e u at hcpos
        rw [targetCircle_eval hk hS hC] at hcpos
        linarith
  rw [hxs.1,hxs.2] at hsource
  dsimp [e] at htarget
  rw [hbase,hxt.1,hxt.2] at htarget
  linarith

theorem sound {r : CoreRow} (hr : r.NumericValid)
    {a b A B u : ℝ} (hsarc : r.source.data.Contains r.source.radius a b)
    (htarc : r.target.data.Contains r.target.radius A B) (hu : r.angle.Mem u)
    (haxis : 0≤forwardMargin r.axis r.source.data.sign r.target.data.sign a b A B (r.phi u)) :
    (r.lowerTarget : ℝ) < chargedCost r.source.data.label r.target.data.label
      r.charge a b A B (r.phi u) := by
  have hp := r.lagrangian_positive hr hsarc htarc hu
  have hid := lagrangian_identity r.axis r.source.data.label r.target.data.label
    r.multiplier r.charge r.source.data.sign r.target.data.sign a b A B (r.phi u)
  have hλ : (0:ℝ)≤r.multiplier := by exact_mod_cast hr.2.2.2.2.2.2.1
  have hn := mul_nonneg hλ haxis
  linarith

end CoreRow
end SquaresInCircles.Eight.Arithmetic
