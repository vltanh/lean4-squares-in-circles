module

public import SquaresInCircles.Eight.Arithmetic.AnglePolynomial

/-!
# The continuous theorem behind a fixed affine table row

`NumericValid` contains only finite rational computations.  Its soundness
theorem proves the strict charged inequality on the full two-state and angle
domain.  The original-axis adapter is in `PreparedRow`.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

def ArcData.signQ (a : ArcData) : ℚ := if a.positive then 1 else -1
theorem ArcData.signQ_cast (a : ArcData) : (a.signQ : ℝ)=a.sign := by
  cases h : a.positive <;> simp [signQ,sign,h]
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
      (.add (.add (.scale ((r.quarter : ℚ)/2) (param 0))
        (.constant (r.source.data.label.c-r.target.data.label.c)))
        (.add (.scale (signQ r.positiveHalf) .angle)
          (.scale (r.multiplier/2) (.add (.constant 1) (.add cosine sine)))))
      (.constant r.sourceSupport.lower))
    (.add (.scale (r.charge/2) (.sub (.add sine cosine) (.constant 1)))
      (.constant r.lowerTarget))

def targetLo (r : CoreRow) : ParamPoly 10 :=
  .add (.mul r.X (param 3)) (.mul r.Y (param 4))
def targetHi (r : CoreRow) : ParamPoly 10 :=
  .add (.mul r.X (param 5)) (.mul r.Y (param 6))
def slopeLo (r : CoreRow) : ParamPoly 10 := .sub r.Y (.mul r.X (param 7))
def slopeHi (r : CoreRow) : ParamPoly 10 := .sub r.Y (.mul r.X (param 8))
def majorant (r : CoreRow) : ParamPoly 10 :=
  .add (.constant (5*r.radicalParameter/16))
    (.add (.scale (15/(16*r.radicalParameter)) r.V)
      (.add (.scale (-5/(16*r.radicalParameter^3)) (.pow r.V 2))
        (.scale (1/(16*r.radicalParameter^5)) (.pow r.V 3))))
def targetCircle (r : CoreRow) : ParamPoly 10 :=
  .sub (.scale r.target.data.shift (.add r.X r.Y)) (.mul (param 9) r.majorant)

def PremiseCheck (r : CoreRow) : Prop :=
  match r.mode with
  | .lower => r.slopeLo.weakCheck (boxes r.target) r.angle ∧
      r.slopeHi.weakCheck (boxes r.target) r.angle
  | .upper => (ParamPoly.neg r.slopeLo).weakCheck (boxes r.target) r.angle ∧
      (ParamPoly.neg r.slopeHi).weakCheck (boxes r.target) r.angle
  | .endpoints => r.target.data.side=true ∨ r.X.weakCheck (boxes r.target) r.angle
  | .circle => r.target.data.side=false ∧ 0<r.radicalParameter

def CostCheck (r : CoreRow) : Prop :=
  match r.mode with
  | .lower => (ParamPoly.add r.base r.targetLo).strictCheck (boxes r.target) r.angle
  | .upper => (ParamPoly.add r.base r.targetHi).strictCheck (boxes r.target) r.angle
  | .endpoints => (ParamPoly.add r.base r.targetLo).strictCheck (boxes r.target) r.angle ∧
      (ParamPoly.add r.base r.targetHi).strictCheck (boxes r.target) r.angle
  | .circle => (ParamPoly.add r.base r.targetCircle).strictCheck (boxes r.target) r.angle

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
  cases h : r.axisFour <;>
    simp [Xs,Ys,axis,sourceX,sourceY,ArcData.signQ_cast,h]

theorem target_coefficients {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hs : Real.sin u=sin7 u+es*u^9) (hc : Real.cos u=cos8 u+ec*u^10) :
    r.X.eval (env r.target es ec) u=targetX r.axis r.target.data.label r.multiplier (r.phi u) ∧
    r.Y.eval (env r.target es ec) u=targetY r.axis r.target.data.label r.multiplier r.target.data.sign (r.phi u) := by
  have htr := shifted_eval (t:=r.target) (r:=r.positiveHalf) hk hs hc
  have hσ := ArcData.signQ_cast r.target.data
  cases h : r.axisFour <;>
    simp only [X,Y,axis,targetX,targetY,sinPhi,cosPhi,h,ParamPoly.eval,
      ParamPoly.scale,ParamPoly.constant,ParamPoly.sub,ScalarExpr.eval,
      CoreRow.phi,htr.1,htr.2,Bool.false_eq_true,↓reduceIte] <;>
    push_cast <;> rw [hσ] <;> constructor <;> ring

theorem norm_identity {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hs : Real.sin u=sin7 u+es*u^9) (hc : Real.cos u=cos8 u+ec*u^10) :
    r.V.eval (env r.target es ec) u=
      (r.X.eval (env r.target es ec) u)^2+(r.Y.eval (env r.target es ec) u)^2 := by
  have htr := shifted_eval (t:=r.target) (r:=r.positiveHalf) hk hs hc
  have hsc := Real.sin_sq_add_cos_sq (AnglePolynomial.phi r.quarter r.positiveHalf u)
  cases hax : r.axisFour <;> cases hsign : r.target.data.positive <;>
    simp only [V,X,Y,hax,sinPhi,cosPhi,ParamPoly.eval,
      ParamPoly.scale,ParamPoly.constant,ParamPoly.sub,ScalarExpr.eval,
      ArcData.signQ,hsign,htr.1,htr.2,Bool.false_eq_true,↓reduceIte] <;>
    push_cast <;>
    linear_combination (-(r.multiplier : ℝ)^2)*hsc

theorem base_eval {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hu : 0≤u ∧ u≤4/5) (hs : Real.sin u=sin7 u+es*u^9)
    (hc : Real.cos u=cos8 u+ec*u^10) :
    r.base.eval (env r.target es ec) u =
      lagrangianBase r.source.data.label r.target.data.label r.multiplier r.charge (r.phi u)+
        r.sourceSupport.lower-r.lowerTarget := by
  have ha := absolute_sum (r:=r.positiveHalf) hk hu
  have he0 : env r.target es ec 0 = Real.pi := rfl
  simp only [base,ParamPoly.eval,ParamPoly.scale,ParamPoly.constant,ParamPoly.sub,
    param,ScalarExpr.eval,sine_eval (t:=r.target) (ec:=ec) hs,
    cosine_eval (t:=r.target) (es:=es) hc,he0]
  unfold lagrangianBase frameWidth frameCharge
  have hcos : |Real.cos (r.phi u)| = Real.sin u+Real.cos u-|Real.sin (r.phi u)| := by
    have ha' : |Real.sin (r.phi u)|+|Real.cos (r.phi u)|=Real.sin u+Real.cos u := ha
    linarith
  rw [hcos]
  dsimp [phi,AnglePolynomial.phi]
  push_cast
  ring

theorem targetCircle_eval {r : CoreRow} {es ec u : ℝ} (hk : r.quarter≤1)
    (hs : Real.sin u=sin7 u+es*u^9) (hc : Real.cos u=cos8 u+ec*u^10) :
    r.targetCircle.eval (env r.target es ec) u =
      (r.target.data.shift : ℝ)*(r.X.eval (env r.target es ec) u+r.Y.eval (env r.target es ec) u)-
      r.target.radiusExpr.value*radicalMajorant r.radicalParameter
        ((r.X.eval (env r.target es ec) u)^2+(r.Y.eval (env r.target es ec) u)^2) := by
  have he9 : env r.target es ec 9 = r.target.radiusExpr.value := rfl
  simp only [targetCircle,majorant,ParamPoly.eval,ParamPoly.scale,ParamPoly.constant,
    ParamPoly.sub,param,ScalarExpr.eval,he9]
  rw [norm_identity hk hs hc]
  unfold radicalMajorant
  push_cast
  ring

/-- The strict Lagrangian bound of a core row, for every state of both arcs and every angle. -/
def Positive (r : CoreRow) : Prop :=
  ∀ a b A B u : ℝ, r.source.data.Contains r.source.radius a b →
    r.target.data.Contains r.target.radius A B → r.angle.Mem u →
    (r.lowerTarget : ℝ) <
      lagrangianBase r.source.data.label r.target.data.label r.multiplier r.charge (r.phi u)+
      sourceX r.axis r.source.data.label r.multiplier (r.phi u)*a+
      sourceY r.axis r.source.data.label r.multiplier r.source.data.sign (r.phi u)*b+
      targetX r.axis r.target.data.label r.multiplier (r.phi u)*A+
      targetY r.axis r.target.data.label r.multiplier r.target.data.sign (r.phi u)*B

/-- Finite coefficient proofs imply the actual strict Lagrangian bound. -/
theorem lagrangian_positive {r : CoreRow} (hr : r.NumericValid) : r.Positive := by
  intro a b A B u hsarc htarc hu
  have hsrc := hr.1
  have htar := hr.2.1
  have hk := hr.2.2.1
  have hlo0 : (0:ℝ)≤r.angle.lo := by exact_mod_cast hr.2.2.2.1
  have hu0 : 0≤u := hlo0.trans hu.1
  have hhi : (r.angle.hi : ℝ)≤4/5 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hr.2.2.2.2.2.1
    rw [Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
    exact h
  have hu4 : u≤4/5 := hu.2.trans hhi
  obtain ⟨es,hes0,hes1,hS⟩ := sin_remainder_coefficient hu0
  obtain ⟨ec,hec0,hec1,hC⟩ := cos_remainder_coefficient hu0
  have he : (boxes r.target).Mem (env r.target es ec) :=
    env_mem htar ⟨hes0,hes1⟩ ⟨by linarith,hec1⟩
  have hbase := base_eval hk ⟨hu0,hu4⟩ hS hC
  have hsource : (r.sourceSupport.lower : ℝ)≤(r.Xs : ℝ)*a+(r.Ys : ℝ)*b :=
    r.sourceSupport.sound hsrc hsarc
  have hxs := r.source_coefficients u
  have hxt := target_coefficients hk hS hC
  have hprem := hr.2.2.2.2.2.2.2.1
  have hcost := hr.2.2.2.2.2.2.2.2
  have htarget : 0 < r.base.eval (env r.target es ec) u+
      r.X.eval (env r.target es ec) u*A+r.Y.eval (env r.target es ec) u*B := by
    cases hm : r.mode with
    | lower =>
        have hp : r.slopeLo.weakCheck (boxes r.target) r.angle ∧
            r.slopeHi.weakCheck (boxes r.target) r.angle := by
          simpa [PremiseCheck,hm] using hprem
        have hc : (ParamPoly.add r.base r.targetLo).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have hL := ParamPoly.weakCheck_sound hp.1 he hu hu0
        have hU := ParamPoly.weakCheck_sound hp.2 he hu hu0
        change 0 ≤ r.Y.eval (env r.target es ec) u+
          -(r.X.eval (env r.target es ec) u*r.target.ratioLo.value) at hL
        change 0 ≤ r.Y.eval (env r.target es ec) u+
          -(r.X.eval (env r.target es ec) u*r.target.ratioHi.value) at hU
        have ht := PreparedArc.lower_endpoint (X := r.X.eval (env r.target es ec) u)
          (Y := r.Y.eval (env r.target es ec) u) htar htarc (by linarith) (by linarith)
        have hcpos := ParamPoly.strictCheck_sound hc he hu hu0
        change 0 < r.base.eval (env r.target es ec) u+
          (r.X.eval (env r.target es ec) u*r.target.aLo.value+
            r.Y.eval (env r.target es ec) u*r.target.bLo.value) at hcpos
        linarith
    | upper =>
        have hp : (ParamPoly.neg r.slopeLo).weakCheck (boxes r.target) r.angle ∧
            (ParamPoly.neg r.slopeHi).weakCheck (boxes r.target) r.angle := by
          simpa [PremiseCheck,hm] using hprem
        have hc : (ParamPoly.add r.base r.targetHi).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have hL := ParamPoly.weakCheck_sound hp.1 he hu hu0
        have hU := ParamPoly.weakCheck_sound hp.2 he hu hu0
        change 0 ≤ -(r.Y.eval (env r.target es ec) u+
          -(r.X.eval (env r.target es ec) u*r.target.ratioLo.value)) at hL
        change 0 ≤ -(r.Y.eval (env r.target es ec) u+
          -(r.X.eval (env r.target es ec) u*r.target.ratioHi.value)) at hU
        have ht := PreparedArc.upper_endpoint (X := r.X.eval (env r.target es ec) u)
          (Y := r.Y.eval (env r.target es ec) u) htar htarc (by linarith) (by linarith)
        have hcpos := ParamPoly.strictCheck_sound hc he hu hu0
        change 0 < r.base.eval (env r.target es ec) u+
          (r.X.eval (env r.target es ec) u*r.target.aHi.value+
            r.Y.eval (env r.target es ec) u*r.target.bHi.value) at hcpos
        linarith
    | endpoints =>
        have hp : r.target.data.side=true ∨ r.X.weakCheck (boxes r.target) r.angle := by
          simpa [PremiseCheck,hm] using hprem
        have hc : (ParamPoly.add r.base r.targetLo).strictCheck (boxes r.target) r.angle ∧
            (ParamPoly.add r.base r.targetHi).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have hmX : r.target.data.side=true ∨ 0≤r.X.eval (env r.target es ec) u :=
          hp.imp_right (fun hh => ParamPoly.weakCheck_sound hh he hu hu0)
        have hL := ParamPoly.strictCheck_sound hc.1 he hu hu0
        have hU := ParamPoly.strictCheck_sound hc.2 he hu hu0
        change 0 < r.base.eval (env r.target es ec) u+
          (r.X.eval (env r.target es ec) u*r.target.aLo.value+
            r.Y.eval (env r.target es ec) u*r.target.bLo.value) at hL
        change 0 < r.base.eval (env r.target es ec) u+
          (r.X.eval (env r.target es ec) u*r.target.aHi.value+
            r.Y.eval (env r.target es ec) u*r.target.bHi.value) at hU
        have ht := PreparedArc.endpoints_lower htar htarc hmX
          (m := min (r.X.eval (env r.target es ec) u*r.target.aLo.value+
              r.Y.eval (env r.target es ec) u*r.target.bLo.value)
            (r.X.eval (env r.target es ec) u*r.target.aHi.value+
              r.Y.eval (env r.target es ec) u*r.target.bHi.value))
          (min_le_left _ _) (min_le_right _ _)
        rcases min_choice (r.X.eval (env r.target es ec) u*r.target.aLo.value+
              r.Y.eval (env r.target es ec) u*r.target.bLo.value)
            (r.X.eval (env r.target es ec) u*r.target.aHi.value+
              r.Y.eval (env r.target es ec) u*r.target.bHi.value) with hmin | hmin <;>
          rw [hmin] at ht <;> linarith
    | circle =>
        have hp : r.target.data.side=false ∧ 0<r.radicalParameter := by
          simpa [PremiseCheck,hm] using hprem
        have hc : (ParamPoly.add r.base r.targetCircle).strictCheck (boxes r.target) r.angle := by
          simpa [CostCheck,hm] using hcost
        have ht := PreparedArc.circle_majorant_lower htar hp.1 htarc
          (by exact_mod_cast hp.2 : (0:ℝ)<r.radicalParameter)
          (X:=r.X.eval (env r.target es ec) u) (Y:=r.Y.eval (env r.target es ec) u)
        have hcpos := ParamPoly.strictCheck_sound hc he hu hu0
        change 0 < r.base.eval (env r.target es ec) u+
          r.targetCircle.eval (env r.target es ec) u at hcpos
        rw [targetCircle_eval hk hS hC] at hcpos
        linarith
  rw [hxs.1,hxs.2] at hsource
  rw [hbase,hxt.1,hxt.2] at htarget
  linarith

/-- The Lagrangian bound and a nonnegative multiplier give the charged inequality wherever
the forward margin is nonnegative. -/
theorem sound_of_positive {r : CoreRow} (hr : r.Positive) (hlam : 0 ≤ r.multiplier)
    {a b A B u : ℝ} (hsarc : r.source.data.Contains r.source.radius a b)
    (htarc : r.target.data.Contains r.target.radius A B) (hu : r.angle.Mem u)
    (haxis : 0≤forwardMargin r.axis r.source.data.sign r.target.data.sign a b A B (r.phi u)) :
    (r.lowerTarget : ℝ) < chargedCost r.source.data.label r.target.data.label
      r.charge a b A B (r.phi u) := by
  have hp := hr a b A B u hsarc htarc hu
  have hid := lagrangian_identity r.axis r.source.data.label r.target.data.label
    r.multiplier r.charge r.source.data.sign r.target.data.sign a b A B (r.phi u)
  have hlam' : (0:ℝ)≤r.multiplier := by exact_mod_cast hlam
  have hn := mul_nonneg hlam' haxis
  linarith

theorem sound {r : CoreRow} (hr : r.NumericValid)
    {a b A B u : ℝ} (hsarc : r.source.data.Contains r.source.radius a b)
    (htarc : r.target.data.Contains r.target.radius A B) (hu : r.angle.Mem u)
    (haxis : 0≤forwardMargin r.axis r.source.data.sign r.target.data.sign a b A B (r.phi u)) :
    (r.lowerTarget : ℝ) < chargedCost r.source.data.label r.target.data.label
      r.charge a b A B (r.phi u) :=
  sound_of_positive (lagrangian_positive hr) hr.2.2.2.2.2.2.1 hsarc htarc hu haxis

end CoreRow
end SquaresInCircles.Eight.Arithmetic
