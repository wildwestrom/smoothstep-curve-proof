/-

This spiral uses a smoothstep-based curvature function,
providing a $G^\infty$ continuous transition from tangent to circular arc.

The heading angle is given by:

$$\theta(l) = \frac{1}{R} \int_0^l F(\tfrac{v}{L})\,dv$$

where:
- $F(z) = \dfrac{\int_0^z G(t)\,dt}{\int_0^1 G(t)\,dt}$
- $G(t) = e^{\left(1-\tfrac{1}{t(1-t)}\right)}$
- $l$ = arc length along the curve
- $L$ = total length of the transition curve
- $R$ = radius of the circular arc

The Cartesian coordinates of the spiral are then:
$$x(l) = \int_0^l \cos\!\big(\theta(v)\big)\,dv,
\quad
y(l) = \int_0^l \sin\!\big(\theta(v)\big)\,dv$$
with initial conditions $x(0)=0,\ y(0)=0,\ \theta(0)=0$.

The curvature is:
$$\kappa(s) = R F\left(\frac{s}{L}\right)$$

---

This spiral also uses a smoothstep-based curvature function,
providing a $G^\infty$ continuous transition from tangent to circular arc.

The advantage of this over the previous smoothstep curve is that its first derivative
has a smaller apex, therefore the angular jerk and snap is smaller, thus requiring a shorter
transition length for the same deflection angle.

The heading angle is given by:
$$
\theta(l) = R \int_0^l F(\tfrac{v}{L})\,dv
$$

where:
- $F(z) = \dfrac{\int_0^z G(t-1)\,dt}{\int_0^1 G(t-1)\,dt}$
- $G(t) = e^{-\tfrac{1}{1-t^2}}$
- $l$ = arc length along the curve
- $L$ = total length of the transition curve
- $R$ = radius of the circular arc

The Cartesian coordinates of the spiral are then:
$$
x(l) = \int_0^l \cos\!\big(\theta(v)\big)\,dv,
\quad
y(l) = \int_0^l \sin\!\big(\theta(v)\big)\,dv
$$

with initial conditions $x(0)=0,\ y(0)=0,\ \theta(0)=0$.

The curvature is:
$$\kappa(s) = \frac{R}{2} F\left(\frac{2s}{L}\right)$$

---

My goal is to prove both of my curvature functions are $C^\infty$ continuous.

-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Filter
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Filter.Tendsto
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

noncomputable
section smoothstep_curve_1

open scoped ContDiff Topology

def denom_fn (t : ℝ) : ℝ := t * (1 - t)

lemma denom_is_C_inf : ContDiffOn ℝ ∞ denom_fn unitInterval := by
  exact contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)

lemma denom_contDiff : ContDiff ℝ ∞ denom_fn := by
  simpa using (contDiff_id.mul (contDiff_const.sub contDiff_id))

lemma denom_contDiffOn : ContDiffOn ℝ ∞ denom_fn unitInterval := by
  simpa using denom_is_C_inf

lemma denom_nonzero_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : 0 < denom_fn t := by
  rcases ht with ⟨ht0, ht1⟩
  exact mul_pos ht0 (sub_pos.mpr ht1)

lemma exp_is_C_inf : ContDiffOn ℝ ∞ (fun t => Real.exp t) unitInterval := by
  exact Real.contDiff_exp.contDiffOn

def bump_core (t : ℝ) : ℝ := Real.exp (-1 / (t * (1 - t)))

lemma denom_fn_Nonzero : ∀ t ∈ Set.Ioo 0 1, denom_fn t ≠ 0 := by
  intro t ht
  exact (denom_nonzero_on_Ioo t ht).ne'

lemma bump_core_is_C_inf : ContDiffOn ℝ ∞ bump_core (Set.Ioo 0 1) := by
  have h_inner2 : ContDiffOn ℝ ∞ (fun t : ℝ => -1 / (t * (1 - t))) (Set.Ioo (0 : ℝ) 1) := by
    simpa [denom_fn] using ContDiffOn.div
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (-1 : ℝ)) (Set.Ioo (0 : ℝ) 1))
      (denom_is_C_inf.mono (Set.Ioo_subset_Icc_self))
      denom_fn_Nonzero
  exact Real.contDiff_exp.comp_contDiffOn h_inner2

lemma expNegInvGlue_comp_denom_fn_eq_indicator_bump :
  (fun t => expNegInvGlue (denom_fn t))
  = Set.indicator (Set.Ioo (0:ℝ) 1) bump_core := by
  funext t
  by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
  · have hpos : 0 < denom_fn t := denom_nonzero_on_Ioo t ht
    have hL : expNegInvGlue (denom_fn t) = Real.exp (-1 / (t * (1 - t))) := by
        have hExp : expNegInvGlue (denom_fn t) = Real.exp (-(denom_fn t)⁻¹) := by
            simp [expNegInvGlue, not_le.mpr hpos]
        rw [hExp, denom_fn, div_eq_mul_inv, neg_mul, one_mul]
    have hR : Set.indicator (Set.Ioo (0:ℝ) 1) bump_core t = Real.exp (-1 / (t * (1 - t))) := by
        simp [Set.indicator_of_mem ht, bump_core, denom_fn]
    exact hL.trans hR.symm
  · have hnonpos : denom_fn t ≤ 0 := by
      have hcases : t ≤ 0 ∨ 1 ≤ t := by
          have : ¬ (0 < t ∧ t < 1) := by simpa [Set.mem_Ioo] using ht
          rcases not_and_or.mp this with hnot0 | hnot1
          · exact Or.inl (le_of_not_gt hnot0)
          · exact Or.inr (le_of_not_gt hnot1)
      cases hcases with
      | inl hle0 =>
          exact mul_nonpos_of_nonpos_of_nonneg hle0
              (sub_nonneg.mpr (le_trans hle0 (by norm_num)))
      | inr h1le =>
          exact mul_nonpos_of_nonneg_of_nonpos
              (le_trans (show (0:ℝ) ≤ 1 by norm_num) h1le)
              (sub_nonpos.mpr h1le)
    simp [expNegInvGlue.zero_of_nonpos hnonpos, Set.indicator_of_notMem ht]

def G (t : ℝ) : ℝ := expNegInvGlue (denom_fn t)

lemma expNegInvGlue_comp_is_C_inf_on_D :
  ContDiffOn ℝ ∞ (fun t => expNegInvGlue (denom_fn t)) unitInterval := by
  simpa using (expNegInvGlue.contDiff.comp denom_contDiff).contDiffOn

-- G is C^∞ continuous on [0, 1]
lemma G_is_C_inf : ContDiffOn ℝ ∞ G unitInterval := by
  exact expNegInvGlue_comp_is_C_inf_on_D

def F_num (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

lemma F_num_is_C_inf : ContDiffOn ℝ ∞ F_num unitInterval := by
  classical
  let P : ℝ → ℝ := fun z => ∫ t in (0)..z, G t
  have hcont : ContinuousOn G (Set.Icc 0 1) := G_is_C_inf.continuousOn
  have h_deriv_within : ∀ x ∈ unitInterval, HasDerivWithinAt P (G x) unitInterval x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hint : IntervalIntegrable G MeasureTheory.volume 0 x := by
      have hcont' : ContinuousOn G (Set.Icc 0 x) := hcont.mono (Set.Icc_subset_Icc le_rfl hx.2)
      simpa using
      (ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
        (u := G) (a := 0) (b := x) (h := hx0) hcont')
    -- within-set FTC filter on `Icc 0 1`
    haveI : Fact (x ∈ Set.Icc (0 : ℝ) 1) := ⟨hx.1, hx.2⟩
    haveI : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := by
      -- Use the instance for `𝓝[Set.Icc a b]` specialized to `a=0`, `b=1`.
      simpa [unitInterval] using
      (inferInstance : intervalIntegral.FTCFilter x (𝓝[Set.Icc (0 : ℝ) 1] x)
      (𝓝[Set.Icc (0 : ℝ) 1] x))
    have hmeas : StronglyMeasurableAtFilter G (𝓝[unitInterval] x) MeasureTheory.volume := by
      have hmeasSet : MeasurableSet unitInterval := by
        simp [unitInterval, isClosed_Icc.measurableSet]
      exact hcont.stronglyMeasurableAtFilter_nhdsWithin (hs := hmeasSet) x
    have hcontWithin : ContinuousWithinAt G unitInterval x := hcont.continuousWithinAt hx
    simpa [P] using
      (intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := x)
      (f := G) hint hmeas hcontWithin)
  have hUD : UniqueDiffOn ℝ unitInterval := by
    simpa [unitInterval] using uniqueDiffOn_Icc_zero_one
  have h_diff : DifferentiableOn ℝ P unitInterval :=
    fun x hx => (h_deriv_within x hx).differentiableWithinAt
  have h_deriv_eq : ∀ x ∈ unitInterval, derivWithin P unitInterval x = G x := by
    intro x hx
    have hsx : UniqueDiffWithinAt ℝ unitInterval x := by
      simpa [unitInterval] using (uniqueDiffOn_Icc_zero_one x ⟨hx.1, hx.2⟩)
    simpa using (HasDerivWithinAt.derivWithin (h_deriv_within x hx) hsx)
  have hP : ContDiffOn ℝ ∞ P unitInterval := by
    have := (contDiffOn_infty_iff_derivWithin (𝕜 := ℝ) (s₂ := unitInterval) (f₂ := P) hUD)
    refine this.mpr ?_
    refine And.intro h_diff ?_
    exact (contDiffOn_congr (s := unitInterval)
      (f₁ := derivWithin P unitInterval) (f := G) h_deriv_eq).mpr G_is_C_inf
  have h_congr_PI : ∀ z ∈ unitInterval, F_num z = P z := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz.1
    have : ∫ t in (0)..z, G t = ∫ t in Set.Ioc 0 z, G t := by
      simpa using
      (intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
      (f := G) (a := (0 : ℝ)) (b := z) hz0)
    simp [F_num, P, Set.uIoc, hz0, this]
  exact (contDiffOn_congr (s := unitInterval) (f₁ := F_num) (f := P) h_congr_PI).mpr hP

def F_den : ℝ := ∫ t in Set.uIoc 0 1, G t

lemma F_den_pos : 0 < F_den := by
  have hfi : IntervalIntegrable G MeasureTheory.volume 0 1 := by
    simpa using (ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      (u := G) (a := 0) (b := 1) (h := by norm_num) G_is_C_inf.continuousOn)
  have hpos : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → 0 < G x := by
    intro x hx
    exact expNegInvGlue.pos_of_pos (denom_nonzero_on_Ioo x hx)
  have hposI' : 0 < ∫ x in (0)..(1), G x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:=0) (b:=1) (f:=G) hfi hpos (by norm_num)
  have hposI : 0 < ∫ x in Set.Ioc 0 1, G x := by
    simpa [intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
      (f:=G) (a:=0) (b:=1) (by norm_num : (0:ℝ) ≤ 1)] using hposI'
  simpa [F_den, Set.uIoc, le_rfl] using hposI

lemma F_den_ne_0 : F_den ≠ 0 := by
  exact F_den_pos.ne'

def F (z : ℝ) : ℝ :=
  if z ≤ 0 then 0
  else if 1 ≤ z then 1
  else F_num z / F_den

lemma F_eq_ratio_on_unit {z : ℝ} (hz : z ∈ unitInterval) :
  F z = F_num z / F_den := by
  rcases hz with ⟨hz0, hz1⟩
  by_cases h0 : z = 0
  · subst h0
    simp [F, F_num, F_den, Set.uIoc, le_rfl]
  by_cases h1 : z = 1
  · subst h1
    have hden_ne : F_den ≠ 0 := ne_of_gt F_den_pos
    have hI : (∫ t in Set.Ioc 0 1, G t) = F_den := by
        simp [F_den, Set.uIoc, le_rfl]
    have hnum : F_num 1 = F_den := by
        simpa [F_num, Set.uIoc, le_rfl] using hI
    simp [F, le_rfl, hnum, hden_ne]
  simp [F, not_le.mpr (lt_of_le_of_ne hz0 (by simpa [eq_comm] using h0)),
    not_le.mpr (lt_of_le_of_ne hz1 (by simpa using h1))]

lemma G_NeZero : NeZero (fun (t : ℝ) => G t) := by
  refine ⟨by
    intro hzero
    have hx : (1 / 2 : ℝ) ∈ unitInterval := by constructor <;> norm_num
    have hIoo : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by constructor <;> norm_num
    have hden_pos : 0 < denom_fn (1 / 2 : ℝ) := denom_nonzero_on_Ioo _ hIoo
    have hGeq : G (1 / 2 : ℝ) = expNegInvGlue (denom_fn (1 / 2)) :=
      by exact rfl
    have hposE : 0 < expNegInvGlue (denom_fn (1 / 2 : ℝ)) :=
      expNegInvGlue.pos_of_pos hden_pos
    have hGzero : G (1 / 2 : ℝ) = 0 := by
      simpa using congrArg (fun f => f (1 / 2 : ℝ)) hzero
    have : expNegInvGlue (denom_fn (1 / 2 : ℝ)) = 0 := by
      rw [← hGeq]
      exact hGzero
    exact (ne_of_gt hposE) this⟩

-- F is C^∞ continuous on [0, 1]
lemma F_is_C_inf : ContDiffOn ℝ ∞ F unitInterval := by
  have h_congr : ∀ x ∈ unitInterval, F x = (fun x => F_num x / F_den) x := by
    intro x hx; simpa using F_eq_ratio_on_unit hx
  exact (contDiffOn_congr (s := unitInterval) (f₁ := F)
    (f := fun x => F_num x / F_den) h_congr).mpr
    (ContDiffOn.div_const F_num_is_C_inf F_den)

def κ_smooth (s R L) :=
  R * Real.smoothTransition (s / L)

lemma κ_smooth_is_C_inf : ContDiffOn ℝ ∞ (fun s ↦ κ_smooth s R L) (Set.Icc 0 L) := by
  simpa [κ_smooth] using contDiffOn_const.mul
    (Real.smoothTransition.contDiff.comp_contDiffOn (contDiffOn_id.div_const (c := L)))

lemma κ_smooth_at_zero : κ_smooth 0 R L = 0 := by
  simp [κ_smooth, Real.smoothTransition.zero]

lemma κ_smooth_at_L (hL : L ≠ 0) : κ_smooth L R L = R := by
  have : L / L = (1 : ℝ) := by
    simpa using (div_self hL)
  simp [κ_smooth, this, Real.smoothTransition.one]

def κ (s R L : ℝ) : ℝ :=
  R * F (s / L)

-- My curvature function is C^∞ continuous on [0, 1]
theorem κ_is_C_inf_on_Icc (R L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => κ s R L) (Set.Icc 0 L) := by
    -- compose with F which is C^∞ on [0,1]
  have h_comp : ContDiffOn ℝ ∞ (fun s : ℝ => F (s / L)) (Set.Icc 0 L) := by
    refine (F_is_C_inf.comp (contDiffOn_id.div_const (c := L)) ?maps)
    -- show s/L maps [0,L] into [0,1]
    intro s hs
    rcases hs with ⟨hs0, hsL⟩
    exact ⟨div_nonneg hs0 (le_of_lt hL),
      by simpa [div_self (ne_of_gt hL)] using
      div_le_div_of_nonneg_right hsL (le_of_lt hL)⟩
  simpa [κ] using (contDiffOn_const.mul h_comp)

theorem κ_at_zero : κ 0 R L = 0 := by
  simp [κ, F]

theorem κ_at_L (hL : L ≠ 0) : κ L R L = R := by
  have : L / L = (1 : ℝ) := by
    simpa using (div_self hL)
  simp [κ, F, this]

end smoothstep_curve_1

noncomputable
section smoothstep_curve_2
