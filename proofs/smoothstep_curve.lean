import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Topology.Order.DenselyOrdered

section GenericFramework

open ContDiff Topology
open MeasureTheory
open Filter

/-
## Generic Framework for Smoothstep Curves

The following definitions and lemmas establish the mathematical foundation for constructing
smoothstep curves from any C^∞ shape function shapeFn on [0,1] (or equivalently, from its derivative
G = shapeFn' which serves as a bump function in the implementation).
-/

lemma intervalIntegrable_on_unit_segment
  {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiffOn ℝ ∞ f unitInterval)
  (ha : a ∈ unitInterval) (hb : b ∈ unitInterval) (hab : a ≤ b) :
  IntervalIntegrable f volume a b :=
  (hf.continuousOn.mono fun _ ht => ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩).intervalIntegrable_of_Icc hab

/-- The antiderivative `z ↦ ∫ t in (0)..z, f t` based at `0`. -/
noncomputable def antiderivativeFromZero (f : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ t in (0)..z, f t

-- Helper: convert uIoc integral to intervalIntegral
lemma uIoc_to_intervalIntegral (f : ℝ → ℝ) {z : ℝ} (hz : z ∈ unitInterval) :
  (∫ t in Set.uIoc 0 z, f t) = ∫ t in (0)..z, f t := by
  simp [Set.uIoc, hz.1, (intervalIntegral.integral_of_le (μ := volume) (f := f) (a := 0) (b := z) hz.1).symm]

-- Global smoothness of the antiderivative when f is globally C^∞
lemma antiderivative_is_C_inf_global
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (antiderivativeFromZero f) := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · intro x
    exact (intervalIntegral.integral_hasDerivAt_right
      (hf.continuous.intervalIntegrable _ _)
      (hf.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      hf.continuous.continuousAt).differentiableAt
  · have hderiv : deriv (antiderivativeFromZero f) = f := by
      ext x
      exact (intervalIntegral.integral_hasDerivAt_right
        (hf.continuous.intervalIntegrable _ _)
        (hf.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
        hf.continuous.continuousAt).deriv
    rw [hderiv]
    exact hf

/-
### Core Definitions
-/

namespace Smooth

/-- Integral of the shape function along an interval `∫₀ᶻ G(t) dt`. Should be monotonically increasing. -/
noncomputable def shapeFnInt (G : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

/-- Constant `∫₀¹ G(t) dt` used to normalize the shape.
See `integral_Ioc_eq_of_support_unit` for proof that any upper bound ≥ 1 gives the same value. -/
noncomputable def shapeFnConst (G : ℝ → ℝ) : ℝ := ∫ t in Set.uIoc 0 1, G t

/-- The normalized shape function -/
noncomputable def shapeFn (G : ℝ → ℝ) (z : ℝ) : ℝ := shapeFnInt G z / shapeFnConst G

lemma shape_fn_zero_at_zero (G : ℝ → ℝ) : shapeFn G 0 = 0 := by simp [shapeFn, shapeFnInt]

lemma shape_fn_one_at_one (G : ℝ → ℝ) (shape_den_nonzero : shapeFnConst G ≠ 0) : shapeFn G 1 = 1 := by
  unfold shapeFn shapeFnInt shapeFnConst
  exact div_self shape_den_nonzero

-- Global smoothness of shape numerator when G is globally C^∞ and vanishes on (-∞, 0]
lemma shape_numerator_contDiff
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish_left : ∀ x, x ≤ 0 → G x = 0) :
    ContDiff ℝ ∞ (shapeFnInt G) := by
  have heq : shapeFnInt G = antiderivativeFromZero G := by
    ext z
    rcases le_or_gt z 0 with hz | hz
    · -- z ≤ 0
      simp only [shapeFnInt, Set.uIoc_comm, Set.uIoc_of_le hz]
      have h1 : ∫ t in Set.Ioc z 0, G t = 0 :=
        MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => hG_vanish_left t ht.2
      simp only [antiderivativeFromZero, intervalIntegral.integral_of_ge hz, h1, neg_zero]
    · -- 0 < z
      simp only [shapeFnInt, antiderivativeFromZero, Set.uIoc_of_le hz.le, intervalIntegral.integral_of_le hz.le]
  rw [heq]
  exact antiderivative_is_C_inf_global G hG

lemma ShapeFnConst_pos
  {G : ℝ → ℝ} (hint : IntervalIntegrable G volume 0 1)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  0 < shapeFnConst G := by
  rw [shapeFnConst, uIoc_to_intervalIntegral G ⟨zero_le_one, le_rfl⟩]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hint hpos (by norm_num)

lemma ShapeFnConst_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  MonotoneOn (shapeFnInt G) unitInterval := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hint_xy := intervalIntegrable_on_unit_segment hG hx hy hxy
    have h0x := intervalIntegrable_on_unit_segment hG ⟨le_rfl, by norm_num⟩ hx hx.1
    have hpos_xy t (ht : t ∈ Set.Ioo x y) : 0 < G t :=
      hpos t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0x hint_xy
    have hxInt : (∫ t in (0)..x, G t) = shapeFnInt G x := by simp [shapeFnInt, uIoc_to_intervalIntegral G hx]
    have hyInt : (∫ t in (0)..y, G t) = shapeFnInt G y := by simp [shapeFnInt, uIoc_to_intervalIntegral G hy]
    have hinc_pos := intervalIntegral.intervalIntegral_pos_of_pos_on hint_xy hpos_xy hlt
    linarith [hadd]

-- When G vanishes on (-∞, 0], shapeFnInt is zero for z ≤ 0
lemma shapeFnInt_eq_zero_of_nonpos
    {G : ℝ → ℝ} (hG_vanish : ∀ x, x ≤ 0 → G x = 0) {z : ℝ} (hz : z ≤ 0) :
    shapeFnInt G z = 0 := by
  simp only [shapeFnInt]
  rcases hz.lt_or_eq with hz' | rfl
  · -- z < 0: integral from 0 to z with G = 0 on Ioc z 0
    rw [Set.uIoc_comm, Set.uIoc_of_le hz'.le]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    exact hG_vanish t (ht.2 : t ≤ 0)
  · simp

lemma shapeFn_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < shapeFnConst G) :
  MonotoneOn (shapeFn G) unitInterval := fun _ hx _ hy hxy => by
  unfold shapeFn shapeFnConst
  exact div_le_div_of_nonneg_right (ShapeFnConst_monotone_on_unit hG hpos hx hy hxy) hden.le

-- Global derivative lemmas (avoiding iteratedDerivWithin)

lemma deriv_shapeFnInt_eq_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0) (x : ℝ) :
    deriv (shapeFnInt G) x = G x := by
  have hshapeFnInt := shape_numerator_contDiff hG hG_vanish
  have hderiv_prim : deriv (antiderivativeFromZero G) x = G x :=
    (intervalIntegral.integral_hasDerivAt_right
      (hG.continuous.intervalIntegrable _ _)
      (hG.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      hG.continuous.continuousAt).deriv
  have heq_nonneg : ∀ z, 0 ≤ z → shapeFnInt G z = antiderivativeFromZero G z := fun z hz => by
    simp only [shapeFnInt, antiderivativeFromZero, Set.uIoc_of_le hz, intervalIntegral.integral_of_le hz]
  have heq_neg : ∀ z, z ≤ 0 → shapeFnInt G z = antiderivativeFromZero G z := fun z hz => by
    simp only [shapeFnInt, antiderivativeFromZero]
    rw [Set.uIoc_comm, Set.uIoc_of_le hz, intervalIntegral.integral_of_ge hz]
    have : ∫ (t : ℝ) in Set.Ioc z 0, G t = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => hG_vanish t (ht.2 : t ≤ 0)
    simp [this]
  have heq : shapeFnInt G = antiderivativeFromZero G := by
    ext z
    rcases le_or_gt z 0 with hz | hz
    · exact heq_neg z hz
    · exact heq_nonneg z hz.le
  rw [heq, hderiv_prim]

lemma iteratedDeriv_succ_shapeFnInt_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0) (x : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (shapeFnInt G) x = iteratedDeriv n G x := by
  have hderiv_eq : deriv (shapeFnInt G) = G := funext (deriv_shapeFnInt_eq_global hG hG_vanish)
  induction n generalizing x with
  | zero => simp [iteratedDeriv_one, hderiv_eq]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    rw [hderiv_eq]

lemma iteratedDeriv_succ_shapeFn_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0) (x : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (shapeFn G) x = (1 / shapeFnConst G) * iteratedDeriv n G x := by
  set c := (1 / shapeFnConst G)
  have hshapeFn_eq : shapeFn G = fun z => c * shapeFnInt G z := by
    ext z; simp [shapeFn, c, div_eq_mul_inv, mul_comm]
  have hshapeFnInt := shape_numerator_contDiff hG hG_vanish
  induction n generalizing x with
  | zero =>
    rw [iteratedDeriv_one, hshapeFn_eq]
    simp [deriv_shapeFnInt_eq_global hG hG_vanish]
  | succ n ih =>
    have hG_diff : Differentiable ℝ (iteratedDeriv n G) :=
      ContDiff.differentiable_iteratedDeriv' n (contDiff_infty.mp hG (n + 1))
    calc iteratedDeriv (n + 1 + 1) (shapeFn G) x
        = deriv (iteratedDeriv (n + 1) (shapeFn G)) x := by rw [iteratedDeriv_succ]
      _ = deriv (fun y => c * iteratedDeriv n G y) x := by
          congr 1; ext y; rw [ih]
      _ = c * deriv (iteratedDeriv n G) x := deriv_const_mul c hG_diff.differentiableAt
      _ = c * iteratedDeriv (n + 1) G x := by rw [← iteratedDeriv_succ]

lemma shapeFn_deriv_vanishes_at_point_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0)
    {x : ℝ} (hG_x : G x = 0)
    (hG_deriv_x : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n G x = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDeriv n (shapeFn G) x = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  simp only [iteratedDeriv_succ_shapeFn_global hG hG_vanish]
  rcases k with _ | k <;> simp [hG_x, hG_deriv_x _ (Nat.succ_pos _)]

-- Unit interval derivative lemmas (legacy, for proofs that still need them)

-- shapeFn maps to [0,1] on unitInterval
lemma shapeFn_mem_unitInterval
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < shapeFnConst G)
  {z : ℝ} (hz : z ∈ unitInterval) :
  shapeFn G z ∈ unitInterval := by
  have hshapeFnmono := shapeFn_monotone_on_unit hG hpos hden
  constructor
  · simpa [shape_fn_zero_at_zero G] using hshapeFnmono ⟨le_rfl, by norm_num⟩ hz hz.1
  · simpa [shape_fn_one_at_one G hden.ne'] using hshapeFnmono hz ⟨zero_le_one, le_rfl⟩ hz.2

/-- Curvature profile induced by a shape function over a transition of length `L`. -/
noncomputable def curvatureOfShape (shapeFn : ℝ → ℝ) (s R₁ R₂ L : ℝ) : ℝ :=
  R₁ + (R₂ - R₁) * shapeFn (s / L)

lemma div_mem_unitInterval_of_mem_Icc {L : ℝ} (hL : 0 < L) {s : ℝ}
    (hs : s ∈ Set.Icc 0 L) : s / L ∈ unitInterval :=
  ⟨div_nonneg hs.1 hL.le, by simpa [div_self hL.ne'] using div_le_div_of_nonneg_right hs.2 hL.le⟩

lemma curvatureOfShape_at_zero (shapeFn : ℝ → ℝ) (R₁ R₂ L : ℝ) (hshapeFn0 : shapeFn 0 = 0) :
    curvatureOfShape shapeFn 0 R₁ R₂ L = R₁ := by simp [curvatureOfShape, hshapeFn0]

lemma curvatureOfShape_at_L (shapeFn : ℝ → ℝ) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (hshapeFn1 : shapeFn 1 = 1) :
    curvatureOfShape shapeFn L R₁ R₂ L = R₂ := by simp [curvatureOfShape, div_self hL, hshapeFn1]

lemma curvatureOfShape_deriv_vanishes_at_zero
    {shapeFn : ℝ → ℝ} (hshapeFn : ContDiff ℝ ∞ shapeFn)
    (hflat : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n shapeFn 0 = 0)
    (R₁ R₂ L : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => curvatureOfShape shapeFn s R₁ R₂ L) 0 = 0 := by
  rw [show (fun s => curvatureOfShape shapeFn s R₁ R₂ L) =
      (fun s => R₁ + (R₂ - R₁) * shapeFn ((1 / L) * s)) by
        ext s
        simp [curvatureOfShape, div_eq_mul_inv, mul_comm]]
  rw [iteratedDeriv_const_add (Nat.one_le_iff_ne_zero.mp hn).bot_lt]
  rw [iteratedDeriv_const_mul_field]
  have hshapeFnn : ContDiff ℝ n shapeFn := hshapeFn.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  rw [iteratedDeriv_comp_const_mul hshapeFnn (1 / L)]
  simp [hflat n hn]

lemma curvatureOfShape_deriv_vanishes_at_L
    {shapeFn : ℝ → ℝ} (hshapeFn : ContDiff ℝ ∞ shapeFn)
    (hflat : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n shapeFn 1 = 0)
    (R₁ R₂ L : ℝ) (hL : L ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => curvatureOfShape shapeFn s R₁ R₂ L) L = 0 := by
  have hshift :
      iteratedDeriv n (fun t => curvatureOfShape shapeFn (t + L) R₁ R₂ L) 0 =
        iteratedDeriv n (fun s => curvatureOfShape shapeFn s R₁ R₂ L) L := by
    simpa using congrArg (fun g => g 0) (iteratedDeriv_comp_add_const n
      (fun s => curvatureOfShape shapeFn s R₁ R₂ L) L)
  have harg : ∀ t : ℝ, (t + L) / L = (1 / L) * t + 1 := by
    intro t
    field_simp [hL]
  rw [← hshift]
  rw [show (fun t => curvatureOfShape shapeFn (t + L) R₁ R₂ L) =
      (fun t => R₁ + (R₂ - R₁) * shapeFn ((1 / L) * t + 1)) by
        ext t
        simp [curvatureOfShape, harg t]]
  rw [iteratedDeriv_const_add (Nat.one_le_iff_ne_zero.mp hn).bot_lt]
  rw [iteratedDeriv_const_mul_field]
  have hshifted : ContDiff ℝ n (fun z => shapeFn (z + 1)) :=
    (hshapeFn.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  have hshift_shapeFn : iteratedDeriv n (fun z => shapeFn (z + 1)) = fun t => iteratedDeriv n shapeFn (t + 1) := by
    simpa using iteratedDeriv_comp_add_const n shapeFn 1
  rw [show (fun t => shapeFn ((1 / L) * t + 1)) = (fun t => (fun z => shapeFn (z + 1)) ((1 / L) * t)) by
        ext t
        simp]
  rw [iteratedDeriv_comp_const_mul hshifted (1 / L)]
  rw [hshift_shapeFn]
  simp [hflat n hn]

-- Helper lemma for the common setup in monotonicity proofs
private lemma curvature_inequality_helper_of_shape
    {shapeFn : ℝ → ℝ} (hmono : MonotoneOn shapeFn unitInterval) (L : ℝ) (hL : 0 < L)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 L) (hy : y ∈ Set.Icc 0 L) (hxy : x ≤ y) :
    shapeFn (x / L) ≤ shapeFn (y / L) :=
  hmono (div_mem_unitInterval_of_mem_Icc hL hx) (div_mem_unitInterval_of_mem_Icc hL hy)
    (div_le_div_of_nonneg_right hxy hL.le)

lemma curvatureOfShape_monotone_on_Icc
    {shapeFn : ℝ → ℝ} (hshapeFnmono : MonotoneOn shapeFn unitInterval)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hmono : R₁ ≤ R₂) :
    MonotoneOn (fun s => curvatureOfShape shapeFn s R₁ R₂ L) (Set.Icc 0 L) := fun _ hx _ hy hxy =>
  add_le_add_right (mul_le_mul_of_nonneg_left
    (curvature_inequality_helper_of_shape hshapeFnmono L hL _ _ hx hy hxy) (sub_nonneg.mpr hmono)) R₁

lemma curvatureOfShape_antitone_on_Icc
    {shapeFn : ℝ → ℝ} (hshapeFnmono : MonotoneOn shapeFn unitInterval)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hmono : R₂ ≤ R₁) :
    AntitoneOn (fun s => curvatureOfShape shapeFn s R₁ R₂ L) (Set.Icc 0 L) := fun _ hx _ hy hxy =>
  add_le_add_right (mul_le_mul_of_nonpos_left
    (curvature_inequality_helper_of_shape hshapeFnmono L hL _ _ hx hy hxy) (sub_nonpos.mpr hmono)) R₁

section SmoothStepStructure

/-
### SmoothstepCurve Structure

This structure encapsulates a complete smoothstep curve with all its properties.
-/

/-- A globally smooth monotone shape together with its induced curvature profile. -/
structure SmoothstepCurve where
  /-- The shape function `shapeFn : ℝ → ℝ`. -/
  shapeFn : ℝ → ℝ
  /-- The induced curvature profile `curvature(s, R₁, R₂, L) = R₁ + (R₂ - R₁) * shapeFn (s / L)`. -/
  curvature : ℝ → ℝ → ℝ → ℝ → ℝ

  ----- Condition 1: Global Smoothness (shapeFn ∈ C^∞(ℝ)) -----
  shapeFn_is_C_inf : ContDiff ℝ ∞ shapeFn

  ----- Condition 2: Boundary values and extension -----
  shapeFn_zero : shapeFn 0 = 0
  shapeFn_one : shapeFn 1 = 1
  -- shapeFn is 0 for z ≤ 0
  shapeFn_eq_zero_of_nonpos : ∀ z, z ≤ 0 → shapeFn z = 0
  -- shapeFn is 1 for z ≥ 1
  shapeFn_eq_one_of_one_le : ∀ z, 1 ≤ z → shapeFn z = 1

  ----- Curvature smoothness and boundary matching -----
  -- curvature is globally C^∞
  curvature_is_C_inf : ∀ R₁ R₂ L, ContDiff ℝ ∞ (fun s => curvature s R₁ R₂ L)
  -- The defining formula: curvature(s) = R₁ + ΔR · shapeFn(s/L) where ΔR = R₂ - R₁
  curvature_formula : ∀ s R₁ R₂ L, curvature s R₁ R₂ L = R₁ + (R₂ - R₁) * shapeFn (s / L)

  ----- Condition 3: Monotonicity (shapeFn'(z) ≥ 0 for all z ∈ [0,1]) -----
  -- shapeFn is monotonically increasing on [0,1]
  shapeFn_monotone_on_unit : MonotoneOn shapeFn unitInterval

  ----- Condition 4: Flatness at endpoints (shapeFn^(n)(0) = shapeFn^(n)(1) = 0 for all n ≥ 1) -----
  -- All derivatives vanish at z = 0, ensuring G^∞ continuity at the start join
  shapeFn_deriv_vanishes_at_zero : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n shapeFn 0 = 0
  -- All derivatives vanish at z = 1, ensuring G^∞ continuity at the end join
  shapeFn_deriv_vanishes_at_one : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n shapeFn 1 = 0

/-- shapeFn maps [0,1] into [0,1] for a smoothstep curve. -/
lemma SmoothstepCurve.shapeFn_mem_unitInterval' (sc : SmoothstepCurve) {z : ℝ} (hz : z ∈ unitInterval) :
    sc.shapeFn z ∈ unitInterval := by
  constructor
  · rw [← sc.shapeFn_zero]
    exact sc.shapeFn_monotone_on_unit (by norm_num : (0 : ℝ) ∈ unitInterval) hz hz.1
  · rw [← sc.shapeFn_one]
    exact sc.shapeFn_monotone_on_unit hz (by norm_num : (1 : ℝ) ∈ unitInterval) hz.2

/-- Constructor that takes an abstract shape function satisfying the four core properties. -/
noncomputable def mkSmoothstepCurveFromShape (shapeFn : ℝ → ℝ)
  (hshapeFn_smooth : ContDiff ℝ ∞ shapeFn)
  (hshapeFn_zero : shapeFn 0 = 0) (hshapeFn_one : shapeFn 1 = 1)
  (hshapeFn_eq_zero_of_nonpos : ∀ z, z ≤ 0 → shapeFn z = 0)
  (hshapeFn_eq_one_of_one_le : ∀ z, 1 ≤ z → shapeFn z = 1)
  (hshapeFn_mono : MonotoneOn shapeFn unitInterval)
  (hshapeFn_deriv_zero : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n shapeFn 0 = 0)
  (hshapeFn_deriv_one : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n shapeFn 1 = 0) :
  SmoothstepCurve :=
  {
    shapeFn := shapeFn,
    curvature := fun s R₁ R₂ L => curvatureOfShape shapeFn s R₁ R₂ L,
    shapeFn_is_C_inf := hshapeFn_smooth,
    shapeFn_zero := hshapeFn_zero,
    shapeFn_one := hshapeFn_one,
    shapeFn_eq_zero_of_nonpos := hshapeFn_eq_zero_of_nonpos,
    shapeFn_eq_one_of_one_le := hshapeFn_eq_one_of_one_le,
    curvature_is_C_inf := fun R₁ R₂ L => by
      simp only [curvatureOfShape]
      exact contDiff_const.add (contDiff_const.mul (hshapeFn_smooth.comp (contDiff_id.div_const L))),
    curvature_formula := fun _ _ _ _ => rfl,
    shapeFn_monotone_on_unit := hshapeFn_mono,
    shapeFn_deriv_vanishes_at_zero := hshapeFn_deriv_zero,
    shapeFn_deriv_vanishes_at_one := hshapeFn_deriv_one
  }

-- Helper lemmas for expNegInvGlue compositions
-- These show that shapeFn has vanishing derivatives when G = expNegInvGlue ∘ denom,
-- without requiring denom itself to vanish.

lemma slope_zero_of_left_const {f : ℝ → ℝ} (hf : ∀ x ≤ 0, f x = f 0) :
    (fun x => slope f 0 x) =ᶠ[𝓝[Set.Iio (0 : ℝ)] 0] fun _ => 0 :=
  Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => by
    have hfx : f x = f 0 := hf x (le_of_lt hx)
    simp [slope, hfx]

lemma iteratedDerivWithin_zero_fun_all {s : Set ℝ} {n : ℕ} :
    ∀ x, iteratedDerivWithin n (fun _ => (0 : ℝ)) s x = 0 := by
  intro x
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDerivWithin_succ]
    have : iteratedDerivWithin n (fun _ => (0 : ℝ)) s = 0 := funext ih
    rw [this]
    simp

lemma iteratedDeriv_expNegInvGlue_nonpos :
    ∀ (n : ℕ) {x : ℝ}, x ≤ 0 → iteratedDeriv n expNegInvGlue x = 0 := by
  intro n
  induction n with
  | zero => exact expNegInvGlue.zero_of_nonpos
  | succ n hn =>
    intro x hx
    simp only [iteratedDeriv_succ]
    rcases hx.lt_or_eq with hxlt | rfl
    · -- x < 0: deriv is 0 on open set where function is constant
      have heq : Set.EqOn (iteratedDeriv n expNegInvGlue) (fun _ => 0) (Set.Iio 0) :=
        fun _ hy => hn hy.le
      simpa using Set.EqOn.deriv heq isOpen_Iio hxlt
    · -- x = 0: use limit argument
      have hconst := slope_zero_of_left_const fun y hy => (hn hy).trans (hn le_rfl).symm
      have hDiff : HasDerivAt (iteratedDeriv n expNegInvGlue) (deriv (iteratedDeriv n expNegInvGlue) 0) 0 :=
        ((expNegInvGlue.contDiff.of_le (by exact_mod_cast le_top)).differentiable_iteratedDeriv' (m := n) 0).hasDerivAt
      have hNeBot : NeBot (𝓝[Set.Iio 0] (0 : ℝ)) :=
        mem_closure_iff_nhdsWithin_neBot.mp (by simp [closure_Iio])
      exact tendsto_nhds_unique
        (hDiff.tendsto_slope.mono_left (nhdsWithin_mono _ fun _ h => h.ne))
        (tendsto_const_nhds.congr' hconst.symm)

lemma iteratedDeriv_expNegInvGlue_zero (n : ℕ) :
    iteratedDeriv n expNegInvGlue 0 = 0 :=
  iteratedDeriv_expNegInvGlue_nonpos n le_rfl

lemma iteratedDeriv_comp_expNegInvGlue_at
    {denom : ℝ → ℝ} (hdenom : ContDiff ℝ ∞ denom)
    {a : ℝ} (ha : denom a = 0) :
    ∀ n : ℕ, iteratedDeriv n (fun t => expNegInvGlue (denom t)) a = 0 := by
  classical
  intro n
  have hsum := iteratedDeriv_comp_eq_sum_orderedFinpartition (n := (⊤ : ℕ∞)) (i := n)
    (hi := by exact_mod_cast le_top) (g := expNegInvGlue) (f := denom) (x := a)
    (hg := expNegInvGlue.contDiff.contDiffAt) (hf := hdenom.contDiffAt)
  simp only [ha, iteratedDeriv_expNegInvGlue_zero, zero_mul, Finset.sum_const_zero] at hsum
  exact hsum

-- G = expNegInvGlue ∘ denom vanishes when denom ≤ 0
lemma expNegInvGlue_comp_vanish_of_nonpos
    {denom : ℝ → ℝ} (hdenom_nonpos : ∀ x, x ≤ 0 → denom x ≤ 0) :
    ∀ x, x ≤ 0 → expNegInvGlue (denom x) = 0 := fun x hx =>
  expNegInvGlue.zero_of_nonpos (hdenom_nonpos x hx)

lemma expNegInvGlue_comp_vanish_of_one_le
    {denom : ℝ → ℝ} (hdenom_nonpos : ∀ x, 1 ≤ x → denom x ≤ 0) :
    ∀ x, 1 ≤ x → expNegInvGlue (denom x) = 0 := fun x hx =>
  expNegInvGlue.zero_of_nonpos (hdenom_nonpos x hx)

-- Global derivative lemmas using iteratedDeriv instead of iteratedDerivWithin
lemma iteratedDeriv_shapeFn_vanishes_at_endpoint_expNegInvGlue_comp
    {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
    (hdenom_nonpos_left : ∀ x, x ≤ 0 → denom x ≤ 0)
    {a : ℝ} (ha_zero : denom a = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDeriv n (shapeFn (fun t => expNegInvGlue (denom t))) a = 0 := by
  let G := fun t => expNegInvGlue (denom t)
  have hG : ContDiff ℝ ∞ G := expNegInvGlue.contDiff.comp hdenom_contDiff
  have hG_vanish : ∀ x, x ≤ 0 → G x = 0 := expNegInvGlue_comp_vanish_of_nonpos hdenom_nonpos_left
  exact shapeFn_deriv_vanishes_at_point_global hG hG_vanish
    (by simp [G, ha_zero, expNegInvGlue.zero])
    (fun k _ => iteratedDeriv_comp_expNegInvGlue_at hdenom_contDiff ha_zero k)

-- General support bound: integral over Ioc 0 b equals integral over Ioc 0 1 when G vanishes on [1, ∞)
lemma integral_Ioc_eq_of_support_unit
    {G : ℝ → ℝ} (hint : IntervalIntegrable G volume 0 1)
    (hint' : IntervalIntegrable G volume 1 b)
    (hG_vanish : ∀ x, 1 ≤ x → G x = 0) (hb : 1 ≤ b) :
    ∫ t in Set.Ioc 0 b, G t = ∫ t in Set.Ioc 0 1, G t := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint hint'
  rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le (zero_le_one.trans hb),
      intervalIntegral.integral_of_le hb] at hsplit
  have hzero : ∫ x in Set.Ioc 1 b, G x = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => hG_vanish t ht.1.le
  linarith

-- When G vanishes on [1, ∞), shapeFnInt equals shapeFnConst for z ≥ 1
lemma shapeFnInt_eq_denom_of_one_le
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, 1 ≤ x → G x = 0) {z : ℝ} (hz : 1 ≤ z) :
    shapeFnInt G z = shapeFnConst G := by
  simp only [shapeFnInt, shapeFnConst]
  rw [Set.uIoc_of_le zero_le_one, Set.uIoc_of_le (zero_le_one.trans hz)]
  exact integral_Ioc_eq_of_support_unit
    (hG.continuous.intervalIntegrable 0 1)
    (hG.continuous.intervalIntegrable 1 z)
    hG_vanish hz

-- Global smoothness of shapeFn when G is globally C^∞ and vanishes on (-∞, 0]
lemma shape_fn_contDiff
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish_left : ∀ x, x ≤ 0 → G x = 0) :
    ContDiff ℝ ∞ (shapeFn G) :=
  (shape_numerator_contDiff hG hG_vanish_left).div_const _

lemma shapeFn_eq_zero_of_nonpos
    {G : ℝ → ℝ} (hG_vanish : ∀ x, x ≤ 0 → G x = 0) {z : ℝ} (hz : z ≤ 0) :
    shapeFn G z = 0 := by
  simp [shapeFn, shapeFnInt_eq_zero_of_nonpos hG_vanish hz]

lemma shapeFn_eq_one_of_one_le
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, 1 ≤ x → G x = 0)
    (hden : shapeFnConst G ≠ 0) {z : ℝ} (hz : 1 ≤ z) :
    shapeFn G z = 1 := by
  simp [shapeFn, shapeFnInt_eq_denom_of_one_le hG hG_vanish hz, hden]

lemma iteratedDeriv_shapeFn_vanishes_at_zero_expNegInvGlue_comp
    {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
    (hdenom_nonpos_left : ∀ x, x ≤ 0 → denom x ≤ 0)
    (hdenom_zero : denom 0 = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDeriv n (shapeFn (fun t => expNegInvGlue (denom t))) 0 = 0 :=
  iteratedDeriv_shapeFn_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff hdenom_nonpos_left hdenom_zero

lemma iteratedDeriv_shapeFn_vanishes_at_one_expNegInvGlue_comp
    {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
    (hdenom_nonpos_left : ∀ x, x ≤ 0 → denom x ≤ 0)
    (hdenom_one : denom 1 = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDeriv n (shapeFn (fun t => expNegInvGlue (denom t))) 1 = 0 :=
  iteratedDeriv_shapeFn_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff hdenom_nonpos_left hdenom_one

/-- Parameters describing a denominator suitable for the `expNegInvGlue ∘ denom` construction. -/
structure DenomParams where
  /-- The denominator function used inside `expNegInvGlue`. -/
  denom : ℝ → ℝ
  contDiff : ContDiff ℝ ∞ denom
  pos_on_Ioo : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < denom x
  zero : denom 0 = 0
  one : denom 1 = 0
  nonpos_of_nonpos : ∀ x, x ≤ 0 → denom x ≤ 0
  nonpos_of_one_le : ∀ x, 1 ≤ x → denom x ≤ 0

/-- Build a `SmoothstepCurve` from denominator-side hypotheses. -/
noncomputable def curveFrom (p : DenomParams) : SmoothstepCurve :=
  let G := fun t => expNegInvGlue (p.denom t)
  let hG : ContDiff ℝ ∞ G := expNegInvGlue.contDiff.comp p.contDiff
  let hG_vanish_left : ∀ x, x ≤ 0 → G x = 0 := expNegInvGlue_comp_vanish_of_nonpos p.nonpos_of_nonpos
  let hG_vanish_right : ∀ x, 1 ≤ x → G x = 0 := expNegInvGlue_comp_vanish_of_one_le p.nonpos_of_one_le
  let hfi : IntervalIntegrable G volume 0 1 := hG.continuous.intervalIntegrable 0 1
  let hden : 0 < shapeFnConst G := ShapeFnConst_pos hfi (fun x hx => expNegInvGlue.pos_of_pos (p.pos_on_Ioo x hx))
  mkSmoothstepCurveFromShape (shapeFn G)
    (shape_fn_contDiff hG hG_vanish_left)
    (shape_fn_zero_at_zero G)
    (shape_fn_one_at_one G hden.ne')
    (fun _z hz => shapeFn_eq_zero_of_nonpos hG_vanish_left hz)
    (fun _z hz => shapeFn_eq_one_of_one_le hG hG_vanish_right hden.ne' hz)
    (shapeFn_monotone_on_unit hG.contDiffOn (fun x hx => expNegInvGlue.pos_of_pos (p.pos_on_Ioo x hx)) hden)
    (iteratedDeriv_shapeFn_vanishes_at_zero_expNegInvGlue_comp p.contDiff p.nonpos_of_nonpos p.zero)
    (iteratedDeriv_shapeFn_vanishes_at_one_expNegInvGlue_comp p.contDiff p.nonpos_of_nonpos p.one)

end SmoothStepStructure

end Smooth

end GenericFramework
