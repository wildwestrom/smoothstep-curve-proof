import proofs.smoothstep_curve

/-
## Standard Smoothstep Curve

This section keeps the generic "parameterize by `G`" design but instantiates it
with the classical bump
```
G₁ z = expNegInvGlue (z * (1 - z)).
```
On the open interval `(0,1)` this coincides with `exp (-1 / (z (1 - z)))`, so it
is strictly positive there, integrates to a positive finite constant, and every
iterated derivative of `G₁` vanishes at `z = 0` and `z = 1`.  The exported shape
is still the normalized antiderivative `shapeFn G₁`, so downstream applications remain free
to swap in different bumps when tighter high-order derivative bounds are needed.
-/

section CanonicalSmoothstep

open scoped ContDiff Topology
open Smooth MeasureTheory

/-
### Canonical Smoothstep

Relies on `expNegInvGlue` to glue every derivative to zero at the endpoints.
-/

/-- The canonical denominator `z * (1 - z)`. -/
def denomCanonical (z : ℝ) : ℝ := z * (1 - z)

lemma denomCanonical_contDiff : ContDiff ℝ ∞ denomCanonical :=
  contDiff_id.mul (contDiff_const.sub contDiff_id)

lemma denomCanonical_pos_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    0 < denomCanonical t := by
  rcases ht with ⟨ht0, ht1⟩
  exact mul_pos ht0 (sub_pos.mpr ht1)

-- Canonical denominator vanishes at both endpoints
lemma denomCanonical_fn_zero : denomCanonical 0 = 0 := by simp [denomCanonical]
lemma denomCanonical_fn_one : denomCanonical 1 = 0 := by simp [denomCanonical]

-- Canonical denominator is nonpositive outside (0,1)
lemma denomCanonical_nonpos_of_nonpos : ∀ x, x ≤ 0 → denomCanonical x ≤ 0 := fun x hx => by
  simp only [denomCanonical]
  exact mul_nonpos_of_nonpos_of_nonneg hx (by linarith : 0 ≤ 1 - x)

lemma denomCanonical_nonpos_of_one_le : ∀ x, 1 ≤ x → denomCanonical x ≤ 0 := fun x hx => by
  simp only [denomCanonical]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ x) (by linarith : 1 - x ≤ 0)

-- Resulting bump vanishes at both endpoints
lemma G₁_zero : (fun t => expNegInvGlue (denomCanonical t)) 0 = 0 := by
  simp [denomCanonical_fn_zero, expNegInvGlue.zero_of_nonpos (le_refl 0)]

lemma G₁_one : (fun t => expNegInvGlue (denomCanonical t)) 1 = 0 := by
  simp [denomCanonical_fn_one, expNegInvGlue.zero_of_nonpos (le_refl 0)]

/-- Denominator parameters for the canonical smoothstep family. -/
def denomCanonicalParams : Smooth.DenomParams where
  denom := denomCanonical
  contDiff := denomCanonical_contDiff
  pos_on_Ioo := denomCanonical_pos_on_Ioo
  zero := denomCanonical_fn_zero
  one := denomCanonical_fn_one
  nonpos_of_nonpos := denomCanonical_nonpos_of_nonpos
  nonpos_of_one_le := denomCanonical_nonpos_of_one_le

/-- The canonical smoothstep curve built from `denomCanonical`. -/
noncomputable def curveCanonical : SmoothstepCurve :=
  Smooth.curveFrom denomCanonicalParams

end CanonicalSmoothstep

/-
## Parametric Families of Denominators
-/

section ParametricDenominators

open scoped ContDiff Topology
open Smooth MeasureTheory

variable (a : ℝ)

/-
Here we simply rescale the denominator with a single coefficient `a` and pick
```
G₂ z = expNegInvGlue (az(1 - z)),
```
for some positive parameter `a`. Inside `(0,1)` this behaves like
`exp (-1 / (a z (1 - z)))`, while `expNegInvGlue` glues the bump (and every derivative)
to zero at the endpoints. Normalizing the antiderivative once again gives the shape `shapeFn G₂`,
so the public API is unchanged even though this particular bump can yield smaller
jerk/snap bounds in practice.
-/

/-- A one-parameter scaling of the canonical denominator. -/
def denomScaled (z : ℝ) : ℝ := a * z * (1 - z)

lemma denomScaled_contDiff : ContDiff ℝ ∞ (denomScaled a) :=
  (contDiff_const.mul contDiff_id).mul (contDiff_const.sub contDiff_id)

lemma denomScaled_pos_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo 0 1) (ha : 0 < a) :
    0 < denomScaled a x := by
  rcases hx with ⟨hx0, hx1⟩
  have hx_pos : 0 < x := hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have : 0 < a * x * (1 - x) := by
    exact mul_pos (mul_pos ha hx_pos) h1x_pos
  simpa [denomScaled] using this

lemma denomScaled_zero : denomScaled a 0 = 0 := by
  simp [denomScaled]

lemma denomScaled_one : denomScaled a 1 = 0 := by
  simp [denomScaled]

lemma denomScaled_nonpos_of_nonpos (ha : 0 < a) : ∀ x, x ≤ 0 → denomScaled a x ≤ 0 := fun x hx => by
  simp only [denomScaled]
  have h1 : a * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hx
  exact mul_nonpos_of_nonpos_of_nonneg h1 (by linarith : 0 ≤ 1 - x)

lemma denomScaled_nonpos_of_one_le (ha : 0 < a) : ∀ x, 1 ≤ x → denomScaled a x ≤ 0 := fun x hx => by
  simp only [denomScaled]
  have h1 : 0 ≤ a * x := mul_nonneg ha.le (by linarith : 0 ≤ x)
  exact mul_nonpos_of_nonneg_of_nonpos h1 (by linarith : 1 - x ≤ 0)

/-- Denominator parameters for the scaled family. -/
def denomScaledParams (ha : 0 < a) : DenomParams where
  denom := denomScaled a
  contDiff := denomScaled_contDiff a
  pos_on_Ioo := fun {_} hx => denomScaled_pos_on_Ioo (a := a) hx ha
  zero := denomScaled_zero a
  one := denomScaled_one a
  nonpos_of_nonpos := denomScaled_nonpos_of_nonpos a ha
  nonpos_of_one_le := denomScaled_nonpos_of_one_le a ha

/-- The smoothstep curve induced by `denomScaled`. -/
noncomputable def curveScaled (ha : 0 < a) : SmoothstepCurve :=
  curveFrom (denomScaledParams a ha)

/-
Now we tweak it further by adding asymmetric powers of `p` and `q`
```
G(z) = expNegInvGlue (az^p(1 - z)^q)
```
-/

/-- A power-weighted denominator `a * z^p * (1 - z)^q`. -/
def denomPow (a : ℝ) (p q : ℕ) (z : ℝ) : ℝ :=
  a * z ^ p * (1 - z) ^ q

lemma denomPow_contDiff (a : ℝ) (p q : ℕ) : ContDiff ℝ ∞ (denomPow a p q) := by
  have hz_pow : ContDiff ℝ ∞ (fun z : ℝ => z ^ p) := by
    simpa using contDiff_id.pow p
  have h1_pow : ContDiff ℝ ∞ (fun z : ℝ => (1 - z) ^ q) := by
    simpa using (contDiff_const.sub contDiff_id).pow q
  have hconst : ContDiff ℝ ∞ (fun _ : ℝ => a) := contDiff_const
  have hprod := (hconst.mul hz_pow).mul h1_pow
  simpa [denomPow] using hprod

lemma denomPow_pos_on_Ioo {a : ℝ} {p q : ℕ} (ha : 0 < a) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomPow a p q x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hx_pos : 0 < x := hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have hz := pow_pos hx_pos p
  have h1z := pow_pos h1x_pos q
  exact mul_pos (mul_pos ha hz) h1z

lemma denomPow_zero {a : ℝ} {p q : ℕ} (hp : 0 < p) :
    denomPow a p q 0 = 0 := by
  cases p with
  | zero => cases hp
  | succ p' =>
      simp [denomPow]

lemma denomPow_one {a : ℝ} {p q : ℕ} (hq : 0 < q) :
    denomPow a p q 1 = 0 := by
  cases q with
  | zero => cases hq
  | succ q' =>
      simp [denomPow]

-- For nonpos_of_nonpos: z^p ≤ 0 when z ≤ 0 requires p odd
-- For nonpos_of_one_le: (1-z)^q ≤ 0 when z ≥ 1 requires q odd
lemma denomPow_nonpos_of_nonpos {a : ℝ} (ha : 0 < a) (p q : ℕ) (hp_odd : Odd p) :
    ∀ x, x ≤ 0 → denomPow a p q x ≤ 0 := by
  intro x hx
  simp only [denomPow]
  have hz_pow : x ^ p ≤ 0 := Odd.pow_nonpos hp_odd hx
  have h1z_pow : (0 : ℝ) < (1 - x) ^ q := pow_pos (by linarith : 0 < 1 - x) q
  have := mul_nonpos_of_nonneg_of_nonpos (mul_pos ha h1z_pow).le hz_pow
  linarith [this]

lemma denomPow_nonpos_of_one_le {a : ℝ} (ha : 0 < a) (p q : ℕ) (hq_odd : Odd q) :
    ∀ x, 1 ≤ x → denomPow a p q x ≤ 0 := by
  intro x hx
  simp only [denomPow]
  have hz_pow : (0 : ℝ) < x ^ p := pow_pos (by linarith : 0 < x) p
  have h1z_pow : (1 - x) ^ q ≤ 0 := Odd.pow_nonpos hq_odd (by linarith : 1 - x ≤ 0)
  have := mul_nonpos_of_nonneg_of_nonpos (mul_pos ha hz_pow).le h1z_pow
  linarith [this]

/-- Denominator parameters for the odd-power family. -/
def denomPowParams {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hp_odd : Odd p) (hq_odd : Odd q) :
    DenomParams where
  denom := denomPow a p q
  contDiff := denomPow_contDiff a p q
  pos_on_Ioo := denomPow_pos_on_Ioo (a := a) (p := p) (q := q) ha
  zero := denomPow_zero (a := a) (p := p) (q := q) hp
  one := denomPow_one (a := a) (p := p) (q := q) hq
  nonpos_of_nonpos := denomPow_nonpos_of_nonpos ha p q hp_odd
  nonpos_of_one_le := denomPow_nonpos_of_one_le ha p q hq_odd

/-- The smoothstep curve induced by `denomPow`. -/
noncomputable def curvePow {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hp_odd : Odd p) (hq_odd : Odd q) :
    SmoothstepCurve :=
  curveFrom (denomPowParams (a := a) (p := p) (q := q) ha hp hq hp_odd hq_odd)

/-
Polynomial bump denominator with an affine skew term
-/

/-- A cubic denominator with an affine skew factor. -/
def denomPoly (α β : ℝ) (z : ℝ) : ℝ :=
  (z * (1 - z)) * (α + β * z)

lemma denomPoly_contDiff (α β : ℝ) : ContDiff ℝ ∞ (denomPoly α β) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ => z * (1 - z)) := by
    simpa [denomCanonical] using denomCanonical_contDiff
  have h2 : ContDiff ℝ ∞ (fun z : ℝ => α + β * z) :=
    (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hprod :
      ContDiff ℝ ∞ (fun z : ℝ => (z * (1 - z)) * (α + β * z)) :=
    h1.mul h2
  simpa [denomPoly] using hprod

lemma denomPoly_pos_on_Ioo {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomPoly α β x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hbase : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
  have hβx : 0 ≤ β * x := mul_nonneg hβ hx0.le
  have hlin : 0 < α + β * x := by
    have hαle : α ≤ α + β * x := by
      have := add_le_add_left hβx α
      simpa using this
    exact lt_of_lt_of_le hα hαle
  have := mul_pos hbase hlin
  simpa [denomPoly] using this

lemma denomPoly_zero (α β : ℝ) : denomPoly α β 0 = 0 := by
  simp [denomPoly]

lemma denomPoly_one (α β : ℝ) : denomPoly α β 1 = 0 := by
  simp [denomPoly]

-- For global smoothness, we need denomPoly nonpositive outside (0,1).
-- This requires β = 0 (otherwise for large negative z, the sign is wrong).
-- When β = 0: denomPoly α 0 z = α * z(1-z), same as denomScaled α.
lemma denomPoly_nonpos_of_nonpos {α : ℝ} (hα : 0 < α) :
    ∀ x, x ≤ 0 → denomPoly α 0 x ≤ 0 := by
  intro x hx
  simp only [denomPoly]
  have h1 : x * (1 - x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx (by linarith : 0 ≤ 1 - x)
  have h2 : 0 ≤ α + 0 * x := by simp [hα.le]
  exact mul_nonpos_of_nonpos_of_nonneg h1 h2

lemma denomPoly_nonpos_of_one_le {α : ℝ} (hα : 0 < α) :
    ∀ x, 1 ≤ x → denomPoly α 0 x ≤ 0 := by
  intro x hx
  simp only [denomPoly]
  have h1 : x * (1 - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ x) (by linarith : 1 - x ≤ 0)
  have h2 : 0 ≤ α + 0 * x := by simp [hα.le]
  exact mul_nonpos_of_nonpos_of_nonneg h1 h2

lemma denomPoly_pos_left_witness {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ x, x ≤ 0 ∧ 0 < denomPoly α β x := by
  refine ⟨-(α / β) - 1, ?_, ?_⟩
  · have : -(α / β) < 0 := by
      have hdiv : 0 < α / β := div_pos hα hβ
      linarith
    linarith
  · have hx : -(α / β) - 1 < 0 := by
      have : -(α / β) < 0 := by
        have hdiv : 0 < α / β := div_pos hα hβ
        linarith
      linarith
    have hbase : (-(α / β) - 1) * (1 - (-(α / β) - 1)) < 0 := by
      have h1 : 0 < 1 - (-(α / β) - 1) := by linarith
      exact mul_neg_of_neg_of_pos hx h1
    have hlin : α + β * (-(α / β) - 1) < 0 := by
      have hcalc : α + β * (-(α / β) - 1) = -β := by
        field_simp [hβ.ne']
        linarith
      rw [hcalc]
      linarith
    have : 0 < (-(α / β) - 1) * (1 - (-(α / β) - 1)) * (α + β * (-(α / β) - 1)) :=
      mul_pos_of_neg_of_neg hbase hlin
    simpa [denomPoly] using this

lemma denomPoly_pos_right_witness {α β : ℝ} (hα : 0 < α) (hβ : β < 0) :
    ∃ x, 1 ≤ x ∧ 0 < denomPoly α β x := by
  refine ⟨α / (-β) + 1, ?_, ?_⟩
  · have : 0 ≤ α / (-β) := div_nonneg hα.le (neg_nonneg.mpr hβ.le)
    linarith
  · have hx : 1 < α / (-β) + 1 := by
      have : 0 < α / (-β) := div_pos hα (neg_pos.mpr hβ)
      linarith
    have hbase : (α / (-β) + 1) * (1 - (α / (-β) + 1)) < 0 := by
      have hxpos : 0 < α / (-β) + 1 := by linarith
      have h1 : 1 - (α / (-β) + 1) < 0 := by linarith
      exact mul_neg_of_pos_of_neg hxpos h1
    have hlin : α + β * (α / (-β) + 1) < 0 := by
      have hdiv : α / (-β) = -(α / β) := by
        field_simp [hβ.ne']
      rw [hdiv]
      have hcancel : β * (α / β) = α := by
        field_simp [hβ.ne']
        rw [div_self (ne_of_lt hβ)]
      have hcalc : β * (-(α / β)) = -α := by
        nlinarith
      nlinarith [hcalc, hβ]
    have : 0 < (α / (-β) + 1) * (1 - (α / (-β) + 1)) * (α + β * (α / (-β) + 1)) :=
      mul_pos_of_neg_of_neg hbase hlin
    simpa [denomPoly] using this

lemma denomPoly_beta_eq_zero_of_global_nonpos {α β : ℝ} (hα : 0 < α)
    (hleft : ∀ x, x ≤ 0 → denomPoly α β x ≤ 0)
    (hright : ∀ x, 1 ≤ x → denomPoly α β x ≤ 0) :
    β = 0 := by
  by_contra hβ
  rcases lt_or_gt_of_ne hβ with hβ_neg | hβ_pos
  · rcases denomPoly_pos_right_witness hα hβ_neg with ⟨x, hx, hx_pos⟩
    exact (not_lt_of_ge (hright x hx)) hx_pos
  · rcases denomPoly_pos_left_witness hα hβ_pos with ⟨x, hx, hx_pos⟩
    exact (not_lt_of_ge (hleft x hx)) hx_pos

/-- Denominator parameters for the globally valid `β = 0` polynomial family. -/
def denomPolyParams {α : ℝ} (hα : 0 < α) : DenomParams where
  denom := denomPoly α 0
  contDiff := denomPoly_contDiff α 0
  pos_on_Ioo := denomPoly_pos_on_Ioo hα le_rfl
  zero := denomPoly_zero α 0
  one := denomPoly_one α 0
  nonpos_of_nonpos := denomPoly_nonpos_of_nonpos hα
  nonpos_of_one_le := denomPoly_nonpos_of_one_le hα

/-- The globally valid polynomial family, necessarily using `β = 0`. -/
noncomputable def curvePoly {α : ℝ} (hα : 0 < α) : SmoothstepCurve :=
  curveFrom (denomPolyParams (α := α) hα)

end ParametricDenominators

section AsymmetricDenominators

open scoped ContDiff Topology
open Smooth MeasureTheory

/-- A globally valid asymmetric denominator obtained by modulating `denomCanonical`
with the canonical shape function. -/
noncomputable def denomSkewed (α β : ℝ) (z : ℝ) : ℝ :=
  denomCanonical z * (α + β * curveCanonical.shapeFn z)

lemma denomSkewed_contDiff (α β : ℝ) : ContDiff ℝ ∞ (denomSkewed α β) := by
  refine denomCanonical_contDiff.mul ?_
  exact contDiff_const.add (contDiff_const.mul curveCanonical.shapeFn_is_C_inf)

lemma denomSkewed_pos_on_Ioo {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomSkewed α β x := by
  intro x hx
  have hbase : 0 < denomCanonical x := denomCanonical_pos_on_Ioo x hx
  have hxshapeFn : curveCanonical.shapeFn x ∈ unitInterval := curveCanonical.shapeFn_mem_unitInterval' ⟨hx.1.le, hx.2.le⟩
  have hβshapeFn : 0 ≤ β * curveCanonical.shapeFn x := mul_nonneg hβ hxshapeFn.1
  have hlin : 0 < α + β * curveCanonical.shapeFn x := by
    have hαle : α ≤ α + β * curveCanonical.shapeFn x := by
      have := add_le_add_left hβshapeFn α
      simpa using this
    exact lt_of_lt_of_le hα hαle
  exact mul_pos hbase hlin

lemma denomSkewed_zero (α β : ℝ) : denomSkewed α β 0 = 0 := by
  simp [denomSkewed, denomCanonical]

lemma denomSkewed_one (α β : ℝ) : denomSkewed α β 1 = 0 := by
  simp [denomSkewed, denomCanonical]

lemma denomSkewed_nonpos_of_nonpos {α β : ℝ} (hα : 0 < α) :
    ∀ x, x ≤ 0 → denomSkewed α β x ≤ 0 := by
  intro x hx
  rw [denomSkewed]
  have hbase : denomCanonical x ≤ 0 := denomCanonical_nonpos_of_nonpos x hx
  have hlin : 0 ≤ α + β * curveCanonical.shapeFn x := by
    rw [curveCanonical.shapeFn_eq_zero_of_nonpos x hx]
    simpa using hα.le
  exact mul_nonpos_of_nonpos_of_nonneg hbase hlin

lemma denomSkewed_nonpos_of_one_le {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ x, 1 ≤ x → denomSkewed α β x ≤ 0 := by
  intro x hx
  rw [denomSkewed]
  have hbase : denomCanonical x ≤ 0 := denomCanonical_nonpos_of_one_le x hx
  have hlin : 0 ≤ α + β * curveCanonical.shapeFn x := by
    rw [curveCanonical.shapeFn_eq_one_of_one_le x hx]
    linarith
  exact mul_nonpos_of_nonpos_of_nonneg hbase hlin

/-- Denominator parameters for the asymmetric smoothstep family. -/
noncomputable def denomSkewedParams {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : DenomParams where
  denom := denomSkewed α β
  contDiff := denomSkewed_contDiff α β
  pos_on_Ioo := denomSkewed_pos_on_Ioo hα hβ
  zero := denomSkewed_zero α β
  one := denomSkewed_one α β
  nonpos_of_nonpos := denomSkewed_nonpos_of_nonpos hα
  nonpos_of_one_le := denomSkewed_nonpos_of_one_le hα hβ

/-- A globally smooth asymmetric family built from `denomSkewed`. -/
noncomputable def curveSkewed {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : SmoothstepCurve :=
  curveFrom (denomSkewedParams (α := α) (β := β) hα hβ)

end AsymmetricDenominators

section ClosureProperties

open scoped ContDiff Topology
open Smooth

namespace Smooth

lemma SmoothstepCurve.curvature_deriv_vanishes_at_zero
    (sc : SmoothstepCurve) (R₁ R₂ L : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => sc.curvature s R₁ R₂ L) 0 = 0 := by
  simpa [sc.curvature_formula] using
    (curvatureOfShape_deriv_vanishes_at_zero sc.shapeFn_is_C_inf sc.shapeFn_deriv_vanishes_at_zero R₁ R₂ L n hn)

lemma SmoothstepCurve.curvature_deriv_vanishes_at_L
    (sc : SmoothstepCurve) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => sc.curvature s R₁ R₂ L) L = 0 := by
  simpa [sc.curvature_formula] using
    (curvatureOfShape_deriv_vanishes_at_L sc.shapeFn_is_C_inf sc.shapeFn_deriv_vanishes_at_one R₁ R₂ L hL n hn)

lemma SmoothstepCurve.curvature_eq_start_of_nonpos
    (sc : SmoothstepCurve) (R₁ R₂ L s : ℝ) (hL : 0 < L) (hs : s ≤ 0) :
    sc.curvature s R₁ R₂ L = R₁ := by
  rw [sc.curvature_formula]
  have hs_div : s / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs hL.le
  simp [sc.shapeFn_eq_zero_of_nonpos _ hs_div]

lemma SmoothstepCurve.curvature_eq_end_of_ge_L
    (sc : SmoothstepCurve) (R₁ R₂ L s : ℝ) (hL : 0 < L) (hs : L ≤ s) :
    sc.curvature s R₁ R₂ L = R₂ := by
  rw [sc.curvature_formula]
  have hs_div : 1 ≤ s / L := by
    simpa [div_self hL.ne'] using div_le_div_of_nonneg_right hs hL.le
  simp [sc.shapeFn_eq_one_of_one_le _ hs_div]

lemma iteratedDeriv_comp_vanish_of_flat
    {g φ : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hφ : ContDiff ℝ ∞ φ)
    {a : ℝ} (hflat : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n φ a = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDeriv n (fun z => g (φ z)) a = 0 := by
  intro n hn
  have hsum := iteratedDeriv_comp_eq_sum_orderedFinpartition (n := (⊤ : ℕ∞)) (i := n)
    (hi := by exact_mod_cast le_top) (g := g) (f := φ) (x := a)
    (hg := hg.contDiffAt) (hf := hφ.contDiffAt)
  have hparts :
      ∀ c : OrderedFinpartition n,
        ∏ j : Fin c.length, iteratedDeriv (c.partSize j) φ a = 0 := by
    intro c
    have hlen : 0 < c.length := c.length_pos (Nat.one_le_iff_ne_zero.mp hn).bot_lt
    have hprod :
        ((Finset.univ : Finset (Fin c.length)).prod fun j =>
            iteratedDeriv (c.partSize j) φ a : ℝ) = 0 := by
      refine Finset.prod_eq_zero
        (s := (Finset.univ : Finset (Fin c.length)))
        (f := fun j => iteratedDeriv (c.partSize j) φ a)
        (i := ⟨0, hlen⟩) ?_ ?_
      · simp
      · exact hflat _ (Nat.succ_le_of_lt (c.partSize_pos ⟨0, hlen⟩))
    simpa using hprod
  have hsum_zero :
      ∑ c : OrderedFinpartition n,
        iteratedDeriv c.length g (φ a) * ∏ j : Fin c.length, iteratedDeriv (c.partSize j) φ a = 0 := by
    refine Finset.sum_eq_zero ?_
    intro c _
    simp [hparts c]
  simpa using hsum.trans hsum_zero

/-- Convex combination of two shape functions. -/
def mixShape (t : ℝ) (shapeFn₁ shapeFn₂ : ℝ → ℝ) : ℝ → ℝ :=
  fun z => t * shapeFn₁ z + (1 - t) * shapeFn₂ z

lemma iteratedDeriv_mixShape
    {shapeFn₁ shapeFn₂ : ℝ → ℝ} (hshapeFn₁ : ContDiff ℝ ∞ shapeFn₁) (hshapeFn₂ : ContDiff ℝ ∞ shapeFn₂)
    (t x : ℝ) (n : ℕ) :
    iteratedDeriv n (mixShape t shapeFn₁ shapeFn₂) x =
      t * iteratedDeriv n shapeFn₁ x + (1 - t) * iteratedDeriv n shapeFn₂ x := by
  have h₁ : ContDiffAt ℝ n (fun z => t * shapeFn₁ z) x :=
    (contDiff_const.mul hshapeFn₁).contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  have h₂ : ContDiffAt ℝ n (fun z => (1 - t) * shapeFn₂ z) x :=
    (contDiff_const.mul hshapeFn₂).contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  rw [show mixShape t shapeFn₁ shapeFn₂ = (fun z => t * shapeFn₁ z) + (fun z => (1 - t) * shapeFn₂ z) by rfl]
  rw [iteratedDeriv_add h₁ h₂, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]

/-- Reparametrize a smoothstep curve by a globally smooth map with the same flat endpoints. -/
noncomputable def reparam (base : SmoothstepCurve) (φ : ℝ → ℝ)
    (hφ_smooth : ContDiff ℝ ∞ φ)
    (hφ_zero_of_nonpos : ∀ z, z ≤ 0 → φ z = 0)
    (hφ_one_of_one_le : ∀ z, 1 ≤ z → φ z = 1)
    (hφ_mem : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → φ z ∈ unitInterval)
    (hφ_mono : MonotoneOn φ unitInterval)
    (hφ_flat_zero : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n φ 0 = 0)
    (hφ_flat_one : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n φ 1 = 0) :
    SmoothstepCurve :=
  mkSmoothstepCurveFromShape
    (fun z => base.shapeFn (φ z))
    (base.shapeFn_is_C_inf.comp hφ_smooth)
    (by simp [hφ_zero_of_nonpos 0 le_rfl, base.shapeFn_zero])
    (by simp [hφ_one_of_one_le 1 le_rfl, base.shapeFn_one])
    (fun z hz => by simpa [hφ_zero_of_nonpos z hz] using base.shapeFn_zero)
    (fun z hz => by simpa [hφ_one_of_one_le z hz] using base.shapeFn_one)
    (fun _ hx _ hy hxy => base.shapeFn_monotone_on_unit (hφ_mem hx) (hφ_mem hy) (hφ_mono hx hy hxy))
    (fun n hn => by
      simpa using iteratedDeriv_comp_vanish_of_flat base.shapeFn_is_C_inf hφ_smooth hφ_flat_zero n hn)
    (fun n hn => by
      simpa using iteratedDeriv_comp_vanish_of_flat base.shapeFn_is_C_inf hφ_smooth hφ_flat_one n hn)

/-- Convexly mix two smoothstep curves. -/
noncomputable def mixCurve (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (c₁ c₂ : SmoothstepCurve) : SmoothstepCurve :=
  mkSmoothstepCurveFromShape
    (mixShape t c₁.shapeFn c₂.shapeFn)
    ((contDiff_const.mul c₁.shapeFn_is_C_inf).add (contDiff_const.mul c₂.shapeFn_is_C_inf))
    (by simp [mixShape, c₁.shapeFn_zero, c₂.shapeFn_zero])
    (by simp [mixShape, c₁.shapeFn_one, c₂.shapeFn_one, sub_eq_add_neg])
    (fun z hz => by simp [mixShape, c₁.shapeFn_eq_zero_of_nonpos z hz, c₂.shapeFn_eq_zero_of_nonpos z hz])
    (fun z hz => by simp [mixShape, c₁.shapeFn_eq_one_of_one_le z hz, c₂.shapeFn_eq_one_of_one_le z hz, sub_eq_add_neg])
    (fun _ hx _ hy hxy => by
      have h₁ := c₁.shapeFn_monotone_on_unit hx hy hxy
      have h₂ := c₂.shapeFn_monotone_on_unit hx hy hxy
      have ht0 : 0 ≤ t := ht.1
      have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      exact add_le_add
        (mul_le_mul_of_nonneg_left h₁ ht0)
        (mul_le_mul_of_nonneg_left h₂ ht1))
    (fun n hn => by
      rw [iteratedDeriv_mixShape c₁.shapeFn_is_C_inf c₂.shapeFn_is_C_inf t 0 n]
      simp [c₁.shapeFn_deriv_vanishes_at_zero n hn, c₂.shapeFn_deriv_vanishes_at_zero n hn])
    (fun n hn => by
      rw [iteratedDeriv_mixShape c₁.shapeFn_is_C_inf c₂.shapeFn_is_C_inf t 1 n]
      simp [c₁.shapeFn_deriv_vanishes_at_one n hn, c₂.shapeFn_deriv_vanishes_at_one n hn])

/-- Concatenate two curvature transitions with a shared middle curvature `R₁`. -/
noncomputable def concat (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ : ℝ) : ℝ → ℝ :=
  fun s => sc₁.curvature s R₀ R₁ L₁ + sc₂.curvature (s - L₁) R₁ R₂ L₂ - R₁

lemma concat_contDiff (sc₁ sc₂ : SmoothstepCurve) (R₀ R₁ R₂ L₁ L₂ : ℝ) :
    ContDiff ℝ ∞ (concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂) := by
  unfold concat
  have hshift : ContDiff ℝ ∞ (fun s => sc₂.curvature (s - L₁) R₁ R₂ L₂) := by
    simpa [sub_eq_add_neg] using
      (sc₂.curvature_is_C_inf R₁ R₂ L₂).comp (contDiff_id.add (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => -L₁))
  have hsum :=
    (sc₁.curvature_is_C_inf R₀ R₁ L₁).add hshift
  exact hsum.sub contDiff_const

lemma concat_eq_first_of_le_join (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ s : ℝ) (hL₂ : 0 < L₂) (hs : s ≤ L₁) :
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ s = sc₁.curvature s R₀ R₁ L₁ := by
  unfold concat
  rw [sc₂.curvature_eq_start_of_nonpos R₁ R₂ L₂ (s - L₁) hL₂ (by linarith)]
  ring

lemma concat_eq_shifted_second_of_join_le (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ s : ℝ) (hL₁ : 0 < L₁) (hs : L₁ ≤ s) :
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ s = sc₂.curvature (s - L₁) R₁ R₂ L₂ := by
  unfold concat
  rw [sc₁.curvature_eq_end_of_ge_L R₀ R₁ L₁ s hL₁ hs]
  ring

lemma concat_at_join (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ : ℝ) (hL₁ : L₁ ≠ 0) :
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ L₁ = R₁ := by
  calc
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ L₁
        = sc₁.curvature L₁ R₀ R₁ L₁ + sc₂.curvature 0 R₁ R₂ L₂ - R₁ := by
            simp [concat]
    _ = R₁ := by
      rw [sc₁.curvature_formula, sc₂.curvature_formula]
      simp [sc₂.shapeFn_zero, div_self hL₁, sc₁.shapeFn_one]

lemma concat_deriv_vanishes_at_join (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ : ℝ) (hL₁ : L₁ ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂) L₁ = 0 := by
  have h₁ : ContDiffAt ℝ n (fun s => sc₁.curvature s R₀ R₁ L₁) L₁ :=
    (sc₁.curvature_is_C_inf R₀ R₁ L₁).contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  have h₂ : ContDiffAt ℝ n (fun s => sc₂.curvature (s - L₁) R₁ R₂ L₂) L₁ :=
    (by
      have hshift : ContDiff ℝ ∞ (fun s => sc₂.curvature (s - L₁) R₁ R₂ L₂) := by
        simpa [sub_eq_add_neg] using
          (sc₂.curvature_is_C_inf R₁ R₂ L₂).comp (contDiff_id.add (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => -L₁))
      exact hshift.contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞))))
  have hsum : ContDiffAt ℝ n ((fun s => sc₁.curvature s R₀ R₁ L₁) + fun s => sc₂.curvature (s - L₁) R₁ R₂ L₂) L₁ :=
    h₁.add h₂
  have hconst : ContDiffAt ℝ n (fun _ : ℝ => R₁) L₁ :=
    (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => R₁).contDiffAt.of_le
      (by exact_mod_cast le_top (a := (n : ℕ∞)))
  rw [show concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ =
      ((fun s => sc₁.curvature s R₀ R₁ L₁) + fun s => sc₂.curvature (s - L₁) R₁ R₂ L₂) - fun _ => R₁ by
        rfl]
  rw [iteratedDeriv_sub hsum hconst, iteratedDeriv_add h₁ h₂, iteratedDeriv_const,
    if_neg (Nat.one_le_iff_ne_zero.mp hn)]
  have hleft : iteratedDeriv n (fun s => sc₁.curvature s R₀ R₁ L₁) L₁ = 0 :=
    sc₁.curvature_deriv_vanishes_at_L R₀ R₁ L₁ hL₁ n hn
  have hright_shift :
      iteratedDeriv n (fun s => sc₂.curvature (s - L₁) R₁ R₂ L₂) L₁ =
        iteratedDeriv n (fun s => sc₂.curvature s R₁ R₂ L₂) (L₁ - L₁) := by
    simpa using congrArg (fun f => f L₁) (iteratedDeriv_comp_sub_const n
      (fun s => sc₂.curvature s R₁ R₂ L₂) L₁)
  rw [hleft, hright_shift, sub_self]
  simp [sc₂.curvature_deriv_vanishes_at_zero R₁ R₂ L₂ n hn]

end Smooth

end ClosureProperties
