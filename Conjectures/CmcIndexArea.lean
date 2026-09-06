import Mathlib

/-!
# A Positively Curved Counterexample to a CMC Index–Area Bound

Lean certification of the computational content of
`cmc_index_area_counterexample.tex`.

The paper fixes `a ∈ (0,1)` and considers the rotationally symmetric metric
`g = dr² + f(r)² g_{S²}` on `ℝ³` with warping function
`f(r) = r (1+r²)^((a-1)/2)` (eq. `eq:warping`/`eq:metric`).  Everything the
paper actually computes — the derivatives of `f`, the sign and pole values of
the sectional curvatures, the areas and mean curvatures of the coordinate
spheres `Σ_R = {r = R}`, the constant Jacobi potential, the full Jacobi
spectrum, the index/nullity count, and the divergence of
`(1+h²)·Area` while `index + nullity ≡ 1` — is formalized and proved below.

Genuinely geometric facts that Mathlib cannot express (that `-f''/f` and
`(1-(f')²)/f²` *are* the sectional curvatures of the warped metric, that
`|A|² = 2(f'/f)²` and `Ric(ν,ν) = -2 f''/f` on a coordinate sphere, that the
spectrum of `-Δ` on a round 2-sphere of radius `f(R)` is `ℓ(ℓ+1)/f(R)²` with
multiplicity `2ℓ+1`) enter as *definitions* (`Krad`, `Ktan`, `jacobiEig`,
`sphIndex`, `sphNullity`), each documented with the tex formula it encodes;
all subsequent reasoning about them is fully proved.
-/

namespace CmcIndexArea

open Real Filter Topology

noncomputable section

/-! ## The warped-product model (tex §2) -/

/-- The warping function `f(r) = r (1+r²)^((a-1)/2)` (tex eq. `eq:warping`). -/
def f (a r : ℝ) : ℝ := r * (1 + r ^ 2) ^ ((a - 1) / 2)

/-- The claimed first derivative `f'(r) = (1+r²)^((a-3)/2) (1+ar²)`
(tex eq. `eq:fp`). -/
def fp (a r : ℝ) : ℝ := (1 + r ^ 2) ^ ((a - 3) / 2) * (1 + a * r ^ 2)

/-- The claimed second derivative
`f''(r) = (a-1) r (1+r²)^((a-5)/2) (3+ar²)` (tex eq. `eq:fpp`). -/
def fpp (a r : ℝ) : ℝ := (a - 1) * r * (1 + r ^ 2) ^ ((a - 5) / 2) * (3 + a * r ^ 2)

/-- Radial sectional curvature `K_rad = -f''/f` of the rotational metric
(standard warped-product formula, tex Lemma 2 proof). -/
def Krad (a r : ℝ) : ℝ := -fpp a r / f a r

/-- Tangential sectional curvature `K_tan = (1-(f')²)/f²` of the rotational
metric (standard warped-product formula, tex Lemma 2 proof). -/
def Ktan (a r : ℝ) : ℝ := (1 - fp a r ^ 2) / f a r ^ 2

/-- `Area(Σ_R) = 4π f(R)²` (tex eq. `eq:area-h`). -/
def area (a r : ℝ) : ℝ := 4 * Real.pi * f a r ^ 2

/-- Mean curvature `h_R = 2 f'(R)/f(R)` of the coordinate sphere
(tex eq. `eq:area-h`). -/
def hmean (a r : ℝ) : ℝ := 2 * fp a r / f a r

/-- `S(R) = 2 (f'(R)² - f(R) f''(R))` (tex eq. `eq:spectrum`). -/
def S (a r : ℝ) : ℝ := 2 * (fp a r ^ 2 - f a r * fpp a r)

/-- The `ℓ`-th Jacobi eigenvalue `λ_ℓ = (ℓ(ℓ+1) - S(R))/f(R)²`
(tex eq. `eq:spectrum`); it carries multiplicity `2ℓ+1`. -/
def jacobiEig (a r : ℝ) (ℓ : ℕ) : ℝ := ((ℓ : ℝ) * (ℓ + 1) - S a r) / f a r ^ 2

/-- Strong Morse index of `Σ_R`: number of negative Jacobi eigenvalues counted
with multiplicity `2ℓ+1` (tex Lemma 3). -/
def sphIndex (a r : ℝ) : ℕ := ∑' ℓ : ℕ, if jacobiEig a r ℓ < 0 then 2 * ℓ + 1 else 0

/-- Nullity of `Σ_R`: number of zero Jacobi eigenvalues counted with
multiplicity (tex Lemma 3). -/
def sphNullity (a r : ℝ) : ℕ := ∑' ℓ : ℕ, if jacobiEig a r ℓ = 0 then 2 * ℓ + 1 else 0

/-- The coordinate spheres are embedded 2-spheres, so their genus is `0`. -/
def genus : ℝ := 0

/-! ## Derivatives of the warping function (tex eqs. `eq:fp`, `eq:fpp`) -/

/-- Helper: `(X^(c/2))² = X^c` for `X > 0`. -/
theorem rpow_half_sq {X : ℝ} (hX : 0 < X) (c : ℝ) : (X ^ (c / 2)) ^ 2 = X ^ c := by
  rw [← Real.rpow_natCast (X ^ (c / 2)) 2, ← Real.rpow_mul hX.le]
  norm_num

/-- Certifies tex eq. `eq:fp`: `fp` really is the derivative of `f`. -/
theorem hasDerivAt_f (a r : ℝ) : HasDerivAt (f a) (fp a r) r := by
  have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add 1
  have h2 : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ ((a - 1) / 2))
      (2 * r * ((a - 1) / 2) * (1 + r ^ 2) ^ ((a - 1) / 2 - 1)) r :=
    h1.rpow_const (Or.inl hb.ne')
  have h3 := (hasDerivAt_id r).mul h2
  have e1 : (1 + r ^ 2 : ℝ) ^ ((a - 1) / 2) = (1 + r ^ 2) ^ ((a - 3) / 2) * (1 + r ^ 2) := by
    rw [show (a - 1) / 2 = (a - 3) / 2 + 1 by ring, Real.rpow_add hb, Real.rpow_one]
  have key : 1 * (1 + r ^ 2) ^ ((a - 1) / 2)
      + id r * (2 * r * ((a - 1) / 2) * (1 + r ^ 2) ^ ((a - 1) / 2 - 1)) = fp a r := by
    rw [show (a - 1) / 2 - 1 = (a - 3) / 2 by ring, e1]
    unfold fp
    simp only [id]
    ring
  exact key ▸ h3

/-- Certifies tex eq. `eq:fpp`: `fpp` really is the derivative of `fp`. -/
theorem hasDerivAt_fp (a r : ℝ) : HasDerivAt (fp a) (fpp a r) r := by
  have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add 1
  have h2 : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ ((a - 3) / 2))
      (2 * r * ((a - 3) / 2) * (1 + r ^ 2) ^ ((a - 3) / 2 - 1)) r :=
    h1.rpow_const (Or.inl hb.ne')
  have h3 : HasDerivAt (fun s : ℝ => 1 + a * s ^ 2) (a * (2 * r)) r := by
    simpa using ((hasDerivAt_pow 2 r).const_mul a).const_add 1
  have h4 := h2.mul h3
  have e1 : (1 + r ^ 2 : ℝ) ^ ((a - 3) / 2) = (1 + r ^ 2) ^ ((a - 5) / 2) * (1 + r ^ 2) := by
    rw [show (a - 3) / 2 = (a - 5) / 2 + 1 by ring, Real.rpow_add hb, Real.rpow_one]
  have key : 2 * r * ((a - 3) / 2) * (1 + r ^ 2) ^ ((a - 3) / 2 - 1) * (1 + a * r ^ 2)
      + (1 + r ^ 2) ^ ((a - 3) / 2) * (a * (2 * r)) = fpp a r := by
    rw [show (a - 3) / 2 - 1 = (a - 5) / 2 by ring, e1]
    unfold fpp
    ring
  exact key ▸ h4

/-! ## Pole conditions and signs (tex Lemma 2 proof) -/

/-- Pole condition `f(0) = 0` (tex Lemma 2 proof). -/
theorem f_zero (a : ℝ) : f a 0 = 0 := by simp [f]

/-- Pole condition `f'(0) = 1` (tex Lemma 2 proof). -/
theorem fp_zero (a : ℝ) : fp a 0 = 1 := by simp [fp]

theorem f_pos (a : ℝ) {r : ℝ} (hr : 0 < r) : 0 < f a r := by
  have h : (0:ℝ) < (1 + r ^ 2) ^ ((a - 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
  exact mul_pos hr h

/-- `f' > 0` everywhere (tex eq. `eq:fp`). -/
theorem fp_pos {a : ℝ} (ha : 0 < a) (r : ℝ) : 0 < fp a r := by
  have h1 : (0:ℝ) < (1 + r ^ 2) ^ ((a - 3) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : (0:ℝ) < 1 + a * r ^ 2 := by nlinarith [sq_nonneg r]
  exact mul_pos h1 h2

/-- `f'' < 0` for `r > 0` (tex eq. `eq:fpp`). -/
theorem fpp_neg {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr : 0 < r) : fpp a r < 0 := by
  have h1 : (0:ℝ) < (1 + r ^ 2) ^ ((a - 5) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : (0:ℝ) < 3 + a * r ^ 2 := by nlinarith [sq_nonneg r]
  have h3 : a - 1 < 0 := by linarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h3 hr) h1) h2

/-- `0 < f'(r) < 1` for `r > 0` ("`f'` decreases strictly from 1",
tex Lemma 2 proof). -/
theorem fp_lt_one {a : ℝ} (ha1 : a < 1) {r : ℝ} (hr : 0 < r) : fp a r < 1 := by
  have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
  have hb1 : (1:ℝ) < 1 + r ^ 2 := by nlinarith
  have h1 : (1:ℝ) + a * r ^ 2 < 1 + r ^ 2 := by nlinarith
  have h2 : ((1:ℝ) + r ^ 2) ^ (1:ℝ) < (1 + r ^ 2) ^ ((3 - a) / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt hb1 (by linarith)
  rw [Real.rpow_one] at h2
  have h3 : (1:ℝ) + a * r ^ 2 < (1 + r ^ 2) ^ ((3 - a) / 2) := lt_trans h1 h2
  have hX : (0:ℝ) < (1 + r ^ 2) ^ ((a - 3) / 2) := Real.rpow_pos_of_pos hb _
  calc fp a r = (1 + r ^ 2) ^ ((a - 3) / 2) * (1 + a * r ^ 2) := rfl
    _ < (1 + r ^ 2) ^ ((a - 3) / 2) * (1 + r ^ 2) ^ ((3 - a) / 2) :=
        mul_lt_mul_of_pos_left h3 hX
    _ = 1 := by
        rw [← Real.rpow_add hb, show (a - 3) / 2 + (3 - a) / 2 = 0 by ring, Real.rpow_zero]

/-- `f'` is strictly decreasing on `[0,∞)` (tex Lemma 2 proof). -/
theorem fp_strictAntiOn {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (fp a) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun x _ => (hasDerivAt_fp a x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_fp a x).deriv]
    exact fpp_neg ha ha1 hx

/-! ## Strictly positive sectional curvature (tex Lemma 2) -/

/-- `K_rad > 0` for `r > 0` (tex Lemma 2). -/
theorem Krad_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr : 0 < r) :
    0 < Krad a r :=
  div_pos (neg_pos.mpr (fpp_neg ha ha1 hr)) (f_pos a hr)

/-- `K_tan > 0` for `r > 0` (tex Lemma 2). -/
theorem Ktan_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr : 0 < r) :
    0 < Ktan a r := by
  have h1 : fp a r < 1 := fp_lt_one ha1 hr
  have h0 : 0 < fp a r := fp_pos ha r
  have hsq : fp a r ^ 2 < 1 := by nlinarith
  exact div_pos (by linarith) (pow_pos (f_pos a hr) 2)

/-- Exact formula for the radial curvature away from the pole:
`K_rad = (1-a)(3+ar²)/(1+r²)²` (used for the pole value in tex Lemma 2). -/
theorem Krad_eq (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    Krad a r = (1 - a) * (3 + a * r ^ 2) / (1 + r ^ 2) ^ 2 := by
  have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
  have hT : (0:ℝ) < (1 + r ^ 2) ^ ((a - 5) / 2) := Real.rpow_pos_of_pos hb _
  have e : (1 + r ^ 2 : ℝ) ^ ((a - 1) / 2)
      = (1 + r ^ 2) ^ ((a - 5) / 2) * (1 + r ^ 2) ^ 2 := by
    rw [show (a - 1) / 2 = (a - 5) / 2 + 2 by ring, Real.rpow_add hb]
    norm_num
  unfold Krad fpp f
  rw [e]
  field_simp
  ring

/-- At the pole the radial curvature extends continuously to `3(1-a) > 0`
(tex Lemma 2 proof). -/
theorem Krad_tendsto_pole (a : ℝ) :
    Tendsto (Krad a) (𝓝[>] (0:ℝ)) (𝓝 (3 * (1 - a))) := by
  have hcont : ContinuousAt (fun r : ℝ => (1 - a) * (3 + a * r ^ 2) / (1 + r ^ 2) ^ 2) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have h0 : (1 - a) * (3 + a * (0:ℝ) ^ 2) / (1 + (0:ℝ) ^ 2) ^ 2 = 3 * (1 - a) := by
    norm_num; ring
  have hc : Tendsto (fun r : ℝ => (1 - a) * (3 + a * r ^ 2) / (1 + r ^ 2) ^ 2)
      (𝓝 (0:ℝ)) (𝓝 (3 * (1 - a))) := h0 ▸ hcont.tendsto
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (Krad_eq a (ne_of_gt hr)).symm

/-- Auxiliary function: `1 - f'(r)²` as a smooth function of `u = r²`. -/
def gaux (a u : ℝ) : ℝ := 1 - (1 + u) ^ (a - 3) * (1 + a * u) ^ 2

theorem gaux_zero (a : ℝ) : gaux a 0 = 0 := by simp [gaux]

theorem hasDerivAt_gaux (a : ℝ) : HasDerivAt (gaux a) (3 * (1 - a)) 0 := by
  have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add 1
  have hA : HasDerivAt (fun u : ℝ => (1 + u) ^ (a - 3)) (a - 3) 0 := by
    have := h1.rpow_const (p := a - 3) (Or.inl (by norm_num))
    simpa using this
  have h2 : HasDerivAt (fun u : ℝ => 1 + a * u) a 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul a).const_add 1
  have hB : HasDerivAt (fun u : ℝ => (1 + a * u) ^ 2) (2 * a) 0 := by
    have := h2.pow 2
    simpa using this
  have hprod := hA.mul hB
  have hprod' : HasDerivAt (fun u : ℝ => (1 + u) ^ (a - 3) * (1 + a * u) ^ 2)
      (3 * a - 3) 0 := by
    convert hprod using 1
    simp only [mul_zero, add_zero, one_pow, mul_one, Real.one_rpow, one_mul]
    ring
  have hfinal := hprod'.const_sub 1
  have e : (3 : ℝ) * (1 - a) = -(3 * a - 3) := by ring
  rw [e]
  exact hfinal

/-- At the pole the tangential curvature also extends continuously to
`3(1-a)` (tex Lemma 2 proof). -/
theorem Ktan_tendsto_pole (a : ℝ) :
    Tendsto (Ktan a) (𝓝[>] (0:ℝ)) (𝓝 (3 * (1 - a))) := by
  -- slope of `gaux` at `0`, composed with `r ↦ r²`
  have hslope : Tendsto (slope (gaux a) 0) (𝓝[≠] (0:ℝ)) (𝓝 (3 * (1 - a))) :=
    hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_gaux a)
  have hsq : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun r : ℝ => r ^ 2) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) ^ 2)) :=
        (continuous_pow 2).continuousAt
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using pow_ne_zero 2 (Set.mem_Ioi.mp hr).ne'
  have hcomp : Tendsto (fun r : ℝ => slope (gaux a) 0 (r ^ 2)) (𝓝[>] (0:ℝ))
      (𝓝 (3 * (1 - a))) := hslope.comp hsq
  have hfac : Tendsto (fun r : ℝ => (1 + r ^ 2) ^ (1 - a)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun r : ℝ => (1 + r ^ 2) ^ (1 - a)) 0 := by
      apply ContinuousAt.rpow_const
      · fun_prop
      · left; norm_num
    have h2 : Tendsto (fun r : ℝ => (1 + r ^ 2) ^ (1 - a)) (𝓝[>] (0:ℝ))
        (𝓝 ((1 + (0:ℝ) ^ 2) ^ (1 - a))) := hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h2
  have hmul := hcomp.mul hfac
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
  have hX : (0:ℝ) < (1 + r ^ 2) ^ (a - 1) := Real.rpow_pos_of_pos hb _
  have hslope_eq : slope (gaux a) 0 (r ^ 2) = gaux a (r ^ 2) / r ^ 2 := by
    rw [slope_def_field, gaux_zero, sub_zero, sub_zero]
  have hfp2 : fp a r ^ 2 = (1 + r ^ 2) ^ (a - 3) * (1 + a * r ^ 2) ^ 2 := by
    unfold fp; rw [mul_pow, rpow_half_sq hb]
  have hf2 : f a r ^ 2 = r ^ 2 * (1 + r ^ 2) ^ (a - 1) := by
    unfold f; rw [mul_pow, rpow_half_sq hb]
  have hinv : (1 + r ^ 2 : ℝ) ^ (1 - a) * (1 + r ^ 2) ^ (a - 1) = 1 := by
    rw [← Real.rpow_add hb, show (1 - a) + (a - 1) = 0 by ring, Real.rpow_zero]
  show slope (gaux a) 0 (r ^ 2) * (1 + r ^ 2) ^ (1 - a) = Ktan a r
  rw [hslope_eq]
  unfold Ktan gaux
  rw [hfp2, hf2, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero 2 hr0) (mul_pos (pow_pos hr 2) hX).ne']
  linear_combination ((1 - (1 + r ^ 2) ^ (a - 3) * (1 + a * r ^ 2) ^ 2) * r ^ 2) * hinv

/-! ## The spectral quantity `S(R)` (tex Lemma 3 proof) -/

/-- With the geometric inputs `|A|² = 2(f'/f)²` and `Ric_N(ν,ν) = -2 f''/f`
(tex Lemma 3 proof), the Jacobi potential is the constant
`q_R = 2((f')² - f f'')/f² = S(R)/f(R)²`. -/
theorem jacobi_potential (a : ℝ) {r : ℝ} (hf : f a r ≠ 0) :
    2 * (fp a r / f a r) ^ 2 + (-2) * (fpp a r / f a r) = S a r / f a r ^ 2 := by
  unfold S
  field_simp
  ring

/-- Closed form: `S(R) = 2 (1+R²)^(a-3) (1 + (3-a)R² + aR⁴)`. -/
theorem S_eq (a r : ℝ) :
    S a r = 2 * (1 + r ^ 2) ^ (a - 3) * (1 + (3 - a) * r ^ 2 + a * r ^ 4) := by
  have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
  have h1 : ((1 + r ^ 2 : ℝ) ^ ((a - 3) / 2)) ^ 2 = (1 + r ^ 2) ^ (a - 3) :=
    rpow_half_sq hb _
  have h2 : (1 + r ^ 2 : ℝ) ^ ((a - 1) / 2) * (1 + r ^ 2) ^ ((a - 5) / 2)
      = (1 + r ^ 2) ^ (a - 3) := by
    rw [← Real.rpow_add hb]
    congr 1
    ring
  unfold S fp f fpp
  linear_combination (2 * (1 + a * r ^ 2) ^ 2) * h1
    - (2 * (a - 1) * r ^ 2 * (3 + a * r ^ 2)) * h2

/-- `S(R) > 0` for every `R` (tex: `S(R) → 0⁺`). -/
theorem S_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (r : ℝ) : 0 < S a r := by
  rw [S_eq]
  have hX : (0:ℝ) < (1 + r ^ 2) ^ (a - 3) := Real.rpow_pos_of_pos (by positivity) _
  have hB : (0:ℝ) < 1 + (3 - a) * r ^ 2 + a * r ^ 4 := by
    nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  positivity

/-- `S(R) → 0` as `R → ∞` (tex Lemma 3 proof: `S(R) ~ 2aR^{2a-2} → 0⁺`). -/
theorem S_tendsto_zero {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (S a) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun r : ℝ => 6 * (1 + r ^ 2) ^ (a - 1))
    (fun r => (S_pos ha ha1 r).le)
  · -- S(R) ≤ 6 (1+R²)^(a-1)
    intro r
    rw [S_eq]
    have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
    have hX : (0:ℝ) < (1 + r ^ 2) ^ (a - 3) := Real.rpow_pos_of_pos hb _
    have h1 : (1:ℝ) + (3 - a) * r ^ 2 + a * r ^ 4 ≤ 3 * (1 + r ^ 2) ^ 2 := by
      nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
    have h2 : (1 + r ^ 2 : ℝ) ^ (a - 3) * (1 + r ^ 2) ^ 2 = (1 + r ^ 2) ^ (a - 1) := by
      rw [← Real.rpow_natCast (1 + r ^ 2) 2, ← Real.rpow_add hb]
      congr 1
      push_cast
      ring
    calc 2 * (1 + r ^ 2 : ℝ) ^ (a - 3) * (1 + (3 - a) * r ^ 2 + a * r ^ 4)
        ≤ 2 * (1 + r ^ 2) ^ (a - 3) * (3 * (1 + r ^ 2) ^ 2) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 6 * ((1 + r ^ 2) ^ (a - 3) * (1 + r ^ 2) ^ 2) := by ring
      _ = 6 * (1 + r ^ 2) ^ (a - 1) := by rw [h2]
  · -- 6 (1+r²)^(a-1) → 0
    have h1 : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop := by
      apply tendsto_atTop_mono ?_ tendsto_id
      intro r
      simp only [id_eq]
      nlinarith [sq_nonneg (r - 1)]
    have h2 : Tendsto (fun x : ℝ => x ^ (a - 1)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 1 - a) (by linarith)
      simpa [show -(1 - a) = a - 1 by ring] using this
    have h3 := (h2.comp h1).const_mul (6:ℝ)
    simpa using h3

/-! ## Divergence of area and weighted area (tex Theorem 1, §4) -/

/-- `f(R) → ∞` (tex: `f(R) ~ R^a`, so the areas diverge). -/
theorem f_tendsto_atTop {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (f a) atTop atTop := by
  have hbound : ∀ᶠ r in atTop, (2:ℝ) ^ ((a - 1) / 2) * r ^ a ≤ f a r := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    have hr0 : (0:ℝ) < r := lt_of_lt_of_le one_pos hr
    have hb : (0:ℝ) < 1 + r ^ 2 := by positivity
    have h1 : (1:ℝ) + r ^ 2 ≤ 2 * r ^ 2 := by nlinarith
    have h2 : ((2:ℝ) * r ^ 2) ^ ((a - 1) / 2) ≤ (1 + r ^ 2) ^ ((a - 1) / 2) :=
      Real.rpow_le_rpow_of_nonpos hb h1 (by linarith)
    have h3 : ((2:ℝ) * r ^ 2) ^ ((a - 1) / 2)
        = 2 ^ ((a - 1) / 2) * r ^ (a - 1) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le]
      congr 1
      push_cast
      ring
    have h4 : r ^ (a - 1) * r = r ^ a := by
      rw [← Real.rpow_add_one hr0.ne' (a - 1)]
      congr 1
      ring
    calc (2:ℝ) ^ ((a - 1) / 2) * r ^ a
        = r * (2 ^ ((a - 1) / 2) * r ^ (a - 1)) := by rw [← h4]; ring
      _ = r * ((2 * r ^ 2) ^ ((a - 1) / 2)) := by rw [h3]
      _ ≤ r * ((1 + r ^ 2) ^ ((a - 1) / 2)) := by
          exact mul_le_mul_of_nonneg_left h2 hr0.le
      _ = f a r := rfl
  have hpow : Tendsto (fun r : ℝ => (2:ℝ) ^ ((a - 1) / 2) * r ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).const_mul_atTop (Real.rpow_pos_of_pos two_pos _)
  exact tendsto_atTop_mono' atTop hbound hpow

/-- `Area(Σ_R) = 4π f(R)² → ∞` (tex Theorem 1). -/
theorem area_tendsto_atTop {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (area a) atTop atTop := by
  have hf := f_tendsto_atTop ha ha1
  have hsq : Tendsto (fun r => f a r ^ 2) atTop atTop := by
    have h := hf.atTop_mul_atTop₀ hf
    simpa [pow_two] using h
  have h4pi : (0:ℝ) < 4 * Real.pi := by positivity
  exact hsq.const_mul_atTop h4pi

/-- tex §4: `(1+h_R²)·Area(Σ_R) = 4π f(R)² + 16π f'(R)²`. -/
theorem energy_identity (a : ℝ) {r : ℝ} (hf : f a r ≠ 0) :
    (1 + hmean a r ^ 2) * area a r
      = 4 * Real.pi * f a r ^ 2 + 16 * Real.pi * fp a r ^ 2 := by
  unfold hmean area
  field_simp
  ring

/-- tex §4: `(1+h_{R}²)·Area(Σ_R) → ∞`. -/
theorem energy_tendsto_atTop {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun r => (1 + hmean a r ^ 2) * area a r) atTop atTop := by
  apply tendsto_atTop_mono (fun r => ?_) (area_tendsto_atTop ha ha1)
  have h1 : 0 ≤ area a r := by unfold area; positivity
  nlinarith [sq_nonneg (hmean a r)]

/-! ## The Jacobi spectrum of a coordinate sphere (tex Lemma 3) -/

/-- When `S(R) > 0` the `ℓ = 0` Jacobi eigenvalue is negative
(tex Lemma 3 proof). -/
theorem jacobiEig_zero_neg {a r : ℝ} (h0 : 0 < S a r) (hf : f a r ≠ 0) :
    jacobiEig a r 0 < 0 := by
  unfold jacobiEig
  have hf2 : (0:ℝ) < f a r ^ 2 := by positivity
  apply div_neg_of_neg_of_pos _ hf2
  push_cast
  linarith

/-- When `S(R) < 2` every `ℓ ≥ 1` Jacobi eigenvalue is positive
(tex Lemma 3 proof: `ℓ(ℓ+1) ≥ 2 > S(R)`). -/
theorem jacobiEig_pos {a r : ℝ} (h2 : S a r < 2) (hf : f a r ≠ 0) {ℓ : ℕ}
    (hl : 1 ≤ ℓ) : 0 < jacobiEig a r ℓ := by
  unfold jacobiEig
  have hf2 : (0:ℝ) < f a r ^ 2 := by positivity
  have hl' : (1:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hl
  apply div_pos _ hf2
  nlinarith

/-- If `0 < S(R) < 2` the strong Morse index is exactly `1`: the only negative
eigenvalue is `ℓ = 0`, with multiplicity `2·0+1 = 1` (tex Lemma 3). -/
theorem sphIndex_eq_one {a r : ℝ} (h0 : 0 < S a r) (h2 : S a r < 2)
    (hf : f a r ≠ 0) : sphIndex a r = 1 := by
  unfold sphIndex
  rw [tsum_eq_single 0 (fun ℓ hℓ =>
    if_neg (not_lt.mpr (jacobiEig_pos h2 hf (Nat.one_le_iff_ne_zero.mpr hℓ)).le))]
  rw [if_pos (jacobiEig_zero_neg h0 hf)]

/-- If `0 < S(R) < 2` the nullity is `0`: no Jacobi eigenvalue vanishes
(tex Lemma 3). -/
theorem sphNullity_eq_zero {a r : ℝ} (h0 : 0 < S a r) (h2 : S a r < 2)
    (hf : f a r ≠ 0) : sphNullity a r = 0 := by
  unfold sphNullity
  have h : ∀ ℓ : ℕ, (if jacobiEig a r ℓ = 0 then 2 * ℓ + 1 else 0) = 0 := by
    intro ℓ
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h
      exact if_neg (jacobiEig_zero_neg h0 hf).ne
    · exact if_neg (jacobiEig_pos h2 hf h).ne'
  simp only [h]
  exact tsum_zero

/-- **tex Lemma 3 (`lem:spectrum`)**: for all sufficiently large `R`,
`i(Σ_R) = 1` and `n(Σ_R) = 0`. -/
theorem eventually_index_one_nullity_zero {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ r in atTop, sphIndex a r = 1 ∧ sphNullity a r = 0 := by
  have h2 : ∀ᶠ r in atTop, S a r < 2 :=
    (S_tendsto_zero ha ha1).eventually_lt_const (by norm_num)
  have hf : ∀ᶠ r in atTop, 0 < f a r :=
    (f_tendsto_atTop ha ha1).eventually_gt_atTop 0
  filter_upwards [h2, hf] with r h2 hf
  exact ⟨sphIndex_eq_one (S_pos ha ha1 r) h2 hf.ne',
    sphNullity_eq_zero (S_pos ha ha1 r) h2 hf.ne'⟩

/-! ## The counterexample (tex Theorem 1 and §4) -/

/-- **tex Theorem 1 (`thm:main`) + §4.** For every `a ∈ (0,1)` and every
proposed constant `C > 0`: the areas of the CMC spheres `Σ_R` diverge, yet
for all sufficiently large `R` the index is `1`, the nullity is `0`, and the
proposed bound `C((1+h²)·Area + genus) ≤ index + nullity` fails, because the
left side exceeds `1 = index + nullity`. -/
theorem main_counterexample {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {C : ℝ}
    (hC : 0 < C) :
    Tendsto (area a) atTop atTop ∧
    ∀ᶠ r in atTop,
      sphIndex a r = 1 ∧ sphNullity a r = 0 ∧
      (sphIndex a r : ℝ) + (sphNullity a r : ℝ)
        < C * ((1 + hmean a r ^ 2) * area a r + genus) := by
  refine ⟨area_tendsto_atTop ha ha1, ?_⟩
  have hE : Tendsto (fun r => C * ((1 + hmean a r ^ 2) * area a r)) atTop atTop :=
    (energy_tendsto_atTop ha ha1).const_mul_atTop hC
  have hE1 : ∀ᶠ r in atTop, 1 < C * ((1 + hmean a r ^ 2) * area a r) :=
    hE.eventually_gt_atTop 1
  filter_upwards [eventually_index_one_nullity_zero ha ha1, hE1] with r hin h1
  obtain ⟨hidx, hnul⟩ := hin
  refine ⟨hidx, hnul, ?_⟩
  rw [hidx, hnul]
  push_cast
  simpa [genus] using h1

/-- **Failure of the proposed estimate (tex eq. `eq:proposed`)**: on this fixed
ambient manifold, no positive constant `C` can make
`C((1+h²)Area(Σ) + g(Σ)) ≤ index + nullity` hold for all the CMC spheres
`Σ_R`; in fact it fails for all sufficiently large `R`. -/
theorem no_constant_works {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ C : ℝ, 0 < C → ∃ r : ℝ,
      sphIndex a r = 1 ∧ sphNullity a r = 0 ∧
      ¬ (C * ((1 + hmean a r ^ 2) * area a r + genus)
          ≤ (sphIndex a r : ℝ) + (sphNullity a r : ℝ)) := by
  intro C hC
  obtain ⟨r, h1, h2, h3⟩ := ((main_counterexample ha ha1 hC).2).exists
  exact ⟨r, h1, h2, not_le.mpr h3⟩

/-- **tex Lemma 2 (`lem:geometry`)**, packaged: the warping function satisfies
the pole conditions `f(0) = 0`, `f'(0) = 1`, and both sectional curvatures of
the metric `dr² + f(r)² g_{S²}` are strictly positive for `r > 0` and extend
continuously to the value `3(1-a) > 0` at the pole. -/
theorem lemma_geometry {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    f a 0 = 0 ∧ fp a 0 = 1 ∧
    (∀ r : ℝ, 0 < r → 0 < Krad a r) ∧
    (∀ r : ℝ, 0 < r → 0 < Ktan a r) ∧
    Tendsto (Krad a) (𝓝[>] (0:ℝ)) (𝓝 (3 * (1 - a))) ∧
    Tendsto (Ktan a) (𝓝[>] (0:ℝ)) (𝓝 (3 * (1 - a))) ∧
    0 < 3 * (1 - a) :=
  ⟨f_zero a, fp_zero a, fun _ hr => Krad_pos ha ha1 hr,
    fun _ hr => Ktan_pos ha ha1 hr, Krad_tendsto_pole a, Ktan_tendsto_pole a,
    by linarith⟩

end

end CmcIndexArea
