import Mathlib

/-!
# An explicit counterexample to a conjectured dimension-free Huisken-energy bound

Formalization of "An explicit counterexample to a conjectured dimension-free
Huisken-energy bound" (`explicit_huisken_energy_counterexample.tex`).

The paper disproves the conjecture of Angenent–Daskalopoulos–Šešum that the
Huisken energy `H_ADS(C) = (4π)^{-(d-1)/2} ∫_{∂C} e^{-|x|²/4} dH^{d-1}` is `< 2`
for every closed convex `C ⊆ ℝ^d`, by exhibiting the cube `Q = [-12/5, 12/5]⁹`
with `H_ADS(Q) > 1002087/500000 > 2`.

Correspondence with the paper (see the individual docstrings):

* `erf`, `erfc` — the error functions (not in Mathlib; defined here as in §2).
* `exp_neg_taylor_lb` — the alternating-series engine behind Lemma 3.1.
* `exp_cert`, `pi_bound`, `integral_exp_neg_sq_lb`, `erf_cert`, `pow_cert`,
  `erf_pow_cert` — Lemma 3.1 (rational certificate) and eq:pi-bound, fully proven.
* `slab_integral`, `facet_integral`, `normalization`, `cube_formula` —
  Proposition 2.1 (cube formula).  The analytic content (Fubini factorization of
  the facet integral, the substitution `t = 2s`, the `(4π)^{-n/2}(2√π)^n = 1`
  normalization) is fully proven; the geometric facet decomposition of `∂Q`
  (Hausdorff measure of a polytope boundary, not in Mathlib) enters
  `cube_formula`/`thm_main` as the hypothesis `hB`.
* `huisken_cube_nine_lb`, `huisken_cube_nine_gt_two`, `thm_main` — Theorem 1.1.
* `erfc_eq_tail`, `gaussian_tail_le`, `erfc_le_mills`, `exp_neg_two_mul_le`,
  `cube_energy_unbounded` — the Mills bound eq:mills (in `≤` form, which
  suffices) and Proposition 2.2 (no dimension-free bound), fully proven for the
  closed-form energies of `cube_formula`.
* `Fm`, `Fm_hessian_diag_pos`, `Fm_strictConvexOn`, `Fm_radial_deriv_pos`,
  `Fm_sublevel_subset_cube`, `cube_scaled_eventually_subset` — the algebraic /
  analytic content of Proposition 4.1 (smooth strictly convex approximants).
  The differential-geometric conclusions (smoothness of `∂C_m`, positivity of
  the principal curvatures, Hausdorff convergence of sets) are classical
  consequences not expressible in current Mathlib.
* `thm_smooth` — Theorem 1.2, modulo the ADS continuity lemma
  ([ADS, Lemma 3.6]), which enters as the convergence hypothesis `hconv`.
-/

namespace HuiskenEnergy

open Real MeasureTheory intervalIntegral

/-- The Gauss error function `erf s = (2/√π) ∫_0^s e^{-t²} dt`.
(Not yet in Mathlib, so we define it here; cf. the paper's §2.) -/
noncomputable def erf (s : ℝ) : ℝ := (2 / √π) * ∫ t in (0 : ℝ)..s, exp (-t ^ 2)

/-- The complementary error function `erfc s = 1 - erf s`. -/
noncomputable def erfc (s : ℝ) : ℝ := 1 - erf s

/-- Degree-9 alternating-Taylor lower bound for `exp (-u)`, valid for all `u ≥ 0`.
This is the analytic engine behind the paper's Lemma 3.1 (rational certificate):
the partial sum of the alternating exponential series ending in a negative term
is a lower bound for `e^{-u}`. -/
theorem exp_neg_taylor_lb {u : ℝ} (hu : 0 ≤ u) :
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 120 + u ^ 6 / 720
      - u ^ 7 / 5040 + u ^ 8 / 40320 - u ^ 9 / 362880 ≤ exp (-u) := by
  set P : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120
      + x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - x ^ 9 / 362880 with hPdef
  have hP : ∀ x : ℝ, HasDerivAt P
      (-1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720
        + x ^ 7 / 5040 - x ^ 8 / 40320) x := by
    intro x
    have h := (((((((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      ((hasDerivAt_pow 2 x).div_const 2)).sub
      ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 4 x).div_const 24)).sub
      ((hasDerivAt_pow 5 x).div_const 120)).add
      ((hasDerivAt_pow 6 x).div_const 720)).sub
      ((hasDerivAt_pow 7 x).div_const 5040)).add
      ((hasDerivAt_pow 8 x).div_const 40320)).sub
      ((hasDerivAt_pow 9 x).div_const 362880)
    convert h using 1
    push_cast
    ring
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y => exp y * P y)
      (exp x * (-x ^ 9 / 362880)) x := by
    intro x
    have h := (Real.hasDerivAt_exp x).mul (hP x)
    convert h using 1
    simp only [hPdef]
    ring
  have hanti : AntitoneOn (fun y => exp y * P y) (Set.Icc 0 u) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 u) ?_ ?_ ?_
    · exact Continuous.continuousOn (by fun_prop)
    · exact fun x _ => ((hderiv x).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      have h1 : (0 : ℝ) ≤ x ^ 9 / 362880 :=
        div_nonneg (pow_nonneg hx.1.le 9) (by norm_num)
      have h2 : (0 : ℝ) < exp x := exp_pos x
      nlinarith
  have key : exp u * P u ≤ exp 0 * P 0 :=
    hanti (Set.left_mem_Icc.2 hu) (Set.right_mem_Icc.2 hu) hu
  have hP0 : exp 0 * P 0 = 1 := by simp [hPdef]
  rw [hP0] at key
  have hmul : exp (-u) * exp u = 1 := by rw [← Real.exp_add]; simp
  have hPu : P u = 1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 120 + u ^ 6 / 720
      - u ^ 7 / 5040 + u ^ 8 / 40320 - u ^ 9 / 362880 := rfl
  rw [← hPu]
  nlinarith [exp_pos u]

/-! ## Lemma 3.1 (Rational certificate) -/

/-- Lemma 3.1, first estimate (eq:certificate): `e^{-36/25} > 2369/10000`.
The paper proves this by a geometric-tail bound on the series for `e^{36/25}`;
here we use the alternating-series lower bound `exp_neg_taylor_lb` directly. -/
theorem exp_cert : (2369 / 10000 : ℝ) < exp (-(36 / 25)) := by
  have h := exp_neg_taylor_lb (u := 36 / 25) (by norm_num)
  have h2 : (2369 / 10000 : ℝ) < 1 - 36 / 25 + (36 / 25) ^ 2 / 2 - (36 / 25) ^ 3 / 6
      + (36 / 25) ^ 4 / 24 - (36 / 25) ^ 5 / 120 + (36 / 25) ^ 6 / 720
      - (36 / 25) ^ 7 / 5040 + (36 / 25) ^ 8 / 40320 - (36 / 25) ^ 9 / 362880 := by
    norm_num
  linarith

/-- The paper's eq:pi-bound: `2/√π > 11281/10000` (a consequence of `π < 22/7`;
we use Mathlib's `pi_lt_3141593`, which is stronger). -/
theorem pi_bound : (11281 / 10000 : ℝ) < 2 / √π := by
  have hs : √π < 20000 / 11281 := by
    rw [show (20000 / 11281 : ℝ) = √((20000 / 11281) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt pi_pos.le (by nlinarith [Real.pi_lt_d4])
  have h0 : 0 < √π := Real.sqrt_pos.2 pi_pos
  rw [lt_div_iff₀ h0]
  nlinarith

/-- The polynomial lower bound for the Gaussian integral `∫_0^{6/5} e^{-t²} dt`,
computed exactly by the fundamental theorem of calculus.  This corresponds to the
paper's rational summation of the alternating series for `erf(6/5)` (Lemma 3.1). -/
theorem integral_exp_neg_sq_lb :
    (806744 / 1000000 : ℝ) ≤ ∫ t in (0 : ℝ)..(6 / 5), exp (-t ^ 2) := by
  have hmono : (∫ t in (0 : ℝ)..(6 / 5),
        (1 - t ^ 2 + t ^ 4 / 2 - t ^ 6 / 6 + t ^ 8 / 24 - t ^ 10 / 120 + t ^ 12 / 720
          - t ^ 14 / 5040 + t ^ 16 / 40320 - t ^ 18 / 362880))
      ≤ ∫ t in (0 : ℝ)..(6 / 5), exp (-t ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · intro t _
      have h := exp_neg_taylor_lb (u := t ^ 2) (sq_nonneg t)
      refine le_trans (le_of_eq ?_) h
      ring
  have hFTC : (∫ t in (0 : ℝ)..(6 / 5),
        (1 - t ^ 2 + t ^ 4 / 2 - t ^ 6 / 6 + t ^ 8 / 24 - t ^ 10 / 120 + t ^ 12 / 720
          - t ^ 14 / 5040 + t ^ 16 / 40320 - t ^ 18 / 362880))
      = (6 / 5 : ℝ) - (6 / 5) ^ 3 / 3 + (6 / 5) ^ 5 / 10 - (6 / 5) ^ 7 / 42
        + (6 / 5) ^ 9 / 216 - (6 / 5) ^ 11 / 1320 + (6 / 5) ^ 13 / 9360
        - (6 / 5) ^ 15 / 75600 + (6 / 5) ^ 17 / 685440 - (6 / 5) ^ 19 / 6894720 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) (6 / 5), HasDerivAt
        (fun s : ℝ => s - s ^ 3 / 3 + s ^ 5 / 10 - s ^ 7 / 42 + s ^ 9 / 216
          - s ^ 11 / 1320 + s ^ 13 / 9360 - s ^ 15 / 75600 + s ^ 17 / 685440
          - s ^ 19 / 6894720)
        (1 - t ^ 2 + t ^ 4 / 2 - t ^ 6 / 6 + t ^ 8 / 24 - t ^ 10 / 120 + t ^ 12 / 720
          - t ^ 14 / 5040 + t ^ 16 / 40320 - t ^ 18 / 362880) t := by
      intro t _
      have h := (((((((((hasDerivAt_id t).sub
        ((hasDerivAt_pow 3 t).div_const 3)).add
        ((hasDerivAt_pow 5 t).div_const 10)).sub
        ((hasDerivAt_pow 7 t).div_const 42)).add
        ((hasDerivAt_pow 9 t).div_const 216)).sub
        ((hasDerivAt_pow 11 t).div_const 1320)).add
        ((hasDerivAt_pow 13 t).div_const 9360)).sub
        ((hasDerivAt_pow 15 t).div_const 75600)).add
        ((hasDerivAt_pow 17 t).div_const 685440)).sub
        ((hasDerivAt_pow 19 t).div_const 6894720)
      convert h using 1
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  calc (806744 / 1000000 : ℝ)
      ≤ (6 / 5 : ℝ) - (6 / 5) ^ 3 / 3 + (6 / 5) ^ 5 / 10 - (6 / 5) ^ 7 / 42
        + (6 / 5) ^ 9 / 216 - (6 / 5) ^ 11 / 1320 + (6 / 5) ^ 13 / 9360
        - (6 / 5) ^ 15 / 75600 + (6 / 5) ^ 17 / 685440 - (6 / 5) ^ 19 / 6894720 := by
        norm_num
    _ = _ := hFTC.symm
    _ ≤ _ := hmono

/-- Lemma 3.1, second estimate (eq:certificate): `erf(6/5) > 91/100`. -/
theorem erf_cert : (91 / 100 : ℝ) < erf (6 / 5) := by
  unfold erf
  calc (91 / 100 : ℝ) < (11281 / 10000) * (806744 / 1000000) := by norm_num
    _ ≤ (2 / √π) * ∫ t in (0 : ℝ)..(6 / 5), exp (-t ^ 2) := by
        apply mul_le_mul pi_bound.le integral_exp_neg_sq_lb (by norm_num)
        positivity

/-- Lemma 3.1, third estimate (eq:certificate): `(91/100)^8 > 47/100`. -/
theorem pow_cert : (47 / 100 : ℝ) < (91 / 100 : ℝ) ^ 8 := by norm_num

/-- Combination of the second and third certificate estimates. -/
theorem erf_pow_cert : (47 / 100 : ℝ) < erf (6 / 5) ^ 8 := by
  calc (47 / 100 : ℝ) < (91 / 100) ^ 8 := pow_cert
    _ ≤ erf (6 / 5) ^ 8 := by
        gcongr
        exact erf_cert.le

/-! ## Theorem 1.1 (thm:main), analytic core -/

/-- Theorem 1.1, analytic core: the closed-form value
`H_ADS(Q) = 18·e^{-36/25}·erf(6/5)^8` of the Huisken energy of the cube
`Q = [-12/5, 12/5]^9` (see `cube_formula` below) exceeds `1002087/500000`. -/
theorem huisken_cube_nine_lb :
    (1002087 / 500000 : ℝ) < 18 * exp (-(36 / 25)) * erf (6 / 5) ^ 8 := by
  calc (1002087 / 500000 : ℝ) = 18 * (2369 / 10000) * (47 / 100) := by norm_num
    _ < 18 * exp (-(36 / 25)) * erf (6 / 5) ^ 8 := by
        have h1 := exp_cert
        have h2 := erf_pow_cert
        nlinarith

/-- Theorem 1.1: the Huisken energy of the cube exceeds `2` (eq:main-bound). -/
theorem huisken_cube_nine_gt_two :
    (2 : ℝ) < 18 * exp (-(36 / 25)) * erf (6 / 5) ^ 8 :=
  lt_trans (by norm_num) huisken_cube_nine_lb

/-! ## Proposition 2.1 (cube-formula) -/

/-- The substitution `t = 2s` in the paper's Proposition 2.1:
`∫_{-a}^{a} e^{-t²/4} dt = 2√π · erf(a/2)`. -/
theorem slab_integral (a : ℝ) :
    (∫ t in (-a)..a, exp (-t ^ 2 / 4)) = 2 * √π * erf (a / 2) := by
  have hsub : (∫ t in (-a)..a, exp (-t ^ 2 / 4))
      = 2 * ∫ s in (-a / 2)..(a / 2), exp (-s ^ 2) := by
    have h := intervalIntegral.integral_comp_div (a := -a) (b := a) (c := 2)
      (fun s => exp (-s ^ 2)) two_ne_zero
    have heq : ∀ t : ℝ, exp (-(t / 2) ^ 2) = exp (-t ^ 2 / 4) := by
      intro t; congr 1; ring
    simp only [heq] at h
    rw [h, smul_eq_mul, neg_div]
  have heven : (∫ s in (-a / 2)..(a / 2), exp (-s ^ 2))
      = 2 * ∫ s in (0 : ℝ)..(a / 2), exp (-s ^ 2) := by
    have hint : ∀ u v : ℝ, IntervalIntegrable (fun s : ℝ => exp (-s ^ 2)) volume u v :=
      fun u v => Continuous.intervalIntegrable (by fun_prop) _ _
    have hneg : (∫ s in (-a / 2)..(0 : ℝ), exp (-s ^ 2))
        = ∫ s in (0 : ℝ)..(a / 2), exp (-s ^ 2) := by
      have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a / 2)
        (fun s : ℝ => exp (-s ^ 2))
      simp only [neg_sq, neg_zero] at h
      rw [show -a / 2 = -(a / 2) by ring]
      exact h.symm
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (hint _ _) (hint _ _), hneg]
    ring
  rw [hsub, heven, erf]
  have hπ : √π ≠ 0 := ne_of_gt (Real.sqrt_pos.2 pi_pos)
  field_simp

/-- Proposition 2.1, Fubini step: the Gaussian weight integrates over the facet
`[-a,a]^n` (sitting at height `a`) to
`e^{-a²/4} (∫_{-a}^a e^{-t²/4} dt)^n`.  This is the display equation in the
proof of Proposition 2.1. -/
theorem facet_integral (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x in Set.univ.pi fun _ : Fin n => Set.Icc (-a) a,
        exp (-(a ^ 2 + ∑ i, x i ^ 2) / 4))
      = exp (-a ^ 2 / 4) * (∫ t in (-a)..a, exp (-t ^ 2 / 4)) ^ n := by
  have h1 : ∀ x : Fin n → ℝ, exp (-(a ^ 2 + ∑ i, x i ^ 2) / 4)
      = exp (-a ^ 2 / 4) * ∏ i, exp (-(x i) ^ 2 / 4) := by
    intro x
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    ring
  simp only [h1]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hmeas : (volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Icc (-a) a)
      = Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (-a) a) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  rw [hmeas]
  rw [MeasureTheory.integral_fin_nat_prod_eq_prod
    (f := fun _ : Fin n => fun t : ℝ => exp (-t ^ 2 / 4))]
  rw [Finset.prod_const]
  have hIcc : (∫ t in Set.Icc (-a) a, exp (-t ^ 2 / 4))
      = ∫ t in (-a)..a, exp (-t ^ 2 / 4) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  rw [hIcc, Finset.card_univ, Fintype.card_fin]

/-- The normalization identity `(4π)^{-n/2} (2√π)^n = 1`. -/
theorem normalization (n : ℕ) : (4 * π) ^ (-(n : ℝ) / 2) * (2 * √π) ^ n = 1 := by
  have h2 : (2 * √π : ℝ) = √(4 * π) := by
    rw [show (4 : ℝ) * π = 2 ^ 2 * π by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h3 : (√(4 * π)) ^ n = (4 * π) ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((4 * π) ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul (by positivity), show (1 : ℝ) / 2 * (n : ℝ) = (n : ℝ) / 2 by ring]
  rw [h2, h3, ← Real.rpow_add (by positivity),
    show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring, Real.rpow_zero]

/-- Proposition 2.1 (cube-formula).  The geometric input — the boundary of the cube
`Q_{n+1}(a) = [-a,a]^{n+1}` decomposes (up to `H^n`-null overlaps) into `2(n+1)`
facets, each isometric to `[-a,a]^n` at height `a`, so that
`∫_{∂Q} e^{-|x|²/4} dH^n = 2(n+1) ∫_{[-a,a]^n} e^{-(a²+|x'|²)/4} dx'` — is not
available in Mathlib (Hausdorff measure on polytope boundaries), so it enters as
the hypothesis `hB`.  Given it, the Huisken energy
`H_ADS(Q) = (4π)^{-n/2} · B` has the closed form `2(n+1) e^{-a²/4} erf(a/2)^n`. -/
theorem cube_formula (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (H B : ℝ)
    (hB : B = 2 * (n + 1) * ∫ x in Set.univ.pi fun _ : Fin n => Set.Icc (-a) a,
        exp (-(a ^ 2 + ∑ i, x i ^ 2) / 4))
    (hH : H = (4 * π) ^ (-(n : ℝ) / 2) * B) :
    H = 2 * (n + 1) * exp (-a ^ 2 / 4) * erf (a / 2) ^ n := by
  rw [hH, hB, facet_integral n ha, slab_integral a]
  have hnorm := normalization n
  calc (4 * π) ^ (-(n : ℝ) / 2) * (2 * (n + 1) * (exp (-a ^ 2 / 4)
        * (2 * √π * erf (a / 2)) ^ n))
      = ((4 * π) ^ (-(n : ℝ) / 2) * (2 * √π) ^ n)
        * (2 * (n + 1) * exp (-a ^ 2 / 4) * erf (a / 2) ^ n) := by
        rw [mul_pow]; ring
    _ = 2 * (n + 1) * exp (-a ^ 2 / 4) * erf (a / 2) ^ n := by rw [hnorm, one_mul]

/-- Theorem 1.1 (thm:main).  Modulo the facet decomposition of `∂Q` (hypothesis
`hB`, see `cube_formula`), the Huisken energy `H = H_ADS(Q)` of the cube
`Q = [-12/5, 12/5]^9 ⊂ ℝ⁹` satisfies `H > 1002087/500000 > 2`, refuting the
dimension-free bound `H_ADS < 2` (eq:conjecture) at hypersurface dimension 8. -/
theorem thm_main (H B : ℝ)
    (hB : B = 2 * 9 * ∫ x in Set.univ.pi fun _ : Fin 8 => Set.Icc (-(12 / 5) : ℝ) (12 / 5),
        exp (-((12 / 5 : ℝ) ^ 2 + ∑ i, x i ^ 2) / 4))
    (hH : H = (4 * π) ^ (-(8 : ℝ) / 2) * B) :
    1002087 / 500000 < H ∧ (2 : ℝ) < H := by
  have hval : H = 2 * (8 + 1) * exp (-(12 / 5 : ℝ) ^ 2 / 4) * erf ((12 / 5) / 2) ^ 8 := by
    refine cube_formula 8 (by norm_num) H B ?_ ?_
    · rw [hB]; norm_num
    · rw [hH]; norm_num
  have heq : H = 18 * exp (-(36 / 25)) * erf (6 / 5) ^ 8 := by
    rw [hval, show (-(12 / 5 : ℝ) ^ 2 / 4) = -(36 / 25) by norm_num,
      show ((12 / 5 : ℝ) / 2) = 6 / 5 by norm_num]
    ring
  rw [heq]
  exact ⟨huisken_cube_nine_lb, huisken_cube_nine_gt_two⟩

/-! ## Proposition 2.2 (prop:unbounded) -/

/-- The complementary error function as a Gaussian tail integral:
`erfc s = (2/√π) ∫_s^∞ e^{-t²} dt` for `s ≥ 0`.  (Uses the Gaussian integral
`∫_0^∞ e^{-t²} dt = √π/2`.) -/
theorem erfc_eq_tail {s : ℝ} (hs : 0 ≤ s) :
    erfc s = (2 / √π) * ∫ t in Set.Ioi s, exp (-t ^ 2) := by
  have hint : Integrable (fun t : ℝ => exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
  have hsplit : (∫ t in Set.Ioc 0 s, exp (-t ^ 2)) + (∫ t in Set.Ioi s, exp (-t ^ 2))
      = ∫ t in Set.Ioi (0 : ℝ), exp (-t ^ 2) := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hint.integrableOn hint.integrableOn,
      Set.Ioc_union_Ioi_eq_Ioi hs]
  have hgauss : (∫ t in Set.Ioi (0 : ℝ), exp (-t ^ 2)) = √π / 2 := by
    simpa using integral_gaussian_Ioi 1
  have hIoc : (∫ t in (0 : ℝ)..s, exp (-t ^ 2)) = ∫ t in Set.Ioc 0 s, exp (-t ^ 2) :=
    intervalIntegral.integral_of_le hs
  have hIocval : (∫ t in Set.Ioc 0 s, exp (-t ^ 2))
      = √π / 2 - ∫ t in Set.Ioi s, exp (-t ^ 2) := by linarith
  unfold erfc erf
  rw [hIoc, hIocval]
  have hπ : √π ≠ 0 := ne_of_gt (Real.sqrt_pos.2 pi_pos)
  field_simp
  ring

/-- The Gaussian tail estimate behind the paper's Mills bound (eq:mills):
for `s > 0`, `∫_s^∞ e^{-t²} dt ≤ e^{-s²}/(2s)` (obtained by replacing `1` with
`t/s` under the integral). -/
theorem gaussian_tail_le {s : ℝ} (hs : 0 < s) :
    (∫ t in Set.Ioi s, exp (-t ^ 2)) ≤ exp (-s ^ 2) / (2 * s) := by
  have hint : Integrable (fun t : ℝ => exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
  have hint2 : Integrable (fun t : ℝ => t * exp (-t ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 1) (by norm_num)
    simpa [Real.rpow_one] using h
  have hval : (∫ t in Set.Ioi s, t * exp (-t ^ 2)) = exp (-s ^ 2) / 2 := by
    have hderiv : ∀ x ∈ Set.Ioi s, HasDerivAt (fun t : ℝ => -exp (-t ^ 2) / 2)
        (x * exp (-x ^ 2)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * x)) x := by
        simpa using (hasDerivAt_pow 2 x).neg
      have h2 := (h1.exp).neg.div_const 2
      convert h2 using 1
      ring
    have htend : Filter.Tendsto (fun t : ℝ => -exp (-t ^ 2) / 2) Filter.atTop
        (nhds 0) := by
      have h1 : Filter.Tendsto (fun t : ℝ => -t ^ 2) Filter.atTop Filter.atBot := by
        rw [Filter.tendsto_neg_atBot_iff]
        exact Filter.tendsto_pow_atTop two_ne_zero
      have h2 := Real.tendsto_exp_atBot.comp h1
      have h3 := h2.neg.div_const 2
      simpa [Function.comp] using h3
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      ((Continuous.continuousWithinAt (by fun_prop))) hderiv hint2.integrableOn htend
    rw [h]
    ring
  have hcmp : (∫ t in Set.Ioi s, exp (-t ^ 2))
      ≤ ∫ t in Set.Ioi s, t / s * exp (-t ^ 2) := by
    apply MeasureTheory.setIntegral_mono_on hint.integrableOn ?_ measurableSet_Ioi
    · intro x hx
      have hx1 : s < x := hx
      have h1 : 1 ≤ x / s := (one_le_div hs).2 hx1.le
      nlinarith [Real.exp_pos (-x ^ 2)]
    · have : (fun t : ℝ => t / s * exp (-t ^ 2))
          = fun t : ℝ => (t * exp (-t ^ 2)) / s := by
        funext t; ring
      rw [this]
      exact (hint2.div_const s).integrableOn
  have heq : (∫ t in Set.Ioi s, t / s * exp (-t ^ 2))
      = (∫ t in Set.Ioi s, t * exp (-t ^ 2)) / s := by
    rw [← MeasureTheory.integral_div]
    congr 1; funext t; ring
  rw [heq, hval] at hcmp
  calc (∫ t in Set.Ioi s, exp (-t ^ 2)) ≤ exp (-s ^ 2) / 2 / s := hcmp
    _ = exp (-s ^ 2) / (2 * s) := by ring

/-- The paper's Mills bound (eq:mills), in the `≤` form (which is all that the
proof of Proposition 2.2 uses): `erfc s ≤ e^{-s²}/(s√π)` for `s > 0`. -/
theorem erfc_le_mills {s : ℝ} (hs : 0 < s) :
    erfc s ≤ exp (-s ^ 2) / (s * √π) := by
  rw [erfc_eq_tail hs.le]
  have hπ : (0 : ℝ) < √π := Real.sqrt_pos.2 pi_pos
  calc (2 / √π) * ∫ t in Set.Ioi s, exp (-t ^ 2)
      ≤ (2 / √π) * (exp (-s ^ 2) / (2 * s)) :=
        mul_le_mul_of_nonneg_left (gaussian_tail_le hs) (by positivity)
    _ = exp (-s ^ 2) / (s * √π) := by field_simp

/-- `erfc s ≥ 0` for `s ≥ 0` (nonnegativity of the Gaussian tail). -/
theorem erfc_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ erfc s := by
  rw [erfc_eq_tail hs]
  have h1 : (0 : ℝ) ≤ ∫ t in Set.Ioi s, exp (-t ^ 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => (exp_pos _).le
  positivity

/-- The paper's elementary inequality `log(1-q) ≥ -2q` on `[0, 1/2]`, in the
exponentiated form `e^{-2q} ≤ 1 - q`. -/
theorem exp_neg_two_mul_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1 / 2) :
    exp (-(2 * q)) ≤ 1 - q := by
  have h := Real.add_one_le_exp (2 * q)
  have hmul : exp (-(2 * q)) * exp (2 * q) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-(2 * q)), Real.exp_pos (2 * q),
    mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - 2 * q)]

set_option maxHeartbeats 400000 in
/-- Proposition 2.2 (prop:unbounded): the closed-form Huisken energies
`2d·e^{-a²/4}·erf(a/2)^{d-1}` of the centrally symmetric cubes `[-a,a]^d`
(cf. `cube_formula`, with `d = n+1`) are unbounded over dimensions and side
lengths.  Following the paper: take `a = 2k` and `d = ⌈k e^{k²}⌉`, which gives
energy `> 2e^{-2}k`. -/
theorem cube_energy_unbounded (M : ℝ) :
    ∃ (n : ℕ) (a : ℝ), 0 < a ∧
      M < 2 * (n + 1) * exp (-a ^ 2 / 4) * erf (a / 2) ^ n := by
  -- Choose an integer `k ≥ 1` with `M < k/4`.
  obtain ⟨k, hk1, hkM⟩ : ∃ k : ℕ, 1 ≤ k ∧ M < (k : ℝ) / 4 := by
    refine ⟨⌊4 * |M|⌋₊ + 1, le_add_self.trans le_rfl, ?_⟩
    have h1 : 4 * |M| < (⌊4 * |M|⌋₊ + 1 : ℕ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    have h2 : M ≤ |M| := le_abs_self M
    push_cast
    push_cast at h1
    linarith
  set K : ℝ := (k : ℝ) with hK
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; exact_mod_cast hk1
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  set E : ℝ := exp (K ^ 2) with hE
  set X : ℝ := exp (-K ^ 2) with hX
  have hEX : X * E = 1 := by rw [hX, hE, ← Real.exp_add]; simp
  have hXpos : 0 < X := exp_pos _
  have hEpos : 0 < E := exp_pos _
  -- the dimension `d = ⌈k e^{k²}⌉`
  set d : ℕ := ⌈K * E⌉₊ with hd
  have hdlb : K * E ≤ (d : ℝ) := Nat.le_ceil _
  have hdub : (d : ℝ) < K * E + 1 := Nat.ceil_lt_add_one (by positivity)
  have hd1 : 0 < d := Nat.ceil_pos.2 (by positivity)
  -- Gaussian tail bounds
  set q : ℝ := erfc K with hq
  have hq0 : 0 ≤ q := erfc_nonneg (by positivity)
  have hqmills : q ≤ X / (K * √π) := by
    have := erfc_le_mills hKpos
    rwa [← hX] at this
  have hπ32 : (3 / 2 : ℝ) < √π := by
    have h9 : (3 / 2 : ℝ) ^ 2 < π := by nlinarith [pi_gt_three]
    have := Real.lt_sqrt (x := 3 / 2) (y := π) (by norm_num)
    exact this.2 h9
  have hπpos : (0 : ℝ) < √π := by linarith
  have hXhalf : X ≤ 1 / 2 := by
    have hmono : X ≤ exp (-1) := by
      rw [hX]
      apply Real.exp_le_exp.2
      nlinarith
    have he : (2 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hinv : exp (-1) * exp 1 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-1 : ℝ)]
  -- `q·K√π ≤ X`
  have hqK : q * (K * √π) ≤ X :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < K * √π)).1 hqmills
  -- `q ≤ 1/3 ≤ 1/2`
  have hq13 : q ≤ 1 / 3 := by
    have h32 : (3 / 2 : ℝ) ≤ K * √π := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h32 hq0]
  -- `d·q < 1`
  have hdq : (d : ℝ) * q < 1 := by
    have h1 : (d : ℝ) * (q * (K * √π)) ≤ (d : ℝ) * X :=
      mul_le_mul_of_nonneg_left hqK (by positivity)
    have h2 : (d : ℝ) * X < (K * E + 1) * X := by
      exact mul_lt_mul_of_pos_right hdub hXpos
    have h3 : (K * E + 1) * X = K + X := by
      have : K * E * X = K := by rw [mul_assoc, mul_comm E X, hEX, mul_one]
      nlinarith [this]
    have h4 : K + X ≤ K * √π := by nlinarith
    have h5 : (d : ℝ) * q * (K * √π) < K * √π := by nlinarith
    have h6 : (0 : ℝ) < K * √π := by positivity
    nlinarith
  -- the power bound `(1-q)^n ≥ e^{-2}` for `n = d-1`
  set n : ℕ := d - 1 with hn
  have hnd : n + 1 = d := Nat.succ_pred_eq_of_pos hd1
  have hnled : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d 1
  -- make the abbreviations opaque from here on (their defining equations are
  -- recorded above); this keeps later tactics from unfolding `⌈K e^{K²}⌉₊`
  clear_value n q d X E K
  have hqn : (n : ℝ) * (2 * q) < 2 := by
    have h1 : (n : ℝ) * q ≤ (d : ℝ) * q := by
      apply mul_le_mul_of_nonneg_right hnled hq0
    nlinarith
  have hpow : exp (-2 : ℝ) ≤ (1 - q) ^ n := by
    have h1 : exp (-(2 * q)) ^ n ≤ (1 - q) ^ n := by
      gcongr
      exact exp_neg_two_mul_le hq0 (by linarith)
    have h2 : exp (-(2 * q)) ^ n = exp ((n : ℝ) * -(2 * q)) := by
      rw [← Real.exp_nat_mul]
    have h3 : exp (-2 : ℝ) ≤ exp ((n : ℝ) * -(2 * q)) := by
      apply Real.exp_le_exp.2
      nlinarith
    calc exp (-2 : ℝ) ≤ exp ((n : ℝ) * -(2 * q)) := h3
      _ = exp (-(2 * q)) ^ n := h2.symm
      _ ≤ (1 - q) ^ n := h1
  -- `e^{-2} > 1/8`
  have hexp2 : (1 / 8 : ℝ) < exp (-2 : ℝ) := by
    have he : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hepos : (0 : ℝ) < exp 1 := exp_pos 1
    have hsq : exp (-2 : ℝ) * (exp 1 * exp 1) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-2 : ℝ)]
  -- assemble
  refine ⟨n, 2 * K, by linarith, ?_⟩
  have ha1 : -(2 * K) ^ 2 / 4 = -K ^ 2 := by ring
  have ha2 : 2 * K / 2 = K := by ring
  rw [ha1, ha2, ← hX]
  have herf : erf K = 1 - q := by rw [hq, erfc]; ring
  rw [herf]
  have hcast : ((n : ℝ) + 1) = (d : ℝ) := by exact_mod_cast congrArg Nat.cast hnd
  rw [hcast]
  have hdX : K ≤ (d : ℝ) * X := by
    calc K = K * E * X := by rw [mul_assoc, mul_comm E X, hEX, mul_one]
      _ ≤ (d : ℝ) * X := mul_le_mul_of_nonneg_right hdlb hXpos.le
  have hfinal : (d : ℝ) * X / 4 < 2 * (d : ℝ) * X * (1 - q) ^ n := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdXpos : 0 < (d : ℝ) * X := mul_pos hd0 hXpos
    have h8 : 2 * ((d : ℝ) * X) * (1 / 8) < 2 * ((d : ℝ) * X) * exp (-2 : ℝ) :=
      mul_lt_mul_of_pos_left hexp2 (by linarith)
    have h9 : 2 * ((d : ℝ) * X) * exp (-2 : ℝ) ≤ 2 * ((d : ℝ) * X) * (1 - q) ^ n :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    calc (d : ℝ) * X / 4 = 2 * ((d : ℝ) * X) * (1 / 8) := by ring
      _ < 2 * ((d : ℝ) * X) * exp (-2 : ℝ) := h8
      _ ≤ 2 * ((d : ℝ) * X) * (1 - q) ^ n := h9
      _ = 2 * (d : ℝ) * X * (1 - q) ^ n := by ring
  calc M < K / 4 := hkM
    _ ≤ (d : ℝ) * X / 4 := by linarith
    _ < 2 * (d : ℝ) * X * (1 - q) ^ n := hfinal

/-! ## Proposition 4.1 (prop:approximation): smooth strictly convex approximants -/

/-- The defining function of the approximating body `C_m` in the rescaled
`z = 5x/12` coordinates (eq:smooth-approximation):
`F_m(z) = Σᵢ z_i^{2m} + (1/m) Σᵢ z_i²`. -/
noncomputable def Fm (m : ℕ) (z : Fin 9 → ℝ) : ℝ :=
  ∑ i, (z i ^ (2 * m) + (1 / (m : ℝ)) * z i ^ 2)

/-- Prop 4.1: the (diagonal) Hessian entries of `F_m` are strictly positive:
`∂²F_m/∂z_i² = 2m(2m-1)z^{2m-2} + 2/m > 0` for `m ≥ 1`. -/
theorem Fm_hessian_diag_pos {m : ℕ} (hm : 1 ≤ m) (z : ℝ) :
    0 < 2 * (m : ℝ) * (2 * (m : ℝ) - 1) * z ^ (2 * m - 2) + 2 / (m : ℝ) := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : 0 ≤ z ^ (2 * m - 2) := Even.pow_nonneg ⟨m - 1, by omega⟩ z
  have h2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ 2 * (m : ℝ) * (2 * (m : ℝ) - 1) := by nlinarith
  nlinarith

/-- Prop 4.1: `F_m` is strictly convex on `ℝ⁹` (for `m ≥ 1`). -/
theorem Fm_strictConvexOn {m : ℕ} (hm : 1 ≤ m) :
    StrictConvexOn ℝ Set.univ (Fm m) := by
  have hg : StrictConvexOn ℝ Set.univ
      (fun t : ℝ => t ^ (2 * m) + (1 / (m : ℝ)) * t ^ 2) := by
    have h1 : StrictConvexOn ℝ Set.univ (fun t : ℝ => t ^ (2 * m)) :=
      Even.strictConvexOn_pow (even_two_mul m) (by omega)
    have h2 : ConvexOn ℝ Set.univ (fun t : ℝ => (1 / (m : ℝ)) * t ^ 2) := by
      have h3 : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) :=
        (Even.strictConvexOn_pow even_two two_ne_zero).convexOn
      have h4 := h3.smul (c := 1 / (m : ℝ)) (by positivity)
      simpa [smul_eq_mul] using h4
    have h5 := h1.add_convexOn h2
    simpa [Pi.add_def] using h5
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hxy
  have hsum : ∀ i : Fin 9,
      (a * x i + b * y i) ^ (2 * m) + (1 / (m : ℝ)) * (a * x i + b * y i) ^ 2
        ≤ a * (x i ^ (2 * m) + (1 / (m : ℝ)) * x i ^ 2)
          + b * (y i ^ (2 * m) + (1 / (m : ℝ)) * y i ^ 2) := by
    intro i
    have h := hg.convexOn.2 (Set.mem_univ (x i)) (Set.mem_univ (y i)) ha.le hb.le hab
    simpa [smul_eq_mul] using h
  have hstrict :
      (a * x j + b * y j) ^ (2 * m) + (1 / (m : ℝ)) * (a * x j + b * y j) ^ 2
        < a * (x j ^ (2 * m) + (1 / (m : ℝ)) * x j ^ 2)
          + b * (y j ^ (2 * m) + (1 / (m : ℝ)) * y j ^ 2) := by
    have h := hg.2 (Set.mem_univ (x j)) (Set.mem_univ (y j)) hj ha hb hab
    simpa [smul_eq_mul] using h
  have hpt : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by
    simp [smul_eq_mul]
  calc Fm m (a • x + b • y)
      = ∑ i, ((a * x i + b * y i) ^ (2 * m)
          + (1 / (m : ℝ)) * (a * x i + b * y i) ^ 2) := by
        unfold Fm
        exact Finset.sum_congr rfl fun i _ => by rw [hpt i]
    _ < ∑ i, (a * (x i ^ (2 * m) + (1 / (m : ℝ)) * x i ^ 2)
          + b * (y i ^ (2 * m) + (1 / (m : ℝ)) * y i ^ 2)) :=
        Finset.sum_lt_sum (fun i _ => hsum i) ⟨j, Finset.mem_univ j, hstrict⟩
    _ = a • Fm m x + b • Fm m y := by
        unfold Fm
        rw [smul_eq_mul, smul_eq_mul, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]

/-- Prop 4.1: on the level set `F_m = 1` one has
`z·∇F_m(z) = 2m Σ z_i^{2m} + (2/m) Σ z_i² > 0`, so the gradient of `F_m` never
vanishes on `∂C_m` (whence the boundary is smooth). -/
theorem Fm_radial_deriv_pos {m : ℕ} (hm : 1 ≤ m) (z : Fin 9 → ℝ)
    (hz : Fm m z = 1) :
    0 < 2 * (m : ℝ) * ∑ i, z i ^ (2 * m) + (2 / (m : ℝ)) * ∑ i, z i ^ 2 := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hS1 : 0 ≤ ∑ i, z i ^ (2 * m) :=
    Finset.sum_nonneg fun i _ => Even.pow_nonneg (even_two_mul m) _
  have hS2 : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hFm : Fm m z = (∑ i, z i ^ (2 * m)) + (1 / (m : ℝ)) * ∑ i, z i ^ 2 := by
    unfold Fm
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hzsum : (∑ i, z i ^ (2 * m)) + (1 / (m : ℝ)) * ∑ i, z i ^ 2 = 1 := by
    rw [← hFm]
    exact hz
  have hu : 0 ≤ (1 / (m : ℝ)) * ∑ i, z i ^ 2 := by positivity
  have hcoef : (2 / (m : ℝ)) * ∑ i, z i ^ 2
      = 2 * ((1 / (m : ℝ)) * ∑ i, z i ^ 2) := by ring
  rw [hcoef]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1) hS1]

/-- Prop 4.1, first containment, in `z`-coordinates: `C_m ⊆ Q`, i.e. if
`F_m(z) ≤ 1` then `|z_i| ≤ 1` for every `i`. -/
theorem Fm_sublevel_subset_cube {m : ℕ} (hm : 1 ≤ m) {z : Fin 9 → ℝ}
    (hz : Fm m z ≤ 1) (i : Fin 9) : |z i| ≤ 1 := by
  have hterm : ∀ j : Fin 9, 0 ≤ z j ^ (2 * m) + (1 / (m : ℝ)) * z j ^ 2 := by
    intro j
    have h1 : 0 ≤ z j ^ (2 * m) := Even.pow_nonneg (even_two_mul m) _
    have h2 : 0 ≤ (1 / (m : ℝ)) * z j ^ 2 := by positivity
    linarith
  have hle : z i ^ (2 * m) + (1 / (m : ℝ)) * z i ^ 2 ≤ 1 :=
    le_trans (Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)) hz
  have h1 : z i ^ (2 * m) ≤ 1 := by
    have h2 : 0 ≤ (1 / (m : ℝ)) * z i ^ 2 := by positivity
    linarith
  have h2 : |z i| ^ (2 * m) ≤ 1 := by
    rwa [Even.pow_abs (even_two_mul m)]
  exact (pow_le_one_iff_of_nonneg (abs_nonneg _) (by omega)).1 h2

/-- Prop 4.1, second containment, in `z`-coordinates, eventually in `m`:
for `0 < η < 1` and all sufficiently large `m`, every `z` with `|z_i| ≤ 1-η`
satisfies `F_m(z) < 1` (i.e. `(1-η)Q ⊆ interior C_m`); the quantitative bound is
`F_m(z) ≤ 9(1-η)^{2m} + (9/m)(1-η)² < 1` as in the paper. -/
theorem cube_scaled_eventually_subset {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ∀ z : Fin 9 → ℝ, (∀ i, |z i| ≤ 1 - η) → Fm m z < 1 := by
  have hr0 : (0 : ℝ) ≤ (1 - η) ^ 2 := sq_nonneg _
  have hr1 : (1 - η) ^ 2 < 1 := by nlinarith
  have ht1 : Filter.Tendsto (fun m : ℕ => ((1 - η) ^ 2) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have ht2 : Filter.Tendsto (fun m : ℕ => (9 : ℝ) / m) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 9
  have ht : Filter.Tendsto
      (fun m : ℕ => 9 * ((1 - η) ^ 2) ^ m + ((9 : ℝ) / m) * (1 - η) ^ 2)
      Filter.atTop (nhds 0) := by
    have h := (ht1.const_mul 9).add (ht2.mul_const ((1 - η) ^ 2))
    simpa using h
  filter_upwards [ht.eventually_lt_const one_pos, Filter.eventually_ge_atTop 1]
    with m hlt hm1
  intro z hzb
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hb1 : ∀ i : Fin 9, z i ^ (2 * m) ≤ ((1 - η) ^ 2) ^ m := by
    intro i
    have h := pow_le_pow_left₀ (abs_nonneg _) (hzb i) (2 * m)
    rw [Even.pow_abs (even_two_mul m)] at h
    calc z i ^ (2 * m) ≤ (1 - η) ^ (2 * m) := h
      _ = ((1 - η) ^ 2) ^ m := by rw [← pow_mul]
  have hb2 : ∀ i : Fin 9, z i ^ 2 ≤ (1 - η) ^ 2 := by
    intro i
    have h := pow_le_pow_left₀ (abs_nonneg _) (hzb i) 2
    rwa [sq_abs] at h
  have hsum : Fm m z ≤ 9 * ((1 - η) ^ 2) ^ m + ((9 : ℝ) / m) * (1 - η) ^ 2 := by
    unfold Fm
    calc ∑ i, (z i ^ (2 * m) + (1 / (m : ℝ)) * z i ^ 2)
        ≤ ∑ _i : Fin 9, (((1 - η) ^ 2) ^ m + (1 / (m : ℝ)) * (1 - η) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          have h4 : (1 / (m : ℝ)) * z i ^ 2 ≤ (1 / (m : ℝ)) * (1 - η) ^ 2 :=
            mul_le_mul_of_nonneg_left (hb2 i) (by positivity)
          linarith [hb1 i]
      _ = 9 * ((1 - η) ^ 2) ^ m + ((9 : ℝ) / m) * (1 - η) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  linarith

/-! ## Theorem 1.2 (thm:smooth) -/

/-- `F_m` is infinitely differentiable (a polynomial), the smoothness half of
"∂C_m is a smooth hypersurface": together with the nonvanishing gradient on the
level set (`Fm_radial_deriv_pos`) this is what the implicit function theorem
consumes. -/
theorem Fm_contDiff (m : ℕ) : ContDiff ℝ ⊤ (Fm m) := by
  unfold Fm
  exact ContDiff.sum fun i _ =>
    ((ContinuousLinearMap.proj i : (Fin 9 → ℝ) →L[ℝ] ℝ).contDiff.pow _).add
      (contDiff_const.mul
        ((ContinuousLinearMap.proj i : (Fin 9 → ℝ) →L[ℝ] ℝ).contDiff.pow _))

/-- The approximant body `C_m` of eq:smooth-approximation realized in Euclidean
`x`-space: `F_m` is written in the paper's `z`-coordinates, related to ambient
coordinates by the homothety `x = (12/5) z` (so that `{|z_i| ≤ 1}` corresponds to
the cube `Q = [-12/5, 12/5]⁹` whose Huisken energy is `18 e^{-36/25} erf(6/5)^8`).
Hence `C_m = { x | F_m((5/12)x) ≤ 1 }`, with Euclidean norm and Hausdorff measure. -/
noncomputable def bodyE (m : ℕ) : Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | Fm m (fun i => (5 / 12) * x.ofLp i) ≤ 1}

/-- The Huisken boundary energy `H_ADS(C_m) = (4π)^{-4} ∫_{∂C_m} e^{-|x|²/4} dH^8`
of the approximant body — the paper's defining formula, transcribed with Mathlib's
`8`-dimensional Hausdorff measure `μH[8]` on Euclidean `ℝ⁹` and the Euclidean norm. -/
noncomputable def huiskenEnergy (m : ℕ) : ℝ :=
  (((4 : ℝ) * π) ^ 4)⁻¹ *
    ∫ x in frontier (bodyE m), exp (-‖x‖ ^ 2 / 4) ∂μH[8]

/-- Theorem 1.2 (thm:smooth), modulo the continuity of the Huisken energy under
(local) Hausdorff convergence of convex bodies ([ADS, Lemma 3.6], not available
in Mathlib; it enters as the hypothesis `hconv`): the genuine Huisken energies
`huiskenEnergy m` of the bodies `C_m = {F_m ≤ 1}` (defined above by the paper's
integral formula, not a free parameter) converge to
`H_ADS(Q) = 18 e^{-36/25} erf(6/5)^8` — the convergence justified geometrically by
the Hausdorff convergence `C_m → Q` certified below.

The conclusion is about the *constructed body itself*: there is an index `m ≥ 1`
whose body `C_m` is strictly convex (`Fm_strictConvexOn`, genuinely proved),
contained in the unit cube `Q` (`Fm_sublevel_subset_cube`, proved), contains the
shrunken cube `(1-η)Q` (`cube_scaled_eventually_subset`, proved — this pair is
the Hausdorff convergence `C_m → Q`), and has Huisken energy
`huiskenEnergy m > 2`. -/
theorem thm_smooth
    (hconv : Filter.Tendsto huiskenEnergy Filter.atTop
      (nhds (18 * exp (-(36 / 25)) * erf (6 / 5) ^ 8)))
    {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    ∃ m, 1 ≤ m
      -- smoothness of the defining function (with the nonvanishing gradient below,
      -- the two implicit-function-theorem inputs for smoothness of ∂C_m):
      ∧ ContDiff ℝ ⊤ (Fm m)
      -- strict convexity of F_m — with the positive Hessian this is the
      -- positive-principal-curvature mechanism:
      ∧ StrictConvexOn ℝ Set.univ (Fm m)
      -- everywhere-positive Hessian diagonal (Prop 4.1's curvature input):
      ∧ (∀ z : ℝ, 0 < 2 * (m : ℝ) * (2 * (m : ℝ) - 1) * z ^ (2 * m - 2) + 2 / (m : ℝ))
      -- the gradient is nonvanishing on ∂C_m = {F_m = 1} (radial derivative > 0):
      ∧ (∀ z : Fin 9 → ℝ, Fm m z = 1 →
          0 < 2 * (m : ℝ) * ∑ i, z i ^ (2 * m) + (2 / (m : ℝ)) * ∑ i, z i ^ 2)
      ∧ (∀ z : Fin 9 → ℝ, Fm m z ≤ 1 → ∀ i, |z i| ≤ 1)
      ∧ (∀ z : Fin 9 → ℝ, (∀ i, |z i| ≤ 1 - η) → Fm m z < 1)
      ∧ 2 < huiskenEnergy m := by
  have h2 : ∀ᶠ m : ℕ in Filter.atTop, 2 < huiskenEnergy m :=
    hconv.eventually_const_lt huisken_cube_nine_gt_two
  have hη := cube_scaled_eventually_subset h0 h1
  have hone : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ m := Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩
  obtain ⟨m, hm1, hmη, hm2⟩ := (hone.and (hη.and h2)).exists
  exact ⟨m, hm1, Fm_contDiff m, Fm_strictConvexOn hm1,
    fun z => Fm_hessian_diag_pos hm1 z,
    fun z hz => Fm_radial_deriv_pos hm1 z hz,
    fun z hz i => Fm_sublevel_subset_cube hm1 hz i, hmη, hm2⟩

end HuiskenEnergy
