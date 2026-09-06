import Mathlib

/-!
# A Counterexample at the Omitted Parameter in an Affine-Maximal Bernstein Statement

Lean certification of `affine_maximal_omitted_parameter.tex`.

For a smooth strictly convex `f : ℝ² → ℝ` write `D = det D²f` and `L_f u = f^{ij} u_{ij}`,
where `(f^{ij}) = (D²f)⁻¹` (eq. (1) of the paper), and let `G_f = f_{ij} dx^i dx^j` be the
Calabi (Hessian) metric (eq. (2)).  The paper shows that if the standing assumption `a ≠ 0`
is dropped from the Sun–Xu affine-maximal Bernstein statement (quadratic rigidity for
`a ∉ [-2/3, -1/3]`), the statement becomes false: at `a = 0` the equation `L_f (D^a) = 0`
is vacuous, and the explicit nonquadratic potential

  `f (x, y) = ½ (x² + y²) + x⁴`   (eq. (4))

is smooth, strictly convex, and has a complete Calabi metric.

## Formalization map (tex ↔ Lean)

* eq. (1), `L_f u = f^{ij} u_{ij}` — `LOp` (built from `pderiv`, `hessOf`), transcribed
  via genuine Fréchet derivatives.
* eq. (2), Calabi metric — transcribed as the length functional of `C¹` curves through the
  Hessian quadratic form: `speed`, `lengths`, `calabiDist`.  (Mathlib's
  `Geometry.Manifold.Riemannian` has Riemannian metrics but no completeness transfer
  criterion, so completeness is stated directly for Cauchy sequences of `calabiDist`,
  exactly following the paper's proof.)
* eq. (4) and `D² f = diag (1 + 12x², 1)`, `D = 1 + 12x²` — `f`, `hessOf_f`,
  `det_hessOf_f`, certified by explicit `HasFDerivAt` computations.
* Strict convexity — `strictConvexOn_f`; positive definiteness — `hessOf_f_posDef`.
* Nonquadratic — `f_not_quadratic`.
* `L_f (D⁰) = L_f 1 = 0` — `pde_f_at_zero` (and `LOp_const`, the Remark: the `a = 0`
  equation is vacuous for *every* potential).
* Completeness of `G_f` (the display `Length_{G_f} γ ≥ Length_Euc γ`, the Cauchy-sequence
  argument) — `dist_le_integral_speed`, `dist_le_calabiDist`, `calabiDist_le_mul_dist`,
  `calabiComplete_f`.
* Theorem 1 — `theorem_one`; the concluding sentence ("any formulation that includes
  `a = 0` is false") — `bernstein_fails_at_zero` and `omitted_parameter_statement_false`,
  with the Bernstein assertion transcribed as `BernsteinAssertion`.
-/

namespace AffineMaximalOmittedParameter

open Set Filter Matrix intervalIntegral
open scoped ContDiff Topology

/-! ## Generic second-order machinery (§1 of the paper)

Everything in this section is stated for an arbitrary potential `g : ℝ × ℝ → ℝ`, so that
the Bernstein assertion itself can be transcribed faithfully. -/

/-- The coordinate basis vectors of `ℝ²`. -/
def e : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

/-- `pderiv i u` is the `i`-th partial derivative `u_i` of `u : ℝ² → ℝ`, defined through the
Fréchet derivative. -/
noncomputable def pderiv (i : Fin 2) (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ u p (e i)

/-- The Hessian matrix `(u_{ij})` of `u : ℝ² → ℝ`. -/
noncomputable def hessOf (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => pderiv i (pderiv j u) p

/-- Eq. (1): the affine-maximal-type operator `L_g u = g^{ij} u_{ij}`, where
`(g^{ij}) = (D²g)⁻¹` is the inverse Hessian. -/
noncomputable def LOp (g u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ i, ∑ j, (hessOf g p)⁻¹ i j * pderiv i (pderiv j u) p

/-- Eq. (2): the Calabi metric `G_g = g_{ij} dx^i dx^j`, as the length
`√(G_g(v, v)) = √(vᵀ (D²g) v)` of a tangent vector `v` at `p`. -/
noncomputable def speed (g : ℝ × ℝ → ℝ) (p v : ℝ × ℝ) : ℝ :=
  Real.sqrt (![v.1, v.2] ⬝ᵥ (hessOf g p *ᵥ ![v.1, v.2]))

/-- The set of `G_g`-lengths of `C¹` curves joining `p` to `q` (parametrized on `[0,1]`);
this transcribes `Length_{G_g}(γ) = ∫ √(G_g(γ', γ'))` from the paper's completeness proof. -/
def lengths (g : ℝ × ℝ → ℝ) (p q : ℝ × ℝ) : Set ℝ :=
  {l | ∃ γ γ' : ℝ → ℝ × ℝ,
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (γ' t) t) ∧ ContinuousOn γ' (Icc 0 1) ∧
    γ 0 = p ∧ γ 1 = q ∧ l = ∫ t in (0 : ℝ)..1, speed g (γ t) (γ' t)}

/-- The Calabi (path) distance: infimum of Calabi lengths of curves joining `p` to `q`. -/
noncomputable def calabiDist (g : ℝ × ℝ → ℝ) (p q : ℝ × ℝ) : ℝ :=
  sInf (lengths g p q)

/-- Completeness of the Calabi metric of `g`, phrased for Cauchy sequences of the path
distance `calabiDist g` (as in the paper: "every `G_f`-Cauchy sequence … converges … also
in `G_f`"). -/
def CalabiComplete (g : ℝ × ℝ → ℝ) : Prop :=
  ∀ u : ℕ → ℝ × ℝ,
    (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, calabiDist g (u m) (u n) < ε) →
    ∃ L : ℝ × ℝ, Tendsto (fun n => calabiDist g (u n) L) atTop (𝓝 0)

/-- `g` is a quadratic polynomial on `ℝ²`. -/
def IsQuadratic (g : ℝ × ℝ → ℝ) : Prop :=
  ∃ A B C A₁ B₁ A₀ : ℝ, ∀ x y : ℝ,
    g (x, y) = A * x ^ 2 + B * x * y + C * y ^ 2 + A₁ * x + B₁ * y + A₀

/-- The Bernstein assertion at parameter `a`, transcribed in this framework for entire
potentials on `ℝ²`: every smooth strictly convex potential solving `L_g (D^a) = 0`
(eq. (1)) whose Calabi metric is complete must be quadratic.  The Sun–Xu conjecture
concerns `a ∉ [-2/3, -1/3]` **with the standing assumption `a ≠ 0`**; the paper shows the
assertion is false if `a = 0` is allowed. -/
def BernsteinAssertion (a : ℝ) : Prop :=
  ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g → StrictConvexOn ℝ univ g →
    (∀ p : ℝ × ℝ, LOp g (fun q => (hessOf g q).det ^ a) p = 0) →
    CalabiComplete g → IsQuadratic g

/-! ## The `a = 0` equation is vacuous (Remark 2 and the display `L_f(D⁰) = L_f(1) = 0`) -/

/-- Partial derivatives annihilate constants. -/
theorem pderiv_const (i : Fin 2) (c : ℝ) : pderiv i (fun _ : ℝ × ℝ => c) = fun _ => 0 := by
  funext p
  simp [pderiv]

/-- Remark 2: at `a = 0` the equation is vacuous — `L_g` annihilates constants for **every**
potential `g` (indeed `f^{ij} (1)_{ij} = 0` regardless of the coefficients). -/
theorem LOp_const (g : ℝ × ℝ → ℝ) (c : ℝ) (p : ℝ × ℝ) : LOp g (fun _ => c) p = 0 := by
  simp [LOp, pderiv_const]

/-! ## The counterexample potential (eq. (4)) -/

/-- Eq. (4): `f (x, y) = ½ (x² + y²) + x⁴`. -/
noncomputable def f (p : ℝ × ℝ) : ℝ := (p.1 ^ 2 + p.2 ^ 2) / 2 + p.1 ^ 4

/-- `f` is smooth ("`f` is smooth and strictly convex"). -/
theorem contDiff_f : ContDiff ℝ ∞ f := by
  unfold f
  fun_prop

/-- First derivative of `f`: `∇f (x, y) = (x + 4x³, y)`, certified as a Fréchet
derivative. -/
theorem hasFDerivAt_f (p : ℝ × ℝ) :
    HasFDerivAt f
      ((p.1 + 4 * p.1 ^ 3) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hrw : f = fun q : ℝ × ℝ => 2⁻¹ * (q.1 ^ 2 + q.2 ^ 2) + q.1 ^ 4 := by
    funext q
    simp only [f]
    ring
  rw [hrw]
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have h := (((h1.pow 2).add (h2.pow 2)).const_mul (2⁻¹ : ℝ)).add (h1.pow 4)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp
  ring

/-- `∂f/∂x = x + 4x³`. -/
theorem pderiv_fst_f : pderiv 0 f = fun p : ℝ × ℝ => p.1 + 4 * p.1 ^ 3 := by
  funext p
  rw [pderiv, (hasFDerivAt_f p).fderiv]
  simp [e]

/-- `∂f/∂y = y`. -/
theorem pderiv_snd_f : pderiv 1 f = fun p : ℝ × ℝ => p.2 := by
  funext p
  rw [pderiv, (hasFDerivAt_f p).fderiv]
  simp [e]

/-- Second derivative of `x ↦ x + 4x³` in the plane, certified as a Fréchet derivative. -/
theorem hasFDerivAt_pderiv_fst_f (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => q.1 + 4 * q.1 ^ 3)
      ((1 + 12 * p.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have h := h1.add ((h1.pow 3).const_mul (4 : ℝ))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp
  ring

/-- The Hessian computation of the paper: `D²f = diag (1 + 12x², 1)`. -/
theorem hessOf_f (p : ℝ × ℝ) : hessOf f p = !![1 + 12 * p.1 ^ 2, 0; 0, 1] := by
  have hsnd : fderiv ℝ (fun q : ℝ × ℝ => q.2) p = ContinuousLinearMap.snd ℝ ℝ ℝ :=
    HasFDerivAt.fderiv hasFDerivAt_snd
  have h00 : hessOf f p 0 0 = 1 + 12 * p.1 ^ 2 := by
    simp only [hessOf, Matrix.of_apply, pderiv_fst_f, pderiv,
      (hasFDerivAt_pderiv_fst_f p).fderiv]
    simp [e]
  have h01 : hessOf f p 0 1 = 0 := by
    simp only [hessOf, Matrix.of_apply, pderiv_snd_f, pderiv, hsnd]
    simp [e]
  have h10 : hessOf f p 1 0 = 0 := by
    simp only [hessOf, Matrix.of_apply, pderiv_fst_f, pderiv,
      (hasFDerivAt_pderiv_fst_f p).fderiv]
    simp [e]
  have h11 : hessOf f p 1 1 = 1 := by
    simp only [hessOf, Matrix.of_apply, pderiv_snd_f, pderiv, hsnd]
    simp [e]
  rw [Matrix.eta_fin_two (hessOf f p), h00, h01, h10, h11]

/-- `D = det D²f = 1 + 12x²`. -/
theorem det_hessOf_f (p : ℝ × ℝ) : (hessOf f p).det = 1 + 12 * p.1 ^ 2 := by
  rw [hessOf_f]
  simp [Matrix.det_fin_two_of]

/-- `D > 0` everywhere. -/
theorem det_hessOf_f_pos (p : ℝ × ℝ) : 0 < (hessOf f p).det := by
  rw [det_hessOf_f]
  positivity

/-- "`D²f` is positive definite at every point". -/
theorem hessOf_f_posDef (p : ℝ × ℝ) : (hessOf f p).PosDef := by
  rw [hessOf_f]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hs : star x = x := by
      ext i
      simp
    have hexp : x ⬝ᵥ ((!![1 + 12 * p.1 ^ 2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x)
        = (1 + 12 * p.1 ^ 2) * x 0 ^ 2 + x 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [hs, hexp]
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      fin_cases i
      · exact Or.inl (by simpa using hi)
      · exact Or.inr (by simpa using hi)
    rcases hx' with h | h
    · nlinarith [pow_two_pos_of_ne_zero h, sq_nonneg (x 1), sq_nonneg (p.1 * x 0)]
    · nlinarith [pow_two_pos_of_ne_zero h, sq_nonneg (x 0), sq_nonneg (p.1 * x 0)]

/-- The inverse Hessian `(f^{ij}) = diag ((1 + 12x²)⁻¹, 1)` entering eq. (1). -/
theorem inv_hessOf_f (p : ℝ × ℝ) :
    (hessOf f p)⁻¹ = !![(1 + 12 * p.1 ^ 2)⁻¹, 0; 0, 1] := by
  have hne : (1 : ℝ) + 12 * p.1 ^ 2 ≠ 0 := by positivity
  rw [hessOf_f, Matrix.inv_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.det_fin_two_of, inv_mul_cancel₀ hne]

/-! ## `f` is strictly convex (via 1-D slices and the second-derivative test) -/

private theorem slice1_deriv (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 / 2 + t ^ 4) (x + 4 * x ^ 3) x := by
  have h := ((hasDerivAt_pow 2 x).div_const 2).add (hasDerivAt_pow 4 x)
  convert h using 1
  push_cast
  ring

private theorem slice1_deriv2 (x : ℝ) :
    HasDerivAt (fun t : ℝ => t + 4 * t ^ 3) (1 + 12 * x ^ 2) x := by
  have h := (hasDerivAt_id x).add ((hasDerivAt_pow 3 x).const_mul (4 : ℝ))
  convert h using 1
  push_cast
  ring

private theorem slice2_deriv (y : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
  have h := (hasDerivAt_pow 2 y).div_const 2
  convert h using 1
  push_cast
  ring

/-- The slice `t ↦ t²/2 + t⁴` is strictly convex (`(t²/2 + t⁴)'' = 1 + 12t² > 0`). -/
theorem strictConvexOn_slice1 : StrictConvexOn ℝ univ fun t : ℝ => t ^ 2 / 2 + t ^ 4 := by
  refine strictConvexOn_of_deriv2_pos convex_univ (by fun_prop) fun x _ => ?_
  have e1 : deriv (fun t : ℝ => t ^ 2 / 2 + t ^ 4) = fun t => t + 4 * t ^ 3 :=
    funext fun t => (slice1_deriv t).deriv
  have e2 : deriv^[2] (fun t : ℝ => t ^ 2 / 2 + t ^ 4) x
      = deriv (deriv fun t : ℝ => t ^ 2 / 2 + t ^ 4) x := rfl
  rw [e2, e1, (slice1_deriv2 x).deriv]
  positivity

/-- The slice `t ↦ t²/2` is strictly convex. -/
theorem strictConvexOn_slice2 : StrictConvexOn ℝ univ fun t : ℝ => t ^ 2 / 2 := by
  refine strictConvexOn_of_deriv2_pos convex_univ (by fun_prop) fun x _ => ?_
  have e1 : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t := funext fun t => (slice2_deriv t).deriv
  have e2 : deriv^[2] (fun t : ℝ => t ^ 2 / 2) x = deriv (deriv fun t : ℝ => t ^ 2 / 2) x := rfl
  rw [e2, e1]
  simp

/-- "`f` is smooth and strictly convex". -/
theorem strictConvexOn_f : StrictConvexOn ℝ univ f := by
  refine ⟨convex_univ, ?_⟩
  rintro ⟨px, py⟩ - ⟨qx, qy⟩ - hne a b ha hb hab
  rw [Ne, Prod.mk.injEq, not_and_or] at hne
  have hgoal : f (a • (px, py) + b • (qx, qy))
      = ((a * px + b * qx) ^ 2 / 2 + (a * px + b * qx) ^ 4) + (a * py + b * qy) ^ 2 / 2 := by
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, f]
    ring
  have hfp : f (px, py) = (px ^ 2 / 2 + px ^ 4) + py ^ 2 / 2 := by
    simp only [f]
    ring
  have hfq : f (qx, qy) = (qx ^ 2 / 2 + qx ^ 4) + qy ^ 2 / 2 := by
    simp only [f]
    ring
  rw [hgoal, smul_eq_mul, smul_eq_mul, hfp, hfq]
  rcases hne with h | h
  · have c1 : (a * px + b * qx) ^ 2 / 2 + (a * px + b * qx) ^ 4
        < a * (px ^ 2 / 2 + px ^ 4) + b * (qx ^ 2 / 2 + qx ^ 4) := by
      simpa [smul_eq_mul] using
        strictConvexOn_slice1.2 (mem_univ px) (mem_univ qx) h ha hb hab
    have c2 : (a * py + b * qy) ^ 2 / 2 ≤ a * (py ^ 2 / 2) + b * (qy ^ 2 / 2) := by
      simpa [smul_eq_mul] using
        strictConvexOn_slice2.convexOn.2 (mem_univ py) (mem_univ qy) ha.le hb.le hab
    nlinarith [c1, c2]
  · have c1 : (a * px + b * qx) ^ 2 / 2 + (a * px + b * qx) ^ 4
        ≤ a * (px ^ 2 / 2 + px ^ 4) + b * (qx ^ 2 / 2 + qx ^ 4) := by
      simpa [smul_eq_mul] using
        strictConvexOn_slice1.convexOn.2 (mem_univ px) (mem_univ qx) ha.le hb.le hab
    have c2 : (a * py + b * qy) ^ 2 / 2 < a * (py ^ 2 / 2) + b * (qy ^ 2 / 2) := by
      simpa [smul_eq_mul] using
        strictConvexOn_slice2.2 (mem_univ py) (mem_univ qy) h ha hb hab
    nlinarith [c1, c2]

/-! ## `f` is nonquadratic ("It is plainly nonquadratic") -/

theorem f_not_quadratic : ¬ IsQuadratic f := by
  rintro ⟨A, B, C, A₁, B₁, A₀, h⟩
  have h0 := h 0 0
  have h1 := h 1 0
  have hm := h (-1) 0
  have h2 := h 2 0
  simp only [f] at h0 h1 hm h2
  norm_num at h0 h1 hm h2
  linarith

/-! ## The PDE at `a = 0`: `L_f (D⁰) = L_f 1 = 0` -/

/-- The display of the paper's proof: at `a = 0` one has `D⁰ ≡ 1` (`Real.rpow_zero`), hence
`L_f (D⁰) = L_f 1 = f^{ij} (1)_{ij} = 0`, and eq. (1) is satisfied identically. -/
theorem pde_f_at_zero (p : ℝ × ℝ) :
    LOp f (fun q => (hessOf f q).det ^ (0 : ℝ)) p = 0 := by
  have h : (fun q : ℝ × ℝ => (hessOf f q).det ^ (0 : ℝ)) = fun _ => (1 : ℝ) :=
    funext fun q => Real.rpow_zero _
  rw [h]
  exact LOp_const f 1 p

/-! ## Completeness of the Calabi metric

This section follows the paper's proof verbatim: from `D²f ≥ I` (as quadratic forms), every
`C¹` curve satisfies `Length_{G_f}(γ) ≥ Length_Euc(γ) ≥ dist(endpoints)`, so the identity
map `(ℝ², G_f) → (ℝ², Euclid)` is distance nonincreasing; a `G_f`-Cauchy sequence is
Euclidean-Cauchy, hence converges to some `L`, and near `L` the metric `G_f` is uniformly
comparable to the Euclidean one (via the straight segment), so convergence holds in `G_f`
too. -/

/-- The Calabi quadratic form of `f`: `G_f(v,v) = (1 + 12x²) v₁² + v₂²` at `p = (x, y)`. -/
theorem speed_f (p v : ℝ × ℝ) :
    speed f p v = Real.sqrt ((1 + 12 * p.1 ^ 2) * v.1 ^ 2 + v.2 ^ 2) := by
  rw [speed, hessOf_f]
  congr 1
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- `D²f ≥ I` as quadratic forms: the Calabi speed dominates the (sup-product) norm of the
tangent vector.  This is the pointwise form of the display
`Length_{G_f}(γ) ≥ Length_Euc(γ)`. -/
theorem norm_le_speed_f (p v : ℝ × ℝ) : ‖v‖ ≤ speed f p v := by
  rw [speed_f, Prod.norm_def]
  have h1 : ‖v.1‖ ≤ Real.sqrt ((1 + 12 * p.1 ^ 2) * v.1 ^ 2 + v.2 ^ 2) := by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v.2, sq_nonneg (p.1 * v.1)])
  have h2 : ‖v.2‖ ≤ Real.sqrt ((1 + 12 * p.1 ^ 2) * v.1 ^ 2 + v.2 ^ 2) := by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v.1, sq_nonneg (p.1 * v.1)])
  exact max_le h1 h2

theorem speed_f_nonneg (p v : ℝ × ℝ) : 0 ≤ speed f p v := by
  rw [speed_f]
  exact Real.sqrt_nonneg _

/-- Continuity of the Calabi speed along a curve. -/
theorem continuousOn_speed_f {γ γ' : ℝ → ℝ × ℝ} {s : Set ℝ}
    (hγ : ContinuousOn γ s) (hγ' : ContinuousOn γ' s) :
    ContinuousOn (fun t => speed f (γ t) (γ' t)) s := by
  simp only [speed_f]
  apply Real.continuous_sqrt.comp_continuousOn
  fun_prop

/-- The key display of the completeness proof: for every `C¹` curve `γ`,
`dist (γ 0) (γ 1) ≤ Length_Euc(γ) ≤ Length_{G_f}(γ)`. -/
theorem dist_le_integral_speed {γ γ' : ℝ → ℝ × ℝ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) :
    dist (γ 0) (γ 1) ≤ ∫ t in (0 : ℝ)..1, speed f (γ t) (γ' t) := by
  have hu : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hγc : ContinuousOn γ (Icc (0 : ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hi1 : IntervalIntegrable γ' MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [hu]
  have hftc : ∫ t in (0 : ℝ)..1, γ' t = γ 1 - γ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hγ t (hu ▸ ht)) hi1
  calc dist (γ 0) (γ 1) = ‖γ 1 - γ 0‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ = ‖∫ t in (0 : ℝ)..1, γ' t‖ := by rw [hftc]
    _ ≤ ∫ t in (0 : ℝ)..1, ‖γ' t‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, speed f (γ t) (γ' t) := by
        apply intervalIntegral.integral_mono_on zero_le_one
          (by apply ContinuousOn.intervalIntegrable; rw [hu]; exact hγ'.norm)
          (by apply ContinuousOn.intervalIntegrable; rw [hu]
              exact continuousOn_speed_f hγc hγ')
        exact fun t _ => norm_le_speed_f (γ t) (γ' t)

/-- The straight segment from `p` to `q` realizes an element of `lengths f p q`. -/
theorem segment_mem_lengths (p q : ℝ × ℝ) :
    (∫ t in (0 : ℝ)..1, speed f (p + t • (q - p)) (q - p)) ∈ lengths f p q := by
  refine ⟨fun t => p + t • (q - p), fun _ => q - p, fun t _ => ?_, continuousOn_const,
    by simp, by simp, rfl⟩
  simpa using ((hasDerivAt_id t).smul_const (q - p)).const_add p

/-- Every element of `lengths f p q` dominates the Euclidean distance. -/
theorem dist_le_of_mem_lengths {p q : ℝ × ℝ} {l : ℝ} (hl : l ∈ lengths f p q) :
    dist p q ≤ l := by
  obtain ⟨γ, γ', hγ, hγ', h0, h1, rfl⟩ := hl
  rw [← h0, ← h1]
  exact dist_le_integral_speed hγ hγ'

theorem lengths_nonempty (p q : ℝ × ℝ) : (lengths f p q).Nonempty :=
  ⟨_, segment_mem_lengths p q⟩

theorem lengths_bddBelow (p q : ℝ × ℝ) : BddBelow (lengths f p q) :=
  ⟨dist p q, fun _ hl => dist_le_of_mem_lengths hl⟩

/-- "The identity map `(ℝ², G_f) → (ℝ², g_Euc)` is distance nonincreasing." -/
theorem dist_le_calabiDist (p q : ℝ × ℝ) : dist p q ≤ calabiDist f p q :=
  le_csInf (lengths_nonempty p q) fun _ hl => dist_le_of_mem_lengths hl

/-- Local comparability in the other direction ("on a Euclidean compact neighborhood …,
`G_f` is uniformly equivalent to the Euclidean metric"): the straight segment bounds the
Calabi distance by an explicit multiple of the Euclidean distance. -/
theorem calabiDist_le_mul_dist (p q : ℝ × ℝ) :
    calabiDist f p q ≤ Real.sqrt (2 * (1 + 12 * (|p.1| + |q.1|) ^ 2)) * dist p q := by
  set C := Real.sqrt (2 * (1 + 12 * (|p.1| + |q.1|) ^ 2)) with hC
  have key : ∀ t ∈ Icc (0 : ℝ) 1, speed f (p + t • (q - p)) (q - p) ≤ C * dist p q := by
    intro t ht
    rw [speed_f]
    have hx : |(p + t • (q - p)).1| ≤ |p.1| + |q.1| := by
      have hfst : (p + t • (q - p)).1 = (1 - t) * p.1 + t * q.1 := by
        simp [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        ring
      rw [hfst]
      calc |(1 - t) * p.1 + t * q.1| ≤ |(1 - t) * p.1| + |t * q.1| := abs_add_le _ _
        _ = (1 - t) * |p.1| + t * |q.1| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
        _ ≤ |p.1| + |q.1| := by
            nlinarith [abs_nonneg p.1, abs_nonneg q.1, ht.1, ht.2]
    have hd1 : |(q - p).1| ≤ dist p q := by
      have : |(q - p).1| = dist p.1 q.1 := by
        rw [Real.dist_eq, Prod.fst_sub, abs_sub_comm]
      rw [this, Prod.dist_eq]
      exact le_max_left _ _
    have hd2 : |(q - p).2| ≤ dist p q := by
      have : |(q - p).2| = dist p.2 q.2 := by
        rw [Real.dist_eq, Prod.snd_sub, abs_sub_comm]
      rw [this, Prod.dist_eq]
      exact le_max_right _ _
    have h1 : (p + t • (q - p)).1 ^ 2 ≤ (|p.1| + |q.1|) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have h2 : (q - p).1 ^ 2 ≤ dist p q ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
    have h3 : (q - p).2 ^ 2 ≤ dist p q ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd2 2
    have harg : (1 + 12 * (p + t • (q - p)).1 ^ 2) * (q - p).1 ^ 2 + (q - p).2 ^ 2
        ≤ 2 * (1 + 12 * (|p.1| + |q.1|) ^ 2) * dist p q ^ 2 := by
      nlinarith [sq_nonneg ((q - p).1), sq_nonneg (p + t • (q - p)).1,
        abs_nonneg p.1, abs_nonneg q.1, dist_nonneg (x := p) (y := q)]
    calc Real.sqrt ((1 + 12 * (p + t • (q - p)).1 ^ 2) * (q - p).1 ^ 2 + (q - p).2 ^ 2)
        ≤ Real.sqrt (2 * (1 + 12 * (|p.1| + |q.1|) ^ 2) * dist p q ^ 2) :=
          Real.sqrt_le_sqrt harg
      _ = C * dist p q := by
          rw [hC, Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]
  calc calabiDist f p q ≤ ∫ t in (0 : ℝ)..1, speed f (p + t • (q - p)) (q - p) :=
        csInf_le (lengths_bddBelow p q) (segment_mem_lengths p q)
    _ ≤ ∫ t in (0 : ℝ)..1, C * dist p q := by
        apply intervalIntegral.integral_mono_on zero_le_one ?_ _root_.intervalIntegrable_const key
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le zero_le_one]
        exact continuousOn_speed_f (by fun_prop) continuousOn_const
    _ = C * dist p q := by simp

/-- The Calabi distance vanishes on the diagonal. -/
theorem calabiDist_self (p : ℝ × ℝ) : calabiDist f p p = 0 := by
  have h1 : calabiDist f p p ≤ 0 := by
    have := calabiDist_le_mul_dist p p
    simpa using this
  have h2 : 0 ≤ calabiDist f p p := le_trans dist_nonneg (dist_le_calabiDist p p)
  linarith

/-- Completeness of the Calabi metric of `f` (the final step of the paper's proof of
Theorem 1): every `G_f`-Cauchy sequence is Euclidean-Cauchy, converges to a Euclidean
limit `L`, and by local uniform comparability it converges to `L` in `G_f` as well. -/
theorem calabiComplete_f : CalabiComplete f := by
  intro u hu
  -- `u` is Cauchy for the Euclidean (product) metric
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun m hm n hn =>
      lt_of_le_of_lt (dist_le_calabiDist (u m) (u n)) (hN m hm n hn)⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, ?_⟩
  have hdist0 : Tendsto (fun n => dist (u n) L) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hL
  set C := Real.sqrt (2 * (1 + 12 * (2 * |L.1| + 1) ^ 2)) with hCdef
  have hev : ∀ᶠ n in atTop, calabiDist f (u n) L ≤ C * dist (u n) L := by
    have h1 : ∀ᶠ n in atTop, dist (u n) L < 1 :=
      hdist0.eventually_lt_const one_pos
    filter_upwards [h1] with n hn
    have hfst : |(u n).1 - L.1| ≤ dist (u n) L := by
      have : |(u n).1 - L.1| = dist (u n).1 L.1 := (Real.dist_eq _ _).symm
      rw [this, Prod.dist_eq]
      exact le_max_left _ _
    have hb : |(u n).1| + |L.1| ≤ 2 * |L.1| + 1 := by
      have habs : |(u n).1| ≤ |(u n).1 - L.1| + |L.1| := by
        calc |(u n).1| = |(u n).1 - L.1 + L.1| := by ring_nf
          _ ≤ |(u n).1 - L.1| + |L.1| := abs_add_le _ _
      linarith
    calc calabiDist f (u n) L
        ≤ Real.sqrt (2 * (1 + 12 * (|(u n).1| + |L.1|) ^ 2)) * dist (u n) L :=
          calabiDist_le_mul_dist (u n) L
      _ ≤ C * dist (u n) L := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          apply Real.sqrt_le_sqrt
          nlinarith [abs_nonneg (u n).1, abs_nonneg L.1]
  have hCd : Tendsto (fun n => C * dist (u n) L) atTop (𝓝 0) := by
    simpa using hdist0.const_mul C
  exact squeeze_zero'
    (Eventually.of_forall fun n =>
      le_trans dist_nonneg (dist_le_calabiDist (u n) L))
    hev hCd

/-! ## Theorem 1 and the falsity of the omitted-parameter Bernstein statement -/

/-- **Theorem 1** of the paper: `f (x,y) = ½(x² + y²) + x⁴` is smooth, strictly convex
(with everywhere positive-definite Hessian), nonquadratic, its Calabi metric `G_f` is
complete, and eq. (1) holds with `a = 0`. -/
theorem theorem_one :
    ContDiff ℝ ∞ f ∧
    StrictConvexOn ℝ univ f ∧
    (∀ p : ℝ × ℝ, (hessOf f p).PosDef) ∧
    ¬ IsQuadratic f ∧
    (∀ p : ℝ × ℝ, LOp f (fun q => (hessOf f q).det ^ (0 : ℝ)) p = 0) ∧
    CalabiComplete f :=
  ⟨contDiff_f, strictConvexOn_f, hessOf_f_posDef, f_not_quadratic,
    pde_f_at_zero, calabiComplete_f⟩

/-- The Bernstein assertion is **false** at the omitted parameter `a = 0`
(the abstract's "any formulation that includes `a = 0` is false"). -/
theorem bernstein_fails_at_zero : ¬ BernsteinAssertion 0 := fun h =>
  f_not_quadratic (h f contDiff_f strictConvexOn_f pde_f_at_zero calabiComplete_f)

/-- `0 ∉ [-2/3, -1/3]`: the omitted parameter lies in the range the faulty statement
quantifies over. -/
theorem zero_notMem_interval : (0 : ℝ) ∉ Icc (-(2 : ℝ) / 3) (-(1 : ℝ) / 3) := by
  rw [mem_Icc]
  norm_num

/-- Consequence in Theorem 1: "the Bernstein statement allowing every
`a ∉ [-2/3, -1/3]` is false". -/
theorem omitted_parameter_statement_false :
    ¬ ∀ a : ℝ, a ∉ Icc (-(2 : ℝ) / 3) (-(1 : ℝ) / 3) → BernsteinAssertion a :=
  fun h => bernstein_fails_at_zero (h 0 zero_notMem_interval)

end AffineMaximalOmittedParameter
