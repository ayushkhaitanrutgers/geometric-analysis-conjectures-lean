import Mathlib

/-!
# An exact reduction of the index-four conjecture for the critical spherical
catenoid in hyperbolic three-space

Lean certification of `exact_reduction.tex`.

The paper studies the critical rotational free-boundary minimal annulus
`Σ_a ⊂ B³(r(a)) ⊂ ℍ³`, `a > 1/2`, with profile `B(s)² = a cosh(2s) − 1/2`,
`K² = a² − 1/4`, on `[−s₀,s₀] × S¹`, and the Robin radial operators
`𝒜_k u = −(Bu')'/B + (2 + k²/B² − 2K²/B⁴)u`, `u'(s₀) = coth(r) u(s₀)`
(tex eq. `eq:radial-operator-reduction`).  It proves

* **Lemma 2.1** (`lemma_geometric` below): the pinching inequality
  `cosh(2s₀) > 2a` (equivalently `B₀² > 2K²`, tex eq. `eq:G-global-reduction`)
  is automatic, and the odd mode-zero sector has exactly one negative
  eigenvalue and trivial kernel;
* **Lemma 2.2** (`mode_zero_even_count`, `mode_zero_index`): the even
  mode-zero sector has `1 + 1_{r'(a)<0}` negative eigenvalues and nullity
  `1_{r'(a)=0}`, so `ind₀(Σ_a) = 2 + 1_{r'(a)<0}`
  (tex eq. `eq:mode-zero-index-reduction`);
* **Theorem 2.3** (`exact_index_formula`, `weak_equivalence`,
  `strong_equivalence`): the exact index formula
  `ind(Σ_a) = 4 + 1_{r'(a)<0} + 2 Σ_{k≥2} 1_{μ₀ᵉ(k)<0}` and the two
  equivalences (tex eqs. `eq:exact-index-formula-reduction`,
  `eq:weak-equivalence-reduction`, `eq:strong-equivalence-reduction`).

**What is fully proved from first principles** (no spectral hypotheses):
all closed-form identities of the paper — the axial-boost field
`v = a sinh(2s)/B` is positive, solves `𝒜₀ v = 0` (`jacobi_axial`), and has
Robin defect `(2a − cosh 2s₀)/(B₀² sinh 2s₀)` (`odd_defect`,
tex eq. `eq:odd-defect-reduction`); the weighted Wronskian of the parametric
field `φ_a` against `v` is the constant `a/K` (`wronskian_const`,
`wronskian_at_zero`); the Sturm consequence that `φ_a` has at most one zero
in `(0,s₀]`; the equivalence `B₀² > 2K² ↔ cosh(2s₀) > 2a` (`pinching_iff`);
the mode-two Picone/substitution identity of tex
eq. `eq:k2-picone-reduction` (`picone_identity`, a genuine
integration-by-parts statement proved via FTC); the pointwise potential gap
behind tex eq. `eq:mode-monotonicity-reduction` (`potential_gap`); and the
sign analysis of the coefficient `3B² − 2K²` from tex §3
(`neck_coeff_neg`, `coeff_strictMono`, `coeff_unique_root`).

**What enters as hypotheses** (fields of `CatenoidData`, each documented with
the tex statement it transcribes): the Sturm shooting count for the Robin
problem (tex eq. `eq:shooting-count-reduction`), the variational tests
`𝒮(Φ⁰,Φ⁰) < 0`, `𝒮(Φ¹,Φ¹) < 0`, the boundary data of the parametric Jacobi
field `φ_a` (tex eq. `eq:parametric-data-reduction`), the mode-one count and
the positivity of the higher odd/even sectors (quoted by the paper from
Pigazzini), and the eigenvalue monotonicity
`μ₀ᵉ(k) ≥ μ₀ᵉ(2) + (k²−4)/B₀²`.  All counting, case analysis, and the three
main results are then *proved*, exactly following the paper's arguments.
-/

namespace ExactReduction

open Real Set Topology

noncomputable section

/-! ## The profile data (tex §2) -/

/-- `B(s)² = a cosh(2s) − 1/2` (tex §2). -/
def Bsq (a s : ℝ) : ℝ := a * Real.cosh (2 * s) - 1 / 2

/-- The profile function `B(s) = √(a cosh(2s) − 1/2)` of the metric
`ds² + B(s)² dθ²` (tex §2). -/
def B (a s : ℝ) : ℝ := Real.sqrt (Bsq a s)

/-- `K² = a² − 1/4` (tex §2); `|II|² = 2K²/B⁴`. -/
def Ksq (a : ℝ) : ℝ := a ^ 2 - 1 / 4

/-- `K = √(a² − 1/4) > 0`. -/
def K (a : ℝ) : ℝ := Real.sqrt (Ksq a)

/-- The Robin coefficient of the free-boundary condition:
`coth r = a sinh(2s₀)/B₀²` (closed formula recorded in the tex proof of
Lemma 2.1; we take it as the *definition* of the Robin coefficient). -/
def cothr (a s₀ : ℝ) : ℝ := a * Real.sinh (2 * s₀) / Bsq a s₀

/-- The radial potential of the mode-`k` operator
`𝒜_k u = −(Bu')'/B + Q_k u`, `Q_k = 2 + k²/B² − 2K²/B⁴`
(tex eq. `eq:radial-operator-reduction`). -/
def Q (a : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  2 + (k : ℝ) ^ 2 / Bsq a s - 2 * Ksq a / Bsq a s ^ 2

/-- The axial-boost Jacobi field `v(s) = a sinh(2s)/B(s)` (tex Lemma 2.1
proof); it is the odd zero-energy solution of the mode-zero problem. -/
def v (a s : ℝ) : ℝ := a * Real.sinh (2 * s) / B a s

/-- The derivative of the axial-boost field:
`v'(s) = 2a cosh(2s)/B − a² sinh(2s)²/B³`. -/
def vd (a s : ℝ) : ℝ :=
  2 * a * Real.cosh (2 * s) / B a s - a ^ 2 * Real.sinh (2 * s) ^ 2 / B a s ^ 3

/-! ## Elementary positivity and symmetry facts -/

theorem Bsq_pos {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) : 0 < Bsq a s := by
  have h1 : (1 : ℝ) ≤ Real.cosh (2 * s) := Real.one_le_cosh _
  have h2 : a ≤ a * Real.cosh (2 * s) := le_mul_of_one_le_right (by linarith) h1
  unfold Bsq; linarith

theorem B_pos {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) : 0 < B a s :=
  Real.sqrt_pos.mpr (Bsq_pos ha s)

theorem B_sq {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) : B a s ^ 2 = Bsq a s :=
  Real.sq_sqrt (Bsq_pos ha s).le

theorem Ksq_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < Ksq a := by
  unfold Ksq; nlinarith

theorem K_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < K a :=
  Real.sqrt_pos.mpr (Ksq_pos ha)

theorem K_sq {a : ℝ} (ha : 1 / 2 < a) : K a ^ 2 = Ksq a :=
  Real.sq_sqrt (Ksq_pos ha).le

theorem B_even (a s : ℝ) : B a (-s) = B a s := by
  unfold B Bsq; rw [mul_neg, Real.cosh_neg]

theorem v_zero (a : ℝ) : v a 0 = 0 := by simp [v]

theorem v_pos {a : ℝ} (ha : 1 / 2 < a) {s : ℝ} (hs : 0 < s) : 0 < v a s := by
  have h1 : 0 < Real.sinh (2 * s) := Real.sinh_pos_iff.mpr (by linarith)
  exact div_pos (mul_pos (by linarith) h1) (B_pos ha s)

/-- `B · v = a sinh(2s)`: the axial-boost field times the profile. -/
theorem B_mul_v {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) :
    B a s * v a s = a * Real.sinh (2 * s) := by
  unfold v; field_simp [(B_pos ha s).ne']

/-! ## Derivatives of the profile data -/

theorem hasDerivAt_Bsq (a s : ℝ) :
    HasDerivAt (Bsq a) (2 * a * Real.sinh (2 * s)) s := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.cosh (2 * t))
      (Real.sinh (2 * s) * 2) s := h1.cosh
  have h3 := (h2.const_mul a).sub_const (1 / 2)
  convert h3 using 1
  ring

/-- `B' = v`: the derivative of the profile is the axial-boost field. -/
theorem hasDerivAt_B {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) :
    HasDerivAt (B a) (v a s) s := by
  have h := (Real.hasDerivAt_sqrt (Bsq_pos ha s).ne').comp s (hasDerivAt_Bsq a s)
  convert h using 1
  unfold v B
  field_simp

theorem hasDerivAt_v {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) :
    HasDerivAt (v a) (vd a s) s := by
  have hB := B_pos ha s
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have hnum : HasDerivAt (fun t : ℝ => a * Real.sinh (2 * t))
      (a * (Real.cosh (2 * s) * 2)) s := h1.sinh.const_mul a
  have h := hnum.div (hasDerivAt_B ha s) hB.ne'
  convert h using 1
  unfold vd v
  have hB2 : B a s ^ 2 = Bsq a s := B_sq ha s
  field_simp

/-! ## The odd Robin defect (tex eq. `eq:odd-defect-reduction`) -/

/-- **tex eq. `eq:odd-defect-reduction`**:
`v'(s₀)/v(s₀) − coth r = (2a − cosh(2s₀))/(B₀² sinh(2s₀))`. -/
theorem odd_defect {a : ℝ} (ha : 1 / 2 < a) {s : ℝ} (hs : 0 < s) :
    vd a s / v a s - cothr a s
      = (2 * a - Real.cosh (2 * s)) / (Bsq a s * Real.sinh (2 * s)) := by
  have hB := B_pos ha s
  have hBsq := Bsq_pos ha s
  have hsh : 0 < Real.sinh (2 * s) := Real.sinh_pos_iff.mpr (by linarith)
  have hv := v_pos ha hs
  have hB2 : B a s ^ 2 = Bsq a s := B_sq ha s
  have hch : Real.cosh (2 * s) ^ 2 - Real.sinh (2 * s) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (2 * s)
  have hq_def : Bsq a s = a * Real.cosh (2 * s) - 1 / 2 := rfl
  have hvdv : vd a s / v a s
      = 2 * Real.cosh (2 * s) / Real.sinh (2 * s)
        - a * Real.sinh (2 * s) / Bsq a s := by
    rw [div_eq_iff hv.ne']
    unfold vd v
    field_simp
    linear_combination a * Real.sinh (2 * s) ^ 2 * hB2
  rw [hvdv]
  unfold cothr
  field_simp
  linear_combination 2 * a * hch + 2 * Real.cosh (2 * s) * hq_def

/-! ## The axial-boost field is a Jacobi field: `𝒜₀ v = 0` -/

/-- **`𝒜₀ v = 0`** (tex Lemma 2.1 proof: the axial boost produces the odd
zero-energy solution of the mode-zero radial problem): `(B v')' = Q₀ · (B v)`. -/
theorem jacobi_axial {a : ℝ} (ha : 1 / 2 < a) (s : ℝ) :
    HasDerivAt (fun t => B a t * vd a t) (Q a 0 s * (B a s * v a s)) s := by
  have key : ∀ t, B a t * vd a t
      = 2 * a * Real.cosh (2 * t) - a ^ 2 * Real.sinh (2 * t) ^ 2 / Bsq a t := by
    intro t
    have hB := B_pos ha t
    have hB2 : B a t ^ 2 = Bsq a t := B_sq ha t
    unfold vd
    field_simp [hB.ne', (Bsq_pos ha t).ne']
    linear_combination a * Real.sinh (2 * t) ^ 2 * hB2
  simp only [key]
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have hch : HasDerivAt (fun t : ℝ => 2 * a * Real.cosh (2 * t))
      (2 * a * (Real.sinh (2 * s) * 2)) s := h1.cosh.const_mul (2 * a)
  have hnum : HasDerivAt (fun t : ℝ => a ^ 2 * Real.sinh (2 * t) ^ 2)
      (a ^ 2 * ((2 : ℕ) * Real.sinh (2 * s) ^ 1 * (Real.cosh (2 * s) * 2))) s :=
    (h1.sinh.pow 2).const_mul (a ^ 2)
  have hfrac := hnum.div (hasDerivAt_Bsq a s) (Bsq_pos ha s).ne'
  have hD := hch.sub hfrac
  convert hD using 1
  have hch2 : Real.cosh (2 * s) ^ 2 - Real.sinh (2 * s) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (2 * s)
  have hq_def : Bsq a s = a * Real.cosh (2 * s) - 1 / 2 := rfl
  rw [B_mul_v ha s]
  unfold Q Ksq
  have hBsq := Bsq_pos ha s
  field_simp
  linear_combination (-8 * Bsq a s * Real.sinh (2 * s)
      + 8 * a * Real.cosh (2 * s) * Real.sinh (2 * s)
      + 4 * Real.sinh (2 * s)) * hq_def
    + 8 * a ^ 2 * Real.sinh (2 * s) * hch2

/-- The pinching equivalence of tex eq. `eq:G-global-reduction`:
`B₀² > 2K² ↔ cosh(2s₀) > 2a`. -/
theorem pinching_iff {a : ℝ} (ha : 1 / 2 < a) (s₀ : ℝ) :
    2 * Ksq a < Bsq a s₀ ↔ 2 * a < Real.cosh (2 * s₀) := by
  have ha0 : (0 : ℝ) < a := by linarith
  unfold Bsq Ksq
  constructor <;> intro h <;> nlinarith

/-! ## The weighted Wronskian and Sturm separation (tex §2, after Lemma 2.1)

The parametric Jacobi field `φ_a` enters only through its Cauchy data at `0`
and its ODE `𝒜₀ φ_a = 0` (tex eq. `eq:parametric-data-reduction`).  From
those hypotheses everything below is *proved*: the weighted Wronskian
against the axial-boost field is the nonzero constant `a/K`, the quotient
`φ_a/v` is strictly decreasing, and hence `φ_a` has at most one zero in
`(0, s₀]` — the Sturm separation claim of the tex. -/

/-- The weighted Wronskian `W = B (φ v' − φ' v)`. -/
def Wr (a : ℝ) (φ φd : ℝ → ℝ) (s : ℝ) : ℝ :=
  B a s * (φ s * vd a s - φd s * v a s)

/-- If `𝒜₀ φ = 0`, the weighted Wronskian of `φ` against `v` is constant. -/
theorem wronskian_const {a : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hODE : ∀ s, HasDerivAt (fun t => B a t * φd t) (Q a 0 s * (B a s * φ s)) s)
    (s : ℝ) : Wr a φ φd s = Wr a φ φd 0 := by
  have hEq : Wr a φ φd = fun u => φ u * (B a u * vd a u) - B a u * φd u * v a u := by
    funext u; unfold Wr; ring
  have hderiv : ∀ u : ℝ, HasDerivAt (Wr a φ φd) 0 u := by
    intro u
    rw [hEq]
    have h1 := (hφ u).mul (jacobi_axial ha u)
    have h2 := (hODE u).mul (hasDerivAt_v ha u)
    have h3 := h1.sub h2
    convert h3 using 1
    ring
  exact is_const_of_deriv_eq_zero (fun u => (hderiv u).differentiableAt)
    (fun u => (hderiv u).deriv) s 0

/-- With the Cauchy data of tex eq. `eq:parametric-data-reduction`
(`φ(0) = 1/(2K) > 0`, `φ'(0) = 0`) the Wronskian constant is `a/K ≠ 0`. -/
theorem wronskian_at_zero {a : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hφ0 : φ 0 = 1 / (2 * K a)) (hφd0 : φd 0 = 0) :
    Wr a φ φd 0 = a / K a := by
  have hB : B a 0 ≠ 0 := (B_pos ha 0).ne'
  have hK : K a ≠ 0 := (K_pos ha).ne'
  unfold Wr vd
  rw [hφ0, hφd0, v_zero]
  norm_num [Real.sinh_zero, Real.cosh_zero]
  field_simp

/-- The Wronskian is the constant `a/K` everywhere. -/
theorem wronskian_eq {a : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hODE : ∀ s, HasDerivAt (fun t => B a t * φd t) (Q a 0 s * (B a s * φ s)) s)
    (hφ0 : φ 0 = 1 / (2 * K a)) (hφd0 : φd 0 = 0) (s : ℝ) :
    Wr a φ φd s = a / K a := by
  rw [wronskian_const ha hφ hODE s, wronskian_at_zero ha hφ0 hφd0]

/-- Sturm separation, quantitative form: the quotient `φ/v` is strictly
decreasing on `(0, s₀]` (tex §2: "Sturm separation therefore shows that
`φ_a` has at most one zero in `(0,s₀]`"). -/
theorem quotient_strictAnti {a s₀ : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) :
    StrictAntiOn (fun s => φ s / v a s) (Ioc 0 s₀) := by
  have haK : 0 < a / K a := div_pos (by linarith) (K_pos ha)
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 s₀)
  · intro x hx
    exact (((hφ x).div (hasDerivAt_v ha x)
      (v_pos ha hx.1).ne').continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hvx := v_pos ha hx.1
    have hd : HasDerivAt (fun s => φ s / v a s)
        ((φd x * v a x - φ x * vd a x) / v a x ^ 2) x :=
      (hφ x).div (hasDerivAt_v ha x) hvx.ne'
    rw [hd.deriv]
    have hnum : φd x * v a x - φ x * vd a x = -(a / K a) / B a x := by
      have h := hW x
      unfold Wr at h
      rw [eq_div_iff (B_pos ha x).ne']
      linear_combination -h
    rw [hnum]
    apply div_neg_of_neg_of_pos
    · rw [neg_div]
      exact neg_lt_zero.mpr (div_pos haK (B_pos ha x))
    · positivity

/-- `φ` has at most one zero in `(0, s₀]`. -/
theorem zeros_subsingleton {a s₀ : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) :
    Set.Subsingleton {s ∈ Ioc 0 s₀ | φ s = 0} := by
  intro x hx y hy
  have hanti := quotient_strictAnti (s₀ := s₀) ha hφ hW
  apply hanti.injOn hx.1 hy.1
  simp only [hx.2, hy.2, zero_div]

/-- If `φ(s₀) ≥ 0` then `φ > 0` on the interior (used in the tex Lemma 2.2
case analysis: "If `φ_a(s₀)>0`, then `φ_a` has no zero"). -/
theorem phi_pos_of_boundary_nonneg {a s₀ : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hs₀ : 0 < s₀) (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) (hb : 0 ≤ φ s₀) :
    ∀ s ∈ Ioo 0 s₀, 0 < φ s := by
  intro s hs
  have hanti := quotient_strictAnti (s₀ := s₀) ha hφ hW
  have h1 : φ s₀ / v a s₀ < φ s / v a s :=
    hanti ⟨hs.1, hs.2.le⟩ ⟨hs₀, le_refl _⟩ hs.2
  have h2 : 0 ≤ φ s₀ / v a s₀ := div_nonneg hb (v_pos ha hs₀).le
  have h3 : 0 < φ s / v a s := lt_of_le_of_lt h2 h1
  have h4 := mul_pos h3 (v_pos ha hs.1)
  rwa [div_mul_cancel₀ _ (v_pos ha hs.1).ne'] at h4

/-- If `φ(s₀) ≥ 0`, the interior zero set is empty. -/
theorem zero_set_empty {a s₀ : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hs₀ : 0 < s₀) (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) (hb : 0 ≤ φ s₀) :
    {s ∈ Ioo 0 s₀ | φ s = 0} = ∅ := by
  ext s
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro hs
  exact (phi_pos_of_boundary_nonneg ha hs₀ hφ hW hb s hs).ne'

/-- If `φ(0) > 0` and `φ(s₀) < 0`, there is exactly one interior zero
(tex Lemma 2.2 case analysis: "then `φ_a` has exactly one zero"). -/
theorem zero_set_singleton {a s₀ : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hs₀ : 0 < s₀) (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) (hφ0 : 0 < φ 0) (hb : φ s₀ < 0) :
    {s ∈ Ioo 0 s₀ | φ s = 0}.ncard = 1 := by
  -- a point near `0` where `φ` is still positive
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < φ s :=
    ((hφ 0).continuousAt.tendsto.eventually_const_lt hφ0).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨ε, hεp, hεm⟩ := (hev.and
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hs₀) fun x hx => hx)).exists
  -- intermediate value between `ε` and `s₀`
  have hcont : ContinuousOn φ (Icc ε s₀) := fun x _ =>
    (hφ x).continuousAt.continuousWithinAt
  have hz : (0 : ℝ) ∈ Ioo (φ s₀) (φ ε) := ⟨hb, hεp⟩
  obtain ⟨z, hzm, hφz⟩ := intermediate_value_Ioo' hεm.2.le hcont hz
  have hzIoo : z ∈ Ioo 0 s₀ := ⟨lt_trans hεm.1 hzm.1, hzm.2⟩
  rw [Set.ncard_eq_one]
  refine ⟨z, ?_⟩
  ext y
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hy, hφy⟩
    exact zeros_subsingleton ha hφ hW ⟨⟨hy.1, hy.2.le⟩, hφy⟩
      ⟨⟨hzIoo.1, hzIoo.2.le⟩, hφz⟩
  · rintro rfl
    exact ⟨hzIoo, hφz⟩

/-- The endpoint alternative in the `r'(a)<0` case is impossible: `φ(0) > 0`,
`φ(s₀) = 0` and `φ'(s₀) > 0` contradict the at-most-one-zero property
(tex Lemma 2.2: "starting positive, the solution would then have to be
negative immediately to the left of `s₀`, producing one interior zero in
addition to the endpoint zero"). -/
theorem no_boundary_zero_pos_deriv {a s₀ : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hs₀ : 0 < s₀) (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) (hφ0 : 0 < φ 0) (hb : φ s₀ = 0)
    (hd : 0 < φd s₀) : False := by
  -- a point near `0` where `φ` is positive
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < φ s :=
    ((hφ 0).continuousAt.tendsto.eventually_const_lt hφ0).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨ε, hεp, hεm⟩ := (hev.and
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hs₀) fun x hx => hx)).exists
  -- a point just left of `s₀` where `φ` is negative
  have hslope : Filter.Tendsto (slope φ s₀) (𝓝[≠] s₀) (𝓝 (φd s₀)) :=
    hasDerivAt_iff_tendsto_slope.mp (hφ s₀)
  have hle : 𝓝[<] s₀ ≤ 𝓝[≠] s₀ :=
    nhdsWithin_mono s₀ fun x hx => ne_of_lt hx
  have hev2 : ∀ᶠ s in 𝓝[<] s₀, 0 < slope φ s₀ s :=
    (hslope.eventually_const_lt hd).filter_mono hle
  obtain ⟨t, hts, htm⟩ := (hev2.and
    (Filter.eventually_of_mem (Ioo_mem_nhdsLT hεm.2) fun x hx => hx)).exists
  have htneg : φ t < 0 := by
    have h1 : slope φ s₀ t = φ t / (t - s₀) := by
      rw [slope_def_field, hb, sub_zero]
    rw [h1] at hts
    have h2 : t - s₀ < 0 := sub_neg.mpr htm.2
    by_contra h
    rw [not_lt] at h
    exact absurd hts (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos h h2.le))
  -- intermediate value between `ε` and `t`
  have hcont : ContinuousOn φ (Icc ε t) := fun x _ =>
    (hφ x).continuousAt.continuousWithinAt
  have hz : (0 : ℝ) ∈ Ioo (φ t) (φ ε) := ⟨htneg, hεp⟩
  obtain ⟨z, hzm, hφz⟩ := intermediate_value_Ioo' htm.1.le hcont hz
  -- `z` and `s₀` are two distinct zeros in `(0, s₀]`
  have hlt : z < s₀ := lt_trans hzm.2 htm.2
  have hzs : z = s₀ :=
    zeros_subsingleton ha hφ hW
      ⟨⟨lt_trans hεm.1 hzm.1, hlt.le⟩, hφz⟩
      ⟨⟨hs₀, le_refl _⟩, hb⟩
  rw [hzs] at hlt
  exact lt_irrefl s₀ hlt

/-! ## The spectral data of the catenoid (transcribed hypotheses)

`CatenoidData a` bundles every input about `Σ_a` that lives outside Mathlib
(free-boundary minimal surface theory and one-dimensional Robin spectral
theory).  Each field is documented with the tex statement it transcribes.
Everything after the structure declaration is *proved* from these fields. -/

/-- Spectral/geometric inputs for the critical catenoid `Σ_a` (tex §2). -/
structure CatenoidData (a : ℝ) where
  /-- Half-length `s₀ = s₀(a)` of the profile interval `[-s₀, s₀]` (tex §2). -/
  s₀ : ℝ
  hs₀ : 0 < s₀
  /-- The scalar `r'(a)`: derivative of the ball radius in the parameter. -/
  rp : ℝ
  /-- Number of negative eigenvalues of the Robin problem for `𝒜_k`
  (tex eq. `eq:radial-operator-reduction`) in the **even** sector on `[0,s₀]`
  (`u'(0) = 0`, `u'(s₀) = coth(r) u(s₀)`). -/
  NnegE : ℕ → ℕ
  /-- Same count in the **odd** sector (`u(0) = 0`). -/
  NnegO : ℕ → ℕ
  /-- Nullity (dimension of the Robin kernel) of `𝒜_k`, even sector. -/
  NnulE : ℕ → ℕ
  /-- Nullity of `𝒜_k`, odd sector. -/
  NnulO : ℕ → ℕ
  /-- First even radial eigenvalue `μ₀^even(k)` of `𝒜_k` (tex §2, used for
  `k ≥ 2`). -/
  μ : ℕ → ℝ
  /-- The even parametric Jacobi field `φ_a = ⟨∂_a Φ_a, ν_a⟩` (tex §2)… -/
  φ : ℝ → ℝ
  /-- …and its derivative. -/
  φd : ℝ → ℝ
  hφderiv : ∀ s, HasDerivAt φ (φd s) s
  /-- tex eq. `eq:parametric-data-reduction`: `φ_a(0) = 1/(2K)`. -/
  hφ0 : φ 0 = 1 / (2 * K a)
  /-- tex eq. `eq:parametric-data-reduction`: `φ_a'(0) = 0`. -/
  hφd0 : φd 0 = 0
  /-- tex eq. `eq:parametric-data-reduction`: `𝒜₀ φ_a = 0`, in the
  self-adjoint form `(B φ')' = Q₀ · (B φ)`. -/
  hφODE : ∀ s, HasDerivAt (fun t => B a t * φd t) (Q a 0 s * (B a s * φ s)) s
  /-- tex eq. `eq:parametric-data-reduction`: the Robin defect of `φ_a` is
  `φ_a'(s₀) − coth(r) φ_a(s₀) = −r'(a) K/B₀²`. -/
  hφRobin : φd s₀ - cothr a s₀ * φ s₀ = -(rp * K a / Bsq a s₀)
  /-- tex eq. `eq:shooting-count-reduction` for the even mode-0 sector,
  applied to the zero-energy shot `φ_a`: if `φ_a(s₀) ≠ 0` then
  `N₋ = n_z(φ_a) + 1_{φ_a'(s₀)/φ_a(s₀) − coth r < 0}`. -/
  shootE : φ s₀ ≠ 0 →
    NnegE 0 = {s ∈ Ioo 0 s₀ | φ s = 0}.ncard
      + (if φd s₀ / φ s₀ - cothr a s₀ < 0 then 1 else 0)
  /-- The endpoint case `φ_a(s₀) = 0` of the shooting count, via the Prüfer
  angle (tex: "The cases in which `w(s₀)=0` follow either directly from the
  Pruefer angle or by a one-sided limiting argument", and the Lemma 2.2 proof
  step "the zero-energy Pruefer angle at `s₀` is exactly `π` … precisely one
  Robin eigenangle has been crossed"): `N₋ = n_z(φ_a) + 1`. -/
  shootE₀ : φ s₀ = 0 → NnegE 0 = {s ∈ Ioo 0 s₀ | φ s = 0}.ncard + 1
  /-- tex eq. `eq:shooting-count-reduction` for the odd mode-0 sector,
  applied to the zero-energy shot `v` (the axial-boost field). -/
  shootO : v a s₀ ≠ 0 →
    NnegO 0 = {s ∈ Ioo 0 s₀ | v a s = 0}.ncard
      + (if vd a s₀ / v a s₀ - cothr a s₀ < 0 then 1 else 0)
  /-- Variational test with the even ambient coordinate `Φ⁰ = A cosh φ`:
  `𝒮(Φ⁰,Φ⁰) < 0`, so the even mode-0 problem has a negative eigenvalue
  (tex Lemma 2.2 proof). -/
  testE : 1 ≤ NnegE 0
  /-- Variational test with the odd ambient coordinate `Φ¹ = A sinh φ`:
  `𝒮(Φ¹,Φ¹) = −∫|II|²(Φ¹)² < 0` (tex Lemma 2.1 proof). -/
  testO : 1 ≤ NnegO 0
  /-- The even mode-0 Robin kernel is spanned by the zero-energy even shot
  `φ_a`; it is nontrivial iff `φ_a` satisfies the Robin condition
  (tex Lemma 2.2 proof). -/
  nulE : NnulE 0 = if φd s₀ - cothr a s₀ * φ s₀ = 0 then 1 else 0
  /-- Likewise the odd mode-0 kernel is spanned by `v` (tex Lemma 2.1 proof:
  "the odd kernel is trivial" iff `v` fails the Robin condition). -/
  nulO : NnulO 0 = if vd a s₀ - cothr a s₀ * v a s₀ = 0 then 1 else 0
  /-- "The mode-1 sector has index two and nullity two" (tex §2, quoted from
  Pigazzini): per sign `k = ±1` the radial problem contributes index 1… -/
  mode1neg : NnegE 1 + NnegO 1 = 1
  /-- …and nullity 1. -/
  mode1nul : NnulE 1 + NnulO 1 = 1
  /-- "For every `k ≥ 2`, the odd radial sector is strictly positive"
  (tex §2). -/
  oddPos : ∀ k, 2 ≤ k → NnegO k = 0 ∧ NnulO k = 0
  /-- "All even eigenvalues except possibly the first are positive" (tex §2):
  the even sector count in mode `k ≥ 2` is governed by the sign of
  `μ₀^even(k)`. -/
  evenTail : ∀ k, 2 ≤ k →
    NnegE k = (if μ k < 0 then 1 else 0) ∧ NnulE k = (if μ k = 0 then 1 else 0)
  /-- tex eq. `eq:mode-monotonicity-reduction`:
  `μ₀^even(k) ≥ μ₀^even(2) + (k²−4)/B₀²`. -/
  μmono : ∀ k : ℕ, 2 ≤ k → μ 2 + ((k : ℝ) ^ 2 - 4) / Bsq a s₀ ≤ μ k

namespace CatenoidData

variable {a : ℝ}

/-- Morse index of `Σ_a` through the angular-mode decomposition: mode `0`
counts once, the pair of modes `±k` (`k ≥ 1`) counts twice (tex §2: "After
separation into angular modes"; the decomposition itself is the working
definition of the index here, as in the paper). -/
def ind (D : CatenoidData a) : ℕ :=
  D.NnegE 0 + D.NnegO 0 + 2 * ∑' k : ℕ, (D.NnegE (k + 1) + D.NnegO (k + 1))

/-- Nullity of `Σ_a` through the mode decomposition. -/
def nul (D : CatenoidData a) : ℕ :=
  D.NnulE 0 + D.NnulO 0 + 2 * ∑' k : ℕ, (D.NnulE (k + 1) + D.NnulO (k + 1))

/-- The Wronskian of the parametric field against the axial-boost field is
the constant `a/K` (proved from the transcribed Cauchy data and ODE). -/
theorem wr (ha : 1 / 2 < a) (D : CatenoidData a) (s : ℝ) :
    Wr a D.φ D.φd s = a / K a :=
  wronskian_eq ha D.hφderiv D.hφODE D.hφ0 D.hφd0 s

theorem phi_zero_pos (ha : 1 / 2 < a) (D : CatenoidData a) : 0 < D.φ 0 := by
  rw [D.hφ0]
  exact div_pos one_pos (mul_pos two_pos (K_pos ha))

end CatenoidData

/-! ## Lemma 2.1: the geometric inequality is automatic -/

/-- **tex Lemma 2.1** (`eq:G-global-reduction`): for every `a > 1/2` the
pinching inequality `cosh(2s₀) > 2a` — equivalently `B₀² > 2K²` — holds, and
the odd mode-zero sector has exactly one negative eigenvalue and trivial
kernel.  Proved from the shooting count, the `Φ¹` test, and the fully
formalized defect identity `eq:odd-defect-reduction`. -/
theorem lemma_geometric (ha : 1 / 2 < a) (D : CatenoidData a) :
    2 * a < Real.cosh (2 * D.s₀) ∧ 2 * Ksq a < Bsq a D.s₀ ∧
      D.NnegO 0 = 1 ∧ D.NnulO 0 = 0 := by
  have hv := v_pos ha D.hs₀
  have hzero : {s ∈ Ioo 0 D.s₀ | v a s = 0}.ncard = 0 := by
    have he : {s ∈ Ioo 0 D.s₀ | v a s = 0} = ∅ := by
      ext s
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun hs => (v_pos ha hs.1).ne'
    rw [he, Set.ncard_empty]
  have hshoot := D.shootO hv.ne'
  rw [hzero, zero_add] at hshoot
  have hquot : vd a D.s₀ / v a D.s₀ - cothr a D.s₀ < 0 := by
    by_contra hq
    rw [if_neg hq] at hshoot
    have h := D.testO
    rw [hshoot] at h
    exact absurd h (by norm_num)
  have hch : 2 * a < Real.cosh (2 * D.s₀) := by
    have h2 := hquot
    rw [odd_defect ha D.hs₀] at h2
    have hden : 0 < Bsq a D.s₀ * Real.sinh (2 * D.s₀) :=
      mul_pos (Bsq_pos ha D.s₀) (Real.sinh_pos_iff.mpr (by linarith [D.hs₀]))
    by_contra hc
    rw [not_lt] at hc
    exact absurd h2 (not_lt.mpr (div_nonneg (by linarith) hden.le))
  refine ⟨hch, (pinching_iff ha D.s₀).mpr hch, ?_, ?_⟩
  · rw [hshoot, if_pos hquot]
  · rw [D.nulO]
    have heq : vd a D.s₀ - cothr a D.s₀ * v a D.s₀
        = (vd a D.s₀ / v a D.s₀ - cothr a D.s₀) * v a D.s₀ := by
      field_simp
    rw [if_neg (by rw [heq]; exact (mul_neg_of_neg_of_pos hquot hv).ne)]

/-! ## Lemma 2.2: the exact mode-zero count -/

/-- The interior zero set of `φ` has at most one point (Sturm separation). -/
theorem interior_zeros_le_one {a s₀ : ℝ} {φ φd : ℝ → ℝ} (ha : 1 / 2 < a)
    (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) :
    {s ∈ Ioo 0 s₀ | φ s = 0}.ncard ≤ 1 := by
  have hsub : Set.Subsingleton {s ∈ Ioo 0 s₀ | φ s = 0} := by
    intro x hx y hy
    exact zeros_subsingleton ha hφ hW
      ⟨⟨hx.1.1, hx.1.2.le⟩, hx.2⟩ ⟨⟨hy.1.1, hy.1.2.le⟩, hy.2⟩
  rcases hsub.eq_empty_or_singleton with h | ⟨x, h⟩
  · rw [h, Set.ncard_empty]
    omega
  · rw [h, Set.ncard_singleton]

/-- If `φ(s₀) = 0`, the at-most-one-zero property leaves no interior zero. -/
theorem interior_zeros_empty_of_boundary_zero {a s₀ : ℝ} {φ φd : ℝ → ℝ}
    (ha : 1 / 2 < a) (hs₀ : 0 < s₀) (hφ : ∀ s, HasDerivAt φ (φd s) s)
    (hW : ∀ s, Wr a φ φd s = a / K a) (hb : φ s₀ = 0) :
    {s ∈ Ioo 0 s₀ | φ s = 0} = ∅ := by
  ext y
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro hy hφy
  have heq := zeros_subsingleton ha hφ hW
    ⟨⟨hy.1, hy.2.le⟩, hφy⟩ ⟨⟨hs₀, le_refl _⟩, hb⟩
  exact absurd heq (ne_of_lt hy.2)

/-- **tex Lemma 2.2** (`lem:mode-zero-count-reduction`), radial part: the
even mode-zero sector has `N₋^{0,even} = 1 + 1_{r'(a)<0}` negative
eigenvalues, and its nullity is `1_{r'(a)=0}`.  Proved by the paper's case
analysis on the sign of `r'(a)` and of `φ_a(s₀)`, using the Sturm lemmas
above and the transcribed shooting count. -/
theorem mode_zero_even_count {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    D.NnegE 0 = 1 + (if D.rp < 0 then 1 else 0) ∧
      D.NnulE 0 = (if D.rp = 0 then 1 else 0) := by
  have hK := K_pos ha
  have hBsq := Bsq_pos ha D.s₀
  have hφ0 := D.phi_zero_pos ha
  have hW := D.wr ha
  have hd := D.hφRobin
  have hquot_eq : D.φ D.s₀ ≠ 0 →
      D.φd D.s₀ / D.φ D.s₀ - cothr a D.s₀
        = (D.φd D.s₀ - cothr a D.s₀ * D.φ D.s₀) / D.φ D.s₀ := by
    intro h; field_simp
  constructor
  · rcases lt_trichotomy D.rp 0 with hrp | hrp | hrp
    · -- `r'(a) < 0`: the Robin defect of `φ_a` is positive
      have hdpos : 0 < D.φd D.s₀ - cothr a D.s₀ * D.φ D.s₀ := by
        rw [hd]
        have h1 : D.rp * K a / Bsq a D.s₀ < 0 :=
          div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hrp hK) hBsq
        linarith
      rw [if_pos hrp]
      rcases lt_trichotomy (D.φ D.s₀) 0 with hb | hb | hb
      · -- `φ_a(s₀) < 0`: one interior zero and a negative boundary quotient
        have hn := zero_set_singleton ha D.hs₀ D.hφderiv hW hφ0 hb
        have hq : D.φd D.s₀ / D.φ D.s₀ - cothr a D.s₀ < 0 := by
          rw [hquot_eq hb.ne]
          exact div_neg_of_pos_of_neg hdpos hb
        rw [D.shootE hb.ne, hn, if_pos hq]
      · -- `φ_a(s₀) = 0` with `φ_a'(s₀) > 0`: impossible
        exfalso
        have hdd : 0 < D.φd D.s₀ := by
          rw [hb, mul_zero, sub_zero] at hdpos
          exact hdpos
        exact no_boundary_zero_pos_deriv ha D.hs₀ D.hφderiv hW hφ0 hb hdd
      · -- `φ_a(s₀) > 0`: would give `N₋ = 0`, contradicting the `Φ⁰` test
        exfalso
        have hn := zero_set_empty ha D.hs₀ D.hφderiv hW hb.le
        have hq : ¬(D.φd D.s₀ / D.φ D.s₀ - cothr a D.s₀ < 0) := by
          rw [not_lt, hquot_eq hb.ne']
          exact div_nonneg hdpos.le hb.le
        have h := D.shootE hb.ne'
        rw [hn, Set.ncard_empty, zero_add, if_neg hq] at h
        have := D.testE
        omega
    · -- `r'(a) = 0`: the defect vanishes; `0` is the second eigenvalue
      have hd0 : D.φd D.s₀ - cothr a D.s₀ * D.φ D.s₀ = 0 := by
        rw [hd, hrp]; ring
      rw [if_neg (by rw [hrp]; exact lt_irrefl 0), add_zero]
      rcases eq_or_ne (D.φ D.s₀) 0 with hb | hb
      · have hone := interior_zeros_empty_of_boundary_zero ha D.hs₀ D.hφderiv hW hb
        have h := D.shootE₀ hb
        rw [hone, Set.ncard_empty, zero_add] at h
        exact h
      · have h := D.shootE hb
        have hq : ¬(D.φd D.s₀ / D.φ D.s₀ - cothr a D.s₀ < 0) := by
          rw [hquot_eq hb, hd0, zero_div]
          exact lt_irrefl 0
        rw [if_neg hq, add_zero] at h
        have hle := interior_zeros_le_one (s₀ := D.s₀) ha D.hφderiv hW
        have hge := D.testE
        omega
    · -- `r'(a) > 0`: the defect is negative
      have hdneg : D.φd D.s₀ - cothr a D.s₀ * D.φ D.s₀ < 0 := by
        rw [hd]
        have h1 : 0 < D.rp * K a / Bsq a D.s₀ := div_pos (mul_pos hrp hK) hBsq
        linarith
      rw [if_neg (not_lt.mpr hrp.le), add_zero]
      rcases lt_trichotomy (D.φ D.s₀) 0 with hb | hb | hb
      · -- one interior zero, positive boundary quotient
        have hn := zero_set_singleton ha D.hs₀ D.hφderiv hW hφ0 hb
        have hq : ¬(D.φd D.s₀ / D.φ D.s₀ - cothr a D.s₀ < 0) := by
          rw [not_lt, hquot_eq hb.ne]
          exact (div_pos_of_neg_of_neg hdneg hb).le
        rw [D.shootE hb.ne, hn, if_neg hq]
      · -- endpoint zero with negative slope: Prüfer case, `N₋ = 0 + 1`
        have hone := interior_zeros_empty_of_boundary_zero ha D.hs₀ D.hφderiv hW hb
        have h := D.shootE₀ hb
        rw [hone, Set.ncard_empty, zero_add] at h
        exact h
      · -- `φ_a(s₀) > 0`: no zero, negative boundary quotient
        have hn := zero_set_empty ha D.hs₀ D.hφderiv hW hb.le
        have hq : D.φd D.s₀ / D.φ D.s₀ - cothr a D.s₀ < 0 := by
          rw [hquot_eq hb.ne']
          exact div_neg_of_neg_of_pos hdneg hb
        rw [D.shootE hb.ne', hn, Set.ncard_empty, zero_add, if_pos hq]
  · -- nullity: the kernel is nontrivial exactly when `r'(a) = 0`
    rw [D.nulE, hd]
    rcases eq_or_ne D.rp 0 with h | h
    · rw [if_pos (by rw [h]; norm_num), if_pos h]
    · rw [if_neg (neg_ne_zero.mpr
        (div_ne_zero (mul_ne_zero h hK.ne') hBsq.ne')), if_neg h]

/-- **tex eq. `eq:mode-zero-index-reduction`**: the full mode-zero
contribution to the Morse index is `ind₀(Σ_a) = 2 + 1_{r'(a)<0}`. -/
theorem mode_zero_index {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    D.NnegE 0 + D.NnegO 0 = 2 + (if D.rp < 0 then 1 else 0) := by
  have h1 := (mode_zero_even_count ha D).1
  have h2 := (lemma_geometric ha D).2.2.1
  omega

/-! ## Theorem 2.3: the exact reduction -/

/-- Tail positivity, from tex eq. `eq:mode-monotonicity-reduction`: beyond an
explicit mode all first even eigenvalues are positive.  This is what makes
the sums in the index formula finite. -/
theorem CatenoidData.mu_pos_tail {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    ∃ N : ℕ, ∀ k, N ≤ k → 0 < D.μ k := by
  refine ⟨3 + ⌈Bsq a D.s₀ * |D.μ 2|⌉₊, fun k hk => ?_⟩
  have hB := Bsq_pos ha D.s₀
  have h2 : 2 ≤ k := by omega
  have hmono := D.μmono k h2
  have hcr : Bsq a D.s₀ * |D.μ 2| ≤ (⌈Bsq a D.s₀ * |D.μ 2|⌉₊ : ℝ) := Nat.le_ceil _
  have hkr : (3 : ℝ) + (⌈Bsq a D.s₀ * |D.μ 2|⌉₊ : ℝ) ≤ (k : ℝ) := by
    have h := Nat.cast_le (α := ℝ) |>.mpr hk
    push_cast at h
    linarith
  have habs : Bsq a D.s₀ * (-(D.μ 2)) ≤ Bsq a D.s₀ * |D.μ 2| :=
    mul_le_mul_of_nonneg_left (neg_le_abs _) hB.le
  have hc0 : (0 : ℝ) ≤ (⌈Bsq a D.s₀ * |D.μ 2|⌉₊ : ℝ) := Nat.cast_nonneg _
  have hgap : Bsq a D.s₀ * (-(D.μ 2)) < (k : ℝ) ^ 2 - 4 := by
    nlinarith [sq_nonneg ((k : ℝ) - 3 - (⌈Bsq a D.s₀ * |D.μ 2|⌉₊ : ℝ))]
  have hdiv : -(D.μ 2) < ((k : ℝ) ^ 2 - 4) / Bsq a D.s₀ := by
    rw [lt_div_iff₀ hB, mul_comm (-(D.μ 2)) (Bsq a D.s₀)]
    exact hgap
  linarith

/-- **tex eq. `eq:exact-index-formula-reduction`** (Theorem 2.3, the exact
reduction of the index-four conjecture):
`ind(Σ_a) = 4 + 1_{r'(a)<0} + 2 Σ_{k≥2} 1_{μ₀^even(k)<0}`. -/
theorem exact_index_formula {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    D.ind = 4 + (if D.rp < 0 then 1 else 0)
      + 2 * ∑' k : ℕ, (if D.μ (k + 2) < 0 then (1 : ℕ) else 0) := by
  classical
  obtain ⟨N, hN⟩ := D.mu_pos_tail ha
  have hf0 : ∀ k ∉ Finset.range (N + 1 + 1),
      D.NnegE (k + 1) + D.NnegO (k + 1) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    have h2 : 2 ≤ k + 1 := by omega
    rw [(D.evenTail (k + 1) h2).1, (D.oddPos (k + 1) h2).1,
      if_neg (not_lt.mpr (hN (k + 1) (by omega)).le)]
  have hg0 : ∀ k ∉ Finset.range (N + 1),
      (if D.μ (k + 2) < 0 then (1 : ℕ) else 0) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [if_neg (not_lt.mpr (hN (k + 2) (by omega)).le)]
  unfold CatenoidData.ind
  rw [tsum_eq_sum hf0, tsum_eq_sum hg0, Finset.sum_range_succ']
  have hterm : ∀ k ∈ Finset.range (N + 1),
      D.NnegE (k + 1 + 1) + D.NnegO (k + 1 + 1)
        = (if D.μ (k + 2) < 0 then (1 : ℕ) else 0) := by
    intro k _
    have h2 : 2 ≤ k + 2 := by omega
    have hkk : k + 1 + 1 = k + 2 := by omega
    rw [hkk, (D.evenTail (k + 2) h2).1, (D.oddPos (k + 2) h2).1, add_zero]
  rw [Finset.sum_congr rfl hterm]
  have hmode0 := mode_zero_index ha D
  have h01 : D.NnegE (0 + 1) + D.NnegO (0 + 1) = 1 := by simpa using D.mode1neg
  omega

/-- The companion nullity decomposition (proved exactly the same way; the
tex uses it for `eq:strong-equivalence-reduction`):
`nul(Σ_a) = 2 + 1_{r'(a)=0} + 2 Σ_{k≥2} 1_{μ₀^even(k)=0}`. -/
theorem nullity_formula {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    D.nul = 2 + (if D.rp = 0 then 1 else 0)
      + 2 * ∑' k : ℕ, (if D.μ (k + 2) = 0 then (1 : ℕ) else 0) := by
  classical
  obtain ⟨N, hN⟩ := D.mu_pos_tail ha
  have hf0 : ∀ k ∉ Finset.range (N + 1 + 1),
      D.NnulE (k + 1) + D.NnulO (k + 1) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    have h2 : 2 ≤ k + 1 := by omega
    rw [(D.evenTail (k + 1) h2).2, (D.oddPos (k + 1) h2).2,
      if_neg (hN (k + 1) (by omega)).ne']
  have hg0 : ∀ k ∉ Finset.range (N + 1),
      (if D.μ (k + 2) = 0 then (1 : ℕ) else 0) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [if_neg (hN (k + 2) (by omega)).ne']
  unfold CatenoidData.nul
  rw [tsum_eq_sum hf0, tsum_eq_sum hg0, Finset.sum_range_succ']
  have hterm : ∀ k ∈ Finset.range (N + 1),
      D.NnulE (k + 1 + 1) + D.NnulO (k + 1 + 1)
        = (if D.μ (k + 2) = 0 then (1 : ℕ) else 0) := by
    intro k _
    have h2 : 2 ≤ k + 2 := by omega
    have hkk : k + 1 + 1 = k + 2 := by omega
    rw [hkk, (D.evenTail (k + 2) h2).2, (D.oddPos (k + 2) h2).2, add_zero]
  rw [Finset.sum_congr rfl hterm]
  have hE := (mode_zero_even_count ha D).2
  have hO := (lemma_geometric ha D).2.2.2
  have h01 : D.NnulE (0 + 1) + D.NnulO (0 + 1) = 1 := by simpa using D.mode1nul
  omega

/-- **tex eq. `eq:weak-equivalence-reduction`** (Theorem 2.3):
`ind(Σ_a) = 4 ⟺ r'(a) ≥ 0 and μ₀^even(2) ≥ 0`. -/
theorem weak_equivalence {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    D.ind = 4 ↔ 0 ≤ D.rp ∧ 0 ≤ D.μ 2 := by
  classical
  rw [exact_index_formula ha D]
  obtain ⟨N, hN⟩ := D.mu_pos_tail ha
  have hg0 : ∀ k ∉ Finset.range (N + 1),
      (if D.μ (k + 2) < 0 then (1 : ℕ) else 0) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [if_neg (not_lt.mpr (hN (k + 2) (by omega)).le)]
  rw [tsum_eq_sum hg0]
  constructor
  · intro h
    have ht : (if D.rp < 0 then (1 : ℕ) else 0) = 0 := by omega
    have hS : (∑ k ∈ Finset.range (N + 1),
        if D.μ (k + 2) < 0 then (1 : ℕ) else 0) = 0 := by omega
    constructor
    · by_contra hrp
      rw [not_le] at hrp
      rw [if_pos hrp] at ht
      exact one_ne_zero ht
    · by_contra hμ
      rw [not_le] at hμ
      have h0 := Finset.sum_eq_zero_iff.mp hS 0 (Finset.mem_range.mpr (by omega))
      rw [if_pos (by simpa using hμ)] at h0
      exact one_ne_zero h0
  · rintro ⟨hrp, hμ2⟩
    have ht : (if D.rp < 0 then (1 : ℕ) else 0) = 0 := if_neg (not_lt.mpr hrp)
    have hall : ∀ k ∈ Finset.range (N + 1),
        (if D.μ (k + 2) < 0 then (1 : ℕ) else 0) = 0 := by
      intro k _
      have h2 : 2 ≤ k + 2 := by omega
      have hmono := D.μmono (k + 2) h2
      have hgap : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ 2 - 4 := by
        push_cast
        nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
      have hpos : (0 : ℝ) ≤ D.μ (k + 2) := by
        have hdiv : (0 : ℝ) ≤ (((k + 2 : ℕ) : ℝ) ^ 2 - 4) / Bsq a D.s₀ :=
          div_nonneg hgap (Bsq_pos ha D.s₀).le
        linarith
      rw [if_neg (not_lt.mpr hpos)]
    rw [ht, Finset.sum_eq_zero hall]
    norm_num

/-- **tex eq. `eq:strong-equivalence-reduction`** (Theorem 2.3, the strong
form): `ind(Σ_a) = 4` and `nul(Σ_a) = 2` ⟺ `r'(a) > 0` and
`μ₀^even(2) > 0`. -/
theorem strong_equivalence {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    (D.ind = 4 ∧ D.nul = 2) ↔ 0 < D.rp ∧ 0 < D.μ 2 := by
  classical
  obtain ⟨N, hN⟩ := D.mu_pos_tail ha
  have hg0 : ∀ k ∉ Finset.range (N + 1),
      (if D.μ (k + 2) = 0 then (1 : ℕ) else 0) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [if_neg (hN (k + 2) (by omega)).ne']
  constructor
  · rintro ⟨hind, hnul⟩
    obtain ⟨hrp, hμ2⟩ := (weak_equivalence ha D).mp hind
    rw [nullity_formula ha D, tsum_eq_sum hg0] at hnul
    have ht : (if D.rp = 0 then (1 : ℕ) else 0) = 0 := by omega
    have hS : (∑ k ∈ Finset.range (N + 1),
        if D.μ (k + 2) = 0 then (1 : ℕ) else 0) = 0 := by omega
    constructor
    · rcases hrp.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [if_pos h.symm] at ht
        exact one_ne_zero ht
    · rcases hμ2.lt_or_eq with h | h
      · exact h
      · exfalso
        have h0 := Finset.sum_eq_zero_iff.mp hS 0 (Finset.mem_range.mpr (by omega))
        rw [if_pos (by simpa using h.symm)] at h0
        exact one_ne_zero h0
  · rintro ⟨hrp, hμ2⟩
    refine ⟨(weak_equivalence ha D).mpr ⟨hrp.le, hμ2.le⟩, ?_⟩
    rw [nullity_formula ha D, tsum_eq_sum hg0]
    have ht : (if D.rp = 0 then (1 : ℕ) else 0) = 0 := if_neg hrp.ne'
    have hall : ∀ k ∈ Finset.range (N + 1),
        (if D.μ (k + 2) = 0 then (1 : ℕ) else 0) = 0 := by
      intro k _
      have h2 : 2 ≤ k + 2 := by omega
      have hmono := D.μmono (k + 2) h2
      have hgap : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ 2 - 4 := by
        push_cast
        nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
      have hpos : (0 : ℝ) < D.μ (k + 2) := by
        have hdiv : (0 : ℝ) ≤ (((k + 2 : ℕ) : ℝ) ^ 2 - 4) / Bsq a D.s₀ :=
          div_nonneg hgap (Bsq_pos ha D.s₀).le
        linarith
      rw [if_neg hpos.ne']
    rw [ht, Finset.sum_eq_zero hall]
    norm_num

/-! ## Supporting analytic facts for the residual conditions (tex §2–§3) -/

theorem continuous_Bsq (a : ℝ) : Continuous (Bsq a) := by
  unfold Bsq; fun_prop

theorem continuous_B (a : ℝ) : Continuous (B a) := by
  unfold B; exact Real.continuous_sqrt.comp (continuous_Bsq a)

theorem continuous_v {a : ℝ} (ha : 1 / 2 < a) : Continuous (v a) := by
  unfold v
  exact Continuous.div (by fun_prop) (continuous_B a) fun s => (B_pos ha s).ne'

theorem continuous_Q {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) : Continuous (Q a k) := by
  unfold Q
  exact (continuous_const.add (continuous_const.div (continuous_Bsq a)
      fun s => (Bsq_pos ha s).ne')).sub
    (continuous_const.div ((continuous_Bsq a).pow 2)
      fun s => pow_ne_zero 2 (Bsq_pos ha s).ne')

/-- The profile is largest at the boundary: `B(s)² ≤ B₀²` on `[−s₀, s₀]`. -/
theorem Bsq_le {a : ℝ} (ha : 0 < a) {s s₀ : ℝ} (hs : s ∈ Icc (-s₀) s₀) :
    Bsq a s ≤ Bsq a s₀ := by
  have habs : |s| ≤ s₀ := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hs₀ : 0 ≤ s₀ := le_trans (abs_nonneg s) habs
  have h1 : |2 * s| ≤ |2 * s₀| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (habs.trans_eq (abs_of_nonneg hs₀).symm) (abs_nonneg 2)
  have h2 := Real.cosh_le_cosh.mpr h1
  unfold Bsq
  have := mul_le_mul_of_nonneg_left h2 ha.le
  linarith

/-- The pointwise mechanism behind tex eq. `eq:mode-monotonicity-reduction`:
for `k ≥ 2`, `Q_k(s) − Q_2(s) = (k²−4)/B(s)² ≥ (k²−4)/B₀²` on `[−s₀,s₀]`;
integrated against the ground state this yields
`μ₀^even(k) ≥ μ₀^even(2) + (k²−4)/B₀²`. -/
theorem potential_gap {a : ℝ} (ha : 1 / 2 < a) {k : ℕ} (hk : 2 ≤ k)
    {s s₀ : ℝ} (hs : s ∈ Icc (-s₀) s₀) :
    ((k : ℝ) ^ 2 - 4) / Bsq a s₀ ≤ Q a k s - Q a 2 s := by
  have heq : Q a k s - Q a 2 s = ((k : ℝ) ^ 2 - 4) / Bsq a s := by
    unfold Q
    push_cast
    ring
  rw [heq]
  have hnum : (0 : ℝ) ≤ (k : ℝ) ^ 2 - 4 := by
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have h1 : Bsq a s ≤ Bsq a s₀ := Bsq_le (by linarith) hs
  have h2 := Bsq_pos ha s
  gcongr

/-- tex §2, after `eq:k2-picone-reduction`: "For `a>1` the coefficient
`3B²−2K²` is negative near the neck" — its value at the neck `s = 0` is
`3B(0)² − 2K² = −(2a−1)(a−1) < 0`. -/
theorem neck_coeff_neg {a : ℝ} (h1 : 1 < a) : 3 * Bsq a 0 - 2 * Ksq a < 0 := by
  unfold Bsq Ksq
  rw [mul_zero, Real.cosh_zero]
  nlinarith

/-- Combined with Lemma 2.1, the same coefficient is positive at the
boundary (`B₀² > 2K²` and `K² > 0` give `3B₀² − 2K² > 4K² > 0`). -/
theorem boundary_coeff_pos {a : ℝ} (ha : 1 / 2 < a) {s₀ : ℝ}
    (hp : 2 * Ksq a < Bsq a s₀) : 0 < 3 * Bsq a s₀ - 2 * Ksq a := by
  have := Ksq_pos ha
  linarith

/-- The coefficient `3B² − 2K²` is strictly increasing in `s ≥ 0`. -/
theorem coeff_strictMono {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (fun s => 3 * Bsq a s - 2 * Ksq a) (Ici 0) := by
  intro x hx y hy hxy
  simp only
  have h1 : Real.cosh (2 * x) < Real.cosh (2 * y) := by
    rw [Real.cosh_lt_cosh,
      abs_of_nonneg (by linarith [mem_Ici.mp hx] : (0 : ℝ) ≤ 2 * x),
      abs_of_nonneg (by linarith [mem_Ici.mp hx] : (0 : ℝ) ≤ 2 * y)]
    linarith
  unfold Bsq
  nlinarith

/-- **tex §3**: "The factor in parentheses changes sign exactly once."  For
`a > 1` the coefficient `3B² − 2K²` (equivalently `3 − 2K²/B²` after
dividing by `B² > 0`) has exactly one zero between the neck and the
boundary: it is negative at `s = 0` (`neck_coeff_neg`), positive at `s₀`
(by Lemma 2.1 via `boundary_coeff_pos`), and strictly increasing. -/
theorem coeff_unique_root {a : ℝ} (h1 : 1 < a) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hp : 2 * Ksq a < Bsq a s₀) :
    ∃! s, s ∈ Ioo 0 s₀ ∧ 3 * Bsq a s - 2 * Ksq a = 0 := by
  have ha : (1 : ℝ) / 2 < a := by linarith
  have hneg := neck_coeff_neg h1
  have hpos := boundary_coeff_pos ha hp
  have hcont : ContinuousOn (fun s => 3 * Bsq a s - 2 * Ksq a) (Icc 0 s₀) :=
    ((continuous_Bsq a).const_mul 3 |>.sub continuous_const).continuousOn
  have hz : (0 : ℝ) ∈ Ioo (3 * Bsq a 0 - 2 * Ksq a)
      (3 * Bsq a s₀ - 2 * Ksq a) := ⟨hneg, hpos⟩
  obtain ⟨z, hzm, hφz⟩ := intermediate_value_Ioo hs₀.le hcont hz
  have hφz' : 3 * Bsq a z - 2 * Ksq a = 0 := hφz
  refine ⟨z, ⟨hzm, hφz'⟩, ?_⟩
  rintro y ⟨hy, hφy⟩
  exact (coeff_strictMono (show (0 : ℝ) < a by linarith)).injOn
    (mem_Ici.mpr hy.1.le) (mem_Ici.mpr hzm.1.le) (by rw [hφy, hφz'])

/-! ## The mode-two Picone identity (tex eq. `eq:k2-picone-reduction`) -/

/-- **tex eq. `eq:k2-picone-reduction`**, fully formalized: substituting
`u = Bh` into the mode-two Robin quadratic form
`𝒮₂(u,u) = ∫ (B u'² + Q₂ B u²) − coth r · B₀ (u(s₀)² + u(−s₀)²)`
(with `u' = B'h + Bh' = vh + Bh'`) gives
`𝒮₂(Bh,Bh) = ∫ [B³ (h')² + ((3B² − 2K²)/B) h²]`.
The proof is a genuine integration by parts: the pointwise difference of the
two integrands is the exact derivative of `s ↦ a B(s) sinh(2s) h(s)²`, and
the resulting boundary values cancel the Robin term exactly (this uses the
closed formula `coth r = a sinh(2s₀)/B₀²`). -/
theorem picone_identity {a : ℝ} (ha : 1 / 2 < a) (s₀ : ℝ) {h hd : ℝ → ℝ}
    (hh : ∀ s, HasDerivAt h (hd s) s) (hdc : Continuous hd) :
    (∫ s in (-s₀)..s₀,
        (B a s * (v a s * h s + B a s * hd s) ^ 2
          + Q a 2 s * B a s * (B a s * h s) ^ 2))
      - cothr a s₀ * B a s₀
          * ((B a s₀ * h s₀) ^ 2 + (B a (-s₀) * h (-s₀)) ^ 2)
    = ∫ s in (-s₀)..s₀,
        (B a s ^ 3 * hd s ^ 2
          + (3 * Bsq a s - 2 * Ksq a) / B a s * h s ^ 2) := by
  have hhc : Continuous h :=
    Differentiable.continuous fun s => (hh s).differentiableAt
  have hBc := continuous_B a
  have hvc := continuous_v ha
  have hQc := continuous_Q ha 2
  have hshc : Continuous fun x : ℝ => Real.sinh (2 * x) := by fun_prop
  have hchc : Continuous fun x : ℝ => Real.cosh (2 * x) := by fun_prop
  -- Step A: the primitive `P = a·(B sinh(2s))·h²` and its derivative
  have hP : ∀ x : ℝ,
      HasDerivAt (fun t => a * (B a t * Real.sinh (2 * t)) * h t ^ 2)
        (a * (v a x * Real.sinh (2 * x) + B a x * (Real.cosh (2 * x) * 2))
            * h x ^ 2
          + a * (B a x * Real.sinh (2 * x)) * (2 * h x * hd x)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun t : ℝ => B a t * Real.sinh (2 * t))
        (v a x * Real.sinh (2 * x) + B a x * (Real.cosh (2 * x) * 2)) x :=
      (hasDerivAt_B ha x).mul h1.sinh
    have h3 : HasDerivAt (fun t : ℝ => h t ^ 2) (2 * h x * hd x) x := by
      simpa using (hh x).pow 2
    exact (h2.const_mul a).mul h3
  -- Step B: the pointwise integrand identity
  have hkey : ∀ x : ℝ,
      (B a x * (v a x * h x + B a x * hd x) ^ 2
        + Q a 2 x * B a x * (B a x * h x) ^ 2)
      - (B a x ^ 3 * hd x ^ 2
          + (3 * Bsq a x - 2 * Ksq a) / B a x * h x ^ 2)
      = a * (v a x * Real.sinh (2 * x) + B a x * (Real.cosh (2 * x) * 2))
            * h x ^ 2
        + a * (B a x * Real.sinh (2 * x)) * (2 * h x * hd x) := by
    intro x
    have hB := B_pos ha x
    have hBsq := Bsq_pos ha x
    have hB2 : B a x ^ 2 = Bsq a x := B_sq ha x
    have hBv : B a x * v a x = a * Real.sinh (2 * x) := B_mul_v ha x
    have hch : Real.cosh (2 * x) ^ 2 - Real.sinh (2 * x) ^ 2 = 1 :=
      Real.cosh_sq_sub_sinh_sq (2 * x)
    have hq_def : Bsq a x = a * Real.cosh (2 * x) - 1 / 2 := rfl
    have hK_def : Ksq a = a ^ 2 - 1 / 4 := rfl
    unfold Q
    field_simp [hB.ne', hBsq.ne']
    linear_combination
      (Bsq a x ^ 2 * B a x * h x * (2 * B a x * hd x + h x * v a x)) * hBv
      + (2 * h x ^ 2 * (Bsq a x ^ 3 + Bsq a x ^ 2 * B a x ^ 2
          - Bsq a x ^ 2 * a * Real.cosh (2 * x) + 2 * Bsq a x ^ 2
          + 2 * Bsq a x * B a x ^ 2 - Bsq a x * Ksq a
          - B a x ^ 2 * Ksq a)) * hB2
      + (2 * Bsq a x ^ 3 * h x ^ 2) * hq_def
  -- Step C: integrability of all three integrands
  have hi1 : IntervalIntegrable
      (fun s => B a s * (v a s * h s + B a s * hd s) ^ 2
        + Q a 2 s * B a s * (B a s * h s) ^ 2)
      MeasureTheory.volume (-s₀) s₀ :=
    ((hBc.mul (((hvc.mul hhc).add (hBc.mul hdc)).pow 2)).add
      ((hQc.mul hBc).mul ((hBc.mul hhc).pow 2))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun s => B a s ^ 3 * hd s ^ 2
        + (3 * Bsq a s - 2 * Ksq a) / B a s * h s ^ 2)
      MeasureTheory.volume (-s₀) s₀ :=
    (((hBc.pow 3).mul (hdc.pow 2)).add
      ((Continuous.div (((continuous_Bsq a).const_mul 3).sub continuous_const)
          hBc fun s => (B_pos ha s).ne').mul (hhc.pow 2))).intervalIntegrable _ _
  have hPdc : Continuous (fun x =>
      a * (v a x * Real.sinh (2 * x) + B a x * (Real.cosh (2 * x) * 2))
          * h x ^ 2
        + a * (B a x * Real.sinh (2 * x)) * (2 * h x * hd x)) :=
    ((((hvc.mul hshc).add (hBc.mul (hchc.mul continuous_const))).const_mul a).mul
        (hhc.pow 2)).add
      (((hBc.mul hshc).const_mul a).mul ((continuous_const.mul hhc).mul hdc))
  -- Step D: fundamental theorem of calculus for the primitive
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hP x) (hPdc.intervalIntegrable (-s₀) s₀)
  have hsub := intervalIntegral.integral_sub hi1 hi2
  have hcongr : (∫ s in (-s₀)..s₀,
      ((B a s * (v a s * h s + B a s * hd s) ^ 2
        + Q a 2 s * B a s * (B a s * h s) ^ 2)
      - (B a s ^ 3 * hd s ^ 2
          + (3 * Bsq a s - 2 * Ksq a) / B a s * h s ^ 2)))
      = ∫ s in (-s₀)..s₀,
        (a * (v a s * Real.sinh (2 * s) + B a s * (Real.cosh (2 * s) * 2))
            * h s ^ 2
          + a * (B a s * Real.sinh (2 * s)) * (2 * h s * hd s)) :=
    intervalIntegral.integral_congr fun x _ => hkey x
  -- Step E: the boundary values cancel the Robin term
  have hbdry : a * (B a s₀ * Real.sinh (2 * s₀)) * h s₀ ^ 2
      - a * (B a (-s₀) * Real.sinh (2 * (-s₀))) * h (-s₀) ^ 2
      = cothr a s₀ * B a s₀
          * ((B a s₀ * h s₀) ^ 2 + (B a (-s₀) * h (-s₀)) ^ 2) := by
    rw [B_even, mul_neg, Real.sinh_neg]
    unfold cothr
    have hB2 : B a s₀ ^ 2 = Bsq a s₀ := B_sq ha s₀
    field_simp [(Bsq_pos ha s₀).ne']
    linear_combination
      (-(B a s₀ * Real.sinh (2 * s₀)) * (h s₀ ^ 2 + h (-s₀) ^ 2)) * hB2
  linarith [hftc, hsub, hcongr, hbdry]

/-! ## The packaged main theorem and the §3 consequences -/

/-- **tex Theorem 2.3 ("Exact reduction of the index-four conjecture")**,
packaged: the exact index formula `eq:exact-index-formula-reduction`
together with the weak equivalence `eq:weak-equivalence-reduction` and the
strong equivalence `eq:strong-equivalence-reduction`. -/
theorem exact_reduction {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a) :
    D.ind = 4 + (if D.rp < 0 then 1 else 0)
        + 2 * ∑' k : ℕ, (if D.μ (k + 2) < 0 then (1 : ℕ) else 0)
      ∧ (D.ind = 4 ↔ 0 ≤ D.rp ∧ 0 ≤ D.μ 2)
      ∧ ((D.ind = 4 ∧ D.nul = 2) ↔ 0 < D.rp ∧ 0 < D.μ 2) :=
  ⟨exact_index_formula ha D, weak_equivalence ha D, strong_equivalence ha D⟩

/-- tex §3: "a parameter with `r'(a) < 0` would force an additional negative
mode and disprove the index-four conjecture." -/
theorem index_ne_four_of_rp_neg {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a)
    (hrp : D.rp < 0) : D.ind ≠ 4 := fun hind =>
  absurd ((weak_equivalence ha D).mp hind).1 (not_le.mpr hrp)

/-- tex §3: "`r'(a) = 0` does not change the index, but it creates an
additional even mode-zero Jacobi field and therefore violates the strong
nullity statement": the nullity then exceeds `2`. -/
theorem nul_ne_two_of_rp_zero {a : ℝ} (ha : 1 / 2 < a) (D : CatenoidData a)
    (hrp : D.rp = 0) : D.nul ≠ 2 := by
  intro hnul
  rw [nullity_formula ha D, hrp, if_pos rfl] at hnul
  omega

end

end ExactReduction
