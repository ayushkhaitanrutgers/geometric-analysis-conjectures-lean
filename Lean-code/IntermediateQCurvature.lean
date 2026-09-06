import Mathlib

/-!
# Intermediate `Q`-curvature positivity fails in dimension 30 — Lean certification

This file certifies, as far as Mathlib permits, the proofs of the paper

> *An explicit counterexample to intermediate `Q`-curvature positivity in dimension
> thirty*, which specializes the Vétois–Zeitler construction to
> `(m, n) = (4, 30)` and refutes Li–Xu's Conjecture 1.

The paper studies `𝒬_{2k}[u] = u^{-(n+2k)/(n-2m)} (-Δ)^k (u^{(n-2k)/(n-2m)})` on `ℝ³⁰`
with `m = 4`, builds a two-bump family `u_ε = κ ∫ |x-y|^{-22} h_ε(y) dy`, and shows
`0 < c_ε ≤ 𝒬₈[u_ε] ≤ C_ε` everywhere while `𝒬₆[u_ε](0) < 0` for small `ε`.

## What is *fully* proved here (no hypotheses)

* **The constants** (Section 2): the identity of the two forms of `κ` in (2.4)/(eq:kappa)
  (`kappaConst_eq`, `kappaConst_closed_form`, `kappaConst_pos`,
  `kappaConst_eq_eleven_fundamental`), the value and positivity of
  `a₀ = 11Γ(11)/(2⁸Γ(19))` (`a0Const_val`, `a0Const_pos`, `a0Const_bubble`), the Li–Xu
  exponents `19/11, 1, 18/11, 12/11, 2/11` at `(n,m) = (30,4)` (`LiXu_exponents`), and
  the GJMS normalization factors `1/11, 1/12 > 0` of (eq:standard-normalization),
  (eq:q8-standard), (eq:q6-standard) (`standard_normalization_factors`).
* **The bubble identity** (eq:bubble-identity) in radial form (`ρ = |x|²`, radial
  Laplacian `60∂ρ + 4ρ∂ρ²` of `ℝ³⁰` — the transcription of `Δ` on radial profiles):
  `Δ⁴(1+ρ)^{-11} = 451666575360 (1+ρ)^{-19}` by four genuine `deriv` computations
  (`bubble_identity_radial`), with `451666575360 = 2⁸Γ(19)/Γ(11)`
  (`bubble_constant_eq`) and `ψ = W^{19/11}` (eq:W-psi) radially
  (`bubble_psi_relation`).
* **Polyharmonicity of the Riesz kernel** of (eq:fundamental-solution), radially:
  `Δ⁴ ρ^{-11} = 0` away from the pole (`riesz_kernel_polyharmonic`).
* **The two-pole Taylor tables of Lemma 3.1** (eq:A-expansion), (eq:F-degree-six):
  a staged, fully checked truncated-power-series computation.  `denomM`/`denomP` are
  certified as the truncated 11th powers of `1 ∓ 2t + t² + q`
  (`sqM_spec` … `denomM_spec`, `sqP_spec` … `denomP_spec`); the displayed expansion
  `expA` of `A_r/S` is certified by `expA · denom ≡ 1` through weighted degree 6
  (`poleM_inverse_spec`, `poleP_inverse_spec`, `expA_convex_combination`); the table
  `tblF` of `F_r = (A_r/S)^{12/11}` is certified as the generalized-binomial
  combination `∑_{j≤6} binom(12/11,j) Xʲ`, `X = A_r/S - 1`
  (`tblX_spec` … `tblX6_spec`, `genBinom_1211`, `tblF_spec`), and its weight-six
  entries are the paper's `C₆₀, C₄₁, C₂₂, C₀₃` (`tblF_weight_six`).
* **The operator computation of Lemma 3.1** (eq:radial-laplacian),
  (eq:laplacian-coefficients): the operator `Dop = ∂ₜ² + 58∂_q + 4q∂_q²` (the Laplacian
  of `ℝ × ℝ²⁹` on functions of `(t, |z|²)`), implemented with genuine nested `deriv`s,
  applied three times to a *general* weighted-degree-`≤6` polynomial:
  `Δ³F(0) = 720·C₆₀ + 4176·C₄₁ + 43152·C₂₂ + 1424016·C₀₃` (`Dop_cubed_at_origin`; the
  weight-`<6` coefficients all die, exactly as the paper asserts).
* **The sign computation** (eq:eta-polynomial), (eq:negative-exact): combining the two,
  `(-Δ)³` of the certified Taylor polynomial `taylorF η` at the origin equals
  `125042688 - 460505088η² + 557383680η⁴ - 221921280η⁶` (`eta_polynomial`), which at
  `η = 9/11` (i.e. `r = 10`) equals `-43658772480/1771561 < 0` (`two_pole_value`,
  `two_pole_neg`).
* **Remark 3.2**: the polynomial form of (eq:K-identity)
  (`K_identity_polynomial`), `K(10) = -1819115520 < 0` with inner sum `-2842368`
  (`K_at_ten`), and the cross-check `24·K(10) = 11⁶·(-43658772480/1771561)`
  (`K_cross_check`).
* **The two-pole functions on `ℝ³⁰`** (eq:A-r), (eq:F-r): `A_r(0) = r+1`, `F₁₀(0) = 1`,
  `A_r ≥ 0`, and the scaling `A_r^{12/11} = S^{12/11}F_r` (`twoPoleA_zero`,
  `twoPoleF_ten_zero`, `twoPoleA_rpow`).
* **The inequality/limit reasoning of Propositions 2.4 and 3.4**: from the comparison
  estimates to the two-sided bound `11C^{-30/11} ≤ 𝒬₈ ≤ 11C^{30/11}`
  (`Q8_uniform_bounds`), the slow-decay barrier for every `s ≤ 0`
  (`slow_decay_barrier`), the normalization computation
  `(11κ)^{-18/11}κ^{12/11}11^{12/11} = (11κ)^{-6/11}` (`q6_limit_normalization`),
  negativity of the limit value (eq:q6-limit) (`q6_limit_value_neg`), and persistence
  of the sign for small `ε` (`q6_eventually_negative`).

## What is certified *with hypotheses* (transcribed analytic inputs)

`theorem_main_certificate` is the Lean form of Theorem 1.1: it consumes, as explicit
hypotheses, the conclusions of the potential-theoretic Lemmas 2.1–2.3 and 3.3
(smooth positivity of `u_ε`, the two-sided comparisons `C⁻¹ψ ≤ h_ε ≤ Cψ`,
`C⁻¹W ≤ u_ε ≤ CW`, the formula `𝒬₈[u_ε] = 11h_ε u_ε^{-19/11}` from
`(-Δ)⁴u_ε = 11h_ε`, and the convergence of `𝒬₆[u_ε](0)` to the limit (eq:q6-limit))
and concludes: for all sufficiently small `ε > 0`, `𝒬₈[u_ε]` lies between two positive
constants while `𝒬₆[u_ε](0) < 0`.

## What is not formalizable in current Mathlib

Riesz potentials and their elliptic regularity, mollifier convergence in `C⁶`, the
distributional equation `(-Δ)⁴(11Φ * h) = 11h`, and the multi-dimensional chain rule
identifying `Δ` on `ℝ³⁰` with its radial/partial-radial transcriptions `radLap` and
`Dop` used here.  These enter only through the stated hypotheses of
`theorem_main_certificate` and through the (documented) interpretation of `radLap`/
`Dop`/the coefficient tables as the paper's radial Laplacians and Taylor expansions.
-/

/-! ### The normalization constants of Section 2

`omega29` is the (transcribed) volume `|𝕊²⁹| = 2π¹⁵/Γ(15)` of the unit sphere in `ℝ³⁰`;
`kappaConst` is the constant `κ` of \eqref{eq:kappa}; `fundamentalConst n m` is the
constant of the fundamental solution `Γ((n-2m)/2) / (2^{2m} π^{n/2} Γ(m)) · |x|^{2m-n}`
of `(-Δ)^m` on `ℝⁿ` and `a0Const` is the constant `a₀` of
\eqref{eq:background-potential}.  All identities claimed for them in the paper are
proved below from `Real.Gamma` computations. -/

/-- The volume of the unit sphere `𝕊²⁹ ⊂ ℝ³⁰`: `ω₂₉ = 2π¹⁵/Γ(15)`. -/
noncomputable def omega29 : ℝ := 2 * Real.pi ^ 15 / Real.Gamma 15

/-- The constant `κ` of \eqref{eq:kappa} (first displayed form). -/
noncomputable def kappaConst : ℝ :=
  Real.Gamma 12 / (2 ^ 7 * (Nat.factorial 3) * Real.Gamma 15 * omega29)

/-- The constant of the fundamental solution of `(-Δ)^m` on `ℝⁿ`. -/
noncomputable def fundamentalConst (n m : ℕ) : ℝ :=
  Real.Gamma (((n : ℝ) - 2 * m) / 2) / (2 ^ (2 * m) * Real.pi ^ ((n : ℝ) / 2) * Real.Gamma m)

/-- The constant `a₀ = 11Γ(11)/(2⁸Γ(19))` of \eqref{eq:background-potential}. -/
noncomputable def a0Const : ℝ := 11 * Real.Gamma 11 / (2 ^ 8 * Real.Gamma 19)

theorem Gamma_four : Real.Gamma 4 = 6 := by
  rw [show (4:ℝ) = (3:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

theorem Gamma_eleven : Real.Gamma 11 = 3628800 := by
  rw [show (11:ℝ) = (10:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

theorem Gamma_twelve : Real.Gamma 12 = 39916800 := by
  rw [show (12:ℝ) = (11:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

theorem Gamma_fifteen : Real.Gamma 15 = 87178291200 := by
  rw [show (15:ℝ) = (14:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

theorem Gamma_nineteen : Real.Gamma 19 = 6402373705728000 := by
  rw [show (19:ℝ) = (18:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

/-- **The identity of the two displayed forms of `κ` in \eqref{eq:kappa}**:
`Γ(12)/(2⁷·3!·Γ(15)·ω₂₉) = 11Γ(11)/(2⁸π¹⁵Γ(4))`. -/
theorem kappaConst_eq :
    kappaConst = 11 * Real.Gamma 11 / (2 ^ 8 * Real.pi ^ 15 * Real.Gamma 4) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [kappaConst, omega29, Gamma_eleven, Gamma_twelve, Gamma_fifteen, Gamma_four]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- Closed form of `κ`. -/
theorem kappaConst_closed_form : kappaConst = 51975 / (2 * Real.pi ^ 15) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [kappaConst_eq, Gamma_eleven, Gamma_four]
  field_simp
  ring

theorem kappaConst_pos : 0 < kappaConst := by
  rw [kappaConst_closed_form]
  have hπ : 0 < Real.pi ^ 15 := pow_pos Real.pi_pos 15
  positivity

/-- The fundamental-solution constant of Lemma 2.1 specializes at `(n,m) = (30,4)` to
`Γ(11)/(2⁸π¹⁵Γ(4))`, so that `κ = 11 · Φ`-constant: `u_ε = 11 Φ * h_ε` solves
`(-Δ)⁴u_ε = 11 h_ε`, which is \eqref{eq:top-equation}. -/
theorem kappaConst_eq_eleven_fundamental : kappaConst = 11 * fundamentalConst 30 4 := by
  rw [kappaConst_eq, fundamentalConst]
  have e1 : (((30:ℕ) : ℝ) - 2 * (4:ℕ)) / 2 = 11 := by norm_num
  have e2 : (((30:ℕ) : ℝ)) / 2 = ((15:ℕ) : ℝ) := by norm_num
  rw [e1, e2, Real.rpow_natCast]
  norm_num
  ring

/-- `a₀ = 11/451666575360`, in particular `a₀ > 0` (Lemma 2.3's background constant). -/
theorem a0Const_val : a0Const = 11 / 451666575360 := by
  rw [a0Const, Gamma_eleven, Gamma_nineteen]
  norm_num

theorem a0Const_pos : 0 < a0Const := by rw [a0Const_val]; norm_num

/-- Consistency of \eqref{eq:background-potential} with \eqref{eq:bubble-identity}:
`a₀ · (2⁸ Γ(19)/Γ(11)) = 11`, i.e. convolving the bubble identity with `11Φ`
sends `2⁸(Γ(19)/Γ(11))ψ` to `11·(a₀/11)·` that constant `= 11 ψ`-potential `= a₀ W`. -/
theorem a0Const_bubble : a0Const * (2 ^ 8 * Real.Gamma 19 / Real.Gamma 11) = 11 := by
  rw [a0Const, Gamma_eleven, Gamma_nineteen]
  norm_num

/-- **The Li–Xu exponents at `(n,m) = (30,4)`** entering \eqref{eq:LX-definition}:
`(n+2k)/(n-2m)` and `(n-2k)/(n-2m)` for `k = 4` and `k = 3`, and the conformal
exponent `4/(n-2m) = 2/11` of the metric `g = u^{2/11}|dx|²`. -/
theorem LiXu_exponents :
    ((30:ℝ) + 2*4) / (30 - 2*4) = 19/11 ∧ ((30:ℝ) - 2*4) / (30 - 2*4) = 1 ∧
    ((30:ℝ) + 2*3) / (30 - 2*4) = 18/11 ∧ ((30:ℝ) - 2*3) / (30 - 2*4) = 12/11 ∧
    (4:ℝ) / (30 - 2*4) = 2/11 := by
  norm_num

/-- **The GJMS normalization factors** of \eqref{eq:standard-normalization} at
`(n,m) = (30,4)`: `2/(n-8) = 1/11` and `2/(n-6) = 1/12`, both positive — so
\eqref{eq:q8-standard} and \eqref{eq:q6-standard} hold and sign statements transfer
between the two normalizations. -/
theorem standard_normalization_factors :
    (2:ℝ) / (30 - 2*4) = 1/11 ∧ (2:ℝ) / (30 - 2*3) = 1/12 ∧
    (0:ℝ) < 2 / (30 - 2*4) ∧ (0:ℝ) < 2 / (30 - 2*3) := by
  norm_num

/-! ### Radial calculus -/

/-- The radial form of the Euclidean Laplacian on `ℝ³⁰` acting on profiles in the
variable `ρ = |x|²`:  `Δ f(|x|²) = 60 f'(ρ) + 4 ρ f''(ρ)` (since `2n = 60` for `n = 30`). -/
noncomputable def radLap (f : ℝ → ℝ) : ℝ → ℝ :=
  fun ρ => 60 * deriv f ρ + 4 * ρ * deriv (deriv f) ρ

/-- Derivative of `c / (1+x)^(k+1)` away from `x = -1`. -/
theorem hasDerivAt_inv_shift_pow (c : ℝ) (k : ℕ) {ρ : ℝ} (h : (1:ℝ) + ρ ≠ 0) :
    HasDerivAt (fun x : ℝ => c / (1+x)^(k+1)) (-(c*(k+1)) / (1+ρ)^(k+2)) ρ := by
  have hb : HasDerivAt (fun x : ℝ => (1+x)^(k+1)) ((k+1)*(1+ρ)^k) ρ := by
    have h1 : HasDerivAt (fun x : ℝ => 1+x) 1 ρ := by
      simpa using (hasDerivAt_id ρ).const_add 1
    simpa using h1.pow (k+1)
  have hd := (hasDerivAt_const ρ c).div hb (pow_ne_zero (k+1) h)
  convert hd using 1
  field_simp
  ring

/-- Derivative of `c / x^(k+1)` away from `x = 0`. -/
theorem hasDerivAt_inv_pow' (c : ℝ) (k : ℕ) {ρ : ℝ} (h : ρ ≠ 0) :
    HasDerivAt (fun x : ℝ => c / x^(k+1)) (-(c*(k+1)) / ρ^(k+2)) ρ := by
  have hb : HasDerivAt (fun x : ℝ => x^(k+1)) ((k+1)*ρ^k) ρ := by
    simpa using hasDerivAt_pow (k+1) ρ
  have hd := (hasDerivAt_const ρ c).div hb (pow_ne_zero (k+1) h)
  convert hd using 1
  field_simp
  ring

/-- `radLap` only depends on the restriction of the profile to an open set. -/
theorem radLap_congr {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (h : ∀ x ∈ U, f x = g x) :
    ∀ x ∈ U, radLap f x = radLap g x := by
  intro x hx
  have hfg : f =ᶠ[nhds x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  have hd : ∀ y ∈ U, deriv f y = deriv g y := fun y hy =>
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) h)
  have hdd : deriv f =ᶠ[nhds x] deriv g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hd
  simp only [radLap, hfg.deriv_eq, hdd.deriv_eq]

section BubbleIdentity

/-- The open set on which the spherical-bubble computation takes place. -/
def shiftedDomain : Set ℝ := {x : ℝ | (1:ℝ) + x ≠ 0}

theorem isOpen_shiftedDomain : IsOpen shiftedDomain := by
  have : shiftedDomain = (fun x : ℝ => 1 + x) ⁻¹' {y : ℝ | y ≠ 0} := rfl
  rw [this]
  exact isOpen_ne.preimage (continuous_const.add continuous_id)

theorem radLap_W0 : ∀ ρ ∈ shiftedDomain,
    radLap (fun x => 1/(1+x)^11) ρ = (-132)/(1+ρ)^12 + (-528)/(1+ρ)^13 := by
  intro ρ h
  have hd : ∀ y ∈ shiftedDomain, deriv (fun x : ℝ => 1/(1+x)^11) y = (-11)/(1+y)^12 := by
    intro y hy
    have h1 := hasDerivAt_inv_shift_pow 1 10 hy
    norm_num at h1
    have h1' : HasDerivAt (fun x : ℝ => 1/(1+x)^11) ((-11)/(1+y)^12) y := by
      simpa using h1
    exact h1'.deriv
  have hdd : deriv (fun x : ℝ => 1/(1+x)^11) =ᶠ[nhds ρ] fun y => (-11)/(1+y)^12 :=
    Filter.eventuallyEq_of_mem (isOpen_shiftedDomain.mem_nhds h) hd
  have h2 : HasDerivAt (fun y : ℝ => (-11)/(1+y)^12) (132/(1+ρ)^13) ρ := by
    have := hasDerivAt_inv_shift_pow (-11) 11 h
    norm_num at this
    exact this
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : (1:ℝ) + ρ ≠ 0 := h
  field_simp
  ring

theorem radLap_W1 : ∀ ρ ∈ shiftedDomain,
    radLap (fun x => (-132)/(1+x)^12 + (-528)/(1+x)^13) ρ
      = 12672/(1+ρ)^13 + 109824/(1+ρ)^14 + 384384/(1+ρ)^15 := by
  intro ρ h
  have hd : ∀ y ∈ shiftedDomain, deriv (fun x : ℝ => (-132)/(1+x)^12 + (-528)/(1+x)^13) y
      = 1584/(1+y)^13 + 6864/(1+y)^14 := by
    intro y hy
    have h1 := hasDerivAt_inv_shift_pow (-132) 11 hy
    have h2 := hasDerivAt_inv_shift_pow (-528) 12 hy
    norm_num at h1 h2
    exact (h1.fun_add h2).deriv
  have hdd : deriv (fun x : ℝ => (-132)/(1+x)^12 + (-528)/(1+x)^13)
      =ᶠ[nhds ρ] fun y => 1584/(1+y)^13 + 6864/(1+y)^14 :=
    Filter.eventuallyEq_of_mem (isOpen_shiftedDomain.mem_nhds h) hd
  have h2 : HasDerivAt (fun y : ℝ => 1584/(1+y)^13 + 6864/(1+y)^14)
      ((-20592)/(1+ρ)^14 + (-96096)/(1+ρ)^15) ρ := by
    have h1 := hasDerivAt_inv_shift_pow 1584 12 h
    have h2 := hasDerivAt_inv_shift_pow 6864 13 h
    norm_num at h1 h2
    exact h1.fun_add h2
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : (1:ℝ) + ρ ≠ 0 := h
  field_simp
  ring

theorem radLap_W2 : ∀ ρ ∈ shiftedDomain,
    radLap (fun x => 12672/(1+x)^13 + 109824/(1+x)^14 + 384384/(1+x)^15) ρ
      = (-658944)/(1+ρ)^14 + (-9225216)/(1+ρ)^15 + (-69189120)/(1+ρ)^16
        + (-369008640)/(1+ρ)^17 := by
  intro ρ h
  have hd : ∀ y ∈ shiftedDomain,
      deriv (fun x : ℝ => 12672/(1+x)^13 + 109824/(1+x)^14 + 384384/(1+x)^15) y
      = (-164736)/(1+y)^14 + (-1537536)/(1+y)^15 + (-5765760)/(1+y)^16 := by
    intro y hy
    have h1 := hasDerivAt_inv_shift_pow 12672 12 hy
    have h2 := hasDerivAt_inv_shift_pow 109824 13 hy
    have h3 := hasDerivAt_inv_shift_pow 384384 14 hy
    norm_num at h1 h2 h3
    exact ((h1.fun_add h2).fun_add h3).deriv
  have hdd : deriv (fun x : ℝ => 12672/(1+x)^13 + 109824/(1+x)^14 + 384384/(1+x)^15)
      =ᶠ[nhds ρ] fun y => (-164736)/(1+y)^14 + (-1537536)/(1+y)^15 + (-5765760)/(1+y)^16 :=
    Filter.eventuallyEq_of_mem (isOpen_shiftedDomain.mem_nhds h) hd
  have h2 : HasDerivAt
      (fun y : ℝ => (-164736)/(1+y)^14 + (-1537536)/(1+y)^15 + (-5765760)/(1+y)^16)
      (2306304/(1+ρ)^15 + 23063040/(1+ρ)^16 + 92252160/(1+ρ)^17) ρ := by
    have h1 := hasDerivAt_inv_shift_pow (-164736) 13 h
    have h2 := hasDerivAt_inv_shift_pow (-1537536) 14 h
    have h3 := hasDerivAt_inv_shift_pow (-5765760) 15 h
    norm_num at h1 h2 h3
    exact (h1.fun_add h2).fun_add h3
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : (1:ℝ) + ρ ≠ 0 := h
  field_simp
  ring

theorem radLap_W3 : ∀ ρ ∈ shiftedDomain,
    radLap (fun x => (-658944)/(1+x)^14 + (-9225216)/(1+x)^15 + (-69189120)/(1+x)^16
        + (-369008640)/(1+x)^17) ρ
      = 451666575360/(1+ρ)^19 := by
  intro ρ h
  have hd : ∀ y ∈ shiftedDomain,
      deriv (fun x : ℝ => (-658944)/(1+x)^14 + (-9225216)/(1+x)^15 + (-69189120)/(1+x)^16
        + (-369008640)/(1+x)^17) y
      = 9225216/(1+y)^15 + 138378240/(1+y)^16 + 1107025920/(1+y)^17
        + 6273146880/(1+y)^18 := by
    intro y hy
    have h1 := hasDerivAt_inv_shift_pow (-658944) 13 hy
    have h2 := hasDerivAt_inv_shift_pow (-9225216) 14 hy
    have h3 := hasDerivAt_inv_shift_pow (-69189120) 15 hy
    have h4 := hasDerivAt_inv_shift_pow (-369008640) 16 hy
    norm_num at h1 h2 h3 h4
    exact (((h1.fun_add h2).fun_add h3).fun_add h4).deriv
  have hdd : deriv (fun x : ℝ => (-658944)/(1+x)^14 + (-9225216)/(1+x)^15
        + (-69189120)/(1+x)^16 + (-369008640)/(1+x)^17)
      =ᶠ[nhds ρ] fun y => 9225216/(1+y)^15 + 138378240/(1+y)^16 + 1107025920/(1+y)^17
        + 6273146880/(1+y)^18 :=
    Filter.eventuallyEq_of_mem (isOpen_shiftedDomain.mem_nhds h) hd
  have h2 : HasDerivAt (fun y : ℝ => 9225216/(1+y)^15 + 138378240/(1+y)^16
        + 1107025920/(1+y)^17 + 6273146880/(1+y)^18)
      ((-138378240)/(1+ρ)^16 + (-2214051840)/(1+ρ)^17 + (-18819440640)/(1+ρ)^18
        + (-112916643840)/(1+ρ)^19) ρ := by
    have h1 := hasDerivAt_inv_shift_pow 9225216 14 h
    have h2 := hasDerivAt_inv_shift_pow 138378240 15 h
    have h3 := hasDerivAt_inv_shift_pow 1107025920 16 h
    have h4 := hasDerivAt_inv_shift_pow 6273146880 17 h
    norm_num at h1 h2 h3 h4
    exact ((h1.fun_add h2).fun_add h3).fun_add h4
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : (1:ℝ) + ρ ≠ 0 := h
  field_simp
  ring

/-- **Certification of the bubble identity \eqref{eq:bubble-identity}** in radial form:
four applications of the radial Laplacian `Δ = 60 ∂ρ + 4ρ ∂ρ²` of `ℝ³⁰` to the profile
`W(ρ) = (1+ρ)^{-11}` of the spherical bubble produce
`451666575360 (1+ρ)^{-19} = 2⁸ (Γ(19)/Γ(11)) ψ(ρ)`, with `ψ = W^{19/11}` the profile of
`(1+|x|²)^{-19}`.  Since `(-Δ)⁴ = Δ⁴`, this is `(-Δ)⁴ W = 2⁸ (Γ(19)/Γ(11)) ψ`. -/
theorem bubble_identity_radial : ∀ ρ ∈ shiftedDomain,
    radLap (radLap (radLap (radLap (fun x => 1/(1+x)^11)))) ρ
      = 451666575360/(1+ρ)^19 := by
  intro ρ h
  have r1 : ∀ x ∈ shiftedDomain, radLap (radLap (fun y : ℝ => 1/(1+y)^11)) x
      = (12672/(1+x)^13 + 109824/(1+x)^14 + 384384/(1+x)^15) := fun x hx =>
    (radLap_congr isOpen_shiftedDomain radLap_W0 x hx).trans (radLap_W1 x hx)
  have r2 : ∀ x ∈ shiftedDomain, radLap (radLap (radLap (fun y : ℝ => 1/(1+y)^11))) x
      = ((-658944)/(1+x)^14 + (-9225216)/(1+x)^15 + (-69189120)/(1+x)^16
        + (-369008640)/(1+x)^17) := fun x hx =>
    (radLap_congr isOpen_shiftedDomain r1 x hx).trans (radLap_W2 x hx)
  exact (radLap_congr isOpen_shiftedDomain r2 ρ h).trans (radLap_W3 ρ h)

/-- The numerical constant in the bubble identity is exactly `2⁸ Γ(19)/Γ(11)`. -/
theorem bubble_constant_eq : (2:ℝ)^8 * Real.Gamma 19 / Real.Gamma 11 = 451666575360 := by
  have g19 : Real.Gamma 19 = 6402373705728000 := by
    rw [show (19:ℝ) = (18:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have g11 : Real.Gamma 11 = 3628800 := by
    rw [show (11:ℝ) = (10:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [g19, g11]
  norm_num

/-- **Certification of \eqref{eq:W-psi} in radial form**: the source of the bubble
identity is `ψ = W^{19/11}`, i.e. `((1+ρ)^{-11})^{19/11} = (1+ρ)^{-19}`. -/
theorem bubble_psi_relation (ρ : ℝ) (h : (0:ℝ) < 1 + ρ) :
    (1/(1+ρ)^11 : ℝ) ^ ((19:ℝ)/11) = 1/(1+ρ)^19 := by
  have h11 : ((1+ρ)^(11:ℕ) : ℝ) = (1+ρ) ^ ((11:ℕ):ℝ) := (Real.rpow_natCast _ 11).symm
  have h19 : ((1+ρ)^(19:ℕ) : ℝ) = (1+ρ) ^ ((19:ℕ):ℝ) := (Real.rpow_natCast _ 19).symm
  rw [one_div, one_div, h11, h19, ← Real.rpow_neg h.le, ← Real.rpow_neg h.le,
    ← Real.rpow_mul h.le]
  norm_num

end BubbleIdentity

section Polyharmonic

/-- The kernel domain `ρ = |x|² ≠ 0`, i.e. `x ≠ 0`. -/
theorem isOpen_ne_zero : IsOpen {x : ℝ | x ≠ 0} := isOpen_ne

theorem radLap_K0 : ∀ ρ ∈ {x : ℝ | x ≠ 0},
    radLap (fun x => 1/x^11) ρ = (-132)/ρ^12 := by
  intro ρ h
  have hd : ∀ y ∈ {x : ℝ | x ≠ 0}, deriv (fun x : ℝ => 1/x^11) y = (-11)/y^12 := by
    intro y hy
    have h1 := hasDerivAt_inv_pow' 1 10 hy
    norm_num at h1
    have h1' : HasDerivAt (fun x : ℝ => 1/x^11) ((-11)/y^12) y := by
      simpa using h1
    exact h1'.deriv
  have hdd : deriv (fun x : ℝ => 1/x^11) =ᶠ[nhds ρ] fun y => (-11)/y^12 :=
    Filter.eventuallyEq_of_mem (isOpen_ne_zero.mem_nhds h) hd
  have h2 : HasDerivAt (fun y : ℝ => (-11)/y^12) (132/ρ^13) ρ := by
    have := hasDerivAt_inv_pow' (-11) 11 h
    norm_num at this
    exact this
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : ρ ≠ 0 := h
  field_simp
  ring

theorem radLap_K1 : ∀ ρ ∈ {x : ℝ | x ≠ 0},
    radLap (fun x => (-132)/x^12) ρ = 12672/ρ^13 := by
  intro ρ h
  have hd : ∀ y ∈ {x : ℝ | x ≠ 0}, deriv (fun x : ℝ => (-132)/x^12) y = 1584/y^13 := by
    intro y hy
    have h1 := hasDerivAt_inv_pow' (-132) 11 hy
    norm_num at h1
    exact h1.deriv
  have hdd : deriv (fun x : ℝ => (-132)/x^12) =ᶠ[nhds ρ] fun y => 1584/y^13 :=
    Filter.eventuallyEq_of_mem (isOpen_ne_zero.mem_nhds h) hd
  have h2 : HasDerivAt (fun y : ℝ => 1584/y^13) ((-20592)/ρ^14) ρ := by
    have := hasDerivAt_inv_pow' 1584 12 h
    norm_num at this
    exact this
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : ρ ≠ 0 := h
  field_simp
  ring

theorem radLap_K2 : ∀ ρ ∈ {x : ℝ | x ≠ 0},
    radLap (fun x => 12672/x^13) ρ = (-658944)/ρ^14 := by
  intro ρ h
  have hd : ∀ y ∈ {x : ℝ | x ≠ 0}, deriv (fun x : ℝ => 12672/x^13) y = (-164736)/y^14 := by
    intro y hy
    have h1 := hasDerivAt_inv_pow' 12672 12 hy
    norm_num at h1
    exact h1.deriv
  have hdd : deriv (fun x : ℝ => 12672/x^13) =ᶠ[nhds ρ] fun y => (-164736)/y^14 :=
    Filter.eventuallyEq_of_mem (isOpen_ne_zero.mem_nhds h) hd
  have h2 : HasDerivAt (fun y : ℝ => (-164736)/y^14) (2306304/ρ^15) ρ := by
    have := hasDerivAt_inv_pow' (-164736) 13 h
    norm_num at this
    exact this
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : ρ ≠ 0 := h
  field_simp
  ring

theorem radLap_K3 : ∀ ρ ∈ {x : ℝ | x ≠ 0},
    radLap (fun x => (-658944)/x^14) ρ = 0 := by
  intro ρ h
  have hd : ∀ y ∈ {x : ℝ | x ≠ 0}, deriv (fun x : ℝ => (-658944)/x^14) y = 9225216/y^15 := by
    intro y hy
    have h1 := hasDerivAt_inv_pow' (-658944) 13 hy
    norm_num at h1
    exact h1.deriv
  have hdd : deriv (fun x : ℝ => (-658944)/x^14) =ᶠ[nhds ρ] fun y => 9225216/y^15 :=
    Filter.eventuallyEq_of_mem (isOpen_ne_zero.mem_nhds h) hd
  have h2 : HasDerivAt (fun y : ℝ => 9225216/y^15) ((-138378240)/ρ^16) ρ := by
    have := hasDerivAt_inv_pow' 9225216 14 h
    norm_num at this
    exact this
  rw [radLap, hd ρ h, hdd.deriv_eq, h2.deriv]
  have h0 : ρ ≠ 0 := h
  field_simp
  ring

/-- **The Riesz kernel `|x|^{-22}` is 4-harmonic away from its pole** (the key property
of the fundamental solution \eqref{eq:fundamental-solution} of `(-Δ)⁴` on `ℝ³⁰`), in
radial form: four applications of `Δ = 60 ∂ρ + 4ρ ∂ρ²` to `ρ^{-11}` give zero. -/
theorem riesz_kernel_polyharmonic : ∀ ρ ∈ {x : ℝ | x ≠ 0},
    radLap (radLap (radLap (radLap (fun x => 1/x^11)))) ρ = 0 := by
  intro ρ h
  have r1 : ∀ x ∈ {x : ℝ | x ≠ 0}, radLap (radLap (fun y : ℝ => 1/y^11)) x
      = 12672/x^13 := fun x hx =>
    (radLap_congr isOpen_ne_zero radLap_K0 x hx).trans (radLap_K1 x hx)
  have r2 : ∀ x ∈ {x : ℝ | x ≠ 0}, radLap (radLap (radLap (fun y : ℝ => 1/y^11))) x
      = (-658944)/x^14 := fun x hx =>
    (radLap_congr isOpen_ne_zero r1 x hx).trans (radLap_K2 x hx)
  exact (radLap_congr isOpen_ne_zero r2 ρ h).trans (radLap_K3 ρ h)

end Polyharmonic

/-! ### Formal truncated power-series algebra for Lemma 3.1 (the two-pole calculation)

We work with coefficient tables `ℕ → ℕ → ℝ` for polynomials/power series
`∑ c(a,b) t^a q^b` in the variables `t = x₁`, `q = |z|²` of the paper, truncated to
weighted degree `a + 2b ≤ 6` (weight one for `t`, weight two for `q`).  `mulC` is the
coefficient formula for the product of two such series; on the corner `a + 2b ≤ 6` it
only reads corner entries of its factors, so all staged identities below are exact
statements about the corresponding real-analytic Taylor expansions. -/

-- The staged table lemmas below use `first`-combinator fallbacks; on entries where the
-- primary branch already closes the goal the fallbacks are (harmlessly) unreachable.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Coefficient of `t^a q^b` in the product of the series with coefficients `P`, `Q`. -/
def mulC (P Q : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1), P i j * Q (a-i) (b-j)

/-- The constant series `1`. -/
def oneC (a b : ℕ) : ℝ := if a = 0 ∧ b = 0 then 1 else 0

/-- `1 - 2t + t² + q`, i.e. `|x - e₁|²` in the coordinates of Lemma 3.1. -/
def baseM (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then -2 else
  if a = 0 ∧ b = 1 then 1 else
  if a = 2 ∧ b = 0 then 1 else
  0

/-- `1 + 2t + t² + q`, i.e. `|x + e₁|²` in the coordinates of Lemma 3.1. -/
def baseP (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 2 else
  if a = 0 ∧ b = 1 then 1 else
  if a = 2 ∧ b = 0 then 1 else
  0

/-- `(1-2t+t²+q)²` (truncated). -/
def sqM (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then -4 else
  if a = 0 ∧ b = 1 then 2 else
  if a = 2 ∧ b = 0 then 6 else
  if a = 1 ∧ b = 1 then -4 else
  if a = 3 ∧ b = 0 then -4 else
  if a = 0 ∧ b = 2 then 1 else
  if a = 2 ∧ b = 1 then 2 else
  if a = 4 ∧ b = 0 then 1 else
  0

/-- `(1-2t+t²+q)⁴` (truncated). -/
def pow4M (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then -8 else
  if a = 0 ∧ b = 1 then 4 else
  if a = 2 ∧ b = 0 then 28 else
  if a = 1 ∧ b = 1 then -24 else
  if a = 3 ∧ b = 0 then -56 else
  if a = 0 ∧ b = 2 then 6 else
  if a = 2 ∧ b = 1 then 60 else
  if a = 4 ∧ b = 0 then 70 else
  if a = 1 ∧ b = 2 then -24 else
  if a = 3 ∧ b = 1 then -80 else
  if a = 5 ∧ b = 0 then -56 else
  if a = 0 ∧ b = 3 then 4 else
  if a = 2 ∧ b = 2 then 36 else
  if a = 4 ∧ b = 1 then 60 else
  if a = 6 ∧ b = 0 then 28 else
  0

/-- `(1-2t+t²+q)⁸` (truncated). -/
def pow8M (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then -16 else
  if a = 0 ∧ b = 1 then 8 else
  if a = 2 ∧ b = 0 then 120 else
  if a = 1 ∧ b = 1 then -112 else
  if a = 3 ∧ b = 0 then -560 else
  if a = 0 ∧ b = 2 then 28 else
  if a = 2 ∧ b = 1 then 728 else
  if a = 4 ∧ b = 0 then 1820 else
  if a = 1 ∧ b = 2 then -336 else
  if a = 3 ∧ b = 1 then -2912 else
  if a = 5 ∧ b = 0 then -4368 else
  if a = 0 ∧ b = 3 then 56 else
  if a = 2 ∧ b = 2 then 1848 else
  if a = 4 ∧ b = 1 then 8008 else
  if a = 6 ∧ b = 0 then 8008 else
  0

/-- `(1-2t+t²+q)¹⁰` (truncated). -/
def pow10M (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then -20 else
  if a = 0 ∧ b = 1 then 10 else
  if a = 2 ∧ b = 0 then 190 else
  if a = 1 ∧ b = 1 then -180 else
  if a = 3 ∧ b = 0 then -1140 else
  if a = 0 ∧ b = 2 then 45 else
  if a = 2 ∧ b = 1 then 1530 else
  if a = 4 ∧ b = 0 then 4845 else
  if a = 1 ∧ b = 2 then -720 else
  if a = 3 ∧ b = 1 then -8160 else
  if a = 5 ∧ b = 0 then -15504 else
  if a = 0 ∧ b = 3 then 120 else
  if a = 2 ∧ b = 2 then 5400 else
  if a = 4 ∧ b = 1 then 30600 else
  if a = 6 ∧ b = 0 then 38760 else
  0

/-- `(1-2t+t²+q)¹¹` (truncated): the denominator of the first pole. -/
def denomM (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then -22 else
  if a = 0 ∧ b = 1 then 11 else
  if a = 2 ∧ b = 0 then 231 else
  if a = 1 ∧ b = 1 then -220 else
  if a = 3 ∧ b = 0 then -1540 else
  if a = 0 ∧ b = 2 then 55 else
  if a = 2 ∧ b = 1 then 2090 else
  if a = 4 ∧ b = 0 then 7315 else
  if a = 1 ∧ b = 2 then -990 else
  if a = 3 ∧ b = 1 then -12540 else
  if a = 5 ∧ b = 0 then -26334 else
  if a = 0 ∧ b = 3 then 165 else
  if a = 2 ∧ b = 2 then 8415 else
  if a = 4 ∧ b = 1 then 53295 else
  if a = 6 ∧ b = 0 then 74613 else
  0

/-- `(1+2t+t²+q)²` (truncated). -/
def sqP (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 4 else
  if a = 0 ∧ b = 1 then 2 else
  if a = 2 ∧ b = 0 then 6 else
  if a = 1 ∧ b = 1 then 4 else
  if a = 3 ∧ b = 0 then 4 else
  if a = 0 ∧ b = 2 then 1 else
  if a = 2 ∧ b = 1 then 2 else
  if a = 4 ∧ b = 0 then 1 else
  0

/-- `(1+2t+t²+q)⁴` (truncated). -/
def pow4P (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 8 else
  if a = 0 ∧ b = 1 then 4 else
  if a = 2 ∧ b = 0 then 28 else
  if a = 1 ∧ b = 1 then 24 else
  if a = 3 ∧ b = 0 then 56 else
  if a = 0 ∧ b = 2 then 6 else
  if a = 2 ∧ b = 1 then 60 else
  if a = 4 ∧ b = 0 then 70 else
  if a = 1 ∧ b = 2 then 24 else
  if a = 3 ∧ b = 1 then 80 else
  if a = 5 ∧ b = 0 then 56 else
  if a = 0 ∧ b = 3 then 4 else
  if a = 2 ∧ b = 2 then 36 else
  if a = 4 ∧ b = 1 then 60 else
  if a = 6 ∧ b = 0 then 28 else
  0

/-- `(1+2t+t²+q)⁸` (truncated). -/
def pow8P (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 16 else
  if a = 0 ∧ b = 1 then 8 else
  if a = 2 ∧ b = 0 then 120 else
  if a = 1 ∧ b = 1 then 112 else
  if a = 3 ∧ b = 0 then 560 else
  if a = 0 ∧ b = 2 then 28 else
  if a = 2 ∧ b = 1 then 728 else
  if a = 4 ∧ b = 0 then 1820 else
  if a = 1 ∧ b = 2 then 336 else
  if a = 3 ∧ b = 1 then 2912 else
  if a = 5 ∧ b = 0 then 4368 else
  if a = 0 ∧ b = 3 then 56 else
  if a = 2 ∧ b = 2 then 1848 else
  if a = 4 ∧ b = 1 then 8008 else
  if a = 6 ∧ b = 0 then 8008 else
  0

/-- `(1+2t+t²+q)¹⁰` (truncated). -/
def pow10P (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 20 else
  if a = 0 ∧ b = 1 then 10 else
  if a = 2 ∧ b = 0 then 190 else
  if a = 1 ∧ b = 1 then 180 else
  if a = 3 ∧ b = 0 then 1140 else
  if a = 0 ∧ b = 2 then 45 else
  if a = 2 ∧ b = 1 then 1530 else
  if a = 4 ∧ b = 0 then 4845 else
  if a = 1 ∧ b = 2 then 720 else
  if a = 3 ∧ b = 1 then 8160 else
  if a = 5 ∧ b = 0 then 15504 else
  if a = 0 ∧ b = 3 then 120 else
  if a = 2 ∧ b = 2 then 5400 else
  if a = 4 ∧ b = 1 then 30600 else
  if a = 6 ∧ b = 0 then 38760 else
  0

/-- `(1+2t+t²+q)¹¹` (truncated): the denominator of the second pole. -/
def denomP (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 22 else
  if a = 0 ∧ b = 1 then 11 else
  if a = 2 ∧ b = 0 then 231 else
  if a = 1 ∧ b = 1 then 220 else
  if a = 3 ∧ b = 0 then 1540 else
  if a = 0 ∧ b = 2 then 55 else
  if a = 2 ∧ b = 1 then 2090 else
  if a = 4 ∧ b = 0 then 7315 else
  if a = 1 ∧ b = 2 then 990 else
  if a = 3 ∧ b = 1 then 12540 else
  if a = 5 ∧ b = 0 then 26334 else
  if a = 0 ∧ b = 3 then 165 else
  if a = 2 ∧ b = 2 then 8415 else
  if a = 4 ∧ b = 1 then 53295 else
  if a = 6 ∧ b = 0 then 74613 else
  0

/-- The paper's display \eqref{eq:A-expansion}: the weighted-degree-`≤ 6` Taylor table of
`A_r/S = ((1+η)/2)(1-2t+t²+q)^{-11} + ((1-η)/2)(1+2t+t²+q)^{-11}`, `η = (r-1)/(r+1)`. -/
def expA (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 22*η else
  if a = 0 ∧ b = 1 then -11 else
  if a = 2 ∧ b = 0 then 253 else
  if a = 1 ∧ b = 1 then -264*η else
  if a = 3 ∧ b = 0 then 2024*η else
  if a = 0 ∧ b = 2 then 66 else
  if a = 2 ∧ b = 1 then -3300 else
  if a = 4 ∧ b = 0 then 12650 else
  if a = 1 ∧ b = 2 then 1716*η else
  if a = 3 ∧ b = 1 then -28600*η else
  if a = 5 ∧ b = 0 then 65780*η else
  if a = 0 ∧ b = 3 then -286 else
  if a = 2 ∧ b = 2 then 23166 else
  if a = 4 ∧ b = 1 then -193050 else
  if a = 6 ∧ b = 0 then 296010 else
  0

/-- `X := A_r/S - 1` (the quantity whose powers enter the binomial expansion). -/
def tblX (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 1 ∧ b = 0 then 22*η else
  if a = 0 ∧ b = 1 then -11 else
  if a = 2 ∧ b = 0 then 253 else
  if a = 1 ∧ b = 1 then -264*η else
  if a = 3 ∧ b = 0 then 2024*η else
  if a = 0 ∧ b = 2 then 66 else
  if a = 2 ∧ b = 1 then -3300 else
  if a = 4 ∧ b = 0 then 12650 else
  if a = 1 ∧ b = 2 then 1716*η else
  if a = 3 ∧ b = 1 then -28600*η else
  if a = 5 ∧ b = 0 then 65780*η else
  if a = 0 ∧ b = 3 then -286 else
  if a = 2 ∧ b = 2 then 23166 else
  if a = 4 ∧ b = 1 then -193050 else
  if a = 6 ∧ b = 0 then 296010 else
  0

/-- `X^2` (truncated). -/
def tblX2 (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 2 ∧ b = 0 then 484*η^2 else
  if a = 1 ∧ b = 1 then -484*η else
  if a = 3 ∧ b = 0 then 11132*η else
  if a = 0 ∧ b = 2 then 121 else
  if a = 2 ∧ b = 1 then -5566 - 11616*η^2 else
  if a = 4 ∧ b = 0 then 64009 + 89056*η^2 else
  if a = 1 ∧ b = 2 then 8712*η else
  if a = 3 ∧ b = 1 then -323312*η else
  if a = 5 ∧ b = 0 then 1580744*η else
  if a = 0 ∧ b = 3 then -1452 else
  if a = 2 ∧ b = 2 then 105996 + 145200*η^2 else
  if a = 4 ∧ b = 1 then -1948100 - 2327072*η^2 else
  if a = 6 ∧ b = 0 then 6400900 + 6990896*η^2 else
  0

/-- `X^3` (truncated). -/
def tblX3 (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 3 ∧ b = 0 then 10648*η^3 else
  if a = 2 ∧ b = 1 then -15972*η^2 else
  if a = 4 ∧ b = 0 then 367356*η^2 else
  if a = 1 ∧ b = 2 then 7986*η else
  if a = 3 ∧ b = 1 then -367356*η - 383328*η^3 else
  if a = 5 ∧ b = 0 then 4224594*η + 2938848*η^3 else
  if a = 0 ∧ b = 3 then -1331 else
  if a = 2 ∧ b = 2 then 91839 + 479160*η^2 else
  if a = 4 ∧ b = 1 then -2112297 - 16546992*η^2 else
  if a = 6 ∧ b = 0 then 16194277 + 85961304*η^2 else
  0

/-- `X^4` (truncated). -/
def tblX4 (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 4 ∧ b = 0 then 234256*η^4 else
  if a = 3 ∧ b = 1 then -468512*η^3 else
  if a = 5 ∧ b = 0 then 10775776*η^3 else
  if a = 2 ∧ b = 2 then 351384*η^2 else
  if a = 4 ∧ b = 1 then -16163664*η^2 - 11244288*η^4 else
  if a = 6 ∧ b = 0 then 185882136*η^2 + 86206208*η^4 else
  0

/-- `X^5` (truncated). -/
def tblX5 (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 5 ∧ b = 0 then 5153632*η^5 else
  if a = 4 ∧ b = 1 then -12884080*η^4 else
  if a = 6 ∧ b = 0 then 296333840*η^4 else
  0

/-- `X^6` (truncated). -/
def tblX6 (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 6 ∧ b = 0 then 113379904*η^6 else
  0

/-- The paper's display \eqref{eq:F-degree-six} together with all lower-order terms: the
weighted-degree-`≤ 6` Taylor table of `F_r = (A_r/S)^{12/11}`.  Its four weight-six
entries are exactly the coefficients `C₆₀, C₄₁, C₂₂, C₀₃` displayed in Lemma 3.1. -/
def tblF (η : ℝ) (a b : ℕ) : ℝ :=
  if a = 0 ∧ b = 0 then 1 else
  if a = 1 ∧ b = 0 then 24*η else
  if a = 0 ∧ b = 1 then -12 else
  if a = 2 ∧ b = 0 then 276 + 24*η^2 else
  if a = 1 ∧ b = 1 then -312*η else
  if a = 3 ∧ b = 0 then 2760*η - 160*η^3 else
  if a = 0 ∧ b = 2 then 78 else
  if a = 2 ∧ b = 1 then -3876 - 336*η^2 else
  if a = 4 ∧ b = 0 then 16974 - 1104*η^2 + 1680*η^4 else
  if a = 1 ∧ b = 2 then 2184*η else
  if a = 3 ∧ b = 1 then -41712*η + 2400*η^3 else
  if a = 5 ∧ b = 0 then 86664*η + 33120*η^3 - 21504*η^5 else
  if a = 0 ∧ b = 3 then -364 else
  if a = 2 ∧ b = 2 then 29148 + 2520*η^2 else
  if a = 4 ∧ b = 1 then -275460 + 17328*η^2 - 26880*η^4 else
  if a = 6 ∧ b = 0 then 396980 + 388056*η^2 - 618240*η^4 + 308224*η^6 else
  0

/-! #### Staged certification of the tables

Each lemma below is a finite, fully checked identity between coefficient tables on the
corner `a + 2b ≤ 6`.  Chained together they certify the displayed Taylor tables:
the eleventh power of the base gives the pole denominators, `expA · denom` is `1`
(so `expA` is the correct expansion of the two-pole sum), and `tblF` is the
generalized-binomial combination `∑_j binom(12/11, j) X^j`. -/

theorem sqM_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC baseM baseM a b = sqM a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, baseM, sqM]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, baseM, sqM]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, baseM, sqM]; ring)

theorem pow4M_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC sqM sqM a b = pow4M a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, sqM, pow4M]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, sqM, pow4M]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, sqM, pow4M]; ring)

theorem pow8M_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC pow4M pow4M a b = pow8M a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow4M, pow8M]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow4M, pow8M]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow4M, pow8M]; ring)

theorem pow10M_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC pow8M sqM a b = pow10M a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow8M, sqM, pow10M]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow8M, sqM, pow10M]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow8M, sqM, pow10M]; ring)

theorem denomM_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC pow10M baseM a b = denomM a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow10M, baseM, denomM]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow10M, baseM, denomM]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow10M, baseM, denomM]; ring)

theorem sqP_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC baseP baseP a b = sqP a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, baseP, sqP]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, baseP, sqP]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, baseP, sqP]; ring)

theorem pow4P_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC sqP sqP a b = pow4P a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, sqP, pow4P]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, sqP, pow4P]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, sqP, pow4P]; ring)

theorem pow8P_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC pow4P pow4P a b = pow8P a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow4P, pow8P]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow4P, pow8P]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow4P, pow8P]; ring)

theorem pow10P_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC pow8P sqP a b = pow10P a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow8P, sqP, pow10P]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow8P, sqP, pow10P]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow8P, sqP, pow10P]; ring)

theorem denomP_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC pow10P baseP a b = denomP a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow10P, baseP, denomP]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow10P, baseP, denomP]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, pow10P, baseP, denomP]; ring)

/-- `expA` at `η = 1` is the reciprocal of `(1-2t+t²+q)¹¹` through weighted degree 6:
this certifies the generalized-binomial expansion of the first pole `|x-e₁|^{-22}`. -/
theorem poleM_inverse_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC (expA 1) denomM a b = oneC a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, expA, denomM, oneC]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, expA, denomM, oneC]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, expA, denomM, oneC]; ring)

/-- `expA` at `η = -1` is the reciprocal of `(1+2t+t²+q)¹¹` through weighted degree 6:
this certifies the expansion of the second pole `|x+e₁|^{-22}`. -/
theorem poleP_inverse_spec : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC (expA (-1)) denomP a b = oneC a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, expA, denomP, oneC]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, expA, denomP, oneC]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, expA, denomP, oneC]; ring)

/-- The two-pole table is the convex combination of the two single-pole tables with
weights `(1+η)/2` and `(1-η)/2`, exactly as in \eqref{eq:A-r}. -/
theorem expA_convex_combination (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    expA η a b = (1+η)/2 * expA 1 a b + (1-η)/2 * expA (-1) a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [expA]; norm_num; done)
      | (simp only [expA]; norm_num; ring)
      | (simp only [expA]; ring)

/-- `X = A_r/S - 1`. -/
theorem tblX_spec (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    tblX η a b = expA η a b - oneC a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [expA, tblX, oneC]; norm_num; done)
      | (simp only [expA, tblX, oneC]; norm_num; ring)
      | (simp only [expA, tblX, oneC]; ring)

theorem tblX2_spec (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC (tblX η) (tblX η) a b = tblX2 η a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX2]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX2]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX2]; ring)

theorem tblX3_spec (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC (tblX η) (tblX2 η) a b = tblX3 η a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX2, tblX3]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX2, tblX3]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX2, tblX3]; ring)

theorem tblX4_spec (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC (tblX η) (tblX3 η) a b = tblX4 η a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX3, tblX4]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX3, tblX4]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX3, tblX4]; ring)

theorem tblX5_spec (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC (tblX η) (tblX4 η) a b = tblX5 η a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX4, tblX5]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX4, tblX5]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX4, tblX5]; ring)

theorem tblX6_spec (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    mulC (tblX η) (tblX5 η) a b = tblX6 η a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX5, tblX6]; norm_num; done)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX5, tblX6]; norm_num; ring)
      | (simp only [mulC, Finset.sum_range_succ, Finset.sum_range_zero, tblX, tblX5, tblX6]; ring)

/-- The generalized binomial coefficients `binom(12/11, j)` for `j = 0, …, 6`,
via the standard product formula (the paper's display after \eqref{eq:F-degree-six}). -/
noncomputable def genBinom (α : ℝ) (j : ℕ) : ℝ :=
  (∏ i ∈ Finset.range j, (α - i)) / (Nat.factorial j)

theorem genBinom_1211 :
    genBinom (12/11) 0 = 1 ∧ genBinom (12/11) 1 = 12/11 ∧ genBinom (12/11) 2 = (6/121) ∧
    genBinom (12/11) 3 = (-20/1331) ∧ genBinom (12/11) 4 = (105/14641) ∧
    genBinom (12/11) 5 = (-672/161051) ∧ genBinom (12/11) 6 = (4816/1771561) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (norm_num [genBinom, Finset.prod_range_succ, Nat.factorial]; try ring)

/-- The Taylor table of `F_r = (A_r/S)^{12/11}` is the generalized-binomial combination
`∑_{j≤6} binom(12/11, j) · X^j` of the certified powers of `X = A_r/S - 1`.
Together with the staged lemmas above this certifies every displayed coefficient of
\eqref{eq:A-expansion} and \eqref{eq:F-degree-six}. -/
theorem tblF_spec (η : ℝ) : ∀ a b : ℕ, a + 2*b ≤ 6 →
    tblF η a b = oneC a b + (12/11) * tblX η a b + (6/121) * tblX2 η a b
      + (-20/1331) * tblX3 η a b + (105/14641) * tblX4 η a b
      + (-672/161051) * tblX5 η a b + (4816/1771561) * tblX6 η a b := by
  intro a b hab
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first
      | omega
      | (simp only [oneC, tblX, tblX2, tblX3, tblX4, tblX5, tblX6, tblF]; norm_num; done)
      | (simp only [oneC, tblX, tblX2, tblX3, tblX4, tblX5, tblX6, tblF]; norm_num; ring)
      | (simp only [oneC, tblX, tblX2, tblX3, tblX4, tblX5, tblX6, tblF]; ring)

/-- The four weight-six entries of the certified table are exactly the coefficients
`C₆₀, C₄₁, C₂₂, C₀₃` displayed in the proof of Lemma 3.1. -/
theorem tblF_weight_six (η : ℝ) :
    tblF η 6 0 = 396980 + 388056*η^2 - 618240*η^4 + 308224*η^6 ∧
    tblF η 4 1 = -275460 + 17328*η^2 - 26880*η^4 ∧
    tblF η 2 2 = 29148 + 2520*η^2 ∧
    tblF η 0 3 = -364 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [tblF]; norm_num)

/-! ### The iterated operator `Δ = ∂ₜ² + 58 ∂_q + 4q ∂_q²` acting on Taylor polynomials

`Dop` is the paper's display \eqref{eq:radial-laplacian}: the Euclidean Laplacian of
`ℝ × ℝ²⁹` acting on functions of `t = x₁` and `q = |z|²` (so `58 = 2·29`).  Below it is
applied three times, with genuine `deriv`-computations, to a completely general
polynomial of weighted degree `≤ 6`; the result certifies the paper's display
\eqref{eq:laplacian-coefficients}: only the four weight-six coefficients survive, with
the weights `720, 4176, 43152, 1424016`. -/

/-- The operator `∂ₜ² + 58 ∂_q + 4q ∂_q²` of \eqref{eq:radial-laplacian}, as an operator
on functions of the two real variables `(t, q)`, via genuine one-dimensional `deriv`s. -/
noncomputable def Dop (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t q =>
  deriv (fun s : ℝ => deriv (fun s' : ℝ => f s' q) s) t
    + 58 * deriv (fun r : ℝ => f t r) q
    + 4 * q * deriv (fun r : ℝ => deriv (fun r' : ℝ => f t r') r) q

/-- Derivative of a general sextic. -/
theorem hasDerivAt_poly6 (a b c d e f g x : ℝ) :
    HasDerivAt (fun s : ℝ => a*s^6 + b*s^5 + c*s^4 + d*s^3 + e*s^2 + f*s + g)
      (6*a*x^5 + 5*b*x^4 + 4*c*x^3 + 3*d*x^2 + 2*e*x + f) x := by
  have h := ((((((HasDerivAt.const_mul a (hasDerivAt_pow 6 x)).fun_add
      (HasDerivAt.const_mul b (hasDerivAt_pow 5 x))).fun_add
      (HasDerivAt.const_mul c (hasDerivAt_pow 4 x))).fun_add
      (HasDerivAt.const_mul d (hasDerivAt_pow 3 x))).fun_add
      (HasDerivAt.const_mul e (hasDerivAt_pow 2 x))).fun_add
      (HasDerivAt.const_mul f (hasDerivAt_id' x))).fun_add
      (hasDerivAt_const x g)
  convert h using 1
  push_cast
  ring

/-- Derivative of a general cubic. -/
theorem hasDerivAt_poly3 (a b c d x : ℝ) :
    HasDerivAt (fun s : ℝ => a*s^3 + b*s^2 + c*s + d) (3*a*x^2 + 2*b*x + c) x := by
  have h := (((HasDerivAt.const_mul a (hasDerivAt_pow 3 x)).fun_add
      (HasDerivAt.const_mul b (hasDerivAt_pow 2 x))).fun_add
      (HasDerivAt.const_mul c (hasDerivAt_id' x))).fun_add (hasDerivAt_const x d)
  convert h using 1
  push_cast
  ring

theorem Dop_stage1 (a00 a10 a20 a01 a30 a11 a40 a21 a02 a50 a31 a12 a60 a41 a22 a03 : ℝ) :
    Dop (fun t q : ℝ => a60*t^6 + a50*t^5 + a41*t^4*q + a40*t^4 + a31*t^3*q + a30*t^3 + a22*t^2*q^2 + a21*t^2*q + a20*t^2 + a12*t*q^2 + a11*t*q + a10*t + a03*q^3 + a02*q^2 + a01*q + a00)
      = (fun t q : ℝ => (58*a41 + 30*a60)*t^4 + (58*a31 + 20*a50)*t^3 + (124*a22 + 12*a41)*t^2*q + (58*a21 + 12*a40)*t^2 + (124*a12 + 6*a31)*t*q + (58*a11 + 6*a30)*t + (198*a03 + 2*a22)*q^2 + (124*a02 + 2*a21)*q + (58*a01 + 2*a20)) := by
  funext t q
  simp only [Dop]
  have ht : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => a60*s'^6 + a50*s'^5 + a41*s'^4*q + a40*s'^4 + a31*s'^3*q + a30*s'^3 + a22*s'^2*q^2 + a21*s'^2*q + a20*s'^2 + a12*s'*q^2 + a11*s'*q + a10*s' + a03*q^3 + a02*q^2 + a01*q + a00)
      (6*a60*s^5 + 5*a50*s^4 + 4*(a41*q + a40)*s^3 + 3*(a31*q + a30)*s^2 + 2*(a22*q^2 + a21*q + a20)*s + (a12*q^2 + a11*q + a10)) s := by
    intro s
    have e : (fun s' : ℝ => a60*s'^6 + a50*s'^5 + a41*s'^4*q + a40*s'^4 + a31*s'^3*q + a30*s'^3 + a22*s'^2*q^2 + a21*s'^2*q + a20*s'^2 + a12*s'*q^2 + a11*s'*q + a10*s' + a03*q^3 + a02*q^2 + a01*q + a00)
        = (fun u : ℝ => a60*u^6 + a50*u^5 + (a41*q + a40)*u^4 + (a31*q + a30)*u^3 + (a22*q^2 + a21*q + a20)*u^2 + (a12*q^2 + a11*q + a10)*u + (a03*q^3 + a02*q^2 + a01*q + a00)) := by
      funext u; ring
    rw [e]
    exact hasDerivAt_poly6 _ _ _ _ _ _ _ s
  have het : (fun s : ℝ => deriv (fun s' : ℝ => a60*s'^6 + a50*s'^5 + a41*s'^4*q + a40*s'^4 + a31*s'^3*q + a30*s'^3 + a22*s'^2*q^2 + a21*s'^2*q + a20*s'^2 + a12*s'*q^2 + a11*s'*q + a10*s' + a03*q^3 + a02*q^2 + a01*q + a00) s)
      = (fun s : ℝ => 6*a60*s^5 + 5*a50*s^4 + 4*(a41*q + a40)*s^3 + 3*(a31*q + a30)*s^2 + 2*(a22*q^2 + a21*q + a20)*s + (a12*q^2 + a11*q + a10)) := funext fun s => (ht s).deriv
  have htt : HasDerivAt (fun s : ℝ => 6*a60*s^5 + 5*a50*s^4 + 4*(a41*q + a40)*s^3 + 3*(a31*q + a30)*s^2 + 2*(a22*q^2 + a21*q + a20)*s + (a12*q^2 + a11*q + a10))
      (6*0*t^5 + 5*(6*a60)*t^4 + 4*(5*a50)*t^3 + 3*(4*(a41*q + a40))*t^2 + 2*(3*(a31*q + a30))*t + (2*(a22*q^2 + a21*q + a20))) t := by
    have e : (fun s : ℝ => 6*a60*s^5 + 5*a50*s^4 + 4*(a41*q + a40)*s^3 + 3*(a31*q + a30)*s^2 + 2*(a22*q^2 + a21*q + a20)*s + (a12*q^2 + a11*q + a10))
        = (fun u : ℝ => 0*u^6 + (6*a60)*u^5 + (5*a50)*u^4 + (4*(a41*q + a40))*u^3 + (3*(a31*q + a30))*u^2 + (2*(a22*q^2 + a21*q + a20))*u + (a12*q^2 + a11*q + a10)) := by
      funext u; ring
    rw [e]
    have h := hasDerivAt_poly6 0 (6*a60) (5*a50) (4*(a41*q + a40)) (3*(a31*q + a30)) (2*(a22*q^2 + a21*q + a20)) (a12*q^2 + a11*q + a10) t
    convert h using 1
    try ring
  have hq : ∀ r : ℝ, HasDerivAt (fun r' : ℝ => a60*t^6 + a50*t^5 + a41*t^4*r' + a40*t^4 + a31*t^3*r' + a30*t^3 + a22*t^2*r'^2 + a21*t^2*r' + a20*t^2 + a12*t*r'^2 + a11*t*r' + a10*t + a03*r'^3 + a02*r'^2 + a01*r' + a00)
      (3*a03*r^2 + 2*(a22*t^2 + a12*t + a02)*r + (a41*t^4 + a31*t^3 + a21*t^2 + a11*t + a01)) r := by
    intro r
    have e : (fun r' : ℝ => a60*t^6 + a50*t^5 + a41*t^4*r' + a40*t^4 + a31*t^3*r' + a30*t^3 + a22*t^2*r'^2 + a21*t^2*r' + a20*t^2 + a12*t*r'^2 + a11*t*r' + a10*t + a03*r'^3 + a02*r'^2 + a01*r' + a00)
        = (fun u : ℝ => a03*u^3 + (a22*t^2 + a12*t + a02)*u^2 + (a41*t^4 + a31*t^3 + a21*t^2 + a11*t + a01)*u + (a60*t^6 + a50*t^5 + a40*t^4 + a30*t^3 + a20*t^2 + a10*t + a00)) := by
      funext u; ring
    rw [e]
    exact hasDerivAt_poly3 _ _ _ _ r
  have heq : (fun r : ℝ => deriv (fun r' : ℝ => a60*t^6 + a50*t^5 + a41*t^4*r' + a40*t^4 + a31*t^3*r' + a30*t^3 + a22*t^2*r'^2 + a21*t^2*r' + a20*t^2 + a12*t*r'^2 + a11*t*r' + a10*t + a03*r'^3 + a02*r'^2 + a01*r' + a00) r)
      = (fun r : ℝ => 3*a03*r^2 + 2*(a22*t^2 + a12*t + a02)*r + (a41*t^4 + a31*t^3 + a21*t^2 + a11*t + a01)) := funext fun r => (hq r).deriv
  have hqq : HasDerivAt (fun r : ℝ => 3*a03*r^2 + 2*(a22*t^2 + a12*t + a02)*r + (a41*t^4 + a31*t^3 + a21*t^2 + a11*t + a01))
      (3*0*q^2 + 2*(3*a03)*q + (2*(a22*t^2 + a12*t + a02))) q := by
    have e : (fun r : ℝ => 3*a03*r^2 + 2*(a22*t^2 + a12*t + a02)*r + (a41*t^4 + a31*t^3 + a21*t^2 + a11*t + a01))
        = (fun u : ℝ => 0*u^3 + (3*a03)*u^2 + (2*(a22*t^2 + a12*t + a02))*u + (a41*t^4 + a31*t^3 + a21*t^2 + a11*t + a01)) := by
      funext u; ring
    rw [e]
    have h := hasDerivAt_poly3 0 (3*a03) (2*(a22*t^2 + a12*t + a02)) (a41*t^4 + a31*t^3 + a21*t^2 + a11*t + a01) q
    convert h using 1
    try ring
  rw [het, heq, htt.deriv, (hq q).deriv, hqq.deriv]
  ring

theorem Dop_stage2 (a20 a01 a30 a11 a40 a21 a02 a50 a31 a12 a60 a41 a22 a03 : ℝ) :
    Dop (fun t q : ℝ => (58*a41 + 30*a60)*t^4 + (58*a31 + 20*a50)*t^3 + (124*a22 + 12*a41)*t^2*q + (58*a21 + 12*a40)*t^2 + (124*a12 + 6*a31)*t*q + (58*a11 + 6*a30)*t + (198*a03 + 2*a22)*q^2 + (124*a02 + 2*a21)*q + (58*a01 + 2*a20))
      = (fun t q : ℝ => (7192*a22 + 1392*a41 + 360*a60)*t^2 + (7192*a12 + 696*a31 + 120*a50)*t + (24552*a03 + 496*a22 + 24*a41)*q + (7192*a02 + 232*a21 + 24*a40)) := by
  funext t q
  simp only [Dop]
  have ht : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => (58*a41 + 30*a60)*s'^4 + (58*a31 + 20*a50)*s'^3 + (124*a22 + 12*a41)*s'^2*q + (58*a21 + 12*a40)*s'^2 + (124*a12 + 6*a31)*s'*q + (58*a11 + 6*a30)*s' + (198*a03 + 2*a22)*q^2 + (124*a02 + 2*a21)*q + (58*a01 + 2*a20))
      (6*0*s^5 + 5*0*s^4 + 4*((58*a41 + 30*a60))*s^3 + 3*((58*a31 + 20*a50))*s^2 + 2*((124*a22 + 12*a41)*q + (58*a21 + 12*a40))*s + ((124*a12 + 6*a31)*q + (58*a11 + 6*a30))) s := by
    intro s
    have e : (fun s' : ℝ => (58*a41 + 30*a60)*s'^4 + (58*a31 + 20*a50)*s'^3 + (124*a22 + 12*a41)*s'^2*q + (58*a21 + 12*a40)*s'^2 + (124*a12 + 6*a31)*s'*q + (58*a11 + 6*a30)*s' + (198*a03 + 2*a22)*q^2 + (124*a02 + 2*a21)*q + (58*a01 + 2*a20))
        = (fun u : ℝ => 0*u^6 + 0*u^5 + ((58*a41 + 30*a60))*u^4 + ((58*a31 + 20*a50))*u^3 + ((124*a22 + 12*a41)*q + (58*a21 + 12*a40))*u^2 + ((124*a12 + 6*a31)*q + (58*a11 + 6*a30))*u + ((198*a03 + 2*a22)*q^2 + (124*a02 + 2*a21)*q + (58*a01 + 2*a20))) := by
      funext u; ring
    rw [e]
    exact hasDerivAt_poly6 _ _ _ _ _ _ _ s
  have het : (fun s : ℝ => deriv (fun s' : ℝ => (58*a41 + 30*a60)*s'^4 + (58*a31 + 20*a50)*s'^3 + (124*a22 + 12*a41)*s'^2*q + (58*a21 + 12*a40)*s'^2 + (124*a12 + 6*a31)*s'*q + (58*a11 + 6*a30)*s' + (198*a03 + 2*a22)*q^2 + (124*a02 + 2*a21)*q + (58*a01 + 2*a20)) s)
      = (fun s : ℝ => 6*0*s^5 + 5*0*s^4 + 4*((58*a41 + 30*a60))*s^3 + 3*((58*a31 + 20*a50))*s^2 + 2*((124*a22 + 12*a41)*q + (58*a21 + 12*a40))*s + ((124*a12 + 6*a31)*q + (58*a11 + 6*a30))) := funext fun s => (ht s).deriv
  have htt : HasDerivAt (fun s : ℝ => 6*0*s^5 + 5*0*s^4 + 4*((58*a41 + 30*a60))*s^3 + 3*((58*a31 + 20*a50))*s^2 + 2*((124*a22 + 12*a41)*q + (58*a21 + 12*a40))*s + ((124*a12 + 6*a31)*q + (58*a11 + 6*a30)))
      (6*0*t^5 + 5*(6*0)*t^4 + 4*(5*0)*t^3 + 3*(4*((58*a41 + 30*a60)))*t^2 + 2*(3*((58*a31 + 20*a50)))*t + (2*((124*a22 + 12*a41)*q + (58*a21 + 12*a40)))) t := by
    have e : (fun s : ℝ => 6*0*s^5 + 5*0*s^4 + 4*((58*a41 + 30*a60))*s^3 + 3*((58*a31 + 20*a50))*s^2 + 2*((124*a22 + 12*a41)*q + (58*a21 + 12*a40))*s + ((124*a12 + 6*a31)*q + (58*a11 + 6*a30)))
        = (fun u : ℝ => 0*u^6 + (6*0)*u^5 + (5*0)*u^4 + (4*((58*a41 + 30*a60)))*u^3 + (3*((58*a31 + 20*a50)))*u^2 + (2*((124*a22 + 12*a41)*q + (58*a21 + 12*a40)))*u + ((124*a12 + 6*a31)*q + (58*a11 + 6*a30))) := by
      funext u; ring
    rw [e]
    have h := hasDerivAt_poly6 0 (6*0) (5*0) (4*((58*a41 + 30*a60))) (3*((58*a31 + 20*a50))) (2*((124*a22 + 12*a41)*q + (58*a21 + 12*a40))) ((124*a12 + 6*a31)*q + (58*a11 + 6*a30)) t
    convert h using 1
    try ring
  have hq : ∀ r : ℝ, HasDerivAt (fun r' : ℝ => (58*a41 + 30*a60)*t^4 + (58*a31 + 20*a50)*t^3 + (124*a22 + 12*a41)*t^2*r' + (58*a21 + 12*a40)*t^2 + (124*a12 + 6*a31)*t*r' + (58*a11 + 6*a30)*t + (198*a03 + 2*a22)*r'^2 + (124*a02 + 2*a21)*r' + (58*a01 + 2*a20))
      (3*0*r^2 + 2*((198*a03 + 2*a22))*r + ((124*a22 + 12*a41)*t^2 + (124*a12 + 6*a31)*t + (124*a02 + 2*a21))) r := by
    intro r
    have e : (fun r' : ℝ => (58*a41 + 30*a60)*t^4 + (58*a31 + 20*a50)*t^3 + (124*a22 + 12*a41)*t^2*r' + (58*a21 + 12*a40)*t^2 + (124*a12 + 6*a31)*t*r' + (58*a11 + 6*a30)*t + (198*a03 + 2*a22)*r'^2 + (124*a02 + 2*a21)*r' + (58*a01 + 2*a20))
        = (fun u : ℝ => 0*u^3 + ((198*a03 + 2*a22))*u^2 + ((124*a22 + 12*a41)*t^2 + (124*a12 + 6*a31)*t + (124*a02 + 2*a21))*u + ((58*a41 + 30*a60)*t^4 + (58*a31 + 20*a50)*t^3 + (58*a21 + 12*a40)*t^2 + (58*a11 + 6*a30)*t + (58*a01 + 2*a20))) := by
      funext u; ring
    rw [e]
    exact hasDerivAt_poly3 _ _ _ _ r
  have heq : (fun r : ℝ => deriv (fun r' : ℝ => (58*a41 + 30*a60)*t^4 + (58*a31 + 20*a50)*t^3 + (124*a22 + 12*a41)*t^2*r' + (58*a21 + 12*a40)*t^2 + (124*a12 + 6*a31)*t*r' + (58*a11 + 6*a30)*t + (198*a03 + 2*a22)*r'^2 + (124*a02 + 2*a21)*r' + (58*a01 + 2*a20)) r)
      = (fun r : ℝ => 3*0*r^2 + 2*((198*a03 + 2*a22))*r + ((124*a22 + 12*a41)*t^2 + (124*a12 + 6*a31)*t + (124*a02 + 2*a21))) := funext fun r => (hq r).deriv
  have hqq : HasDerivAt (fun r : ℝ => 3*0*r^2 + 2*((198*a03 + 2*a22))*r + ((124*a22 + 12*a41)*t^2 + (124*a12 + 6*a31)*t + (124*a02 + 2*a21)))
      (3*0*q^2 + 2*(3*0)*q + (2*((198*a03 + 2*a22)))) q := by
    have e : (fun r : ℝ => 3*0*r^2 + 2*((198*a03 + 2*a22))*r + ((124*a22 + 12*a41)*t^2 + (124*a12 + 6*a31)*t + (124*a02 + 2*a21)))
        = (fun u : ℝ => 0*u^3 + (3*0)*u^2 + (2*((198*a03 + 2*a22)))*u + ((124*a22 + 12*a41)*t^2 + (124*a12 + 6*a31)*t + (124*a02 + 2*a21))) := by
      funext u; ring
    rw [e]
    have h := hasDerivAt_poly3 0 (3*0) (2*((198*a03 + 2*a22))) ((124*a22 + 12*a41)*t^2 + (124*a12 + 6*a31)*t + (124*a02 + 2*a21)) q
    convert h using 1
    try ring
  rw [het, heq, htt.deriv, (hq q).deriv, hqq.deriv]
  ring

set_option linter.unusedVariables false in
theorem Dop_stage3 (a40 a21 a02 a50 a31 a12 a60 a41 a22 a03 : ℝ) :
    Dop (fun t q : ℝ => (7192*a22 + 1392*a41 + 360*a60)*t^2 + (7192*a12 + 696*a31 + 120*a50)*t + (24552*a03 + 496*a22 + 24*a41)*q + (7192*a02 + 232*a21 + 24*a40))
      = (fun t q : ℝ => (1424016*a03 + 43152*a22 + 4176*a41 + 720*a60)) := by
  funext t q
  simp only [Dop]
  have ht : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => (7192*a22 + 1392*a41 + 360*a60)*s'^2 + (7192*a12 + 696*a31 + 120*a50)*s' + (24552*a03 + 496*a22 + 24*a41)*q + (7192*a02 + 232*a21 + 24*a40))
      (6*0*s^5 + 5*0*s^4 + 4*0*s^3 + 3*0*s^2 + 2*((7192*a22 + 1392*a41 + 360*a60))*s + ((7192*a12 + 696*a31 + 120*a50))) s := by
    intro s
    have e : (fun s' : ℝ => (7192*a22 + 1392*a41 + 360*a60)*s'^2 + (7192*a12 + 696*a31 + 120*a50)*s' + (24552*a03 + 496*a22 + 24*a41)*q + (7192*a02 + 232*a21 + 24*a40))
        = (fun u : ℝ => 0*u^6 + 0*u^5 + 0*u^4 + 0*u^3 + ((7192*a22 + 1392*a41 + 360*a60))*u^2 + ((7192*a12 + 696*a31 + 120*a50))*u + ((24552*a03 + 496*a22 + 24*a41)*q + (7192*a02 + 232*a21 + 24*a40))) := by
      funext u; ring
    rw [e]
    exact hasDerivAt_poly6 _ _ _ _ _ _ _ s
  have het : (fun s : ℝ => deriv (fun s' : ℝ => (7192*a22 + 1392*a41 + 360*a60)*s'^2 + (7192*a12 + 696*a31 + 120*a50)*s' + (24552*a03 + 496*a22 + 24*a41)*q + (7192*a02 + 232*a21 + 24*a40)) s)
      = (fun s : ℝ => 6*0*s^5 + 5*0*s^4 + 4*0*s^3 + 3*0*s^2 + 2*((7192*a22 + 1392*a41 + 360*a60))*s + ((7192*a12 + 696*a31 + 120*a50))) := funext fun s => (ht s).deriv
  have htt : HasDerivAt (fun s : ℝ => 6*0*s^5 + 5*0*s^4 + 4*0*s^3 + 3*0*s^2 + 2*((7192*a22 + 1392*a41 + 360*a60))*s + ((7192*a12 + 696*a31 + 120*a50)))
      (6*0*t^5 + 5*(6*0)*t^4 + 4*(5*0)*t^3 + 3*(4*0)*t^2 + 2*(3*0)*t + (2*((7192*a22 + 1392*a41 + 360*a60)))) t := by
    have e : (fun s : ℝ => 6*0*s^5 + 5*0*s^4 + 4*0*s^3 + 3*0*s^2 + 2*((7192*a22 + 1392*a41 + 360*a60))*s + ((7192*a12 + 696*a31 + 120*a50)))
        = (fun u : ℝ => 0*u^6 + (6*0)*u^5 + (5*0)*u^4 + (4*0)*u^3 + (3*0)*u^2 + (2*((7192*a22 + 1392*a41 + 360*a60)))*u + ((7192*a12 + 696*a31 + 120*a50))) := by
      funext u; ring
    rw [e]
    have h := hasDerivAt_poly6 0 (6*0) (5*0) (4*0) (3*0) (2*((7192*a22 + 1392*a41 + 360*a60))) ((7192*a12 + 696*a31 + 120*a50)) t
    convert h using 1
    try ring
  have hq : ∀ r : ℝ, HasDerivAt (fun r' : ℝ => (7192*a22 + 1392*a41 + 360*a60)*t^2 + (7192*a12 + 696*a31 + 120*a50)*t + (24552*a03 + 496*a22 + 24*a41)*r' + (7192*a02 + 232*a21 + 24*a40))
      (3*0*r^2 + 2*0*r + ((24552*a03 + 496*a22 + 24*a41))) r := by
    intro r
    have e : (fun r' : ℝ => (7192*a22 + 1392*a41 + 360*a60)*t^2 + (7192*a12 + 696*a31 + 120*a50)*t + (24552*a03 + 496*a22 + 24*a41)*r' + (7192*a02 + 232*a21 + 24*a40))
        = (fun u : ℝ => 0*u^3 + 0*u^2 + ((24552*a03 + 496*a22 + 24*a41))*u + ((7192*a22 + 1392*a41 + 360*a60)*t^2 + (7192*a12 + 696*a31 + 120*a50)*t + (7192*a02 + 232*a21 + 24*a40))) := by
      funext u; ring
    rw [e]
    exact hasDerivAt_poly3 _ _ _ _ r
  have heq : (fun r : ℝ => deriv (fun r' : ℝ => (7192*a22 + 1392*a41 + 360*a60)*t^2 + (7192*a12 + 696*a31 + 120*a50)*t + (24552*a03 + 496*a22 + 24*a41)*r' + (7192*a02 + 232*a21 + 24*a40)) r)
      = (fun r : ℝ => 3*0*r^2 + 2*0*r + ((24552*a03 + 496*a22 + 24*a41))) := funext fun r => (hq r).deriv
  have hqq : HasDerivAt (fun r : ℝ => 3*0*r^2 + 2*0*r + ((24552*a03 + 496*a22 + 24*a41)))
      (3*0*q^2 + 2*(3*0)*q + (2*0)) q := by
    have e : (fun r : ℝ => 3*0*r^2 + 2*0*r + ((24552*a03 + 496*a22 + 24*a41)))
        = (fun u : ℝ => 0*u^3 + (3*0)*u^2 + (2*0)*u + ((24552*a03 + 496*a22 + 24*a41))) := by
      funext u; ring
    rw [e]
    have h := hasDerivAt_poly3 0 (3*0) (2*0) ((24552*a03 + 496*a22 + 24*a41)) q
    convert h using 1
    try ring
  rw [het, heq, htt.deriv, (hq q).deriv, hqq.deriv]
  ring

/-- **Certification of \eqref{eq:laplacian-coefficients}.**  Applying the operator
`Δ = ∂ₜ² + 58 ∂_q + 4q ∂_q²` three times (as genuine real derivative computations) to a
completely general polynomial of weighted degree `≤ 6` and evaluating at the origin
kills every coefficient except the four of weighted degree exactly six, which enter
with the weights displayed in the paper:
`Δ³F(0) = 720·C₆₀ + 4176·C₄₁ + 43152·C₂₂ + 1424016·C₀₃`. -/
theorem Dop_cubed_at_origin (a00 a10 a20 a01 a30 a11 a40 a21 a02 a50 a31 a12 a60 a41 a22 a03 : ℝ) :
    Dop (Dop (Dop (fun t q : ℝ => a60*t^6 + a50*t^5 + a41*t^4*q + a40*t^4 + a31*t^3*q + a30*t^3 + a22*t^2*q^2 + a21*t^2*q + a20*t^2 + a12*t*q^2 + a11*t*q + a10*t + a03*q^3 + a02*q^2 + a01*q + a00))) 0 0
      = 720*a60 + 4176*a41 + 43152*a22 + 1424016*a03 := by
  rw [Dop_stage1, Dop_stage2, Dop_stage3]
  norm_num
  ring

/-! ### The exact sixth-order sign calculation (Lemma 3.1, \eqref{eq:eta-polynomial}) -/

/-- The certified sixth-order weighted Taylor polynomial of `F_r = (A_r/S)^{12/11}` as a
real polynomial function of `(t, q)`; its coefficients are exactly the entries of the
certified table `tblF` (see `taylorF_coeff`). -/
noncomputable def taylorF (η : ℝ) : ℝ → ℝ → ℝ := fun t q =>
  (396980 + 388056*η^2 - 618240*η^4 + 308224*η^6)*t^6
  + (86664*η + 33120*η^3 - 21504*η^5)*t^5
  + (-275460 + 17328*η^2 - 26880*η^4)*t^4*q
  + (16974 - 1104*η^2 + 1680*η^4)*t^4
  + (-41712*η + 2400*η^3)*t^3*q
  + (2760*η - 160*η^3)*t^3
  + (29148 + 2520*η^2)*t^2*q^2
  + (-3876 - 336*η^2)*t^2*q
  + (276 + 24*η^2)*t^2
  + (2184*η)*t*q^2
  + (-312*η)*t*q
  + (24*η)*t
  + (-364)*q^3
  + 78*q^2
  + (-12)*q
  + 1

/-- The coefficients of `taylorF` are precisely the entries of the table `tblF`
certified by the staged truncated-series computation. -/
theorem taylorF_coeff (η t q : ℝ) :
    taylorF η t q =
      tblF η 0 0 + tblF η 1 0 * t + tblF η 2 0 * t^2 + tblF η 0 1 * q
      + tblF η 3 0 * t^3 + tblF η 1 1 * (t*q) + tblF η 4 0 * t^4
      + tblF η 2 1 * (t^2*q) + tblF η 0 2 * q^2 + tblF η 5 0 * t^5
      + tblF η 3 1 * (t^3*q) + tblF η 1 2 * (t*q^2) + tblF η 6 0 * t^6
      + tblF η 4 1 * (t^4*q) + tblF η 2 2 * (t^2*q^2) + tblF η 0 3 * q^3 := by
  simp only [taylorF, tblF]
  norm_num
  try ring

/-- `Δ³ [F_r]₆ (0)` via the generic operator theorem. -/
theorem Dop_cubed_taylorF (η : ℝ) :
    Dop (Dop (Dop (taylorF η))) 0 0
      = 720*(396980 + 388056*η^2 - 618240*η^4 + 308224*η^6)
        + 4176*(-275460 + 17328*η^2 - 26880*η^4)
        + 43152*(29148 + 2520*η^2) + 1424016*(-364) := by
  have h := Dop_cubed_at_origin 1 (24*η) (276 + 24*η^2) (-12) (2760*η - 160*η^3) (-312*η)
      (16974 - 1104*η^2 + 1680*η^4) (-3876 - 336*η^2) 78 (86664*η + 33120*η^3 - 21504*η^5)
      (-41712*η + 2400*η^3) (2184*η) (396980 + 388056*η^2 - 618240*η^4 + 308224*η^6)
      (-275460 + 17328*η^2 - 26880*η^4) (29148 + 2520*η^2) (-364)
  have e : taylorF η = (fun t q : ℝ =>
      (396980 + 388056*η^2 - 618240*η^4 + 308224*η^6)*t^6
      + (86664*η + 33120*η^3 - 21504*η^5)*t^5
      + (-275460 + 17328*η^2 - 26880*η^4)*t^4*q
      + (16974 - 1104*η^2 + 1680*η^4)*t^4
      + (-41712*η + 2400*η^3)*t^3*q
      + (2760*η - 160*η^3)*t^3
      + (29148 + 2520*η^2)*t^2*q^2
      + (-3876 - 336*η^2)*t^2*q
      + (276 + 24*η^2)*t^2
      + (2184*η)*t*q^2
      + (-312*η)*t*q
      + (24*η)*t
      + (-364)*q^3
      + 78*q^2
      + (-12)*q
      + 1) := by
    funext t q
    simp only [taylorF]
  rw [e]
  exact h

/-- **Certification of \eqref{eq:eta-polynomial} (Lemma 3.1)**:
`(-Δ)³ F_r(0) = 125042688 - 460505088 η² + 557383680 η⁴ - 221921280 η⁶`, applied to the
certified sixth-order Taylor polynomial, using `(-Δ)³ = -Δ³`. -/
theorem eta_polynomial (η : ℝ) :
    -(Dop (Dop (Dop (taylorF η))) 0 0)
      = 125042688 - 460505088*η^2 + 557383680*η^4 - 221921280*η^6 := by
  rw [Dop_cubed_taylorF]
  ring

/-- **Certification of \eqref{eq:negative-exact}**: at `r = 10`, i.e. `η = 9/11`,
`(-Δ)³ F₁₀(0) = -43658772480/1771561`. -/
theorem two_pole_value :
    -(Dop (Dop (Dop (taylorF (9/11)))) 0 0) = -43658772480/1771561 := by
  rw [eta_polynomial]
  norm_num

/-- The two-pole quantity is strictly negative: the paper's key sign. -/
theorem two_pole_neg : -(Dop (Dop (Dop (taylorF (9/11)))) 0 0) < 0 := by
  rw [two_pole_value]
  norm_num

/-! ### Remark 3.2: the Vétois–Zeitler palindromic sign polynomial -/

/-- The Vétois–Zeitler coefficients at `(m,n) = (4,30)` and the polynomial
`K(r) = 64r(b₀ + b₁r + b₂r² + b₁r³ + b₀r⁴)` of \eqref{eq:K-polynomial}. -/
noncomputable def VZK (r : ℝ) : ℝ :=
  64*r*(29952 + (-1009152)*r + 7168512*r^2 + (-1009152)*r^3 + 29952*r^4)

/-- **Certification of \eqref{eq:K-identity} at the polynomial level**: multiplying the
`η`-polynomial by `S⁶ = (1+r)⁶` (with `η = (r-1)/(r+1)`, so `ηS = r-1`) gives `24·K(r)`.
Since `(-Δ)³(A_r^{12/11})(0) = S^{12/11}(-Δ)³F_r(0)` and `S^{12/11}·S^{-6·(? )}`… i.e.
`S⁶·[η-polynomial] = 24 K(r)` is the polynomial form of
`(-Δ)³(A_r^{12/11})(0) = 24(1+r)^{-54/11}K(r)`. -/
theorem K_identity_polynomial (r : ℝ) :
    125042688*(1+r)^6 - 460505088*(r-1)^2*(1+r)^4 + 557383680*(r-1)^4*(1+r)^2
      - 221921280*(r-1)^6 = 24 * VZK r := by
  rw [VZK]
  ring

/-- The arithmetic checks of Remark 3.2: the inner palindromic sum at `r = 10` is
`-2842368`, hence `K(10) = -1819115520 < 0`. -/
theorem K_at_ten :
    (29952:ℝ) + (-1009152)*10 + 7168512*10^2 + (-1009152)*10^3 + 29952*10^4 = -2842368 ∧
    VZK 10 = -1819115520 ∧ VZK 10 < 0 := by
  refine ⟨by norm_num, by rw [VZK]; norm_num, by rw [VZK]; norm_num⟩

/-- Cross-check between Lemma 3.1 and Remark 3.2:
`24·K(10) = 11⁶ · (-43658772480/1771561)`, i.e. the two computations of the sign agree
(`11⁶ = 1771561`). -/
theorem K_cross_check :
    (24:ℝ) * VZK 10 = 11^6 * (-43658772480/1771561) ∧ ((11:ℝ)^6 = 1771561) := by
  constructor
  · rw [VZK]; norm_num
  · norm_num

/-! ### The two-pole functions on `ℝ³⁰` (Section 3, \eqref{eq:A-r}, \eqref{eq:F-r}) -/

/-- Euclidean `ℝ³⁰`. -/
abbrev R30 : Type := EuclideanSpace ℝ (Fin 30)

/-- The unit vector `e₁ ∈ ℝ³⁰`. -/
noncomputable def unitPole : R30 := EuclideanSpace.single 0 1

/-- The two-pole Riesz kernel sum `A_r(x) = r|x-e₁|^{-22} + |x+e₁|^{-22}` of
\eqref{eq:A-r}. -/
noncomputable def twoPoleA (r : ℝ) (x : R30) : ℝ :=
  r * ‖x - unitPole‖ ^ (-22 : ℤ) + ‖x + unitPole‖ ^ (-22 : ℤ)

/-- `F_r = (A_r/S)^{12/11}` of \eqref{eq:F-r}, `S = 1 + r`. -/
noncomputable def twoPoleF (r : ℝ) (x : R30) : ℝ :=
  (twoPoleA r x / (1 + r)) ^ ((12:ℝ)/11)

theorem norm_unitPole : ‖unitPole‖ = 1 := by
  rw [unitPole, PiLp.norm_single]
  norm_num

/-- `A_r(0) = r + 1`; in particular `A₁₀(0) = 11` as used in the proof of
Proposition 3.4. -/
theorem twoPoleA_zero (r : ℝ) : twoPoleA r 0 = r + 1 := by
  rw [twoPoleA, zero_sub, norm_neg, zero_add, norm_unitPole]
  norm_num

theorem twoPoleA_ten_zero : twoPoleA 10 0 = 11 := by rw [twoPoleA_zero]; norm_num

theorem twoPoleF_ten_zero : twoPoleF 10 0 = 1 := by
  rw [twoPoleF, twoPoleA_ten_zero]
  norm_num

theorem twoPoleA_nonneg {r : ℝ} (hr : 0 ≤ r) (x : R30) : 0 ≤ twoPoleA r x := by
  rw [twoPoleA]
  have h1 : (0:ℝ) ≤ ‖x - unitPole‖ ^ (-22 : ℤ) := zpow_nonneg (norm_nonneg _) _
  have h2 : (0:ℝ) ≤ ‖x + unitPole‖ ^ (-22 : ℤ) := zpow_nonneg (norm_nonneg _) _
  have := mul_nonneg hr h1
  linarith

/-- The scaling relation `A_r^{12/11} = S^{12/11} F_r` used in the proof of
Proposition 3.4 (`S = 1+r > 0`). -/
theorem twoPoleA_rpow {r : ℝ} (hr : 0 ≤ r) (x : R30) :
    twoPoleA r x ^ ((12:ℝ)/11) = (1 + r) ^ ((12:ℝ)/11) * twoPoleF r x := by
  have hS : (0:ℝ) < 1 + r := by linarith
  rw [twoPoleF, Real.div_rpow (twoPoleA_nonneg hr x) hS.le]
  have hne : (1 + r) ^ ((12:ℝ)/11) ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos hS _)
  field_simp

/-! ### Certificates for the analytic propositions

The remaining content of the paper consists of standard potential-theory facts about
the mollified family `u_ε = κ ∫ |x-y|^{-22} h_ε(y) dy` (existence and smoothness of the
Riesz potential, the comparison Lemma 2.3, and the `C⁶` convergence Lemma 3.3).  These
have no Mathlib counterpart, so the propositions of the paper are certified here in
hypothesis form: each theorem takes the transcribed conclusion of the corresponding
analytic lemma as a hypothesis and gives a complete proof of the remaining
(inequality/limit) reasoning of the paper. -/

/-- **Certificate for Proposition 2.4** (\eqref{eq:q8-bounds}): given the two-sided
comparisons of Lemma 2.3 and the formula \eqref{eq:q8-explicit}
`𝒬₈[u_ε] = 11 h_ε u_ε^{-19/11}` (from Lemma 2.1), the top-order curvature is bounded
between the explicit positive constants `11 C^{-30/11}` and `11 C^{30/11}`. -/
theorem Q8_uniform_bounds {X : Type*} (u h ψ W Q8 : X → ℝ) (Cc : ℝ) (hCc : 1 ≤ Cc)
    (hW : ∀ x, 0 < W x)
    (hψ : ∀ x, ψ x = W x ^ ((19:ℝ)/11))
    (hh_lo : ∀ x, Cc⁻¹ * ψ x ≤ h x) (hh_up : ∀ x, h x ≤ Cc * ψ x)
    (hu_lo : ∀ x, Cc⁻¹ * W x ≤ u x) (hu_up : ∀ x, u x ≤ Cc * W x)
    (hQ8 : ∀ x, Q8 x = 11 * h x * u x ^ (-(19:ℝ)/11)) :
    ∀ x, 11 * Cc ^ (-(30:ℝ)/11) ≤ Q8 x ∧ Q8 x ≤ 11 * Cc ^ ((30:ℝ)/11) := by
  intro x
  have hCc0 : (0:ℝ) < Cc := lt_of_lt_of_le one_pos hCc
  have hWx := hW x
  have hux : 0 < u x := lt_of_lt_of_le (by positivity) (hu_lo x)
  have hp : -(19:ℝ)/11 ≤ 0 := by norm_num
  -- rpow bookkeeping
  have hWp : (0:ℝ) < W x ^ ((19:ℝ)/11) := Real.rpow_pos_of_pos hWx _
  have key : ∀ c : ℝ, 0 < c →
      (c * W x) ^ (-(19:ℝ)/11) = c ^ (-(19:ℝ)/11) * W x ^ (-(19:ℝ)/11) := by
    intro c hc
    exact Real.mul_rpow hc.le hWx.le
  have hWcancel : W x ^ ((19:ℝ)/11) * W x ^ (-(19:ℝ)/11) = 1 := by
    rw [← Real.rpow_add hWx]
    norm_num
  constructor
  · -- lower bound
    have h1 : (Cc * W x) ^ (-(19:ℝ)/11) ≤ u x ^ (-(19:ℝ)/11) :=
      Real.rpow_le_rpow_of_nonpos hux (hu_up x) hp
    have h2 : Cc⁻¹ * ψ x * ((Cc * W x) ^ (-(19:ℝ)/11)) ≤ h x * u x ^ (-(19:ℝ)/11) := by
      have hA : 0 ≤ Cc⁻¹ * ψ x := by
        rw [hψ x]; positivity
      have hB : 0 ≤ (Cc * W x) ^ (-(19:ℝ)/11) := Real.rpow_nonneg (by positivity) _
      exact mul_le_mul (hh_lo x) h1 hB (le_trans hA (hh_lo x))
    have h3 : Cc⁻¹ * ψ x * ((Cc * W x) ^ (-(19:ℝ)/11)) = Cc ^ (-(30:ℝ)/11) := by
      rw [hψ x, key Cc hCc0]
      have hinv : Cc⁻¹ = Cc ^ (-(1:ℝ)) := (Real.rpow_neg_one Cc).symm
      rw [hinv]
      calc Cc ^ (-(1:ℝ)) * W x ^ ((19:ℝ)/11) * (Cc ^ (-(19:ℝ)/11) * W x ^ (-(19:ℝ)/11))
          = (Cc ^ (-(1:ℝ)) * Cc ^ (-(19:ℝ)/11))
            * (W x ^ ((19:ℝ)/11) * W x ^ (-(19:ℝ)/11)) := by ring
        _ = Cc ^ (-(30:ℝ)/11) * 1 := by
            rw [hWcancel, ← Real.rpow_add hCc0]
            norm_num
        _ = Cc ^ (-(30:ℝ)/11) := mul_one _
    rw [hQ8 x, mul_assoc]
    calc 11 * Cc ^ (-(30:ℝ)/11) = 11 * (Cc⁻¹ * ψ x * ((Cc * W x) ^ (-(19:ℝ)/11))) := by
          rw [h3]
      _ ≤ 11 * (h x * u x ^ (-(19:ℝ)/11)) := by linarith
  · -- upper bound
    have h1 : u x ^ (-(19:ℝ)/11) ≤ (Cc⁻¹ * W x) ^ (-(19:ℝ)/11) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hu_lo x) hp
    have h2 : h x * u x ^ (-(19:ℝ)/11) ≤ Cc * ψ x * ((Cc⁻¹ * W x) ^ (-(19:ℝ)/11)) := by
      have hh0 : 0 ≤ h x := le_trans (by rw [hψ x]; positivity) (hh_lo x)
      have hB : 0 ≤ u x ^ (-(19:ℝ)/11) := Real.rpow_nonneg hux.le _
      exact mul_le_mul (hh_up x) h1 hB (by rw [hψ x]; positivity)
    have h3 : Cc * ψ x * ((Cc⁻¹ * W x) ^ (-(19:ℝ)/11)) = Cc ^ ((30:ℝ)/11) := by
      rw [hψ x, key Cc⁻¹ (by positivity)]
      have hCc1 : Cc = Cc ^ (1:ℝ) := (Real.rpow_one Cc).symm
      have hinv : Cc⁻¹ ^ (-(19:ℝ)/11) = Cc ^ ((19:ℝ)/11) := by
        rw [← Real.rpow_neg_one Cc, ← Real.rpow_mul hCc0.le]
        norm_num
      rw [hinv]
      calc Cc * W x ^ ((19:ℝ)/11) * (Cc ^ ((19:ℝ)/11) * W x ^ (-(19:ℝ)/11))
          = (Cc ^ (1:ℝ) * Cc ^ ((19:ℝ)/11))
            * (W x ^ ((19:ℝ)/11) * W x ^ (-(19:ℝ)/11)) := by
            rw [Real.rpow_one]; ring
        _ = Cc ^ ((30:ℝ)/11) * 1 := by
            rw [hWcancel, ← Real.rpow_add hCc0]
            norm_num
        _ = Cc ^ ((30:ℝ)/11) := mul_one _
    rw [hQ8 x, mul_assoc]
    calc 11 * (h x * u x ^ (-(19:ℝ)/11)) ≤ 11 * (Cc * ψ x * ((Cc⁻¹ * W x) ^ (-(19:ℝ)/11))) := by
          linarith
      _ = 11 * Cc ^ ((30:ℝ)/11) := by rw [h3]

/-- **The slow-decay barrier** (\eqref{eq:barrier} with any `s ≤ 0`): a positive
uniform lower bound implies the barrier `c|x|^s ≤ Q` for `|x| ≥ 1`, as in the last
step of the proof of Proposition 2.4. -/
theorem slow_decay_barrier {X : Type*} [NormedAddCommGroup X] (Q8 : X → ℝ) (c : ℝ)
    (hc : 0 < c) (hlow : ∀ x, c ≤ Q8 x) (s : ℝ) (hs : s ≤ 0) :
    ∀ x : X, 1 ≤ ‖x‖ → c * ‖x‖ ^ s ≤ Q8 x := by
  intro x hx
  have h1 : ‖x‖ ^ s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx hs
  have h2 : c * ‖x‖ ^ s ≤ c * 1 := by
    exact mul_le_mul_of_nonneg_left h1 hc.le
  calc c * ‖x‖ ^ s ≤ c * 1 := h2
    _ = c := mul_one c
    _ ≤ Q8 x := hlow x

/-- **The normalization computation in the proof of Proposition 3.4**:
`(11κ)^{-18/11} κ^{12/11} 11^{12/11} · V = (11κ)^{-6/11} · V`. -/
theorem q6_limit_normalization (κ : ℝ) (hκ : 0 < κ) (V : ℝ) :
    (11*κ) ^ (-(18:ℝ)/11) * κ ^ ((12:ℝ)/11) * (11:ℝ) ^ ((12:ℝ)/11) * V
      = (11*κ) ^ (-(6:ℝ)/11) * V := by
  have h11 : (0:ℝ) < 11 := by norm_num
  have e0 : ∀ p : ℝ, (11*κ) ^ p = (11:ℝ) ^ p * κ ^ p := fun p =>
    Real.mul_rpow h11.le hκ.le
  rw [e0, e0]
  have e1 : (11:ℝ) ^ (-(18:ℝ)/11) * (11:ℝ) ^ ((12:ℝ)/11) = (11:ℝ) ^ (-(6:ℝ)/11) := by
    rw [← Real.rpow_add h11]
    norm_num
  have e2 : κ ^ (-(18:ℝ)/11) * κ ^ ((12:ℝ)/11) = κ ^ (-(6:ℝ)/11) := by
    rw [← Real.rpow_add hκ]
    norm_num
  calc (11:ℝ) ^ (-(18:ℝ)/11) * κ ^ (-(18:ℝ)/11) * κ ^ ((12:ℝ)/11) * (11:ℝ) ^ ((12:ℝ)/11) * V
      = ((11:ℝ) ^ (-(18:ℝ)/11) * (11:ℝ) ^ ((12:ℝ)/11))
        * (κ ^ (-(18:ℝ)/11) * κ ^ ((12:ℝ)/11)) * V := by ring
    _ = (11:ℝ) ^ (-(6:ℝ)/11) * κ ^ (-(6:ℝ)/11) * V := by rw [e1, e2]

/-- **The limit value \eqref{eq:q6-limit} is negative**:
`-(43658772480/1771561) · (11κ)^{-6/11} < 0`. -/
theorem q6_limit_value_neg :
    (-(43658772480:ℝ)/1771561) * (11 * kappaConst) ^ (-(6:ℝ)/11) < 0 := by
  have hκ : (0:ℝ) < 11 * kappaConst := by
    have := kappaConst_pos
    linarith
  have h1 : (0:ℝ) < (11 * kappaConst) ^ (-(6:ℝ)/11) := Real.rpow_pos_of_pos hκ _
  have h2 : (-(43658772480:ℝ)/1771561) < 0 := by norm_num
  exact mul_neg_of_neg_of_pos h2 h1

/-- **Certificate for Proposition 3.4** (\eqref{eq:q6-epsilon-negative}): if
`𝒬₆[u_ε](0)` converges as `ε ↓ 0` to a negative limit (Lemma 3.3 + Lemma 3.1 give the
limit `-(43658772480/1771561)(11κ)^{-6/11}`), then `𝒬₆[u_ε](0) < 0` for all
sufficiently small `ε > 0`. -/
theorem q6_eventually_negative (Q6 : ℝ → ℝ) (L : ℝ) (hL : L < 0)
    (hconv : Filter.Tendsto Q6 (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), Q6 ε < 0 :=
  hconv.eventually_lt_const hL

/-- The negation of the conjecture's conclusion: a negative intermediate curvature
value refutes `𝒬₆[u] > 0` (and a fortiori `𝒬₆[u] ≥ 0`). -/
theorem conjecture_conclusion_fails (Q6val : ℝ) (h : Q6val < 0) : ¬ (0 ≤ Q6val) :=
  not_le.mpr h

/-- **Certificate for Theorem 1.1.**  Hypotheses: the transcribed conclusions of the
analytic Lemmas 2.1–2.3 (positivity, the comparison estimates, and the formula
`𝒬₈[u_ε] = 11 h_ε u_ε^{-19/11}`) for every `ε ∈ (0, 1/4)`, and the convergence of
`𝒬₆[u_ε](0)` to the limit value of \eqref{eq:q6-limit} (Lemma 3.3 with Lemma 3.1).
Conclusion: for all sufficiently small `ε > 0`, the top-order curvature `𝒬₈[u_ε]` is
bounded between two positive constants (hence satisfies the slow-decay barrier
\eqref{eq:barrier} with `s = 0`), while `𝒬₆[u_ε](0) < 0`: Li–Xu's Conjecture 1 fails. -/
theorem theorem_main_certificate {X : Type*}
    (u h ψ W Q8 : ℝ → X → ℝ) (Q6₀ : ℝ → ℝ) (Cc : ℝ → ℝ)
    (hCc : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), 1 ≤ Cc ε)
    (hW : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), ∀ x, 0 < W ε x)
    (hψ : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), ∀ x, ψ ε x = W ε x ^ ((19:ℝ)/11))
    (hh_lo : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), ∀ x, (Cc ε)⁻¹ * ψ ε x ≤ h ε x)
    (hh_up : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), ∀ x, h ε x ≤ Cc ε * ψ ε x)
    (hu_lo : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), ∀ x, (Cc ε)⁻¹ * W ε x ≤ u ε x)
    (hu_up : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), ∀ x, u ε x ≤ Cc ε * W ε x)
    (hQ8 : ∀ ε ∈ Set.Ioo (0:ℝ) (1/4), ∀ x, Q8 ε x = 11 * h ε x * u ε x ^ (-(19:ℝ)/11))
    (hQ6conv : Filter.Tendsto Q6₀ (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((-(43658772480:ℝ)/1771561) * (11 * kappaConst) ^ (-(6:ℝ)/11)))) :
    ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c ≤ Q8 ε x ∧ Q8 ε x ≤ C) ∧ Q6₀ ε < 0 := by
  have hmem : Set.Ioo (0:ℝ) (1/4) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
    apply mem_nhdsWithin.mpr
    exact ⟨Set.Iio (1/4), isOpen_Iio, by norm_num, by
      intro y hy
      exact ⟨hy.2, hy.1⟩⟩
  have hneg : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), Q6₀ ε < 0 :=
    q6_eventually_negative Q6₀ _ q6_limit_value_neg hQ6conv
  filter_upwards [hmem, hneg] with ε hε hQ6ε
  refine ⟨⟨11 * (Cc ε) ^ (-(30:ℝ)/11), 11 * (Cc ε) ^ ((30:ℝ)/11), ?_, ?_, ?_⟩, hQ6ε⟩
  · have hC0 : (0:ℝ) < Cc ε := lt_of_lt_of_le one_pos (hCc ε hε)
    positivity
  · have hC0 : (0:ℝ) < Cc ε := lt_of_lt_of_le one_pos (hCc ε hε)
    positivity
  · exact Q8_uniform_bounds (u ε) (h ε) (ψ ε) (W ε) (Q8 ε) (Cc ε) (hCc ε hε)
      (hW ε hε) (hψ ε hε) (hh_lo ε hε) (hh_up ε hε) (hu_lo ε hε) (hu_up ε hε) (hQ8 ε hε)
