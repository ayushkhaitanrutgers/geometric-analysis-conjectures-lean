import Mathlib

/-!
# Generic integer-order umbilics of analytic W-congruences

Lean certification of `integer_w_congruence_genericity.tex`.

The paper proves: within the fixed-`m` stratum `𝒮_m` of real-analytic nondegenerate
`W`-congruence germs (normalized umbilic parameter `m ∈ ℤ, m ≥ 1`), the discriminant
generically has unsigned real type `A_m`; the exceptional locus `κ = 0` is a smooth
hypersurface. The proof route is: hodograph reduction (`W = 2JE`, `(X-2)Δ = AE`,
`δ = 4Δ`, hence `XΔ = 2Δ`), analytic linearization of `X` (Poincaré–Dulac plus
vanishing of the sole resonance), weight classification `Δ = c₂v² + c₁u^{(m+1)/2}v +
c₀u^{m+1}`, completion of the square, and an explicit analytic deformation
`F_t = F + tH`, `H = e^φ u^m`, which moves `κ` with nonzero speed.

What is formalized where (tex tags in parentheses):

* `Wexpr`, `deltaExpr`, `discFun` — the extended Weingarten operator (eq:W) and
  discriminant (eq:delta) as expressions/functions.
* `deltaExpr_hodograph` — `δ = 4Δ` under the hodograph substitution
  `P_x = B+G, P_y = A, Q_x = -F, Q_y = G-B` (Lemma 1, eq:identities).
* `W_eq_two_J_E` — the identity `W = 2JE` (Lemma 1, eq:identities): a complete
  polynomial verification, with the chain-rule values of the ten derivatives of
  `(P,Q)` through the hodograph map substituted, and the two Schwarz mixed-partial
  compatibility constraints as hypotheses.
* `E_zero_of_W_zero` — `J ≠ 0` and `W = 0` force `E = 0` (Lemma 1 proof).
* `pd1`/`pd2`/`Xop`/`Eexpr`/`Dfun` and `Eexpr_eq`, `X_sub_two_Dfun`,
  `eigen_of_E_zero` — the vector field `X` (eq:X), the function `E` (eq:E),
  `Δ = B² - AF` (eq:Delta); real-calculus proofs of `E = (1-G_B)F - XF - 2BG_A`,
  of `(X-2)Δ = AE` (eq:identities), and of the eigen-equation `XΔ = 2Δ`
  (eq:eigen) for `W`-congruence germs.
* `Afun_model`, `Bfun_model`, `jacobian_model_ne_zero`, `Gfun_model`,
  `GB_zero_value`, `lambda_zero_value`, `CK_determinant` — the normalized-two-jet
  computations: `A = ax + O(2)`, `B = ((m+1)/2)a y + O(2)` (display after eq:AB),
  `J(0) = ((m+1)/2)a² ≠ 0` (Lemma 1 proof), `G_B(0) = (1-m)/(m+1)`, hence
  `λ(0) = 1 - G_B(0) = 2m/(m+1) = mα` (eq:lambda) and the Cauchy–Kowalevski
  determinant `(1+G_B(0))(1-G_B(0)) = 4m/(m+1)² > 0` (eq:det). These are exact
  computations on the normalized quadratic model jet
  `P = axy, Q = (q₂₀/2)x² + (q₀₂/2)y²` (eq:normal, eq:m); higher-order terms of the
  germ do not enter any of these origin values.
* `Eexpr_linear_model`, `linear_part_of_F_vanishes`, `Delta_two_jet` — the
  linear-order coefficient extraction of `E = 0`: for `m ≠ 1` the linear part of
  `F` vanishes, so `Δ = B² + O(3)` (eq:linear; also the `m = 1` caveat after
  Lemma 1, where `G_B(0) = 0` and the argument fails).
* `X0op_monomial`, `bracket_A_component`, `bracket_B_component` — the homological
  eigenvalue computations `[X₀, A^iB^j∂_A] = (α(i-1)+j)A^iB^j∂_A` and
  `[X₀, A^iB^j∂_B] = (αi+j-1)A^iB^j∂_B` (Proposition 2 proof), via genuine
  one-variable calculus.
* `no_A_resonance`, `B_resonance_iff` — the resonance arithmetic (Proposition 2
  proof): no `∂_A`-resonance ever; a `∂_B`-resonance only for odd `m ≥ 3`, at the
  single monomial `A^r∂_B`, `r = (m+1)/2`.
* `euler`, `euler_coe` — the Euler operator `u_i ∂_{u_i}` on 2-variable formal
  power series, defined coefficientwise and *proved* to agree with
  `X i * pderiv i` on polynomials (the local Mathlib lacks `MvPowerSeries.pderiv`).
* `resonant_coefficient_vanishes` — the killing step (eq:kill): if
  `(X₀-2)Δ' + 2cA^rB = 0` with `2r = m+1` then `c = 0`, because `A^rB` lies in the
  kernel of the scalar homological operator `X₀ - 2`. This is the heart of
  Proposition 2.
* `weight_two_solutions`, `eigen_support`, `eigen_series_eq` — Proposition 3:
  a formal power series satisfying `XΔ = 2Δ` (in linearized coordinates, scaled by
  `m+1`) is supported on the weight-two monomials `u^{m+1}, u^{(m+1)/2}v, v²`
  (eq:weight and the display following it) — in particular the entire germ is a
  polynomial with at most three terms.
* `complete_square`, `kappa_t_formula` — completing the square (Proposition 3,
  eq:split) and the deformation bookkeeping `κ_t = κ - tC` (eq:kappat).
* `UnsignedAm`, `unsignedAm_iff` — the unsigned real `A_m` normal form
  `ε₂v² + ε₁u^{m+1}` (Introduction): `c₂v² + κu^{m+1}` with `c₂ ≠ 0` is linearly
  right-equivalent to it exactly when `κ ≠ 0` (Proposition 3, "type `A_m` iff
  `κ ≠ 0`"); the scaling diffeomorphism is exhibited via real powers.
* `cohomological_solvable` — unique formal solvability of the cohomological
  equation `Xφ = λ - λ(0)` (eq:cohomology): every nonconstant monomial is divided
  by its strictly positive weight `αi + j`.  (Convergence is the standard
  Poincaré-domain estimate, not in Mathlib.)
* `X0op_exp_mul_pow`, `XH_eq_lambda_H` — `H = e^φ u^m` satisfies
  `XH = (1-G_B)H` (eq:H, eq:Hhomogeneous), by real calculus.
* `Eexpr_deform`, `Eexpr_deform_zero`, `Dfun_deform` — the deformation
  `F_t = F + tH, G_t = G` (eq:deform) satisfies `E(F_t,G_t) = 0` and
  `Δ_t = Δ - tAH`.
* `Xop_mul_fst`, `X_AH_eq_two_AH` — `X(AH) = 2AH` (display before eq:kappat), by
  the derivation property of `X`.
* `eigen_series_order` — among the weight-two monomials only `u^{m+1}` has
  ordinary order `m+1`, so an eigen-series of order `≥ m+1` equals `Cu^{m+1}`
  (eq:kappat).
* `m_one_discriminant`, `m_one_A1_iff` — the `m = 1` branch (eq:m1):
  `δ₂ = 4a(ay² + q₂₀x²)` on the normalized 2-jet, and unsigned `A₁` ⟺ `q₂₀ ≠ 0`.
* `transverse_line_dense_open` — the general topological genericity mechanism of
  §5: a continuous scalar `κ` moved with nonzero speed along continuous curves
  through every point has `{κ ≠ 0}` open and dense.
* `StratumData`, `generic_unsigned_Am`, `exceptional_locus_line` — Theorem 1
  (thm:main). The analytic package that Mathlib cannot express (the analytic
  coefficient topology on `𝒮_m`, convergence of the Poincaré–Dulac normalization,
  the Cauchy–Kowalevski production of `P_t, Q_t` from `F_t, G_t` (eq:CK1–eq:CK2),
  and the analytic dependence of `κ` on the germ) is a hypothesis structure whose
  every field is annotated with the tex statement it encodes; `trivialModel` shows
  the package is consistent (not vacuous).

Not formalizable in current Mathlib (hence hypotheses/comments only): the analytic
coefficient topology on germ spaces, convergent Poincaré–Dulac normalization
(Arnold), the Cauchy–Kowalevski theorem, and the transport of `X, Δ, H` through
the linearizing coordinate change.
-/

open Real MvPowerSeries

namespace IntegerWCongruenceGenericity

noncomputable section

/-! ## §1 The Weingarten operator and the discriminant

`Wexpr` is the extended Weingarten expression (eq:W) evaluated on the ten
derivative values `P_x, P_y, Q_x, Q_y, P_{xx}, P_{xy}, P_{yy}, Q_{xx}, Q_{xy},
Q_{yy}` of a line congruence `f = (x,y,0)`, `ξ = (P,Q,1)`; `deltaExpr` is the
discriminant (eq:delta) on the four first-derivative values. -/

/-- The extended Weingarten expression `W(P,Q)` (eq:W), as a polynomial in the
derivative values of `P` and `Q`. -/
def Wexpr (px py qx qy pxx pxy pyy qxx qxy qyy : ℝ) : ℝ :=
  (qy - px) * (qxx * pyy - pxx * qyy) - 2 * py * (pxx * qxy - qxx * pxy)
    + 2 * qx * (pxy * qyy - pyy * qxy)

/-- The discriminant `δ = (P_x - Q_y)² + 4P_yQ_x` (eq:delta), as a polynomial in
the first-derivative values. -/
def deltaExpr (px py qx qy : ℝ) : ℝ := (px - qy) ^ 2 + 4 * py * qx

/-! ## §2 Hodograph reduction

The hodograph coordinates are `A = P_y`, `B = (P_x - Q_y)/2` (eq:AB), and `F, G`
are defined by `-Q_x = F(A,B)`, `(P_x + Q_y)/2 = G(A,B)` (eq:FG), so that
`P_x = B + G, P_y = A, Q_x = -F, Q_y = G - B`.

We use honest one-variable partial derivatives `pd1, pd2` on `ℝ × ℝ → ℝ` to
define the vector field `X` (eq:X), the function `E` (eq:E) and `Δ = B² - AF`
(eq:Delta), and prove the identities of Lemma 1 by real calculus. -/

/-- Partial derivative in the first variable. -/
def pd1 (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun a => f (a, p.2)) p.1

/-- Partial derivative in the second variable. -/
def pd2 (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun b => f (p.1, b)) p.2

/-- The hodograph vector field `X = A(1+G_B)∂_A + (B - AG_A)∂_B` (eq:X), applied
to a function `f` of `(A,B)`. -/
def Xop (G f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (1 + pd2 G p) * pd1 f p + (p.2 - p.1 * pd1 G p) * pd2 f p

/-- The reduced Weingarten function
`E = (1-G_B)F - (1+G_B)AF_A + (AG_A - B)F_B - 2BG_A` (eq:E). -/
def Eexpr (F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - pd2 G p) * F p - (1 + pd2 G p) * p.1 * pd1 F p
    + (p.1 * pd1 G p - p.2) * pd2 F p - 2 * p.2 * pd1 G p

/-- The hodograph discriminant `Δ = B² - AF` (eq:Delta). -/
def Dfun (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := p.2 ^ 2 - p.1 * F p

/-- **Lemma 1 (eq:identities), third identity: `δ = 4Δ`.**  Substituting the
hodograph relations `P_x = B+G, P_y = A, Q_x = -F, Q_y = G-B` (the display after
eq:FG) into the discriminant (eq:delta). -/
theorem deltaExpr_hodograph (A B F G : ℝ) :
    deltaExpr (B + G) A (-F) (G - B) = 4 * (B ^ 2 - A * F) := by
  unfold deltaExpr; ring

/-- **Lemma 1 (eq:identities), first identity: `W = 2JE`.**
Here `a1 = A_x, a2 = A_y, b1 = B_x, b2 = B_y` are the first derivatives of the
hodograph coordinate functions, `J = a1·b2 - a2·b1` is the hodograph Jacobian,
and the ten arguments of `Wexpr` are the chain-rule values of the derivatives of
`(P,Q)` obtained from `P_x = B+G(A,B), P_y = A, Q_x = -F(A,B), Q_y = G(A,B)-B`.
The two hypotheses are the Schwarz mixed-partial compatibilities
`P_{xy} = ∂_x P_y = ∂_y P_x` and `Q_{xy} = ∂_y Q_x = ∂_x Q_y`, which hold for any
`C²` pair `(P,Q)`.  The proof is a complete polynomial verification. -/
theorem W_eq_two_J_E (A B F G FA FB GA GB a1 a2 b1 b2 : ℝ)
    (hP : a1 = (1 + GB) * b2 + GA * a2)
    (hQ : GA * a1 + (GB - 1) * b1 = -(FA * a2 + FB * b2)) :
    Wexpr (B + G) A (-F) (G - B)
      ((1 + GB) * b1 + GA * a1) a1 a2
      (-(FA * a1 + FB * b1)) (-(FA * a2 + FB * b2)) (GA * a2 + (GB - 1) * b2)
    = 2 * (a1 * b2 - a2 * b1)
        * ((1 - GB) * F - (1 + GB) * A * FA + (A * GA - B) * FB - 2 * B * GA) := by
  unfold Wexpr
  linear_combination
    (-2 * (A * FA * a1 + A * FB * b1 + B * GA * a1 + B * GB * b1 - B * b1)) * hP
    + (2 * (B * a1 - F * a2)) * hQ

/-- **Lemma 1, proof**: since `J(0) ≠ 0`, `W = 0` implies `E = 0`. -/
theorem E_zero_of_W_zero (J E : ℝ) (hJ : J ≠ 0) (hW : 2 * J * E = 0) : E = 0 := by
  rcases mul_eq_zero.mp hW with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · norm_num at h'
    · exact absurd h' hJ
  · exact h

/-- `E = (1-G_B)F - XF - 2BG_A` (the display for `E(F,G)` in §4). -/
theorem Eexpr_eq (F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    Eexpr F G p = (1 - pd2 G p) * F p - Xop G F p - 2 * p.2 * pd1 G p := by
  unfold Eexpr Xop; ring

/-- `∂_A Δ = -F - A F_A` (used for `(X-2)Δ = AE`). -/
theorem pd1_Dfun (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ (fun a => F (a, p.2)) p.1) :
    pd1 (Dfun F) p = -F p - p.1 * pd1 F p := by
  have h : HasDerivAt (fun a : ℝ => p.2 ^ 2 - a * F (a, p.2))
      (0 - (1 * F (p.1, p.2) + p.1 * deriv (fun a => F (a, p.2)) p.1)) p.1 :=
    (hasDerivAt_const _ _).sub ((hasDerivAt_id _).mul hF.hasDerivAt)
  have h2 := h.deriv
  simp only [pd1, Dfun]
  rw [h2]
  ring

/-- `∂_B Δ = 2B - A F_B` (used for `(X-2)Δ = AE`). -/
theorem pd2_Dfun (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ (fun b => F (p.1, b)) p.2) :
    pd2 (Dfun F) p = 2 * p.2 - p.1 * pd2 F p := by
  have h : HasDerivAt (fun b : ℝ => b ^ 2 - p.1 * F (p.1, b))
      ((2 : ℕ) * p.2 ^ 1 - p.1 * deriv (fun b => F (p.1, b)) p.2) p.2 :=
    (hasDerivAt_pow 2 p.2).sub (hF.hasDerivAt.const_mul p.1)
  have h2 := h.deriv
  simp only [pd2, Dfun]
  rw [h2]
  push_cast
  ring

/-- **Lemma 1 (eq:identities), second identity: `(X - 2)Δ = AE`.**  A direct
application of eq:X to `B² - AF`, by real calculus. -/
theorem X_sub_two_Dfun (F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF1 : DifferentiableAt ℝ (fun a => F (a, p.2)) p.1)
    (hF2 : DifferentiableAt ℝ (fun b => F (p.1, b)) p.2) :
    Xop G (Dfun F) p - 2 * Dfun F p = p.1 * Eexpr F G p := by
  unfold Xop
  rw [pd1_Dfun F p hF1, pd2_Dfun F p hF2]
  unfold Eexpr Dfun
  ring

/-- **Lemma 1 (eq:eigen): for a `W`-congruence germ, `XΔ = 2Δ`.**  Combines the
previous identity with `E = 0` (which follows from `W = 0` and `J(0) ≠ 0` via
`W_eq_two_J_E` and `E_zero_of_W_zero`). -/
theorem eigen_of_E_zero (F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF1 : DifferentiableAt ℝ (fun a => F (a, p.2)) p.1)
    (hF2 : DifferentiableAt ℝ (fun b => F (p.1, b)) p.2)
    (hE : Eexpr F G p = 0) :
    Xop G (Dfun F) p = 2 * Dfun F p := by
  have h := X_sub_two_Dfun F G p hF1 hF2
  rw [hE, mul_zero] at h
  linarith

/-! ### The normalized two-jet (eq:normal, eq:m, eq:linear)

At a normalized nondegenerate umbilic, `p₂₀ = p₀₂ = q₁₁ = 0`, `p₁₁ = a ≠ 0`,
`q₀₂ = -ma` (eq:normal, eq:m), and the germ has no linear part.  All origin
values below (`A_x(0), B_y(0), J(0), G_B(0), λ(0)`, the CK determinant) depend
only on the quadratic jet, so we compute them exactly on the normalized
quadratic model `P = axy`, `Q = (q₂₀/2)x² + (q₀₂/2)y²`. -/

/-- The normalized quadratic model jet of `P` (eq:normal): `p₁₁ = a`, all other
second derivatives zero. -/
def Pmod (a : ℝ) : ℝ × ℝ → ℝ := fun q => a * q.1 * q.2

/-- The normalized quadratic model jet of `Q` (eq:normal): `q₁₁ = 0`, free
`q₂₀, q₀₂`. -/
def Qmod (q20 q02 : ℝ) : ℝ × ℝ → ℝ := fun q => q20 / 2 * q.1 ^ 2 + q02 / 2 * q.2 ^ 2

theorem pd1_Pmod (a : ℝ) (p : ℝ × ℝ) : pd1 (Pmod a) p = a * p.2 := by
  have h : (fun x : ℝ => Pmod a (x, p.2)) = fun x => a * p.2 * x := by
    funext x; unfold Pmod; ring
  rw [pd1, h, deriv_const_mul_field, deriv_id'', mul_one]

theorem pd2_Pmod (a : ℝ) (p : ℝ × ℝ) : pd2 (Pmod a) p = a * p.1 := by
  have h : (fun y : ℝ => Pmod a (p.1, y)) = fun y => a * p.1 * y := by
    funext y; unfold Pmod; ring
  rw [pd2, h, deriv_const_mul_field, deriv_id'', mul_one]

theorem pd1_Qmod (q20 q02 : ℝ) (p : ℝ × ℝ) : pd1 (Qmod q20 q02) p = q20 * p.1 := by
  have h : HasDerivAt (fun x : ℝ => q20 / 2 * x ^ 2 + q02 / 2 * p.2 ^ 2)
      (q20 / 2 * ((2 : ℕ) * p.1 ^ 1) + 0) p.1 :=
    (((hasDerivAt_pow 2 p.1)).const_mul (q20 / 2)).add (hasDerivAt_const _ _)
  have h2 := h.deriv
  unfold pd1 Qmod
  rw [h2]
  push_cast
  ring

theorem pd2_Qmod (q20 q02 : ℝ) (p : ℝ × ℝ) : pd2 (Qmod q20 q02) p = q02 * p.2 := by
  have h : HasDerivAt (fun y : ℝ => q20 / 2 * p.1 ^ 2 + q02 / 2 * y ^ 2)
      (0 + q02 / 2 * ((2 : ℕ) * p.2 ^ 1)) p.2 :=
    (hasDerivAt_const _ _).add ((hasDerivAt_pow 2 p.2).const_mul (q02 / 2))
  have h2 := h.deriv
  unfold pd2 Qmod
  rw [h2]
  push_cast
  ring

/-- The hodograph coordinate `A = P_y` (eq:AB). -/
def Afun (P : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => pd2 P p

/-- The hodograph coordinate `B = (P_x - Q_y)/2` (eq:AB). -/
def Bfun (P Q : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => (pd1 P p - pd2 Q p) / 2

/-- The function `G = (P_x + Q_y)/2` (eq:FG). -/
def Gfun (P Q : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => (pd1 P p + pd2 Q p) / 2

/-- On the normalized model: `A = ax` exactly (display after eq:AB:
`A = ax + O(2)`). -/
theorem Afun_model (a : ℝ) : Afun (Pmod a) = fun p => a * p.1 := by
  funext p; rw [Afun, pd2_Pmod]

/-- On the normalized model with `q₀₂ = -ma`: `B = ((m+1)/2)a·y` exactly
(display after eq:AB: `B = ((m+1)/2)ay + O(2)`). -/
theorem Bfun_model (m : ℕ) (a q20 : ℝ) :
    Bfun (Pmod a) (Qmod q20 (-(m * a))) = fun p => (m + 1) * a / 2 * p.2 := by
  funext p
  rw [Bfun, pd1_Pmod, pd2_Qmod]
  ring

/-- **Lemma 1 proof: `J(0) = ((m+1)/2)a² ≠ 0`**, so `(A,B)` are analytic local
coordinates.  The Jacobian `A_x B_y - A_y B_x` of the model at any point. -/
theorem jacobian_model_ne_zero (m : ℕ) (a q20 : ℝ) (ha : a ≠ 0) (p : ℝ × ℝ) :
    pd1 (Afun (Pmod a)) p * pd2 (Bfun (Pmod a) (Qmod q20 (-(m * a)))) p
      - pd2 (Afun (Pmod a)) p * pd1 (Bfun (Pmod a) (Qmod q20 (-(m * a)))) p ≠ 0 := by
  rw [Afun_model a, Bfun_model m a q20]
  have h1 : pd1 (fun p : ℝ × ℝ => a * p.1) p = a := by
    rw [pd1, deriv_const_mul_field, deriv_id'', mul_one]
  have h2 : pd2 (fun p : ℝ × ℝ => a * p.1) p = 0 := by
    simp [pd2]
  have h3 : pd1 (fun p : ℝ × ℝ => (m + 1) * a / 2 * p.2) p = 0 := by
    simp [pd1]
  have h4 : pd2 (fun p : ℝ × ℝ => (m + 1) * a / 2 * p.2) p = (m + 1) * a / 2 := by
    rw [pd2, deriv_const_mul_field, deriv_id'', mul_one]
  rw [h1, h2, h3, h4]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hre : a * (((m : ℝ) + 1) * a / 2) - 0 * 0 = ((m : ℝ) + 1) * a ^ 2 / 2 := by ring
  rw [hre]
  exact div_ne_zero (mul_ne_zero hm1 ha2) two_ne_zero

/-- On the normalized model with `q₀₂ = -ma`: `G = ((1-m)/(m+1))·B` exactly, so
`G_A(0) = 0` and `G_B(0) = (1-m)/(m+1)` — the value entering eq:lambda and
eq:det. -/
theorem Gfun_model (m : ℕ) (a q20 : ℝ) (p : ℝ × ℝ) :
    Gfun (Pmod a) (Qmod q20 (-(m * a))) p
      = (1 - m) / (m + 1) * Bfun (Pmod a) (Qmod q20 (-(m * a))) p := by
  rw [Gfun, Bfun, pd1_Pmod, pd2_Qmod]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `G_B(0) = (1-m)/(m+1)`, packaged as the value used below. -/
def GB0 (m : ℕ) : ℝ := (1 - (m : ℝ)) / ((m : ℝ) + 1)

/-- **eq:lambda**: `λ(0) = 1 - G_B(0) = 2m/(m+1) = mα` with `α = 2/(m+1)`. -/
theorem lambda_zero_value (m : ℕ) :
    1 - GB0 m = 2 * m / (m + 1) ∧ 1 - GB0 m = m * (2 / (m + 1)) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  unfold GB0
  constructor <;> field_simp <;> ring

/-- **eq:det**: the Cauchy–Kowalevski determinant
`(1+G_B(0))(1-G_B(0)) = 4m/(m+1)²`, strictly positive for `m ≥ 1`.  (The CK
theorem itself, producing analytic `x_t, y_t` and hence `P_t, Q_t` from
eq:CK1–eq:CK2, is not available in Mathlib; this is the paper's noncharacteristic
determinant computation.) -/
theorem CK_determinant (m : ℕ) (hm : 1 ≤ m) :
    (1 + GB0 m) * (1 - GB0 m) = 4 * m / (m + 1) ^ 2
      ∧ 0 < (1 + GB0 m) * (1 - GB0 m) := by
  have hm0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : (1 + GB0 m) * (1 - GB0 m) = 4 * m / (m + 1) ^ 2 := by
    unfold GB0; field_simp; ring
  refine ⟨heq, ?_⟩
  rw [heq]
  positivity

/-! ### The linear-order coefficient extraction of `E = 0` (eq:linear)

The linear part of `E` sees only the linear parts of `F` and `G` (quadratic
remainders contribute `O(2)` to `E`).  On the exact linear model
`F = f₁₀A + f₀₁B`, `G = gB` (with `g = G_B(0) = (1-m)/(m+1)` and `G_A(0) = 0`
from `Gfun_model`), `E` is computed exactly; `E = 0` then forces the linear part
of `F` to vanish whenever `g ≠ 0`, i.e. whenever `m ≠ 1` — this is why
`Δ = B² + O(3)` (eq:linear) and why the case `m = 1` ("`F` may have a linear
`A`-term", end of §2) is treated separately. -/

/-- `E` on the linear model: `E = -2g·f₁₀·A - g·f₀₁·B` exactly. -/
theorem Eexpr_linear_model (f10 f01 g : ℝ) (p : ℝ × ℝ) :
    Eexpr (fun q => f10 * q.1 + f01 * q.2) (fun q => g * q.2) p
      = -2 * g * f10 * p.1 - g * f01 * p.2 := by
  have hF1 : pd1 (fun q : ℝ × ℝ => f10 * q.1 + f01 * q.2) p = f10 := by
    have h : HasDerivAt (fun x : ℝ => f10 * x + f01 * p.2) (f10 * 1 + 0) p.1 :=
      ((hasDerivAt_id p.1).const_mul f10).add (hasDerivAt_const _ _)
    have h2 := h.deriv
    rw [pd1]; rw [h2]; ring
  have hF2 : pd2 (fun q : ℝ × ℝ => f10 * q.1 + f01 * q.2) p = f01 := by
    have h : HasDerivAt (fun y : ℝ => f10 * p.1 + f01 * y) (0 + f01 * 1) p.2 :=
      (hasDerivAt_const _ _).add ((hasDerivAt_id p.2).const_mul f01)
    have h2 := h.deriv
    rw [pd2]; rw [h2]; ring
  have hG1 : pd1 (fun q : ℝ × ℝ => g * q.2) p = 0 := by
    simp [pd1]
  have hG2 : pd2 (fun q : ℝ × ℝ => g * q.2) p = g := by
    rw [pd2, deriv_const_mul_field, deriv_id'', mul_one]
  rw [Eexpr, hF1, hF2, hG1, hG2]
  ring

/-- **eq:linear**: for `m ≠ 1` (`g = G_B(0) ≠ 0`), `E = 0` kills the linear part
of `F`; hence `Δ = B² - AF = B² + O(3)`. -/
theorem linear_part_of_F_vanishes (f10 f01 g : ℝ) (hg : g ≠ 0)
    (hE : ∀ p : ℝ × ℝ,
      Eexpr (fun q => f10 * q.1 + f01 * q.2) (fun q => g * q.2) p = 0) :
    f10 = 0 ∧ f01 = 0 := by
  have h1 := hE (1, 0)
  have h2 := hE (0, 1)
  rw [Eexpr_linear_model] at h1 h2
  norm_num at h1 h2
  constructor
  · rcases h1 with h | h
    · exact absurd h hg
    · exact h
  · rcases h2 with h | h
    · exact absurd h hg
    · exact h

/-- With the linear part of `F` gone, the two-jet of `Δ` is exactly `B²`
(eq:linear: `Δ = B² + O(3)`). -/
theorem Delta_two_jet (p : ℝ × ℝ) : Dfun (fun _ => 0) p = p.2 ^ 2 := by
  simp [Dfun]

/-! ## §3 Analytic normal form: resonances

The linearized field is `X₀ = αA∂_A + B∂_B`, `α = 2/(m+1)` (eq:linear).  We
first certify the homological eigenvalue computations of Proposition 2's proof
by real calculus, then the resonance arithmetic.  Throughout, the rational
weight relation `αi + j = w` is cleared of denominators as
`2i + (m+1)j = (m+1)w`. -/

/-- The linear model field `X₀ = αu∂_u + v∂_v` applied to a function. -/
def X0op (α : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  α * p.1 * pd1 f p + p.2 * pd2 f p

/-- `X₀(u^i v^j) = (αi + j)·u^i v^j`: the scalar eigenvalue computation behind
the commutator display in Proposition 2's proof and behind eq:weight. -/
theorem X0op_monomial (α : ℝ) (i j : ℕ) (p : ℝ × ℝ) :
    X0op α (fun q => q.1 ^ i * q.2 ^ j) p = (α * i + j) * (p.1 ^ i * p.2 ^ j) := by
  have hd1 : HasDerivAt (fun a : ℝ => a ^ i * p.2 ^ j) ((i * p.1 ^ (i - 1)) * p.2 ^ j) p.1 :=
    (hasDerivAt_pow i p.1).mul_const _
  have hd2 : HasDerivAt (fun b : ℝ => p.1 ^ i * b ^ j) (p.1 ^ i * (j * p.2 ^ (j - 1))) p.2 :=
    (hasDerivAt_pow j p.2).const_mul _
  simp only [X0op, pd1, pd2]
  rw [hd1.deriv, hd2.deriv]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hi; subst hj; simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      subst hi; push_cast; simp only [pow_zero]; ring
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; push_cast; simp only [pow_zero]; ring
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      push_cast; ring

/-- **Proposition 2 proof, first commutator**:
`[X₀, u^iv^j ∂_A] = (α(i-1)+j)·u^iv^j ∂_A`.  For `Y = h∂_A` one has
`[X₀, Y] = (X₀h - αh)∂_A`; on the monomial `h = u^iv^j` this coefficient is
`(α(i-1)+j)h`. -/
theorem bracket_A_component (α : ℝ) (i j : ℕ) (p : ℝ × ℝ) :
    X0op α (fun q => q.1 ^ i * q.2 ^ j) p - α * (p.1 ^ i * p.2 ^ j)
      = (α * (i - 1) + j) * (p.1 ^ i * p.2 ^ j) := by
  rw [X0op_monomial]
  ring

/-- **Proposition 2 proof, second commutator**:
`[X₀, u^iv^j ∂_B] = (αi+j-1)·u^iv^j ∂_B`.  For `Y = h∂_B` one has
`[X₀, Y] = (X₀h - h)∂_B`. -/
theorem bracket_B_component (α : ℝ) (i j : ℕ) (p : ℝ × ℝ) :
    X0op α (fun q => q.1 ^ i * q.2 ^ j) p - p.1 ^ i * p.2 ^ j
      = (α * i + j - 1) * (p.1 ^ i * p.2 ^ j) := by
  rw [X0op_monomial]
  ring

/-- **Proposition 2 proof: there is no nonlinear `∂_A`-component resonance.**
The resonance relation `α(i-1) + j = 0`, cleared of denominators
(`α = 2/(m+1)`), reads `2i + (m+1)j = 2`; for `m ≥ 1` it has no solution with
`i + j ≥ 2`. -/
theorem no_A_resonance (m i j : ℕ) (hm : 1 ≤ m) (hij : 2 ≤ i + j) :
    2 * i + (m + 1) * j ≠ 2 := by
  intro h
  rcases j with _ | _ | k
  · omega
  · omega
  · have hexp : (m + 1) * (k + 2) = (m + 1) * k + 2 * m + 2 := by ring
    rw [hexp] at h
    omega

/-- **Proposition 2 proof: the `∂_B`-component resonances.**  The relation
`αi + j = 1`, cleared of denominators, reads `2i + (m+1)j = m+1`; with
`i + j ≥ 2` its only solution is `j = 0, i = r = (m+1)/2` — possible only for
odd `m ≥ 3` (the resonant monomial `cA^r∂_B`). -/
theorem B_resonance_iff (m i j : ℕ) :
    (2 ≤ i + j ∧ 2 * i + (m + 1) * j = m + 1)
      ↔ (j = 0 ∧ 2 * i = m + 1 ∧ 3 ≤ m ∧ m % 2 = 1) := by
  constructor
  · rintro ⟨hij, hw⟩
    rcases j with _ | _ | k
    · refine ⟨rfl, by omega, by omega, by omega⟩
    · omega
    · exfalso
      have hexp : (m + 1) * (k + 2) = (m + 1) * k + 2 * m + 2 := by ring
      rw [hexp] at hw
      omega
  · rintro ⟨rfl, h2, h3, _⟩
    omega

/-! ### Formal power series and the Euler operator

The eigen-equation eq:eigen, written in the linearizing coordinates of eq:linearized
and multiplied by `m+1`, becomes `2·u∂_uΔ + (m+1)·v∂_vΔ = 2(m+1)·Δ`.  We realize
`u_i∂_{u_i}` on `MvPowerSeries (Fin 2) ℝ` coefficientwise (the local Mathlib has no
`MvPowerSeries.pderiv`) and *prove* that on polynomials it agrees with
`X i * pderiv i`, so the definition is honest. -/

/-- The Euler operator `u_i ∂/∂u_i` on 2-variable formal power series,
coefficientwise: it multiplies the coefficient of the monomial `n` by `n i`. -/
def euler (i : Fin 2) (f : MvPowerSeries (Fin 2) ℝ) : MvPowerSeries (Fin 2) ℝ :=
  fun n => (n i : ℝ) * MvPowerSeries.coeff n f

theorem coeff_euler (i : Fin 2) (f : MvPowerSeries (Fin 2) ℝ) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (euler i f) = (n i : ℝ) * MvPowerSeries.coeff n f := rfl

/-- **Justification of `euler`**: on polynomials it is exactly
`X i * ∂/∂(X i)`. -/
theorem euler_coe (i : Fin 2) (P : MvPolynomial (Fin 2) ℝ) :
    euler i (P : MvPowerSeries (Fin 2) ℝ)
      = ((MvPolynomial.X i * MvPolynomial.pderiv i P : MvPolynomial (Fin 2) ℝ) :
          MvPowerSeries (Fin 2) ℝ) := by
  ext n
  rw [coeff_euler, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe]
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [MvPolynomial.pderiv_monomial]
      rw [show (MvPolynomial.X i * MvPolynomial.monomial (s - Finsupp.single i 1) (a * s i) :
            MvPolynomial (Fin 2) ℝ)
          = MvPolynomial.monomial (Finsupp.single i 1 + (s - Finsupp.single i 1)) (a * s i) by
        rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
      rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      rcases Nat.eq_zero_or_pos (s i) with hs | hs
      · have h1 : ((s i : ℕ) : ℝ) = 0 := by rw [hs]; norm_num
        rw [h1, mul_zero, ite_self]
        by_cases h : s = n
        · subst h; simp [hs]
        · simp [h]
      · have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.mpr hs
        have hkey : Finsupp.single i 1 + (s - Finsupp.single i 1) = s := by
          rw [add_comm]; exact tsub_add_cancel_of_le hle
        rw [hkey]
        split_ifs with h
        · subst h; ring
        · ring
  | add p q hp hq =>
      rw [map_add, mul_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, ← hp, ← hq]
      ring

/-- Extensionality for `Fin 2`-indexed exponents. -/
theorem fin2_finsupp_ext {n e : Fin 2 →₀ ℕ} (h0 : n 0 = e 0) (h1 : n 1 = e 1) :
    n = e := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- **eq:weight solutions (Proposition 3 proof)**: the nonnegative-integer
solutions of `αi + j = 2`, i.e. `2i + (m+1)j = 2(m+1)`, are exactly `(m+1, 0)`,
`(0, 2)`, and — only when `m` is odd — `((m+1)/2, 1)`. -/
theorem weight_two_solutions (m i j : ℕ) :
    2 * i + (m + 1) * j = 2 * (m + 1) ↔
      (i = m + 1 ∧ j = 0) ∨ (2 * i = m + 1 ∧ j = 1) ∨ (i = 0 ∧ j = 2) := by
  constructor
  · intro h
    rcases j with _ | _ | _ | k
    · left; constructor <;> omega
    · right; left; constructor <;> omega
    · right; right; constructor <;> omega
    · exfalso
      have hexp : (m + 1) * (k + 3) = (m + 1) * k + 3 * (m + 1) := by ring
      rw [hexp] at h
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨h2, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

/-- **Proposition 3, support step**: a formal series solving the (denominator-
cleared) eigen-equation `2·u∂_uΔ + (m+1)·v∂_vΔ = 2(m+1)Δ` (eq:eigen in the
linearized coordinates of eq:linearized) is supported on the weight-two
monomials of eq:weight. -/
theorem eigen_support (m : ℕ) (f : MvPowerSeries (Fin 2) ℝ)
    (heig : (2 : ℝ) • euler 0 f + ((m : ℝ) + 1) • euler 1 f = (2 * ((m : ℝ) + 1)) • f)
    (n : Fin 2 →₀ ℕ) (hn : MvPowerSeries.coeff n f ≠ 0) :
    (n 0 = m + 1 ∧ n 1 = 0) ∨ (2 * n 0 = m + 1 ∧ n 1 = 1) ∨ (n 0 = 0 ∧ n 1 = 2) := by
  have h := congrArg (fun g => MvPowerSeries.coeff n g) heig
  simp only [map_add, MvPowerSeries.coeff_smul, coeff_euler] at h
  have hw : 2 * n 0 + (m + 1) * n 1 = 2 * (m + 1) := by
    by_contra hne
    have hcast : ((2 * n 0 + (m + 1) * n 1 : ℕ) : ℝ) ≠ ((2 * (m + 1) : ℕ) : ℝ) := by
      exact_mod_cast hne
    apply hn
    have hfac : ((2 * n 0 + (m + 1) * n 1 : ℕ) : ℝ) * MvPowerSeries.coeff n f
        = ((2 * (m + 1) : ℕ) : ℝ) * MvPowerSeries.coeff n f := by
      push_cast
      linarith
    by_contra hc
    exact hcast (mul_right_cancel₀ hc hfac)
  exact (weight_two_solutions m (n 0) (n 1)).mp hw

/-- **Proposition 3 (display after eq:weight)**: the *entire* analytic germ is a
polynomial with at most three terms,
`Δ = c₀·u^{m+1} + c₁·u^{(m+1)/2}v + c₂·v²` — when `m` is even the middle
coefficient is automatically `0` (no integer `(m+1)/2`-monomial exists), so the
formula below covers both parities. -/
theorem eigen_series_eq (m : ℕ) (f : MvPowerSeries (Fin 2) ℝ)
    (heig : (2 : ℝ) • euler 0 f + ((m : ℝ) + 1) • euler 1 f = (2 * ((m : ℝ) + 1)) • f) :
    f = MvPowerSeries.monomial (Finsupp.single 0 (m + 1))
          (MvPowerSeries.coeff (Finsupp.single 0 (m + 1)) f)
      + MvPowerSeries.monomial (Finsupp.single 0 ((m + 1) / 2) + Finsupp.single 1 1)
          (MvPowerSeries.coeff (Finsupp.single 0 ((m + 1) / 2) + Finsupp.single 1 1) f)
      + MvPowerSeries.monomial (Finsupp.single 1 2)
          (MvPowerSeries.coeff (Finsupp.single 1 2) f) := by
  set e1 : Fin 2 →₀ ℕ := Finsupp.single 0 (m + 1) with he1
  set e2 : Fin 2 →₀ ℕ := Finsupp.single 0 ((m + 1) / 2) + Finsupp.single 1 1 with he2
  set e3 : Fin 2 →₀ ℕ := Finsupp.single 1 2 with he3
  have he1a : e1 0 = m + 1 := by rw [he1, Finsupp.single_eq_same]
  have he1b : e1 1 = 0 := by rw [he1, Finsupp.single_eq_of_ne (by decide)]
  have he2a : e2 0 = (m + 1) / 2 := by
    rw [he2, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide)]
    omega
  have he2b : e2 1 = 1 := by
    rw [he2, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide)]
  have he3a : e3 0 = 0 := by rw [he3, Finsupp.single_eq_of_ne (by decide)]
  have he3b : e3 1 = 2 := by rw [he3, Finsupp.single_eq_same]
  have h12 : e1 ≠ e2 := by
    intro h
    have h' : e1 1 = e2 1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h
    rw [he1b, he2b] at h'
    omega
  have h13 : e1 ≠ e3 := by
    intro h
    have h' : e1 1 = e3 1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h
    rw [he1b, he3b] at h'
    omega
  have h23 : e2 ≠ e3 := by
    intro h
    have h' : e2 1 = e3 1 := congrArg (fun s : Fin 2 →₀ ℕ => s 1) h
    rw [he2b, he3b] at h'
    omega
  ext n
  simp only [map_add, MvPowerSeries.coeff_monomial]
  by_cases h1 : n = e1
  · subst h1
    rw [if_pos rfl, if_neg h12, if_neg h13]
    ring
  · by_cases h2 : n = e2
    · subst h2
      rw [if_neg (fun h => h12 h.symm), if_pos rfl, if_neg h23]
      ring
    · by_cases h3 : n = e3
      · subst h3
        rw [if_neg (fun h => h13 h.symm), if_neg (fun h => h23 h.symm), if_pos rfl]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h3]
        have hz : (0 : ℝ) + 0 + 0 = 0 := by norm_num
        rw [hz]
        by_contra hc
        rcases eigen_support m f heig n hc with ⟨h0, h1'⟩ | ⟨h0, h1'⟩ | ⟨h0, h1'⟩
        · exact h1 (fin2_finsupp_ext (by omega) (by omega))
        · exact h2 (fin2_finsupp_ext (by omega) (by omega))
        · exact h3 (fin2_finsupp_ext (by omega) (by omega))

/-- **Proposition 2, the killing step (eq:kill)**: if
`(X₀ - 2)Δ' + 2c·A^rB = 0` with `2r = m+1` (all scaled by `m+1`), then `c = 0`:
the monomial `A^rB` has weight `αr + 1 = 2` and so lies in the kernel of the
scalar homological operator `X₀ - 2`; taking its coefficient forces `c = 0`.
Hence every nonlinear resonance of `X` vanishes and the convergent
Poincaré–Dulac normal form is exactly linear (eq:linearized). -/
theorem resonant_coefficient_vanishes (m r : ℕ) (hr : 2 * r = m + 1) (c : ℝ)
    (D : MvPowerSeries (Fin 2) ℝ)
    (hkill : (2 : ℝ) • euler 0 D + ((m : ℝ) + 1) • euler 1 D - (2 * ((m : ℝ) + 1)) • D
        + (2 * c * ((m : ℝ) + 1)) •
            MvPowerSeries.monomial (Finsupp.single 0 r + Finsupp.single 1 1) (1 : ℝ)
      = 0) :
    c = 0 := by
  set e : Fin 2 →₀ ℕ := Finsupp.single 0 r + Finsupp.single 1 1 with he
  have he0 : e 0 = r := by
    rw [he, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide)]
    omega
  have he1 : e 1 = 1 := by
    rw [he, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide)]
  have h := congrArg (fun gg => MvPowerSeries.coeff e gg) hkill
  simp only [map_add, map_sub, MvPowerSeries.coeff_smul, coeff_euler,
    MvPowerSeries.coeff_monomial, if_true, map_zero, he0, he1] at h
  have hrr : (r : ℝ) * 2 = (m : ℝ) + 1 := by
    have hc' : ((2 * r : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hr
    push_cast at hc'
    linarith
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hkey : c * ((m : ℝ) + 1) = 0 := by
    linear_combination (1 / 2) * h - (MvPowerSeries.coeff e D / 2) * hrr
  rcases mul_eq_zero.mp hkey with h' | h'
  · exact h'
  · exact absurd h' (ne_of_gt hm1)

/-! ### Completing the square and the unsigned `A_m` normal form -/

/-- **Proposition 3, completing the square (eq:split)**: with `2r = m+1` (odd
case; the even case is `c₁ = 0`), the substitution `v ↦ v + (c₁/2c₂)u^r` turns
`c₂v² + c₁u^rv + c₀u^{m+1}` into `c₂v² + κu^{m+1}` with
`κ = c₀ - c₁²/(4c₂)`. -/
theorem complete_square (c₂ c₁ c₀ : ℝ) (hc : c₂ ≠ 0) (r : ℕ) (u v : ℝ) :
    c₂ * v ^ 2 + c₁ * u ^ r * v + c₀ * u ^ (2 * r)
      = c₂ * (v + c₁ / (2 * c₂) * u ^ r) ^ 2
        + (c₀ - c₁ ^ 2 / (4 * c₂)) * u ^ (2 * r) := by
  field_simp
  ring

/-- **eq:kappat**: subtracting `t·AH = t·C·u^{m+1}` from
`Δ = c₂v² + c₁u^rv + c₀u^{m+1}` and completing the square yields
`κ_t = κ - tC` — the coefficients `c₂, c₁` are untouched, so `dκ/dt = -C`. -/
theorem kappa_t_formula (c₂ c₁ c₀ C t : ℝ) (hc : c₂ ≠ 0) (r : ℕ) (u v : ℝ) :
    (c₂ * v ^ 2 + c₁ * u ^ r * v + c₀ * u ^ (2 * r)) - t * (C * u ^ (2 * r))
      = c₂ * (v + c₁ / (2 * c₂) * u ^ r) ^ 2
        + ((c₀ - c₁ ^ 2 / (4 * c₂)) - t * C) * u ^ (2 * r) := by
  field_simp
  ring

/-- **eq:kappat, even case**: when `m` is even there is no middle term
(`c₁ = 0` automatically, by `weight_two_solutions`), and the shift is immediate:
`κ_t = c₀ - tC`. -/
theorem kappa_t_formula_even (c₂ c₀ C t : ℝ) (k : ℕ) (u v : ℝ) :
    (c₂ * v ^ 2 + c₀ * u ^ k) - t * (C * u ^ k)
      = c₂ * v ^ 2 + (c₀ - t * C) * u ^ k := by
  ring

/-- Unsigned real `A_m` singularity (Introduction): right-equivalence, by a
linear diagonal coordinate change, to `ε₂v² + ε₁u^{m+1}` with
`ε₁, ε₂ ∈ {±1}`.  (The germs to which this is applied are already in the normal
coordinates of eq:split, so linear changes suffice.) -/
def UnsignedAm (m : ℕ) (f : ℝ × ℝ → ℝ) : Prop :=
  ∃ s t ε₁ ε₂ : ℝ, s ≠ 0 ∧ t ≠ 0 ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
    ∀ p : ℝ × ℝ, f (s * p.1, t * p.2) = ε₂ * p.2 ^ 2 + ε₁ * p.1 ^ (m + 1)

/-- For `y > 0` and `k ≥ 1` there is a positive `s` with `s^k = y⁻¹` (the
scaling used to normalize the coefficients to `±1`). -/
theorem exists_pow_eq_inv (y : ℝ) (hy : 0 < y) (k : ℕ) (hk : 1 ≤ k) :
    ∃ s : ℝ, 0 < s ∧ s ^ k = y⁻¹ := by
  refine ⟨y ^ (-(1 / (k : ℝ))), Real.rpow_pos_of_pos hy _, ?_⟩
  rw [← Real.rpow_natCast (y ^ (-(1 / (k : ℝ)))) k, ← Real.rpow_mul hy.le]
  rw [show -(1 / (k : ℝ)) * k = -1 by
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
    field_simp]
  exact Real.rpow_neg_one y

/-- **Proposition 3, classification**: `c₂v² + κu^{m+1}` with `c₂ ≠ 0` has
unsigned real type `A_m` if and only if `κ ≠ 0`.  (If `κ = 0` the germ is
`c₂v²`, of type `A_∞`, and no diagonal change produces the `u^{m+1}` term.) -/
theorem unsignedAm_iff (m : ℕ) (c₂ κ : ℝ) (hc : c₂ ≠ 0) :
    UnsignedAm m (fun p => c₂ * p.2 ^ 2 + κ * p.1 ^ (m + 1)) ↔ κ ≠ 0 := by
  constructor
  · rintro ⟨s, t, ε₁, ε₂, hs, ht, hε₁, hε₂, hid⟩ hκ0
    have h := hid (1, 0)
    simp only [hκ0] at h
    norm_num at h
    rcases hε₁ with h1 | h1 <;> rw [h1] at h <;> norm_num at h
  · intro hκ
    -- scale `u` by `s` with `s^{m+1} = |κ|⁻¹` and `v` by `t` with `t² = |c₂|⁻¹`
    obtain ⟨s, hspos, hspow⟩ :=
      exists_pow_eq_inv |κ| (abs_pos.mpr hκ) (m + 1) (by omega)
    obtain ⟨t, htpos, htpow⟩ :=
      exists_pow_eq_inv |c₂| (abs_pos.mpr hc) 2 (by omega)
    refine ⟨s, t, if 0 < κ then 1 else -1, if 0 < c₂ then 1 else -1,
      ne_of_gt hspos, ne_of_gt htpos, ?_, ?_, ?_⟩
    · split_ifs <;> simp
    · split_ifs <;> simp
    · intro p
      have hκs : κ * s ^ (m + 1) = if 0 < κ then 1 else -1 := by
        rw [hspow]
        rcases lt_trichotomy κ 0 with h | h | h
        · rw [if_neg (by linarith), abs_of_neg h]
          field_simp
        · exact absurd h hκ
        · rw [if_pos h, abs_of_pos h]
          field_simp
      have hct : c₂ * t ^ 2 = if 0 < c₂ then 1 else -1 := by
        rw [htpow]
        rcases lt_trichotomy c₂ 0 with h | h | h
        · rw [if_neg (by linarith), abs_of_neg h]
          field_simp
        · exact absurd h hc
        · rw [if_pos h, abs_of_pos h]
          field_simp
      calc c₂ * (t * p.2) ^ 2 + κ * (s * p.1) ^ (m + 1)
          = (c₂ * t ^ 2) * p.2 ^ 2 + (κ * s ^ (m + 1)) * p.1 ^ (m + 1) := by ring
        _ = (if 0 < c₂ then 1 else -1) * p.2 ^ 2
            + (if 0 < κ then 1 else -1) * p.1 ^ (m + 1) := by rw [hκs, hct]

/-! ## §4 The analytic transverse deformation -/

/-- **eq:cohomology, formal solvability**: the cohomological equation
`Xφ = λ - λ(0)`, in linearizing coordinates and cleared of denominators
(`2·u∂_uφ + (m+1)·v∂_vφ = (m+1)·g` with `g = λ - λ(0)`, `g(0) = 0`), has a
unique formal power-series solution with `φ(0) = 0`: every nonconstant monomial
is divided by its strictly positive weight `2i + (m+1)j`.  (Convergence of `φ`
is the standard Poincaré-domain estimate — both eigenvalues positive — which
Mathlib does not yet know.) -/
theorem cohomological_solvable (m : ℕ) (g : MvPowerSeries (Fin 2) ℝ)
    (hg : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) g = 0) :
    ∃! φ : MvPowerSeries (Fin 2) ℝ,
      MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) φ = 0 ∧
      (2 : ℝ) • euler 0 φ + ((m : ℝ) + 1) • euler 1 φ = ((m : ℝ) + 1) • g := by
  have hzero : ∀ n : Fin 2 →₀ ℕ, n 0 = 0 → n 1 = 0 → n = 0 := by
    intro n h0 h1
    exact fin2_finsupp_ext (e := 0) (by simpa using h0) (by simpa using h1)
  have hwpos : ∀ n : Fin 2 →₀ ℕ, n ≠ 0 →
      (0 : ℝ) < 2 * (n 0 : ℝ) + ((m : ℝ) + 1) * (n 1 : ℝ) := by
    intro n hn
    by_cases h0 : n 0 = 0
    · have h1 : n 1 ≠ 0 := fun h => hn (hzero n h0 h)
      have : (1 : ℝ) ≤ (n 1 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
      have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) (n 0)]
    · have : (1 : ℝ) ≤ (n 0 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      nlinarith [Nat.cast_nonneg (α := ℝ) (n 1), Nat.cast_nonneg (α := ℝ) m]
  set φ₀ : MvPowerSeries (Fin 2) ℝ :=
    fun n => (((m : ℝ) + 1) * MvPowerSeries.coeff n g)
      / (2 * (n 0 : ℝ) + ((m : ℝ) + 1) * (n 1 : ℝ)) with hphi
  have hcoeff : ∀ k : Fin 2 →₀ ℕ, MvPowerSeries.coeff k φ₀
      = (((m : ℝ) + 1) * MvPowerSeries.coeff k g)
          / (2 * (k 0 : ℝ) + ((m : ℝ) + 1) * (k 1 : ℝ)) := fun k => rfl
  refine ⟨φ₀, ⟨?_, ?_⟩, ?_⟩
  · -- φ(0) = 0
    rw [hcoeff, hg]
    norm_num
  · -- the equation, coefficientwise
    ext n
    simp only [map_add, MvPowerSeries.coeff_smul, coeff_euler, hcoeff]
    by_cases hn : n = 0
    · subst hn
      rw [hg]
      norm_num
    · have hw' : (2 * (n 0 : ℝ) + ((m : ℝ) + 1) * (n 1 : ℝ)) ≠ 0 :=
        ne_of_gt (hwpos n hn)
      field_simp
  · -- uniqueness
    rintro ψ ⟨hψ0, hψeq⟩
    ext n
    rw [hcoeff]
    have h := congrArg (fun f => MvPowerSeries.coeff n f) hψeq
    simp only [map_add, MvPowerSeries.coeff_smul, coeff_euler] at h
    by_cases hn : n = 0
    · subst hn
      rw [hψ0, hg]
      norm_num
    · have hw := hwpos n hn
      rw [eq_div_iff (ne_of_gt hw)]
      linear_combination h

/-- `X₀(e^φ·u^m) = (X₀φ + αm)·e^φ·u^m`: the derivation computation behind
eq:H/eq:Hhomogeneous, by real calculus (chain rule for `exp`, product rule). -/
theorem X0op_exp_mul_pow (α : ℝ) (φ : ℝ × ℝ → ℝ) (m : ℕ) (hm : 1 ≤ m) (p : ℝ × ℝ)
    (h1 : DifferentiableAt ℝ (fun a => φ (a, p.2)) p.1)
    (h2 : DifferentiableAt ℝ (fun b => φ (p.1, b)) p.2) :
    X0op α (fun q => Real.exp (φ q) * q.1 ^ m) p
      = (X0op α φ p + α * m) * (Real.exp (φ p) * p.1 ^ m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hd1 : HasDerivAt (fun a : ℝ => Real.exp (φ (a, p.2)) * a ^ (k + 1))
      (Real.exp (φ (p.1, p.2)) * deriv (fun a => φ (a, p.2)) p.1 * p.1 ^ (k + 1)
        + Real.exp (φ (p.1, p.2)) * ((k + 1) * p.1 ^ k)) p.1 := by
    have := (h1.hasDerivAt.exp).mul (hasDerivAt_pow (k + 1) p.1)
    simpa using this
  have hd2 : HasDerivAt (fun b : ℝ => Real.exp (φ (p.1, b)) * p.1 ^ (k + 1))
      (Real.exp (φ (p.1, p.2)) * deriv (fun b => φ (p.1, b)) p.2 * p.1 ^ (k + 1)) p.2 :=
    (h2.hasDerivAt.exp).mul_const _
  simp only [X0op, pd1, pd2]
  rw [hd1.deriv, hd2.deriv]
  push_cast
  ring

/-- **eq:Hhomogeneous**: if `φ` solves the cohomological equation
`X₀φ = λ - λ(0)` with `λ(0) = αm` (eq:lambda), then `H = e^φu^m` satisfies
`X₀H = λ·H` — in the hodograph picture, `XH = (1 - G_B)H`. -/
theorem XH_eq_lambda_H (α : ℝ) (φ lam : ℝ × ℝ → ℝ) (m : ℕ) (hm : 1 ≤ m) (p : ℝ × ℝ)
    (h1 : DifferentiableAt ℝ (fun a => φ (a, p.2)) p.1)
    (h2 : DifferentiableAt ℝ (fun b => φ (p.1, b)) p.2)
    (hcoh : X0op α φ p = lam p - α * m) :
    X0op α (fun q => Real.exp (φ q) * q.1 ^ m) p
      = lam p * (Real.exp (φ p) * p.1 ^ m) := by
  rw [X0op_exp_mul_pow α φ m hm p h1 h2, hcoh]
  ring

/-- Linearity of `E` in `F` along the deformation `F_t = F + tH` (eq:deform):
`E(F + tH, G) = E(F,G) + t·((1-G_B)H - XH)`. -/
theorem Eexpr_deform (F G H : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ)
    (hF1 : DifferentiableAt ℝ (fun a => F (a, p.2)) p.1)
    (hF2 : DifferentiableAt ℝ (fun b => F (p.1, b)) p.2)
    (hH1 : DifferentiableAt ℝ (fun a => H (a, p.2)) p.1)
    (hH2 : DifferentiableAt ℝ (fun b => H (p.1, b)) p.2) :
    Eexpr (fun q => F q + t * H q) G p
      = Eexpr F G p + t * ((1 - pd2 G p) * H p - Xop G H p) := by
  have hp1 : pd1 (fun q => F q + t * H q) p = pd1 F p + t * pd1 H p := by
    have hd : HasDerivAt (fun a : ℝ => F (a, p.2) + t * H (a, p.2))
        (deriv (fun a => F (a, p.2)) p.1 + t * deriv (fun a => H (a, p.2)) p.1) p.1 :=
      hF1.hasDerivAt.add (hH1.hasDerivAt.const_mul t)
    simp only [pd1]
    exact hd.deriv
  have hp2 : pd2 (fun q => F q + t * H q) p = pd2 F p + t * pd2 H p := by
    have hd : HasDerivAt (fun b : ℝ => F (p.1, b) + t * H (p.1, b))
        (deriv (fun b => F (p.1, b)) p.2 + t * deriv (fun b => H (p.1, b)) p.2) p.2 :=
      hF2.hasDerivAt.add (hH2.hasDerivAt.const_mul t)
    simp only [pd2]
    exact hd.deriv
  simp only [Eexpr, Xop, hp1, hp2]
  ring

/-- **§4, the deformation is a `W`-congruence**: if `E(F,G) = 0` and
`XH = (1-G_B)H` (eq:Hhomogeneous), then `E(F_t, G_t) = E(F + tH, G) = 0`
(eq:deform); by Lemma 1 this gives `W(P_t,Q_t) = 0`. -/
theorem Eexpr_deform_zero (F G H : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ)
    (hF1 : DifferentiableAt ℝ (fun a => F (a, p.2)) p.1)
    (hF2 : DifferentiableAt ℝ (fun b => F (p.1, b)) p.2)
    (hH1 : DifferentiableAt ℝ (fun a => H (a, p.2)) p.1)
    (hH2 : DifferentiableAt ℝ (fun b => H (p.1, b)) p.2)
    (hE : Eexpr F G p = 0)
    (hXH : Xop G H p = (1 - pd2 G p) * H p) :
    Eexpr (fun q => F q + t * H q) G p = 0 := by
  rw [Eexpr_deform F G H t p hF1 hF2 hH1 hH2, hE, hXH]
  ring

/-- `Δ_t = Δ - t·AH` (display before eq:kappat). -/
theorem Dfun_deform (F H : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) :
    Dfun (fun q => F q + t * H q) p = Dfun F p - t * (p.1 * H p) := by
  simp only [Dfun]
  ring

/-- `X` applied to a product with the coordinate `A`:
`X(A·H) = A·((1+G_B)H + XH)` — the derivation property of `X` plus
`XA = A(1+G_B)`. -/
theorem Xop_mul_fst (G H : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h1 : DifferentiableAt ℝ (fun a => H (a, p.2)) p.1) :
    Xop G (fun q => q.1 * H q) p = p.1 * ((1 + pd2 G p) * H p + Xop G H p) := by
  have hd1 : HasDerivAt (fun a : ℝ => a * H (a, p.2))
      (1 * H (p.1, p.2) + p.1 * deriv (fun a => H (a, p.2)) p.1) p.1 :=
    (hasDerivAt_id _).mul h1.hasDerivAt
  have hd2 : pd2 (fun q => q.1 * H q) p = p.1 * pd2 H p := by
    simp only [pd2]
    exact deriv_const_mul_field _
  simp only [Xop, pd1] at *
  rw [hd1.deriv, hd2]
  ring

/-- **Display before eq:kappat: `X(AH) = 2AH`.**  From `XA = A(1+G_B)` and
`XH = (1-G_B)H`, the derivation property gives
`X(AH) = A(1+G_B)H + A(1-G_B)H = 2AH`. -/
theorem X_AH_eq_two_AH (G H : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h1 : DifferentiableAt ℝ (fun a => H (a, p.2)) p.1)
    (hXH : Xop G H p = (1 - pd2 G p) * H p) :
    Xop G (fun q => q.1 * H q) p = 2 * (p.1 * H p) := by
  rw [Xop_mul_fst G H p h1, hXH]
  ring

/-- **eq:kappat, order step**: among the weight-two monomials
(`u^{m+1}`, `u^{(m+1)/2}v`, `v²`), only `u^{m+1}` has ordinary order `m+1` when
`m ≥ 2`.  Hence an eigen-series whose coefficients vanish below total degree
`m+1` — as `AH` does, having order `m+1` — is exactly `C·u^{m+1}`, where `C` is
its `(m+1,0)`-coefficient (nonzero for `AH`, whose leading term is a nonzero
multiple of `A^{m+1}`). -/
theorem eigen_series_order (m : ℕ) (hm : 2 ≤ m) (f : MvPowerSeries (Fin 2) ℝ)
    (heig : (2 : ℝ) • euler 0 f + ((m : ℝ) + 1) • euler 1 f = (2 * ((m : ℝ) + 1)) • f)
    (horder : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < m + 1 → MvPowerSeries.coeff n f = 0) :
    f = MvPowerSeries.monomial (Finsupp.single 0 (m + 1))
          (MvPowerSeries.coeff (Finsupp.single 0 (m + 1)) f) := by
  ext n
  rw [MvPowerSeries.coeff_monomial]
  by_cases h : n = Finsupp.single 0 (m + 1)
  · rw [if_pos h, h]
  · rw [if_neg h]
    by_contra hc
    rcases eigen_support m f heig n hc with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine h (fin2_finsupp_ext ?_ ?_)
      · rw [Finsupp.single_eq_same]; exact h0
      · rw [Finsupp.single_eq_of_ne (by decide)]; exact h1
    · exact hc (horder n (by omega))
    · exact hc (horder n (by omega))

/-! ## The case `m = 1` (eq:m1)

For `m = 1` the normalization gives directly `δ₂ = 4a(ay² + q₂₀x²)`: computed
exactly on the normalized quadratic model (`q₀₂ = -a`); the cubic-and-higher
remainder of the germ contributes only `O(3)` to `δ`.  `q₂₀ ≠ 0` is precisely
the unsigned real `A₁` condition; `q₂₀ = 0` is the rank-one exceptional
locus. -/

/-- The discriminant as a function, `δ = (P_x - Q_y)² + 4P_yQ_x` (eq:delta). -/
def discFun (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (pd1 P p - pd2 Q p) ^ 2 + 4 * pd2 P p * pd1 Q p

/-- **eq:m1**: on the normalized `m = 1` two-jet (`p₁₁ = a`, `q₀₂ = -a`),
`δ₂ = 4a(ay² + q₂₀x²)` exactly. -/
theorem m_one_discriminant (a q20 : ℝ) (p : ℝ × ℝ) :
    discFun (Pmod a) (Qmod q20 (-a)) p = 4 * a * (a * p.2 ^ 2 + q20 * p.1 ^ 2) := by
  rw [discFun, pd1_Pmod, pd2_Pmod, pd1_Qmod, pd2_Qmod]
  ring

/-- **`m = 1` branch of Theorem 1**: the two-jet `δ₂` has unsigned real type
`A₁` if and only if `q₂₀ ≠ 0`. -/
theorem m_one_A1_iff (a q20 : ℝ) (ha : a ≠ 0) :
    UnsignedAm 1 (fun p => 4 * a * (a * p.2 ^ 2 + q20 * p.1 ^ 2)) ↔ q20 ≠ 0 := by
  have hfe : (fun p : ℝ × ℝ => 4 * a * (a * p.2 ^ 2 + q20 * p.1 ^ 2))
      = fun p => (4 * a * a) * p.2 ^ 2 + (4 * a * q20) * p.1 ^ (1 + 1) := by
    funext p
    ring
  rw [hfe, unsignedAm_iff 1 (4 * a * a) (4 * a * q20)
    (mul_ne_zero (mul_ne_zero (by norm_num) ha) ha)]
  constructor
  · intro h hq
    exact h (by rw [hq]; ring)
  · intro h hq
    rcases mul_eq_zero.mp hq with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact ha h''
    · exact h h'

/-! ## §5 Proof of the main theorem

The genericity mechanism: `κ` is a continuous scalar on the stratum (a finite-jet
analytic function of the germ in the analytic coefficient topology), and through
every germ runs a continuous curve of genuine germs along which `κ` moves affinely
with nonzero speed `-C` (eq:kappat).  Then `{κ ≠ 0}` is open and dense, and the
exceptional locus is cut out transversely. -/

/-- **The topological genericity lemma (Theorem 1 proof)**: if a continuous
scalar `κ` on a topological space is moved with nonzero affine speed along a
continuous curve through every point, then `{κ ≠ 0}` is open and dense. -/
theorem transverse_line_dense_open {S : Type*} [TopologicalSpace S] (κ : S → ℝ)
    (hκ : Continuous κ)
    (hdef : ∀ x : S, ∃ γ : ℝ → S, Continuous γ ∧ γ 0 = x ∧
      ∃ C : ℝ, C ≠ 0 ∧ ∀ t, κ (γ t) = κ x - t * C) :
    IsOpen {x | κ x ≠ 0} ∧ Dense {x | κ x ≠ 0} := by
  constructor
  · -- openness: a finite-jet nonvanishing condition
    have : {x | κ x ≠ 0} = κ ⁻¹' {(0 : ℝ)}ᶜ := rfl
    rw [this]
    exact isOpen_compl_singleton.preimage hκ
  · -- density via the transverse deformation
    rw [dense_iff_inter_open]
    rintro U hU ⟨x, hxU⟩
    obtain ⟨γ, hγc, hγ0, C, hC, hκt⟩ := hdef x
    have hV : IsOpen (γ ⁻¹' U) := hU.preimage hγc
    have h0V : (0 : ℝ) ∈ γ ⁻¹' U := by
      simp only [Set.mem_preimage, hγ0]
      exact hxU
    obtain ⟨t, htV, htne⟩ :=
      (dense_compl_singleton (κ x / C)).inter_open_nonempty (γ ⁻¹' U) hV ⟨0, h0V⟩
    have htne' : t ≠ κ x / C := by simpa using htne
    refine ⟨γ t, htV, ?_⟩
    simp only [Set.mem_setOf_eq, hκt t]
    intro hzero
    apply htne'
    rw [eq_div_iff hC]
    linarith

/-- **The hypothesis package for the fixed-`m` analytic stratum `𝒮_m`.**  `S` is
the stratum with its analytic coefficient topology (§1); the fields record what
the paper's analytic machinery (not expressible in current Mathlib) provides:

* `disc x` — the discriminant germ of `x` written in the right-equivalence
  coordinates of Proposition 3 (via Lemma 1's hodograph reduction, the convergent
  Poincaré–Dulac linearization of Proposition 2 — whose sole possible resonant
  coefficient vanishes by `resonant_coefficient_vanishes` — and the weight
  classification `eigen_series_eq` + completing the square `complete_square`);
* `c₂ x ≠ 0` — the nondegenerate `v²`-coefficient (`Δ = B² + O(3)`, eq:linear);
* `kappa x` — the scalar `κ` of eq:split, with `disc_eq` recording Proposition 3's
  normal form `δ ∼ c₂v² + κu^{m+1}` (the factor 4 of `δ = 4Δ` is absorbed);
* `kappa_continuous` — `κ` is a finite-jet analytic function of the germ, hence
  continuous in the analytic coefficient topology (Theorem 1 proof: "this is a
  finite-jet nonvanishing condition");
* `deform` — the analytic family `t ↦ (P_t, Q_t)` of eq:deform, produced from
  `F_t = F + tH` by Cauchy–Kowalevski (eq:CK1–eq:CK2; the determinant is
  nonzero by `CK_determinant`), staying inside the fixed-`m` stratum, continuous
  in `t`, and equal to the germ at `t = 0`;
* `Cc x ≠ 0` and `kappa_deform` — eq:kappat: `κ_t = κ - tC` with
  `C ≠ 0` the leading coefficient of `AH = Cu^{m+1}`
  (`X(AH) = 2AH` by `X_AH_eq_two_AH`; `AH = Cu^{m+1}` by `eigen_series_order`;
  the bookkeeping `κ_t = κ - tC` by `kappa_t_formula`). -/
structure StratumData (m : ℕ) (S : Type*) [TopologicalSpace S] where
  /-- The discriminant germ in Proposition 3's right-equivalence coordinates. -/
  disc : S → ℝ × ℝ → ℝ
  /-- The `v²`-coefficient of eq:split. -/
  c₂ : S → ℝ
  /-- The scalar `κ` of eq:split / Theorem 1. -/
  kappa : S → ℝ
  /-- `c₂ ≠ 0` (eq:split). -/
  c₂_ne : ∀ x, c₂ x ≠ 0
  /-- Proposition 3: `δ ∼ c₂v² + κu^{m+1}`. -/
  disc_eq : ∀ x p, disc x p = c₂ x * p.2 ^ 2 + kappa x * p.1 ^ (m + 1)
  /-- `κ` is a finite-jet function, continuous in the coefficient topology. -/
  kappa_continuous : Continuous kappa
  /-- The analytic deformation family of eq:deform, inside the stratum. -/
  deform : S → ℝ → S
  /-- Continuity of the family in the deformation parameter. -/
  deform_continuous : ∀ x, Continuous (deform x)
  /-- At `t = 0` the family is the original germ. -/
  deform_zero : ∀ x, deform x 0 = x
  /-- The leading coefficient `C` of `AH = Cu^{m+1}` (eq:kappat). -/
  Cc : S → ℝ
  /-- `C ≠ 0` (eq:kappat). -/
  Cc_ne : ∀ x, Cc x ≠ 0
  /-- eq:kappat: `κ_t = κ - tC`. -/
  kappa_deform : ∀ x t, kappa (deform x t) = kappa x - t * Cc x

/-- **Theorem 1 (thm:main)**: in the fixed-`m` stratum, the set of germs whose
discriminant has unsigned real type `A_m` — equivalently `κ ≠ 0` — is open and
dense. -/
theorem generic_unsigned_Am (m : ℕ) {S : Type*} [TopologicalSpace S]
    (D : StratumData m S) :
    IsOpen {x | UnsignedAm m (D.disc x)} ∧ Dense {x | UnsignedAm m (D.disc x)} := by
  have hset : {x | UnsignedAm m (D.disc x)} = {x | D.kappa x ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    have hfe : D.disc x = fun p => D.c₂ x * p.2 ^ 2 + D.kappa x * p.1 ^ (m + 1) :=
      funext fun p => D.disc_eq x p
    rw [hfe, unsignedAm_iff m (D.c₂ x) (D.kappa x) (D.c₂_ne x)]
  rw [hset]
  exact transverse_line_dense_open D.kappa D.kappa_continuous
    (fun x => ⟨D.deform x, D.deform_continuous x, D.deform_zero x,
      D.Cc x, D.Cc_ne x, D.kappa_deform x⟩)

/-- **Theorem 1, exceptional locus**: along each deformation line the function
`t ↦ κ(deform x t)` is affine with derivative `-C ≠ 0`, and it vanishes at
exactly one parameter — the transversality making `{κ = 0}` a smooth
hypersurface ("`dκ/dt = -C ≠ 0`"). -/
theorem exceptional_locus_line (m : ℕ) {S : Type*} [TopologicalSpace S]
    (D : StratumData m S) (x : S) :
    (∀ t : ℝ, HasDerivAt (fun t => D.kappa (D.deform x t)) (-(D.Cc x)) t) ∧
      ∃! t : ℝ, D.kappa (D.deform x t) = 0 := by
  constructor
  · intro t
    have hfe : (fun t => D.kappa (D.deform x t)) = fun t => D.kappa x - t * D.Cc x :=
      funext fun t => D.kappa_deform x t
    rw [hfe]
    simpa using (hasDerivAt_const t (D.kappa x)).sub ((hasDerivAt_id t).mul_const (D.Cc x))
  · refine ⟨D.kappa x / D.Cc x, ?_, ?_⟩
    · show D.kappa (D.deform x (D.kappa x / D.Cc x)) = 0
      rw [D.kappa_deform, div_mul_cancel₀ _ (D.Cc_ne x)]
      ring
    · intro t ht
      rw [D.kappa_deform] at ht
      rw [eq_div_iff (D.Cc_ne x)]
      linarith

/-- The hypothesis package is consistent (not vacuous): the model in which the
stratum is the `κ`-line itself. -/
def trivialModel (m : ℕ) : StratumData m ℝ where
  disc x := fun p => p.2 ^ 2 + x * p.1 ^ (m + 1)
  c₂ _ := 1
  kappa x := x
  c₂_ne _ := one_ne_zero
  disc_eq x p := by ring
  kappa_continuous := continuous_id
  deform x t := x - t
  deform_continuous x := (continuous_const.sub continuous_id)
  deform_zero x := by ring
  Cc _ := 1
  Cc_ne _ := one_ne_zero
  kappa_deform x t := by ring

/-- Sanity check of Theorem 1 in the model: both conclusions hold. -/
example (m : ℕ) :
    IsOpen {x : ℝ | UnsignedAm m ((trivialModel m).disc x)}
      ∧ Dense {x : ℝ | UnsignedAm m ((trivialModel m).disc x)} :=
  generic_unsigned_Am m (trivialModel m)

end

end IntegerWCongruenceGenericity
