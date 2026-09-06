import Mathlib

/-!
# Umbilics of Analytic W-Congruences with `m ∉ ℕ` Have `A∞` Discriminant

Lean certification of `noninteger_w_congruence.tex`.

The paper studies nondegenerate umbilics of real-analytic `W`-congruences
`f(x,y) = (x,y,0)`, `ξ(x,y) = (P,Q,1)` with the extended Weingarten equation
(tex `eq:W`) and discriminant `δ = (P_x−Q_y)² + 4 P_y Q_x` (tex `eq:disc`),
normalized at the umbilic by `p20 = p02 = q11 = 0`, `p11 = a ≠ 0`, `q02 ≠ 0`,
`p11 ≠ q02` (tex `eq:normalization`), with parameter `m = −q02/a` (tex `eq:m`).
Main theorem (`thm:main`): if `m` is not a positive integer, the discriminant
germ is analytically right-equivalent to `v²` — type `A∞`.

What is formalized, and how:

* **All arithmetic of the normalized parameter** — `α = 2/(m+1)`, the resonance
  equivalences `nα = 1 ↔ m = 2n−1` and `nα = 2 ↔ m = n−1`, and the three
  nonresonance conditions used in the paper — is fully proved
  (`one_add_GB_eq_alpha`, `resonance_BB_iff`, `resonance_first_iff`,
  `nonresonance_first`, `nonresonance_second`).

* **The hodograph identities of Lemma 1 (`lem:identities`)** are certified as
  follows.  `W = 2JE` is proved as a polynomial identity in the point values of
  all first/second derivatives, with the two Schwarz mixed-partial symmetries
  (`P_xy = P_yx`, `Q_xy = Q_yx`) as hypotheses (`W_eq_two_J_E`);
  `(X−2)Δ = A·E` is proved with `∂_AΔ`, `∂_BΔ` computed as honest derivatives
  of `Δ = B² − A·F` (`hasDerivAt_Delta_fst/snd`, `X_sub_two_Delta_eq_A_mul_E`);
  `δ = 4Δ` is `discrim_eq_four_Delta`; and the eigenfunction equation
  `XΔ = 2Δ` (`eq:eigenfunction`) follows in `XDelta_eq_two_Delta` from
  `W = 0` and `J ≠ 0`.  The preliminary jet computation "`m ≠ 1` and the first
  differentiated `W`-equation give `q20 = 0`" (tex §2) is fully proved from the
  product rule as `q20_eq_zero`.  The claim `Δ = B² + O(3)` of `eq:linear` is
  proved as a genuine asymptotic statement (`Delta_sub_Bsq_isBigO`).

* **The invariant-curve recursion of Lemma 2 (`lem:curve`)**: the triangular
  Briot–Bouquet recursion `(nα − 1) φ_n = Ψ_n(φ_2,…,φ_{n−1})` (tex
  `eq:recursion`) is proved to have a unique formal solution under the
  nonresonance `nα ≠ 1` (`briotBouquet_recursion`).  The *convergence* of that
  formal solution (the majorant argument, cited by the paper to
  Ilyashenko–Yakovenko) is genuine hard analysis absent from Mathlib; the
  analytic invariant curve therefore enters the main theorem only through the
  hypothesis that coordinates `(s,t)` as in tex `eq:Xst` exist.

* **Section 4 (the heart of the paper)** is fully formalized at the level of
  formal power series in the coordinates `(s,t)` of `eq:Xst`, i.e. in
  `ℝ⟦s⟧⟦t⟧`: the two restriction/leading-coefficient arguments
  (`eq:firstrestriction`, `eq:secondrestriction`) are `restriction_first` and
  `restriction_second`; both analytic divisions are done via `X ∣ ·`; the
  operator computation `X(tH) = t(XH + wH)` is `Xact_X_mul`; the square-root
  coordinate change `t̃ = t√U` is built from a self-contained formal
  square-root construction (`sqrtCoeff`, `exists_powerSeries_sqrt`); and the
  conclusion `δ = 4Δ = (t·unit)²` — the formal-power-series form of "the
  discriminant is right-equivalent to `v²`", i.e. type `A∞` — is
  `discriminant_formal_square` / `umbilic_typeAInfinity`.

Everything below compiles with zero `sorry`s; the only unproved inputs are the
explicitly documented hypotheses transcribing tex `eq:Xst` (existence of the
analytic invariant-curve coordinates) and the pointwise chain-rule/Schwarz
identifications noted above.
-/

namespace NonintegerWCongruence

open PowerSeries Filter Asymptotics

noncomputable section

/-! ## §1. The normalized parameter and its resonances

Tex `eq:normalization`, `eq:m`, `eq:linear`, and the two displayed resonance
equivalences `nα = 1 ↔ m = 2n−1` (proof of Lemma 2) and `nα = 2 ↔ m = n−1`
(proof of Theorem 1). -/

/-- The normalized parameter `m = −q02/a` (tex `eq:m`, with `p11 = a`). -/
def mparam (a q02 : ℝ) : ℝ := -q02 / a

/-- The linearization eigenvalue `α = 2/(m+1)` (tex `eq:linear`). -/
def alpha (m : ℝ) : ℝ := 2 / (m + 1)

theorem m_add_one_ne_zero {m : ℝ} (hm1 : m ≠ -1) : m + 1 ≠ 0 := fun h => hm1 (by linarith)

/-- `α ≠ 0` (tex `eq:linear`). -/
theorem alpha_ne_zero {m : ℝ} (hm1 : m ≠ -1) : alpha m ≠ 0 :=
  div_ne_zero two_ne_zero (m_add_one_ne_zero hm1)

/-- Certifies the linear part of the vector field `X` (tex `eq:linear`):
from `G = ((1−m)/(1+m))B + O(2)` the `∂_A`-coefficient `A(1+G_B)` of `X`
has linear part `α·A`, because `1 + (1−m)/(1+m) = 2/(m+1) = α`. -/
theorem one_add_GB_eq_alpha {m : ℝ} (hm1 : m ≠ -1) : 1 + (1 - m) / (1 + m) = alpha m := by
  have h : (1 : ℝ) + m ≠ 0 := by intro h; exact hm1 (by linarith)
  have halpha : alpha m = 2 / (1 + m) := by rw [alpha, add_comm]
  rw [halpha, eq_div_iff h, add_mul, div_mul_cancel₀ _ h]
  ring

/-- The resonance equivalence of Lemma 2 (tex proof of `lem:curve`):
`nα = 1 ↔ m = 2n − 1`. -/
theorem resonance_BB_iff {m : ℝ} (hm1 : m ≠ -1) (n : ℕ) :
    (n : ℝ) * alpha m = 1 ↔ m = 2 * (n : ℝ) - 1 := by
  have h := m_add_one_ne_zero hm1
  unfold alpha
  rw [← mul_div_assoc, div_eq_iff h]
  constructor <;> intro hh <;> linarith

/-- The resonance equivalence in the proof of Theorem 1 (tex §4):
`nα = 2 ↔ m = n − 1`. -/
theorem resonance_first_iff {m : ℝ} (hm1 : m ≠ -1) (n : ℕ) :
    (n : ℝ) * alpha m = 2 ↔ m = (n : ℝ) - 1 := by
  have h := m_add_one_ne_zero hm1
  unfold alpha
  rw [← mul_div_assoc, div_eq_iff h]
  constructor <;> intro hh <;> linarith

/-- First nonresonance condition (used for `eq:firstrestriction`): if `m ≠ 0`,
`m ≠ −1` and `m` is not a positive integer, then `nα ≠ 2` for every `n ≥ 1`.
(The paper needs this for `n ≥ 3`; it holds already from `n ≥ 1`, which is why
the restriction `f = Δ(s,0)` vanishes identically with no order bookkeeping.) -/
theorem nonresonance_first {m : ℝ} (hm0 : m ≠ 0) (hm1 : m ≠ -1)
    (hmnat : ∀ k : ℕ, 0 < k → m ≠ (k : ℝ)) :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) * alpha m ≠ 2 := by
  intro n hn hres
  have hm := (resonance_first_iff hm1 n).mp hres
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · exact hm0 (by push_cast at hm; linarith)
  · refine hmnat (n - 1) (by omega) ?_
    rw [hm]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring

/-- Second nonresonance condition (used for `eq:secondrestriction` and for the
Briot–Bouquet recursion `eq:recursion`): if `m ≠ −1` and `m` is not a positive
integer, then `nα ≠ 1` for every `n ≥ 0`.  (`nα = 1` would force `m = 2n−1`,
which is `−1` for `n = 0` and a positive odd integer for `n ≥ 1`.) -/
theorem nonresonance_second {m : ℝ} (hm1 : m ≠ -1)
    (hmnat : ∀ k : ℕ, 0 < k → m ≠ (k : ℝ)) :
    ∀ n : ℕ, (n : ℝ) * alpha m ≠ 1 := by
  intro n hres
  have hm := (resonance_BB_iff hm1 n).mp hres
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    exact hm1 (by push_cast at hm; linarith)
  · refine hmnat (2 * n - 1) (by omega) ?_
    rw [hm]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    ring

/-! ## §2. The Weingarten equation and the hodograph identities (Lemma 1)

Tex `eq:W`, `eq:disc`, `eq:hodograph`, `eq:Delta`, `eq:X`, `eq:E`,
`lem:identities`, `eq:eigenfunction`. -/

/-- The extended Weingarten operator `W(P,Q)` (tex `eq:W`), as a function of the
point values of the first and second derivatives of `P` and `Q`. -/
def Wop (Px Py Qx Qy Pxx Pxy Pyy Qxx Qxy Qyy : ℝ) : ℝ :=
  (Qy - Px) * (Qxx * Pyy - Pxx * Qyy) - 2 * Py * (Pxx * Qxy - Qxx * Pxy)
    + 2 * Qx * (Pxy * Qyy - Pyy * Qxy)

/-- The discriminant `δ = (P_x−Q_y)² + 4 P_y Q_x` (tex `eq:disc`). -/
def discrim (Px Py Qx Qy : ℝ) : ℝ := (Px - Qy) ^ 2 + 4 * Py * Qx

/-- The function `E` of tex `eq:E`. -/
def Eop (A B F FA FB GA GB : ℝ) : ℝ :=
  (1 - GB) * F - (1 + GB) * A * FA + (A * GA - B) * FB - 2 * B * GA

/-- **Lemma 1, first identity (`W = 2JE`).**  Point values: `A, B` are the
hodograph coordinates, `Ax, Ay, Bx, By` their `(x,y)`-derivatives,
`F, FA, FB, G, GA, GB` the values and `(A,B)`-partials of `F` and `G` from
tex `eq:hodograph`.  The arguments of `Wop` are exactly the chain-rule
expansions of the first and second derivatives of `P, Q` obtained from
`P_x = B+G`, `P_y = A`, `Q_x = −F`, `Q_y = G−B` ("these four identities and
their first derivatives", tex proof of `lem:identities`).  The two hypotheses
are the Schwarz symmetries `P_yx = P_xy` and `Q_yx = Q_xy` written in the same
chain-rule form; `J = A_x B_y − A_y B_x`. -/
theorem W_eq_two_J_E (A B Ax Ay Bx By F FA FB G GA GB : ℝ)
    (hSchwarzP : Ax = By + GA * Ay + GB * By)
    (hSchwarzQ : -(FA * Ay + FB * By) = GA * Ax + GB * Bx - Bx) :
    Wop (B + G) A (-F) (G - B)
        (Bx + GA * Ax + GB * Bx) Ax Ay
        (-(FA * Ax + FB * Bx)) (-(FA * Ay + FB * By)) (GA * Ay + GB * By - By)
      = 2 * (Ax * By - Ay * Bx) * Eop A B F FA FB GA GB := by
  subst hSchwarzP
  unfold Wop Eop
  linear_combination (-2 * (Ay * B * GA - Ay * F + B * By * GB + B * By)) * hSchwarzQ

/-- **Lemma 1, third identity (`δ = 4Δ`).**  Under the hodograph substitutions
`P_x = B+G`, `P_y = A`, `Q_x = −F`, `Q_y = G−B` the discriminant of tex
`eq:disc` equals `4Δ = 4(B² − AF)` (tex `eq:Delta`). -/
theorem discrim_eq_four_Delta (A B F G : ℝ) :
    discrim (B + G) A (-F) (G - B) = 4 * (B ^ 2 - A * F) := by
  unfold discrim
  ring

/-- Partial derivative `∂_A Δ = −F − A F_A` of `Δ = B² − AF` (tex `eq:Delta`),
as an honest one-variable derivative in the `A`-slot. -/
theorem hasDerivAt_Delta_fst (F : ℝ → ℝ → ℝ) (FA A B : ℝ)
    (hFA : HasDerivAt (fun x => F x B) FA A) :
    HasDerivAt (fun x => B ^ 2 - x * F x B) (-(F A B) - A * FA) A := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 A := hasDerivAt_id A
  have h := (hid.mul hFA).const_sub (B ^ 2)
  convert h using 1
  ring

/-- Partial derivative `∂_B Δ = 2B − A F_B` of `Δ = B² − AF` (tex `eq:Delta`). -/
theorem hasDerivAt_Delta_snd (F : ℝ → ℝ → ℝ) (FB A B : ℝ)
    (hFB : HasDerivAt (fun y => F A y) FB B) :
    HasDerivAt (fun y => y ^ 2 - A * F A y) (2 * B - A * FB) B := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * B) B := by
    simpa using hasDerivAt_pow 2 B
  exact hsq.sub (hFB.const_mul A)

/-- **Lemma 1, second identity (`(X−2)Δ = A·E`).**  Applying the vector field
`X = A(1+G_B)∂_A + (B−AG_A)∂_B` (tex `eq:X`) to `Δ = B² − AF` and subtracting
`2Δ` gives `A·E`, with `∂_AΔ = −F−AF_A` and `∂_BΔ = 2B−AF_B` as computed in
`hasDerivAt_Delta_fst/snd`. -/
theorem X_sub_two_Delta_eq_A_mul_E (A B F FA FB GA GB : ℝ) :
    A * (1 + GB) * (-F - A * FA) + (B - A * GA) * (2 * B - A * FB)
      - 2 * (B ^ 2 - A * F) = A * Eop A B F FA FB GA GB := by
  unfold Eop
  ring

/-- **`eq:eigenfunction` at a point.**  Combining all of Lemma 1: under the
hodograph chain-rule substitutions and Schwarz symmetries, if the Jacobian
`J = A_x B_y − A_y B_x` is nonzero and the Weingarten equation `W = 0` holds,
then `X Δ = 2Δ`, where `∂_AΔ`, `∂_BΔ` are genuine derivatives of
`Δ = B² − A·F`. -/
theorem XDelta_eq_two_Delta (F : ℝ → ℝ → ℝ) (A B FA FB G GA GB Ax Ay Bx By : ℝ)
    (hFA : HasDerivAt (fun x => F x B) FA A)
    (hFB : HasDerivAt (fun y => F A y) FB B)
    (hSchwarzP : Ax = By + GA * Ay + GB * By)
    (hSchwarzQ : -(FA * Ay + FB * By) = GA * Ax + GB * Bx - Bx)
    (hJ : Ax * By - Ay * Bx ≠ 0)
    (hW : Wop (B + G) A (-(F A B)) (G - B)
        (Bx + GA * Ax + GB * Bx) Ax Ay
        (-(FA * Ax + FB * Bx)) (-(FA * Ay + FB * By)) (GA * Ay + GB * By - By) = 0) :
    A * (1 + GB) * deriv (fun x => B ^ 2 - x * F x B) A
      + (B - A * GA) * deriv (fun y => y ^ 2 - A * F A y) B
      = 2 * (B ^ 2 - A * F A B) := by
  -- `W = 2JE` and `J ≠ 0` give `E = 0` (tex: "the equation W = 0 implies E = 0")
  have hWJE := W_eq_two_J_E A B Ax Ay Bx By (F A B) FA FB G GA GB hSchwarzP hSchwarzQ
  have hE : Eop A B (F A B) FA FB GA GB = 0 := by
    rw [hW] at hWJE
    have h2J : (2 : ℝ) * (Ax * By - Ay * Bx) ≠ 0 := by
      exact mul_ne_zero two_ne_zero hJ
    exact (mul_eq_zero.mp hWJE.symm).resolve_left h2J
  rw [(hasDerivAt_Delta_fst F FA A B hFA).deriv, (hasDerivAt_Delta_snd F FB A B hFB).deriv]
  have hkey := X_sub_two_Delta_eq_A_mul_E A B (F A B) FA FB GA GB
  rw [hE, mul_zero] at hkey
  linarith

/-- **The jet computation of tex §2**: "Because `m ≠ 1`, the first
differentiated `W`-equation gives `q20 = 0`."  Here `T1, …, T6` are the six
factors of tex `eq:W` restricted to the line `y = 0`
(`T1 = Q_y−P_x`, `T2 = Q_xx P_yy − P_xx Q_yy`, `T3 = P_y`,
`T4 = P_xx Q_xy − Q_xx P_xy`, `T5 = Q_x`, `T6 = P_xy Q_yy − P_yy Q_xy`).
The hypotheses record: the umbilic conditions `T1(0) = T3(0) = T5(0) = 0`;
the normalized 2-jet values (tex `eq:normalization`, with `q02 = −m·a`)
`T1'(0) = q11 − p20 = 0`, `T3'(0) = p11 = a`, `T5'(0) = q20`,
`T4(0) = p20·q11 − q20·p11 = −q20·a`, `T6(0) = p11·q02 − p02·q11 = −m·a²`;
differentiability of the second factors; and the `W`-equation along `y = 0`.
Everything else — the product rule and the conclusion — is proved. -/
theorem q20_eq_zero (a m q20 : ℝ) (ha : a ≠ 0) (hm : m ≠ 1)
    (T1 T2 T3 T4 T5 T6 : ℝ → ℝ) (d2 d4 d6 : ℝ)
    (hT1 : T1 0 = 0) (hT3 : T3 0 = 0) (hT5 : T5 0 = 0)
    (h1 : HasDerivAt T1 0 0) (h3 : HasDerivAt T3 a 0) (h5 : HasDerivAt T5 q20 0)
    (h2 : HasDerivAt T2 d2 0) (h4 : HasDerivAt T4 d4 0) (h6 : HasDerivAt T6 d6 0)
    (hT4 : T4 0 = -q20 * a) (hT6 : T6 0 = -m * a ^ 2)
    (hW : ∀ x, T1 x * T2 x - 2 * T3 x * T4 x + 2 * T5 x * T6 x = 0) :
    q20 = 0 := by
  -- the derivative of the (identically zero) W-expression at 0
  have hA : HasDerivAt (fun x => T1 x * T2 x) (0 * T2 0 + T1 0 * d2) 0 := h1.mul h2
  have hB : HasDerivAt (fun x => 2 * T3 x * T4 x) (2 * (a * T4 0 + T3 0 * d4)) 0 := by
    simpa [mul_assoc] using (h3.mul h4).const_mul (2 : ℝ)
  have hC : HasDerivAt (fun x => 2 * T5 x * T6 x) (2 * (q20 * T6 0 + T5 0 * d6)) 0 := by
    simpa [mul_assoc] using (h5.mul h6).const_mul (2 : ℝ)
  have hD : HasDerivAt (fun x => T1 x * T2 x - 2 * T3 x * T4 x + 2 * T5 x * T6 x)
      ((0 * T2 0 + T1 0 * d2) - 2 * (a * T4 0 + T3 0 * d4)
        + 2 * (q20 * T6 0 + T5 0 * d6)) 0 := (hA.sub hB).add hC
  have hzero : HasDerivAt (fun x => T1 x * T2 x - 2 * T3 x * T4 x + 2 * T5 x * T6 x)
      (0 : ℝ) 0 := by
    have : (fun x => T1 x * T2 x - 2 * T3 x * T4 x + 2 * T5 x * T6 x) = fun _ => (0 : ℝ) :=
      funext hW
    rw [this]
    exact hasDerivAt_const 0 0
  have hval : (0 * T2 0 + T1 0 * d2) - 2 * (a * T4 0 + T3 0 * d4)
      + 2 * (q20 * T6 0 + T5 0 * d6) = 0 := hD.unique hzero
  rw [hT1, hT3, hT5, hT4, hT6] at hval
  -- hval : 2·a²·q20 − 2·m·a²·q20 = 0, i.e. 2a²(1−m)·q20 = 0
  have hkey : 2 * a ^ 2 * (1 - m) * q20 = 0 := by linarith [hval]
  have hne : 2 * a ^ 2 * (1 - m) ≠ 0 := by
    have h1m : (1 : ℝ) - m ≠ 0 := fun h => hm (by linarith)
    positivity
  exact (mul_eq_zero.mp hkey).resolve_left hne

/-- **`eq:linear`, last assertion (`Δ = B² + O(3)`)** as a genuine asymptotic
statement: since the normalized 2-jet gives `F = O(2)` (tex `eq:hodograph`),
the function `Δ = B² − A·F` differs from `B²` by `O(‖(A,B)‖³)` at the origin. -/
theorem Delta_sub_Bsq_isBigO (F : ℝ × ℝ → ℝ)
    (hF : F =O[nhds (0 : ℝ × ℝ)] fun p => ‖p‖ ^ 2) :
    (fun p : ℝ × ℝ => (p.2 ^ 2 - p.1 * F p) - p.2 ^ 2) =O[nhds 0]
      fun p => ‖p‖ ^ 3 := by
  have h1 : (fun p : ℝ × ℝ => p.1) =O[nhds (0 : ℝ × ℝ)] fun p => ‖p‖ :=
    isBigO_of_le _ fun p => by simpa using norm_fst_le p
  have h2 := h1.mul hF
  have h3 : (fun p : ℝ × ℝ => p.1 * F p) =O[nhds 0] fun p => ‖p‖ ^ 3 := by
    refine h2.trans (isBigO_of_le _ fun p => ?_)
    simp only [norm_mul, norm_pow, norm_norm]
    exact le_of_eq (by ring)
  simpa using h3.neg_left

/-! ## §3. The Briot–Bouquet recursion (Lemma 2, formal part)

Tex `eq:invariance`, `eq:recursion`: seeking the invariant curve `B = φ(A)`,
`φ(A) = Σ_{n≥2} φ_n Aⁿ`, invariance gives the triangular recursion
`(nα − 1) φ_n = Ψ_n(φ_2,…,φ_{n−1})`.  We prove that, under the nonresonance
`nα ≠ 1` for `n ≥ 2` (equivalently `m ≠ 2n−1`, excluded since `m` is not a
positive integer), this recursion has a unique formal solution.  The
convergence of the resulting series (the majorant argument for analytic
Briot–Bouquet equations, cited by the paper to Ilyashenko–Yakovenko, Ch. 2)
is not formalized; the analytic invariant curve enters the main theorem below
only through the hypothesis that the coordinates of tex `eq:Xst` exist. -/

/-- The formal solution of the Briot–Bouquet recursion: `φ_n = 0` for `n < 2`
and `φ_n = Ψ_n(φ|_{<n}) / (nα − 1)` for `n ≥ 2` (tex `eq:recursion`). -/
noncomputable def bbSol (α : ℝ) (Ψ : ℕ → (ℕ → ℝ) → ℝ) : ℕ → ℝ
  | n =>
    if 2 ≤ n then
      Ψ n (fun k => if _hk : k < n then bbSol α Ψ k else 0) / ((n : ℝ) * α - 1)
    else 0
  decreasing_by exact _hk

/-- **Lemma 2, formal part (tex `eq:recursion`).**  If `nα ≠ 1` for all
`n ≥ 2` (nonresonance; equivalent to `m ≠ 2n−1` by `resonance_BB_iff`) and
each `Ψ_n` depends only on the coefficients `φ_k`, `k < n` (triangularity),
then the recursion `(nα − 1) φ_n = Ψ_n(φ)` with `φ_0 = φ_1 = 0` has exactly
one solution. -/
theorem briotBouquet_recursion (α : ℝ) (hα : ∀ n : ℕ, 2 ≤ n → (n : ℝ) * α ≠ 1)
    (Ψ : ℕ → (ℕ → ℝ) → ℝ)
    (hΨ : ∀ (n : ℕ) (f g : ℕ → ℝ), (∀ k, k < n → f k = g k) → Ψ n f = Ψ n g) :
    ∃! φ : ℕ → ℝ,
      (∀ n : ℕ, n < 2 → φ n = 0)
        ∧ ∀ n : ℕ, 2 ≤ n → ((n : ℝ) * α - 1) * φ n = Ψ n φ := by
  have hden : ∀ n : ℕ, 2 ≤ n → (n : ℝ) * α - 1 ≠ 0 := fun n hn h =>
    hα n hn (by linarith)
  refine ⟨bbSol α Ψ, ⟨?_, ?_⟩, ?_⟩
  · intro n hn
    rw [bbSol]
    simp [Nat.not_le.mpr hn]
  · intro n hn
    have hunf : bbSol α Ψ n
        = Ψ n (fun k => if _hk : k < n then bbSol α Ψ k else 0) / ((n : ℝ) * α - 1) := by
      rw [bbSol]
      simp [hn]
    rw [hunf, mul_comm, div_mul_cancel₀ _ (hden n hn)]
    exact hΨ n _ _ fun k hk => by simp [hk]
  · intro φ' ⟨hlow, hrec⟩
    funext n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · rw [hlow n h2, bbSol]
        simp [Nat.not_le.mpr h2]
      · have hΨeq : Ψ n φ' = Ψ n (fun k => if _hk : k < n then bbSol α Ψ k else 0) :=
          hΨ n _ _ fun k hk => by simp [hk, ih k hk]
        have h1 := hrec n h2
        rw [hΨeq] at h1
        have hunf : bbSol α Ψ n
            = Ψ n (fun k => if _hk : k < n then bbSol α Ψ k else 0) / ((n : ℝ) * α - 1) := by
          rw [bbSol]
          simp [h2]
        rw [hunf, eq_div_iff (hden n h2)]
        linear_combination h1

/-! ## §4. One-variable restriction arguments (tex `eq:firstrestriction`,
`eq:secondrestriction`)

These are the two "one-dimensional order comparisons" of the abstract, carried
out honestly on formal power series: if the restriction of `Δ` (resp. `H`) to
the invariant curve were nonzero of some order `n`, comparing leading
coefficients in the restricted equation forces a resonance, which is excluded.
Hence the restrictions vanish identically. -/

/-- Leading-coefficient computation for `v·f′` when all coefficients of `f`
below `n` vanish and `v = α·s + O(s²)`:  the `n`-th coefficient is `n·α·fₙ`. -/
theorem coeff_mul_derivative_of_vanishing (v f : PowerSeries ℝ) (n : ℕ)
    (hv0 : constantCoeff v = 0) (hmin : ∀ k, k < n → coeff k f = 0) :
    coeff n (v * d⁄dX ℝ f) = (n : ℝ) * coeff 1 v * coeff n f := by
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, hv0, zero_mul]
    simp
  | succ m =>
    rw [coeff_mul, Finset.sum_eq_single (1, m)]
    · rw [coeff_derivative]
      push_cast
      ring
    · rintro ⟨i, j⟩ hmem hne
      rw [Finset.mem_antidiagonal] at hmem
      rcases Nat.eq_zero_or_pos i with hi | hi
      · have : coeff i v = 0 := by
          rw [hi, coeff_zero_eq_constantCoeff_apply, hv0]
        rw [this, zero_mul]
      · have hi2 : 2 ≤ i := by
          rcases Nat.lt_or_ge i 2 with h | h
          · have hi1 : i = 1 := by omega
            have hjm : j = m := by omega
            exact absurd (by rw [hi1, hjm]) hne
          · exact h
        have hj : j + 1 < m + 1 := by omega
        rw [coeff_derivative, hmin (j + 1) hj, zero_mul, mul_zero]
    · intro habs
      exact absurd (Finset.mem_antidiagonal.mpr (by simp [add_comm])) habs

/-- Leading-coefficient computation for `w·f` when all coefficients of `f`
below `n` vanish: the `n`-th coefficient is `w(0)·fₙ`. -/
theorem coeff_mul_of_vanishing (w f : PowerSeries ℝ) (n : ℕ)
    (hmin : ∀ k, k < n → coeff k f = 0) :
    coeff n (w * f) = constantCoeff w * coeff n f := by
  rw [coeff_mul, Finset.sum_eq_single (0, n)]
  · rw [coeff_zero_eq_constantCoeff_apply]
  · rintro ⟨i, j⟩ hmem hne
    rw [Finset.mem_antidiagonal] at hmem
    have hi : i ≠ 0 := by
      rintro rfl
      apply hne
      have hj : j = n := by omega
      rw [hj]
    have hj : j < n := by omega
    rw [hmin j hj, mul_zero]
  · intro habs
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) habs

/-- **First restriction argument (tex `eq:firstrestriction`).**  If
`v(s) f′(s) = 2 f(s)` with `v = αs + O(s²)` and `nα ≠ 2` for all `n ≥ 1`
(no first resonance, by `nonresonance_first`), then `f ≡ 0`.  This is the
paper's leading-term comparison `αn = 2 ⟺ m = n−1`, run at the true order of
`f`; the paper's bound `n ≥ 3` is not needed because `m ∉ {0} ∪ ℕ` already
excludes every `n ≥ 1`. -/
theorem restriction_first (α : ℝ) (v f : PowerSeries ℝ)
    (hv0 : constantCoeff v = 0) (hv1 : coeff 1 v = α)
    (hres : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * α ≠ 2)
    (heq : v * d⁄dX ℝ f = 2 * f) : f = 0 := by
  by_contra hf
  have hex : ∃ n, coeff n f ≠ 0 := by
    by_contra hcon
    refine hf (PowerSeries.ext fun n => ?_)
    rw [map_zero]
    by_contra hne
    exact hcon ⟨n, hne⟩
  classical
  set n := Nat.find hex with hndef
  have hn : coeff n f ≠ 0 := Nat.find_spec hex
  have hmin : ∀ k, k < n → coeff k f = 0 := fun k hk => not_not.mp (Nat.find_min hex hk)
  have h1 : coeff n (v * d⁄dX ℝ f) = (n : ℝ) * α * coeff n f := by
    rw [coeff_mul_derivative_of_vanishing v f n hv0 hmin, hv1]
  have h2 : (n : ℝ) * α * coeff n f = 2 * coeff n f := by
    rw [← h1, heq, two_mul, map_add, two_mul]
  have h3 : ((n : ℝ) * α - 2) * coeff n f = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h | h
  · have hres' : (n : ℝ) * α = 2 := by linarith
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hres'
      norm_num at hres'
    · exact hres n h0 hres'
  · exact hn h

/-- **Second restriction argument (tex `eq:secondrestriction`).**  If
`v(s) h′(s) + (w(s)−2) h(s) = 0` with `v = αs + O(s²)`, `w(0) = 1`, and
`nα ≠ 1` for all `n` (no second resonance, by `nonresonance_second`), then
`h ≡ 0`.  This is the paper's comparison `αn + 1 = 2 ⟺ m = 2n−1` (the case
`n = 0` being impossible since `w(0) − 2 = −1 ≠ 0`). -/
theorem restriction_second (α : ℝ) (v w h : PowerSeries ℝ)
    (hv0 : constantCoeff v = 0) (hv1 : coeff 1 v = α)
    (hw0 : constantCoeff w = 1)
    (hres : ∀ n : ℕ, (n : ℝ) * α ≠ 1)
    (heq : v * d⁄dX ℝ h + (w - 2) * h = 0) : h = 0 := by
  by_contra hh
  have hex : ∃ n, coeff n h ≠ 0 := by
    by_contra hcon
    refine hh (PowerSeries.ext fun n => ?_)
    rw [map_zero]
    by_contra hne
    exact hcon ⟨n, hne⟩
  classical
  set n := Nat.find hex with hndef
  have hn : coeff n h ≠ 0 := Nat.find_spec hex
  have hmin : ∀ k, k < n → coeff k h = 0 := fun k hk => not_not.mp (Nat.find_min hex hk)
  have h1 : coeff n (v * d⁄dX ℝ h) = (n : ℝ) * α * coeff n h := by
    rw [coeff_mul_derivative_of_vanishing v h n hv0 hmin, hv1]
  have h2 : coeff n ((w - 2) * h) = -1 * coeff n h := by
    rw [coeff_mul_of_vanishing (w - 2) h n hmin, map_sub, hw0, map_ofNat]
    norm_num
  have h3 : ((n : ℝ) * α - 1) * coeff n h = 0 := by
    have := congrArg (fun φ => coeff n φ) heq
    simp only [map_add, map_zero] at this
    rw [h1, h2] at this
    linear_combination this
  rcases mul_eq_zero.mp h3 with h | h
  · exact hres n (by linarith)
  · exact hn h

/-! ## §5. A self-contained formal square root

Needed for the paper's coordinate change `t̃ = t·√U` (tex, end of proof of
`thm:main`).  Mathlib has no square-root construction for power series, so we
build one: the classical coefficient recursion `v₀ = c`,
`vₙ = e·(uₙ − Σ_{0<i<n} vᵢ v_{n−i})`, `e = (2c)⁻¹`. -/

variable {R : Type*} [CommRing R]

/-- Coefficients of the formal square root of a series with coefficients `u`,
given a square root `c` of `u 0` and an inverse `e` of `2c`. -/
noncomputable def sqrtCoeff (u : ℕ → R) (c e : R) : ℕ → R
  | 0 => c
  | n + 1 =>
    e * (u (n + 1) -
      ∑ i ∈ (Finset.range n).attach,
        sqrtCoeff u c e (i.1 + 1) * sqrtCoeff u c e (n - i.1))
  decreasing_by
  · have := i.2
    simp only [Finset.mem_range] at this
    omega
  · omega

/-- The square-root recursion works: `(Σ sqrtCoeff · Xⁿ)² = Σ uₙ Xⁿ`. -/
theorem coeff_sqrt_mul_sqrt (u : ℕ → R) (c e : R)
    (hc : c * c = u 0) (he : e * (2 * c) = 1) (n : ℕ) :
    coeff n (mk (sqrtCoeff u c e) * mk (sqrtCoeff u c e)) = u n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk]
  cases n with
  | zero =>
    simp only [Finset.sum_range_one, Nat.sub_self]
    rw [show sqrtCoeff u c e 0 = c from by rw [sqrtCoeff]]
    exact hc
  | succ m =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_self, Nat.sub_zero]
    have h0 : sqrtCoeff u c e 0 = c := by rw [sqrtCoeff]
    have hsucc : sqrtCoeff u c e (m + 1)
        = e * (u (m + 1) - ∑ i ∈ Finset.range m,
            sqrtCoeff u c e (i + 1) * sqrtCoeff u c e (m - i)) := by
      rw [sqrtCoeff, Finset.sum_attach (Finset.range m)
        (fun i => sqrtCoeff u c e (i + 1) * sqrtCoeff u c e (m - i))]
    rw [h0, hsucc]
    set S := ∑ i ∈ Finset.range m, sqrtCoeff u c e (i + 1) * sqrtCoeff u c e (m - i) with hS
    linear_combination (u (m + 1) - S) * he

/-- **Formal square root.**  If `c² = u(0)` and `2c` has inverse `e`, then `u`
has a square root in `R⟦X⟧` with constant coefficient `c`. -/
theorem exists_powerSeries_sqrt (u : PowerSeries R) (c e : R)
    (hc : c * c = constantCoeff u) (he : e * (2 * c) = 1) :
    ∃ v : PowerSeries R, v * v = u ∧ constantCoeff v = c := by
  refine ⟨mk (sqrtCoeff (fun n => coeff n u) c e), ?_, ?_⟩
  · ext n
    rw [coeff_sqrt_mul_sqrt (fun n => coeff n u) c e ?_ he n]
    rw [← coeff_zero_eq_constantCoeff_apply] at hc
    exact hc
  · rw [constantCoeff_mk]
    rw [sqrtCoeff]

/-! ## §6. The two-variable setting: `ℝ⟦s⟧⟦t⟧` and the vector field `X`

Tex `eq:Xst`: after Lemma 2, analytic coordinates `(s,t)` exist in which the
invariant curve is `{t = 0}` and `X = v(s,t)∂_s + t·w(s,t)∂_t` with
`v(s,0) = αs + O(s²)` and `w(0,0) = 1`.  We realize the germs at the origin as
formal power series in `ℝ⟦s⟧⟦t⟧` (`t` the outer variable), which is faithful
for all the divisibility and coefficient statements the proof of `thm:main`
makes.  The existence of these coordinates (which uses the convergence part of
Lemma 2) is the one analytic input taken as a hypothesis below. -/

/-- Formal germs in the invariant-curve coordinates `(s,t)` of tex `eq:Xst`:
power series in `t` with coefficients in `ℝ⟦s⟧`. -/
abbrev PS2 : Type := PowerSeries (PowerSeries ℝ)

/-- Partial derivative `∂_s` on `ℝ⟦s⟧⟦t⟧`, acting on each `t`-coefficient. -/
noncomputable def dS (Φ : PS2) : PS2 :=
  mk fun n => d⁄dX ℝ (coeff n Φ)

/-- Restriction to `{t = 0}` intertwines `∂_s` with `d/ds`. -/
theorem constantCoeff_dS (Φ : PS2) :
    constantCoeff (dS Φ) = d⁄dX ℝ (constantCoeff Φ) := by
  unfold dS
  rw [constantCoeff_mk, ← coeff_zero_eq_constantCoeff_apply]

/-- `∂_s` is `t`-linear: `∂_s(t·Φ) = t·∂_sΦ`. -/
theorem dS_X_mul (Φ : PS2) : dS (X * Φ) = X * dS Φ := by
  ext n
  cases n with
  | zero =>
    simp only [dS, coeff_mk, coeff_zero_X_mul, map_zero]
  | succ k =>
    simp only [dS, coeff_mk, coeff_succ_X_mul]

/-- `∂_t X = 1` for the `t`-derivative (`derivativeFun`, which avoids the
`Derivation` algebra packaging). -/
theorem derivativeFun_X' : (X : PS2).derivativeFun = 1 := by
  ext n
  rw [coeff_derivativeFun]
  cases n with
  | zero => simp
  | succ k => simp [coeff_X]

/-- The vector field `X = v ∂_s + t·w ∂_t` of tex `eq:Xst`, acting on formal
germs. -/
noncomputable def Xact (v w Φ : PS2) : PS2 :=
  v * dS Φ + X * w * derivativeFun Φ

/-- Leibniz computation of tex §4: `X(tH) = t·(XH + wH)` (from `Xt = tw`). -/
theorem Xact_X_mul (v w H : PS2) : Xact v w (X * H) = X * (Xact v w H + w * H) := by
  unfold Xact
  rw [dS_X_mul]
  have hdT : (X * H : PS2).derivativeFun = H + X * H.derivativeFun := by
    rw [derivativeFun_mul, derivativeFun_X', smul_eq_mul, smul_eq_mul, mul_one]
    ring
  rw [hdT]
  ring

/-- Restricting the vector field to the invariant curve `{t = 0}`:
`(XΦ)(s,0) = v(s,0)·(d/ds)(Φ(s,0))` (the `t·w ∂_t` part dies). -/
theorem constantCoeff_Xact (v w Φ : PS2) :
    constantCoeff (Xact v w Φ)
      = constantCoeff v * d⁄dX ℝ (constantCoeff Φ) := by
  unfold Xact
  rw [map_add, map_mul, constantCoeff_dS, map_mul, map_mul, constantCoeff_X,
    zero_mul, zero_mul, add_zero]

/-! ## §7. Main theorem (tex `thm:main`, proof in §4)

The discriminant equals `4Δ` (Lemma 1), and we show `4Δ = (t·V)²` with `V` a
unit of positive constant term: the formal-power-series statement of
"`δ` is analytically right-equivalent to `v²`", i.e. the umbilic has type
`A∞`.  The hypotheses transcribe exactly the data provided by Lemma 1 and
Lemma 2 of the paper (`eq:Xst`, `eq:eigenfunction`, `eq:linear`):

* `hv0`, `hv1` : `v(s,0) = α·s + O(s²)`;
* `hw0`        : `w(0,0) = 1`;
* `heig`       : `XΔ = 2Δ` (tex `eq:eigenfunction`, proved pointwise above in
                 `XDelta_eq_two_Delta`);
* `hΔ2`        : the `t²`-coefficient of `Δ` is positive at `s = 0` — this is
                 "`Δ = B² + O(3)` (tex `eq:linear`, proved above as
                 `Delta_sub_Bsq_isBigO`) plus transversality of `t`". -/

theorem discriminant_formal_square (α : ℝ)
    (hres2 : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * α ≠ 2)
    (hres1 : ∀ n : ℕ, (n : ℝ) * α ≠ 1)
    (v w Δ : PS2)
    (hv0 : constantCoeff (constantCoeff v) = 0)
    (hv1 : coeff 1 (constantCoeff v) = α)
    (hw0 : constantCoeff (constantCoeff w) = 1)
    (heig : Xact v w Δ = 2 * Δ)
    (hΔ2 : 0 < constantCoeff (coeff 2 Δ)) :
    ∃ V : PS2, IsUnit V ∧ 0 < constantCoeff (constantCoeff V)
      ∧ 4 * Δ = (X * V) ^ 2 := by
  -- Step 1 (tex eq:firstrestriction): restrict `XΔ = 2Δ` to the invariant
  -- curve and conclude `Δ(s,0) ≡ 0`.
  have hrest1 : constantCoeff v * d⁄dX ℝ (constantCoeff Δ)
      = 2 * constantCoeff Δ := by
    have := congrArg (constantCoeff (R := PowerSeries ℝ)) heig
    rwa [constantCoeff_Xact, map_mul, map_ofNat] at this
  have hΔ0 : constantCoeff Δ = 0 :=
    restriction_first α (constantCoeff v) (constantCoeff Δ) hv0 hv1 hres2 hrest1
  -- Step 2: first analytic division `Δ = t·H`.
  obtain ⟨H, hH⟩ : X ∣ Δ := X_dvd_iff.mpr hΔ0
  -- Step 3 (tex §4): `X(tH) = 2tH` becomes `XH + (w−2)H = 0`.
  have hcancel : Xact v w H + w * H = 2 * H := by
    have h1 : X * (Xact v w H + w * H) = X * (2 * H) := by
      rw [← Xact_X_mul, ← hH, heig, hH]
      ring
    exact mul_left_cancel₀ X_ne_zero h1
  have hHeq : Xact v w H + (w - 2) * H = 0 := by linear_combination hcancel
  -- Step 4 (tex eq:secondrestriction): restrict again and conclude `H(s,0) ≡ 0`.
  have hrest2 : constantCoeff v * d⁄dX ℝ (constantCoeff H)
      + (constantCoeff w - 2) * constantCoeff H = 0 := by
    have := congrArg (constantCoeff (R := PowerSeries ℝ)) hHeq
    rwa [map_add, constantCoeff_Xact, map_mul, map_sub, map_ofNat, map_zero] at this
  have hH0 : constantCoeff H = 0 :=
    restriction_second α (constantCoeff v) (constantCoeff w) (constantCoeff H)
      hv0 hv1 hw0 hres1 hrest2
  -- Step 5: second analytic division, `Δ = t²·U` (tex eq:factor).
  obtain ⟨U, hU⟩ : X ∣ H := X_dvd_iff.mpr hH0
  have hΔU : Δ = X * (X * U) := by rw [hH, hU]
  -- Step 6: `U(0,0) > 0` (tex: "the quadratic term in eq:linear and
  -- transversality of t imply U(0,0) > 0").
  have hcoeff2 : coeff 2 Δ = constantCoeff U := by
    rw [hΔU, show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply]
  have hU0 : 0 < constantCoeff (constantCoeff U) := by rwa [hcoeff2] at hΔ2
  -- Step 7: the square-root coordinate change `t̃ = t·√U` (tex, end of proof).
  -- First a square root of `U(·,0) ∈ ℝ⟦s⟧` …
  have hcpos : 0 < Real.sqrt (constantCoeff (constantCoeff U)) := Real.sqrt_pos.mpr hU0
  obtain ⟨b, hb, hbc⟩ :=
    exists_powerSeries_sqrt (constantCoeff U)
      (Real.sqrt (constantCoeff (constantCoeff U)))
      (2 * Real.sqrt (constantCoeff (constantCoeff U)))⁻¹
      (Real.mul_self_sqrt hU0.le)
      (inv_mul_cancel₀ (mul_pos two_pos hcpos).ne')
  -- … then a square root of `U` itself, using that `2b` is a unit in `ℝ⟦s⟧`.
  obtain ⟨ub, hub⟩ : IsUnit (2 * b : PowerSeries ℝ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_mul, map_ofNat, hbc]
    exact isUnit_iff_ne_zero.mpr (mul_pos two_pos hcpos).ne'
  have hub_inv : (↑ub⁻¹ : PowerSeries ℝ) * (2 * b) = 1 := by
    rw [← hub]
    exact ub.inv_mul
  obtain ⟨V₀, hV₀, hV₀c⟩ := exists_powerSeries_sqrt U b (↑ub⁻¹) hb hub_inv
  -- Step 8: assemble `V = 2·V₀`; then `4Δ = (t·V)²` with `V` a unit,
  -- `V(0,0) = 2√(U(0,0)) > 0`.
  refine ⟨2 * V₀, ?_, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, map_mul, map_ofNat, hV₀c]
    exact ⟨ub, hub⟩
  · rw [map_mul, map_ofNat, map_mul, map_ofNat, hV₀c, hbc]
    positivity
  · rw [hΔU, ← hV₀]
    ring

/-- **Theorem 1 (tex `thm:main`), headline form.**  Let `(P,Q)` solve the
Weingarten equation with a nondegenerate umbilic normalized as in
`eq:normalization` (`p11 = a ≠ 0`, `q02 ≠ 0`, `a ≠ q02`), and suppose the
parameter `m = −q02/a` is **not a positive integer**.  Let `(v, w, Δ)` be the
formal germs, in the invariant-curve coordinates `(s,t)` of tex `eq:Xst`, of
the vector-field coefficients and of `Δ = δ/4`; the hypotheses `hv0–hΔ2`
record exactly what Lemmas 1–2 of the paper establish for them (see
`discriminant_formal_square`).  Then the discriminant `δ = 4Δ` is the square
`(t·V)²` of a formal coordinate function (`V` a unit with `V(0,0) > 0`): the
umbilic has type `A∞`. -/
theorem umbilic_typeAInfinity (a q02 : ℝ)
    (ha : a ≠ 0) (hq02 : q02 ≠ 0) (haq : a ≠ q02)
    (hmnat : ∀ k : ℕ, 0 < k → mparam a q02 ≠ (k : ℝ))
    (v w Δ : PS2)
    (hv0 : constantCoeff (constantCoeff v) = 0)
    (hv1 : coeff 1 (constantCoeff v) = alpha (mparam a q02))
    (hw0 : constantCoeff (constantCoeff w) = 1)
    (heig : Xact v w Δ = 2 * Δ)
    (hΔ2 : 0 < constantCoeff (coeff 2 Δ)) :
    ∃ V : PS2, IsUnit V ∧ 0 < constantCoeff (constantCoeff V)
      ∧ 4 * Δ = (X * V) ^ 2 := by
  -- the admissibility exclusions of tex §1: `m ≠ 0` and `m ≠ −1`
  have hm0 : mparam a q02 ≠ 0 := by
    unfold mparam
    exact div_ne_zero (neg_ne_zero.mpr hq02) ha
  have hm1 : mparam a q02 ≠ -1 := by
    unfold mparam
    intro h
    rw [div_eq_iff ha] at h
    exact haq (by linarith)
  exact discriminant_formal_square (alpha (mparam a q02))
    (nonresonance_first hm0 hm1 hmnat)
    (nonresonance_second hm1 hmnat)
    v w Δ hv0 hv1 hw0 heig hΔ2

end

end NonintegerWCongruence
