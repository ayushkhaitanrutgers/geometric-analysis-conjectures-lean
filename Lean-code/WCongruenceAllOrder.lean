import Mathlib

/-!
# All-order compatibility of the resonant Taylor equation at an umbilic of a W-congruence

Lean certification of `w_congruence_all_order.tex`.

The paper proves (Theorem 1.1): at a normalized nondegenerate umbilic of parameter
`m = -q₀₂/p₁₁ ∈ ℤ`, `m ≥ 1`, the resonant Taylor equation `W_{m0} = 0` follows from
the jet equations `W_{ij} = 0` of lower total order, so it imposes no extra condition.
The route is: hodograph reduction (`W = 2JE`, `(X-2)Δ = AE`), a finite Poincaré–Dulac
normalization of `X = X₀ + 𝒪(2)`, `X₀ = αA∂_A + B∂_B`, `α = 2/(m+1)`, the killing
identity (eq:killc) removing the only possible nonlinear resonance, and the vanishing
top eigenvalue `α(m+1) - 2 = 0`.

All germs are represented by their finite jets: bivariate real polynomials
`R2 = MvPolynomial (Fin 2) ℝ` with the order filtration `Ord k f` (`f = 𝒪(k)`).
Only jets of finite order enter the paper's argument (see the remark after
Theorem 1.1), so this is a faithful setting for every statement below.

## What is formalized where (tex tags in parentheses)

**Fully proved, no extra hypotheses:**

* `resonance` — **Lemma 3.1** (lem:resonance, the analytic-algebraic heart of the
  paper): if `X = X₀ + 𝒪(2)`, `Δ = B² + 𝒪(3)` and `R = (X-2)Δ = 𝒪(m+1)` (eq:Rorder),
  then the `A^{m+1}`-coefficient of `R` vanishes.  The proof is the paper's, in
  scalar-eigenfunction form: `exists_u`/`exists_v` perform the finite Poincaré–Dulac
  normalization (`sweep`, `step_nonres`, `step_res` are the homological eliminations
  (eq:homA)–(eq:homB); `nonres_al`/`nonres_one_of` are the resonance arithmetic of §3,
  isolating `j = 0`, `2i = m+1`); the `c = 0` step inside `resonance` is exactly
  (eq:killc), obtained from the degree-`(r+1)` coefficient of `R` at `A^r B` using
  `α r = 1`; the final coefficient computation is (eq:Rtop) with `α(m+1) - 2 = 0`.
* `key_identity` — the exact hodograph identity `(X-2)Δ = A·E` (eq:key) of
  **Lemma 2.1**, as a polynomial identity for arbitrary jets `F`, `G`
  (`Eexpr` = (eq:E), `Xa`/`Xb` = (eq:X), `Dexpr` = (eq:Delta)).
* `hodograph_resonant_coefficient` — **Theorem 1.1 in hodograph form** (§4): from the
  normalized leading jets (eq:leadingFG) and `E = 𝒪(m)` (eq:Eord) it deduces
  `[A^m]E_m = 0` (eq:Em).  The derivation of `X = X₀ + 𝒪(2)`, `Δ = B² + 𝒪(3)`
  (eq:leading) from (eq:leadingFG) is part of the proof.
* `Wexpr_eq_det`, `Wexpr_eq_det_hess` — both equalities of (eq:hess), including
  `W = det(Hess(xQ - yP), Hess P, Hess Q)`.
* `Wdelta_identity` — the six-term rearrangement (eq:Wdelta) in the proof of
  Lemma 2.1, cleared of denominators (`4W = …`, with `2B` and `4Δ` in place of `B`,
  `Δ`); Schwarz symmetry enters through `pderiv_pderiv_comm` exactly as in the paper.
* `W00_at_umbilic` — `W(0) = 0` at an umbilic (the vacuous order-0 case of eq:lower).
* `W10_eq` — the identity `W_{10} = 2 q₂₀ a² (1-m)` (eq:W10) for arbitrary germs with
  the normalized 2-jet (eq:norm), and `W10_vanishes_of_m_eq_one` — the `m = 1` case of
  **Theorem 1.1** (end of §4).
* `hodograph_linearization` — the linearizations `A = ax + 𝒪(2)`,
  `2B = (m+1)ay + 𝒪(2)` and the Jacobian value `2J(0) = (m+1)a²` (eq:ABlinear, eq:J).

**Formalized with explicit bridge hypotheses:**

* `allorder_compatibility` — **Theorem 1.1** (thm:main) for `m ≥ 2`, stated for the
  jet family `W_{ij}` with two hypotheses transcribing the hodograph bridge, which
  needs the formal/analytic inverse function theorem not available in Mathlib:
  `hWE` (the equivalence `W = 𝒪(m) ↔ E = 𝒪(m)` from `W = 2JE` (eq:WE) and the fact
  that the hodograph map is a local diffeomorphism with unit Jacobian `J`), and
  `hreturn` (the coefficient translation `W_{m0} = 2J(0)·m!·a^m·[A^m]E_m` (eq:return)).
  Given these, the conclusion `W_{m0} = 0` (eq:target) follows from the fully proved
  hodograph theorem.

**Not formalized:**

* The construction of the hodograph coordinates themselves — inverting
  `(x,y) ↦ (A,B)` and regarding `F`, `G` of (eq:FG) as functions of `(A,B)` — i.e.
  the germ-level content of (eq:WE); it is exactly what the two hypotheses of
  `allorder_compatibility` package.
* Corollary 4.2 (cor:ideal), the universal jet-ring form: the real-jet version of the
  same statement is `allorder_compatibility`; the localized polynomial-ring variant
  is not separately formalized.
-/

namespace WCongruenceAllOrder

open MvPolynomial

/-- The plane of hodograph variables `(A,B)` (or of the original variables `(x,y)`):
bivariate real polynomials, used as the ring of finite jets. -/
abbrev R2 : Type := MvPolynomial (Fin 2) ℝ

/-- The first variable (`A` in hodograph form, `x` in the original chart). -/
noncomputable def va : R2 := X 0

/-- The second variable (`B` in hodograph form, `y` in the original chart). -/
noncomputable def vb : R2 := X 1

/-- Total degree of an exponent vector. -/
def dg (d : Fin 2 →₀ ℕ) : ℕ := d 0 + d 1

/-- `Ord k f`: every coefficient of `f` of total degree `< k` vanishes, i.e. `f = 𝒪(k)`
in the notation of the paper (order of vanishing at the origin at least `k`). -/
def Ord (k : ℕ) (f : R2) : Prop := ∀ d : Fin 2 →₀ ℕ, dg d < k → coeff d f = 0

/-- Extensionality for exponent vectors on two variables. -/
lemma finsupp_fin2_ext {d e : Fin 2 →₀ ℕ} (h0 : d 0 = e 0) (h1 : d 1 = e 1) : d = e := by
  ext a
  fin_cases a
  · exact h0
  · exact h1

lemma dg_add (d e : Fin 2 →₀ ℕ) : dg (d + e) = dg d + dg e := by
  simp [dg, Finsupp.add_apply]; omega

lemma dg_single (i : Fin 2) (c : ℕ) : dg (Finsupp.single i c) = c := by
  fin_cases i <;> simp [dg]

lemma dg_eq_zero {d : Fin 2 →₀ ℕ} (h : dg d = 0) : d = 0 := by
  refine finsupp_fin2_ext ?_ ?_ <;> simp [dg] at h ⊢ <;> omega

/-! ### The `Ord` toolkit -/

lemma Ord.mono {k K : ℕ} {f : R2} (h : Ord K f) (hkK : k ≤ K) : Ord k f :=
  fun d hd => h d (lt_of_lt_of_le hd hkK)

lemma ord_zero (k : ℕ) : Ord k (0 : R2) := fun d _ => coeff_zero d

lemma ord_top (f : R2) : Ord 0 f := fun _ hd => absurd hd (Nat.not_lt_zero _)

lemma Ord.add {k : ℕ} {f g : R2} (hf : Ord k f) (hg : Ord k g) : Ord k (f + g) :=
  fun d hd => by rw [coeff_add, hf d hd, hg d hd, add_zero]

lemma Ord.neg {k : ℕ} {f : R2} (hf : Ord k f) : Ord k (-f) :=
  fun d hd => by rw [coeff_neg, hf d hd, neg_zero]

lemma Ord.sub {k : ℕ} {f g : R2} (hf : Ord k f) (hg : Ord k g) : Ord k (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma Ord.smul {k : ℕ} {f : R2} (c : ℝ) (hf : Ord k f) : Ord k (c • f) :=
  fun d hd => by rw [coeff_smul, hf d hd, smul_zero]

lemma Ord.finsetSum {k : ℕ} {ι : Type*} {s : Finset ι} {F : ι → R2}
    (h : ∀ x ∈ s, Ord k (F x)) : Ord k (∑ x ∈ s, F x) := by
  intro d hd
  rw [coeff_sum]
  exact Finset.sum_eq_zero fun x hx => h x hx d hd

lemma Ord.mul {j k : ℕ} {f g : R2} (hf : Ord j f) (hg : Ord k g) : Ord (j + k) (f * g) := by
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d1, d2⟩ hmem
  rw [Finset.mem_antidiagonal] at hmem
  have hdg : dg d1 + dg d2 = dg d := by rw [← hmem, dg_add]
  rcases lt_or_ge (dg d1) j with h1 | h1
  · rw [hf d1 h1, zero_mul]
  · rw [hg d2 (by omega), mul_zero]

lemma Ord.pow {f : R2} (hf : Ord 1 f) (n : ℕ) : Ord n (f ^ n) := by
  induction n with
  | zero => exact ord_top _
  | succ n ih => rw [pow_succ]; exact ih.mul hf

lemma ord_monomial (d : Fin 2 →₀ ℕ) (c : ℝ) : Ord (dg d) (monomial d c) := by
  intro d' hd'
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact lt_irrefl _ hd'

lemma ord_va : Ord 1 va := by
  intro d hd
  have hd0 : d = 0 := dg_eq_zero (by omega)
  subst hd0
  simp [va]

lemma ord_vb : Ord 1 vb := by
  intro d hd
  have hd0 : d = 0 := dg_eq_zero (by omega)
  subst hd0
  simp [vb]

/-- Coefficient formula for partial derivatives. -/
lemma coeff_pderiv (i : Fin 2) (f : R2) (d : Fin 2 →₀ ℕ) :
    coeff d (pderiv i f) = ((d i : ℝ) + 1) * coeff (d + Finsupp.single i 1) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = d + Finsupp.single i 1
    · subst h
      rw [if_pos (add_tsub_cancel_right _ _), if_pos rfl]
      have hdi : (d + Finsupp.single i 1 : Fin 2 →₀ ℕ) i = d i + 1 := by
        rw [Finsupp.add_apply, Finsupp.single_eq_same]
      rw [hdi]
      push_cast
      ring
    · rw [if_neg h]
      by_cases h2 : s - Finsupp.single i 1 = d
      · rw [if_pos h2]
        have hsi : s i = 0 := by
          by_contra hsi
          apply h
          have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.mpr (by omega)
          rw [← h2, tsub_add_cancel_of_le hle]
        rw [hsi]
        simp
      · rw [if_neg h2, mul_zero]
  | add f g hf hg =>
    rw [map_add, coeff_add, coeff_add, hf, hg]
    ring

lemma Ord.pderiv {k : ℕ} {f : R2} (h : Ord (k + 1) f) (i : Fin 2) : Ord k (pderiv i f) := by
  intro d hd
  rw [coeff_pderiv, h _ (by rw [dg_add, dg_single]; omega), mul_zero]

/-! ### Exponent-pair helpers -/

/-- The exponent vector of the monomial `A^i B^j`. -/
noncomputable def dp (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

@[simp] lemma dp_apply_zero (i j : ℕ) : dp i j 0 = i := by
  simp [dp, Finsupp.add_apply]

@[simp] lemma dp_apply_one (i j : ℕ) : dp i j 1 = j := by
  simp [dp, Finsupp.add_apply]

@[simp] lemma dg_dp (i j : ℕ) : dg (dp i j) = i + j := by simp [dg]

lemma eq_dp (d : Fin 2 →₀ ℕ) : dp (d 0) (d 1) = d :=
  finsupp_fin2_ext (by simp) (by simp)

lemma dp_inj {i j i' j' : ℕ} (h : dp i j = dp i' j') : i = i' ∧ j = j' := by
  constructor
  · have := congrArg (fun d => d 0) h; simpa using this
  · have := congrArg (fun d => d 1) h; simpa using this

lemma va_pow_mul_vb_pow (i j : ℕ) : va ^ i * vb ^ j = monomial (dp i j) 1 := by
  rw [va, vb, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul, dp]

/-! ### Vector fields as derivations

`Der p q f = p ∂_A f + q ∂_B f` is the planar vector field `p ∂_A + q ∂_B` applied to `f`.
The vector field `X` of the paper (eq:X) has this shape. -/

/-- The vector field `p ∂_A + q ∂_B` applied to `f`. -/
noncomputable def Der (p q f : R2) : R2 := p * pderiv 0 f + q * pderiv 1 f

lemma va_def : va = X 0 := rfl
lemma vb_def : vb = X 1 := rfl

lemma X_eq_monomial (i : Fin 2) : (X i : R2) = monomial (Finsupp.single i 1) 1 := by
  rw [← pow_one (X i : R2), X_pow_eq_monomial]

lemma Der_add (p q f g : R2) : Der p q (f + g) = Der p q f + Der p q g := by
  simp only [Der, map_add]; ring

lemma Der_sub (p q f g : R2) : Der p q (f - g) = Der p q f - Der p q g := by
  simp only [Der, map_sub]; ring

lemma Der_smul (p q : R2) (c : ℝ) (f : R2) : Der p q (c • f) = c • Der p q f := by
  rw [Der, Der, Derivation.map_smul, Derivation.map_smul, mul_smul_comm, mul_smul_comm,
    smul_add]

lemma Der_zero (p q : R2) : Der p q 0 = 0 := by simp [Der]

lemma Der_one (p q : R2) : Der p q 1 = 0 := by simp [Der]

lemma Der_sum {ι : Type*} (p q : R2) (s : Finset ι) (F : ι → R2) :
    Der p q (∑ x ∈ s, F x) = ∑ x ∈ s, Der p q (F x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Der_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Der_add, ih]

/-- Leibniz rule. -/
lemma Der_mul (p q f g : R2) : Der p q (f * g) = Der p q f * g + f * Der p q g := by
  simp only [Der, pderiv_mul]; ring

/-- Power rule (with the `n = 0` convention `0 • ⋯ = 0`). -/
lemma Der_pow (p q u : R2) (n : ℕ) :
    Der p q (u ^ n) = (n : ℝ) • (u ^ (n - 1) * Der p q u) := by
  induction n with
  | zero => simp [Der_one]
  | succ n ih =>
    rw [pow_succ, Der_mul, ih]
    cases n with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [smul_mul_assoc]
      have h1 : u ^ k * Der p q u * u = u ^ (k + 1) * Der p q u := by ring
      rw [h1]
      push_cast
      module

/-- A vector field whose coefficients vanish to order `c+1` raises the order of
vanishing by `c`. -/
lemma Ord.der {c k : ℕ} {p q f : R2} (hp : Ord (c + 1) p) (hq : Ord (c + 1) q)
    (hf : Ord k f) : Ord (k + c) (Der p q f) := by
  show Ord (k + c) (p * MvPolynomial.pderiv 0 f + q * MvPolynomial.pderiv 1 f)
  cases k with
  | zero =>
    have h1 := hp.mul (ord_top (MvPolynomial.pderiv 0 f))
    have h2 := hq.mul (ord_top (MvPolynomial.pderiv 1 f))
    exact (h1.mono (by omega)).add (h2.mono (by omega))
  | succ k =>
    have h1 := hp.mul (hf.pderiv 0)
    have h2 := hq.mul (hf.pderiv 1)
    exact (h1.mono (by omega)).add (h2.mono (by omega))

lemma va_mul_pderiv_monomial (d : Fin 2 →₀ ℕ) (c : ℝ) :
    va * pderiv 0 (monomial d c) = monomial d (c * d 0) := by
  rw [pderiv_monomial]
  rcases Nat.eq_zero_or_pos (d 0) with h0 | h0
  · rw [h0]
    simp
  · rw [va_def, X_eq_monomial, monomial_mul, one_mul,
      add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr h0)]

lemma vb_mul_pderiv_monomial (d : Fin 2 →₀ ℕ) (c : ℝ) :
    vb * pderiv 1 (monomial d c) = monomial d (c * d 1) := by
  rw [pderiv_monomial]
  rcases Nat.eq_zero_or_pos (d 1) with h0 | h0
  · rw [h0]
    simp
  · rw [vb_def, X_eq_monomial, monomial_mul, one_mul,
      add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr h0)]

/-- The diagonal action of the linear vector field `X₀ = α A ∂_A + B ∂_B` on monomials:
`X₀ (A^i B^j) = (α i + j) A^i B^j`, plus the higher-order perturbation.  This encodes the
homological eigenvalues (eq:homA)–(eq:homB) at the level of scalar functions. -/
lemma der_monomial (α : ℝ) (p' q' : R2) (d : Fin 2 →₀ ℕ) (c : ℝ) :
    Der (α • va + p') (vb + q') (monomial d c)
      = monomial d (c * (α * d 0 + d 1)) + Der p' q' (monomial d c) := by
  have h1 : α • monomial d (c * (d 0 : ℝ)) + monomial d (c * (d 1 : ℝ))
      = monomial d (c * (α * d 0 + d 1)) := by
    rw [smul_monomial, smul_eq_mul, ← map_add]
    congr 1
    ring
  show (α • va + p') * pderiv 0 (monomial d c) + (vb + q') * pderiv 1 (monomial d c)
      = monomial d (c * (α * (d 0 : ℝ) + (d 1 : ℝ)))
        + (p' * pderiv 0 (monomial d c) + q' * pderiv 1 (monomial d c))
  rw [add_mul, add_mul, smul_mul_assoc, va_mul_pderiv_monomial, vb_mul_pderiv_monomial,
    ← h1]
  abel

/-- Schwarz: partial derivatives of polynomials commute. -/
lemma pderiv_pderiv_comm (i j : Fin 2) (f : R2) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · induction f using MvPolynomial.induction_on' with
    | monomial s c =>
      rw [pderiv_monomial, pderiv_monomial, pderiv_monomial, pderiv_monomial]
      have e1 : s - Finsupp.single j 1 - Finsupp.single i 1
          = s - Finsupp.single i 1 - Finsupp.single j 1 := tsub_right_comm
      have e2 : (s - Finsupp.single j 1 : Fin 2 →₀ ℕ) i = s i := by
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hij), tsub_zero]
      have e3 : (s - Finsupp.single i 1 : Fin 2 →₀ ℕ) j = s j := by
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hij, tsub_zero]
      rw [e1, e2, e3]
      congr 1
      ring
    | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]

/-! ### Order comparison of powers of perturbed coordinates -/

lemma ord_one_of_sub_va {u : R2} (hu : Ord 2 (u - va)) : Ord 1 u := by
  have h := (hu.mono (by omega)).add ord_va
  simpa using h

lemma ord_one_of_sub_vb {v : R2} (hv : Ord 2 (v - vb)) : Ord 1 v := by
  have h := (hv.mono (by omega)).add ord_vb
  simpa using h

lemma Ord.pow_sub {u g : R2} (hu : Ord 1 u) (hg : Ord 1 g) (hd : Ord 2 (u - g)) (n : ℕ) :
    Ord (n + 1) (u ^ n - g ^ n) := by
  induction n with
  | zero => simpa using ord_zero 1
  | succ n ih =>
    have key : u ^ (n + 1) - g ^ (n + 1) = u ^ n * (u - g) + (u ^ n - g ^ n) * g := by ring
    rw [key]
    have h1 : Ord (n + 2) (u ^ n * (u - g)) := (hu.pow n).mul hd
    have h2 := ih.mul hg
    exact (h1.mono (by omega)).add (h2.mono (by omega))

/-- `u^i v^j` agrees with the monomial `A^i B^j` to order `i + j`. -/
lemma ord_prodpow_sub {u v : R2} (hu : Ord 2 (u - va)) (hv : Ord 2 (v - vb)) (i j : ℕ) :
    Ord (i + j + 1) (u ^ i * v ^ j - va ^ i * vb ^ j) := by
  have hu1 : Ord 1 u := ord_one_of_sub_va hu
  have hv1 : Ord 1 v := ord_one_of_sub_vb hv
  have key : u ^ i * v ^ j - va ^ i * vb ^ j
      = u ^ i * (v ^ j - vb ^ j) + (u ^ i - va ^ i) * vb ^ j := by ring
  rw [key]
  have h1 := (hu1.pow i).mul (hv1.pow_sub ord_vb hv j)
  have h2 := (hu1.pow_sub ord_va hu i).mul (ord_vb.pow j)
  exact (h1.mono (by omega)).add (h2.mono (by omega))

/-! ### The homological elimination step

At a fixed total degree `k`, the operator `f ↦ X₀ f - λ f` acts diagonally on monomials
with eigenvalue `α i + j - λ` (the scalar counterpart of (eq:homA)–(eq:homB)).  When no
eigenvalue vanishes on the relevant monomials, all degree-`k` coefficients of an error
term can be removed by adding a homogeneous correction `w`. -/

lemma coeff_sum_monomial (s : Finset (Fin 2 →₀ ℕ)) (g : (Fin 2 →₀ ℕ) → ℝ)
    (d' : Fin 2 →₀ ℕ) :
    coeff d' (∑ d ∈ s, monomial d (g d)) = if d' ∈ s then g d' else 0 := by
  classical
  rw [coeff_sum,
    Finset.sum_congr rfl (fun d _ => coeff_monomial d' d (g d)),
    Finset.sum_ite_eq' s d' g]

/-- Core elimination: remove the coefficients of `f` indexed by a set `s` of
degree-`k` exponents on which the eigenvalue `α i + j - λ` does not vanish. -/
lemma step_core (α lam : ℝ) {p' q' : R2} (hp' : Ord 2 p') (hq' : Ord 2 q')
    (k : ℕ) (f : R2) (s : Finset (Fin 2 →₀ ℕ)) (hs : ∀ d ∈ s, dg d = k)
    (hnr : ∀ d ∈ s, α * (d 0 : ℝ) + (d 1 : ℝ) ≠ lam) :
    ∃ w : R2, Ord k w ∧
      Ord (k + 1) (Der (α • va + p') (vb + q') w - lam • w
        + ∑ d ∈ s, monomial d (coeff d f)) := by
  classical
  refine ⟨∑ d ∈ s, monomial d (-(coeff d f) / (α * (d 0 : ℝ) + (d 1 : ℝ) - lam)), ?_, ?_⟩
  · exact Ord.finsetSum fun d hd =>
      (ord_monomial d _).mono (le_of_eq (hs d hd).symm)
  · rw [Der_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Ord.finsetSum
    intro d hd
    have hlam : (α * (d 0 : ℝ) + (d 1 : ℝ)) - lam ≠ 0 := sub_ne_zero.mpr (hnr d hd)
    set γ : ℝ := -(coeff d f) / (α * (d 0 : ℝ) + (d 1 : ℝ) - lam) with hγ
    have hcancel : γ * ((α * (d 0 : ℝ) + (d 1 : ℝ)) - lam) = -(coeff d f) := by
      rw [hγ, div_mul_cancel₀ _ hlam]
    have hc : γ * (α * (d 0 : ℝ) + (d 1 : ℝ)) - lam * γ + coeff d f = 0 := by
      linear_combination hcancel
    rw [der_monomial]
    have hmon : monomial d (γ * (α * (d 0 : ℝ) + (d 1 : ℝ))) - lam • monomial d γ
        + monomial d (coeff d f) = 0 := by
      rw [smul_monomial, smul_eq_mul, ← map_sub, ← map_add, hc, map_zero]
    have hsplit : monomial d (γ * (α * (d 0 : ℝ) + (d 1 : ℝ))) + Der p' q' (monomial d γ)
          - lam • monomial d γ + monomial d (coeff d f)
        = Der p' q' (monomial d γ)
          + (monomial d (γ * (α * (d 0 : ℝ) + (d 1 : ℝ))) - lam • monomial d γ
            + monomial d (coeff d f)) := by
      abel
    rw [hsplit, hmon, add_zero]
    exact Ord.der (c := 1) hp' hq' ((ord_monomial d γ).mono (le_of_eq (hs d hd).symm))

/-- Nonresonant step: if no eigenvalue vanishes in degree `k`, an error of order `k`
can be pushed to order `k + 1` by a degree-`k` correction. -/
lemma step_nonres (α lam : ℝ) {p' q' : R2} (hp' : Ord 2 p') (hq' : Ord 2 q')
    (k : ℕ) {f : R2} (hf : Ord k f)
    (hnr : ∀ d : Fin 2 →₀ ℕ, dg d = k → α * (d 0 : ℝ) + (d 1 : ℝ) ≠ lam) :
    ∃ w : R2, Ord k w ∧
      Ord (k + 1) (f + (Der (α • va + p') (vb + q') w - lam • w)) := by
  classical
  obtain ⟨w, hw, hstep⟩ := step_core α lam hp' hq' k f
    (f.support.filter fun d => dg d = k)
    (fun d hd => (Finset.mem_filter.mp hd).2)
    (fun d hd => hnr d (Finset.mem_filter.mp hd).2)
  refine ⟨w, hw, ?_⟩
  have hrest : Ord (k + 1)
      (f - ∑ d ∈ f.support.filter (fun d => dg d = k), monomial d (coeff d f)) := by
    intro d' hd'
    rw [coeff_sub, coeff_sum_monomial]
    by_cases hmem : d' ∈ f.support.filter fun d => dg d = k
    · rw [if_pos hmem, sub_self]
    · rw [if_neg hmem, sub_zero]
      rcases Nat.lt_or_ge (dg d') k with h | h
      · exact hf d' h
      · have hdk : dg d' = k := by omega
        by_contra hne
        exact hmem (Finset.mem_filter.mpr ⟨mem_support_iff.mpr hne, hdk⟩)
  have heq : f + (Der (α • va + p') (vb + q') w - lam • w)
      = (Der (α • va + p') (vb + q') w - lam • w
          + ∑ d ∈ f.support.filter (fun d => dg d = k), monomial d (coeff d f))
        + (f - ∑ d ∈ f.support.filter (fun d => dg d = k), monomial d (coeff d f)) := by
    abel
  rw [heq]
  exact hstep.add hrest

/-- Resonant step at the single exceptional exponent `ρ`: all degree-`k` coefficients
except the resonant one can be removed; the resonant monomial survives untouched. -/
lemma step_res (α lam : ℝ) {p' q' : R2} (hp' : Ord 2 p') (hq' : Ord 2 q')
    (k : ℕ) {f : R2} (hf : Ord k f) (ρ : Fin 2 →₀ ℕ) (hρ : dg ρ = k)
    (hnr : ∀ d : Fin 2 →₀ ℕ, dg d = k → d ≠ ρ → α * (d 0 : ℝ) + (d 1 : ℝ) ≠ lam) :
    ∃ w : R2, Ord k w ∧
      Ord (k + 1) (f + (Der (α • va + p') (vb + q') w - lam • w)
        - monomial ρ (coeff ρ f)) := by
  classical
  obtain ⟨w, hw, hstep⟩ := step_core α lam hp' hq' k f
    (f.support.filter fun d => dg d = k ∧ d ≠ ρ)
    (fun d hd => (Finset.mem_filter.mp hd).2.1)
    (fun d hd => hnr d (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp hd).2.2)
  refine ⟨w, hw, ?_⟩
  have hrest : Ord (k + 1)
      (f - ∑ d ∈ f.support.filter (fun d => dg d = k ∧ d ≠ ρ), monomial d (coeff d f)
        - monomial ρ (coeff ρ f)) := by
    intro d' hd'
    rw [coeff_sub, coeff_sub, coeff_sum_monomial, coeff_monomial]
    by_cases hdρ : d' = ρ
    · subst hdρ
      have hnotmem : d' ∉ f.support.filter fun d => dg d = k ∧ d ≠ d' := by
        intro h
        exact (Finset.mem_filter.mp h).2.2 rfl
      rw [if_neg hnotmem, if_pos rfl, sub_zero, sub_self]
    · have hρd' : ¬(ρ = d') := fun h => hdρ h.symm
      rw [if_neg hρd', sub_zero]
      by_cases hmem : d' ∈ f.support.filter fun d => dg d = k ∧ d ≠ ρ
      · rw [if_pos hmem, sub_self]
      · rw [if_neg hmem, sub_zero]
        rcases Nat.lt_or_ge (dg d') k with h | h
        · exact hf d' h
        · have hdk : dg d' = k := by omega
          by_contra hne
          exact hmem (Finset.mem_filter.mpr ⟨mem_support_iff.mpr hne, hdk, hdρ⟩)
  have heq : f + (Der (α • va + p') (vb + q') w - lam • w) - monomial ρ (coeff ρ f)
      = (Der (α • va + p') (vb + q') w - lam • w
          + ∑ d ∈ f.support.filter (fun d => dg d = k ∧ d ≠ ρ), monomial d (coeff d f))
        + (f - ∑ d ∈ f.support.filter (fun d => dg d = k ∧ d ≠ ρ),
            monomial d (coeff d f) - monomial ρ (coeff ρ f)) := by
    abel
  rw [heq]
  exact hstep.add hrest

/-- Finite nonresonant normalization sweep: iterate `step_nonres` from degree `K - j`
up to degree `K`.  Only finitely many homogeneous corrections are used, exactly as in
the paper ("no convergence question arises"). -/
lemma sweep (α lam : ℝ) {p' q' : R2} (hp' : Ord 2 p') (hq' : Ord 2 q')
    (K kmin : ℕ) (hkmin : 1 ≤ kmin)
    (hnr : ∀ d : Fin 2 →₀ ℕ, kmin ≤ dg d → dg d < K → α * (d 0 : ℝ) + (d 1 : ℝ) ≠ lam) :
    ∀ j : ℕ, ∀ f : R2, kmin ≤ K - j → Ord (K - j) f →
      ∃ w : R2, Ord kmin w ∧
        Ord K (f + (Der (α • va + p') (vb + q') w - lam • w)) := by
  intro j
  induction j with
  | zero =>
    intro f _ hf
    refine ⟨0, ord_zero _, ?_⟩
    simpa [Der_zero] using hf
  | succ j ih =>
    intro f hk hf
    have hK : j + 2 ≤ K := by omega
    obtain ⟨w₁, hw₁, hf₁⟩ := step_nonres α lam hp' hq' (K - (j + 1)) hf
      (fun d hd => hnr d (by omega) (by omega))
    have hstep : Ord (K - j) (f + (Der (α • va + p') (vb + q') w₁ - lam • w₁)) := by
      have hj : K - (j + 1) + 1 = K - j := by omega
      rwa [hj] at hf₁
    obtain ⟨w₂, hw₂, hf₂⟩ := ih _ (by omega) hstep
    refine ⟨w₁ + w₂, (hw₁.mono hk).add hw₂, ?_⟩
    have heq : f + (Der (α • va + p') (vb + q') (w₁ + w₂) - lam • (w₁ + w₂))
        = (f + (Der (α • va + p') (vb + q') w₁ - lam • w₁))
          + (Der (α • va + p') (vb + q') w₂ - lam • w₂) := by
      rw [Der_add, smul_add]
      abel
    rw [heq]
    exact hf₂

/-! ### The eigenvalue `α = 2/(m+1)` and the resonance arithmetic

(eq:leading): `X₀ = α A ∂_A + B ∂_B` with `α = 2/(m+1)`.  The scalar homological
eigenvalues are `α i + j - λ`; the paper's resonance analysis (§3) shows the only
possible vanishing for `λ = 1` in degree `≥ 2` is at `j = 0`, `i = r = (m+1)/2`. -/

/-- `α = 2/(m+1)` (eq:leading). -/
noncomputable def al (m : ℕ) : ℝ := 2 / (m + 1)

lemma al_pos (m : ℕ) : 0 < al m := by
  rw [al]
  positivity

lemma al_lt_one {m : ℕ} (hm : 2 ≤ m) : al m < 1 := by
  rw [al, div_lt_one (by positivity)]
  have h : (2 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

lemma al_mul_eq_one_iff (m i : ℕ) : al m * i = 1 ↔ 2 * i = m + 1 := by
  rw [al, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity : ((m : ℝ) + 1) ≠ 0)]
  constructor <;> intro h <;> exact_mod_cast h

lemma al_mul_succ (m : ℕ) : al m * ((m : ℝ) + 1) = 2 := by
  rw [al, div_mul_cancel₀]
  positivity

/-- No `∂_A`-type scalar resonance: `α i + j ≠ α` in degrees `≥ 2` (cf. eq:homA). -/
lemma nonres_al {m : ℕ} (hm : 2 ≤ m) (d : Fin 2 →₀ ℕ) (h2 : 2 ≤ dg d) :
    al m * (d 0 : ℝ) + (d 1 : ℝ) ≠ al m := by
  intro heq
  have h0 := al_pos m
  have h1 := al_lt_one hm
  have hdg : dg d = d 0 + d 1 := rfl
  rcases Nat.eq_zero_or_pos (d 0) with hz | hpos
  · have hj : 2 ≤ d 1 := by omega
    have hjr : (2 : ℝ) ≤ (d 1 : ℝ) := by exact_mod_cast hj
    rw [hz] at heq
    push_cast at heq
    linarith
  · rcases Nat.eq_zero_or_pos (d 1) with hz1 | hpos1
    · have hi : 2 ≤ d 0 := by omega
      have hir : (2 : ℝ) ≤ (d 0 : ℝ) := by exact_mod_cast hi
      rw [hz1] at heq
      push_cast at heq
      nlinarith
    · have hir : (1 : ℝ) ≤ (d 0 : ℝ) := by exact_mod_cast hpos
      have hjr : (1 : ℝ) ≤ (d 1 : ℝ) := by exact_mod_cast hpos1
      nlinarith

/-- The `∂_B`-type scalar eigenvalue `α i + j - 1` can vanish in degree `≥ 2` only when
`j = 0` and `2 i = m + 1` (cf. eq:homB and the resonance analysis of §3). -/
lemma nonres_one_of {m : ℕ} (hm : 2 ≤ m) (d : Fin 2 →₀ ℕ) (h2 : 2 ≤ dg d)
    (hne : ¬(d 1 = 0 ∧ 2 * d 0 = m + 1)) : al m * (d 0 : ℝ) + (d 1 : ℝ) ≠ 1 := by
  intro heq
  have h0 := al_pos m
  have h1 := al_lt_one hm
  have hdg : dg d = d 0 + d 1 := rfl
  rcases Nat.eq_zero_or_pos (d 1) with hz | hpos
  · rw [hz] at heq
    push_cast at heq
    have hmul : al m * (d 0 : ℝ) = 1 := by linarith
    exact hne ⟨hz, (al_mul_eq_one_iff m (d 0)).mp hmul⟩
  · rcases Nat.lt_or_ge (d 1) 2 with hlt | hge
    · have hd1 : d 1 = 1 := by omega
      rw [hd1] at heq
      push_cast at heq
      have hmul : al m * (d 0 : ℝ) = 0 := by linarith
      have hd0 : (d 0 : ℝ) = 0 := by
        rcases mul_eq_zero.mp hmul with h | h
        · exact absurd h (ne_of_gt h0)
        · exact h
      have hd0' : d 0 = 0 := by exact_mod_cast hd0
      omega
    · have hjr : (2 : ℝ) ≤ (d 1 : ℝ) := by exact_mod_cast hge
      have hnn : (0 : ℝ) ≤ al m * (d 0 : ℝ) := by positivity
      linarith

/-! ### Construction of the eigenfunctions `u` and `v`

This is the finite Poincaré–Dulac normalization of the paper (proof of Lemma 3.1),
performed at the level of scalar eigenfunctions: instead of normalizing the vector
field `X` itself, we build polynomials `u = A + 𝒪(2)`, `v = B + 𝒪(2)` with
`X u = α u + 𝒪(m+1)` and `X v = v + c u^r + 𝒪(m+1)`, where the single possibly
resonant term `c u^r` (present only for odd `m`, `r = (m+1)/2`) corresponds to the
resonant vector-field term `c A^r ∂_B` of the paper. -/

lemma exists_u {m : ℕ} (hm : 2 ≤ m) {p' q' : R2} (hp' : Ord 2 p') (hq' : Ord 2 q') :
    ∃ u : R2, Ord 2 (u - va) ∧
      Ord (m + 1) (Der (al m • va + p') (vb + q') u - al m • u) := by
  have hXva : Der (al m • va + p') (vb + q') va = al m • va + p' := by
    show (al m • va + p') * MvPolynomial.pderiv 0 va
        + (vb + q') * MvPolynomial.pderiv 1 va = _
    rw [va_def, pderiv_X_self, pderiv_X_of_ne (by decide), mul_one, mul_zero, add_zero]
  obtain ⟨w, hw, hfin⟩ := sweep (al m) (al m) hp' hq' (m + 1) 2 (by omega)
    (fun d h2 _ => nonres_al hm d h2) (m + 1 - 2) p' (by omega) (by
      have h : m + 1 - (m + 1 - 2) = 2 := by omega
      rw [h]; exact hp')
  refine ⟨va + w, by simpa using hw, ?_⟩
  have heq : Der (al m • va + p') (vb + q') (va + w) - al m • (va + w)
      = p' + (Der (al m • va + p') (vb + q') w - al m • w) := by
    rw [Der_add, hXva, smul_add]
    abel
  rw [heq]
  exact hfin

lemma exists_v {m : ℕ} (hm : 2 ≤ m) {p' q' : R2} (hp' : Ord 2 p') (hq' : Ord 2 q')
    {u : R2} (hu : Ord 2 (u - va)) :
    ∃ (v : R2) (c : ℝ) (r : ℕ), Ord 2 (v - vb) ∧
      Ord (m + 1) (Der (al m • va + p') (vb + q') v - v - c • u ^ r) ∧
      (c = 0 ∨ (2 * r = m + 1 ∧ 2 ≤ r)) := by
  have hXvb : Der (al m • va + p') (vb + q') vb = vb + q' := by
    show (al m • va + p') * MvPolynomial.pderiv 0 vb
        + (vb + q') * MvPolynomial.pderiv 1 vb = _
    rw [vb_def, pderiv_X_self, pderiv_X_of_ne (by decide), mul_zero, mul_one, zero_add]
  rcases Nat.even_or_odd m with hme | hmo
  · -- even `m`: no resonance at all (2 i = m + 1 is impossible), full sweep, `c = 0`
    obtain ⟨t, ht⟩ := hme
    have hnr : ∀ d : Fin 2 →₀ ℕ, 2 ≤ dg d → dg d < m + 1 →
        al m * (d 0 : ℝ) + (d 1 : ℝ) ≠ 1 := by
      intro d h2 _
      exact nonres_one_of hm d h2 (by rintro ⟨-, h2d⟩; omega)
    obtain ⟨w, hw, hfin⟩ := sweep (al m) 1 hp' hq' (m + 1) 2 (by omega) hnr
      (m + 1 - 2) q' (by omega) (by
        have h : m + 1 - (m + 1 - 2) = 2 := by omega
        rw [h]; exact hq')
    rw [one_smul] at hfin
    refine ⟨vb + w, 0, 0, by simpa using hw, ?_, Or.inl rfl⟩
    have heq : Der (al m • va + p') (vb + q') (vb + w) - (vb + w) - (0 : ℝ) • u ^ 0
        = q' + (Der (al m • va + p') (vb + q') w - w) := by
      rw [Der_add, hXvb, zero_smul, sub_zero]
      abel
    rw [heq]
    exact hfin
  · -- odd `m`: sweep to degree `r`, isolate the resonant coefficient `c`, sweep on
    obtain ⟨t, ht⟩ := hmo
    have hr2 : 2 ≤ t + 1 := by omega
    have h2r : 2 * (t + 1) = m + 1 := by omega
    set r := t + 1 with hrdef
    -- Phase a: nonresonant sweep from degree 2 up to degree r
    have hnra : ∀ d : Fin 2 →₀ ℕ, 2 ≤ dg d → dg d < r →
        al m * (d 0 : ℝ) + (d 1 : ℝ) ≠ 1 := by
      intro d h2 hlt
      refine nonres_one_of hm d h2 ?_
      rintro ⟨h1, h2d⟩
      have hdg : dg d = d 0 + d 1 := rfl
      omega
    obtain ⟨w₁, hw₁, hph1⟩ := sweep (al m) 1 hp' hq' r 2 (by omega) hnra
      (r - 2) q' (by omega) (by
        have h : r - (r - 2) = 2 := by omega
        rw [h]; exact hq')
    rw [one_smul] at hph1
    set g := q' + (Der (al m • va + p') (vb + q') w₁ - w₁) with hgdef
    -- Phase b: the resonant degree r; only the exponent (r, 0) can resist (eq:homB)
    have hnrb : ∀ d : Fin 2 →₀ ℕ, dg d = r → d ≠ dp r 0 →
        al m * (d 0 : ℝ) + (d 1 : ℝ) ≠ 1 := by
      intro d hdr hne
      refine nonres_one_of hm d (by omega) ?_
      rintro ⟨h1, h2d⟩
      apply hne
      have hdg : dg d = d 0 + d 1 := rfl
      have hd0 : d 0 = r := by omega
      rw [← eq_dp d, hd0, h1]
    obtain ⟨w₂, hw₂, hph2⟩ := step_res (al m) 1 hp' hq' r hph1 (dp r 0) (by simp) hnrb
    rw [one_smul] at hph2
    set c := coeff (dp r 0) g with hcdef
    have hmon : (monomial (dp r 0)) c = c • va ^ r := by
      have h := va_pow_mul_vb_pow r 0
      rw [pow_zero, mul_one] at h
      rw [h, smul_monomial, smul_eq_mul, mul_one]
    -- The error of `v₂ = vb + w₁ + w₂` relative to the target `v + c • u^r`
    have hord2 : Ord (r + 1)
        (Der (al m • va + p') (vb + q') (vb + w₁ + w₂) - (vb + w₁ + w₂) - c • u ^ r) := by
      have hdiff : Ord (r + 1) ((monomial (dp r 0)) c - c • u ^ r) := by
        rw [hmon]
        have hpow := ((ord_one_of_sub_va hu).pow_sub ord_va hu r).smul c
        have heq : c • va ^ r - c • u ^ r = -(c • (u ^ r - va ^ r)) := by
          rw [smul_sub]
          abel
        rw [heq]
        exact hpow.neg
      have heq2 : Der (al m • va + p') (vb + q') (vb + w₁ + w₂) - (vb + w₁ + w₂) - c • u ^ r
          = (g + (Der (al m • va + p') (vb + q') w₂ - w₂) - (monomial (dp r 0)) c)
            + ((monomial (dp r 0)) c - c • u ^ r) := by
        rw [Der_add, Der_add, hXvb, hgdef]
        abel
      rw [heq2]
      exact hph2.add hdiff
    -- Phase c: nonresonant sweep from degree r + 1 up to degree m + 1
    have hnrc : ∀ d : Fin 2 →₀ ℕ, r + 1 ≤ dg d → dg d < m + 1 →
        al m * (d 0 : ℝ) + (d 1 : ℝ) ≠ 1 := by
      intro d hge _
      refine nonres_one_of hm d (by omega) ?_
      rintro ⟨h1, h2d⟩
      have hdg : dg d = d 0 + d 1 := rfl
      omega
    obtain ⟨w₃, hw₃, hph3⟩ := sweep (al m) 1 hp' hq' (m + 1) (r + 1) (by omega) hnrc
      (m + 1 - (r + 1))
      (Der (al m • va + p') (vb + q') (vb + w₁ + w₂) - (vb + w₁ + w₂) - c • u ^ r)
      (by omega) (by
        have h : m + 1 - (m + 1 - (r + 1)) = r + 1 := by omega
        rw [h]; exact hord2)
    rw [one_smul] at hph3
    refine ⟨vb + w₁ + w₂ + w₃, c, r, ?_, ?_, Or.inr ⟨h2r, hr2⟩⟩
    · have heq : vb + w₁ + w₂ + w₃ - vb = w₁ + w₂ + w₃ := by abel
      rw [heq]
      exact (hw₁.add (hw₂.mono hr2)).add (hw₃.mono (by omega))
    · have heqf : Der (al m • va + p') (vb + q') (vb + w₁ + w₂ + w₃)
            - (vb + w₁ + w₂ + w₃) - c • u ^ r
          = (Der (al m • va + p') (vb + q') (vb + w₁ + w₂) - (vb + w₁ + w₂) - c • u ^ r)
            + (Der (al m • va + p') (vb + q') w₃ - w₃) := by
        rw [Der_add]
        abel
      rw [heqf]
      exact hph3

/-! ### Expansion in the basis `u^i v^j`

Since `u = A + 𝒪(2)` and `v = B + 𝒪(2)`, the products `u^i v^j` are triangular with
respect to the degree filtration; every germ of order `≥ k₀` can be expanded as a finite
combination of them modulo any fixed order.  These lemmas replace the coordinate change
`Φ` of the paper's proof of Lemma 3.1: they let us read coefficients "in the normalized
coordinates" without composing power series. -/

/-- Finite combination `∑ e_{ij} u^i v^j` over `0 ≤ i, j < N`. -/
noncomputable def Sm (N : ℕ) (u v : R2) (e : ℕ × ℕ → ℝ) : R2 :=
  ∑ p ∈ Finset.range N ×ˢ Finset.range N, e p • (u ^ p.1 * v ^ p.2)

/-- Coefficient extraction from `Sm`: if `e` vanishes below the degree of `d`, then the
`d`-coefficient of `∑ e_{ij} u^i v^j` is exactly `e (d 0, d 1)`. -/
lemma coeff_Sm (N : ℕ) {u v : R2} (hu : Ord 2 (u - va)) (hv : Ord 2 (v - vb))
    (e : ℕ × ℕ → ℝ) (d : Fin 2 →₀ ℕ) (hd0 : d 0 < N) (hd1 : d 1 < N)
    (hlow : ∀ p : ℕ × ℕ, p.1 + p.2 < dg d → e p = 0) :
    coeff d (Sm N u v e) = e (d 0, d 1) := by
  classical
  have hu1 := ord_one_of_sub_va hu
  have hv1 := ord_one_of_sub_vb hv
  have hdd : dg d = d 0 + d 1 := rfl
  have hmem : (d 0, d 1) ∈ Finset.range N ×ˢ Finset.range N :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hd0, Finset.mem_range.mpr hd1⟩
  have hoff : ∀ b ∈ Finset.range N ×ˢ Finset.range N, b ≠ (d 0, d 1) →
      coeff d (e b • (u ^ b.1 * v ^ b.2)) = 0 := by
    rintro ⟨i, j⟩ - hne
    rw [coeff_smul, smul_eq_mul]
    rcases Nat.lt_trichotomy (i + j) (dg d) with hlt | heq | hgt
    · rw [hlow (i, j) hlt, zero_mul]
    · have hdiff := ord_prodpow_sub hu hv i j
      have hcv : coeff d (u ^ i * v ^ j) = 0 := by
        have hsplit : u ^ i * v ^ j
            = (u ^ i * v ^ j - va ^ i * vb ^ j) + va ^ i * vb ^ j := by ring
        rw [hsplit, coeff_add, hdiff d (by omega), zero_add, va_pow_mul_vb_pow,
          coeff_monomial, if_neg]
        intro hdp
        apply hne
        have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) hdp
        have h1 := congrArg (fun z : Fin 2 →₀ ℕ => z 1) hdp
        simp only [dp_apply_zero, dp_apply_one] at h0 h1
        simp [h0, h1]
      rw [hcv, mul_zero]
    · have hcv : coeff d (u ^ i * v ^ j) = 0 := by
        have hord := (hu1.pow i).mul (hv1.pow j)
        exact hord d (by omega)
      rw [hcv, mul_zero]
  have hcv : coeff d (u ^ d 0 * v ^ d 1) = 1 := by
    have hdiff := ord_prodpow_sub hu hv (d 0) (d 1)
    have hsplit : u ^ d 0 * v ^ d 1
        = (u ^ d 0 * v ^ d 1 - va ^ d 0 * vb ^ d 1) + va ^ d 0 * vb ^ d 1 := by ring
    rw [hsplit, coeff_add, hdiff d (by omega), zero_add, va_pow_mul_vb_pow,
      coeff_monomial, if_pos (eq_dp d)]
  rw [Sm, coeff_sum, Finset.sum_eq_single_of_mem _ hmem hoff, coeff_smul, smul_eq_mul,
    hcv, mul_one]

/-- Triangularity: if a finite combination `∑ e_{ij} u^i v^j` vanishes to order `K`,
then all its coefficients of total degree `< K` vanish. -/
lemma ext_vanish (N : ℕ) {u v : R2} (hu : Ord 2 (u - va)) (hv : Ord 2 (v - vb))
    (e : ℕ × ℕ → ℝ) (K : ℕ)
    (hsupp : ∀ p : ℕ × ℕ, N ≤ p.1 ∨ N ≤ p.2 → e p = 0)
    (hg : Ord K (Sm N u v e)) :
    ∀ p : ℕ × ℕ, p.1 + p.2 < K → e p = 0 := by
  suffices h : ∀ n : ℕ, n < K → ∀ p : ℕ × ℕ, p.1 + p.2 = n → e p = 0 by
    intro p hp
    exact h _ hp p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnK p hpn
    by_cases hp1 : N ≤ p.1
    · exact hsupp p (Or.inl hp1)
    by_cases hp2 : N ≤ p.2
    · exact hsupp p (Or.inr hp2)
    have hcoeff := coeff_Sm N hu hv e (dp p.1 p.2)
      (by simp only [dp_apply_zero]; omega) (by simp only [dp_apply_one]; omega)
      (fun q hq => by
        simp only [dg_dp] at hq
        exact ih (q.1 + q.2) (by omega) (by omega) q rfl)
    have hzero := hg (dp p.1 p.2) (by simp only [dg_dp]; omega)
    rw [hcoeff] at hzero
    simpa using hzero

/-- Expansion lemma: every polynomial of order `≥ k₀` agrees, modulo order `K ≤ N`,
with a finite combination `∑ e_{ij} u^i v^j` supported in degrees `k₀ ≤ i + j < K`. -/
lemma expand (N : ℕ) {u v : R2} (hu : Ord 2 (u - va)) (hv : Ord 2 (v - vb)) (k₀ : ℕ) :
    ∀ K : ℕ, K ≤ N → ∀ f : R2, Ord k₀ f →
      ∃ e : ℕ × ℕ → ℝ,
        (∀ p : ℕ × ℕ, p.1 + p.2 < k₀ ∨ K ≤ p.1 + p.2 ∨ N ≤ p.1 ∨ N ≤ p.2 → e p = 0) ∧
        Ord K (f - Sm N u v e) := by
  intro K
  induction K with
  | zero =>
    intro _ f _
    refine ⟨fun _ => 0, fun p _ => rfl, ?_⟩
    have hSm0 : Sm N u v (fun _ => 0) = 0 := by simp [Sm]
    rw [hSm0, sub_zero]
    exact ord_top f
  | succ K ihK =>
    intro hKN f hf
    obtain ⟨e, hesupp, hOrd⟩ := ihK (by omega) f hf
    by_cases hk₀ : K < k₀
    · -- still below the starting order: `e ≡ 0` and `f` itself has order `≥ K + 1`
      refine ⟨e, fun p hp => hesupp p ?_, ?_⟩
      · rcases hp with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · have he0 : ∀ p, e p = 0 := by
          intro p
          rcases Nat.lt_or_ge (p.1 + p.2) k₀ with h | h
          · exact hesupp p (Or.inl h)
          · exact hesupp p (Or.inr (Or.inl (by omega)))
        have hSm0 : Sm N u v e = 0 := by
          rw [Sm]
          apply Finset.sum_eq_zero
          intro p _
          rw [he0 p, zero_smul]
        rw [hSm0, sub_zero]
        exact hf.mono (by omega)
    · -- absorb the degree-`K` coefficients of the remainder
      set T := f - Sm N u v e with hT
      set t : ℕ × ℕ → ℝ := fun p =>
        if p.1 + p.2 = K ∧ p.1 < N ∧ p.2 < N then coeff (dp p.1 p.2) T else 0 with ht
      refine ⟨fun p => e p + t p, ?_, ?_⟩
      · intro p hp
        have hepz : e p = 0 := by
          rcases hp with h | h | h | h
          · exact hesupp p (Or.inl h)
          · exact hesupp p (Or.inr (Or.inl (by omega)))
          · exact hesupp p (Or.inr (Or.inr (Or.inl h)))
          · exact hesupp p (Or.inr (Or.inr (Or.inr h)))
        have htpz : t p = 0 := by
          simp only [ht]
          refine if_neg ?_
          rintro ⟨h1, h2, h3⟩
          rcases hp with h | h | h | h <;> omega
        simp only [hepz, htpz, add_zero]
      · have hSm : Sm N u v (fun p => e p + t p) = Sm N u v e + Sm N u v t := by
          simp only [Sm, add_smul, Finset.sum_add_distrib]
        have hgoal : f - Sm N u v (fun p => e p + t p) = T - Sm N u v t := by
          rw [hSm, hT]
          abel
        rw [hgoal]
        intro d hd
        have hdd : dg d = d 0 + d 1 := rfl
        rw [coeff_sub]
        have hlowt : ∀ q : ℕ × ℕ, q.1 + q.2 < dg d → t q = 0 := by
          intro q hq
          simp only [ht]
          refine if_neg ?_
          rintro ⟨h1, -⟩
          omega
        rcases Nat.lt_or_ge (dg d) K with hdK | hdK
        · have hcoefft : coeff d (Sm N u v t) = 0 := by
            rw [coeff_Sm N hu hv t d (by omega) (by omega) hlowt]
            simp only [ht]
            refine if_neg ?_
            rintro ⟨h1, -⟩
            omega
          rw [hOrd d hdK, hcoefft, sub_zero]
        · have hdgK : dg d = K := by omega
          have hd0 : d 0 < N := by omega
          have hd1 : d 1 < N := by omega
          have hcoefft : coeff d (Sm N u v t) = coeff d T := by
            rw [coeff_Sm N hu hv t d hd0 hd1 hlowt]
            simp only [ht]
            rw [if_pos ⟨by omega, hd0, hd1⟩, eq_dp]
          rw [hcoefft, sub_self]

/-! ### The action of `X - 2` on the basis `u^i v^j`

With `X u = α u + ρ_u`, `X v = v + c u^r + ρ_v` (`ρ_u, ρ_v = 𝒪(m+1)`), one gets
`(X - 2)(u^i v^j) = (α i + j - 2) u^i v^j + c j·u^i v^{j-1} u^r + (high order)`.
This is the scalar-eigenfunction form of the diagonalized action of `X₀` used
in (eq:killc) and (eq:Rtop) of the paper. -/

/-- Purely algebraic identity behind the action of a derivation on `u^i v^j`. -/
lemma der_basis (u v ru rv Du Dv : R2) (alv c : ℝ) (r i j : ℕ)
    (hDu : Du = alv • u + ru) (hDv : Dv = v + c • u ^ r + rv) :
    ((i : ℝ) • (u ^ (i - 1) * Du)) * v ^ j + u ^ i * ((j : ℝ) • (v ^ (j - 1) * Dv))
      - (alv * i + j) • (u ^ i * v ^ j)
    = (c * j) • (u ^ i * v ^ (j - 1) * u ^ r)
      + ((i : ℝ) • (u ^ (i - 1) * ru * v ^ j) + (j : ℝ) • (u ^ i * v ^ (j - 1) * rv)) := by
  subst hDu hDv
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · push_cast
      simp only [pow_zero, smul_eq_C_mul, map_add, map_mul, map_zero]
      ring
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      push_cast
      simp only [pow_zero, smul_eq_C_mul, map_add, map_mul, map_one, map_zero,
        map_natCast]
      ring
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · push_cast
      simp only [pow_zero, smul_eq_C_mul, map_add, map_mul, map_one, map_zero,
        map_natCast]
      ring
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      push_cast
      simp only [smul_eq_C_mul, map_add, map_mul, map_one, map_natCast]
      ring

/-- `(X - 2)(v²) = 2c·u^r v + 2 v ρ_v` — the exact form of the resonant forcing of the
quadratic part `Δ₂ = B²`, cf. (eq:killc). -/
lemma der_vsq (p q u v : R2) (c : ℝ) (r : ℕ) :
    Der p q (v * v) - (2 : ℝ) • (v * v)
      = (2 * c) • (u ^ r * v) + (2 : ℝ) • (v * (Der p q v - v - c • u ^ r)) := by
  set rv := Der p q v - v - c • u ^ r with hrv
  have hDv : Der p q v = v + c • u ^ r + rv := by
    rw [hrv]
    abel
  rw [Der_mul, hDv]
  simp only [smul_eq_C_mul, map_mul, map_ofNat]
  ring

/-- Collection lemma: modulo order `T`, applying `X - 2` to `∑ d_{ij} u^i v^j`
multiplies each coefficient by the eigenvalue `α i + j - 2`.  The resonant `c`-terms
either vanish (`c = 0`) or land beyond order `T` (`T ≤ k₀ + r - 1`). -/
lemma collect (N : ℕ) (p q u v : R2) (alv c : ℝ) (r M : ℕ)
    (u2 : Ord 2 (u - va)) (v2 : Ord 2 (v - vb))
    (hru : Ord M (Der p q u - alv • u))
    (hrv : Ord M (Der p q v - v - c • u ^ r))
    (d : ℕ × ℕ → ℝ) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hd : ∀ p' : ℕ × ℕ, p'.1 + p'.2 < k₀ → d p' = 0)
    (T : ℕ) (hT1 : T ≤ k₀ - 1 + M) (hTc : c = 0 ∨ T ≤ k₀ + r - 1) :
    Ord T (Der p q (Sm N u v d) - (2 : ℝ) • Sm N u v d
      - Sm N u v (fun p' => (alv * p'.1 + p'.2 - 2) * d p')) := by
  have hu1 := ord_one_of_sub_va u2
  have hv1 := ord_one_of_sub_vb v2
  have hsum : Der p q (Sm N u v d) - (2 : ℝ) • Sm N u v d
        - Sm N u v (fun p' => (alv * p'.1 + p'.2 - 2) * d p')
      = ∑ pr ∈ Finset.range N ×ˢ Finset.range N,
          d pr • (Der p q (u ^ pr.1 * v ^ pr.2)
            - (alv * pr.1 + pr.2) • (u ^ pr.1 * v ^ pr.2)) := by
    simp only [Sm]
    rw [Der_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro pr _
    rw [Der_smul]
    module
  rw [hsum]
  apply Ord.finsetSum
  rintro ⟨i, j⟩ -
  by_cases hdp : d (i, j) = 0
  · rw [hdp, zero_smul]
    exact ord_zero T
  · have hk : k₀ ≤ i + j := by
      by_contra hlt
      exact hdp (hd (i, j) (by omega))
    have hDu : Der p q u = alv • u + (Der p q u - alv • u) := by abel
    have hDv : Der p q v = v + c • u ^ r + (Der p q v - v - c • u ^ r) := by abel
    rw [Der_mul, Der_pow, Der_pow,
      der_basis u v (Der p q u - alv • u) (Der p q v - v - c • u ^ r)
        (Der p q u) (Der p q v) alv c r i j hDu hDv]
    apply Ord.smul
    apply Ord.add
    · -- the resonant `c`-term
      rcases hTc with rfl | hTr
      · rw [zero_mul, zero_smul]
        exact ord_zero T
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [Nat.cast_zero, mul_zero, zero_smul]
          exact ord_zero T
        · have hord : Ord (i + (j - 1) + r) (u ^ i * v ^ (j - 1) * u ^ r) :=
            ((hu1.pow i).mul (hv1.pow (j - 1))).mul (hu1.pow r)
          exact (hord.smul _).mono (by omega)
    · apply Ord.add
      · -- the `ρ_u` error
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · rw [Nat.cast_zero, zero_smul]
          exact ord_zero T
        · have hord : Ord (i - 1 + M + j) (u ^ (i - 1) * (Der p q u - alv • u) * v ^ j) :=
            ((hu1.pow (i - 1)).mul hru).mul (hv1.pow j)
          exact (hord.smul _).mono (by omega)
      · -- the `ρ_v` error
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [Nat.cast_zero, zero_smul]
          exact ord_zero T
        · have hord : Ord (i + (j - 1) + M)
              (u ^ i * v ^ (j - 1) * (Der p q v - v - c • u ^ r)) :=
            ((hu1.pow i).mul (hv1.pow (j - 1))).mul hrv
          exact (hord.smul _).mono (by omega)

/-! ### The resonance lemma (Lemma 3.1 of the paper)

Let `X = X₀ + 𝒪(2)` with `X₀ = α A ∂_A + B ∂_B`, `α = 2/(m+1)`, let
`Δ = B² + 𝒪(3)`, and suppose `R := (X - 2)Δ = 𝒪(m+1)` (eq:Rorder).  Then the
coefficient of `A^{m+1}` in `R` vanishes.  The proof is the paper's: a finite
Poincaré–Dulac normalization (only finitely many homogeneous corrections), the
killing identity (eq:killc) — which uses the degree-`(r+1)` part of `R` with
`r = (m+1)/2` to force the sole possible resonant coefficient `c` to vanish — and
the vanishing eigenvalue `α(m+1) - 2 = 0` in the top degree (eq:Rtop). -/

theorem resonance {m : ℕ} (hm : 2 ≤ m) {p' q' Δ : R2}
    (hp' : Ord 2 p') (hq' : Ord 2 q')
    (hΔ : Ord 3 (Δ - vb * vb))
    (hR : Ord (m + 1) (Der (al m • va + p') (vb + q') Δ - (2 : ℝ) • Δ)) :
    coeff (dp (m + 1) 0) (Der (al m • va + p') (vb + q') Δ - (2 : ℝ) • Δ) = 0 := by
  classical
  obtain ⟨u, hu, hru⟩ := exists_u hm hp' hq'
  obtain ⟨v, c, r, hv, hrv, hcr⟩ := exists_v hm hp' hq' hu
  set P : R2 := al m • va + p' with hPdef
  set Q : R2 := vb + q' with hQdef
  have hu1 := ord_one_of_sub_va hu
  have hv1 := ord_one_of_sub_vb hv
  have hP1 : Ord 1 P := by
    rw [hPdef]
    exact (ord_va.smul (al m)).add (hp'.mono (by omega))
  have hQ1 : Ord 1 Q := by
    rw [hQdef]
    exact ord_vb.add (hq'.mono (by omega))
  have hΔ2 : Ord 2 Δ := by
    have h1 : Ord 2 (Δ - vb * vb) := hΔ.mono (by omega)
    have h2 : Ord 2 (vb * vb) := ord_vb.mul ord_vb
    have h3 := h1.add h2
    simpa using h3
  -- Step 1: the resonant coefficient `c` vanishes.  For even `m` this holds by
  -- construction; for odd `m` it is the killing identity (eq:killc), read off from the
  -- degree-`(r+1)` coefficient of `R` at the exponent `A^r B`.
  have hc0 : c = 0 := by
    rcases hcr with hc | ⟨h2r, hr2⟩
    · exact hc
    · have hrm : r + 2 ≤ m + 1 := by omega
      have hΔv : Ord 3 (Δ - v * v) := by
        have hvv : Ord 3 (v * v - vb * vb) := by
          have hkey : v * v - vb * vb = (v - vb) * (v + vb) := by ring
          rw [hkey]
          exact hv.mul (hv1.add ord_vb)
        have hkey2 : Δ - v * v = (Δ - vb * vb) - (v * v - vb * vb) := by abel
        rw [hkey2]
        exact hΔ.sub hvv
      obtain ⟨e, hesupp, hOrdE⟩ := expand (m + 2) hu hv 3 (r + 2) (by omega) _ hΔv
      have hcol := collect (m + 2) P Q u v (al m) c r (m + 1) hu hv hru hrv e 3
        (by omega) (fun pp hpp => hesupp pp (Or.inl hpp)) (r + 2) (by omega)
        (Or.inr (by omega))
      have hOrdT1 : Ord (r + 2) (Der P Q (Δ - v * v - Sm (m + 2) u v e)
          - (2 : ℝ) • (Δ - v * v - Sm (m + 2) u v e)) := by
        have hda := Ord.der (c := 0) hP1 hQ1 hOrdE
        exact (hda.mono (by omega)).sub (hOrdE.smul 2)
      -- `R` agrees with `(2c)·u^r v + ∑ (αi+j-2) e_{ij} u^i v^j` to order `r+2`
      have hvsq' : Der P Q (v * v) = (2 : ℝ) • (v * v) + (2 * c) • (u ^ r * v)
          + (2 : ℝ) • (v * (Der P Q v - v - c • u ^ r)) := by
        have h := der_vsq P Q u v c r
        rw [add_assoc, ← h]
        abel
      have hDer3 : Der P Q Δ = Der P Q (v * v) + Der P Q (Sm (m + 2) u v e)
          + Der P Q (Δ - v * v - Sm (m + 2) u v e) := by
        rw [← Der_add, ← Der_add]
        congr 1
        abel
      have hsm3 : (2 : ℝ) • Δ = (2 : ℝ) • (v * v) + (2 : ℝ) • Sm (m + 2) u v e
          + (2 : ℝ) • (Δ - v * v - Sm (m + 2) u v e) := by
        rw [← smul_add, ← smul_add]
        congr 1
        abel
      have hsplit : Der P Q Δ - (2 : ℝ) • Δ
            - ((2 * c) • (u ^ r * v)
              + Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp))
          = (Der P Q (Sm (m + 2) u v e) - (2 : ℝ) • Sm (m + 2) u v e
              - Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp))
            + (Der P Q (Δ - v * v - Sm (m + 2) u v e)
              - (2 : ℝ) • (Δ - v * v - Sm (m + 2) u v e))
            + (2 : ℝ) • (v * (Der P Q v - v - c • u ^ r)) := by
        rw [hDer3, hsm3, hvsq']
        abel
      have hRdiff1 : Ord (r + 2) (Der P Q Δ - (2 : ℝ) • Δ
          - ((2 * c) • (u ^ r * v)
            + Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp))) := by
        rw [hsplit]
        exact (hcol.add hOrdT1).add (((hv1.mul hrv).smul 2).mono (by omega))
      have hcomb : Ord (r + 2) ((2 * c) • (u ^ r * v)
          + Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp)) := by
        have hkey : (2 * c) • (u ^ r * v)
              + Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp)
            = (Der P Q Δ - (2 : ℝ) • Δ)
              - (Der P Q Δ - (2 : ℝ) • Δ
                - ((2 * c) • (u ^ r * v)
                  + Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp))) := by
          abel
        rw [hkey]
        exact (hR.mono (by omega)).sub hRdiff1
      -- merge the two pieces into a single coefficient family
      have hmem31 : (r, 1) ∈ Finset.range (m + 2) ×ˢ Finset.range (m + 2) :=
        Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
      have hmerge : Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp
            + (if pp = (r, 1) then 2 * c else 0))
          = Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp)
            + (2 * c) • (u ^ r * v ^ 1) := by
        simp only [Sm, add_smul, Finset.sum_add_distrib]
        congr 1
        have hterm : ∀ pp ∈ Finset.range (m + 2) ×ˢ Finset.range (m + 2),
            (if pp = (r, 1) then 2 * c else 0) • (u ^ pp.1 * v ^ pp.2)
              = (if pp = (r, 1) then (2 * c) • (u ^ r * v ^ 1) else 0) := by
          intro pp _
          by_cases h : pp = (r, 1)
          · rw [if_pos h, if_pos h, h]
          · rw [if_neg h, if_neg h, zero_smul]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ (r, 1) _, if_pos hmem31]
      have hsupp3 : ∀ pp : ℕ × ℕ, (m + 2) ≤ pp.1 ∨ (m + 2) ≤ pp.2 →
          (al m * pp.1 + pp.2 - 2) * e pp + (if pp = (r, 1) then 2 * c else 0) = 0 := by
        intro pp hpp
        have he0 : e pp = 0 := hesupp pp (Or.inr (Or.inr hpp))
        rw [he0, mul_zero, zero_add, if_neg]
        rintro rfl
        simp only [] at hpp
        omega
      have hSmE3 : Ord (r + 2) (Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * e pp
          + (if pp = (r, 1) then 2 * c else 0))) := by
        rw [hmerge, pow_one]
        rwa [add_comm ((2 * c) • (u ^ r * v))] at hcomb
      have hE3v := ext_vanish (m + 2) hu hv _ (r + 2) hsupp3 hSmE3 (r, 1) (by norm_num)
      have halr : al m * (r : ℝ) = 1 := (al_mul_eq_one_iff m r).mpr h2r
      simp only [halr] at hE3v
      norm_num at hE3v
      exact hE3v
  -- Step 2: with `c = 0`, expand `Δ` itself in the basis and read the coefficient of
  -- `A^{m+1}`: the eigenvalue `α(m+1) - 2` vanishes (eq:Rtop).
  rw [hc0] at hrv
  obtain ⟨d, hdsupp, hOrdD⟩ := expand (m + 2) hu hv 2 (m + 2) (le_refl _) Δ hΔ2
  have hcol2 := collect (m + 2) P Q u v (al m) 0 r (m + 1) hu hv hru hrv d 2
    (by omega) (fun pp hpp => hdsupp pp (Or.inl hpp)) (m + 2) (by omega) (Or.inl rfl)
  have hOrdT2 : Ord (m + 2) (Der P Q (Δ - Sm (m + 2) u v d)
      - (2 : ℝ) • (Δ - Sm (m + 2) u v d)) := by
    have hda := Ord.der (c := 0) hP1 hQ1 hOrdD
    exact (hda.mono (by omega)).sub (hOrdD.smul 2)
  have hsplit2 : Der P Q Δ - (2 : ℝ) • Δ
        - Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp)
      = (Der P Q (Sm (m + 2) u v d) - (2 : ℝ) • Sm (m + 2) u v d
          - Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp))
        + (Der P Q (Δ - Sm (m + 2) u v d) - (2 : ℝ) • (Δ - Sm (m + 2) u v d)) := by
    have hD : Der P Q Δ = Der P Q (Sm (m + 2) u v d) + Der P Q (Δ - Sm (m + 2) u v d) := by
      rw [← Der_add]
      congr 1
      abel
    have hS : (2 : ℝ) • Δ = (2 : ℝ) • Sm (m + 2) u v d
        + (2 : ℝ) • (Δ - Sm (m + 2) u v d) := by
      rw [← smul_add]
      congr 1
      abel
    rw [hD, hS]
    abel
  have hRdiff2 : Ord (m + 2) (Der P Q Δ - (2 : ℝ) • Δ
      - Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp)) := by
    rw [hsplit2]
    exact hcol2.add hOrdT2
  have hSmE4 : Ord (m + 1) (Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp)) := by
    have hkey : Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp)
        = (Der P Q Δ - (2 : ℝ) • Δ)
          - (Der P Q Δ - (2 : ℝ) • Δ
            - Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp)) := by
      abel
    rw [hkey]
    exact hR.sub (hRdiff2.mono (by omega))
  have hsupp4 : ∀ pp : ℕ × ℕ, (m + 2) ≤ pp.1 ∨ (m + 2) ≤ pp.2 →
      (al m * pp.1 + pp.2 - 2) * d pp = 0 := by
    intro pp hpp
    rw [hdsupp pp (Or.inr (Or.inr hpp)), mul_zero]
  have hE4low := ext_vanish (m + 2) hu hv _ (m + 1) hsupp4 hSmE4
  have hcoefflow : ∀ qq : ℕ × ℕ, qq.1 + qq.2 < dg (dp (m + 1) 0) →
      (al m * qq.1 + qq.2 - 2) * d qq = 0 := by
    intro qq hqq
    simp only [dg_dp] at hqq
    exact hE4low qq (by omega)
  have hcS := coeff_Sm (m + 2) hu hv _ (dp (m + 1) 0)
    (by simp only [dp_apply_zero]; omega) (by simp only [dp_apply_one]; omega) hcoefflow
  have hfinal : coeff (dp (m + 1) 0) (Der P Q Δ - (2 : ℝ) • Δ)
      = coeff (dp (m + 1) 0) (Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp))
        + coeff (dp (m + 1) 0) (Der P Q Δ - (2 : ℝ) • Δ
          - Sm (m + 2) u v (fun pp => (al m * pp.1 + pp.2 - 2) * d pp)) := by
    rw [← coeff_add]
    congr 1
    abel
  rw [hfinal, hRdiff2 _ (by simp only [dg_dp]; omega), add_zero, hcS]
  simp only [dp_apply_zero, dp_apply_one]
  have h2 : al m * ((m : ℝ) + 1) = 2 := al_mul_succ m
  push_cast
  rw [h2]
  norm_num

/-! ### The hodograph objects (§2 of the paper)

`F` and `G` are the two remaining combinations of first derivatives, regarded as
functions of the hodograph coordinates `(A,B)` (eq:FG).  Here they are arbitrary
polynomial jets in `(A,B) = (va, vb)`; the objects of Lemma 2.1 are defined verbatim. -/

/-- (eq:E): `E = (1 - G_B)F - (1 + G_B) A F_A + (A G_A - B) F_B - 2 B G_A`. -/
noncomputable def Eexpr (F G : R2) : R2 :=
  (1 - pderiv 1 G) * F - (1 + pderiv 1 G) * (va * pderiv 0 F)
    + (va * pderiv 0 G - vb) * pderiv 1 F - 2 * (vb * pderiv 0 G)

/-- The `∂_A`-coefficient of the vector field `X` (eq:X): `A(1 + G_B)`. -/
noncomputable def Xa (G : R2) : R2 := va * (1 + pderiv 1 G)

/-- The `∂_B`-coefficient of the vector field `X` (eq:X): `B - A G_A`. -/
noncomputable def Xb (G : R2) : R2 := vb - va * pderiv 0 G

/-- (eq:Delta): `Δ = B² - A F`. -/
noncomputable def Dexpr (F : R2) : R2 := vb * vb - va * F

/-- **The exact hodograph identity (eq:key) of Lemma 2.1**: `(X - 2)Δ = A·E`,
proved as a polynomial identity valid for arbitrary jets `F`, `G`. -/
theorem key_identity (F G : R2) :
    Der (Xa G) (Xb G) (Dexpr F) - (2 : ℝ) • Dexpr F = va * Eexpr F G := by
  simp only [Der, Xa, Xb, Dexpr, Eexpr, va_def, vb_def, map_sub, pderiv_mul,
    pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_C_mul, map_ofNat]
  ring

/-- **Theorem 1.1 in hodograph form.**  Assume the normalized leading jets
(eq:leadingFG): `F = 𝒪(2)` and `G = ((1-m)/(1+m)) B + 𝒪(2)`.  If `E = 𝒪(m)`
— which encodes the lower-order jet equations `W_{ij} = 0`, `i+j < m`, through
`W = 2JE` (eq:WE) — then the coefficient of `A^m` in `E` vanishes, which encodes the
resonant equation `W_{m0} = 0` through (eq:return).  This is the entire §4 argument. -/
theorem hodograph_resonant_coefficient {m : ℕ} (hm : 2 ≤ m) {F G : R2}
    (hF : Ord 2 F)
    (hG : Ord 2 (G - ((1 - (m : ℝ)) / (1 + (m : ℝ))) • vb))
    (hE : Ord m (Eexpr F G)) :
    coeff (dp m 0) (Eexpr F G) = 0 := by
  set c₀ : ℝ := (1 - (m : ℝ)) / (1 + (m : ℝ)) with hc₀
  set G' : R2 := G - c₀ • vb with hG'
  have hmR : (1 : ℝ) + (m : ℝ) ≠ 0 := by positivity
  have hc₀al : 1 + c₀ = al m := by
    rw [hc₀, al]
    field_simp
    ring
  have hpdG1 : pderiv 1 G' = pderiv 1 G - C c₀ := by
    rw [hG', map_sub, Derivation.map_smul, vb_def, pderiv_X_self, smul_eq_C_mul, mul_one]
  have hpdG0 : pderiv 0 G' = pderiv 0 G := by
    rw [hG', map_sub, Derivation.map_smul, vb_def,
      pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide), smul_zero, sub_zero]
  have hXa : Xa G = al m • va + va * pderiv 1 G' := by
    rw [Xa, hpdG1, smul_eq_C_mul, ← hc₀al, map_add, map_one]
    ring
  have hXb : Xb G = vb + -(va * pderiv 0 G') := by
    rw [Xb, hpdG0]
    ring
  have hp' : Ord 2 (va * pderiv 1 G') := by
    have h1 : Ord 1 (pderiv 1 G') := hG.pderiv 1
    exact ord_va.mul h1
  have hq' : Ord 2 (-(va * pderiv 0 G')) := (ord_va.mul (hG.pderiv 0)).neg
  have hΔ : Ord 3 (Dexpr F - vb * vb) := by
    have hkey : Dexpr F - vb * vb = -(va * F) := by
      rw [Dexpr]
      ring
    rw [hkey]
    exact (ord_va.mul hF).neg
  have hRE : Der (al m • va + va * pderiv 1 G') (vb + -(va * pderiv 0 G')) (Dexpr F)
      - (2 : ℝ) • Dexpr F = va * Eexpr F G := by
    rw [← hXa, ← hXb]
    exact key_identity F G
  have hROrd : Ord (m + 1) (Der (al m • va + va * pderiv 1 G')
      (vb + -(va * pderiv 0 G')) (Dexpr F) - (2 : ℝ) • Dexpr F) := by
    rw [hRE]
    exact (ord_va.mul hE).mono (by omega)
  have hres := resonance hm hp' hq' hΔ hROrd
  rw [hRE] at hres
  have hdp : dp (m + 1) 0 = Finsupp.single 0 1 + dp m 0 := by
    refine finsupp_fin2_ext ?_ ?_ <;> (simp [Finsupp.add_apply]; try omega)
  rw [hdp, va_def, coeff_X_mul] at hres
  exact hres

/-- **Theorem 1.1 (all-order resonant compatibility), jet form.**
The two hypotheses `hWE` and `hreturn` transcribe the hodograph bridge of the paper,
which lies beyond the formal-polynomial calculus available here:

* `hWE` encodes `W = 2JE` (eq:WE) together with the diffeomorphism invariance of the
  vanishing order: the jet equations `W_{ij} = 0` for `i + j < m` (eq:lower) are
  equivalent to `E = 𝒪(m)` (eq:Eord), since `J` is a unit.
* `hreturn` encodes the coefficient translation (eq:return):
  `W_{m0} = 2 J(0) m! a^m [A^m]E_m`, obtained by pulling the degree-`m` part of
  `W = 2JE` back through the diagonal linearization `A = ax`, `B = ((m+1)/2)a y`
  of the hodograph map (eq:ABlinear).

Given these, the lower-order equations (eq:lower) force the resonant equation
`W_{m0} = 0` (eq:target). -/
theorem allorder_compatibility {m : ℕ} (hm : 2 ≤ m) (F G : R2) (W : ℕ → ℕ → ℝ)
    (J0 a : ℝ)
    (hF : Ord 2 F)
    (hG : Ord 2 (G - ((1 - (m : ℝ)) / (1 + (m : ℝ))) • vb))
    (hWE : (∀ i j, i + j < m → W i j = 0) → Ord m (Eexpr F G))
    (hreturn : W m 0 = 2 * J0 * (Nat.factorial m) * a ^ m * coeff (dp m 0) (Eexpr F G))
    (hlower : ∀ i j, i + j < m → W i j = 0) :
    W m 0 = 0 := by
  rw [hreturn, hodograph_resonant_coefficient hm hF hG (hWE hlower), mul_zero]

/-! ### The Weingarten operator `W(P,Q)` in the original chart (§1 of the paper)

Here `R2` is read as polynomials in the original variables `(x, y) = (va, vb)`.
All mixed partials are written with the `x`-derivative outermost, so that no use of
Schwarz symmetry is hidden in the definition; where the paper's rearrangement uses
equality of mixed partials, `pderiv_pderiv_comm` is invoked explicitly. -/

/-- (eq:W): the equation for a `W`-congruence,
`W = (Q_y - P_x)(Q_{xx}P_{yy} - P_{xx}Q_{yy}) - 2P_y(P_{xx}Q_{xy} - Q_{xx}P_{xy})
   + 2Q_x(P_{xy}Q_{yy} - P_{yy}Q_{xy})`. -/
noncomputable def Wexpr (P Q : R2) : R2 :=
  (pderiv 1 Q - pderiv 0 P)
      * (pderiv 0 (pderiv 0 Q) * pderiv 1 (pderiv 1 P)
        - pderiv 0 (pderiv 0 P) * pderiv 1 (pderiv 1 Q))
    - C 2 * pderiv 1 P
      * (pderiv 0 (pderiv 0 P) * pderiv 0 (pderiv 1 Q)
        - pderiv 0 (pderiv 0 Q) * pderiv 0 (pderiv 1 P))
    + C 2 * pderiv 0 Q
      * (pderiv 0 (pderiv 1 P) * pderiv 1 (pderiv 1 Q)
        - pderiv 1 (pderiv 1 P) * pderiv 0 (pderiv 1 Q))

/-- (eq:hess), first equality: `W` as a `3×3` determinant. -/
theorem Wexpr_eq_det (P Q : R2) :
    Wexpr P Q = Matrix.det
      !![C 2 * pderiv 0 Q, pderiv 1 Q - pderiv 0 P, -(C 2 * pderiv 1 P);
         pderiv 0 (pderiv 0 P), pderiv 0 (pderiv 1 P), pderiv 1 (pderiv 1 P);
         pderiv 0 (pderiv 0 Q), pderiv 0 (pderiv 1 Q), pderiv 1 (pderiv 1 Q)] := by
  rw [Matrix.det_fin_three, Wexpr]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- (eq:hess), second equality: `W = det(Hess(xQ - yP), Hess P, Hess Q)`, where a
symmetric Hessian is represented by the row `(f_xx, f_xy, f_yy)`. -/
theorem Wexpr_eq_det_hess (P Q : R2) :
    Wexpr P Q = Matrix.det
      !![pderiv 0 (pderiv 0 (va * Q - vb * P)), pderiv 0 (pderiv 1 (va * Q - vb * P)),
           pderiv 1 (pderiv 1 (va * Q - vb * P));
         pderiv 0 (pderiv 0 P), pderiv 0 (pderiv 1 P), pderiv 1 (pderiv 1 P);
         pderiv 0 (pderiv 0 Q), pderiv 0 (pderiv 1 Q), pderiv 1 (pderiv 1 Q)] := by
  have h1 : pderiv 0 (pderiv 0 (va * Q - vb * P))
      = C 2 * pderiv 0 Q + va * pderiv 0 (pderiv 0 Q) - vb * pderiv 0 (pderiv 0 P) := by
    simp only [map_sub, map_add, pderiv_mul, va_def, vb_def, pderiv_X_self,
      pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide), map_ofNat, map_zero,
      Derivation.map_one_eq_zero]
    ring
  have h2 : pderiv 0 (pderiv 1 (va * Q - vb * P))
      = (pderiv 1 Q - pderiv 0 P) + va * pderiv 0 (pderiv 1 Q)
        - vb * pderiv 0 (pderiv 1 P) := by
    simp only [map_sub, map_add, pderiv_mul, va_def, vb_def, pderiv_X_self,
      pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), map_zero,
      Derivation.map_one_eq_zero]
    ring
  have h3 : pderiv 1 (pderiv 1 (va * Q - vb * P))
      = -(C 2 * pderiv 1 P) + va * pderiv 1 (pderiv 1 Q)
        - vb * pderiv 1 (pderiv 1 P) := by
    simp only [map_sub, map_add, pderiv_mul, va_def, vb_def, pderiv_X_self,
      pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), map_ofNat, map_zero,
      Derivation.map_one_eq_zero]
    ring
  rw [h1, h2, h3, Matrix.det_fin_three, Wexpr]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- `A = P_y` as a function of the original variables (eq:AB). -/
noncomputable def Afun (P : R2) : R2 := pderiv 1 P

/-- `2B = P_x - Q_y`: twice the `B` of (eq:AB), doubled to avoid division. -/
noncomputable def B2fun (P Q : R2) : R2 := pderiv 0 P - pderiv 1 Q

/-- `F = -Q_x` (eq:FG), as a function of the original variables. -/
noncomputable def Ffun (Q : R2) : R2 := -pderiv 0 Q

/-- `4Δ = (2B)² - 4AF`: four times the discriminant `Δ = B² - AF` (eq:Delta). -/
noncomputable def D4fun (P Q : R2) : R2 :=
  B2fun P Q * B2fun P Q - C 4 * (Afun P * Ffun Q)

/-- **(eq:Wdelta), cleared of denominators**: the direct rearrangement of the six terms
of (eq:W) in the proof of Lemma 2.1, in the equivalent integral form
`4W = (2A_x - (2B)_y)(4Δ)_x + (2F_y - (2B)_x)(4Δ)_y + 4·det[(A,2B,F); ∂_x(…); ∂_y(…)]`
(the paper's identity is this one divided by `4`, with `B = (2B)/2`, `Δ = (4Δ)/4`).
Equality of mixed partials (Schwarz) enters exactly here, as in the paper. -/
theorem Wdelta_identity (P Q : R2) :
    C 4 * Wexpr P Q
      = (C 2 * pderiv 0 (Afun P) - pderiv 1 (B2fun P Q)) * pderiv 0 (D4fun P Q)
        + (C 2 * pderiv 1 (Ffun Q) - pderiv 0 (B2fun P Q)) * pderiv 1 (D4fun P Q)
        + C 4 * Matrix.det
            !![Afun P, B2fun P Q, Ffun Q;
               pderiv 0 (Afun P), pderiv 0 (B2fun P Q), pderiv 0 (Ffun Q);
               pderiv 1 (Afun P), pderiv 1 (B2fun P Q), pderiv 1 (Ffun Q)] := by
  have hcomm : ∀ f : R2, pderiv (1 : Fin 2) (pderiv 0 f) = pderiv 0 (pderiv 1 f) :=
    fun f => pderiv_pderiv_comm 1 0 f
  rw [Matrix.det_fin_three, Wexpr]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  simp only [Afun, B2fun, Ffun, D4fun]
  have hp4 : ∀ i : Fin 2, pderiv i (4 : R2) = 0 := fun i => by
    rw [← map_ofNat (C : ℝ →+* R2) 4, pderiv_C]
  simp only [map_sub, map_neg, pderiv_mul, map_ofNat, hp4]
  simp only [hcomm]
  ring

/-! ### Jet computations at the normalized umbilic (§1–§2 of the paper)

`constantCoeff ∘ ∂ᵅ` evaluates the jet coefficients `p_{ij}, q_{ij}, W_{ij}` at the
origin.  The following identities hold for arbitrary germs with the stated normalized
low-order jets; no explicit Taylor polynomials are needed. -/

/-- At an umbilic (`p_{01} = q_{10} = 0`, `p_{10} = q_{01}`), the value `W_{00} = W(0)`
vanishes automatically — the order-zero jet equation of (eq:lower) is vacuous. -/
theorem W00_at_umbilic (P Q : R2) (t : ℝ)
    (hPy : constantCoeff (pderiv 1 P) = 0)
    (hQx : constantCoeff (pderiv 0 Q) = 0)
    (hPx : constantCoeff (pderiv 0 P) = t)
    (hQy : constantCoeff (pderiv 1 Q) = t) :
    constantCoeff (Wexpr P Q) = 0 := by
  simp only [Wexpr, map_sub, map_add, map_mul, hPy, hQx, hPx, hQy, constantCoeff_C]
  ring

/-- **(eq:W10)**: at the normalized nondegenerate umbilic
(`p_{10} = p_{01} = q_{10} = q_{01} = 0`, `p_{20} = p_{02} = q_{11} = 0`,
`p_{11} = a`, `q_{02} = -ma`), the first jet equation reads
`W_{10} = 2 q_{20} a² (1 - m)`.  Stated for arbitrary germs `P, Q` (any real `m`);
third-order jet coefficients cancel automatically. -/
theorem W10_eq (P Q : R2) (a q20 mr : ℝ)
    (hPx : constantCoeff (pderiv 0 P) = 0)
    (hPy : constantCoeff (pderiv 1 P) = 0)
    (hQx : constantCoeff (pderiv 0 Q) = 0)
    (hQy : constantCoeff (pderiv 1 Q) = 0)
    (hPxx : constantCoeff (pderiv 0 (pderiv 0 P)) = 0)
    (hPxy : constantCoeff (pderiv 0 (pderiv 1 P)) = a)
    (hPyy : constantCoeff (pderiv 1 (pderiv 1 P)) = 0)
    (hQxx : constantCoeff (pderiv 0 (pderiv 0 Q)) = q20)
    (hQxy : constantCoeff (pderiv 0 (pderiv 1 Q)) = 0)
    (hQyy : constantCoeff (pderiv 1 (pderiv 1 Q)) = -(mr * a)) :
    constantCoeff (pderiv 0 (Wexpr P Q)) = 2 * q20 * a ^ 2 * (1 - mr) := by
  simp only [Wexpr, map_sub, map_add, map_mul, pderiv_mul,
    hPx, hPy, hQx, hQy, hPxx, hPxy, hPyy, hQxx, hQxy, hQyy, constantCoeff_C]
  ring

/-- **(eq:ABlinear) and (eq:J)**: at the normalized umbilic, the hodograph functions
have linearizations `A = a x + 𝒪(2)`, `2B = (m+1) a y + 𝒪(2)`, and the Jacobian
`2J(0) = A_x (2B)_y - A_y (2B)_x = (m+1) a² ≠ 0` at the origin, so `(A,B)` are local
coordinates.  (All values are doubled where the paper's `B` is halved.) -/
theorem hodograph_linearization (P Q : R2) (a mr : ℝ)
    (hPxx : constantCoeff (pderiv 0 (pderiv 0 P)) = 0)
    (hPxy : constantCoeff (pderiv 0 (pderiv 1 P)) = a)
    (hPyy : constantCoeff (pderiv 1 (pderiv 1 P)) = 0)
    (hQxy : constantCoeff (pderiv 0 (pderiv 1 Q)) = 0)
    (hQyy : constantCoeff (pderiv 1 (pderiv 1 Q)) = -(mr * a)) :
    constantCoeff (pderiv 0 (Afun P)) = a
    ∧ constantCoeff (pderiv 1 (Afun P)) = 0
    ∧ constantCoeff (pderiv 0 (B2fun P Q)) = 0
    ∧ constantCoeff (pderiv 1 (B2fun P Q)) = (mr + 1) * a
    ∧ constantCoeff (pderiv 0 (Afun P)) * constantCoeff (pderiv 1 (B2fun P Q))
        - constantCoeff (pderiv 1 (Afun P)) * constantCoeff (pderiv 0 (B2fun P Q))
      = (mr + 1) * a ^ 2 := by
  have hcomm : ∀ f : R2, pderiv (1 : Fin 2) (pderiv 0 f) = pderiv 0 (pderiv 1 f) :=
    fun f => pderiv_pderiv_comm 1 0 f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Afun, B2fun, map_sub, hcomm, hPxx, hPxy, hPyy, hQxy, hQyy]; try ring)

/-- **The case `m = 1` of Theorem 1.1** (end of §4): the identity (eq:W10) has the
factor `1 - m`, so the resonant equation `W_{10} = 0` holds with no hypothesis. -/
theorem W10_vanishes_of_m_eq_one (P Q : R2) (a q20 : ℝ)
    (hPx : constantCoeff (pderiv 0 P) = 0)
    (hPy : constantCoeff (pderiv 1 P) = 0)
    (hQx : constantCoeff (pderiv 0 Q) = 0)
    (hQy : constantCoeff (pderiv 1 Q) = 0)
    (hPxx : constantCoeff (pderiv 0 (pderiv 0 P)) = 0)
    (hPxy : constantCoeff (pderiv 0 (pderiv 1 P)) = a)
    (hPyy : constantCoeff (pderiv 1 (pderiv 1 P)) = 0)
    (hQxx : constantCoeff (pderiv 0 (pderiv 0 Q)) = q20)
    (hQxy : constantCoeff (pderiv 0 (pderiv 1 Q)) = 0)
    (hQyy : constantCoeff (pderiv 1 (pderiv 1 Q)) = -(1 * a)) :
    constantCoeff (pderiv 0 (Wexpr P Q)) = 0 := by
  rw [W10_eq P Q a q20 1 hPx hPy hQx hQy hPxx hPxy hPyy hQxx hQxy hQyy]
  ring

end WCongruenceAllOrder
