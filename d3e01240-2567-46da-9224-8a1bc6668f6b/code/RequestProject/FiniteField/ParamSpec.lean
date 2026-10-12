module

public import Mathlib
public import RequestProject.FiniteField.SeventyOneSpec
public import RequestProject.FiniteField.SixfoldUnits

/-!
# The parameterized prime-sector specification (any modulus `Π` in place of `71`)

The specification defines, for a user-selected modulus `Π`,
`ε = frac((Π-1)/6)`, `Δ = 1 + ε`, `ρ = frac(Π·Δ)`, a tile `v = (a + bω) mod Π` in
`ℤ[ω]/(Π)`, and a symmetry rule "six-fold symmetry may close iff `Π ≡ 0, ±1 (mod 36)`".

* `errorTerm_eq'`, `residual_eq`, `residual_ne_zero_iff`: `ε = ((Π-1) mod 6)/6` and
  `ρ = 1/3` if `Π ≡ 2 (mod 3)`, `ρ = 0` otherwise, for **every** integer `Π`.
* `prime_step`: for primes `p ≥ 5`, `Δ ∈ {1, 5/3}`.
* `card_eisResidue`: `ℤ[ω]/(p)` has `p²` elements, not `Π` (`N_Π := Π` is the size of `ℤ/Π`).
* `eisResidue_isField_iff`: for a prime `p`, `ℤ[ω]/(p)` is a field iff `p ≡ 2 (mod 3)`.
* `zmod_prime_unique`, `zmod_composite_bad`: the field / non-field behaviour of `ℤ/Π`.
* `inert_symmetry_iff`, `split_symmetry_iff`, `prime_symmetry_iff`: for a prime `p ≥ 5` the
  60° turn fixes every colour iff `p mod 36 ∈ {1, 17, 35}` (not `{0, 1, 35}`).
* `spec_rule_wrong_at_17`, `spec_rule_zero_never_prime`: where the specification's rule fails.
* `holonomy_independent_of_symmetry`: `ρ ≠ 0` neither forces nor forbids symmetry.
-/

@[expose] public section

namespace ParamSpec

open FiniteFieldModels ColourWheel Polynomial

/-! ## Derived fundamentals -/

/-- `ε(Π) = frac((Π - 1)/6)`. -/
noncomputable def errorTerm (N : ℤ) : ℚ := Int.fract (((N : ℚ) - 1) / 6)

/-- `Δ(Π) = 1 + ε(Π)`. -/
noncomputable def stepOp (N : ℤ) : ℚ := 1 + errorTerm N

/-- `ρ(Π) = (Π · Δ(Π)) mod 1`. -/
noncomputable def residual (N : ℤ) : ℚ := Int.fract ((N : ℚ) * stepOp N)

theorem errorTerm_eq' (N : ℤ) : errorTerm N = (((N - 1) % 6 : ℤ) : ℚ) / 6 :=
  SeventyOneSpec.errorTerm_eq N

/-- **Residual for every modulus.** `ρ(Π) = 1/3` if `Π ≡ 2 (mod 3)`, else `0`. -/
theorem residual_eq (N : ℤ) : residual N = if N % 3 = 2 then 1 / 3 else 0 :=
  SeventyOneSpec.residual_general N

/-- Holonomy is nonzero exactly when `Π ≡ 2 (mod 3)`. -/
theorem residual_ne_zero_iff (N : ℤ) : residual N ≠ 0 ↔ N % 3 = 2 := by
  rw [residual_eq]; split_ifs with h <;> simp [h]

/-- For a prime `p ≥ 5`: `ε ∈ {0, 2/3}` and `Δ ∈ {1, 5/3}`. -/
theorem prime_step {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    errorTerm p = (if p % 3 = 2 then 2 / 3 else 0) ∧
      stepOp p = (if p % 3 = 2 then 5 / 3 else 1) := by
  have h := SeventyOneSpec.prime_errorTerm hp h5
  have e : errorTerm p = if p % 3 = 2 then 2 / 3 else 0 := by
    simpa [errorTerm] using h
  refine ⟨e, ?_⟩
  rw [stepOp, e]; split_ifs <;> norm_num

/-- The worked example `Π = 71`. -/
theorem example71 : errorTerm 71 = 2 / 3 ∧ stepOp 71 = 5 / 3 ∧ residual 71 = 1 / 3 ∧
    71 % 36 = 35 := by
  have h := prime_step (p := 71) (by norm_num) (by norm_num)
  refine ⟨by simpa using h.1, by simpa using h.2, by rw [residual_eq]; norm_num, by norm_num⟩

/-! ## The ring `ℤ[ω]/(Π)` -/

/-- `ℤ[ω]/(p)` has `p²` elements. -/
theorem card_eisResidue (p : ℕ) [Fact p.Prime] : Fintype.card (EisResidue p) = p ^ 2 :=
  EisResidue.card p

/-- If `X² + X + 1` has a root in `𝔽_p`, then `ℤ[ω]/(p)` is not a field. -/
theorem not_isField_of_root {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r ^ 2 + r + 1 = 0) :
    ¬ IsField (EisResidue p) := by
  intro hF
  haveI := hF.isDomain
  have hω := EisResidue.omega_sq_add p
  set R : EisResidue p := algebraMap (ZMod p) (EisResidue p) r with hR
  have hR2 : R ^ 2 + R + 1 = 0 := by
    have := congrArg (algebraMap (ZMod p) (EisResidue p)) hr
    simpa [hR] using this
  have hprod : (EisResidue.omega p - R) * (EisResidue.omega p + R + 1) = 0 := by
    linear_combination hω - hR2
  have hRs : R = r • (1 : EisResidue p) := by rw [hR, Algebra.smul_def, mul_one]
  obtain ⟨c, _, hu⟩ := EisResidue.coords_unique p 0
  have e0 := hu (0, 0) (by simp)
  rcases mul_eq_zero.mp hprod with h | h
  · have e1 := hu (-r, 1) (by
      show (0 : EisResidue p) = (-r) • 1 + (1 : ZMod p) • EisResidue.omega p
      rw [one_smul, neg_smul, ← hRs]; linear_combination -h)
    have := congrArg Prod.snd (e1.trans e0.symm)
    simp at this
  · have e1 := hu (-(r + 1), -1) (by
      show (0 : EisResidue p) = (-(r + 1)) • 1 + (-1 : ZMod p) • EisResidue.omega p
      rw [neg_smul, neg_smul, one_smul, add_smul, one_smul, ← hRs]; linear_combination h)
    have := congrArg Prod.snd (e1.trans e0.symm)
    simp at this

/-- For a prime `p ≡ 1 (mod 3)`, `X² + X + 1` has a root in `𝔽_p`. -/
theorem exists_root_of_mod_three_eq_one {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ r : ZMod p, r ^ 2 + r + 1 = 0 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by rw [ZMod.card_units]; omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hu3 : (u : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : ZMod p) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu; omega
  refine ⟨u, ?_⟩
  have hsub : (u : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have : ((u : ZMod p) - 1) * ((u : ZMod p) ^ 2 + u + 1) = 0 := by
    linear_combination hu3
  exact (mul_eq_zero.mp this).resolve_left hsub

theorem one_root_three : (1 : ZMod 3) ^ 2 + 1 + 1 = 0 := by decide

/-- **For a prime `p`, `ℤ[ω]/(p)` is a field iff `p ≡ 2 (mod 3)`.** -/
theorem eisResidue_isField_iff (p : ℕ) [Fact p.Prime] :
    IsField (EisResidue p) ↔ p % 3 = 2 := by
  constructor
  · intro hF
    by_contra h
    have : p % 3 = 0 ∨ p % 3 = 1 := by omega
    rcases this with h0 | h1
    · have hp3 : p = 3 := by
        rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0)
          with h' | h' <;> omega
      subst hp3
      exact not_isField_of_root (1 : ZMod 3) one_root_three hF
    · obtain ⟨r, hr⟩ := exists_root_of_mod_three_eq_one h1
      exact not_isField_of_root r hr hF
  · intro h
    haveI : Fact (p % 3 = 2) := ⟨h⟩
    exact Field.toIsField _

/-! ## `ℤ/Π`: field vs non-field -/

theorem zmod_prime_unique (p : ℕ) [Fact p.Prime] (a b : ZMod p) (ha : a ≠ 0) :
    ∃! x : ZMod p, a * x = b :=
  ⟨a⁻¹ * b, by field_simp, fun y hy => by rw [← hy]; field_simp⟩

/-- For composite `n`, some `a ≠ 0` has no inverse, and `a x = 0` has several solutions. -/
theorem zmod_composite_bad {n : ℕ} (h1 : 1 < n) (hn : ¬ n.Prime) :
    ∃ a : ZMod n, a ≠ 0 ∧ (¬ ∃ x : ZMod n, a * x = 1) ∧
      ∃ x y : ZMod n, x ≠ y ∧ a * x = 0 ∧ a * y = 0 := by
  obtain ⟨m, ⟨k, hk⟩, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 h1 hn
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have hkn : k < n := by
    rw [hk]; nlinarith
  have ne : ∀ j : ℕ, 0 < j → j < n → ((j : ℕ) : ZMod n) ≠ 0 := fun j hj hjn h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hj h) (by omega)
  have hmk : ((m : ℕ) : ZMod n) * (k : ℕ) = 0 := by
    rw [← Nat.cast_mul, ← hk, ZMod.natCast_self]
  refine ⟨m, ne m (by omega) hmn, ?_, 0, k, ?_, by simp, hmk⟩
  · rintro ⟨x, hx⟩
    apply ne k hk0 hkn
    calc ((k : ℕ) : ZMod n) = (m * x) * k := by rw [hx, one_mul]
      _ = (m * k) * x := by ring
      _ = 0 := by rw [hmk, zero_mul]
  · exact fun h => ne k hk0 hkn h.symm

/-! ## The six-fold symmetry condition -/

/-- The specification's rule. -/
def specRule (N : ℕ) : Prop := N % 36 = 0 ∨ N % 36 = 1 ∨ N % 36 = 35

/-- The correct rule for primes `p ≥ 5`. -/
def trueRule (p : ℕ) : Prop := p % 36 = 1 ∨ p % 36 = 17 ∨ p % 36 = 35

instance (N : ℕ) : Decidable (specRule N) := by unfold specRule; infer_instance
instance (N : ℕ) : Decidable (trueRule N) := by unfold trueRule; infer_instance

/-- **Inert primes** `p ≡ 2 (mod 3)`, `p ≥ 5`: the 60° turn fixes all colours of
`ℤ[ω]/(p)` iff `p ≡ 17` or `35 (mod 36)`. -/
theorem inert_symmetry_iff (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (hp : 5 ≤ p) :
    (∀ x : EisResidue p, x ≠ 0 →
      colourIndex (1 + EisResidue.omega p) ((1 + EisResidue.omega p) * x) =
        colourIndex (1 + EisResidue.omega p) x) ↔ (p % 36 = 17 ∨ p % 36 = 35) := by
  rw [inert_colours_fixed_iff p hp]
  have h3 : p % 3 = 2 := Fact.out
  have h2 : p % 2 = 1 := by
    by_contra h
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega))
      with h' | h' <;> omega
  omega

/-- **Split primes** `p ≡ 1 (mod 3)`: the residue field of a prime of norm `p` is `𝔽_p`, and
for any primitive sixth root of unity `ζ` the turn fixes all colours iff `p ≡ 1 (mod 36)`. -/
theorem split_symmetry_iff (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ 6) :
    (∀ x : ZMod p, x ≠ 0 → colourIndex ζ (ζ * x) = colourIndex ζ x) ↔ p % 36 = 1 := by
  have h2 : p % 2 = 1 := by
    by_contra h
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega))
      with h' | h' <;> omega
  have h6 : 6 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  rw [colours_fixed_iff hζ h6, ZMod.card]
  have : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  omega

/-- Split primes do have a primitive sixth root of unity in `𝔽_p` (so the statement above is
not vacuous). -/
theorem split_exists_zeta6 (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ 6 := by
  obtain ⟨r, hr⟩ := exists_root_of_mod_three_eq_one hp
  have hp7 : 7 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    by_contra h
    have h4 : p = 4 := by omega
    subst h4; exact absurd (Fact.out : Nat.Prime 4) (by decide)
  have ne : ∀ j : ℕ, 0 < j → j < p → ((j : ℕ) : ZMod p) ≠ 0 := fun j hj hjn h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hj h) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast ne 2 (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast ne 3 (by norm_num) (by omega)
  exact ⟨-r, isPrimitiveRoot_neg_omega hr h2 h3⟩

/-- The two cases combined, in terms of `p mod 36` alone. -/
theorem prime_symmetry_iff (p : ℕ) (hp : p.Prime) :
    (p % 3 = 2 → (p % 9 = 8 ↔ trueRule p)) ∧ (p % 3 = 1 → (p % 36 = 1 ↔ trueRule p)) := by
  unfold trueRule
  rcases hp.eq_two_or_odd with h2 | h2
  · subst h2; decide
  · constructor <;> intro h <;> omega

/-- The specification's rule is wrong at `p = 17`: it predicts failure, but `ℤ[ω]/(17)` has
full six-fold colour symmetry. -/
theorem spec_rule_wrong_at_17 :
    ¬ specRule 17 ∧ trueRule 17 ∧ 17 % 9 = 8 := by decide

/-- `Π ≡ 0 (mod 36)` never happens for a prime. -/
theorem spec_rule_zero_never_prime (N : ℕ) (h : N % 36 = 0) : ¬ N.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd 2 (by omega) with h' | h' <;> omega

/-- On primes, the specification's rule and the correct rule differ exactly when
`p ≡ 17 (mod 36)`. -/
theorem spec_vs_true (p : ℕ) (hp : p.Prime) :
    (specRule p ↔ trueRule p) ↔ p % 36 ≠ 17 := by
  have h0 := spec_rule_zero_never_prime p
  unfold specRule trueRule
  constructor
  · intro h h17; have := h.2 (Or.inr (Or.inl h17)); omega
  · intro h
    constructor
    · rintro (h' | h' | h')
      · exact absurd hp (h0 h')
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rintro (h' | h' | h')
      · exact Or.inr (Or.inl h')
      · exact absurd h' h
      · exact Or.inr (Or.inr h')

/-- **Holonomy and symmetry are independent** (`p = 5, 71, 7, 37`). -/
theorem holonomy_independent_of_symmetry :
    (residual 71 ≠ 0 ∧ trueRule 71) ∧ (residual 5 ≠ 0 ∧ ¬ trueRule 5) ∧
    (residual 37 = 0 ∧ trueRule 37) ∧ (residual 7 = 0 ∧ ¬ trueRule 7) := by
  simp only [residual_eq]
  refine ⟨⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩,
    ⟨by norm_num, by decide⟩⟩

/-! ## The recomputed block for every prime `5 ≤ p < 110` -/

/-- Columns: `p`, `6ε = (p-1) mod 6`, `3ρ`, `p mod 36`, the specification's symmetry rule,
the correct symmetry rule (`ε = (6ε)/6` by `errorTerm_eq'`, `ρ` by `residual_eq`). -/
theorem recompute_table :
    ((List.range 110).filter (fun p => p.Prime ∧ 5 ≤ p)).map (fun p =>
      (p, (p - 1) % 6, (if p % 3 = 2 then 1 else 0), p % 36, decide (specRule p),
        decide (trueRule p))) =
    [(5, 4, 1, 5, false, false), (7, 0, 0, 7, false, false), (11, 4, 1, 11, false, false),
     (13, 0, 0, 13, false, false), (17, 4, 1, 17, false, true), (19, 0, 0, 19, false, false),
     (23, 4, 1, 23, false, false), (29, 4, 1, 29, false, false), (31, 0, 0, 31, false, false),
     (37, 0, 0, 1, true, true), (41, 4, 1, 5, false, false), (43, 0, 0, 7, false, false),
     (47, 4, 1, 11, false, false), (53, 4, 1, 17, false, true), (59, 4, 1, 23, false, false),
     (61, 0, 0, 25, false, false), (67, 0, 0, 31, false, false), (71, 4, 1, 35, true, true),
     (73, 0, 0, 1, true, true), (79, 0, 0, 7, false, false), (83, 4, 1, 11, false, false),
     (89, 4, 1, 17, false, true), (97, 0, 0, 25, false, false), (101, 4, 1, 29, false, false),
     (103, 0, 0, 31, false, false), (107, 4, 1, 35, true, true), (109, 0, 0, 1, true, true)] := by
  decide

/-- Composite moduli give the other error terms: `ε(8) = 1/6`, `ρ(8) = 1/3`;
`ε(10) = 1/2`, `ρ(10) = 0`; `ε(9) = 2/6`, `ρ(9) = 0`. -/
theorem composite_examples :
    errorTerm 8 = 1 / 6 ∧ residual 8 = 1 / 3 ∧ errorTerm 10 = 1 / 2 ∧ residual 10 = 0 ∧
      errorTerm 9 = 1 / 3 ∧ residual 9 = 0 := by
  simp only [errorTerm_eq', residual_eq]; norm_num

end ParamSpec
