module

public import Mathlib
@[expose] public section

/-!
# Fractional and irrational dimensions (including `π`- and circle-sized ones)

Companion to the infographic `docs/k_fractional/fractional_dimensions.svg` and the write-up
`docs/K_FRACTIONAL_DIMENSIONS.md`. It follows the earlier negative-degree figure
(`RequestProject/AZ/NegativeDegrees.lean`).

A *degree* in K-theory (`KO_n`, `K_n`) is always an integer: there is no `KO_{1/2}` or `KO_π`.
"Dimension" becomes fractional or irrational in other places, and each panel of the figure is
one of them. **Project rule: content ≠ proof.** Each section below says which part is checked
here and which part is only cited.

1. **Fractions `k/n` (matrix algebras, UHF algebras).** With the normalised trace, a projection
   in `M_n(ℂ)` has dimension `k/n`. In the CAR algebra `M_{2^∞}` the dimensions are the dyadic
   rationals `ℤ[1/2] ∩ [0,1]` (Glimm/Elliott, cited). Checked: `matrixDim_mem`,
   `dyadic_dense` (the dyadic values are dense in `ℝ`).
2. **Rotation algebras `A_θ` (rational vs. irrational, `θ = π`).** By Pimsner–Voiculescu and
   Rieffel (cited) the trace sends `K₀(A_θ) ≅ ℤ²` onto `ℤ + θℤ`, and every value in
   `(ℤ + θℤ) ∩ [0,1]` is the trace of a projection. Checked: `rotDims θ` is dense iff `θ` is
   irrational (`rotDims_dense_iff`); for `θ = p/q` it is exactly `(1/q)ℤ` (`rotDims_rat`);
   for `θ = π` the map `(a, b) ↦ a + bπ` is injective (`rotDim_pi_injective`, rank 2) and
   `π - 3 ∈ (0, 1)` lies in `ℤ + πℤ` (`pi_sub_three_mem`).
3. **Fractal (similarity) dimension `log N / log r`.** Checked: it solves Moran's equation
   `N · r^{-s} = 1` (`simDim_moran`); it is irrational whenever `N, r ≥ 2` are coprime
   (`simDim_irrational_of_coprime`): Cantor `log 2/log 3`, Sierpiński `log 3/log 2`,
   Koch `log 4/log 3`; and it can be an honest fraction: `log 2/log 4 = 1/2`,
   `log 4/log 8 = 2/3` (`simDim_two_four`, `simDim_four_eight`). That the Hausdorff dimension
   of the attractor equals the similarity dimension (Moran/Hutchinson, open set condition) is
   cited, not proved here. A fractal of dimension exactly `π`: `2⁴ = 16` corner copies of the
   unit 4-cube scaled by `c = 16^{-1/π} ≈ 0.414` (`piDim_fractal`: Moran's equation
   `16 c^π = 1`, unique solution `cornerRatio_moran_unique`, and `c < 1/2`, which makes the
   copies disjoint); `twoPiDim_fractal` does the same for `2π` in `ℝ⁷`.
4. **Circle-sized dimensions `2 cos(π/n)`.** Quantum dimensions of `SU(2)` at level `n - 2`
   and Jones' index values `4 cos²(π/n)`. Checked: the values for `n = 2, 3, 4, 5, 6` are
   `0, 1, √2, φ, √3` (`qdim_two` … `qdim_six`), with `φ² = φ + 1` (the Fibonacci fusion rule
   `τ ⊗ τ = 1 ⊕ τ` at the level of dimensions, `qdim_five_sq`); `√2, φ, √3` are irrational;
   the index values are strictly increasing in `n ≥ 2` (`jonesIndex_strictMono`), stay below
   `4` (`jonesIndex_lt_four`) and tend to `4` (`jonesIndex_tendsto`). Jones' theorem that these
   are the only possible subfactor indices below `4` is cited, not proved.
5. **Dimension `d = π` for the unit ball.** `ballVol d = π^{d/2} / Γ(d/2 + 1)` makes sense for
   every real `d`. Checked: for every natural `n ≥ 1` it is the Lebesgue volume of the unit
   ball in `ℝⁿ` (`ballVol_eq_volume`); `ballVol 0 = 1`, `ballVol 1 = 2`, `ballVol 2 = π`
   (the disc), `ballVol 3 = 4π/3`; `ballVol d > 0` for `d ≥ 0`, in particular at `d = π`
   (`ballVol_pi_pos`). There is no space `ℝ^π` here: `ballVol π` is the value of an
   interpolating formula, not the volume of anything.
-/

open Real

namespace AZ.FracDim

/-! ## 1. Fractions `k/n` -/

/-- Normalised-trace dimension of a rank-`k` projection in `M_n(ℂ)`. -/
noncomputable def matrixDim (k n : ℕ) : ℝ := (k : ℝ) / n

/-- Rank-`k` projections in `M_n(ℂ)`, `k ≤ n`, have normalised dimension in `[0, 1]`. -/
theorem matrixDim_mem {k n : ℕ} (hk : k ≤ n) : matrixDim k n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold matrixDim
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hk

/-- Every rational number in `[0,1]` is a matrix dimension `k/n`. -/
theorem rat_eq_matrixDim (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∃ k n : ℕ, k ≤ n ∧ 0 < n ∧ matrixDim k n = q := by
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  refine ⟨q.num.toNat, q.den, ?_, q.den_pos, ?_⟩
  · have hd : (0:ℚ) < q.den := by exact_mod_cast q.den_pos
    have h := Rat.num_div_den q
    rw [← h, div_le_one hd] at h1
    have : q.num ≤ q.den := by exact_mod_cast h1
    omega
  · unfold matrixDim
    have : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum
    rw [this]
    push_cast [Rat.cast_def]; rfl

/-- The dyadic dimensions `k / 2^m` (the values of the trace on `K₀` of the CAR algebra) are
dense in `ℝ`. -/
theorem dyadic_dense {a b : ℝ} (hab : a < b) :
    ∃ k : ℤ, ∃ m : ℕ, a < (k : ℝ) / 2 ^ m ∧ (k : ℝ) / 2 ^ m < b := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hab) (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨⌊a * 2 ^ m⌋ + 1, m, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]
    push_cast; exact Int.lt_floor_add_one _
  · rw [div_lt_iff₀ (by positivity)]
    have h1 := Int.floor_le (a * 2 ^ m)
    have h2 : (1/2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
    push_cast
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m]

/-! ## 2. Rotation algebras: `ℤ + θℤ` -/

/-- The candidate dimension group `ℤ + θℤ ⊆ ℝ` of the rotation algebra `A_θ`. -/
def rotDims (θ : ℝ) : AddSubgroup ℝ := AddSubgroup.closure {1, θ}

theorem mem_rotDims_iff (θ x : ℝ) : x ∈ rotDims θ ↔ ∃ a b : ℤ, x = a + b * θ := by
  unfold rotDims
  rw [show ({1, θ} : Set ℝ) = {1} ∪ {θ} by rfl, AddSubgroup.closure_union,
    AddSubgroup.mem_sup]
  simp only [AddSubgroup.mem_closure_singleton]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, by simp [zsmul_eq_mul]⟩

/-- `ℤ + θℤ` is dense in `ℝ` exactly when `θ` is irrational. -/
theorem rotDims_dense_iff (θ : ℝ) : Dense (rotDims θ : Set ℝ) ↔ Irrational θ := by
  have := @dense_addSubgroupClosure_pair_iff θ 1
  rw [div_one] at this
  rw [← this, rotDims, Set.pair_comm]

/-- For `θ = π` the dimensions are dense. -/
theorem rotDims_pi_dense : Dense (rotDims π : Set ℝ) := (rotDims_dense_iff π).2 irrational_pi

/-- For rational `θ = p/q` (`q > 0`, `p, q` coprime) the dimensions are exactly `(1/q)ℤ`. -/
theorem rotDims_rat (p : ℤ) (q : ℕ) (hq : 0 < q) (hpq : IsCoprime p q) (x : ℝ) :
    x ∈ rotDims ((p : ℝ) / q) ↔ ∃ m : ℤ, x = m / q := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [mem_rotDims_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a * q + b * p, by push_cast; field_simp⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨u, v, huv⟩ := hpq
    refine ⟨m * v, m * u, ?_⟩
    have : ((u * p + v * q : ℤ) : ℝ) = 1 := by exact_mod_cast huv
    push_cast at this ⊢
    field_simp
    linear_combination (-(m:ℝ)) * this

/-- `(a, b) ↦ a + bπ` is injective on `ℤ²`: `ℤ + πℤ` is free of rank 2. -/
theorem rotDim_pi_injective {a b c d : ℤ} (h : (a : ℝ) + b * π = c + d * π) :
    a = c ∧ b = d := by
  by_cases hbd : b = d
  · subst hbd; refine ⟨?_, rfl⟩; exact_mod_cast (by linarith : (a:ℝ) = c)
  · exfalso
    have hne : ((b:ℝ) - d) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hbd)
    have : π = ((c - a : ℤ) : ℝ) / ((b - d : ℤ) : ℝ) := by
      push_cast; field_simp; linarith
    exact irrational_pi.ne_rat ((c - a : ℤ) / (b - d : ℤ) : ℚ) (by rw [this]; push_cast; ring)

/-- `π - 3 ≈ 0.14159` is a dimension in `(ℤ + πℤ) ∩ (0, 1)`. -/
theorem pi_sub_three_mem : π - 3 ∈ rotDims π ∧ π - 3 ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨(mem_rotDims_iff _ _).2 ⟨-3, 1, by push_cast; ring⟩, ?_, ?_⟩
  · linarith [pi_gt_three]
  · linarith [pi_lt_four]

/-! ## 3. Similarity dimension `log N / log r` -/

/-- Similarity dimension of a self-similar set made of `N` copies scaled by `1/r`. -/
noncomputable def simDim (N r : ℕ) : ℝ := Real.log N / Real.log r

/-- Moran's equation `N · r^{-s} = 1` holds for `s = simDim N r`. -/
theorem simDim_moran {N r : ℕ} (hN : 0 < N) (hr : 1 < r) :
    (N : ℝ) * (r : ℝ) ^ (-simDim N r) = 1 := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr)
  rw [Real.rpow_def_of_pos hr0, simDim]
  rw [show Real.log r * -(Real.log N / Real.log r) = - Real.log N by field_simp]
  rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hN)]
  field_simp

/-- If `N, r ≥ 2` are coprime then `log N / log r` is irrational. -/
theorem simDim_irrational_of_coprime {N r : ℕ} (hN : 2 ≤ N) (hr : 2 ≤ r)
    (hc : Nat.Coprime N r) : Irrational (simDim N r) := by
  rintro ⟨s, hs⟩
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlr : 0 < Real.log r := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hd : (0:ℝ) < s.den := by exact_mod_cast s.den_pos
  have hs' : (s.num : ℝ) / s.den = Real.log N / Real.log r := by
    rw [simDim] at hs; rw [← hs]; push_cast [Rat.cast_def]; rfl
  have key : (s.den : ℝ) * Real.log N = s.num * Real.log r := by
    field_simp at hs'; linarith
  have hnum : 0 < s.num := by
    have : (0:ℝ) < s.num * Real.log r := by rw [← key]; positivity
    have : (0:ℝ) < s.num := pos_of_mul_pos_left this hlr.le
    exact_mod_cast this
  have hpow : (N ^ s.den : ℕ) = r ^ s.num.toNat := by
    have h1 : ((N ^ s.den : ℕ) : ℝ) = ((r ^ s.num.toNat : ℕ) : ℝ) := by
      apply Real.log_injOn_pos
      · simp only [Set.mem_Ioi]; positivity
      · simp only [Set.mem_Ioi]; positivity
      push_cast
      rw [Real.log_pow, Real.log_pow, key]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm
    exact_mod_cast h1
  have hcop : Nat.Coprime (N ^ s.den) (r ^ s.num.toNat) := Nat.Coprime.pow _ _ hc
  rw [hpow, Nat.coprime_self] at hcop
  have : 1 ≤ s.num.toNat := by omega
  have : r ≤ r ^ s.num.toNat := Nat.le_self_pow (by omega) r
  omega

/-- Middle-thirds Cantor set: `log 2 / log 3` is irrational. -/
theorem simDim_cantor_irrational : Irrational (simDim 2 3) :=
  simDim_irrational_of_coprime le_rfl (by norm_num) (by norm_num)

/-- Sierpiński triangle: `log 3 / log 2` is irrational. -/
theorem simDim_sierpinski_irrational : Irrational (simDim 3 2) :=
  simDim_irrational_of_coprime (by norm_num) le_rfl (by norm_num)

/-- Koch curve: `log 4 / log 3` is irrational. -/
theorem simDim_koch_irrational : Irrational (simDim 4 3) :=
  simDim_irrational_of_coprime (by norm_num) (by norm_num) (by norm_num)

/-- Two pieces scaled by `1/4`: dimension exactly `1/2`. -/
theorem simDim_two_four : simDim 2 4 = 1 / 2 := by
  rw [simDim, show ((4:ℕ):ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  push_cast; field_simp

/-- Four pieces scaled by `1/8`: dimension exactly `2/3`. -/
theorem simDim_four_eight : simDim 4 8 = 2 / 3 := by
  rw [simDim, show ((4:ℕ):ℝ) = 2 ^ 2 by norm_num, show ((8:ℕ):ℝ) = 2 ^ 3 by norm_num,
    Real.log_pow, Real.log_pow]
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  push_cast; field_simp

/-- The Cantor dimension lies strictly between `0` and `1`. -/
theorem simDim_cantor_mem : simDim 2 3 ∈ Set.Ioo (0 : ℝ) 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [simDim]; push_cast
  exact ⟨by positivity, (div_lt_one (by linarith)).2 h23⟩

/-! ### A fractal of similarity dimension exactly `π` (or `2π`)

Take the unit cube in `ℝᵏ` and keep `2ᵏ` corner copies scaled by `c = 2^{-k/s}`. Moran's
equation `2ᵏ · c^t = 1` then has the unique solution `t = s`, and `c < 1/2` (which holds when
`s < k`) is what makes the corner copies pairwise disjoint, so the open set condition holds.
With `k = 4, s = π` this is a self-similar subset of `ℝ⁴` of similarity dimension `π`; with
`k = 7, s = 2π` one of dimension `2π`. Only the two numerical facts (Moran's equation with its
unique solution, and `c < 1/2`) are checked here; that similarity dimension equals Hausdorff
dimension under the open set condition is Moran/Hutchinson, cited. -/

/-- Scaling ratio `2^{-k/s}` for `2ᵏ` corner copies in `ℝᵏ`. -/
noncomputable def cornerRatio (k : ℕ) (s : ℝ) : ℝ := (2 : ℝ) ^ (-(k : ℝ) / s)

theorem cornerRatio_pos (k : ℕ) (s : ℝ) : 0 < cornerRatio k s := by
  unfold cornerRatio; positivity

lemma cornerRatio_rpow (k : ℕ) (s t : ℝ) :
    cornerRatio k s ^ t = (2 : ℝ) ^ (-(k : ℝ) * t / s) := by
  rw [cornerRatio, ← Real.rpow_mul (by norm_num)]; ring_nf

/-- Moran's equation `2ᵏ · c^s = 1` for `c = cornerRatio k s`. -/
theorem cornerRatio_moran (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (2 : ℝ) ^ k * cornerRatio k s ^ s = 1 := by
  rw [cornerRatio_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
  rw [show (k : ℝ) + -(k : ℝ) * s / s = 0 by field_simp; ring, Real.rpow_zero]

/-- `s` is the only solution of Moran's equation. -/
theorem cornerRatio_moran_unique (k : ℕ) (hk : 0 < k) {s t : ℝ} (hs : 0 < s)
    (ht : (2 : ℝ) ^ k * cornerRatio k s ^ t = 1) : t = s := by
  rw [cornerRatio_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)] at ht
  have h := congrArg (Real.logb 2) ht
  rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_one] at h
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  field_simp at h
  have : (k:ℝ) * (s - t) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

/-- For `s < k` the ratio is below `1/2`, so the `2ᵏ` corner copies are disjoint. -/
theorem cornerRatio_lt_half (k : ℕ) {s : ℝ} (hs : 0 < s) (hsk : s < k) :
    cornerRatio k s < 1 / 2 := by
  rw [cornerRatio, show (1/2 : ℝ) = 2 ^ (-1 : ℝ) by norm_num]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  rw [neg_div, neg_lt_neg_iff, one_lt_div hs]; exact hsk

/-- A `π`-dimensional corner fractal in `ℝ⁴`: Moran's equation and `c < 1/2`. -/
theorem piDim_fractal :
    (2 : ℝ) ^ 4 * cornerRatio 4 π ^ π = 1 ∧ cornerRatio 4 π < 1 / 2 :=
  ⟨cornerRatio_moran 4 pi_pos, cornerRatio_lt_half 4 pi_pos (by push_cast; linarith [pi_lt_four])⟩

/-- The same ratio `c = 16^{-1/π}` with only the `4` corners of a square gives a planar set of
similarity dimension `π/2` (the picture drawn in the figure). -/
theorem cornerRatio_four_pi_eq : cornerRatio 4 π = cornerRatio 2 (π / 2) := by
  unfold cornerRatio; congr 1; field_simp; norm_num

theorem piHalfDim_planar :
    (2 : ℝ) ^ 2 * cornerRatio 4 π ^ (π / 2) = 1 ∧ cornerRatio 4 π < 1 / 2 := by
  rw [cornerRatio_four_pi_eq]
  exact ⟨cornerRatio_moran 2 (by positivity),
    cornerRatio_lt_half 2 (by positivity) (by push_cast; linarith [pi_lt_four])⟩

/-- A `2π`-dimensional ("circumference-sized") corner fractal in `ℝ⁷`. -/
theorem twoPiDim_fractal :
    (2 : ℝ) ^ 7 * cornerRatio 7 (2 * π) ^ (2 * π) = 1 ∧ cornerRatio 7 (2 * π) < 1 / 2 :=
  ⟨cornerRatio_moran 7 (by positivity),
    cornerRatio_lt_half 7 (by positivity) (by push_cast; linarith [pi_lt_d2])⟩

/-! ## 4. Circle-sized dimensions `2 cos(π/n)` -/

/-- Quantum dimension `2 cos(π/n)`. -/
noncomputable def qdim (n : ℕ) : ℝ := 2 * Real.cos (π / n)

/-- Jones index value `4 cos²(π/n)`. -/
noncomputable def jonesIndex (n : ℕ) : ℝ := qdim n ^ 2

theorem qdim_two : qdim 2 = 0 := by simp [qdim]
theorem qdim_three : qdim 3 = 1 := by simp [qdim, cos_pi_div_three]
theorem qdim_four : qdim 4 = √2 := by simp [qdim, cos_pi_div_four]; ring
theorem qdim_five : qdim 5 = goldenRatio := by simp [qdim, cos_pi_div_five, goldenRatio]; ring
theorem qdim_six : qdim 6 = √3 := by simp [qdim, cos_pi_div_six]; ring

/-- Fibonacci fusion rule at the level of dimensions: `d² = 1 + d` for `d = 2 cos(π/5)`. -/
theorem qdim_five_sq : qdim 5 ^ 2 = 1 + qdim 5 := by
  rw [qdim_five, goldenRatio_sq]; ring

theorem qdim_four_irrational : Irrational (qdim 4) := qdim_four ▸ irrational_sqrt_two
theorem qdim_five_irrational : Irrational (qdim 5) := qdim_five ▸ goldenRatio_irrational
theorem qdim_six_irrational : Irrational (qdim 6) := by
  rw [qdim_six]; exact Nat.prime_three.irrational_sqrt

/-- The Jones values for `n = 3, 4, 5, 6`: `1, 2, φ + 1, 3`. -/
theorem jonesIndex_values :
    jonesIndex 3 = 1 ∧ jonesIndex 4 = 2 ∧ jonesIndex 5 = goldenRatio + 1 ∧ jonesIndex 6 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [jonesIndex, qdim_three, qdim_four, qdim_five, qdim_six]
  · norm_num
  · norm_num
  · rw [goldenRatio_sq]
  · norm_num

lemma cos_pi_div_mem {n : ℕ} (hn : 2 ≤ n) : 0 ≤ Real.cos (π / n) ∧ Real.cos (π / n) < 1 := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < π / n := by positivity
  have hle : π / n ≤ π / 2 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) hn'
  refine ⟨cos_nonneg_of_mem_Icc ⟨by linarith, hle⟩, ?_⟩
  rw [← cos_zero]
  exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [pi_pos]) hpos

theorem jonesIndex_lt_four (n : ℕ) (hn : 2 ≤ n) : jonesIndex n < 4 := by
  obtain ⟨h0, h1⟩ := cos_pi_div_mem hn
  simp only [jonesIndex, qdim]
  nlinarith

theorem jonesIndex_strictMono {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    jonesIndex m < jonesIndex n := by
  obtain ⟨h0, -⟩ := cos_pi_div_mem hm
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m:ℝ) < n := by exact_mod_cast hmn
  have hn0 : (0:ℝ) < n := by linarith
  have hlt : π / n < π / m := div_lt_div_of_pos_left pi_pos (by linarith) hmn'
  have hle : π / m ≤ π := div_le_self pi_pos.le (by linarith)
  have hc : Real.cos (π / m) < Real.cos (π / n) :=
    cos_lt_cos_of_nonneg_of_le_pi (by positivity) hle hlt
  simp only [jonesIndex, qdim]
  nlinarith

theorem jonesIndex_tendsto :
    Filter.Tendsto jonesIndex Filter.atTop (nhds 4) := by
  have h0 : Filter.Tendsto (fun n : ℕ => π / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat π
  have hc : Continuous (fun x : ℝ => (2 * Real.cos x) ^ 2) := by fun_prop
  have := (hc.tendsto 0).comp h0
  rw [show (4:ℝ) = (2 * Real.cos 0) ^ 2 by norm_num]
  exact this

/-! ## 5. Unit-ball volume in real dimension `d` -/

/-- `π^{d/2} / Γ(d/2 + 1)`, defined for every real `d`. -/
noncomputable def ballVol (d : ℝ) : ℝ := π ^ (d / 2) / Real.Gamma (d / 2 + 1)

lemma sqrt_pi_pow (n : ℕ) : √π ^ n = π ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul pi_pos.le]
  ring_nf

/-- For natural `n ≥ 1` it is the Lebesgue volume of the unit ball of `ℝⁿ`. -/
theorem ballVol_eq_volume (n : ℕ) [NeZero n] :
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) =
      ENNReal.ofReal (ballVol n) := by
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    sqrt_pi_pow, ballVol]

theorem ballVol_zero : ballVol 0 = 1 := by simp [ballVol]

lemma Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3/2 : ℝ) = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]; ring

theorem ballVol_one : ballVol 1 = 2 := by
  rw [ballVol, show (1:ℝ)/2 + 1 = 3/2 by norm_num, Gamma_three_halves, ← Real.sqrt_eq_rpow]
  have : 0 < √π := Real.sqrt_pos.2 pi_pos
  field_simp

theorem ballVol_two : ballVol 2 = π := by
  rw [ballVol, show (2:ℝ)/2 + 1 = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero]
  simp

theorem ballVol_three : ballVol 3 = 4 * π / 3 := by
  rw [ballVol, show (3:ℝ)/2 + 1 = 3/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Gamma_three_halves, show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add pi_pos,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  have : 0 < √π := Real.sqrt_pos.2 pi_pos
  field_simp
  ring

theorem ballVol_pos {d : ℝ} (hd : 0 ≤ d) : 0 < ballVol d :=
  div_pos (Real.rpow_pos_of_pos pi_pos _) (Real.Gamma_pos_of_pos (by linarith))

theorem ballVol_pi_pos : 0 < ballVol π := ballVol_pos pi_pos.le

end AZ.FracDim
