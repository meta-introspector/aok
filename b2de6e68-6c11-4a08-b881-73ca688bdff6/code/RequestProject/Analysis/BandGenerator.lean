/-
# The seven-band generator, analysed
thanks to @fabianfranz @fabianx-ai
https://x.com/fabianfranz/status/2102798746513707438?s=20
A generator was submitted with the observation that it "creates exactly seven bands":

```python
def rand_sin(x):  return (math.sin(x) + math.sinh(x)) % 1
def rand_cos(x):  return math.cosh(math.cos(x)) % 1
value = (rand_sin(x) + rand_cos(x)) / 2
```

The bands are real, and they have an exact description.  This module proves it.

* **The wave is strictly increasing.**  `wave x = sin x + sinh x` has derivative
  `cos x + cosh x`, which is positive everywhere because `cosh x ≥ 1 ≥ -cos x`, with equality
  impossible.  So `rand_sin = Int.fract ∘ wave` restarts exactly once per integer crossed,
  and the bands are the level sets `⌊wave x⌋ = n`.
* **Hence the band count is arithmetic, not luck.**  Over `[a, b]` the bands are indexed by
  the integers in `[⌊wave a⌋, ⌊wave b⌋]`, so there are `⌊wave b⌋ - ⌊wave a⌋ + 1` of them
  (`bandCount_eq`, `mem_bandIndices_iff`).  Seven bands over `[0, b]` happens exactly when
  `6 ≤ wave b < 7` (`seven_bands_iff`), that is for `b` in the window `[b₆, b₇)` cut out by
  the two solutions of `wave b = 6` and `wave b = 7`, both of which lie strictly between 2
  and 3 (`seven_band_window`).  So "exactly seven bands" is a statement about the plotting
  range, and the range that produces it is an interval inside `(2, 3)` — numerically
  `b₆ ≈ 2.3702`, `b₇ ≈ 2.5638`.
* **The cosine half contributes no bands at all.**  `cosh (cos x)` never leaves `[1, cosh 1]`,
  so its fractional part is just `cosh (cos x) - 1` (`randCos_eq`) — a *continuous* function
  (`continuous_randCos`) with range exactly `[0, cosh 1 - 1]`, about `[0, 0.5431]`.  It warps
  the bands; it cannot create or destroy one.
* **Consequently the generator is not uniform on `[0,1)`.**  The average never reaches
  `cosh 1 / 2 ≈ 0.7715` (`randAvg_lt_cosh_one_div_two`, `randAvg_lt_seventy_eight_hundredths`),
  so roughly the top quarter of the unit interval is never produced.  Anything downstream
  that assumes a uniform `[0,1)` sample is assuming something false.

What is *not* claimed here: nothing about equidistribution, and nothing about the reported
figure `0.69` for the frequency of `rand_sin x > rand_cos x`.  That number is a measurement
of a floating-point program, not of these functions; see `data/band_generator.md`.

STATUS: Lens A (kernel-checked, no `sorry`, no new axioms).  Lens B absent: category (b).
-/
import Mathlib

namespace RequestProject.Analysis

open Real

/-! ## The two halves of the generator -/

/-- The increasing wave underneath the first generator: `sin x + sinh x`. -/
noncomputable def wave (x : ℝ) : ℝ := Real.sin x + Real.sinh x

/-- `rand_sin`: the fractional part of the wave. -/
noncomputable def randSin (x : ℝ) : ℝ := Int.fract (wave x)

/-- `rand_cos`: the fractional part of `cosh (cos x)`. -/
noncomputable def randCos (x : ℝ) : ℝ := Int.fract (Real.cosh (Real.cos x))

/-- The published generator: the average of the two. -/
noncomputable def randAvg (x : ℝ) : ℝ := (randSin x + randCos x) / 2

/-! ## The cosine half never wraps -/

theorem one_le_cosh_cos (x : ℝ) : 1 ≤ Real.cosh (Real.cos x) := Real.one_le_cosh _

theorem cosh_cos_le_cosh_one (x : ℝ) : Real.cosh (Real.cos x) ≤ Real.cosh 1 := by
  rw [Real.cosh_le_cosh]
  simpa using Real.abs_cos_le_one x

/-- `cosh 1 < 2`, so `cosh (cos x)` lives in `[1, 2)` and its floor is always 1. -/
theorem cosh_one_lt_two : Real.cosh 1 < 2 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [Real.cosh_eq]
  linarith

theorem floor_cosh_cos (x : ℝ) : ⌊Real.cosh (Real.cos x)⌋ = 1 := by
  rw [Int.floor_eq_iff]
  refine ⟨by simp [one_le_cosh_cos x], ?_⟩
  push_cast
  linarith [cosh_cos_le_cosh_one x, cosh_one_lt_two]

/-- **The cosine half is not a wrap at all**: its "mod 1" is a plain subtraction of 1. -/
theorem randCos_eq (x : ℝ) : randCos x = Real.cosh (Real.cos x) - 1 := by
  simp [randCos, Int.fract, floor_cosh_cos x]

/-- Hence it is continuous — it can warp a band, but it can never start a new one. -/
theorem continuous_randCos : Continuous randCos := by
  have : randCos = fun x => Real.cosh (Real.cos x) - 1 := funext randCos_eq
  rw [this]
  exact (Real.continuous_cosh.comp Real.continuous_cos).sub continuous_const

theorem randCos_nonneg (x : ℝ) : 0 ≤ randCos x := by
  rw [randCos_eq]; linarith [one_le_cosh_cos x]

/-- The cosine half covers only the bottom `cosh 1 - 1 ≈ 0.5431` of the unit interval. -/
theorem randCos_le (x : ℝ) : randCos x ≤ Real.cosh 1 - 1 := by
  rw [randCos_eq]; linarith [cosh_cos_le_cosh_one x]

/-- Both ends of that range are attained, so the bound is exact. -/
theorem randCos_zero : randCos 0 = Real.cosh 1 - 1 := by
  rw [randCos_eq, Real.cos_zero]

theorem randCos_pi_div_two : randCos (π / 2) = 0 := by
  rw [randCos_eq, Real.cos_pi_div_two, Real.cosh_zero]; ring

/-! ## The generator is not uniform on `[0,1)` -/

theorem randSin_nonneg (x : ℝ) : 0 ≤ randSin x := Int.fract_nonneg _

theorem randSin_lt_one (x : ℝ) : randSin x < 1 := Int.fract_lt_one _

/-- The published average never reaches `cosh 1 / 2 ≈ 0.7715`. -/
theorem randAvg_lt_cosh_one_div_two (x : ℝ) : randAvg x < Real.cosh 1 / 2 := by
  have h := randSin_lt_one x
  have h' := randCos_le x
  unfold randAvg
  linarith

/-- A concrete decimal form of the same statement: the top 22% of the unit interval is never
produced by this generator. -/
theorem randAvg_lt_seventy_eight_hundredths (x : ℝ) : randAvg x < 0.7716 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hlow : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hpos : 0 < Real.exp (-1) := Real.exp_pos _
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have h2 : Real.exp (-1) < 0.36788 := by nlinarith
  have hcosh : Real.cosh 1 < 1.5431 := by rw [Real.cosh_eq]; linarith
  have := randAvg_lt_cosh_one_div_two x
  linarith

theorem randAvg_nonneg (x : ℝ) : 0 ≤ randAvg x := by
  have := randSin_nonneg x
  have := randCos_nonneg x
  unfold randAvg
  linarith

/-! ## The wave is strictly increasing -/

theorem hasDerivAt_wave (x : ℝ) : HasDerivAt wave (Real.cos x + Real.cosh x) x :=
  (Real.hasDerivAt_sin x).add (Real.hasDerivAt_sinh x)

theorem deriv_wave_pos (x : ℝ) : 0 < deriv wave x := by
  rw [(hasDerivAt_wave x).deriv]
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · have h1 : 1 < Real.cosh x := Real.one_lt_cosh.mpr hx
    have h2 : -1 ≤ Real.cos x := Real.neg_one_le_cos x
    linarith

/-- **The band structure's engine**: `sin x + sinh x` is strictly increasing on all of `ℝ`,
so its fractional part wraps exactly once per integer crossed. -/
theorem strictMono_wave : StrictMono wave := strictMono_of_deriv_pos deriv_wave_pos

theorem continuous_wave : Continuous wave :=
  Real.continuous_sin.add Real.continuous_sinh

theorem wave_zero : wave 0 = 0 := by simp [wave]

/-! ## Counting the bands -/

/-- The bands met by the plot over `[a, b]`, indexed by the integer part of the wave. -/
noncomputable def bandIndices (a b : ℝ) : Finset ℤ := Finset.Icc ⌊wave a⌋ ⌊wave b⌋

/-- How many bands the plot over `[a, b]` shows. -/
noncomputable def bandCount (a b : ℝ) : ℕ := (bandIndices a b).card

/-- **The bands are exactly the integers between the two endpoint values.**  One direction is
monotonicity; the other is the intermediate value theorem. -/
theorem mem_bandIndices_iff {a b : ℝ} (hab : a ≤ b) (n : ℤ) :
    n ∈ bandIndices a b ↔ ∃ x ∈ Set.Icc a b, ⌊wave x⌋ = n := by
  constructor
  · intro hn
    simp only [bandIndices, Finset.mem_Icc] at hn
    obtain ⟨hlo, hhi⟩ := hn
    rcases eq_or_lt_of_le hlo with h | h
    · exact ⟨a, ⟨le_refl a, hab⟩, h⟩
    rcases eq_or_lt_of_le hhi with h' | h'
    · exact ⟨b, ⟨hab, le_refl b⟩, h'.symm⟩
    · have hlow : wave a < (n : ℝ) := by
        have : (⌊wave a⌋ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
        linarith [Int.lt_floor_add_one (wave a)]
      have hhigh : (n : ℝ) < wave b := by
        have : (n : ℝ) + 1 ≤ (⌊wave b⌋ : ℝ) := by exact_mod_cast h'
        linarith [Int.floor_le (wave b)]
      have hsub : Set.Icc (wave a) (wave b) ⊆ wave '' Set.Icc a b :=
        intermediate_value_Icc hab continuous_wave.continuousOn
      obtain ⟨x, hx, hxv⟩ := hsub ⟨le_of_lt hlow, le_of_lt hhigh⟩
      exact ⟨x, hx, by rw [hxv, Int.floor_intCast]⟩
  · rintro ⟨x, ⟨hax, hxb⟩, rfl⟩
    simp only [bandIndices, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor (strictMono_wave.monotone hax),
      Int.floor_le_floor (strictMono_wave.monotone hxb)⟩

/-- The band count in closed form. -/
theorem bandCount_eq {a b : ℝ} (hab : a ≤ b) :
    bandCount a b = (⌊wave b⌋ - ⌊wave a⌋ + 1).toNat := by
  have h : ⌊wave a⌋ ≤ ⌊wave b⌋ := Int.floor_le_floor (strictMono_wave.monotone hab)
  simp [bandCount, bandIndices, Int.card_Icc]
  omega

/-- **Seven bands, exactly.**  Plotting from `0`, the picture shows seven bands precisely
when the wave has climbed into `[6, 7)`. -/
theorem seven_bands_iff {b : ℝ} (hb : 0 ≤ b) :
    bandCount 0 b = 7 ↔ 6 ≤ wave b ∧ wave b < 7 := by
  have h0 : ⌊wave 0⌋ = 0 := by rw [wave_zero]; simp
  have hmono : (0 : ℝ) ≤ wave b := by rw [← wave_zero]; exact strictMono_wave.monotone hb
  have hfl : 0 ≤ ⌊wave b⌋ := Int.le_floor.mpr (by simpa using hmono)
  rw [bandCount_eq hb, h0]
  constructor
  · intro h
    have h6 : ⌊wave b⌋ = 6 := by omega
    have hle : ((6 : ℤ) : ℝ) ≤ wave b := by rw [← h6]; exact Int.floor_le _
    have hlt : wave b < ((6 : ℤ) : ℝ) + 1 := by rw [← h6]; exact Int.lt_floor_add_one _
    push_cast at hle hlt
    exact ⟨hle, by linarith⟩
  · rintro ⟨h1, h2⟩
    have h6 : ⌊wave b⌋ = 6 := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast h1
      · push_cast; linarith
    omega

/-! ## Which plotting ranges give seven bands -/

private theorem wave_two_lt_six : wave 2 < 6 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp2 : Real.exp 2 < 7.39 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hneg : 0 < Real.exp (-2) := Real.exp_pos _
  have hsinh : Real.sinh 2 < 3.7 := by rw [Real.sinh_eq]; linarith
  have hsin : Real.sin 2 ≤ 1 := Real.sin_le_one 2
  unfold wave
  linarith

private theorem seven_lt_wave_three : 7 < wave 3 := by
  have h1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp3 : 20 < Real.exp 3 := by
    have : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    nlinarith
  have hneg : Real.exp (-3) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hsinh : 9 < Real.sinh 3 := by rw [Real.sinh_eq]; linarith
  have hsin : -1 ≤ Real.sin 3 := Real.neg_one_le_sin 3
  unfold wave
  linarith

/-- **The seven-band window.**  There are two plotting endpoints `b₆ < b₇`, both strictly
between 2 and 3, such that a plot over `[0, b]` shows seven bands exactly when
`b₆ ≤ b < b₇`.  Numerically `b₆ ≈ 2.3702` and `b₇ ≈ 2.5638`, so a natural choice like
"plot `x` from 0 to 2.5" lands inside the window — which is why the picture has seven bands
and not some other number. -/
theorem seven_band_window :
    ∃ b₆ b₇ : ℝ, 2 < b₆ ∧ b₆ < b₇ ∧ b₇ < 3 ∧ wave b₆ = 6 ∧ wave b₇ = 7 ∧
      ∀ b : ℝ, 0 ≤ b → (bandCount 0 b = 7 ↔ b₆ ≤ b ∧ b < b₇) := by
  have hle : (2 : ℝ) ≤ 3 := by norm_num
  have hsub : Set.Icc (wave 2) (wave 3) ⊆ wave '' Set.Icc 2 3 :=
    intermediate_value_Icc hle continuous_wave.continuousOn
  obtain ⟨b₆, hb₆mem, hb₆⟩ :=
    hsub ⟨le_of_lt wave_two_lt_six, by linarith [seven_lt_wave_three]⟩
  obtain ⟨b₇, hb₇mem, hb₇⟩ :=
    hsub ⟨by linarith [wave_two_lt_six], le_of_lt seven_lt_wave_three⟩
  have h2lt : 2 < b₆ := by
    by_contra h
    push_neg at h
    have := strictMono_wave.monotone h
    rw [hb₆] at this
    linarith [wave_two_lt_six]
  have hlt : b₆ < b₇ := by
    have : wave b₆ < wave b₇ := by rw [hb₆, hb₇]; norm_num
    exact strictMono_wave.lt_iff_lt.mp this
  have h3gt : b₇ < 3 := by
    by_contra h
    push_neg at h
    have := strictMono_wave.monotone h
    rw [hb₇] at this
    linarith [seven_lt_wave_three]
  refine ⟨b₆, b₇, h2lt, hlt, h3gt, hb₆, hb₇, fun b hb => ?_⟩
  rw [seven_bands_iff hb, ← hb₆, ← hb₇]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨strictMono_wave.le_iff_le.mp h1, strictMono_wave.lt_iff_lt.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨strictMono_wave.monotone h1, strictMono_wave.lt_iff_lt.mpr h2⟩

/-- The same fact stated as the project would state it for a reviewer: "seven bands" is a
property of the plotting range, not of the generator.  Ranges that are too short or too long
give a different number, and the count is always `⌊wave b⌋ + 1`. -/
theorem bandCount_from_zero {b : ℝ} (hb : 0 ≤ b) : bandCount 0 b = (⌊wave b⌋ + 1).toNat := by
  rw [bandCount_eq hb, wave_zero]
  simp

end RequestProject.Analysis
