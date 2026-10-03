module

public import Mathlib

/-!
# A proof-carrying register machine for Euler's pentagonal recurrence

Euler's recurrence computes the partition numbers from the generalized pentagonal numbers
`g⁻ₖ = k(3k-1)/2` and `g⁺ₖ = k(3k+1)/2`:

`p(n) = ∑_{k ≥ 1} (-1)^(k-1) (p(n - g⁻ₖ) + p(n - g⁺ₖ))`, `p(0) = 1`, `p(m) = 0` for `m < 0`.

This file turns that rule into a small operational semantics over an arbitrary commutative ring
`R` (so the same machine runs over `ℤ` and over `ZMod m`).

* **Inner machine** (`innerStep`): registers `(k, g⁻, g⁺, s, A)`. While `g⁻ ≤ n` it adds
  `s · (f(n - g⁻) + [g⁺ ≤ n] f(n - g⁺))` to `A`, then advances `k ↦ k+1`, `g⁻ ↦ g⁻ + 3k + 1`,
  `g⁺ ↦ g⁺ + 3k + 2`, `s ↦ -s`. It halts once `g⁻ > n`.
  - `innerStep_canon`: the transition preserves the invariant "registers are the canonical
    state `canon k`", i.e. `g⁻ = g⁻ₖ`, `g⁺ = g⁺ₖ`, `s = (-1)^(k+1)` and
    `A = ∑_{1 ≤ i < k} (-1)^(i+1) (…)`.
  - `innerStep_measure`: the measure `n + 1 - g⁻` strictly decreases, so the machine terminates;
    `n + 1` steps of fuel always suffice.
  - `innerEval_eq_pentSum`: the halting accumulator is the full recurrence sum `pentSum f n`.
* **Outer machine** (`outerStep`): appends one new table entry, `1` at index `0` and otherwise the
  inner machine's output on the current table.
  - `pentSeq_isPentagonal`: the computed sequence satisfies the recurrence and the base value.
  - `IsPentagonal.unique`, `eq_of_pentagonal_le`: such a sequence is unique (also on an initial
    segment), so the machine computes *the* pentagonal sequence.
  - `pentSeq_map`: a ring homomorphism `R →+* S` carries the `R`-machine's output to the
    `S`-machine's output; e.g. the `ZMod m` machine computes the `ℤ` machine's values mod `m`.

Nothing here mentions partitions; the bridge to `Nat.Partition` is in `PentagonalBridge`.
-/

@[expose] public section

namespace Aristo.Ramanujan.Pentagonal

/-! ### Generalized pentagonal numbers -/

/-- `g⁻ₖ = k(3k-1)/2`, defined by `g⁻₀ = 0`, `g⁻ₖ₊₁ = g⁻ₖ + 3k + 1`. -/
def gMinus : ℕ → ℕ
  | 0 => 0
  | k + 1 => gMinus k + 3 * k + 1

/-- `g⁺ₖ = k(3k+1)/2 = g⁻ₖ + k`. -/
def gPlus (k : ℕ) : ℕ := gMinus k + k

theorem two_mul_gMinus (k : ℕ) : 2 * gMinus k + k = 3 * k ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [gMinus]; nlinarith

theorem two_mul_gPlus (k : ℕ) : 2 * gPlus k = 3 * k ^ 2 + k := by
  have := two_mul_gMinus k; unfold gPlus; omega

theorem le_gMinus (k : ℕ) : k ≤ gMinus k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [gMinus]; omega

theorem gMinus_mono {i j : ℕ} (h : i ≤ j) : gMinus i ≤ gMinus j := by
  induction h with
  | refl => rfl
  | step _ ih => simp only [gMinus]; omega

theorem gMinus_le_gPlus (k : ℕ) : gMinus k ≤ gPlus k := Nat.le_add_right _ _

theorem one_le_gMinus {i : ℕ} (hi : 1 ≤ i) : 1 ≤ gMinus i := le_trans hi (le_gMinus i)

variable {R : Type*} [CommRing R]

/-! ### The recurrence -/

/-- The `i`-th term of the recurrence for index `n`, reading values from `f`. -/
def pentTerm (f : ℕ → R) (n i : ℕ) : R :=
  (-1) ^ (i + 1) * ((if gMinus i ≤ n then f (n - gMinus i) else 0) +
    (if gPlus i ≤ n then f (n - gPlus i) else 0))

/-- `∑_{1 ≤ i ≤ n} (-1)^(i-1) (f(n - g⁻ᵢ) + f(n - g⁺ᵢ))`, with out-of-range terms `0`. -/
def pentSum (f : ℕ → R) (n : ℕ) : R := ∑ i ∈ Finset.Ico 1 (n + 1), pentTerm f n i

/-- A sequence obeying Euler's recurrence with `f 0 = 1`. -/
def IsPentagonal (f : ℕ → R) : Prop := f 0 = 1 ∧ ∀ n, 1 ≤ n → f n = pentSum f n

theorem pentTerm_eq_zero (f : ℕ → R) {n i : ℕ} (h : n < gMinus i) : pentTerm f n i = 0 := by
  have := gMinus_le_gPlus i
  simp [pentTerm, show ¬ gMinus i ≤ n by omega, show ¬ gPlus i ≤ n by omega]

/-- `pentSum f n` only reads `f` below `n`. -/
theorem pentSum_congr {f g : ℕ → R} {n : ℕ} (h : ∀ j < n, f j = g j) :
    pentSum f n = pentSum g n := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
  have h1 := one_le_gMinus hi1
  have h2 := gMinus_le_gPlus i
  unfold pentTerm
  congr 2
  · split_ifs with h3
    · exact h _ (by omega)
    · rfl
  · split_ifs with h3
    · exact h _ (by omega)
    · rfl

/-- The truncated sum up to any `k` past the last nonzero term is the full sum. -/
theorem sum_Ico_eq_pentSum (f : ℕ → R) {n k : ℕ} (hk : n < gMinus k) :
    ∑ i ∈ Finset.Ico 1 k, pentTerm f n i = pentSum f n := by
  unfold pentSum
  have key : ∀ M, k ≤ M → n + 1 ≤ M →
      ∑ i ∈ Finset.Ico 1 M, pentTerm f n i = ∑ i ∈ Finset.Ico 1 k, pentTerm f n i ∧
      ∑ i ∈ Finset.Ico 1 M, pentTerm f n i = ∑ i ∈ Finset.Ico 1 (n + 1), pentTerm f n i := by
    intro M hkM hnM
    constructor
    · symm
      refine Finset.sum_subset (Finset.Ico_subset_Ico_right hkM) fun i hi hnot => ?_
      simp only [Finset.mem_Ico, not_and, not_lt] at hi hnot
      exact pentTerm_eq_zero f (lt_of_lt_of_le hk (gMinus_mono (hnot hi.1)))
    · symm
      refine Finset.sum_subset (Finset.Ico_subset_Ico_right hnM) fun i hi hnot => ?_
      simp only [Finset.mem_Ico, not_and, not_lt] at hi hnot
      exact pentTerm_eq_zero f (lt_of_lt_of_le (hnot hi.1) (le_gMinus i))
  obtain ⟨h1, h2⟩ := key (max k (n + 1)) (le_max_left _ _) (le_max_right _ _)
  rw [← h1, h2]

/-! ### The inner machine -/

/-- Registers of the inner machine. -/
structure InnerState (R : Type*) where
  k : ℕ
  gm : ℕ
  gp : ℕ
  sign : R
  acc : R

/-- One transition: add the current pair of terms and advance to the next pentagonal pair;
halt (`none`) once `g⁻ > n`. -/
def innerStep (f : ℕ → R) (n : ℕ) (s : InnerState R) : Option (InnerState R) :=
  if s.gm ≤ n then
    some ⟨s.k + 1, s.gm + 3 * s.k + 1, s.gp + 3 * s.k + 2, -s.sign,
      s.acc + s.sign * (f (n - s.gm) + if s.gp ≤ n then f (n - s.gp) else 0)⟩
  else none

/-- Run the inner machine for at most `fuel` steps. -/
def innerRun (f : ℕ → R) (n : ℕ) : ℕ → InnerState R → InnerState R
  | 0, s => s
  | fuel + 1, s =>
    match innerStep f n s with
    | none => s
    | some s' => innerRun f n fuel s'

/-- Initial registers: `k = 1`, `g⁻ = 1`, `g⁺ = 2`, `s = 1`, `A = 0`. -/
def innerInit : InnerState R := ⟨1, 1, 2, 1, 0⟩

/-- The inner machine's output for index `n`, with `n + 1` steps of fuel. -/
def innerEval (f : ℕ → R) (n : ℕ) : R := (innerRun f n (n + 1) innerInit).acc

/-- **Termination measure.** Every transition strictly decreases `n + 1 - g⁻`. -/
theorem innerStep_measure {f : ℕ → R} {n : ℕ} {s s' : InnerState R}
    (h : innerStep f n s = some s') : n + 1 - s'.gm < n + 1 - s.gm := by
  unfold innerStep at h
  by_cases hle : s.gm ≤ n
  · rw [if_pos hle] at h
    obtain rfl := Option.some.inj h
    dsimp only
    omega
  · rw [if_neg hle] at h
    exact absurd h (by simp)

/-- The canonical register contents after the first `k - 1` pairs. -/
def canon (f : ℕ → R) (n k : ℕ) : InnerState R :=
  ⟨k, gMinus k, gPlus k, (-1) ^ (k + 1), ∑ i ∈ Finset.Ico 1 k, pentTerm f n i⟩

theorem innerInit_eq_canon (f : ℕ → R) (n : ℕ) : (innerInit : InnerState R) = canon f n 1 := by
  simp [innerInit, canon, gMinus, gPlus]

/-- **Invariant step.** From a canonical state with `g⁻ₖ ≤ n`, the transition lands on the next
canonical state. -/
theorem innerStep_canon (f : ℕ → R) {n k : ℕ} (hk : 1 ≤ k) (h : gMinus k ≤ n) :
    innerStep f n (canon f n k) = some (canon f n (k + 1)) := by
  simp only [innerStep, canon, h, if_true, Option.some.injEq]
  have hg : gPlus (k + 1) = gPlus k + 3 * k + 2 := by simp only [gPlus, gMinus]; omega
  rw [Finset.sum_Ico_succ_top hk]
  simp only [gMinus, hg, pentTerm, h, if_true, InnerState.mk.injEq]
  exact ⟨trivial, trivial, trivial, by ring, trivial⟩

theorem innerStep_canon_none (f : ℕ → R) {n k : ℕ} (h : n < gMinus k) :
    innerStep f n (canon f n k) = none := by
  simp [innerStep, canon, show ¬ gMinus k ≤ n by omega]

theorem innerRun_canon_acc (f : ℕ → R) (n : ℕ) :
    ∀ fuel k, 1 ≤ k → n < gMinus (k + fuel) → (innerRun f n fuel (canon f n k)).acc = pentSum f n
  | 0, k, _, h => sum_Ico_eq_pentSum f h
  | fuel + 1, k, hk, h => by
    by_cases hle : gMinus k ≤ n
    · simp only [innerRun, innerStep_canon f hk hle]
      exact innerRun_canon_acc f n fuel (k + 1) (by omega) (by rwa [add_right_comm, add_assoc])
    · simp only [innerRun, innerStep_canon_none f (show n < gMinus k by omega)]
      exact sum_Ico_eq_pentSum f (by omega)

/-- **Inner machine correctness.** The halting accumulator is the full recurrence sum. -/
theorem innerEval_eq_pentSum (f : ℕ → R) (n : ℕ) : innerEval f n = pentSum f n := by
  unfold innerEval
  rw [innerInit_eq_canon f n]
  exact innerRun_canon_acc f n (n + 1) 1 le_rfl
    (lt_of_lt_of_le (by omega) (le_gMinus (1 + (n + 1))))

/-! ### The outer (table-building) machine -/

/-- Append the next entry: `1` at index `0`, otherwise the inner machine's output on the table. -/
def outerStep (tbl : List R) : List R :=
  tbl ++ [if tbl.length = 0 then 1 else innerEval (fun j => tbl.getD j 0) tbl.length]

/-- The table `[f(0), …, f(N)]` produced by `N + 1` outer steps. -/
def table (R : Type*) [CommRing R] (N : ℕ) : List R := outerStep^[N + 1] []

/-- The sequence computed by the machine. -/
def pentSeq (R : Type*) [CommRing R] (n : ℕ) : R := (table R n).getD n 0

theorem length_iterate_outerStep (m : ℕ) : (outerStep^[m] ([] : List R)).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', outerStep, List.length_append, ih]; rfl

theorem iterate_outerStep_succ (m : ℕ) :
    outerStep^[m + 1] ([] : List R) = outerStep^[m] [] ++
      [if m = 0 then 1 else innerEval (fun j => (outerStep^[m] ([] : List R)).getD j 0) m] := by
  rw [Function.iterate_succ_apply', outerStep, length_iterate_outerStep]

/-- Entries of the table never change once written. -/
theorem getD_iterate_outerStep (m j : ℕ) (hj : j < m) :
    (outerStep^[m] ([] : List R)).getD j 0 = pentSeq R j := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [iterate_outerStep_succ, List.getD_append _ _ _ _ (by rw [length_iterate_outerStep]; exact h),
        ih h]
    · rfl

theorem pentSeq_eq (n : ℕ) :
    pentSeq R n = if n = 0 then 1 else innerEval (fun j => (outerStep^[n] ([] : List R)).getD j 0) n := by
  unfold pentSeq table
  rw [iterate_outerStep_succ, List.getD_append_right _ _ _ _ (by rw [length_iterate_outerStep]),
    length_iterate_outerStep, Nat.sub_self]
  rfl

/-- **Outer machine correctness.** The computed sequence obeys Euler's recurrence and `f 0 = 1`. -/
theorem pentSeq_isPentagonal : IsPentagonal (pentSeq R) := by
  refine ⟨by rw [pentSeq_eq]; simp, fun n hn => ?_⟩
  rw [pentSeq_eq, if_neg (by omega), innerEval_eq_pentSum]
  exact pentSum_congr (fun j hj => getD_iterate_outerStep n j hj)

theorem getD_table (N n : ℕ) (hn : n ≤ N) : (table R N).getD n 0 = pentSeq R n :=
  getD_iterate_outerStep (N + 1) n (by omega)

theorem length_table (N : ℕ) : (table R N).length = N + 1 := length_iterate_outerStep _

/-! ### Uniqueness and change of ring -/

/-- Two sequences with value `1` at `0` and obeying the recurrence for `1 ≤ n ≤ B` agree up to
`B`. -/
theorem eq_of_pentagonal_le {f g : ℕ → R} (B : ℕ) (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hf : ∀ n, 1 ≤ n → n ≤ B → f n = pentSum f n) (hg : ∀ n, 1 ≤ n → n ≤ B → g n = pentSum g n) :
    ∀ n ≤ B, f n = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hf0, hg0]
    · rw [hf n hpos hn, hg n hpos hn]
      exact pentSum_congr (fun j hj => ih j hj (by omega))

theorem IsPentagonal.unique {f g : ℕ → R} (hf : IsPentagonal f) (hg : IsPentagonal g) : f = g :=
  funext fun n => eq_of_pentagonal_le n hf.1 hg.1 (fun m hm _ => hf.2 m hm)
    (fun m hm _ => hg.2 m hm) n le_rfl

theorem pentSum_map {S : Type*} [CommRing S] (φ : R →+* S) (f : ℕ → R) (n : ℕ) :
    φ (pentSum f n) = pentSum (fun j => φ (f j)) n := by
  unfold pentSum pentTerm
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_add]
  congr 2 <;> split_ifs <;> simp

/-- The `S`-machine computes the image of the `R`-machine's values under any ring
homomorphism. -/
theorem pentSeq_map {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ) :
    pentSeq S n = φ (pentSeq R n) := by
  have h : IsPentagonal (fun j => φ (pentSeq R j)) := by
    refine ⟨show φ (pentSeq R 0) = 1 by rw [pentSeq_isPentagonal.1, map_one], fun m hm => ?_⟩
    show φ (pentSeq R m) = _
    rw [pentSeq_isPentagonal.2 m hm, pentSum_map]
  exact congrFun (pentSeq_isPentagonal.unique h) n

/-- In particular the `ZMod m` machine computes the integer machine's values mod `m`. -/
theorem pentSeq_zmod (m n : ℕ) : pentSeq (ZMod m) n = (pentSeq ℤ n : ZMod m) :=
  pentSeq_map (Int.castRingHom (ZMod m)) n

end Aristo.Ramanujan.Pentagonal
