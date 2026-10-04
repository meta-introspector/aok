module

public import RequestProject.Aristo.Fractran.PentagonalLoop
public import RequestProject.Aristo.Fractran.PartsLeTwo
public import RequestProject.Aristo.Ramanujan.PentagonalBridge

/-!
# The pentagonal machine in FRACTRAN, end to end

`fractranPent = lean2fractran PrimeCode.std pentProg` is the FRACTRAN program obtained from the
20-register LOOP program `pentProg` by the certified compiler `lean2fractran`
(706 Minsky instructions, one or two fractions each).

* `fractran_pentagonal` (**all `n`, all `m > 0`**): started on `73 · 2ⁿ · 3ᵐ` with enough fuel
  (at least the explicit step count `time pentProg (initRegs n m)`), the program halts at a
  number whose exponent of `13` is `pentSeq (ZMod m) n` — Euler's pentagonal recurrence mod `m`.
  `fractran_pentagonal_halts`: no fraction applies to that number.
* `fractran_partition_mod`: for `n ≤ 200` this exponent is `p(n) mod m`.
* `fractran_partition`: for `n ≤ 200` and `m > p(n)` it is `p(n)` itself.

Only the last two use the bounded bridge to `Nat.Partition` (`pentSeq_eq_card`, `n ≤ 200`);
the first is a statement about the recurrence for every `n`.
-/

@[expose] public section

namespace Aristo.Fractran.PentFr

open Aristo.Fractran Stmt Aristo.Ramanujan.Pentagonal

/-- The LOOP program is well formed (no loop body writes its own counter). -/
theorem pentProg_WF : pentProg.WF = true := by decide

theorem nth_prime_twenty : Nat.nth Nat.Prime 20 = 73 := by
  have := Nat.nth_count (p := Nat.Prime) (n := 73) (by norm_num)
  rwa [show Nat.count Nat.Prime 73 = 20 by decide] at this

/-- The FRACTRAN program for the pentagonal machine. -/
noncomputable def fractranPent : List FracInstr := lean2fractran PrimeCode.std pentProg

theorem encodeCfg_initRegs (n m : ℕ) :
    encodeCfg PrimeCode.std (0, initRegs n m) = 73 * (2 ^ n * 3 ^ m) := by
  simp [encodeCfg, encodeRegs, Fin.prod_univ_succ, initRegs, PrimeCode.std, Function.update_apply,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, nth_prime_twenty]

/-- **The pentagonal machine in FRACTRAN, for every `n` and every modulus `m > 0`.** Started on
`73 · 2ⁿ · 3ᵐ` with fuel at least `time pentProg (initRegs n m)`, the program `fractranPent`
halts at a number whose `13`-adic exponent is the pentagonal sequence mod `m` at `n`. -/
theorem fractran_pentagonal (n m : ℕ) (hm : 0 < m) (fuel : ℕ)
    (hfuel : time pentProg (initRegs n m) ≤ fuel) :
    (runFuel fractranPent fuel (73 * (2 ^ n * 3 ^ m))).factorization 13 =
      (pentSeq (ZMod m) n).val := by
  rw [fractranPent, ← encodeCfg_initRegs,
    lean2fractran_runFuel PrimeCode.std pentProg pentProg_WF _ fuel hfuel]
  have h13 : (13 : ℕ) = PrimeCode.std.P 5 := by simp [PrimeCode.std, nth_prime_five]
  rw [h13, factorization_encodeCfg]
  simp only [show 5 < 20 by norm_num, dite_true, show ¬ (5 = 20 + len pentProg) by omega,
    if_false, add_zero]
  exact eval_pentProg n m hm

/-- The number reached is a halting number: no fraction of `fractranPent` applies to it. -/
theorem fractran_pentagonal_halts (n m fuel : ℕ) (hfuel : time pentProg (initRegs n m) ≤ fuel) :
    step fractranPent (runFuel fractranPent fuel (73 * (2 ^ n * 3 ^ m))) = none := by
  rw [fractranPent, ← encodeCfg_initRegs,
    lean2fractran_runFuel PrimeCode.std pentProg pentProg_WF _ fuel hfuel]
  exact lean2fractran_halts _ _ _

/-- For `n ≤ 200` the FRACTRAN output is `p(n) mod m`. -/
theorem fractran_partition_mod (n m : ℕ) (hn : n ≤ 200) (hm : 0 < m) (fuel : ℕ)
    (hfuel : time pentProg (initRegs n m) ≤ fuel) :
    (runFuel fractranPent fuel (73 * (2 ^ n * 3 ^ m))).factorization 13 =
      Fintype.card (Nat.Partition n) % m := by
  rw [fractran_pentagonal n m hm fuel hfuel, pentSeq_zmod_eq_card m n hn, ZMod.val_natCast]

/-- **Partition numbers from FRACTRAN.** For `n ≤ 200` and any `m > p(n)`, the FRACTRAN program
started on `73 · 2ⁿ · 3ᵐ` halts at a number whose `13`-adic exponent is `p(n)`. -/
theorem fractran_partition (n m : ℕ) (hn : n ≤ 200) (hm : Fintype.card (Nat.Partition n) < m)
    (fuel : ℕ) (hfuel : time pentProg (initRegs n m) ≤ fuel) :
    (runFuel fractranPent fuel (73 * (2 ^ n * 3 ^ m))).factorization 13 =
      Fintype.card (Nat.Partition n) := by
  rw [fractran_partition_mod n m hn (by omega) fuel hfuel, Nat.mod_eq_of_lt hm]

end Aristo.Fractran.PentFr
