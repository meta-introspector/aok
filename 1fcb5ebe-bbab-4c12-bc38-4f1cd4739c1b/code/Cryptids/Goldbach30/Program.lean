module

public import Cryptids.Core.Fractran

/-!
# A 30-fraction Goldbach FRACTRAN program with a mode-switching shared subroutine

A reworked version of the 43-fraction program in `Cryptids.Goldbach43`. The trial-division
engine is split into

* two small *phase-specific* front ends (`RA ph`, `NT ph`), the only states that touch the
  tested register (`a` in phase `A`, `b` in phase `B`), and
* a *shared* back end (`Q`, `R`, `R2`) used by both phases. A one-bit **mode register** `m`
  (set only while the shared states run on behalf of phase `B`) tells the shared states which
  front end to return to. Fractions that do not care about the mode simply do not mention `m`,
  so it rides along untouched; the only mode-dependent fractions are the two return points.

Other changes relative to the 43-fraction program:

* the "consume one unit of the tested value" and "consume one unit of the divisor" halves of the
  inner loop are separate states (`RA ph` and `Q`), so the loop has no idle return fraction;
* a full pass of the divisor (the wrap) is detected in the shared state `Q`;
* at an exact division the leftover divisor copy `e` is cleared *while* the tested value is
  restored (`NT ph · s · e → NT2 ph · x`), so no separate clearing loop is needed.

Registers: `a=2, b=3, c=5, d=7, e=11, f=13, s=17, g=19, h=23, m=29`; the 11 control states use
the primes `31 … 73`. This file proves `fstep_enc`: one FRACTRAN step is one step of the
abstract machine `astep`.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach30

open ConjectureMachines.Core.Fractran

/-- The 30 fractions. -/
def goldbachProg : FractranProgram :=
  [697/62, 10879/217, 53/31, 20213/111, 315491/259, 61/37, 407/8323, 341/287, 43/533, 43/41,
   329/473, 43/47, 1159/28681, 1007/989, 41/43, 118/9911, 118/901, 53/59, 2821/1007, 8113/689,
   39494/795, 201/11407, 201/1037, 61/67, 3367/1159, 71/793, 39494/915, 1095/142, 71/73,
   78988/355]

/-- The start integer `N0 = 31 · 2² · 3² · 7² · 13` (state `RA A`, `a = b = d = 2`, `f = 1`). -/
def goldbachStart : ℕ := 710892

/-! ## The abstract machine -/

/-- The two phases: testing `a` for primality, or testing `b`. -/
inductive Ph | A | B
  deriving DecidableEq, Repr

/-- The 11 control states. `RA`, `NT`, `NT2` exist once per phase; `Q`, `R`, `R2` are shared. -/
inductive St
  | RA (ph : Ph) | Q | R | R2 | NT (ph : Ph) | NT2 (ph : Ph) | SA | SB
  deriving DecidableEq, Repr

/-- The ten data registers. -/
structure Regs where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  e : ℕ
  f : ℕ
  s : ℕ
  g : ℕ
  h : ℕ
  m : ℕ
  deriving DecidableEq, Repr

/-- A configuration of the abstract machine. -/
structure Cfg where
  st : St
  r : Regs
  deriving DecidableEq, Repr

/-- The prime encoding each control state. -/
def stPrime : St → ℕ
  | .RA .A => 31 | .RA .B => 37 | .Q => 41 | .R => 43 | .R2 => 47
  | .NT .A => 53 | .NT2 .A => 59 | .NT .B => 61 | .NT2 .B => 67 | .SA => 71 | .SB => 73

/-- The product of the register primes. -/
def regProd (r : Regs) : ℕ :=
  2 ^ r.a * 3 ^ r.b * 5 ^ r.c * 7 ^ r.d * 11 ^ r.e * 13 ^ r.f * 17 ^ r.s * 19 ^ r.g *
    23 ^ r.h * 29 ^ r.m

/-- The integer encoding a configuration. -/
def enc (c : Cfg) : ℕ := stPrime c.st * regProd c.r

/-- One step of the abstract machine, written out state by state in FRACTRAN order. -/
def astep : Cfg → Option Cfg
  | ⟨.RA .A, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩ =>
    if 0 < a then some ⟨.Q, ⟨a - 1, b, c, d, e, f, s + 1, g, h, m⟩⟩
    else if 0 < d then some ⟨.R, ⟨a, b, c, d - 1, e + 1, f, s, g, h + 1, m⟩⟩
    else some ⟨.NT .A, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩
  | ⟨.RA .B, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩ =>
    if 0 < b then some ⟨.Q, ⟨a, b - 1, c, d, e, f, s + 1, g, h, m + 1⟩⟩
    else if 0 < d then some ⟨.R, ⟨a, b, c, d - 1, e + 1, f, s, g, h + 1, m + 1⟩⟩
    else some ⟨.NT .B, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩
  | ⟨.Q, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩ =>
    if 0 < m ∧ 0 < d then some ⟨.RA .B, ⟨a, b, c, d - 1, e + 1, f, s, g, h, m - 1⟩⟩
    else if 0 < d then some ⟨.RA .A, ⟨a, b, c, d - 1, e + 1, f, s, g, h, m⟩⟩
    else if 0 < f then some ⟨.R, ⟨a, b, c, d, e, f - 1, s, g, h, m⟩⟩
    else some ⟨.R, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩
  | ⟨.R, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩ =>
    if 0 < e then some ⟨.R2, ⟨a, b, c, d + 1, e - 1, f, s, g, h, m⟩⟩
    else if 0 < m ∧ 0 < h then some ⟨.NT .B, ⟨a, b, c, d, e, f, s, g + 1, h - 1, m - 1⟩⟩
    else if 0 < h then some ⟨.NT .A, ⟨a, b, c, d, e, f, s, g + 1, h - 1, m⟩⟩
    else some ⟨.Q, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩
  | ⟨.R2, r⟩ => some ⟨.R, r⟩
  | ⟨.NT .A, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩ =>
    if 0 < s ∧ 0 < e then some ⟨.NT2 .A, ⟨a + 1, b, c, d, e - 1, f, s - 1, g, h, m⟩⟩
    else if 0 < s then some ⟨.NT2 .A, ⟨a + 1, b, c, d, e, f, s - 1, g, h, m⟩⟩
    else if 0 < g then some ⟨.RA .A, ⟨a, b, c, d + 1, e, f + 1, s, g - 1, h, m⟩⟩
    else if 0 < f then some ⟨.NT .B, ⟨a, b, c, d + 1, e, f - 1, s, g + 1, h, m⟩⟩
    else if 0 < b ∧ 0 < c then some ⟨.RA .A, ⟨a + 1, b - 1, c - 1, d + 2, e, f + 1, s, g, h, m⟩⟩
    else none
  | ⟨.NT .B, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩ =>
    if 0 < s ∧ 0 < e then some ⟨.NT2 .B, ⟨a, b + 1, c, d, e - 1, f, s - 1, g, h, m⟩⟩
    else if 0 < s then some ⟨.NT2 .B, ⟨a, b + 1, c, d, e, f, s - 1, g, h, m⟩⟩
    else if 0 < g then some ⟨.RA .B, ⟨a, b, c, d + 1, e, f + 1, s, g - 1, h, m⟩⟩
    else if 0 < f then some ⟨.SA, ⟨a, b, c, d, e, f - 1, s, g, h, m⟩⟩
    else if 0 < b ∧ 0 < c then some ⟨.RA .A, ⟨a + 1, b - 1, c - 1, d + 2, e, f + 1, s, g, h, m⟩⟩
    else none
  | ⟨.NT2 ph, r⟩ => some ⟨.NT ph, r⟩
  | ⟨.SA, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩ =>
    if 0 < a then some ⟨.SB, ⟨a - 1, b + 1, c + 1, d, e, f, s, g, h, m⟩⟩
    else if 0 < c then some ⟨.RA .A, ⟨a + 2, b, c - 1, d + 2, e, f + 1, s, g, h, m⟩⟩
    else none
  | ⟨.SB, r⟩ => some ⟨.SA, r⟩

/-! ## Rules: the annotated form of the program -/

/-- An annotated FRACTRAN rule: `src → dst`, consuming `cons` and producing `prod`. -/
structure Rule where
  src : St
  cons : Regs
  dst : St
  prod : Regs

/-- Numerator of a rule. -/
def Rule.num (ρ : Rule) : ℕ := stPrime ρ.dst * regProd ρ.prod
/-- Denominator of a rule. -/
def Rule.den (ρ : Rule) : ℕ := stPrime ρ.src * regProd ρ.cons

/-- Componentwise order on registers. -/
def Regs.le (r r' : Regs) : Prop :=
  r.a ≤ r'.a ∧ r.b ≤ r'.b ∧ r.c ≤ r'.c ∧ r.d ≤ r'.d ∧ r.e ≤ r'.e ∧ r.f ≤ r'.f ∧
    r.s ≤ r'.s ∧ r.g ≤ r'.g ∧ r.h ≤ r'.h ∧ r.m ≤ r'.m

instance (r r' : Regs) : Decidable (r.le r') := by unfold Regs.le; infer_instance

/-- `r - cons + prod`, componentwise. -/
def Regs.upd (r cons prod : Regs) : Regs :=
  ⟨r.a - cons.a + prod.a, r.b - cons.b + prod.b, r.c - cons.c + prod.c, r.d - cons.d + prod.d,
   r.e - cons.e + prod.e, r.f - cons.f + prod.f, r.s - cons.s + prod.s, r.g - cons.g + prod.g,
   r.h - cons.h + prod.h, r.m - cons.m + prod.m⟩

/-- Does rule `ρ` fire on configuration `c`? -/
def Rule.fires (ρ : Rule) (c : Cfg) : Bool := decide (ρ.src = c.st ∧ ρ.cons.le c.r)

/-- The configuration after firing rule `ρ`. -/
def Rule.apply (ρ : Rule) (c : Cfg) : Cfg := ⟨ρ.dst, c.r.upd ρ.cons ρ.prod⟩

/-- The zero register vector. -/
def R0 : Regs := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- All 30 rules, in program order. -/
def rules : List Rule :=
  [-- phase A front end: consume one unit of `a`; `a` exhausted with divisor left; exact
   ⟨.RA .A, { R0 with a := 1 }, .Q, { R0 with s := 1 }⟩,
   ⟨.RA .A, { R0 with d := 1 }, .R, { R0 with e := 1, h := 1 }⟩,
   ⟨.RA .A, R0, .NT .A, R0⟩,
   -- phase B front end: the same on `b`, switching the shared states to mode `B`
   ⟨.RA .B, { R0 with b := 1 }, .Q, { R0 with s := 1, m := 1 }⟩,
   ⟨.RA .B, { R0 with d := 1 }, .R, { R0 with e := 1, h := 1, m := 1 }⟩,
   ⟨.RA .B, R0, .NT .B, R0⟩,
   -- shared: consume one unit of the divisor and return to the caller's phase
   ⟨.Q, { R0 with m := 1, d := 1 }, .RA .B, { R0 with e := 1 }⟩,
   ⟨.Q, { R0 with d := 1 }, .RA .A, { R0 with e := 1 }⟩,
   ⟨.Q, { R0 with f := 1 }, .R, R0⟩,
   ⟨.Q, R0, .R, R0⟩,
   -- shared: restore the divisor `d` from `e`
   ⟨.R, { R0 with e := 1 }, .R2, { R0 with d := 1 }⟩,
   ⟨.R2, R0, .R, R0⟩,
   ⟨.R, { R0 with m := 1, h := 1 }, .NT .B, { R0 with g := 1 }⟩,
   ⟨.R, { R0 with h := 1 }, .NT .A, { R0 with g := 1 }⟩,
   ⟨.R, R0, .Q, R0⟩,
   -- phase A back end: restore `a` (clearing `e`), then dispatch
   ⟨.NT .A, { R0 with s := 1, e := 1 }, .NT2 .A, { R0 with a := 1 }⟩,
   ⟨.NT .A, { R0 with s := 1 }, .NT2 .A, { R0 with a := 1 }⟩,
   ⟨.NT2 .A, R0, .NT .A, R0⟩,
   ⟨.NT .A, { R0 with g := 1 }, .RA .A, { R0 with d := 1, f := 1 }⟩,
   ⟨.NT .A, { R0 with f := 1 }, .NT .B, { R0 with d := 1, g := 1 }⟩,
   ⟨.NT .A, { R0 with b := 1, c := 1 }, .RA .A, { R0 with a := 1, d := 2, f := 1 }⟩,
   -- phase B back end
   ⟨.NT .B, { R0 with s := 1, e := 1 }, .NT2 .B, { R0 with b := 1 }⟩,
   ⟨.NT .B, { R0 with s := 1 }, .NT2 .B, { R0 with b := 1 }⟩,
   ⟨.NT2 .B, R0, .NT .B, R0⟩,
   ⟨.NT .B, { R0 with g := 1 }, .RA .B, { R0 with d := 1, f := 1 }⟩,
   ⟨.NT .B, { R0 with f := 1 }, .SA, R0⟩,
   ⟨.NT .B, { R0 with b := 1, c := 1 }, .RA .A, { R0 with a := 1, d := 2, f := 1 }⟩,
   -- success: move on to `n + 2`
   ⟨.SA, { R0 with a := 1 }, .SB, { R0 with b := 1, c := 1 }⟩,
   ⟨.SB, R0, .SA, R0⟩,
   ⟨.SA, { R0 with c := 1 }, .RA .A, { R0 with a := 2, d := 2, f := 1 }⟩]

theorem rules_length : rules.length = 30 := by decide

/-- The annotated rules really are the 30 fractions. -/
theorem goldbachProg_eq : goldbachProg = rules.map fun ρ => frac ρ.num ρ.den := by
  decide +kernel

theorem rules_coprime : ∀ ρ ∈ rules, Nat.Coprime ρ.num ρ.den := by
  decide +kernel

/-! ## Prime bookkeeping -/

def allSt : List St :=
  [.RA .A, .RA .B, .Q, .R, .R2, .NT .A, .NT2 .A, .NT .B, .NT2 .B, .SA, .SB]
theorem mem_allSt (s : St) : s ∈ allSt := by
  cases s <;> (try rename_i ph; cases ph) <;> decide
instance : Fintype St := ⟨allSt.toFinset, by intro x; simpa using mem_allSt x⟩
theorem stPrime_injective : Function.Injective stPrime := by decide
theorem stPrime_prime (s : St) : (stPrime s).Prime := by
  have : ∀ s, stPrime s ∈ ({31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ) := by decide
  have h := this s
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> norm_num
theorem stPrime_ne : ∀ s, stPrime s ≠ 2 ∧ stPrime s ≠ 3 ∧ stPrime s ≠ 5 ∧ stPrime s ≠ 7 ∧
    stPrime s ≠ 11 ∧ stPrime s ≠ 13 ∧ stPrime s ≠ 17 ∧ stPrime s ≠ 19 ∧ stPrime s ≠ 23 ∧
    stPrime s ≠ 29 := by decide
theorem regProd_pos (r : Regs) : 0 < regProd r := by unfold regProd; positivity

theorem enc_fact (st : St) (r : Regs) (p : ℕ) :
    (stPrime st * regProd r).factorization p =
     (if stPrime st = p then 1 else 0) + ((if 2 = p then r.a else 0) + (if 3 = p then r.b else 0) +
     (if 5 = p then r.c else 0) + (if 7 = p then r.d else 0) + (if 11 = p then r.e else 0) +
     (if 13 = p then r.f else 0) + (if 17 = p then r.s else 0) + (if 19 = p then r.g else 0) +
     (if 23 = p then r.h else 0) + (if 29 = p then r.m else 0)) := by
  have hp := stPrime_prime st
  unfold regProd
  simp [Nat.factorization_mul, Nat.factorization_pow, hp.factorization,
    Nat.prime_two.factorization, Nat.prime_three.factorization,
    Nat.prime_five.factorization, (by norm_num : Nat.Prime 7).factorization,
    (by norm_num : Nat.Prime 11).factorization, (by norm_num : Nat.Prime 13).factorization,
    (by norm_num : Nat.Prime 17).factorization, (by norm_num : Nat.Prime 19).factorization,
    (by norm_num : Nat.Prime 23).factorization, (by norm_num : Nat.Prime 29).factorization,
    Finsupp.single_apply, hp.ne_zero]

/-- The difference vector `r - cons`. -/
def Regs.diff (r cons : Regs) : Regs :=
  ⟨r.a - cons.a, r.b - cons.b, r.c - cons.c, r.d - cons.d, r.e - cons.e, r.f - cons.f,
   r.s - cons.s, r.g - cons.g, r.h - cons.h, r.m - cons.m⟩

theorem regProd_split {r cons : Regs} (h : cons.le r) :
    regProd r = regProd cons * regProd (r.diff cons) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨a, b, c, d, e, f, s, V, H, M⟩ := r
  obtain ⟨a', b', c', d', e', f', s', V', H', M'⟩ := cons
  simp only at *
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h3
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h4
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h5
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le h6
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h7
  obtain ⟨V, rfl⟩ := Nat.exists_eq_add_of_le h8
  obtain ⟨H, rfl⟩ := Nat.exists_eq_add_of_le h9
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le h10
  simp [regProd, Regs.diff, pow_add]
  ring

theorem regProd_upd (r cons prod : Regs) :
    regProd (r.upd cons prod) = regProd (r.diff cons) * regProd prod := by
  simp [regProd, Regs.upd, Regs.diff, pow_add]; ring

theorem dvd_iff (st st' : St) (cons r : Regs) :
    stPrime st * regProd cons ∣ stPrime st' * regProd r ↔ st = st' ∧ cons.le r := by
  constructor
  · intro h
    have hle := (Nat.factorization_le_iff_dvd
      (Nat.mul_ne_zero (stPrime_prime st).ne_zero (regProd_pos cons).ne')
      (Nat.mul_ne_zero (stPrime_prime st').ne_zero (regProd_pos r).ne')).2 h
    have key : ∀ p, (stPrime st * regProd cons).factorization p ≤
        (stPrime st' * regProd r).factorization p := fun p => hle p
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := stPrime_ne st
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ := stPrime_ne st'
    have k0 := key (stPrime st)
    have ka := key 2
    have kb := key 3
    have kc := key 5
    have kd := key 7
    have ke := key 11
    have kf := key 13
    have ks := key 17
    have kV := key 19
    have kH := key 23
    have kM := key 29
    simp only [enc_fact] at k0 ka kb kc kd ke kf ks kV kH kM
    refine ⟨?_, ?_⟩
    · by_contra hne
      have : stPrime st' ≠ stPrime st := fun h => hne (stPrime_injective h).symm
      simp [this, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6,
        Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10] at k0
    · simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10]
        at ka kb kc kd ke kf ks kV kH kM
      exact ⟨ka, kb, kc, kd, ke, kf, ks, kV, kH, kM⟩
  · rintro ⟨rfl, h⟩
    rw [regProd_split h, ← mul_assoc]
    exact Dvd.intro _ rfl

theorem den_dvd_enc_iff (ρ : Rule) (c : Cfg) : ρ.den ∣ enc c ↔ ρ.fires c = true := by
  simp [Rule.den, enc, dvd_iff, Rule.fires]

theorem enc_apply (ρ : Rule) (c : Cfg) (h : ρ.fires c = true) :
    enc c / ρ.den * ρ.num = enc (ρ.apply c) := by
  simp only [Rule.fires, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hpos : 0 < ρ.den := Nat.mul_pos (stPrime_prime _).pos (regProd_pos _)
  have : enc c = ρ.den * regProd (c.r.diff ρ.cons) := by
    rw [enc, regProd_split h2, Rule.den, h1, mul_assoc]
  rw [this, Nat.mul_div_cancel_left _ hpos, enc, Rule.apply, regProd_upd, Rule.num]
  ring

/-! ## The abstract machine is the first-firing-rule machine -/

theorem find_filter_src (L : List Rule) (c : Cfg) :
    L.find? (fun ρ => ρ.fires c) =
      (L.filter fun ρ => decide (ρ.src = c.st)).find? (fun ρ => ρ.fires c) := by
  induction L with
  | nil => rfl
  | cons ρ L ih =>
    by_cases h : ρ.src = c.st
    · simp [h, List.find?_cons, ih]
    · have : ρ.fires c = false := by simp [Rule.fires, h]
      simp [h, ih, this]

set_option maxHeartbeats 2000000 in
/-- `astep` is exactly "fire the first applicable rule". -/
theorem astep_eq_find (c : Cfg) :
    astep c = (rules.find? fun ρ => ρ.fires c).map fun ρ => ρ.apply c := by
  rw [find_filter_src]
  rcases c with ⟨st, ⟨a, b, c, d, e, f, s, g, h, m⟩⟩
  cases st <;> (try rename_i ph; cases ph)
  all_goals simp only [rules, List.filter_cons, List.filter_nil, St.RA.injEq, St.NT.injEq,
    St.NT2.injEq, reduceCtorEq, decide_true, decide_false, if_true, if_false]
  all_goals simp only [List.find?_cons, List.find?_nil, Rule.fires, Rule.apply, Regs.le,
    Regs.upd, R0, astep]
  all_goals (repeat' split) <;> simp_all <;> omega

/-- FRACTRAN on the encodings of a list of rules = first firing rule. -/
theorem fstep_map (L : List Rule) (c : Cfg) (hL : ∀ ρ ∈ L, Nat.Coprime ρ.num ρ.den) :
    fstep (L.map fun ρ => frac ρ.num ρ.den) (enc c) =
      (L.find? fun ρ => ρ.fires c).map fun ρ => enc (ρ.apply c) := by
  induction L with
  | nil => rfl
  | cons ρ L ih =>
    have hpos : 0 < ρ.den := Nat.mul_pos (stPrime_prime _).pos (regProd_pos _)
    have hc := hL ρ (by simp)
    rw [List.map_cons]
    by_cases h : ρ.fires c = true
    · rw [fstep_cons_pos hc hpos ((den_dvd_enc_iff ρ c).2 h)]
      simp [h, enc_apply ρ c h]
    · rw [fstep_cons_neg hc hpos (fun h' => h ((den_dvd_enc_iff ρ c).1 h'))]
      simp only [List.find?_cons, Bool.eq_false_iff.2 h]
      exact ih (fun ρ' h' => hL ρ' (by simp [h']))

/-- **One FRACTRAN step is one abstract step.** -/
theorem fstep_enc (c : Cfg) : fstep goldbachProg (enc c) = (astep c).map enc := by
  rw [goldbachProg_eq, fstep_map _ _ rules_coprime, astep_eq_find, Option.map_map]
  rfl

/-- The initial abstract configuration: state `RA A`, `a = b = d = 2`, `f = 1`. -/
def startCfg : Cfg := ⟨.RA .A, ⟨2, 2, 0, 2, 0, 1, 0, 0, 0, 0⟩⟩

theorem goldbachStart_eq : goldbachStart = enc startCfg := by decide +kernel

end ConjectureMachines.Goldbach30
