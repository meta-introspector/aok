module

public import Cryptids.Goldbach29.Loops

/-!
# The 29-fraction FRACTRAN program halts iff Goldbach's conjecture fails

Main result: `goldbachProg_halts_iff`. Started on `N0 = 710892`, the program
`goldbachProg` halts if and only if some even `n ≥ 4` is not a sum of two primes.

The search keeps `a + b = n`, `b - a = 2c` (so `c` counts the splits still to try). At each
split it trial-divides `a`, then `b`; on success it moves to `n + 2` with `a = 2` (the success
loop `NT_B ⇄ SB` moves `a` into `b` and `c`, then the failure fraction starts the next split), on failure
it moves to `(a + 1, b - 1, c - 1)`, and when `c = 0` no fraction applies and it halts.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach29

open Turing Relation ConjectureMachines.Core.Fractran

/-- The top of the main loop: testing the split `n = a + b`, with `c` splits left. -/
def top (a b c : ℕ) : Cfg := ⟨.RA .A, ⟨a, b, c, 2, 0, 1, 0, 0, 0, 0⟩⟩

/-- `n` has a split `p + (n - p)` into two primes with `a ≤ p ≤ n - p`. -/
def GoodFrom (n a : ℕ) : Prop := ∃ p, a ≤ p ∧ p ≤ n - p ∧ p.Prime ∧ (n - p).Prime

theorem testA (a b c : ℕ) (ha : 2 ≤ a) :
    Reaches astep (top a b c) ⟨.NT .A, ⟨a, b, c, 0, 0, if a.Prime then 1 else 0, 0, 0, 0, 0⟩⟩ :=
  primeTest .A b c a ha (a - 2) 2 rfl le_rfl ha (by intro m h1 h2; omega)

theorem testB (a b c : ℕ) (hb : 2 ≤ b) :
    Reaches astep ⟨.RA .B, ⟨a, b, c, 2, 0, 1, 0, 0, 0, 0⟩⟩
      ⟨.NT .B, ⟨a, b, c, 0, 0, if b.Prime then 1 else 0, 0, 0, 0, 0⟩⟩ :=
  primeTest .B a c b hb (b - 2) 2 rfl le_rfl hb (by intro m h1 h2; omega)

/-- The success loop `NT_B·f·a → SB·b·c`, `SB → NT_B·f`: move `a` into `b` and `c`. -/
theorem loopSucc (k a b c : ℕ) :
    Reaches astep ⟨.NT .B, ⟨a + k, b, c, 0, 0, 1, 0, 0, 0, 0⟩⟩
      ⟨.NT .B, ⟨a, b + k, c + k, 0, 0, 1, 0, 0, 0, 0⟩⟩ := by
  induction k generalizing b c with
  | zero => exact ReflTransGen.refl
  | succ k ih =>
    refine ReflTransGen.head (b := ⟨.SB, ⟨a + k, b + 1, c + 1, 0, 0, 0, 0, 0, 0, 0⟩⟩) ?_
      (ReflTransGen.head (b := ⟨.NT .B, ⟨a + k, b + 1, c + 1, 0, 0, 1, 0, 0, 0, 0⟩⟩) ?_ ?_)
    · simp [astep, ← add_assoc]
    · simp [astep]
    · have := ih (b + 1) (c + 1)
      rwa [add_assoc b, add_assoc c, add_comm 1 k] at this

/-- `a` prime: hand over to the test of `b`. -/
theorem reach_testB (a b c : ℕ) (ha : 2 ≤ a) (hpa : a.Prime) :
    Reaches astep (top a b c) ⟨.RA .B, ⟨a, b, c, 2, 0, 1, 0, 0, 0, 0⟩⟩ := by
  have h1 := testA a b c ha
  simp only [hpa, if_true] at h1
  have h2 : astep ⟨.NT .A, ⟨a, b, c, 0, 0, 1, 0, 0, 0, 0⟩⟩ =
      some ⟨.NT .B, ⟨a, b, c, 1, 0, 0, 0, 1, 0, 0⟩⟩ := by
    simp [astep]
  have h3 : astep ⟨.NT .B, ⟨a, b, c, 1, 0, 0, 0, 1, 0, 0⟩⟩ =
      some ⟨.RA .B, ⟨a, b, c, 2, 0, 1, 0, 0, 0, 0⟩⟩ := by
    simp [astep]
  exact h1.trans ((step_reaches h2).trans (step_reaches h3))

/-- Both halves prime: reach `NT_B` with verdict `f = 1` and clean scratch registers. -/
theorem reach_success (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hpa : a.Prime) (hpb : b.Prime) :
    Reaches astep (top a b c) ⟨.NT .B, ⟨a, b, c, 0, 0, 1, 0, 0, 0, 0⟩⟩ := by
  have h4 := testB a b c hb
  simp only [hpb, if_true] at h4
  exact (reach_testB a b c ha hpa).trans h4

/-- Not both halves prime: reach the end of a test with verdict "composite". -/
theorem reach_composite (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hp : ¬ (a.Prime ∧ b.Prime)) :
    ∃ ph, Reaches astep (top a b c) ⟨.NT ph, ⟨a, b, c, 0, 0, 0, 0, 0, 0, 0⟩⟩ := by
  by_cases hpa : a.Prime
  · have hpb : ¬ b.Prime := fun h => hp ⟨hpa, h⟩
    have h4 := testB a b c hb
    simp only [hpb, if_false] at h4
    exact ⟨.B, (reach_testB a b c ha hpa).trans h4⟩
  · have h1 := testA a b c ha
    simp only [hpa, if_false] at h1
    exact ⟨.A, h1⟩

theorem astep_fail (ph : Ph) (a b c : ℕ) :
    astep ⟨.NT ph, ⟨a, b, c, 0, 0, 0, 0, 0, 0, 0⟩⟩ =
      if 0 < b ∧ 0 < c then some (top (a + 1) (b - 1) (c - 1)) else none := by
  cases ph <;> simp [astep, top]

/-- Success: move on to `n + 2`, split `2 + n`. -/
theorem top_succ (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hpa : a.Prime) (hpb : b.Prime) :
    Reaches₁ astep (top a b c) (top 2 (b + a) (c + a - 1)) := by
  have h1 := reach_success a b c ha hb hpa hpb
  have h2 := loopSucc a 0 b c
  rw [Nat.zero_add] at h2
  have h3 : astep ⟨.NT .B, ⟨0, b + a, c + a, 0, 0, 1, 0, 0, 0, 0⟩⟩ =
      some ⟨.NT2 .B, ⟨1, b + a + 1, c + a, 0, 0, 0, 0, 0, 0, 0⟩⟩ := by
    simp [astep]
  have h4 : astep ⟨.NT2 .B, ⟨1, b + a + 1, c + a, 0, 0, 0, 0, 0, 0, 0⟩⟩ =
      some ⟨.NT .B, ⟨1, b + a + 1, c + a, 0, 0, 0, 0, 0, 0, 0⟩⟩ := by
    simp [astep]
  have h5 : astep ⟨.NT .B, ⟨1, b + a + 1, c + a, 0, 0, 0, 0, 0, 0, 0⟩⟩ =
      some (top 2 (b + a) (c + a - 1)) := by
    simp [astep, top]; omega
  exact TransGen.tail' ((h1.trans h2).trans ((step_reaches h3).trans (step_reaches h4))) h5

/-- Failure with splits left: move on to the split `(a + 1) + (b - 1)`. -/
theorem top_fail (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hp : ¬ (a.Prime ∧ b.Prime))
    (hc : 0 < c) : Reaches₁ astep (top a b c) (top (a + 1) (b - 1) (c - 1)) := by
  obtain ⟨ph, h1⟩ := reach_composite a b c ha hb hp
  have h2 := astep_fail ph a b c
  rw [if_pos ⟨by omega, hc⟩] at h2
  exact TransGen.tail' h1 h2

/-- Failure with no splits left: halt. -/
theorem top_halt (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hp : ¬ (a.Prime ∧ b.Prime)) :
    (eval astep (top a b 0)).Dom := by
  obtain ⟨ph, h1⟩ := reach_composite a b 0 ha hb hp
  have h2 := astep_fail ph a b 0
  rw [if_neg (by omega)] at h2
  exact Part.dom_iff_mem.2 ⟨_, mem_eval.2 ⟨h1, h2⟩⟩

theorem GoodFrom.mono {n a a' : ℕ} (h : a ≤ a') (hg : GoodFrom n a') : GoodFrom n a := by
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := hg
  exact ⟨p, le_trans h hp1, hp2, hp3, hp4⟩

/-- If no remaining split of `n = a + b` works, the machine halts. -/
theorem halts_of_not_good (c : ℕ) : ∀ a b, 2 ≤ a → b = a + 2 * c → ¬ GoodFrom (a + b) a →
    (eval astep (top a b c)).Dom := by
  induction c with
  | zero =>
    intro a b ha hb hng
    have hp : ¬ (a.Prime ∧ b.Prime) := fun ⟨h1, h2⟩ =>
      hng ⟨a, le_rfl, by omega, h1, by rwa [show a + b - a = b by omega]⟩
    exact top_halt a b ha (by omega) hp
  | succ c ih =>
    intro a b ha hb hng
    have hp : ¬ (a.Prime ∧ b.Prime) := fun ⟨h1, h2⟩ =>
      hng ⟨a, le_rfl, by omega, h1, by rwa [show a + b - a = b by omega]⟩
    rw [reaches_eval (top_fail a b (c + 1) ha (by omega) hp (by omega)).to_reflTransGen]
    refine ih (a + 1) (b - 1) (by omega) (by omega) ?_
    rw [show a + 1 + (b - 1) = a + b by omega]
    exact fun h => hng (h.mono (by omega))

/-- If some even `m ≥ a + b` has no Goldbach split, the machine halts. -/
theorem halts_of_counterexample (m : ℕ) (hm : Even m) (hng : ¬ GoodFrom m 2) :
    ∀ N a b c, m - (a + b) = N → 2 ≤ a → b = a + 2 * c → a + b ≤ m →
      (eval astep (top a b c)).Dom := by
  obtain ⟨t, rfl⟩ := hm
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro a b c
    induction c generalizing a b with
    | zero =>
      intro hN ha hb hle
      by_cases hp : a.Prime ∧ b.Prime
      · by_cases heq : a + b = t + t
        · exfalso; apply hng; rw [← heq]
          exact GoodFrom.mono ha ⟨a, le_rfl, by omega, hp.1, by
            rw [show a + b - a = b by omega]; exact hp.2⟩
        · rw [reaches_eval (top_succ a b 0 ha (by omega) hp.1 hp.2).to_reflTransGen]
          exact ihN _ (by omega) 2 (b + a) (0 + a - 1) rfl le_rfl (by omega) (by omega)
      · exact top_halt a b ha (by omega) hp
    | succ c ihc =>
      intro hN ha hb hle
      by_cases hp : a.Prime ∧ b.Prime
      · by_cases heq : a + b = t + t
        · exfalso; apply hng; rw [← heq]
          exact GoodFrom.mono ha ⟨a, le_rfl, by omega, hp.1, by
            rw [show a + b - a = b by omega]; exact hp.2⟩
        · rw [reaches_eval (top_succ a b (c + 1) ha (by omega) hp.1 hp.2).to_reflTransGen]
          exact ihN _ (by omega) 2 (b + a) (c + 1 + a - 1) rfl le_rfl (by omega) (by omega)
      · rw [reaches_eval (top_fail a b (c + 1) ha (by omega) hp (by omega)).to_reflTransGen]
        exact ihc (a + 1) (b - 1) (by omega) (by omega) (by omega) (by omega)

/-- A deterministic system that can always make progress inside `S` never halts from `S`. -/
theorem not_dom_of_progress {σ : Type*} {f : σ → Option σ} (S : Set σ)
    (h : ∀ x ∈ S, ∃ y ∈ S, Reaches₁ f x y) : ∀ x ∈ S, ¬ (eval f x).Dom := by
  intro x hx hdom
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 hdom
  have key : ∀ y ∈ S, ¬ Reaches f x y := by
    refine evalInduction (C := fun a => ∀ y ∈ S, ¬ Reaches f a y) hb ?_
    intro a _ IH y hy hreach
    rcases ReflTransGen.cases_head hreach with rfl | ⟨c, hc, hcy⟩
    · obtain ⟨z, hz, haz⟩ := h a hy
      obtain ⟨a', ha', ha'z⟩ := TransGen.head'_iff.1 haz
      exact IH a' ha' z hz ha'z
    · exact IH c hc y hy hcy
  exact key x hx ReflTransGen.refl

/-- If every even number from `a + b` on has a Goldbach split (from `a` for `a + b` itself),
the machine runs forever. -/
theorem not_halts_of_good (a b c : ℕ) (ha : 2 ≤ a) (hb : b = a + 2 * c)
    (hg : GoodFrom (a + b) a) (hall : ∀ m, a + b < m → Even m → GoodFrom m 2) :
    ¬ (eval astep (top a b c)).Dom := by
  let S : Set Cfg := {x | ∃ a b c, x = top a b c ∧ 2 ≤ a ∧ b = a + 2 * c ∧
    GoodFrom (a + b) a ∧ ∀ m, a + b < m → Even m → GoodFrom m 2}
  refine not_dom_of_progress S ?_ _ ⟨a, b, c, rfl, ha, hb, hg, hall⟩
  rintro _ ⟨a, b, c, rfl, ha, hb, hg, hall⟩
  by_cases hp : a.Prime ∧ b.Prime
  · refine ⟨_, ⟨2, b + a, c + a - 1, rfl, le_rfl, by omega, ?_, ?_⟩,
      top_succ a b c ha (by omega) hp.1 hp.2⟩
    · exact hall _ (by omega) ⟨a + c + 1, by omega⟩
    · intro m hm hev; exact hall m (by omega) hev
  · obtain ⟨p, hp1, hp2, hp3, hp4⟩ := hg
    have hpa : p ≠ a := by
      rintro rfl
      exact hp ⟨hp3, by rwa [show p + b - p = b by omega] at hp4⟩
    refine ⟨_, ⟨a + 1, b - 1, c - 1, rfl, by omega, by omega, ?_, ?_⟩,
      top_fail a b c ha (by omega) hp (by omega)⟩
    · rw [show a + 1 + (b - 1) = a + b by omega]
      exact ⟨p, by omega, hp2, hp3, hp4⟩
    · rw [show a + 1 + (b - 1) = a + b by omega]; exact hall

theorem goodFrom_two_iff (n : ℕ) : GoodFrom n 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n := by
  constructor
  · rintro ⟨p, -, hp2, hp3, hp4⟩
    exact ⟨p, n - p, hp3, hp4, by omega⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    rcases le_total p q with h | h
    · exact ⟨p, hp.two_le, by omega, hp, by rwa [show p + q - p = q by omega]⟩
    · exact ⟨q, hq.two_le, by omega, hq, by rwa [show p + q - q = p by omega]⟩

/-- The abstract machine halts from its start iff Goldbach's conjecture fails. -/
theorem astep_halts_iff :
    (eval astep startCfg).Dom ↔ ∃ n, Even n ∧ 4 ≤ n ∧ ¬ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n := by
  have hs : startCfg = top 2 2 0 := rfl
  rw [hs]
  constructor
  · intro hdom
    by_contra hno
    push_neg at hno
    refine not_halts_of_good 2 2 0 le_rfl rfl ?_ ?_ hdom
    · exact (goodFrom_two_iff 4).2 (hno 4 ⟨2, rfl⟩ le_rfl)
    · intro m hm hev; exact (goodFrom_two_iff m).2 (hno m hev (by omega))
  · rintro ⟨n, hev, hn, hng⟩
    rw [← goodFrom_two_iff] at hng
    exact halts_of_counterexample n hev hng _ 2 2 0 rfl le_rfl rfl hn

/-- The FRACTRAN program simulates the abstract machine step for step. -/
theorem respects_enc : Respects astep (fstep goldbachProg) (fun c n => n = enc c) := by
  rintro c _ rfl
  rcases h : astep c with _ | c'
  · simp [fstep_enc, h]
  · exact ⟨enc c', rfl, TransGen.single (by simp [fstep_enc, h])⟩

/-- **Main theorem.** The 29-fraction program, started on `N0 = 710892`, halts if and
only if some even `n ≥ 4` is not the sum of two primes (i.e. iff Goldbach's conjecture fails). -/
theorem goldbachProg_halts_iff :
    FractranHaltsFrom goldbachProg goldbachStart ↔
      ∃ n, Even n ∧ 4 ≤ n ∧ ¬ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n := by
  rw [FractranHaltsFrom, goldbachStart_eq, tr_eval_dom respects_enc rfl, astep_halts_iff]

end ConjectureMachines.Goldbach29
