/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Odd]
    obtain ⟨k, hk⟩ := h
    use k
    calc
      n = (n - 1) + 1 := by ring
      _ = 2 * k + 1 := by rw [hk]


theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Even]
    obtain ⟨k, hk⟩ := h
    use k
    calc
      n = (n - 0) := by ring
      _ = 2 * k := by rw [hk]


example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h1
    have h2: (x + 3) * (x - 2) = 0 := by
      calc
      (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
      _ = 0 := by rw [h1]
    have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
    obtain ha | hb := h3
    left
    calc
      x = (x + 3) - 3 := by ring
      _ = 0 - 3 := by rw [ha]
      _ = -3 := by ring
    right
    calc
      x = (x - 2) + 2 := by ring
      _ = 0 + 2 := by rw [hb]
      _ = 2 := by ring
  · intro h1
    obtain ha | hb := h1
    calc
      x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [ha]
      _ = 0 := by ring
    calc
      x ^ 2 + x - 6 = (2) ^ 2 + (2) - 6 := by rw [hb]
      _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h0
    have h1: (2 * a - 5) ^ 2 ≤ 1^2 := by
      calc
      (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * -1 + 5 := by rel [h0]
      _ = 1 ^ 2 := by ring
    have h2: (5 - 2 * a) ^ 2 ≤ 1^2 := by
      calc
      (5 - 2 * a)^2 = (2 * a - 5)^2 := by ring
      _ ≤ 1 ^ 2 := by rel [h1]
    have h3: 2 * a - 5 ≤ 1 := by cancel 2 at h1
    have h4: 5 - 2 * a ≤ 1 := by cancel 2 at h2
    have h5: 2 * a ≤ 2 * 3 := by
      calc
      2 * a = 2 * a - 5 + 5 := by ring
      _ ≤ 1 + 5  := by rel [h3]
      _ = 6 := by ring
    cancel 2 at h5
    have h6: 2 * a ≥ 2 * 2 := by
      calc
      2 * a = 2 * a - 1 + 1 := by ring
      _ ≥ 2 * a - 1 + (5 - 2 * a) := by rel [h4]
      _ = 2 * 2 := by ring
    cancel 2 at h6
    interval_cases a
    left
    numbers
    right
    numbers
  · intro h0
    obtain h2 | h3 := h0
    · calc
      a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw [h2]
      _ = -1 := by ring
      _ ≤ -1 := by numbers
    · calc
      a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw [h3]
      _ = -1 := by ring
      _ ≤ -1 := by numbers


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain h4 | h6 := hn2
  have h5: n = 2 * 2 := by addarith [h4]
  dsimp[Even]
  use 2
  apply h5
  have h5: n = 3 * 2 := by addarith [h6]
  dsimp[Even]
  use 3
  apply h5


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  dsimp[Even]
  obtain h4 | h6 := hn1
  use 2
  have h5: n = 2 * 2 := by addarith [h4]
  apply h5
  use 3
  have h5: n = 3 * 2 := by addarith [h6]
  apply h5


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have h0: 2 * x = 2 * 6 := by
      calc
      2 * x = 2 * x - 1 + 1 := by ring
      _ = 11 + 1 := by rw [h]
      _ = 2 * 6 := by ring
    cancel 2 at h0
  · intro h
    calc
    2 * x - 1 = 2 * 6 - 1 := by rw [h]
    _ = 11 := by ring

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  sorry

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  dsimp [(· ∣ ·)] at *
  dsimp [Int.ModEq] at *
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    addarith [hc]
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    addarith [hc]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [Int.dvd_iff_modEq] at *
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel [hab]
    _ = 0 := by ring

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  sorry
