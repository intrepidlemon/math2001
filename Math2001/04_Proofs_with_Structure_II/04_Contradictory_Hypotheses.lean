/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  have h2m : m ≤ p := Nat.le_of_dvd hp' hmp
  obtain hn | hn_left : m = p ∨ m < p := eq_or_lt_of_le h2m
  · -- the case m = p
    right
    use hn
  -- the case `1 < m`
  have hnot : ¬m ∣ p := by
    apply H
    apply hm_left
    apply hn_left
  contradiction


example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain hl | hg: a ≤ 2 ∨ 3 ≤ a := le_or_succ_le a 2
  · obtain hbl | hgl: b ≤ 1 ∨ 2 ≤ b := le_or_succ_le b 1
    · have h1: c^2 < 3^2 := by
        calc
          c^2 = a^2 + b^2 := by rw [h_pyth]
          _ ≤ 2^2 + b^2 := by rel [hl]
          _ ≤ 2^2 + 1^2 := by rel [hbl]
          _ = 5 := by ring
          _ < 3^2 := by numbers
      cancel 2 at h1
      interval_cases a
      · interval_cases b
        · interval_cases c
          · numbers at h_pyth
          · numbers at h_pyth
      · interval_cases b
        · interval_cases c
          · numbers at h_pyth
          · numbers at h_pyth
    · have h1: b^2 < c^2 := by
        calc
          b^2 < a^2 + b^2 := by extra
          _ = c^2 := by rw [h_pyth]
      cancel 2 at h1
      have h2: b+1 ≤ c := by
        exact Nat.succ_le_of_lt h1
      have h3: c^2 < (b+1)^2 := by
        calc
        c^2 = a^2 + b^2 := by rw [h_pyth]
        _ ≤ 2^2 + b^2 := by rel [hl]
        _ = b^2 + 2*2 := by ring
        _ ≤ b^2 + 2*b := by rel [hgl]
        _ < b^2 + 2*b + 1 := by extra
        _ = (b+1)^2 := by ring
      cancel 2 at h3
      have h4: ¬(c < b+1) := by
        exact not_lt_of_ge h2
      contradiction
  · use hg

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by cancel n at h

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
    obtain hl | hg : y ≤ 0 ∨ 0 < y := le_or_lt y 0
    · calc
        y ≤ 0 := hl
        _ ≤ x := hx
    · sorry


example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  sorry

example : Prime 7 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor <;> numbers
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  sorry

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at *
  obtain ⟨h1, h2⟩ := h
  obtain hl | he : 2 < p ∨ 2 = p := lt_or_eq_of_le h1
  · right
    obtain heven | hodd : Even p ∨ Odd p := Nat.even_or_odd p
    · dsimp [Even] at heven
      have h3: 2 ∣ p := by
        exact heven
      have h4: 2 = 1 ∨ 2 = p := by
        apply h2
        exact h3
      obtain hf | he := h4
      · numbers at hf
      · have hn: 2 < 2 := by
          calc
            2 < p := hl
            _ = 2 := by rw [he]
        numbers at hn
    · exact hodd
  · left
    addarith [he]
