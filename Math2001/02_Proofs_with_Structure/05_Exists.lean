/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · apply ne_of_lt
    have h1: x * t < x * 0
    · calc
      x * t < 0 := by rel [hxt]
      _ = 0 * 0 := by ring
      _ = x * 0 := by ring
    cancel x at h1

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers


example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  have h1: (a + 1) ^ 2 - a ^ 2 = 2 * a + 1 := by ring
  use a + 1
  use a
  apply h1


example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  have h1: p < (p + q) / 2 := by
    calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  have h2: q > (p + q) / 2 := by
    calc
      q = (q + q) / 2 := by ring
      _ > (p + q) / 2 := by rel [h]
  use (p + q) / 2
  constructor
  apply h1
  apply h2

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/

example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  sorry

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
    use ((b + c) - a) / 2
    use ((a + c) - b) / 2
    use ((a + b) - c) / 2
    constructor
    calc
      (b + c - a) / 2 ≥ (a - a) / 2 := by rel [ha]
      _ = 0 := by ring
    constructor
    calc
      (a + c - b) / 2 ≥ (b - b) / 2 := by rel [hb]
      _ = 0 := by ring
    constructor
    calc
      (a + b - c) / 2 ≥ (c - c) / 2 := by rel [hc]
      _ = 0 := by ring
    constructor
    ring
    constructor
    ring
    ring
