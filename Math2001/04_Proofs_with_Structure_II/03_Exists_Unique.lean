/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro y h1 h2
    have h3: y - 2 ≥ -1 := by
      calc
      y - 2 ≥ 1 - 2 := by rel [h1]
      _ = -1 := by ring
    have h4: y - 2 ≤ 1 := by
      calc
      y - 2 ≤ 3 - 2 := by rel [h2]
      _ = 1 := by ring
    have h5: (y - 2)^2 ≤ 1^2 := by
      apply sq_le_sq'
      use h3
      use h4
    have h6: (y - 2)^2 ≤ 1 := by
      calc
      (y-2)^2 ≤ 1^2 := by rel [h5]
      _ = 1 := by ring
    use h6
  · intro y hy
    have h1: (1 - y)^2 ≤ 1 := by
      apply hy
      numbers
      numbers
    have h2: (3 - y)^2 ≤ 1 := by
      apply hy
      numbers
      numbers
    have h3: (y-2)^2 ≤ 0 := by
      calc
      (y - 2)^2 = ((1 - y)^2 + (3 - y)^2 - 2) / 2 := by ring
      _ ≤ (1 + (3 - y)^2 - 2) / 2 := by rel [h1]
      _ ≤ (1 + 1 - 2) / 2 := by rel [h2]
      _ = 0 := by ring
    have h4: (y-2)^2 = 0 := by
      apply le_antisymm
      · exact h3
      · apply pow_two_nonneg
    cancel 2 at h4
    calc
      y = y - 0 := by ring
      _ = y - (y - 2) := by rw [h4]
      _ = 2 := by ring


example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  · intro r hr
    have h1 :=
      calc
      4 * r = (4 * r - 3) + 3 := by ring
      _ = 9 + 3 := by rw [hr]
      _ = 4 * 3 := by ring
    cancel 4 at h1

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro r
    exact Nat.zero_le r
  · intro m hm
    specialize hm 0
    exact Nat.eq_zero_of_le_zero hm

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  sorry
