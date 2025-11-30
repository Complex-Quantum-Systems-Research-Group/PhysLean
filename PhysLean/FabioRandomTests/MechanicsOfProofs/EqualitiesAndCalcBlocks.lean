import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

-- Example 1.2.1
example {a b : ℝ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring

example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by ring

example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
    calc
    d * (a * f - b * e) = (a * d) * f - d*b*e := by ring
    _ = (b * c) * f - d*b*e := by rw [h1]
    _ = b * (c * f) - d * b * e := by ring
    _ = b * (d * e) - d * b * e := by rw [h2]
    _ = 0 := by ring

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
  a = 2 * b + 5 := by rw [h1]
  _ = 2 * 3 + 5 := by rw [h2]
  _ = 11 := by ring

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
  x = x + 4 - 4 := by ring
  _ = 2 - 4 := by rw [h1]
  _ = -2 := by ring

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
  a = (a - 5 * b) + 5 * b := by ring
  _ = 4 + 5 * b := by rw [h1]
  _ = 4 + 5 * ((b + 2) - 2) := by ring
  _ = 4 + 5 * (3 - 2) := by rw [h2]
  _ = 9 := by ring

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
 calc
 w = (3*w + 1)/3 - 1/3 := by ring
 _ = 4/3 - 1/3 := by rw [h1]
 _ = 1 := by ring

example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
  x = (2*x + 3) - x - 3 := by ring
  _ = x - x - 3 := by rw [h1]
  _ = - 3 := by ring


example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
  x = (2*x - y) - x + y:= by ring
  _ = 4 - x + y := by rw [h1]
  _ = 4 + (y - x + 1) - 1 := by ring
  _ = 4 + 2 - 1 := by rw [h2]

example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
  u = ((u+2*v) + (u-2*v))/2 := by ring
  _ = (4 + 6)/2:= by rw [h1,h2]
  _ = 5 := by ring

example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
  x = (3*(x+y)+(5*x - 3*y))/8 := by ring
  _ = (3*4 + 4)/8 := by rw [h1,h2]
  _ = 2:= by ring
