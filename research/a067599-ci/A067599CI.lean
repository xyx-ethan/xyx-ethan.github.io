import FormalConjectures.OEIS.«67599»

/-!
# Integration smoke tests for the patched A067599 theorem
-/

example {n : ℕ} (hn : 2 ≤ n) (hsq : Squarefree n) : n < OeisA67599.a n :=
  OeisA67599.lt_a_of_squarefree hn hsq

example {n : ℕ} (hn : 2 ≤ n) (hsq : Squarefree n) : OeisA67599.a n ≠ n :=
  OeisA67599.a_ne_of_squarefree hn hsq
