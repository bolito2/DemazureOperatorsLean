import DemazureOperators.Matsumoto

variable (n : ℕ)
def M := CoxeterMatrix.Aₙ n
def cs := (M n).toCoxeterSystem
def W := (M n).Group

abbrev S (n : ℕ) := Equiv.Perm (Fin n)
instance : Group (S (n + 1)) := Equiv.Perm.permGroup
instance : Monoid (S (n + 1)) := sorry

def f_simple : Fin n → S (n + 1) :=
  fun i => Equiv.swap i (i + 1)


theorem f_liftable : (M n).IsLiftable (f_simple n) := sorry

def equiv : W n → S (n + 1) :=
  lift
