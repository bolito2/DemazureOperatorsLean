import Mathlib.GroupTheory.Coxeter.Inversion

open CoxeterSystem

variable {B : Type*} {M : CoxeterMatrix B}
variable {W : Type*} [Group W] [DecidableEq W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

def number_of_reflection_occurrences (w : List B) (t : W) : ℕ :=
  (cs.leftInvSeq w).count t

def parity_number_of_reflection_occurrences (w : List B) (t : W) : ℤ :=
  (-1) ^ (number_of_reflection_occurrences cs w t)

theorem strong_exchange_property (w : List B) (t : W) (h : IsReflection cs t)
 (h' : ℓ (t * π w) < ℓ (π w)) :
  ∃ (i : Fin w.length), t * π w = π (w.eraseIdx i) := by

  sorry
