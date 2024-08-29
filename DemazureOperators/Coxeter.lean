import Mathlib.GroupTheory.Coxeter.Inversion

open CoxeterSystem

variable {B : Type*} {M : CoxeterMatrix B}
variable {W : Type*} [Group W] [DecidableEq W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

def Z2 : Type := Multiplicative (ZMod 2)

#eval (Multiplicative.ofAdd 1 : Z2) * Multiplicative.ofAdd 1

def number_of_reflection_occurrences (w : List B) (t : W) : ℕ :=
  (cs.leftInvSeq w).count t

def parity_number_of_reflection_occurrences (w : List B) (t : W) : Z2 :=
  Multiplicative.ofAdd (number_of_reflection_occurrences cs w t)

def T := { t : W // IsReflection cs t }

def permutation_map (w : List B) : W × Z2 → W × Z2 :=
  fun ⟨t, z⟩ => (π w * t * (π w)⁻¹ , z * (parity_number_of_reflection_occurrences cs w t))

theorem strong_exchange_property (w : List B) (t : W) (h : IsReflection cs t)
 (h' : ℓ (t * π w) < ℓ (π w)) :
  ∃ (i : Fin w.length), t * π w = π (w.eraseIdx i) := by

  sorry
