import DemazureOperators.Coxeter

variable {B : Type*} [DecidableEq B]

structure Move where
  pre : List B
  post : List B

def apply_move (s : Move) (l : List B) :=
  if l.take s.pre.length = s.pre then
    s.post ++ l.drop s.pre.length
  else
    l

#eval apply_move {pre := [1, 2], post := [3, 4]} [1, 2, 3, 4, 5]

def nil_move (i : B) : @Move B := {pre := [i, i], post := []}

open CoxeterSystem

variable {B : Type}  [DecidableEq B]
variable {W : Type} [Group W] [DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

theorem nil_move_wordProd (i : B) (l : List B) : π (apply_move (nil_move i) l) = π l := by
  simp [apply_move, nil_move]
  by_cases h: l.take 2 = [i, i]
  · simp[h]
    have h' : l = l.take 2 ++ l.drop 2 := by simp
    nth_rewrite 2 [h']
    rw[wordProd_append]
    rw[h]
    simp
    convert_to cs.wordProd ([i] ++ [i]) = 1
    rw[wordProd_append]
    simp
  · simp[h]
