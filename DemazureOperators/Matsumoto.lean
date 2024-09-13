import DemazureOperators.Coxeter
open CoxeterSystem

variable {B : Type}  [DecidableEq B]
variable {W : Type} [Group W] [DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

inductive CoxeterMove (cs : CoxeterSystem M W) where
| nil (i : B) (p : ℕ) : CoxeterMove cs
| braid (i j : B) (p : ℕ) : CoxeterMove cs

def apply_coxeterMove (s : CoxeterMove cs) (l : List B) : List B :=
  match s with
  | CoxeterMove.nil i p =>
    match p with
    | 0 =>
      if l.take 2 = [i, i] then
        l.drop 2
      else
        l
    | p + 1 =>
      match l with
      | [] => []
      | h::t => h :: apply_coxeterMove (CoxeterMove.nil i p) t

  | CoxeterMove.braid i j p =>
    match p with
    | 0 =>
      if l.take (M i j) = braidWord M i j then
        braidWord M i j ++ l.drop (M i j)
      else
        l
    | p + 1 =>
      match l with
      | [] => []
      | h::t => h :: apply_coxeterMove (CoxeterMove.braid i j p) t

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

theorem coxeterMove_wordProd (cm : CoxeterMove cs) (l : List B) : π (apply_coxeterMove cs cm l) = π l := by
  cases cm with
  | nil i p =>
    match p with
    | 0 =>
      simp[apply_coxeterMove]
      by_cases h : l.take 2 = [i, i]
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
    | p + 1 =>
      match l with
      | [] => simp[apply_coxeterMove]
      | h::t =>
        simp[apply_coxeterMove, wordProd_cons]
        exact coxeterMove_wordProd (CoxeterMove.nil i p) t

  | braid i j p =>
    match p with
    | 0 =>
      simp[apply_coxeterMove]
      by_cases h : List.take (M.M i j) l = braidWord M i j
      · simp[h]
        have h' : l = l.take (M.M i j) ++ l.drop (M.M i j) := by simp
        nth_rewrite 2 [h']
        repeat rw[wordProd_append]
        rw[h]
      · simp[h]
    | p + 1 =>
      match l with
      | [] => simp[apply_coxeterMove]
      | h::t =>
        simp[apply_coxeterMove, wordProd_cons]
        exact coxeterMove_wordProd (CoxeterMove.braid i j p) t
