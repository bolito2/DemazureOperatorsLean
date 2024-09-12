import DemazureOperators.Coxeter

def apply_nilMove [BEq B] (l : List B) (b : B) (i : ℕ) : List B :=
  match i with
  | 0 => match l with
    | [] => []
    | [x] => [x]
    | _ :: _ :: xs => xs
  | i + 1 => match l with
    | [] => []
    | x :: xs => x :: apply_nilMove xs b i

#eval apply_nilMove [1, 1, 3, 3, 5] 3 2

def apply_alternatingWordMove [BEq B] (l : List B) (a b : B) (i m : ℕ) : List B :=
  match i with
  | 0 => match m with
    | 0 => l
    | m + 1 => match l with
      | [] => []
      | a :: xs => b :: apply_alternatingWordMove xs a b i m
      | b :: xs => a :: apply_alternatingWordMove xs a b i m
  | i + 1 => match l with
    | [] => []
    | x :: xs => x :: apply_alternatingWordMove xs a b i m
