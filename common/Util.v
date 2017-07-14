Definition pair_size {A B : Set} size1 size2 (pair: A*B) :=
  let '(x, y) := pair in
  size1 x + size2 y.
