require import List.

type 'a tree = [
    Empty
  | Node of 'a & ('a tree) list
].
