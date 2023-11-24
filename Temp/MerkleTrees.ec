require import AllCore List BinaryTrees BitEncoding.
(*---*) import BS2Int.

op val_bt (trh : int -> int -> 'a -> 'a -> 'a)
          (bt : 'a bintree)
          (hidx bidx : int) : 'a =
  with bt = Leaf x => x
  with bt = Node l r =>
    trh hidx bidx (val_bt trh l (hidx - 1) (2 * bidx)) (val_bt trh r (hidx - 1) (2 * bidx + 1)). 
  
op cons_ap (trh : int -> int -> 'a -> 'a -> 'a) 
           (bt : 'a bintree) 
           (bs : bool list) 
           (hidx bidx : int) : 'a list =
  with bt = Leaf _, bs = [] => []
  with bt = Leaf _, bs = _ :: _ => witness
  with bt = Node _ _, bs = [] => witness
  with bt = Node l r, bs = b :: bs' =>
    (val_bt trh (if b then l else r) (hidx - 1) (if b then 2 * bidx else 2 * bidx + 1)) 
     :: cons_ap trh (if b then r else l) bs' (hidx - 1) (if b then 2 * bidx + 1 else 2 * bidx). 

op val_ap (trh : int -> int -> 'a -> 'a -> 'a) 
          (ap : 'a list) 
          (bs : bool list)
          (leaf : 'a) 
          (hidx bidx : int) : 'a = 
  with ap = [], bs = [] => leaf
  with ap = [], bs = _ :: _ => witness 
  with ap = _ :: _, bs = [] => witness
  with ap = x :: ap', bs = b :: bs' =>
    trh hidx bidx 
        (if b then x else val_ap trh ap' bs' leaf (hidx - 1) (2 * bidx))
        (if b then val_ap trh ap' bs' leaf (hidx - 1) (2 * bidx + 1) else x).

op extract_collision_bt_ap (trh : int -> int -> 'a -> 'a -> 'a) 
                           (bt : 'a bintree)
                           (ap : 'a list) 
                           (bs : bool list)
                           (leaf : 'a) 
                           (hidx bidx : int) : 'a * 'a * 'a * 'a * int * int =
  with bt = Leaf _, ap = [], bs = [] => witness
  with bt = Leaf _, ap = [], bs = b :: bs' => witness
  with bt = Leaf _, ap = x :: ap', bs = [] => witness
  with bt = Leaf _, ap = x :: ap', bs = b :: bs' => witness
  with bt = Node _ _, ap = [], bs = [] => witness
  with bt = Node _ _, ap = [], bs = b :: bs' => witness
  with bt = Node _ _, ap = x :: ap', bs = [] => witness
  with bt = Node l r, ap = x :: ap', bs = b :: bs' =>
    if b
    then
      if    (val_bt trh l (hidx - 1) (2 * bidx), val_bt trh r (hidx - 1) (2 * bidx + 1)) 
            <> 
            (x, val_ap trh ap' bs' leaf (hidx - 1) (2 * bidx + 1))
         /\ val_bt trh bt hidx bidx = val_ap trh ap bs leaf hidx bidx
      then (val_bt trh l (hidx - 1) (2 * bidx), 
            val_bt trh r (hidx - 1) (2 * bidx + 1), 
            x, 
            val_ap trh ap' bs' leaf (hidx - 1) (2 * bidx + 1), 
            hidx, 
            bidx)
      else extract_collision_bt_ap trh r ap' bs' leaf (hidx - 1) (2 * bidx + 1)
    else
      if    (val_bt trh l (hidx - 1) (2 * bidx), val_bt trh r (hidx - 1) (2 * bidx + 1)) 
            <> 
            (val_ap trh ap' bs' leaf (hidx - 1) (2 * bidx), x)
         /\ val_bt trh bt hidx bidx = val_ap trh ap bs leaf hidx bidx
      then (val_bt trh l (hidx - 1) (2 * bidx), 
            val_bt trh r (hidx - 1) (2 * bidx + 1), 
            val_ap trh ap' bs' leaf (hidx - 1) (2 * bidx), 
            x, 
            hidx, 
            bidx)
      else extract_collision_bt_ap trh l ap' bs' leaf (hidx - 1) (2 * bidx).
  
lemma ecbtapP (trh : int -> int -> 'a -> 'a -> 'a) 
              (bt : 'a bintree)
              (ap : 'a list) 
              (bs : bool list)
              (leaf leaf' : 'a) 
              (bidx : int) :
     fully_balanced bt
  => size ap = size bs
  => height bt = size ap
  => leaf <> leaf'
  => val_bt trh bt (height bt) bidx = val_ap trh ap bs leaf (size ap) bidx
  => vallf_subbt bt bs = Some leaf'
  => let (x1, x1', x2, x2', i, j) = extract_collision_bt_ap trh bt ap bs leaf (height bt) bidx in
        (x1, x1') <> (x2, x2') /\ trh i j x1 x1' = trh i j x2 x2'.
proof.
move=> + + + neq_lf.
elim: ap bs bt bidx => [bs bt bidx fb_bt | x ap ih].
+ rewrite eq_sym size_eq0 => -> /=.
  by case: bt fb_bt => /= /#.
case=> [| b bs]; 1: smt(size_ge0).
by case=> /#.
qed.

lemma ecbtap_vals (trh : int -> int -> 'a -> 'a -> 'a) 
                  (bt : 'a bintree)
                  (ap : 'a list) 
                  (bs : bool list)
                  (leaf leaf' : 'a) 
                  (bsbidx : bool list) :
     fully_balanced bt
  => size ap = size bs
  => height bt = size ap
  => leaf <> leaf'
  => val_bt trh bt (height bt) (bs2int (rev bsbidx)) = val_ap trh ap bs leaf (size ap) (bs2int (rev bsbidx))
  => vallf_subbt bt bs = Some leaf'
  => let (x1, x1', x2, x2', i, j) = extract_collision_bt_ap trh bt ap bs leaf (height bt) (bs2int (rev bsbidx)) in
          x1 = val_bt trh (oget (sub_bt bt (rcons (take (height bt - i) bs) false))) (i - 1) (2 * j)
       /\ x1' = val_bt trh (oget (sub_bt bt (rcons (take (height bt - i) bs) true))) (i - 1) (2 * j + 1)
       /\ x2 = (if nth witness bs (height bt - i) 
                then nth witness ap (height bt - i) 
                else val_ap trh (drop (height bt - i + 1) ap) (drop (height bt - i + 1) bs) leaf (i - 1) (2 * j))
       /\ x2' = (if nth witness bs (height bt - i) 
                 then val_ap trh (drop (height bt - i + 1) ap) (drop (height bt - i + 1) bs) leaf (i - 1) (2 * j + 1) 
                 else nth witness ap (height bt - i))
       /\ 1 <= i <= height bt
       /\ j = bs2int (rev (bsbidx ++ take (height bt - i) bs)).
proof.
move=> + + + neq_lf.
elim: ap bs bt bsbidx => [bs bt bsbidx fb_bt | x ap ih].
+ rewrite eq_sym size_eq0 => -> /=.
  by case: bt fb_bt => /= /#.
case=> [| b bs]; 1: smt(size_ge0).
case=> [/# | l r bsbidx /= [#]].
move=> eqhei fb_l fb_r eqsz eqhesz.
rewrite /vallf_subbt /=.
pose val_l := val_bt trh l _ _.
pose val_r := val_bt trh r _ _.
rewrite (: max (height l) (height r) = size ap) 1:/#.
pose val_ap_l := val_ap trh _ _ _ _ (2 * bs2int (rev bsbidx)).
pose val_ap_r := val_ap trh _ _ _ _ (2 * bs2int (rev bsbidx) + 1).
elim: b => /= eqtrh /= eqlfp; rewrite eqtrh.
+ case (val_l = x /\ val_r = val_ap_r) => /= eqvalxap />.
  - move=> x1 x1' x2 x2' i j ecoll.
    move: (ih bs r (rcons bsbidx true) fb_r _ _ _ _) => /=; 1,2,4: smt().
    * by rewrite rev_rcons bs2int_cons b2i1 /#. 
    rewrite rev_rcons bs2int_cons b2i1 (addzC 1) (: height r = size ap) 1:/# ecoll.
    move => [#] -> -> -> -> ge1_i leszap_i ->.
    rewrite (: ! (1 + size ap - i <= 0)) 1:/# /=.
    rewrite (: 1 + size ap - i <> 0) /=; 1: smt(size_ge0).
    by rewrite -cat_rcons /#.
  by rewrite /= cats0 /= 2!subbt_empty 2!oget_some 2!drop0; smt(size_ge0).
case (val_l = val_ap_l /\ val_r = x) => /= eqvalapx />.
+ move=> x1 x1' x2 x2' i j ecoll.
  move: (ih bs l (rcons bsbidx false) fb_l _ _ _ _) => /=; 1,2,4: smt().
  - by rewrite rev_rcons bs2int_cons b2i0 /#.
  rewrite rev_rcons bs2int_cons b2i0 /= (: height l = size ap) 1:/# ecoll.
  move=> [#] -> -> -> -> ge1_i leszap_i.
  rewrite (: ! (1 + size ap - i <= 0)) 1:/# /=. 
  rewrite (: 1 + size ap - i <> 0) 1:/# /= cat_rcons => -> /#.
by rewrite cats0 /= 2!subbt_empty 2!oget_some 2!drop0; smt(size_ge0).
qed.
