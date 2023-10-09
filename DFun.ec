require import AllCore List Distr SmtMap FinType DList StdBigop. 
(*---*) import Bigreal Bigreal.BRM.

type in_t.
type out_t.

clone import FinType as FT_In with
  type t <- in_t.

clone import MUniFinFun as MUFF_In with
  type t <- in_t,
  
  theory FinT <- FT_In
  
  proof *.

(* 
op doutf : { in_t -> out_t distr | forall (x : in_t), is_lossless (doutf x) } as doutf_ll.
*)

op [lossless] dout : out_t distr.

clone import DList.Program as DL with
  type t <- out_t,  
  op d <- dout.

  
lemma size_behead (s : 'a list) :
  size (behead s) = if s = [] then 0 else size s - 1.
proof. by elim s. qed.

lemma behead_drop (s : 'a list) (i : int)  :
     0 <= i 
  => behead (drop i s) = drop (i + 1) s.
proof.
elim: s i => [// | x s ih i rng_i].
case (i = 0) => [-> //= | neq0_i]; 1: by rewrite drop0.
by rewrite (: ! i <= 0) 2:(: ! i + 1 <= 0) 1,2:/# /= ih // /#.
qed.

lemma head_drop_nth (x0 : 'a) (s : 'a list) (i : int) :
     0 <= i < size s
  => head x0 (drop i s) = nth x0 s i.
proof.
elim: s i => [// | x s ih i /= rng_i].
case (i = 0) => [-> //= | neq0_i].
by rewrite (: ! i <= 0) 1:/# /= ih /#.
qed.

lemma uniq_take_drop_mem (x : 'a) (s : 'a list) (i : int) :
     uniq s
  => (x \in take i s) 
  => ! (x \in drop i s).
proof.
elim: s i => [// | x' s ih i /= [xpnin uqs]].
case (i <= 0) => [// | neq0_i].
case (x = x') => [-> /= | /#].
by move/contra /(_ xpnin): (mem_drop (i - 1) s x').
qed.

lemma uniq_drop_take_mem (x : 'a) (s : 'a list) (i : int) :
     uniq s
  => (x \in drop i s) 
  => ! (x \in take i s).
proof. by smt(uniq_take_drop_mem). qed.


lemma uniq_nth (x0 : 'a) (s : 'a list) :
     uniq s 
  => (forall (i j : int), 0 <= i < size s => 0 <= j < size s => i <> j =>
        nth x0 s i <> nth x0 s j).
proof. by elim: s; smt(nthPn). qed.
     
lemma uniq_index_take_mem (x0 x : 'a) (s : 'a list) (i : int) :
     uniq s
  => index x s <= i < size s
  => ! nth x0 s i \in take (index x s) s.
proof.
move=> uqs rng_i.
rewrite (nthPn x0) => j. rewrite size_take 1:index_ge0.
rewrite (: index x s < size s) 1:/# /=.
move=> rng_j; rewrite nth_take 1:index_ge0 1:/#.
by move/uniq_nth /(_ x0 j i _ _): uqs => /#. 
qed.

lemma eq_from_tofun (s s' : 'a list): 
     size s = card 
  => size s' = card 
  => tofun s = tofun s' 
  => s = s'.
proof.
rewrite /tofun fun_ext => eqsz eqsz' eqf. 
rewrite &(eq_from_nth witness) // 1:/# => i rng_i.
move: (eqf (nth witness enum i)).
by rewrite index_uniq 1:/# 1:enum_uniq.
qed.


op tolist (m : (in_t, out_t) fmap) : (in_t * out_t) list =
  map (fun x => (x, oget m.[x])) enum.

op tolist_sub (m : (in_t, out_t) fmap) (i : int) : (in_t * out_t) list =
  map (fun x => (x, oget m.[x])) (take i enum).

lemma tolistsub_empty (m : (in_t, out_t) fmap) (i : int) :
     i <= 0 
  => tolist_sub m i = [].
proof. by move=>?; rewrite /tolist_sub take_le0. qed.

lemma tolistsub_card m :
  tolist_sub m card = tolist m.
proof. by rewrite /tolist_sub /tolist take_size. qed.

lemma tolistsubS (m : (in_t, out_t) fmap) (i : int) :
     0 <= i < card
  => tolist_sub m (i + 1) 
     = 
     rcons (tolist_sub m i) (nth witness enum i, oget m.[nth witness enum i]).
proof.
elim; elim: i => [@/tolist_sub /= /# | i ge0_i ih ltc_i1].
by rewrite {1}/tolist_sub (take_nth witness) 1:/# map_rcons.
qed.

module Loop_Fmap_Head = {
  proc sample() : (in_t, out_t) fmap = {
    var m : (in_t, out_t) fmap;
    var x : in_t;
    var y : out_t;
    var i : int;
    var w : in_t list;
    
    w <- enum;
    m <- empty;
    while (w <> []) {
      x <- head witness w;
      y <$ dout;
      m.[x] <- y;
      w <- behead w;
    }
    
    return m;    
  }
}.
(*
module Loop_Fmap_Nth = {
  proc sample(n : int) : (in_t, out_t) fmap = {
    var m : (in_t, out_t) fmap;
    var x : in_t;
    var y : out_t;
    var i : int;
    
    i <- 0;
    m <- empty;
    while (i < n) {
      x <- nth witness enum i;
      y <$ dout;
      m.[x] <- y;
      i <- i + 1;
    }
    
    return m;    
  }
}.

module Loop_List_Cons = {
  proc sample(n : int) : (in_t * out_t) list = {
    var m : (in_t * out_t) list;
    var x : in_t;
    var y : out_t;
    
    m <- [];
    while (size m < n) {
      x <- nth witness enum (size m);
      y <$ dout;
      m <- (x, y) :: m;
    }
    
    return m;    
  }
}.
*)
module Loop_List_Rcons = {
  proc sample(n : int) : (in_t * out_t) list = {
    var m : (in_t * out_t) list;
    var x : in_t;
    var y : out_t;
    
    m <- [];
    while (size m < n) {
      x <- nth witness enum (size m);
      y <$ dout;
      m <- rcons m (x, y);
    }
    
    return m;    
  }
}.

module Direct = {
  proc sample() : in_t -> out_t ={
    var f : in_t -> out_t;
    
    f <$ dfun (fun _ => dout);
    
    return f;
  }  
}.

(*
equiv Eqv_Loop_Fmap_Head_Nth :
  Loop_Fmap_Head.sample ~ Loop_Fmap_Nth.sample : n{2} = card ==> ={res}.
proof.
proc.
while (={m} /\ w{1} = drop i{2} enum /\ 0 <= i{2} /\ n{2} = card).
+ wp; rnd; wp; skip => /> &2 ge0_i neqed ltc_i y yin.
  by rewrite -nth0_head nth_drop 3:behead_drop //= -size_eq0 size_drop /#.
wp; skip => />; rewrite drop0; smt(card_gt0).
qed.

lemma Eqv_Loop_Fmap_Nth_List_Rcons (_n : int) :
     0 <= _n <= card
  => equiv[Loop_Fmap_Nth.sample ~ Loop_List_Rcons.sample : 
            ={n} /\ n{1} = _n ==> tolist_sub res{1} _n = res{2}].
proof.
move=> rng_n.
proc.
while (   ={n}
       /\ n{1} = _n
       /\ tolist_sub m{1} i{1} = m{2} 
       /\ i{1} = size m{2}
       /\ 0 <= i{1} <= n{1}).
+ wp; rnd; wp; skip => /> &1 eqsz_i ge0_i _ ltn_i ltn_sz y yin.
  rewrite size_rcons -eqsz_i /=; split => [| /#].
  rewrite tolistsubS 1:/#; congr. 
  + rewrite /tolist_sub &(eq_in_map) => x rng_x /=.
    rewrite get_setE; suff /#: ! (nth witness enum i{1} \in take i{1} enum).
    rewrite (: i{1} = index (nth witness enum i{1}) enum) 1:index_uniq 1:/# 1:enum_uniq //.
    by rewrite uniq_index_take_mem 1:enum_uniq // index_mem mem_nth 1:/#. 
  by rewrite get_set_sameE oget_some.
by wp; skip => /> /#.
qed.
*)

lemma Eqv_Loop_Fmap_Head_List_Rcons (_n : int) :
     0 <= _n <= card
  => equiv[Loop_Fmap_Head.sample ~ Loop_List_Rcons.sample : 
            n{2} = _n ==> tolist_sub res{1} _n = res{2}].
proof.
move=> rng_n.
proc.
splitwhile{1} 3 : (card - size w < _n).
while{1} (   tolist_sub m{1} _n = m{2}
          /\ ! has (mem w{1}) (take _n enum)) (size w{1}).
+ move => &m z.
  wp; sp; conseq (: _ ==> true).
  - move => /> &1 nhas wne y.
    rewrite size_behead wne /=; split => [| /#].
    split => [@/tolist_sub |]. 
    * rewrite -eq_in_map => x xin /=.
      congr; move/hasPn /(_ x xin): nhas => xnin.  
      by rewrite get_setE (: x <> head witness w{1}) 1:-nth0_head //; smt(nthPn).
    by rewrite hasPn => x xin; move/hasPn /(_ x xin): nhas => /#.
  by rnd; skip; rewrite dout_ll.
conseq (: _ 
          ==> 
             tolist_sub m{1} n{2} = m{2} 
          /\ ! has (mem w{1}) (take n{2} enum)); 1: smt(size_ge0).
while (   tolist_sub m{1} (size m{2}) = m{2} 
       /\ w{1} = drop (size m{2}) enum
       /\ n{2} = _n
       /\ card - size w{1} = size m{2}
       /\ size m{2} <= n{2}).
+ wp; rnd; wp; skip => |> &1 &2 eqm -> _ dene ltn_szm _ y yin.
  rewrite size_rcons /= behead_drop 1:/# /=.
  rewrite size_drop 1:/# -?andbA; split; 2: by smt(size_drop).
  rewrite tolistsubS 1:/# /=; congr. 
  - rewrite -{3}eqm /tolist_sub &(eq_in_map) => x rng_x /=.
    rewrite get_setE head_drop_nth 1:/#. 
    suff /#: ! (nth witness enum (size m{2}) \in take (size m{2}) enum).
    rewrite (: (size m{2}) = index (nth witness enum (size m{2})) enum) 1:index_uniq 1:/# 1:enum_uniq //.
    by rewrite uniq_index_take_mem 1:enum_uniq // index_mem mem_nth 1:/#.
  by rewrite head_drop_nth 1:/# get_set_sameE oget_some.
wp; skip => />.
rewrite tolistsub_empty 2:drop0 //=; split => [/# | m m' *].
split => [/#| ]; rewrite hasPn => x xin.
by rewrite (: size m' = _n) 1:/# uniq_take_drop_mem 1:enum_uniq.
qed.

equiv Eqv_Loop_List_Rcons_Sample:
  Loop_List_Rcons.sample ~ Sample.sample : ={n} ==> unzip2 res{1} = res{2}.
proof.
transitivity LoopSnoc.sample (={n} ==> unzip2 res{1} = res{2}) (={n} ==> ={res}); 1,2: by smt().
+ proc.
  while (={n} /\ unzip2 m{1} = l{2} /\ size m{1} = i{2}).
  - by wp; rnd; wp; skip => />; smt(cats1 map_cat size_rcons).
  by wp; skip.
by symmetry; conseq (: ={n} ==> ={res}) => //; apply Sample_LoopSnoc_eq.
qed.


lemma Eqv_Loop_Fmap_Head_Sample (_n : int) :
     0 <= _n <= card
  => equiv[Loop_Fmap_Head.sample ~ Sample.sample : 
        n{2} = _n ==> unzip2 (tolist_sub res{1} _n) = res{2}].
proof.
move=> rng_n.
transitivity Loop_List_Rcons.sample 
             (n{2} = _n ==> tolist_sub res{1} _n = res{2}) 
             (={n} ==> unzip2 res{1} = res{2}); 1,2: by smt().
+ by apply Eqv_Loop_Fmap_Head_List_Rcons.
by apply Eqv_Loop_List_Rcons_Sample.
qed.

equiv Eqv_Loop_Fmap_Head_Sample_Card :
  Loop_Fmap_Head.sample ~ Sample.sample : 
      n{2} = card ==> unzip2 (tolist res{1}) = res{2}.
proof.
conseq (: _ ==> unzip2 (tolist_sub res{1} card) = res{2}) => />.
+ by move=> r; rewrite tolistsub_card.
by move: (Eqv_Loop_Fmap_Head_Sample card _); 1: by smt(card_gt0).
qed.


lemma Pr_Sample_offun &m (f : in_t -> out_t) :
  Pr[Sample.sample(card) @ &m: res = offun f] 
  = 
  big predT (fun y => mu1 dout y) (offun f).  
proof. 
byphoare (: n = card ==> _) => //.
proc.
rnd.
skip => />.
rewrite (: (fun (x : out_t list) => x = offun f) = pred1 (offun f)) 1://.    
rewrite dlist1E; 1: smt(card_gt0). 
by rewrite size_map /card.
qed.


lemma Eq_Pr_Sample_offun_tofun &m (f : in_t -> out_t) :
  Pr[Sample.sample(card) @ &m: res = offun f] 
  = 
  Pr[Sample.sample(card) @ &m: tofun res = f].    
proof. 
byequiv => //.
proc.
rnd.
skip => /> r rin.
by rewrite offunK tofunK; smt(supp_dlist card_gt0).
qed.

lemma Pr_Direct &m (f : in_t -> out_t) :
  Pr[Direct.sample() @ &m : res = f]
  = 
  big predT (fun y => mu1 dout y) (offun f). 
proof.
byphoare => //.
proc. 
rnd.
skip => />. 
by rewrite dfun1E big_mapT.
qed.

equiv Eqv_Sample_Direct :
  Sample.sample ~ Direct.sample: n{1} = card ==> tofun res{1} = res{2}.
proof.
bypr (tofun res{1}) (res{2}) => //.
move => &1 &2 f ->.
by rewrite -Eq_Pr_Sample_offun_tofun Pr_Sample_offun Pr_Direct.
qed.

equiv Eqv_Loop_Fmap_Head_Direct :
  Loop_Fmap_Head.sample ~ Direct.sample : true ==> tofun (unzip2 (tolist res{1})) = res{2}.
proof.
transitivity Sample.sample
             (n{2} = card ==> unzip2 (tolist res{1}) = res{2}) 
             (n{1} = card ==> tofun res{1} = res{2}); 1,2: smt().
+ by apply Eqv_Loop_Fmap_Head_Sample_Card.
by apply Eqv_Sample_Direct.
qed.

lemma tofun_unzip2_tolist m:
  tofun (unzip2 (tolist m)) 
  = 
  fun (x : in_t) => oget m.[x].
proof.
rewrite fun_ext => x @/tofun @/tolist /=.
rewrite -map_comp /(\o) /=.
by rewrite (nth_map witness) 2:nth_index // 1:index_ge0 1:index_mem enumP. 
qed.

equiv Eqv_Loop_Fmap_Head_Direct_Map :
  Loop_Fmap_Head.sample ~ Direct.sample : 
    true ==> (fun (x : in_t) => oget res{1}.[x]) = res{2}.
proof.
conseq (: _ ==> tofun (unzip2 (tolist res{1})) = res{2}) => />.
+ by move=> r; rewrite tofun_unzip2_tolist.
by apply Eqv_Loop_Fmap_Head_Direct.
qed.
