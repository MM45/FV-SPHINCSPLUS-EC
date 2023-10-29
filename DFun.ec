require import AllCore List Distr DJoin SmtMap FinType StdBigop. 
(*---*) import Bigreal Bigreal.BRM.

type in_t.
type out_t.

clone import FinType as FT_In with
  type t <- in_t.


clone import MUniFinFun as MUFF_In with
  type t <- in_t,
  
  theory FinT <- FT_In
  
  proof *.


module Loop_Fmap = {
  proc sample(d : in_t -> out_t distr, xs : in_t list) : (in_t, out_t) fmap = {
    var m : (in_t, out_t) fmap;
    var x : in_t;
    var y : out_t;
    
    m <- empty;
    while (xs <> []) {
      x <- head witness xs;
      y <$ d x;
      m.[x] <- y;
      xs <- behead xs;
    }
    
    return m;    
  }
}.

module Loop_List_Rcons = {
  proc sample(d : in_t -> out_t distr, xs : in_t list) : (in_t * out_t) list = {
    var m : (in_t * out_t) list;
    var x : in_t;
    var y : out_t;
    
    m <- [];
    while (xs <> []) {
      x <- head witness xs;
      y <$ d x;
      m <- rcons m (x, y);
      xs <- behead xs;
    }
    
    return m;    
  }
}.
  
module Direct_Fun = {
  proc sample(d : in_t -> out_t distr) : in_t -> out_t ={
    var f : in_t -> out_t;
    
    f <$ dfun d;
    
    return f;
  }  
}.



section.

local equiv Eqv_Loop_Fmap_Loop_List_Rcons :
  Loop_Fmap.sample ~ Loop_List_Rcons.sample : 
    ={d, xs} /\ uniq xs{1} 
    ==>
    forall (x : in_t), res{1}.[x] = assoc res{2} x. 
proof.
proc => /=.
seq 1 1: (#pre /\ m{1} = empty /\ m{2} = []); 1: by wp.
exists* xs{2}; elim* => xss.
while (   ={d, xs}
       /\ uniq xss 
       /\ unzip1 m{2} ++ xs{2} = xss
       /\ #post).
+ wp; rnd; wp; skip => /> &1 &2 uqs eqm neqn_xs y yin.
  split => [| x]; 1: by rewrite map_rcons /= -cats1 -catA /= head_behead.
  rewrite -cats1 assoc_cat; case (x = head witness xs{2}) => [-> | neqh_x].
  - rewrite get_set_sameE (: ! head witness xs{2} \in unzip1 m{2}) /=.
    *  move/cat_uniq: uqs => [#] _ /hasPn /(_ (head witness xs{2})) + _.
      by rewrite -(mem_head_behead witness).
    by rewrite assoc_cons.
  have eqinx: forall x, x \in m{1} <=> x \in unzip1 m{2}.
  - move=> x'; split => xpin; move: (eqm x'); apply contraLR => /= xpnin.
    * by move/domE: xpin => m1nn; move: xpnin; rewrite -assocTP /#.
    by move/assocTP: xpin => m1nn; move: xpnin; rewrite domE /#.
  rewrite get_set_neqE //; case: (x \in unzip1 m{2}); 1: by rewrite eqm.
  by rewrite -eqinx domE /= => ->; rewrite assoc_cons neqh_x assoc_nil.
by wp; skip => /> &2 uqxs; rewrite emptyE assoc_nil.
qed.

local lemma Pr_Direct_Fun &m (df : in_t -> out_t distr) (f : in_t -> out_t) :
  Pr[Direct_Fun.sample(df) @ &m : res = f] 
  = 
  mu1 (dfun df) f.
proof.
byphoare (: arg = df ==> res = f) => //.
proc.
by rnd; skip.
qed.

local clone import JoinMapSampling as JMS with
  type ta <- in_t,
  type tb <- out_t
  
  proof *.

local lemma Pr_S_sample_tofun &m (df : in_t -> out_t distr) (f : in_t -> out_t) :
  Pr[S.sample(df, enum) @ &m : tofun res = f] 
  = 
  mu1 (dfun df) f.
proof.
byphoare (: arg = (df, enum) ==> tofun res = f) => //.
proc.
rnd; skip => />.
rewrite (: (fun (x : out_t list) => tofun x = f) = (pred1 f) \o tofun) 1:fun_ext //.
by rewrite -dfunE_djoin.
qed.

equiv Eqv_Loop_Fmap_Direct_Fun (df : in_t -> out_t distr) :
  Loop_Fmap.sample ~ Direct_Fun.sample : 
    arg{1} = (df, enum) /\ arg{2} = df 
    ==>
    (fun (x : in_t) => oget res{1}.[x]) = res{2}.
proof.
transitivity S.sample
             (={d, xs} /\ xs{1} = enum ==> (fun (x : in_t) => oget res{1}.[x]) = tofun res{2})
             (arg{1} = (df, enum) /\ arg{2} = df ==> tofun res{1} = res{2}) => //; 1: smt(enum_uniq).
+ transitivity Loop_List_Rcons.sample
               (={d, xs} /\ uniq xs{1} ==> forall (x : in_t), res{1}.[x] = assoc res{2} x)
               (={d, xs} /\ xs{1} = enum ==> size res{2} = card /\ res{1} = zip enum res{2}) => //; 1: smt(enum_uniq).
  - move=> /> &1 &2 eqx eqc.
    rewrite fun_ext => x; rewrite eqx /tofun.
    search assoc uniq. search assoc index.
    rewrite assoc_zip 1:eqc // (onth_nth witness) 2:oget_some //.
    by rewrite index_ge0 eqc index_mem enumP.
  - by apply Eqv_Loop_Fmap_Loop_List_Rcons.
  transitivity S.loop_first
               (={d, xs} /\ xs{1} = enum ==> size res{2} = card /\ res{1} = zip enum res{2})
               (={d, xs} ==> ={res}) => //; 1: smt().
  - proc.
    while (   ={d, xs} 
           /\ xs{2} = drop (size l{2}) enum
           /\ m{1} = zip (take (size l{2}) enum) l{2}
           /\ size l{2} = card - size xs{2}).
    * wp; rnd; wp; skip => /> &2 eqszl ^. 
      rewrite -{1}size_eq0 => neq0_szxs nnxs y yin.
      rewrite size_rcons; split; 1: by rewrite (drop_nth witness) //; smt(size_ge0).
      split; last by move: nnxs eqszl; pose xs := drop (size l{2}) enum; case (xs) => // /#.
      rewrite -zip_rcons 1:size_take; 1,2: smt(size_ge0).
      by congr; rewrite -nth0_head (take_nth witness) 2:nth_drop //; smt(size_ge0).
    by wp; skip => />; rewrite drop0 take0 /= => l _ ->; rewrite take_size.
  - symmetry.
  conseq (: ={d, xs} ==> ={res}) => //; 1: by smt().
  by apply Sample_Loop_first_eq.  
bypr (tofun res{1}) (res{2}) => // /> &1 &2 l -> /= ->.
by rewrite Pr_Direct_Fun Pr_S_sample_tofun.
qed.

end section.
