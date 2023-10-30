require import AllCore List Distr FinType Dexcepted DMap DFun SmtMap.
require import FunSamplingLib.
require BooleanFunctions KeyedHashFunctionsO Reprogramming.


type key.
type input.
type output.

clone import FinType as FinKey with
  type t <= key.

clone import FinType as FinIn with
  type t <= input.
  
clone import FinType as FinOut with
  type t <= output.

axiom gt1_cardout : 1 < FinOut.card.

clone import MUniFinFun as MUFF_Key with
  type t <= key,
  
  theory FinT <= FinKey.

clone import MUniFinFun as MUFF_In with
  type t <= input,
  
  theory FinT <= FinIn.

clone import MFinite as MF_Out with
  type t <= output,
  
  theory Support <= FinOut.

op doutput = MF_Out.dunifin.

clone import BooleanFunctions as BF with
  type in_t <- input,
  type out_t <- output,
  
  theory FinIn <- FinIn,
  theory FinOut <- FinOut,
  theory LR.MUFF <- MUFF_In,
  theory LR.MFY <- MF_Out
  
  proof *.
  realize gt1_cardout by exact: gt1_cardout.
    
op [lossless full uniform] df : (key -> input -> output) distr.

lemma df_funi : is_funiform df.
proof. by rewrite is_full_funiform 1:df_fu df_uni. qed.

clone import KeyedHashFunctionsO as KHFO with
  type key_t <- key,
  type in_t <- input,
  type out_t <- output,
  
    op df <- df
    
  proof *.
  realize df_ll by exact: df_ll.


(* Concrete instantiation of df *)
op dfcs : (input -> output) distr = 
  dfun (fun (_ : input) => doutput).

lemma dfcs_ll : is_lossless dfcs.
proof. by rewrite dfun_ll => x; rewrite dunifin_ll. qed.

lemma dfcs_fu : is_full dfcs.
proof. by rewrite dfun_fu => x; rewrite dunifin_fu. qed.

lemma dfcs_uni : is_uniform dfcs.
proof. by rewrite dfun_uni => x; rewrite dunifin_uni. qed.


op kdfcs = fun (_ : key) => dfcs.

op dfc : (key -> input -> output) distr = dfun kdfcs.

lemma dfc_ll : is_lossless dfc.
proof. by rewrite dfun_ll => x; rewrite dfcs_ll. qed.

lemma dfc_fu : is_full dfc.
proof. by rewrite dfun_fu => x; rewrite dfcs_fu. qed.

lemma dfc_uni : is_uniform dfc.
proof. by rewrite dfun_uni => x; rewrite dfcs_uni. qed.

lemma eq_df_dfc : df = dfc.
proof.
apply eq_funi_ll; 2,4: by rewrite ?(df_ll, dfc_ll).
+ by apply is_full_funiform; 1,2 : rewrite ?(df_uni, df_fu).
by apply is_full_funiform; 1,2 : rewrite ?(dfc_uni, dfc_fu).
qed.


(* 
  Auxiliary module for query counting.
*)
module Counting_O (O : Oracle_t) : Oracle_t = {
  var ctr : int
  
  proc get(k : key, x : input) : output = {
    var y : output;
    
    ctr <- ctr + 1;
    
    y <@ O.get(k, x);
    
    return y;
  }
}.


(* Auxiliary results used in multiple proofs *)
clone import DMapSampling as DMS with
  type t1 <- (input -> output) * (key -> input -> output),
  type t2 <- key -> input -> output
  
  proof *.

module EquivSamplings = {
  proc df() = {
   var g : key -> input -> output;
    
    g <$ df;
    
    return g;
  }

  proc dfc_indep(k : key) = {
    var gk : input -> output;
    var g : key -> input -> output;
    
    gk <$ dfcs;
    
    g <$ dfc;
    
    return (fun k' => if k' = k then gk else g k');
  }
}.

equiv Eqv_df_dfc_indep :
  EquivSamplings.df ~ EquivSamplings.dfc_indep : true ==> ={res}.
proof.
proc.
transitivity{1} {g <$ dfc;}
                (true ==> ={g})
                (true ==> g{1} = fun (k' : key) => if k' = k{2} then gk{2} else g{2} k') => //.
+ rnd; skip => />.
  by rewrite eq_df_dfc.
transitivity{2} {g <$ dlet (kdfcs k) (fun gk => dfun kdfcs.[k <- dunit gk]);}
                (true ==> ={g})
                (={k} ==> g{1} = fun (k' : key) => if k' = k{2} then gk{2} else g{2} k'); 1,2: smt().
+ rnd; skip => /> &2.
  by rewrite -(MUFF_Key.dfunE_dlet_fix1 _ k{2}).    
pose d := dlet dfcs (fun gk => dmap dfc (fun g => (gk, g))).
transitivity{1} {g <@ S.sample(d, fun (gkg : _ * _) (k' : key) => 
                                    if k' = k then gkg.`1 else gkg.`2 k'); }
                (={k} ==> ={g})
                (={k} ==> g{1} = fun k' => if k' = k{2} then gk{2} else g{2} k'); 1,2: by smt().
+ inline *.
  wp; sp.
  rnd.
  skip => /> &2; rewrite ?dmap_id.
  split => [g gin | h g].
  - congr => @/d.
    rewrite dmap_dlet; congr => //.
    rewrite fun_ext => gk.
    rewrite dmap_comp /(\o) /dfc /kdfcs /"_.[_<-_]" /=.
    rewrite (MUFF_Key.dmap_dfun _ (fun k' f => if k' = k{2} then gk else f)) /=.
    congr; rewrite fun_ext => k'.
    case (k{2} = k') => [->|] /=; 1: by rewrite dmap_cst 1:dfcs_ll.
    by rewrite eq_sym => -> /=; rewrite dmap_id.
  rewrite supp_dlet => -[gk [gkin /=]]; rewrite supp_dmap dfun_supp => gin. 
  exists (gk, g); split => /=.  
  + rewrite /d supp_dlet; exists gk; rewrite gkin /= supp_dmap.
    by exists g; rewrite dfc_fu. 
  rewrite fun_ext => k'. move: (gin k').
  rewrite  /"_.[_<-_]" /=; case (k' = k{2}) => [-> /=|]; 1: by rewrite supp_dunit.
  by rewrite eq_sym.
transitivity{1} {g <@ S.map(d, fun (gkg : _ * _) (k' : key) => 
                                    if k' = k then gkg.`1 else gkg.`2 k'); }
                (={k} ==> ={g})
                (={k} ==> g{1} = fun k' => if k' = k{2} then gk{2} else g{2} k'); 1,2: by smt().
+ by call sample.
inline *.
wp; sp.
rnd : *0 *0.
skip => />.
by rewrite dmap_id.
qed.


(** Bound for SPR **)
theory SPRBound.

op [lossless] dkey : key distr.
op [lossless] dinput : input distr.

clone import SPR as KHFO_SPR with
  op din <- dinput,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: dinput_ll.
  realize dkey_ll by exact: dkey_ll.

module (R_BFFind_SPR (A : Adv_SPR) : Adv_BFFind) (BFO : BFOF_t) = {
  var k0 : key
  var x0 : input
  var y0 : output
  var gk : input -> output
  var g : key -> input -> output
    
  module O_R_BFFind_SPR : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var b : bool;
      var y : output;
      
      if (k = k0) {
        b <@ BFO.query(x);
        y <- if !b /\ x <> x0 then gk x else y0;
      } else { 
        y <- g k x;
      }
      
      return y;
    }
  }

  proc find() : input = {
    var x' : input;
    
    k0 <$ dkey;
    x0 <$ dinput;
    y0 <$ doutput;
    
    gk <$ dfun (fun (_ : input) => doutput \ (pred1 y0));
    g <$ dfc;
            
    x' <@ A(O_R_BFFind_SPR).find(k0, x0);
    
    return x';
  }
}.


section.

declare module A <: Adv_SPR {-KHFO.O_Default, -R_BFFind_SPR, -BFOF, -BFOD}.

local lemma SPR_Implies_BFFind &m :
  Pr[KHFO_SPR.SPR(A, KHFO.O_Default).main() @ &m : res] 
  <= 
  Pr[BF_Find(R_BFFind_SPR(A), BFOF).main() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
wp.
swap{1} [2..3] -1; swap{2} [2..3] -1.
seq 2 2 : (={glob A} /\ k{1} = R_BFFind_SPR.k0{2} /\ x{1} = R_BFFind_SPR.x0{2}).
+ by rnd; rnd.
seq 1 4 : (   #pre 
           /\ (forall (k : key, x : input),
                 O_Default.f{1} k x
                 =
                 if k = R_BFFind_SPR.k0{2}
                 then (if !BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                      then R_BFFind_SPR.gk{2} x 
                      else R_BFFind_SPR.y0{2})
                 else R_BFFind_SPR.g{2} k x)
           /\ (forall (x : input),
                 R_BFFind_SPR.gk{2} x <> R_BFFind_SPR.y0{2})).
+ conseq (: true 
            ==>
               (forall (k : key, x : input),
                 O_Default.f{1} k x
                 =
                 if k = R_BFFind_SPR.k0{2}
                 then (if !BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                      then R_BFFind_SPR.gk{2} x 
                      else R_BFFind_SPR.y0{2})
                 else R_BFFind_SPR.g{2} k x)
            /\ (forall (x : input),
                 R_BFFind_SPR.gk{2} x <> R_BFFind_SPR.y0{2})) => //.
  transitivity{1} {O_Default.f <@ EquivSamplings.df();}
                  (true ==> ={O_Default.f})
                  (true 
                   ==>
                     (forall (k : key, x : input),
                       O_Default.f{1} k x
                       =
                       if k = R_BFFind_SPR.k0{2}
                       then (if !BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                            then R_BFFind_SPR.gk{2} x 
                            else R_BFFind_SPR.y0{2})
                       else R_BFFind_SPR.g{2} k x)
                   /\ (forall (x : input),
                        R_BFFind_SPR.gk{2} x <> R_BFFind_SPR.y0{2})); 1,2: smt().
  - inline *.
    by wp; rnd.
  transitivity{1} {O_Default.f <@ EquivSamplings.dfc_indep(k);}
                  (true ==> ={O_Default.f})
                  (k{1} = R_BFFind_SPR.k0{2}
                   ==>
                     (forall (k : key, x : input),
                       O_Default.f{1} k x
                       =
                       if k = R_BFFind_SPR.k0{2}
                       then (if !BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                            then R_BFFind_SPR.gk{2} x 
                            else R_BFFind_SPR.y0{2})
                       else R_BFFind_SPR.g{2} k x)
                   /\ (forall (x : input), 
                         R_BFFind_SPR.gk{2} x <> R_BFFind_SPR.y0{2})); 1,2: smt().
  - by call Eqv_df_dfc_indep.
  inline *.
  wp; sp => />.
seq 1 3 : (   (forall (x : input), 
                 gk{1} x 
                 =
                 if !BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                 then R_BFFind_SPR.gk{2} x 
                 else R_BFFind_SPR.y0{2})
           /\ (forall (x : input),
                 R_BFFind_SPR.gk{2} x <> R_BFFind_SPR.y0{2})); last first.
  - by rnd; skip => /> /#.
  transitivity{1} {gk <@ LR.LambdaRepro.left();}
                (true ==> ={gk})
                (true 
                 ==> 
                    (forall (x : input),
                       gk{1} x 
                       =
                       if ! BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                       then R_BFFind_SPR.gk{2} x
                       else R_BFFind_SPR.y0{2})
                 /\ (forall (x : input),
                       R_BFFind_SPR.gk{2} x <> R_BFFind_SPR.y0{2})); 1,2: smt().
  - inline *.
    by wp; rnd.
  transitivity{1} {gk <@ LR.LambdaRepro.right(x);}
                  (true ==> ={gk})
                  (x{1} = R_BFFind_SPR.x0{2} 
                   ==> 
                     (forall (x : input),
                         gk{1} x 
                         =
                         if ! BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                         then R_BFFind_SPR.gk{2} x
                         else R_BFFind_SPR.y0{2})
                   /\ (forall (x : input),
                         R_BFFind_SPR.gk{2} x <> R_BFFind_SPR.y0{2})); 1,2: smt().
  - by call LR.main_theorem.
  inline *.
  wp; sp => /=.
  swap{1} 1 1.
  rnd; rnd; rnd; skip => /> ? ? ? ? ? ? _ /dfun_supp + x.
  by move => /(_ x) /= /supp_dexcepted [@/pred1].
call (: (forall (k : key, x : input),
           O_Default.f{1} k x
           =
           if k = R_BFFind_SPR.k0{2}
           then (if !BFOF.f{2} x /\ x <> R_BFFind_SPR.x0{2} 
                then R_BFFind_SPR.gk{2} x 
                else R_BFFind_SPR.y0{2})
           else R_BFFind_SPR.g{2} k x)).
+ proc; inline *.
  by wp; skip => /> /#.
by wp; skip => /> /#.
qed.

local lemma SPR_Implies_BFDistinguish &m:
  Pr[KHFO_SPR.SPR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_SPR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_SPR(A)), BFOD).main(true) @ &m : res] |.
proof.
apply (StdOrder.RealOrder.ler_trans Pr[BF_Find(R_BFFind_SPR(A), BFOF).main() @ &m : res]); last first.
+ by rewrite (Find_Implies_Distinguish &m (R_BFFind_SPR(A))).
by rewrite SPR_Implies_BFFind.
qed.

end section.

end SPRBound.


(** Bound for TCR **)
theory TCRBound.

op [lossless full uniform] dkey : key distr.

clone import KHFO.TCR as KHFO_TCR with 
  op dkey <- dkey
  
  proof *.
  realize dkey_ll by exact: dkey_ll.

module (R_BFFind_TCR (A : Adv_TCR) : Adv_BFFind) (BFO : BFOF_t) = {
  var g : key -> input -> output
  var f : input -> output
  var k0 : key
  var x0 : input
  var y0 : output
  var ks : key list
  
  module O_R_BFFind_TCR_Pick : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var y : output;
      
      ks <- rcons ks k;
      
      return g k x; 
    }
  }
  
  module O_R_BFFind_TCR_Find : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var b : bool;
      var y : output;
      
      if (k = k0) {
        b <@ BFO.query(x);
        y <- if !b /\ x <> x0 then f x else y0;
      } else {
        y <- g k x;
      }
      
      return y;
    }
  }

  proc find() : input = {
    var x' : input;
    
    ks <- [];
    
    k0 <$ dkey;
    y0 <$ doutput;
    
    f <$ MUFF_In.dfun (fun (_ : input) => doutput \ (pred1 y0));
    g <$ dfc;
    
    x0 <@ A(O_R_BFFind_TCR_Pick).pick();
            
    x' <@ A(O_R_BFFind_TCR_Find).find(k0);
    
    return x';
  }
}.


section.

declare module A <: Adv_TCR {-KHFO.O_Default, -BFOF, -BFOD, -R_BFFind_TCR, -Counting_O}.

local module TCR_NoRep = {
  var k0 : key
  var g : key -> input -> output
    
  module O_TCR_NoRep : Oracle_t = {
    proc get(k : key, x : input) : output = {
      return g k x;
    }
  }
    
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    
    k0 <$ dkey;
    g <$ dfc;
    
    x <@ A(O_TCR_NoRep).pick();
    y <@ O_TCR_NoRep.get(k0, x);
    
    x' <@ A(O_TCR_NoRep).find(k0);
    y' <@ O_TCR_NoRep.get(k0, x');
    
    return x' <> x /\ y' = y;
  }  
}.

local lemma EqPr_TCR_TCR_NoRep &m :
  Pr[KHFO_TCR.TCR(A, KHFO.O_Default).main() @ &m : res] 
  =
  Pr[TCR_NoRep.main() @ &m : res].
proof.
byequiv=> //.
proc; inline *.
swap{1} 3 - 2.
seq 2 2: (   ={glob A} 
          /\ O_Default.f{1} = TCR_NoRep.g{2}
          /\ k{1} = TCR_NoRep.k0{2}).
+ rnd; rnd; skip => />.
  by rewrite eq_df_dfc.
by sim.
qed.


local module TCR_Rep = {
  var k0 : key
  var gk : input -> output
  var g : key -> input -> output
    
  module O_TCR_Rep_Pick : Oracle_t = {
    proc get(k : key, x : input) : output = {
      return g k x;
    }
  }
  
  module O_TCR_Rep_Find : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var y : output;
      
      if (k = k0) {
        y <- gk x;
      } else {
        y <- g k x;
      }
      
      return y;
    }
  }
  
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    
    k0 <$ dkey;
    gk <$ dfcs;
    g <$ dfc;
    
    x <@ A(O_TCR_Rep_Pick).pick();
    y <@ O_TCR_Rep_Find.get(k0, x);
    
    x' <@ A(O_TCR_Rep_Find).find(k0);
    y' <@ O_TCR_Rep_Find.get(k0, x');
    
    return x' <> x /\ y' = y;
  }  
}.


local clone import DFun as DF with
  type in_t <- key,
  type out_t <- input -> output,
    
  theory FT_In <- FinKey
  
  proof *.

(* Adaptive reprogramming bound for TCR *)
local clone import Reprogramming as Repro with
  type in_t <- key,
  type out_t <- input -> output,
    op dout <- dfcs,
    op p_max_bound <- 1%r / FinKey.card%r,
    
  theory FT_In <- FinKey
  
  proof *.
  realize dout_ll by exact: dfcs_ll.

import ROM_.
import LE.
import Adaptive.

local module TCR_NoRep_ERO = {  
  module O_TCR_NoRep : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var f : input -> output;
      var y : output;
      
      f <@ O_Programmable(ERO).o(k);
      
      return f x;
    }
  }
    
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    var k : key;
    
    ERO.init();
    O_Programmable(ERO).init();
    
    x <@ A(O_TCR_NoRep).pick();
    
    k <$ dkey;
    
    y <@ O_TCR_NoRep.get(k, x);
    
    x' <@ A(O_TCR_NoRep).find(k);
    y' <@ O_TCR_NoRep.get(k, x');
    
    return x' <> x /\ y' = y;
  }  
}.


local module TCR_Rep_ERO = {  
  module O_TCR_Rep : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var f : input -> output;
      var y : output;
      
      f <@ O_Programmable(ERO).o(k);
      
      return f x;
    }
  }
    
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    var k : key;
    var gk : input -> output;
    
    ERO.init();
    O_Programmable(ERO).init();
    
    x <@ A(O_TCR_Rep).pick();
    
    k <$ dkey;
    gk <$ dfcs;
    
    O_Programmable(ERO).set(k, gk);
    
    y <@ O_TCR_Rep.get(k, x);
    
    x' <@ A(O_TCR_Rep).find(k);
    y' <@ O_TCR_Rep.get(k, x');
    
    return x' <> x /\ y' = y;
  }  
}.

local lemma EqPr_TCR_TCR_ERO &m : 
  `| Pr[TCR_NoRep.main() @ &m : res] - 
     Pr[TCR_Rep.main() @ &m : res] |
  =
  `| Pr[TCR_NoRep_ERO.main() @ &m : res] - 
     Pr[TCR_Rep_ERO.main() @ &m : res] |.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc.
  swap{1} 1 1; swap{2} 4 -2.
  seq 2 2 : (   ={glob A}
             /\ TCR_NoRep.k0{1} = k{2}
             /\ TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])).
  - rnd.
    conseq (: true ==> TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
    transitivity{1} {TCR_NoRep.g <@ Direct_Fun.sample(kdfcs);}
                    (true ==> ={TCR_NoRep.g})
                    (true ==> TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
    * by inline *; wp; rnd; wp.
    transitivity{2} {ERO.m <@ Loop_Fmap.sample(kdfcs, FinKey.enum);}
                    (true ==> TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k']))
                    (true ==> ={ERO.m}) => //.
    * symmetry.
      call (Eqv_Loop_Fmap_Direct_Fun kdfcs).
      by skip.
    inline *.
    wp; sp. 
    while (d{1} = kdfcs /\ m{1} = ERO.m{2} /\ xs{1} = w{2}).
    * by wp; rnd; wp; skip.
    by skip.
  inline *.
  wp; sp => /=.
  call (:   TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
         /\ O_Programmable.prog_list{2} = []).
  - proc; inline *.
    by wp; skip.
  wp.
  call (:    TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
          /\ O_Programmable.prog_list{2} = []).
  - proc; inline *.
    by wp; skip.
  by skip.
byequiv => //.
proc.
swap{1} 3 -2; swap{2} [4..5] -2.
seq 3 3 : (   ={glob A}
           /\ TCR_Rep.k0{1} = k{2}
           /\ TCR_Rep.gk{1} = gk{2}
           /\ TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])).
+ rnd; rnd.
  conseq (: true ==> TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
  transitivity{1} {TCR_Rep.g <@ Direct_Fun.sample(kdfcs);}
                  (true ==> ={TCR_Rep.g})
                  (true ==> TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
  - by inline *; wp; rnd; wp.
  transitivity{2} {ERO.m <@ Loop_Fmap.sample(kdfcs, FinKey.enum);}
                  (true ==> TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k']))
                  (true ==> ={ERO.m}) => //.
  - symmetry.
    call (Eqv_Loop_Fmap_Direct_Fun kdfcs).
    by skip.
  inline *.
  wp; sp. 
  while (d{1} = kdfcs /\ m{1} = ERO.m{2} /\ xs{1} = w{2}).
  - by wp; rnd; wp; skip.
  by skip.
inline *.
wp; sp => /=.
call (:   TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
       /\ O_Programmable.prog_list{2} = [(TCR_Rep.k0{1}, TCR_Rep.gk{1})]).
+ proc; inline *.
  wp; skip => /> &1 &2 neqk.
  by rewrite assoc_cons neqk assoc_nil.
wp => /=.
call (:   TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
       /\ O_Programmable.prog_list{2} = []).
+ proc; inline *.
  by wp; skip.
by skip.
qed.

local module (R_Repro_TCR : Adv_INDRepro) (O : POracle, OR : Oracler_t) = {  
  module O_R_Repro_TCR : Oracle_t = {
    proc get(k : key, x : input) = {
      var f : input -> output;
      var y : output;
      
      f <@ O.o(k);
      
      return f x;
    }
  }
  
  proc distinguish() : bool = {
    var k0 : key;
    var x, x' : input;
    var y, y' : output;
    
    x <@ A(O_R_Repro_TCR).pick();
    
    k0 <@ OR.repro(dkey);
    y <@ O_R_Repro_TCR.get(k0, x);
    
    x' <@ A(O_R_Repro_TCR).find(k0);
    y' <@ O_R_Repro_TCR.get(k0, x');
 
    return x' <> x /\ y' = y;
  }
}.
  
local lemma EqPr_TCR_ERO_ReproGame &m :
  `| Pr[TCR_NoRep_ERO.main() @ &m : res] - 
     Pr[TCR_Rep_ERO.main() @ &m : res] |
   =
  `| Pr[IND_Repro(ERO, R_Repro_TCR).main(false) @ &m : res] - 
     Pr[IND_Repro(ERO, R_Repro_TCR).main(true) @ &m : res] |.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc.
  seq 2 2 : (   ={glob A, glob O_Programmable, ERO.m}
             /\ b{2} = false
             /\ O_Programmable.prog_list{2} = []
             /\ O_Programmable.ch{2} = 0).
  - inline *.
    wp => /=.
    while (={w, ERO.m}).
    * by wp; rnd; wp; skip.
    by wp; skip.
  inline *.
  wp; sp => /=.
  call (: ={glob O_Programmable, ERO.m}).
  - proc; inline *.
    by wp; skip.
  wp.
  rcondf{2} 6.
  - move=> &2.
    rnd; wp.
    by call (: true).
  rnd; wp => /=.
  call (: ={glob O_Programmable, ERO.m}).
  - proc; inline *.
    by wp; skip.
  by skip.
byequiv => //.
proc.
seq 2 2 : (   ={glob A, glob O_Programmable, ERO.m}
           /\ b{2} = true
           /\ O_Programmable.prog_list{2} = []
           /\ O_Programmable.ch{2} = 0).
+ inline *.
  wp => /=.
  while (={w, ERO.m}).
  - by wp; rnd; wp; skip.
  by wp; skip.
inline *.
wp; sp => /=.
call (: ={glob O_Programmable, ERO.m}).
+ proc; inline *.
  by wp; skip.
wp.
rcondt{2} 6.
+ move=> &2.
  rnd; wp.
  by call (: true).
wp; rnd; rnd; wp.
call (: ={glob O_Programmable, ERO.m}).
+ proc; inline *.
  by wp; skip.
by skip.
qed.


local module TCR_BFRep = {
  var k0 : key
  var x0 : input
  var y0 : output
  var gk : input -> output
  var g : key -> input -> output
    
  module O_TCR_Rep_Pick : Oracle_t = {
    proc get(k : key, x : input) : output = {
      return g k x;
    }
  }
  
  module O_TCR_Rep_Find : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var b : bool;
      var y : output;
      
      if (k = k0) {
        b <@ BFOF.query(x);
        y <- if !b /\ x <> x0 then gk x else y0; 
      } else {
        y <- g k x;
      }
      
      return y;
    }
  }
  
  proc main() : bool = {
    var x' : input;
    var y' : output;
    
    g <$ dfc;
    
    x0 <@ A(O_TCR_Rep_Pick).pick();

    k0 <$ dkey;
    
    BFOF.init();
    y0 <$ doutput;
    gk <$ dfun (fun (x : input) => doutput \ pred1 y0);
 
    x' <@ A(O_TCR_Rep_Find).find(k0);
    y' <@ O_TCR_Rep_Find.get(k0, x');
    
    return x' <> x0 /\ y' = y0;
  }  
}.

local lemma EqPr_TCR_Rep_TCR_BFRep &m:
  Pr[TCR_Rep.main() @ &m : res]
  =
  Pr[TCR_BFRep.main() @ &m : res].
proof.
byequiv => //.
proc.
swap{1} 3 -1; swap{1} 4 -1; swap{2} 3 -2.
seq 3 3 : (   ={glob A} 
           /\ ={k0, g}(TCR_Rep, TCR_BFRep)
           /\ x{1} = TCR_BFRep.x0{2}).
+ call (: ={g}(TCR_Rep, TCR_BFRep)).
  - by proc.
  by rnd; rnd.
inline{2} BFOF.init.
swap{2} 2 -1.
seq 1 3 : (   #pre
           /\ (forall (x : input),
                 TCR_Rep.gk{1} x 
                 =
                 if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                 then TCR_BFRep.gk{2} x
                 else TCR_BFRep.y0{2})).
+ conseq (_ : true ==> (forall (x : input),
                         TCR_Rep.gk{1} x 
                         =
                         if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                         then TCR_BFRep.gk{2} x
                         else TCR_BFRep.y0{2})) => //.
  transitivity{1} {TCR_Rep.gk <@ LR.LambdaRepro.left();}
                  (true ==> ={TCR_Rep.gk})
                  (true ==> (forall (x : input),
                               TCR_Rep.gk{1} x 
                               =
                               if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                               then TCR_BFRep.gk{2} x
                               else TCR_BFRep.y0{2})) => //.
  - inline *.
    by wp; rnd.
  transitivity{2} {TCR_BFRep.gk <@ LR.LambdaRepro.right(TCR_BFRep.x0);}
                  (true ==> ={gk}(TCR_Rep, TCR_BFRep))
                  (={TCR_BFRep.x0} ==> (forall (x : input),
                                         TCR_BFRep.gk{1} x 
                                         =
                                         if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                                         then TCR_BFRep.gk{2} x
                                         else TCR_BFRep.y0{2})); 1,2: by smt().
  + by call LR.main_theorem.
  inline *.
  wp; sp.
  rnd; rnd; rnd.
  by skip.
inline *.
wp => /=.
call (:   ={k0, g}(TCR_Rep, TCR_BFRep)
       /\ (forall (x : input),
            TCR_Rep.gk{1} x 
            =
            if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
            then TCR_BFRep.gk{2} x
            else TCR_BFRep.y0{2})).
+ proc; inline *.
  by wp; skip => /> /#. 
by wp; skip => /> /#.   
qed.


local lemma LePr_TCRBFRep_BFFind &m :
  Pr[TCR_BFRep.main() @ &m : res]
  <=
  Pr[BF_Find(R_BFFind_TCR(A), BFOF).main() @ &m: res].
proof.
byequiv=> //.
proc; inline *.
wp => /=.
call (:   ={BFOF.f}
       /\ ={k0, x0, y0, g}(TCR_BFRep, R_BFFind_TCR)
       /\ TCR_BFRep.gk{1} = R_BFFind_TCR.f{2}). 
+ proc; inline *.
  by wp; skip.
swap{1} 2 4; swap{2} [2..3] -1; swap{2} 6 -4.
sp.
call (: ={g}(TCR_BFRep, R_BFFind_TCR)).
+ proc.
  by wp; skip.
do 5! rnd; skip => /> g gin k kin f fin y yin gk gkin r r' neqrr.
apply contraLR => -> /=.
by move/dfun_supp /(_ r') /supp_dexcepted: gkin.
qed.

local lemma TCR_Implies_BFDistinguish_A &m:
  Pr[KHFO_TCR.TCR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(true) @ &m : res] |
  +
  `| Pr[IND_Repro(ERO, R_Repro_TCR).main(false) @ &m : res] - 
     Pr[IND_Repro(ERO, R_Repro_TCR).main(true) @ &m : res] |.  
proof.
rewrite EqPr_TCR_TCR_NoRep.
rewrite -StdOrder.RealOrder.ger0_norm 1:Pr[mu_ge0] //-{1}StdOrder.RealOrder.Domain.subr0.
rewrite -(StdOrder.RealOrder.Domain.subrr Pr[TCR_Rep.main() @ &m : res]).
rewrite StdOrder.RealOrder.Domain.opprD StdOrder.RealOrder.Domain.addrA /=.
apply (StdOrder.RealOrder.ler_trans
         (`| Pr[TCR_NoRep.main() @ &m : res] - Pr[TCR_Rep.main() @ &m : res] | +
             Pr[TCR_Rep.main() @ &m : res])).
+ rewrite -{4}(StdOrder.RealOrder.ger0_norm Pr[TCR_Rep.main() @ &m : res]) 1:Pr[mu_ge0] //.
  by apply StdOrder.RealOrder.ler_norm_add.
rewrite StdOrder.RealOrder.Domain.addrC StdOrder.RealOrder.ler_add; last first.
+ by rewrite EqPr_TCR_TCR_ERO EqPr_TCR_ERO_ReproGame.
apply (StdOrder.RealOrder.ler_trans Pr[BF_Find(R_BFFind_TCR(A), BFOF).main() @ &m: res]).
+ by rewrite EqPr_TCR_Rep_TCR_BFRep LePr_TCRBFRep_BFFind.
by rewrite (Find_Implies_Distinguish &m (R_BFFind_TCR(A))).
qed.


declare op qP : { int | 0 <= qP } as ge0_qP.
declare op qF : { int | 0 <= qF } as ge0_qF.

op q : int = qP + qF.

lemma ge0_q : 0 <= q.
proof. by rewrite StdOrder.IntOrder.addr_ge0 1:ge0_qP ge0_qF. qed.

declare axiom A_Pick_queries (O <: Oracle_t{-A}) (n : int):
  hoare[A(Counting_O(O)).pick : Counting_O.ctr = n ==> Counting_O.ctr <= n + qP].

declare axiom A_Find_queries (O <: Oracle_t{-A}) (n : int):
  hoare[A(Counting_O(O)).find : Counting_O.ctr = n ==> Counting_O.ctr <= n + qF].

local module (R_Repro_TCR_C : Adv_INDRepro) (O : POracle, OR : Oracler_t) = {  
  module O_R_Repro_TCR_C = Counting_O(R_Repro_TCR(O, OR).O_R_Repro_TCR) 
  
  proc distinguish() : bool = {
    var k0 : key;
    var x, x' : input;
    var y, y' : output;
    
    Counting_O.ctr <- 0;
    
    x <@ A(O_R_Repro_TCR_C).pick();
    
    k0 <@ OR.repro(dkey);
    y <@ O_R_Repro_TCR_C.get(k0, x);
    
    x' <@ A(O_R_Repro_TCR_C).find(k0);
    y' <@ O_R_Repro_TCR_C.get(k0, x');
 
    return x' <> x /\ y' = y;
  }
}.

local hoare R_Repro_TCR_C_queries :
  R_Repro_TCR_C(O_Programmable(ERO), O_Reprogrammer(O_Programmable(ERO))).distinguish :
    O_Programmable.ch = 0 /\ O_Reprogrammer.ctr = 0 /\ O_Reprogrammer.se 
    ==>
    O_Programmable.ch <= q + 2 /\ O_Reprogrammer.ctr <= 1 /\ O_Reprogrammer.se.
proof.
proc.
sp.
inline 5; inline 8; inline 10; inline 11.
wp => /=.
seq 2 : (   Counting_O.ctr = O_Programmable.ch
         /\ O_Programmable.ch <= qP 
         /\ O_Reprogrammer.ctr = 1 
         /\ O_Reprogrammer.se).
+ call (: arg = dkey /\ O_Reprogrammer.ctr = 0 /\ O_Reprogrammer.se ==> O_Reprogrammer.ctr = 1 /\ O_Reprogrammer.se).
  - proc; inline *.
    sp.
    conseq (: _ ==> true) => // /> ? _.
    rewrite uniform_pmaxE 1:dkey_uni dkey_ll.
    rewrite StdBigop.Bigreal.Num.Domain.div1r.
    rewrite card_size_to_seq StdOrder.RealOrder.ler_eqVlt; left.
    rewrite (: support dkey = predT) // /predT fun_ext => k.
    by rewrite dkey_fu.
  conseq (: _ 
            ==> 
               Counting_O.ctr = O_Programmable.ch 
            /\ O_Programmable.ch <= qP) => //.
  call (:    Counting_O.ctr = 0 
          /\ O_Programmable.ch = 0
          ==>
             Counting_O.ctr = O_Programmable.ch 
          /\ Counting_O.ctr <= qP) => //.
  conseq (: Counting_O.ctr = O_Programmable.ch ==> Counting_O.ctr = O_Programmable.ch)
         (A_Pick_queries (<: R_Repro_TCR(O_Programmable(ERO), O_Reprogrammer(O_Programmable(ERO))).O_R_Repro_TCR) 0) => //. 
  proc (Counting_O.ctr = O_Programmable.ch) => //.
  proc; inline *.
  by wp; skip.
seq 1 : (   Counting_O.ctr = O_Programmable.ch
         /\ O_Programmable.ch <= qP + 1 
         /\ O_Reprogrammer.ctr = 1 
         /\ O_Reprogrammer.se).
+ inline *.
  by wp; skip => /> /#.
call (:    Counting_O.ctr = O_Programmable.ch 
        /\ O_Programmable.ch <= qP + 1 
        /\ O_Reprogrammer.ctr = 1 
        /\ O_Reprogrammer.se
        ==>
        Counting_O.ctr = O_Programmable.ch 
        /\ O_Programmable.ch <= qP + 1 + qF 
        /\ O_Reprogrammer.ctr = 1 
        /\ O_Reprogrammer.se).
+ conseq (: Counting_O.ctr = O_Programmable.ch ==> Counting_O.ctr = O_Programmable.ch)
         (: Counting_O.ctr <= qP + 1 ==> Counting_O.ctr <= qP + 1 + qF) => //.
  - exists* Counting_O.ctr; elim* => ctr.
    conseq (A_Find_queries (<: R_Repro_TCR(O_Programmable(ERO), O_Reprogrammer(O_Programmable(ERO))).O_R_Repro_TCR) ctr) => //; 1: by smt().
  proc (Counting_O.ctr = O_Programmable.ch) => //.
  proc; inline *.
  by wp.
by skip => /> /#.
qed.

lemma TCR_Implies_BFDistinguish &m:
  Pr[KHFO_TCR.TCR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(true) @ &m : res] |
  +
  (q + 2)%r / FinKey.card%r. 
proof.
move: (TCR_Implies_BFDistinguish_A &m).
have -> :
  `| Pr[IND_Repro(ERO, R_Repro_TCR).main(false) @ &m : res] -
     Pr[IND_Repro(ERO, R_Repro_TCR).main(true) @ &m : res] |
  =
  `| Pr[IND_Repro(ERO, R_Repro_TCR_C).main(false) @ &m : res] -
     Pr[IND_Repro(ERO, R_Repro_TCR_C).main(true) @ &m : res] |.
+ do 2! congr; last congr.
  - byequiv=> //. 
    proc. 
    seq 3 3 : (={glob A, glob ERO, glob O_Programmable, glob O_Reprogrammer} /\ !O_Reprogrammer.b{1}).
    * inline{1} 3; inline{2} 3.
      wp.
      conseq (: _ ==> ={glob ERO, glob O_Programmable}) => //.
      by sim.
    inline *.
    rcondf{1} 6; 1: by auto; call (: true) => //.
    rcondf{2} 7; 1: by auto; call (: true) => //; auto. 
    wp.
    call (: ={glob ERO, glob O_Programmable, glob O_Reprogrammer}).
    * by proc; inline *; wp.
    wp; rnd; wp.
    call (: ={glob ERO, glob O_Programmable, glob O_Reprogrammer}). 
    * by proc; inline *; wp.
    by wp.
  byequiv=> //. 
  proc. 
  seq 3 3 : (={glob A, glob ERO, glob O_Programmable, glob O_Reprogrammer} /\ O_Reprogrammer.b{1}).
  - inline{1} 3; inline{2} 3.
    wp.
    conseq (: _ ==> ={glob ERO, glob O_Programmable}) => //.
    by sim.
  inline *.
  rcondt{1} 6; 1: by auto; call (: true) => //.
  rcondt{2} 7; 1: by auto; call (: true) => //; auto. 
  wp.
  call (: ={glob ERO, glob O_Programmable, glob O_Reprogrammer}).
  - by proc; inline *; wp.
  wp; rnd; wp; rnd; wp.
  call (: ={glob ERO, glob O_Programmable, glob O_Reprogrammer}). 
  - by proc; inline *; wp.
  by wp.
pose BFAdv := `| _ - _ |%Real; pose ReproAdv := `| _ - _ |%Real; move => tib.
apply (StdOrder.RealOrder.ler_trans (BFAdv + ReproAdv)) => //.
apply StdOrder.RealOrder.ler_add => //.
by apply (Bound_IND_Repro R_Repro_TCR_C 1 _ (q + 2) _ &m R_Repro_TCR_C_queries) => //; smt(ge0_q).
qed. 

end section.

end TCRBound.

(* Non-adaptive reprogramming bound for TCR *) 
(*
local clone import Reprogramming as Repro with
  type in_t <- key,
  type out_t <- input -> output,
    op dout <- dfcs,
    op p_max_bound <- 1%r / FinKey.card%r,
    
  theory FT_In <- FinKey
  
  proof *.
  realize dout_ll by exact: dfcs_ll.

import ROM_.
import LE.
import NonAdaptive.


local module TCR_NoRep_ERO = {  
  module O_TCR_NoRep_Pick : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var f : input -> output;
      var y : output;
      
      f <@ O_Programmable(ERO).oc(k);
      
      return f x;
    }
  }

  module O_TCR_NoRep_Distinguish : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var f : input -> output;
      var y : output;
      
      f <@ O_Programmable(ERO).o(k);
      
      return f x;
    }
  }
    
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    var k : key;
    
    ERO.init();
    O_Programmable(ERO).init();
    
    x <@ A(O_TCR_NoRep_Pick).pick();
    
    k <$ dkey;
    
    y <@ O_TCR_NoRep_Distinguish.get(k, x);
    
    x' <@ A(O_TCR_NoRep_Distinguish).find(k);
    y' <@ O_TCR_NoRep_Distinguish.get(k, x');
    
    return x' <> x /\ y' = y;
  }  
}.


local module TCR_Rep_ERO = {  
  module O_TCR_Rep_Pick : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var f : input -> output;
      var y : output;
      
      f <@ O_Programmable(ERO).oc(k);
      
      return f x;
    }
  }

  module O_TCR_Rep_Distinguish : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var f : input -> output;
      var y : output;
      
      f <@ O_Programmable(ERO).o(k);
      
      return f x;
    }
  }
    
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    var k : key;
    var gk : input -> output;
    
    ERO.init();
    O_Programmable(ERO).init();
    
    x <@ A(O_TCR_Rep_Pick).pick();
    
    k <$ dkey;
    gk <$ dfcs;
    
    O_Programmable(ERO).set(k, gk);
    
    y <@ O_TCR_Rep_Distinguish.get(k, x);
    
    x' <@ A(O_TCR_Rep_Distinguish).find(k);
    y' <@ O_TCR_Rep_Distinguish.get(k, x');
    
    return x' <> x /\ y' = y;
  }  
}.

local lemma EqPr_TCR_TCR_ERO &m : 
  `| Pr[TCR_NoRep.main() @ &m : res] - 
     Pr[TCR_Rep.main() @ &m : res] |
  =
  `| Pr[TCR_NoRep_ERO.main() @ &m : res] - 
     Pr[TCR_Rep_ERO.main() @ &m : res] |.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc.
  swap{1} 1 1; swap{2} 4 -2.
  seq 2 2 : (   ={glob A}
             /\ TCR_NoRep.k0{1} = k{2}
             /\ TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])).
  - rnd.
    conseq (: true ==> TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
    transitivity{1} {TCR_NoRep.g <@ Direct_Fun.sample(kdfcs);}
                    (true ==> ={TCR_NoRep.g})
                    (true ==> TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
    * by inline *; wp; rnd; wp.
    transitivity{2} {ERO.m <@ Loop_Fmap.sample(kdfcs, FinKey.enum);}
                    (true ==> TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k']))
                    (true ==> ={ERO.m}) => //.
    * symmetry.
      call (Eqv_Loop_Fmap_Direct_Fun kdfcs).
      by skip.
    inline *.
    wp; sp. 
    while (d{1} = kdfcs /\ m{1} = ERO.m{2} /\ xs{1} = w{2}).
    * by wp; rnd; wp; skip.
    by skip.
  inline *.
  wp; sp => /=.
  call (:   TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
         /\ O_Programmable.prog_list{2} = []).
  - proc; inline *.
    by wp; skip.
  wp.
  call (:    TCR_NoRep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
          /\ O_Programmable.prog_list{2} = []).
  - proc; inline *.
    by wp; skip.
  by skip.
byequiv => //.
proc.
swap{1} 3 -2; swap{2} [4..5] -2.
seq 3 3 : (   ={glob A}
           /\ TCR_Rep.k0{1} = k{2}
           /\ TCR_Rep.gk{1} = gk{2}
           /\ TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])).
+ rnd; rnd.
  conseq (: true ==> TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
  transitivity{1} {TCR_Rep.g <@ Direct_Fun.sample(kdfcs);}
                  (true ==> ={TCR_Rep.g})
                  (true ==> TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])) => //.
  - by inline *; wp; rnd; wp.
  transitivity{2} {ERO.m <@ Loop_Fmap.sample(kdfcs, FinKey.enum);}
                  (true ==> TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k']))
                  (true ==> ={ERO.m}) => //.
  - symmetry.
    call (Eqv_Loop_Fmap_Direct_Fun kdfcs).
    by skip.
  inline *.
  wp; sp. 
  while (d{1} = kdfcs /\ m{1} = ERO.m{2} /\ xs{1} = w{2}).
  - by wp; rnd; wp; skip.
  by skip.
inline *.
wp; sp => /=.
call (:   TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
       /\ O_Programmable.prog_list{2} = [(TCR_Rep.k0{1}, TCR_Rep.gk{1})]).
+ proc; inline *.
  wp; skip => /> &1 &2 neqk.
  by rewrite assoc_cons neqk assoc_nil.
wp => /=.
call (:   TCR_Rep.g{1} = (fun (k' : key) => oget ERO.m{2}.[k'])
       /\ O_Programmable.prog_list{2} = []).
+ proc; inline *.
  by wp; skip.
by skip.
qed.

local module (R_Repro_TCR : Adv_INDNARepro) (O : Oraclep_t) = {  
  var x0 : input
  
  module O_R_Repro_TCR_Pick : Oracle_t = {
    proc get(k : key, x : input) = {
      var f : input -> output;
      var y : output;
      
      f <@ O.oc(k);
      
      return f x;
    }
  }
  
  module O_R_Repro_TCR_Distinguish : Oracle_t = {
    proc get(k : key, x : input) = {
      var f : input -> output;
      var y : output;
      
      f <@ O.o(k);
      
      return f x;
    }
  }
  
  proc pick() : key distr list = {
    
    x0 <@ A(O_R_Repro_TCR_Pick).pick();
    
    return [dkey];
  }
  
  proc distinguish(ks : key list) : bool = {
    var k0 : key;
    var x' : input;
    var y0, y' : output;
    
    k0 <- head witness ks;
    
    y0 <@ O_R_Repro_TCR_Distinguish.get(k0, x0);
    
    x' <@ A(O_R_Repro_TCR_Distinguish).find(k0);
    y' <@ O_R_Repro_TCR_Distinguish.get(k0, x');
 
    return x' <> x0 /\ y' = y0;
  }
}.
  
local lemma EqPr_TCR_ERO_ReproGame &m :
  `| Pr[TCR_NoRep_ERO.main() @ &m : res] - 
     Pr[TCR_Rep_ERO.main() @ &m : res] |
   =
  `| Pr[IND_NARepro(ERO, R_Repro_TCR).main(false, 1) @ &m : res] - 
     Pr[IND_NARepro(ERO, R_Repro_TCR).main(true, 1) @ &m : res] |.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc => /=.
  seq 2 2 : (   ={glob A, glob O_Programmable, ERO.m}
             /\ b{2} = false
             /\ n{2} = 1
             /\ O_Programmable.prog_list{2} = []
             /\ O_Programmable.ch{2} = 0).
  - inline *.
    wp => /=.
    while (={w, ERO.m}).
    * by wp; rnd; wp; skip.
    by wp; skip.
  inline *.
  wp; sp => /=.
  call (: ={glob O_Programmable, ERO.m}).
  - proc; inline *.
    by wp; skip.
  wp.
  rcondt{2} ^while. 
  - auto.
    by call (: true).
  rcondf{2} ^if.
  + auto.
    by call (: true).
  rcondf{2} ^while.
  + auto.
    by call (: true).
  wp; rnd; wp.
  call (: ={glob O_Programmable, ERO.m}).
  - proc; inline *.
    by wp; skip.
  by skip.
byequiv => //.
proc => /=.
seq 2 2 : (   ={glob A, glob O_Programmable, ERO.m}
           /\ b{2} = true
           /\ n{2} = 1
           /\ O_Programmable.prog_list{2} = []
           /\ O_Programmable.ch{2} = 0).
+ inline *.
  wp => /=.
  while (={w, ERO.m}).
  - by wp; rnd; wp; skip.
  by wp; skip.
inline *.
wp; sp => /=.
call (: ={glob O_Programmable, ERO.m}).
+ proc; inline *.
  by wp; skip.
wp.
rcondt{2} ^while.
+ auto.
  by call (: true).
rcondt{2} ^if.
+ auto.
  by call (: true).
rcondf{2} ^while.
+ auto.
  by call (: true).
wp; rnd; rnd; wp.
call (: ={glob O_Programmable, ERO.m}).
+ proc; inline *.
  by wp; skip.
by skip.
qed.


local module TCR_BFRep = {
  var k0 : key
  var x0 : input
  var y0 : output
  var gk : input -> output
  var g : key -> input -> output
    
  module O_TCR_Rep_Pick : Oracle_t = {
    proc get(k : key, x : input) : output = {
      return g k x;
    }
  }
  
  module O_TCR_Rep_Find : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var b : bool;
      var y : output;
      
      if (k = k0) {
        b <@ BFOF.query(x);
        y <- if !b /\ x <> x0 then gk x else y0; 
      } else {
        y <- g k x;
      }
      
      return y;
    }
  }
  
  proc main() : bool = {
    var x' : input;
    var y' : output;
    
    g <$ dfc;
    
    x0 <@ A(O_TCR_Rep_Pick).pick();

    k0 <$ dkey;
    
    BFOF.init();
    y0 <$ doutput;
    gk <$ dfun (fun (x : input) => doutput \ pred1 y0);
 
    x' <@ A(O_TCR_Rep_Find).find(k0);
    y' <@ O_TCR_Rep_Find.get(k0, x');
    
    return x' <> x0 /\ y' = y0;
  }  
}.

local lemma EqPr_TCR_Rep_TCR_BFRep &m:
  Pr[TCR_Rep.main() @ &m : res]
  =
  Pr[TCR_BFRep.main() @ &m : res].
proof.
byequiv => //.
proc.
swap{1} 3 -1; swap{1} 4 -1; swap{2} 3 -2.
seq 3 3 : (   ={glob A} 
           /\ ={k0, g}(TCR_Rep, TCR_BFRep)
           /\ x{1} = TCR_BFRep.x0{2}).
+ call (: ={g}(TCR_Rep, TCR_BFRep)).
  - by proc.
  by rnd; rnd.
inline{2} BFOF.init.
swap{2} 2 -1.
seq 1 3 : (   #pre
           /\ (forall (x : input),
                 TCR_Rep.gk{1} x 
                 =
                 if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                 then TCR_BFRep.gk{2} x
                 else TCR_BFRep.y0{2})).
+ conseq (_ : true ==> (forall (x : input),
                         TCR_Rep.gk{1} x 
                         =
                         if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                         then TCR_BFRep.gk{2} x
                         else TCR_BFRep.y0{2})) => //.
  transitivity{1} {TCR_Rep.gk <@ LR.LambdaRepro.left();}
                  (true ==> ={TCR_Rep.gk})
                  (true ==> (forall (x : input),
                               TCR_Rep.gk{1} x 
                               =
                               if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                               then TCR_BFRep.gk{2} x
                               else TCR_BFRep.y0{2})) => //.
  - inline *.
    by wp; rnd.
  transitivity{2} {TCR_BFRep.gk <@ LR.LambdaRepro.right(TCR_BFRep.x0);}
                  (true ==> ={gk}(TCR_Rep, TCR_BFRep))
                  (={TCR_BFRep.x0} ==> (forall (x : input),
                                         TCR_BFRep.gk{1} x 
                                         =
                                         if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
                                         then TCR_BFRep.gk{2} x
                                         else TCR_BFRep.y0{2})); 1,2: by smt().
  + by call LR.main_theorem.
  inline *.
  wp; sp.
  rnd; rnd; rnd.
  by skip.
inline *.
wp => /=.
call (:   ={k0, g}(TCR_Rep, TCR_BFRep)
       /\ (forall (x : input),
            TCR_Rep.gk{1} x 
            =
            if ! BFOF.f{2} x /\ x <> TCR_BFRep.x0{2}
            then TCR_BFRep.gk{2} x
            else TCR_BFRep.y0{2})).
+ proc; inline *.
  by wp; skip => /> /#. 
by wp; skip => /> /#.   
qed.


local lemma LePr_TCRBFRep_BFFind &m :
  Pr[TCR_BFRep.main() @ &m : res]
  <=
  Pr[BF_Find(R_BFFind_TCR(A), BFOF).main() @ &m: res].
proof.
byequiv=> //.
proc; inline *.
wp => /=.
call (:   ={BFOF.f}
       /\ ={k0, x0, y0, g}(TCR_BFRep, R_BFFind_TCR)
       /\ TCR_BFRep.gk{1} = R_BFFind_TCR.f{2}). 
+ proc; inline *.
  by wp; skip.
swap{1} 2 4; swap{2} [2..3] -1; swap{2} 6 -4.
sp.
call (: ={g}(TCR_BFRep, R_BFFind_TCR)).
+ proc.
  by wp; skip.
do 5! rnd; skip => /> g gin k kin f fin y yin gk gkin r r' neqrr.
apply contraLR => -> /=.
by move/dfun_supp /(_ r') /supp_dexcepted: gkin.
qed.

local lemma TCR_Implies_BFDistinguish_A &m:
  Pr[KHFO_TCR.TCR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(true) @ &m : res] |
  +
  `| Pr[IND_NARepro(ERO, R_Repro_TCR).main(false, 1) @ &m : res] - 
     Pr[IND_NARepro(ERO, R_Repro_TCR).main(true, 1) @ &m : res] |.  
proof.
rewrite EqPr_TCR_TCR_NoRep.
rewrite -StdOrder.RealOrder.ger0_norm 1:Pr[mu_ge0] //-{1}StdOrder.RealOrder.Domain.subr0.
rewrite -(StdOrder.RealOrder.Domain.subrr Pr[TCR_Rep.main() @ &m : res]).
rewrite StdOrder.RealOrder.Domain.opprD StdOrder.RealOrder.Domain.addrA /=.
apply (StdOrder.RealOrder.ler_trans
         (`| Pr[TCR_NoRep.main() @ &m : res] - Pr[TCR_Rep.main() @ &m : res] | +
             Pr[TCR_Rep.main() @ &m : res])).
+ rewrite -{4}(StdOrder.RealOrder.ger0_norm Pr[TCR_Rep.main() @ &m : res]) 1:Pr[mu_ge0] //.
  by apply StdOrder.RealOrder.ler_norm_add.
rewrite StdOrder.RealOrder.Domain.addrC StdOrder.RealOrder.ler_add; last first.
+ by rewrite EqPr_TCR_TCR_ERO EqPr_TCR_ERO_ReproGame.
apply (StdOrder.RealOrder.ler_trans Pr[BF_Find(R_BFFind_TCR(A), BFOF).main() @ &m: res]).
+ by rewrite EqPr_TCR_Rep_TCR_BFRep LePr_TCRBFRep_BFFind.
by rewrite (Find_Implies_Distinguish &m (R_BFFind_TCR(A))).
qed.


declare op qP : { int | 0 <= qP } as ge0_qP.

declare axiom A_Pick_queries (O <: Oracle_t{-A}) (n : int):
  hoare[A(Counting_O(O)).pick : Counting_O.ctr = n ==> Counting_O.ctr <= n + qP].


local module (R_Repro_TCR_C : Adv_INDNARepro) (O : Oraclep_t) = {
  import var R_Repro_TCR(O)
   
  module O_R_Repro_TCR_C_Pick = Counting_O(R_Repro_TCR(O).O_R_Repro_TCR_Pick) 
  module O_R_Repro_TCR_C_Distinguish = R_Repro_TCR(O).O_R_Repro_TCR_Distinguish
   
  proc pick() : key distr list = {
    Counting_O.ctr <- 0;
    
    x0 <@ A(O_R_Repro_TCR_C_Pick).pick();

    return [dkey];
  }

  proc distinguish(ks : key list) : bool = {
    var k0 : key;
    var x' : input;
    var y0, y' : output;
    
    k0 <- head witness ks;
    
    y0 <@ O_R_Repro_TCR_C_Distinguish.get(k0, x0);
    
    x' <@ A(O_R_Repro_TCR_C_Distinguish).find(k0);
    y' <@ O_R_Repro_TCR_C_Distinguish.get(k0, x');
 
    return x' <> x0 /\ y' = y0;
  }
}.

local hoare R_Repro_TCR_C_queries :
  R_Repro_TCR_C(O_Programmable(ERO)).pick :
    O_Programmable.ch = 0 
    ==>
    O_Programmable.ch <= qP /\ all ((>=) (1%r / FinKey.card%r)) (map p_max res).
proof.
proc.
sp.
conseq (: _ ==> O_Programmable.ch <= qP).
+ move=> &1 eq0cs ch -> /=.
  rewrite uniform_pmaxE 1:dkey_uni dkey_ll.
  rewrite StdBigop.Bigreal.Num.Domain.div1r.
  rewrite card_size_to_seq StdOrder.RealOrder.ler_eqVlt; left.
  rewrite (: support dkey = predT) // /predT fun_ext => k.
  by rewrite dkey_fu.
call (: Counting_O.ctr = 0 /\ O_Programmable.ch = 0  
        ==>
        Counting_O.ctr = O_Programmable.ch /\ Counting_O.ctr <= qP).
+ conseq (: Counting_O.ctr = O_Programmable.ch ==> Counting_O.ctr = O_Programmable.ch)
         (: Counting_O.ctr = 0 ==> Counting_O.ctr <= 0 + qP) => //.
  - by apply (A_Pick_queries (<: R_Repro_TCR(O_Programmable(ERO)).O_R_Repro_TCR_Pick)).
  proc (Counting_O.ctr = O_Programmable.ch) => //.
  proc; inline *.
  by wp; skip.
by skip.
qed.  

lemma TCR_Implies_BFDistinguish &m:
  Pr[KHFO_TCR.TCR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(true) @ &m : res] |
  +
  qP%r / FinKey.card%r. 
proof.
move: (TCR_Implies_BFDistinguish_A &m).
have -> :
  `| Pr[IND_NARepro(ERO, R_Repro_TCR).main(false, 1) @ &m : res] -
     Pr[IND_NARepro(ERO, R_Repro_TCR).main(true, 1) @ &m : res] |
  =
  `| Pr[IND_NARepro(ERO, R_Repro_TCR_C).main(false, 1) @ &m : res] -
     Pr[IND_NARepro(ERO, R_Repro_TCR_C).main(true, 1) @ &m : res] |.
+ do 2! congr; last congr.
  - byequiv=> //. 
    proc. 
    inline{1} 3; inline{2} 3.
    seq 4 5 : (   ={b, n, ds, R_Repro_TCR.x0, glob A, glob ERO, glob O_Programmable}
               /\ ! b{1}
               /\ n{1} = 1).
    * wp.
      call (: ={glob ERO, glob O_Programmable}).
      + proc; inline *.
        by wp; skip.
      by wp; sim />.
    inline *.
    wp.
    call (: ={glob ERO, glob O_Programmable}).
    * proc; inline *.
      by wp.
    wp.
    while (   ={b, xs, ds, n, glob O_Programmable, R_Repro_TCR.x0} 
           /\ ! b{1}).
    * rcondf{1} ^if; 1: by auto. 
      rcondf{2} ^if; 1: by auto.
      by wp; rnd; skip.
    by wp; skip.
  byequiv=> //. 
  proc.
  inline{1} 3; inline{2} 3.
  seq 4 5 : (   ={b, n, ds, R_Repro_TCR.x0, glob A, glob ERO, glob O_Programmable}
             /\ b{1}
             /\ n{1} = 1).
  - wp.
    call (: ={glob ERO, glob O_Programmable}).
    + proc; inline *.
      by wp; skip.
    by wp; sim />.
  inline *.
  wp.
  call (: ={glob ERO, glob O_Programmable}).
  - proc; inline *.
    by wp.
  wp.
  while (   ={b, xs, ds, n, glob O_Programmable, R_Repro_TCR.x0} 
         /\ b{1}).
  - rcondt{1} ^if; 1: by auto. 
    rcondt{2} ^if; 1: by auto.
    by wp; rnd; rnd; skip.
  by wp; skip.
pose BFAdv := `| _ - _ |%Real; pose ReproAdv := `| _ - _ |%Real; move => tib.
apply (StdOrder.RealOrder.ler_trans (BFAdv + ReproAdv)) => //.
apply StdOrder.RealOrder.ler_add => //.
by apply (Bound_IND_NARepro R_Repro_TCR_C 1 _ qP _ &m R_Repro_TCR_C_queries) => //; smt(ge0_qP).
qed. 

end section.

end TCRBound.
*)
