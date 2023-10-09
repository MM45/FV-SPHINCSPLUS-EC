require import AllCore List Distr FinType Dexcepted DMap DFun.
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
  Auxiliary module types for non-keyed hash function properties.
  Not essential, but used for better readability.
*)
module type Oracle_NKi_t = {
  proc init() : unit
  proc get(x : input) : output 
}.

module type Oracle_NK_t = {
  include Oracle_NKi_t [-init]
}.

module O_NK_Default : Oracle_NKi_t = {
  var gk : input -> output
  
  proc init() : unit = {
    gk <$ MUFF_In.dfun (fun _ => doutput);
  }
  
  proc get(x : input) : output = {
    return gk x;  
  }
}.


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
  proc fixone_dfc(k : key) = {
    var gk : input -> output;
    var g : key -> input -> output;
    
    gk <$ dfcs;
    
    g <$ dfun kdfcs.[k <- dunit gk];
    
    return g;    
  }
  
  proc if_dfc(k : key) = {
    var gk : input -> output;
    var g : key -> input -> output;
    
    gk <$ dfcs;
    
    g <$ dfc;
    
    return (fun k' => if k' = k then gk else g k');
  }
}.

equiv Eqv_fixone_if_dfc :
  EquivSamplings.fixone_dfc ~ EquivSamplings.if_dfc : ={k} ==> ={res}.
proof.
proc.
print S.
pose d := dlet dfcs (fun gk => dmap dfc (fun g => (gk, g))).
transitivity{1} {g <@ S.sample(d, fun (gkg : _ * _) (k' : key) => 
                                    if k' = k then gkg.`1 else gkg.`2 k'); }
                (={k} ==> ={g})
                (={k} ==> g{1} = fun k' => if k' = k{2} then gk{2} else g{2} k'); 1,2: by smt().
+ inline *.
  wp; sp.
  rnd : *0 *0.
  skip => /> &2; rewrite ?dmap_id.
  split => [g gin | h g].
  - congr => @/d.
    rewrite dmap_dlet /=; congr.
    rewrite fun_ext => gk.
    rewrite dmap_comp /(\o) dmap_id /dfc /"_.[_<-_]".
    rewrite (MUFF_Key.dmap_dfun _ (fun k' f => if k' = k{2} then gk else f)) /=.
    congr; rewrite fun_ext => k'.
    case (k{2} = k') => [->|] /=; 1: by rewrite dmap_cst 1:dfcs_ll.
    by rewrite eq_sym => -> /=; rewrite dmap_id.
  rewrite supp_dlet => -[gk [gkin /=]]; rewrite supp_dmap => -[gfix [+ ->] /=]. 
  rewrite dfun_supp supp_dmap => gfixin; exists (gk, gfix); split => /=.
  + rewrite /d supp_dlet; exists gk; rewrite gkin /= supp_dmap.
    by exists gfix; rewrite dfc_fu. 
  rewrite fun_ext => k'; move: (gfixin k').
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


theory SPRBound.

op [lossless] dkey : key distr.
op [lossless] dinput : input distr.

clone import SPR as KHFO_SPR with
  op din <- dinput,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: dinput_ll.
  realize dkey_ll by exact: dkey_ll.


(* 
  Definitions concerning SPR for non-keyed functions.
  Used as intermediate step; could inline reduction
  to remove all these extra definitions (but makes reduction
  bit less readable).
*)
module type Adv_SPR_NK (O : Oracle_NK_t) = {
  proc find(x : input) : input
}.

module SPR_NK (A : Adv_SPR_NK) (O : Oracle_NKi_t) = {
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    
    O.init();
    
    x <$ dinput;
    
    y <@ O.get(x);
    
    x' <@ A(O).find(x);
    
    y' <@ O.get(x');
    
    return x' <> x /\ y' = y;
  }
}.

module (R_SPRNK_SPR (A : Adv_SPR) : Adv_SPR_NK) (O : Oracle_NK_t) = {
  var k0 : key
  var g : key -> input -> output
  
  module O_R_SPRNK_SPR : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var y : output;
      
      if (k = k0) {
        y <@ O.get(x);  
      } else {
        y <- g k x;
      }
      
      return y;
    }
  }
  
  proc find(x : input) : input = {
    var x' : input;
    
    k0 <$ dkey;
    
    g <$ dfc;
    
    x' <@ A(O_R_SPRNK_SPR).find(k0, x);
     
    return x';
  } 
}.

module (R_BFFind_SPRNK (A : Adv_SPR) : Adv_BFFind) (BFO : BFOF_t) = {
  var f : input -> output
  var x0 : input
  var y0 : output
  
  module O_R_BFFind_SPRNK : Oracle_NK_t = {
    proc get(x : input) : output = {
      var b : bool;
      var y : output;
      
      b <@ BFO.query(x);
     
      return if !b /\ x <> x0 then f x else y0;
    }
  }

  proc find() : input = {
    var x' : input;
    
    x0 <$ dinput;
    y0 <$ doutput;
    
    f <$ MUFF_In.dfun (fun (_ : input) => doutput \ (pred1 y0));
            
    x' <@ R_SPRNK_SPR(A, O_R_BFFind_SPRNK).find(x0);
    
    return x';
  }
}.

section.

declare module A <: Adv_SPR {-KHFO.O_Default, -R_BFFind_SPRNK, -O_NK_Default, -BFOF, -BFOD}.

local module SPR_SS = {
  var k0 : key
  
  module O_SPR_SS : Oracle_t = {  
    var g : key -> input -> output
    
    proc init() : unit = {
      var gk : input -> output;
      
      gk <$ dfcs;
      
      g <$ dfun kdfcs.[k0 <- dunit gk];
    }
    
    proc get(k : key, x : input) = {
      return g k x;
    }
  }
  
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    
    k0 <$ dkey;
    
    O_SPR_SS.init();
    
    x <$ dinput;
    y <@ O_SPR_SS.get(k0, x);
    
    x' <@ A(O_SPR_SS).find(k0, x);
    y' <@ O_SPR_SS.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.

local lemma EqPr_SPR_SPRSS &m:
  Pr[SPR(A, O_Default).main() @ &m : res]
  =
  Pr[SPR_SS.main() @ &m : res].
proof.
byequiv => //=.
proc; inline *.
swap{1} 2 -1.
seq 1 1: (={glob A} /\ k{1} = SPR_SS.k0{2}); 1: by rnd.
wp.
conseq (: _ ==>    ={x, x', y} 
                /\ k{1} = SPR_SS.k0{2} 
                /\ O_Default.f{1} = SPR_SS.O_SPR_SS.g{2}); 1: by smt().
call (: O_Default.f{1} = SPR_SS.O_SPR_SS.g{2}); 1: by proc.
wp; rnd => />; 1: by smt().
transitivity{1} {O_Default.f <$ dfc;}
                (true ==> ={O_Default.f})
                (true ==>  O_Default.f{1} = SPR_SS.O_SPR_SS.g{2}) => //.
+ by rnd; skip => />; rewrite eq_df_dfc.
rnd: *0 *0.       
wp; skip => /> &2.
split => [g gin | eqmug f fin].
+ rewrite dmap_id; congr.
  rewrite /dfc (MUFF_Key.dfunE_dlet_fix1 _ (SPR_SS.k0{2})) /=.
  by rewrite /dfcs /kdfcs /dfcs; congr; rewrite fun_ext => f; rewrite dmap_id.
rewrite supp_dlet /=; exists (f SPR_SS.k0{2}).
split; 1: by rewrite dfun_fu /= 1:dunifin_fu dmap_id //= dfun_fu.
rewrite dmap_id dfun_supp => k @/(_.[_<-_]). 
case (SPR_SS.k0{2} = k) => [-> | ?]; 1: by rewrite supp_dunit.
by rewrite dmap_id dfun_supp in fin => /#.
qed.

local lemma EqPr_SPRSS_SPRNK &m:
  Pr[SPR_SS.main() @ &m : res]
  =
  Pr[SPR_NK(R_SPRNK_SPR(A), O_NK_Default).main() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
swap{2} 6 -5; swap{2} 7 -4.
seq 3 3 : (   ={glob A} 
           /\ ={k0}(SPR_SS, R_SPRNK_SPR)
           /\ SPR_SS.O_SPR_SS.g{1} 
              = 
              (fun k => 
                if k = R_SPRNK_SPR.k0{2}
                then O_NK_Default.gk{2}
                else R_SPRNK_SPR.g{2} k)).
+ seq 1 1 : (={glob A} /\ ={k0}(SPR_SS, R_SPRNK_SPR)); 1: by rnd.
  conseq (: _ ==> SPR_SS.O_SPR_SS.g{1} 
                  =
                  fun (k : key) =>
                    if k = R_SPRNK_SPR.k0{2} 
                    then O_NK_Default.gk{2}
                    else R_SPRNK_SPR.g{2} k) => //.
  transitivity{1} {SPR_SS.O_SPR_SS.g <@ EquivSamplings.fixone_dfc(SPR_SS.k0);}
                  (={SPR_SS.k0} ==> ={SPR_SS.O_SPR_SS.g})
                  (SPR_SS.k0{1} = R_SPRNK_SPR.k0{2} 
                   ==> 
                   SPR_SS.O_SPR_SS.g{1}
                   = 
                   (fun k =>  
                     if k = R_SPRNK_SPR.k0{2}
                     then O_NK_Default.gk{2}
                     else R_SPRNK_SPR.g{2} k)); 1,2: by smt().
  - inline *.
    wp; sp.
    rnd; rnd.
    by skip.
  transitivity{1} {SPR_SS.O_SPR_SS.g <@ EquivSamplings.if_dfc(SPR_SS.k0);}
                  (={SPR_SS.k0} ==> ={SPR_SS.O_SPR_SS.g})
                  (SPR_SS.k0{1} = R_SPRNK_SPR.k0{2} 
                   ==> 
                   SPR_SS.O_SPR_SS.g{1}
                   = 
                   (fun k =>  
                     if k = R_SPRNK_SPR.k0{2}
                     then O_NK_Default.gk{2}
                     else R_SPRNK_SPR.g{2} k)); 1,2: by smt().
  - by call Eqv_fixone_if_dfc.
  inline *.
  wp; sp.
  rnd; rnd.
  by skip.
wp.
call (:   SPR_SS.k0{1} = R_SPRNK_SPR.k0{2} 
       /\ SPR_SS.O_SPR_SS.g{1} 
          =
          (fun (k : key) =>
            if k = R_SPRNK_SPR.k0{2}
            then O_NK_Default.gk{2}
            else R_SPRNK_SPR.g{2} k)).
+ proc; inline *.
  by wp; skip.
by wp; rnd; skip.
qed.


local module SPR_NK_Rep (A : Adv_SPR_NK) = {
  var x0 : input
  var y0 : output
  var f : input -> output
  
  module O_SPR_NK_Rep : Oracle_NK_t = {
    proc get(x : input) : output = {
      var b;
      
      b <@ BFOF.query(x);
      
      return if !b /\ x <> x0 then f x else y0;
    }
  }

  proc main() : bool = {
    var x' : input;
    var y' : output;
    
    BFOF.init();

    x0 <$ dinput;
    y0 <$ doutput;

    f <$ MUFF_In.dfun (fun _ => doutput \ (pred1 y0));    
    
    x' <@ A(O_SPR_NK_Rep).find(x0);
    
    y' <@ O_SPR_NK_Rep.get(x');
    
    return x' <> x0 /\ y' = y0;
  }
}.

local lemma EqPr_SPRNK_SPRNKRep &m :
  Pr[SPR_NK(R_SPRNK_SPR(A), O_NK_Default).main() @ &m : res]
  =
  Pr[SPR_NK_Rep(R_SPRNK_SPR(A)).main() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
wp.
call (: ={R_SPRNK_SPR.k0, R_SPRNK_SPR.g} /\
        (forall (x : input), 
          O_NK_Default.gk{1} x 
          = 
          if !BFOF.f{2} x /\ x <> SPR_NK_Rep.x0{2} 
          then SPR_NK_Rep.f{2} x 
          else SPR_NK_Rep.y0{2})).
+ by proc; inline *; auto => /> &1 &2 /(_ x{2}).
rnd; rnd; wp.
swap{1} 2 -1; swap{2} 2 -1.
seq 1 1 : (={glob A} /\ x{1} = SPR_NK_Rep.x0{2}); 1: by rnd.
conseq (_ : _ 
            ==> 
            (forall (x : input), 
              O_NK_Default.gk{1} x 
              = 
              if !BFOF.f{2} x /\ x <> SPR_NK_Rep.x0{2} 
              then SPR_NK_Rep.f{2} x 
              else SPR_NK_Rep.y0{2})).
+ move=> /> &2 gk fl y0 br ih k kin gL glin r.
  by rewrite (eq_sym r); congr; rewrite !ih //= /#.
transitivity{1} {O_NK_Default.gk <@ LR.LambdaRepro.left();}
                (true ==> ={O_NK_Default.gk})
                (x{1} = SPR_NK_Rep.x0{2} 
                 ==> 
                 (forall (x : input),
                   O_NK_Default.gk{1} x 
                   =
                   if ! BFOF.f{2} x /\ x <> SPR_NK_Rep.x0{2} 
                   then SPR_NK_Rep.f{2} x
                   else SPR_NK_Rep.y0{2})); 1,2: by smt().
+ inline *.
  by wp; rnd.
transitivity{1} {O_NK_Default.gk <@ LR.LambdaRepro.right(x);}
                (true ==> ={O_NK_Default.gk})
                (x{1} = SPR_NK_Rep.x0{2} 
                 ==> 
                 (forall (x : input),
                   O_NK_Default.gk{1} x 
                   =
                   if ! BFOF.f{2} x /\ x <> SPR_NK_Rep.x0{2} 
                   then SPR_NK_Rep.f{2} x
                   else SPR_NK_Rep.y0{2})); 1,2: by smt().
+ by call LR.main_theorem.
inline *.
wp; rnd.
swap{2} 1 1.
by rnd; rnd; wp; skip.
qed.  


local lemma EqPr_SPR_SPRNKRep &m:
  Pr[SPR(A, O_Default).main() @ &m : res]
  =
  Pr[SPR_NK_Rep(R_SPRNK_SPR(A)).main() @ &m : res].
proof. 
by rewrite EqPr_SPR_SPRSS EqPr_SPRSS_SPRNK EqPr_SPRNK_SPRNKRep. 
qed.

local lemma SPRNKRep_Implies_BFFind &m :
  Pr[SPR_NK_Rep(R_SPRNK_SPR(A)).main() @ &m : res] 
  <= 
  Pr[BF_Find(R_BFFind_SPRNK(A), BFOF).main() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
wp.
conseq (: ={glob A} ==> ={BFOF.f, x'0} /\ SPR_NK_Rep.f{1} x'0{1} <> SPR_NK_Rep.y0{1}) => // />; 1: by smt().
call (:   ={glob BFOF, R_SPRNK_SPR.k0, R_SPRNK_SPR.g}
       /\ SPR_NK_Rep.y0{1} = R_BFFind_SPRNK.y0{2}
       /\ SPR_NK_Rep.f{1} = R_BFFind_SPRNK.f{2}
       /\ SPR_NK_Rep.x0{1} = R_BFFind_SPRNK.x0{2}).
+ proc; inline *.
  by wp; skip.
rnd; rnd; wp; rnd; rnd; rnd; rnd; skip =>/> fL flin x0 x0in y0 y0in fl' flpin k kin g gin r.
move/MUFF_In.dfun_supp: flpin => /= /(_ r).
by rewrite supp_dexcepted /pred1 /=.
qed.

local lemma SPR_Implies_BFDistinguish &m:
  Pr[KHFO_SPR.SPR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_SPRNK(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_SPRNK(A)), BFOD).main(true) @ &m : res] |.
proof.
apply (StdOrder.RealOrder.ler_trans Pr[BF_Find(R_BFFind_SPRNK(A), BFOF).main() @ &m : res]); last first.
+ by rewrite (Find_Implies_Distinguish &m (R_BFFind_SPRNK(A))).
by rewrite EqPr_SPR_SPRNKRep SPRNKRep_Implies_BFFind.
qed.

end section.

end SPRBound.

(*
theory SPRBound.

type key.
type input.
type output.

clone import FinType as FinKey with
  type t <= key.

clone import FinType as FinIn with
  type t <= input.

clone import FinProdType as FinKeyIn with
  type t1 <= key,
  type t2 <- input,
  
  theory FT1 <= FinKey,
  theory FT2 <= FinIn.
  
clone import FinType as FinOut with
  type t <= output.

axiom gt1_cardout : 1 < FinOut.card.

op [lossless] dkey : key distr.
op [lossless] dinput : input distr.

clone import MUniFinFun as MUFF_Key with
  type t <= key,
  
  theory FinT <= FinKey.

clone import MUniFinFun as MUFF_In with
  type t <= input,
  
  theory FinT <= FinIn.

clone import MUniFinFun as MUFF_KeyIn with
  type t <= key * input,
  
  theory FinT <= FinKeyIn.

clone import MFinite as MF_Out with
  type t <= output,
  
  theory Support <= FinOut.

op doutput = MF_Out.dunifin.

clone import BooleanFunctions as BF with
  type in_t <- key * input,
  type out_t <- output,
  
  theory FinIn <- FinKeyIn,
  theory FinOut <- FinOut,
  theory LR.MUFF <- MUFF_KeyIn,
  theory LR.MFY <- MF_Out
  
  proof *.
  realize gt1_cardout by exact: gt1_cardout.

    
op [lossless full uniform] df : (key -> input -> output) distr.

lemma df_funi : is_funiform df.
proof. by rewrite is_full_funiform 1:df_fu df_uni. qed.

(*
op df' : (key -> input -> output) distr =
  dfun (fun (k : key) => dfun (fun (x : input) => doutput)).

lemma df'_ll : is_lossless df'.
proof. by rewrite dfun_ll => k; rewrite dfun_ll => x /=; apply dunifin_ll. qed.

lemma df'_fu : is_full df'.
proof. by rewrite dfun_fu => k /=; rewrite dfun_fu => x /=; apply dunifin_fu. qed.

lemma df'_uni : is_uniform df'.
proof. by rewrite dfun_uni => k /=; rewrite dfun_uni => x /=; apply dunifin_uni. qed.

lemma df'_funi : is_funiform df'.
proof. by rewrite is_full_funiform 1:df'_fu df'_uni. qed.

lemma eq_df_df' : df = df'.
proof. by rewrite &(eq_funi_ll) 1:df_funi 1:df_ll 1:df'_funi df'_ll. qed.

lemma dmap_df'_eq (k : key) :
  dmap df' (fun f => f k) = dfun (fun (x : input) => doutput).
proof. 
rewrite dfun_projE /= eq_sym -{1}(dscalar1 (dfun (fun (_ : input) => doutput))) -/df'.
by congr; rewrite df'_ll is_losslessP 1:dfun_ll //= dunifin_ll.
qed.
*)

(* Plan:
   - Instantiate KHFO SPR with df
   - Instantiate KHFO SPR with df'
   - Prove SPR with df and df' directly equivalent
   - Create auxiliary KHFO SPR with df', say SPR', where game computes f k immediately after sampling f/k and then initializes its oracle with this function directly (not providing k).
   - Prove regular SPR with df' equivalent to SPR'.
   - Create another auxiliary KHFO SPR, say SPR'', where k does not exist and f is sampled from "dfun (fun (x : input) => doutput)"
   - Prove SPR' equivalent to SPR'' by using transitivity to (1) go from SPR' to a variant that encapsulates the sampling of f and computation of f k in the "S.map" function in DMap.ec, and (2) to go from SPR'' to a variant that directly samples f from "dmap df' (fun f => f k)" (and by lemma dmap_df'_eq above, this is equivalent to sampling f as SPR'' does).
   - At this point, SPR'' should be (close to identical) to the SPR game used in the original proof in HashFunctionBounds.ec. So, use the proof in there and adapt it so that the proof goest through here as well.
   - Combine everything to get the full proof for the original KHFO SPR with df.
*)
clone import KeyedHashFunctionsO as KHFO with
  type key_t <- key,
  type in_t <- input,
  type out_t <- output,
  
    op df <- df
    
  proof *.
  realize df_ll by exact: df_ll.

clone import SPR as KHFO_SPR with
  op din <- dinput,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: dinput_ll.
  realize dkey_ll by exact: dkey_ll.


module (R_BFFind_SPR (A : Adv_SPR) : Adv_BFFind) (BFO : BFOF_t) = {
  var f : key * input -> output
  var k0 : key
  var x0 : input
  var y0 : output
  
  module O_R_BFFind_SPR : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var b;

      b <@ BFO.query((k, x));
      
      return if !b /\ (k, x) <> (k0, x0) then f (k, x) else y0;
    }
  }

  proc find() : key * input = {
    var x' : input;
    
    x0 <$ dinput;
    y0 <$ doutput;

    f <$ MUFF_KeyIn.dfun (fun _ => doutput \ (pred1 y0));
    
    k0 <$ dkey;
    x'  <@ A(O_R_BFFind_SPR).find(k0, x0);
    
    return (k0, x');
  }
}.


section.

declare module A <: Adv_SPR {-KHFO.O_Default, -R_BFFind_SPR, -BFOF, -BFOD}.

local op df'_prod : (key * input -> output) distr =
  dfun (fun (kx : key * input) => doutput).

local lemma df'_prod_ll : is_lossless df'_prod.
proof. by rewrite &(dfun_ll) /= dunifin_ll. qed.

local lemma df'_prod_fu : is_full df'_prod.
proof. by rewrite &(dfun_fu) /= dunifin_fu. qed.

local lemma df'_prod_uni : is_uniform df'_prod.
proof. by rewrite &(dfun_uni) /= dunifin_uni. qed.

local op df' : (key -> input -> output) distr =
  dmap df'_prod (fun (f : key * input -> output) => 
                  (fun (k : key) => fun (x : input) => f (k, x))).
                  
local lemma df'_ll : is_lossless df'.
proof. by rewrite &(dmap_ll) /= df'_prod_ll. qed.

local lemma df'_fu : is_full df'.
proof. 
rewrite &(dmap_fu) /= 2:df'_prod_fu /surjective.
move=> f; exists (fun (kx : key * input) => f kx.`1 kx.`2).
by rewrite fun_ext => k; rewrite fun_ext => x.
qed.

local lemma df'_uni : is_uniform df'.
proof.
rewrite &(dmap_uni) /= 2:df'_prod_uni /injective.
by move=> f g eqfg; rewrite fun_ext => kx /#.
qed.

local lemma df'_funi : is_funiform df'.
proof. by rewrite is_full_funiform 1:df'_fu df'_uni. qed.

local lemma eq_df_df' : df = df'.
proof. by rewrite &(eq_funi_ll) 1:df_funi 1:df_ll 1:df'_funi df'_ll. qed.


local clone import KeyedHashFunctionsO as KHFO' with
  type key_t <- key,
  type in_t <- input,
  type out_t <- output,
  
    op df <- df'
    
  proof *.
  realize df_ll by exact: df'_ll.

local clone import KHFO'.SPR as KHFO'_SPR with
  op din <- dinput,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: dinput_ll.
  realize dkey_ll by exact: dkey_ll.


local equiv Equiv_KHFO_SPR_KHFO'_SPR :
   KHFO_SPR.SPR(A, KHFO.O_Default).main ~ KHFO'_SPR.SPR(A, KHFO'.O_Default).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: ={f}(KHFO.O_Default, KHFO'.O_Default)); 1: by proc.
wp; rnd; wp; rnd; rnd; skip => />.
by rewrite eq_df_df'.
qed.

(*
local clone import DMapSampling as DMS with
  type t1 <- key -> input -> output,
  type t2 <- input -> output
  
  proof *.


local module O_Default_NK : Oracle_t = {
  var f : input -> output
  
  proc init(f_init : input -> output) = {
    f <- f_init;
  }
  
  proc get(k : key, x : input) : output = {
    return f x;
  }
}.

local module SPR_DMS = {
  proc main() : bool = {
    var f : key -> input -> output;
    var k : key;
    var x : input;
    var x' : input;

    f <$ df';
    k <$ dkey;
    O_Default_NK.init(f k);
    x <$ dinput;
    x' <@ A(O_Default_NK).find(k, x);
    
    return x <> x' /\ f k x = f k x';
  }
  
  proc main_map() : bool = {
    var f : input -> output;
    var k : key;
    var x : input;
    var x' : input;

    k <$ dkey;
    f <@ S.map(df', fun f => f k);
    O_Default_NK.init(f);
    x <$ dinput;
    x' <@ A(O_Default_NK).find(k, x);
    
    return x <> x' /\ f x = f x';
  }
  
  proc main_sample() : bool = {
    var f : input -> output;
    var k : key;
    var x : input;
    var x' : input;

    k <$ dkey;
    f <@ S.sample(df', fun f => f k);
    O_Default_NK.init(f);
    x <$ dinput;
    x' <@ A(O_Default_NK).find(k, x);

    return x <> x' /\ f x = f x';
  }
}.

local equiv Equiv_KHFO'_SPR_SPR_DMS_Main :
  KHFO'_SPR.SPR(A, O_Default).main ~ SPR_DMS.main : ={glob A} ==> ={res}. 
proof.
proc; inline *.
call (: O_Default.f{1} O_Default.k{1} = O_Default_NK.f{2}); 1: by proc.
by rnd; wp; rnd; rnd; skip.
qed.


local module SPR_NK = {
  proc main() : bool = {
    var f : input -> output;
    var x, x' : input;
    var k : key;
    
    f <$ dfun (fun (x : input) => doutput);
    O_Default_NK.init(f);
    x <$ dinput;
    k <$ dkey;
    x' <@ A(O_Default_NK).find(k, x);

    return x <> x' /\ f x = f x';
  }
}.

local equiv Equiv_SPR_DMS_Main_SPR_NK :
  SPR_DMS.main ~ SPR_NK.main : ={glob A} ==> ={res}. 
proof.
transitivity SPR_DMS.main_map (={glob A} ==> ={res}) (={glob A} ==> ={res}) => [/# | // | |].
+ proc; inline *.
  call (: ={O_Default_NK.f}); 1: by proc.
  swap{1} 2 -1.
  by rnd; wp; rnd; wp; rnd; skip.
transitivity SPR_DMS.main_sample (={glob A} ==> ={res}) (={glob A} ==> ={res}) => [/# | // | |].
+ proc; inline O_Default_NK.init.
  call (: ={O_Default_NK.f}); 1: by proc.
  rnd; wp => /=.
  by symmetry; call DMS.sample; rnd; skip.
proc; inline *.
swap{2} 5 -4.
wp; call (: ={O_Default_NK.f}); 1: by proc.
wp; rnd; wp; rnd; wp; rnd; skip => /> k kin. 
by rewrite dmap_df'_eq.
qed.

local lemma EqPr_SPR_SPR_NK &m :
  Pr[KHFO_SPR.SPR(A, KHFO.O_Default).main() @ &m : res]
  =
  Pr[SPR_NK.main() @ &m : res].
proof.
byequiv=> //=.
transitivity KHFO'_SPR.SPR(A, KHFO'.O_Default).main 
             (={glob A} ==> ={res}) 
             (={glob A} ==> ={res}) => [/# | // | |].
+ by apply Equiv_KHFO_SPR_KHFO'_SPR.                
transitivity SPR_DMS.main 
             (={glob A} ==> ={res}) 
             (={glob A} ==> ={res}) => [/# | // | |].
+ by apply Equiv_KHFO'_SPR_SPR_DMS_Main.                
by apply Equiv_SPR_DMS_Main_SPR_NK.
qed.
*)


local clone import DMapSampling as DMS with
  type t1 <- key -> input -> output,
  type t2 <- key * input -> output
  
  proof *.

local module O_Default_Uncurry : Oracle_t = {
  var f : key * input -> output
  
  proc init(f_init : key * input -> output) = {
    f <- f_init;
  }
  
  proc get(k : key, x : input) : output = {
    return f (k, x);
  }
}.

local module SPR_DMS = {
  proc main() : bool = {
    var f : key -> input -> output;
    var k : key;
    var x : input;
    var x' : input;

    f <$ df';
    k <$ dkey;
    O_Default_Uncurry.init((fun (kx : key * input) => f kx.`1 kx.`2));
    x <$ dinput;
    x' <@ A(O_Default_Uncurry).find(k, x);
    
    return x' <> x /\ f k x' = f k x;
  }

  proc main_sample() : bool = {
    var f : key * input -> output;
    var k : key;
    var x : input;
    var x' : input;

    f <@ S.sample(df', fun f => (fun (kx : key * input) => f kx.`1 kx.`2));
    k <$ dkey;
    O_Default_Uncurry.init(f);
    x <$ dinput;
    x' <@ A(O_Default_Uncurry).find(k, x);

    return x' <> x /\ f (k, x') = f (k, x);
  }

  proc main_map() : bool = {
    var f : key * input -> output;
    var k : key;
    var x : input;
    var x' : input;

    f <@ S.map(df', fun f => (fun (kx : key * input) => f kx.`1 kx.`2));
    k <$ dkey;
    O_Default_Uncurry.init(f);
    x <$ dinput;
    x' <@ A(O_Default_Uncurry).find(k, x);
    
    return x' <> x /\ f (k, x') = f (k, x);
  }
}.

local equiv Equiv_KHFO'_SPR_SPR_DMS_Main :
  KHFO'_SPR.SPR(A, O_Default).main ~ SPR_DMS.main : ={glob A} ==> ={res}. 
proof.
proc; inline *.
wp; call (: forall (k : key) (x : input),
              O_Default.f{1} k x = O_Default_Uncurry.f{2} (k, x)).
by proc; skip => /> /#.
by wp; rnd; wp; rnd; rnd; skip.
qed.

local module SPR_Uncurry = {
  proc main() : bool = {
    var f : key * input -> output;
    var x, x' : input;
    var k : key;
    
    f <$ df'_prod;
    k <$ dkey;
    O_Default_Uncurry.init(f);
    x <$ dinput;
    x' <@ A(O_Default_Uncurry).find(k, x);

    return x' <> x /\ f (k, x') = f (k, x);
  }
}.

local equiv Equiv_SPR_DMS_Main_SPR_Uncurry :
  SPR_DMS.main ~ SPR_Uncurry.main : ={glob A} ==> ={res}. 
proof.
transitivity SPR_DMS.main_map (={glob A} ==> ={res}) (={glob A} ==> ={res}) => [/# | // | |].
+ proc; inline *.
  call (: ={O_Default_Uncurry.f}); 1: by proc.
  swap{1} 2 -1; swap{2} 5 -4.
  by rnd; wp; rnd; wp; rnd; skip.
transitivity SPR_DMS.main_sample (={glob A} ==> ={res}) (={glob A} ==> ={res}) => [/# | // | |].
+ proc; inline O_Default_Uncurry.init.
  call (: ={O_Default_Uncurry.f}); 1: by proc.
  rnd; wp; rnd => /=.
  by symmetry; call DMS.sample.
proc; inline *.
call (: ={O_Default_Uncurry.f}); 1: by proc.
rnd; wp; rnd; wp; rnd; wp; skip => />. 
split => [fR fRin | _ fL] /=; 2: by rewrite df'_prod_fu.
by rewrite dmap_comp dmap1E /(\o) /pred1; congr; rewrite fun_ext => f /#.
qed.

local lemma EqPr_SPR_SPR_Uncurry &m :
  Pr[KHFO_SPR.SPR(A, KHFO.O_Default).main() @ &m : res]
  =
  Pr[SPR_Uncurry.main() @ &m : res].
proof.
byequiv=> //=.
transitivity KHFO'_SPR.SPR(A, KHFO'.O_Default).main 
             (={glob A} ==> ={res}) 
             (={glob A} ==> ={res}) => [/# | // | |].
+ by apply Equiv_KHFO_SPR_KHFO'_SPR.                
transitivity SPR_DMS.main 
             (={glob A} ==> ={res}) 
             (={glob A} ==> ={res}) => [/# | // | |].
+ by apply Equiv_KHFO'_SPR_SPR_DMS_Main.                
by apply Equiv_SPR_DMS_Main_SPR_Uncurry.
qed.


local module R_Find_SPR_Uncurry_Rand = {
  import var R_BFFind_SPR
  
  module O_R_Find_SPR_Uncurry_Rand : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var b;

      b <@ BFOF.query((k, x));
      
      return if !b /\ (k, x) <> (k0, x0) then f (k, x) else y0;
    }
  }

  proc find() : bool = {
    var x' : input;
    var y' : output;
    
    BFOF.init();
    
    x0 <$ dinput;
    y0 <$ doutput;

    f <$ MUFF_KeyIn.dfun (fun _ => doutput \ (pred1 y0));
    
    k0 <$ dkey;
    x'  <@ A(O_R_Find_SPR_Uncurry_Rand).find(k0, x0);
    
    y' <@ O_R_Find_SPR_Uncurry_Rand.get((k0, x'));
    
    return x' <> x0 /\ y' = y0;
  }
}.

local lemma Find_SPR_Uncurry_Rand_Implies_BFFind &m :
  Pr[R_Find_SPR_Uncurry_Rand.find() @ &m : res] 
  <= 
  Pr[BF_Find(R_BFFind_SPR(A), BFOF).main() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
wp.
conseq (_: ={glob A} 
           ==> 
               ={BFOF.f, R_BFFind_SPR.k0, x'} 
            /\ R_BFFind_SPR.f{1} (R_BFFind_SPR.k0, x'){1} <> R_BFFind_SPR.y0{1}) => />; 1: by smt().
call (: ={glob BFOF, glob R_BFFind_SPR}); 1: by sim.
do 5! rnd; skip => /> fL fLin x0L x0Lin y0L y0Lin fL' + k kin r. 
by rewrite dfun_supp => /(_ (k, r)) /=; rewrite supp_dexcepted /pred1 /= => -[_ ->].
qed.

local lemma EqPr_SPR_Uncurry_BFFind &m :
  Pr[SPR_Uncurry.main() @ &m: res] 
  = 
  Pr[R_Find_SPR_Uncurry_Rand.find() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
wp.
swap{1} 2 3.
swap{1} 4 -3; swap{1} 5 -3.
swap{2} 2 -1; swap{2} 5 -3 => /=.
seq 2 2: (   ={glob A} 
          /\ x{1} = R_BFFind_SPR.x0{2}
          /\ k{1} = R_BFFind_SPR.k0{2}); 1: by rnd; rnd.
call (: forall (k : key) (x : input),
          O_Default_Uncurry.f{1} (k, x) 
          = 
          if !BFOF.f{2} (k, x) /\ (k, x) <> (R_BFFind_SPR.k0, R_BFFind_SPR.x0){2} 
          then R_BFFind_SPR.f{2} (k, x)
          else R_BFFind_SPR.y0{2}).
+ proc; inline *.
  by wp; skip => /> &1 &2 /(_ k{2} x{2}).
wp => />; 1: smt().
conseq (: _ ==> (forall (k : key) (x : input), 
                   f{1} (k, x) 
                   = 
                   if !BFOF.f{2} (k, x) /\ (k, x) <> (R_BFFind_SPR.k0, R_BFFind_SPR.x0){2}
                   then R_BFFind_SPR.f{2} (k, x) 
                   else R_BFFind_SPR.y0{2})).
+ move=> /> &2 fL fR y0 fB ih r.
  by rewrite (eq_sym r); congr; rewrite !ih /= /#.
transitivity {1} {f <@ LR.LambdaRepro.left();}
  (true ==> ={f}) 
  (k{1} = R_BFFind_SPR.k0{2} /\ x{1} = R_BFFind_SPR.x0{2} 
   ==> 
   forall (k : key) (x : input), 
     f{1} (k, x) 
     = 
     if ! BFOF.f{2} (k, x) /\ (k, x) <> (R_BFFind_SPR.k0, R_BFFind_SPR.x0){2} 
     then  R_BFFind_SPR.f{2} (k, x) 
     else  R_BFFind_SPR.y0{2}) => //.
+ by move=> &1 &2 ?; exists R_BFFind_SPR.k0{2} R_BFFind_SPR.x0{2}.
+ by inline *; wp; rnd.
transitivity {1} {R_BFFind_SPR.f <@ LR.LambdaRepro.right(k, x);}
  (true ==> f{1} = R_BFFind_SPR.f{2}) 
  (k{1} = R_BFFind_SPR.k0{2} /\ x{1} = R_BFFind_SPR.x0{2} 
   ==> 
   forall (k : key) (x : input), 
     R_BFFind_SPR.f{1} (k, x) 
     = 
     if ! BFOF.f{2} (k, x) /\ (k, x) <> (R_BFFind_SPR.k0, R_BFFind_SPR.x0){2} 
     then R_BFFind_SPR.f{2} (k, x) 
     else R_BFFind_SPR.y0{2}) => //.
+ by move=> &1 &2 ?; exists R_BFFind_SPR.k0{2} R_BFFind_SPR.x0{2}.
+ by call LR.main_theorem. 
inline *; swap{1} 3 -1.
by wp; rnd; rnd; rnd; wp; skip. 
qed.

lemma SPR_Implies_BFDistinguish &m:
  Pr[KHFO_SPR.SPR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_SPR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_SPR(A)), BFOD).main(true) @ &m : res] |.
proof.
apply (StdOrder.RealOrder.ler_trans Pr[BF_Find(R_BFFind_SPR(A), BFOF).main() @ &m : res]); last first.
+ by rewrite (Find_Implies_Distinguish &m (R_BFFind_SPR(A))).
by rewrite EqPr_SPR_SPR_Uncurry EqPr_SPR_Uncurry_BFFind Find_SPR_Uncurry_Rand_Implies_BFFind.
qed.

end section.

end SPRBound.
*)

(* 
  Try and use Reprogramming.ec theory to do this prove.
*)
theory TCRBound.

op [lossless] dkey : key distr.

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

declare axiom A_pick_ll (O <: Oracle_t{-A}):
  islossless O.get => islossless A(O).pick.

declare axiom A_find_ll (O <: Oracle_t{-A}):
  islossless O.get => islossless A(O).find.

local module TCR_SS = {
  var k0 : key
  
  module O_TCR_SS : Oracle_t = {  
    var g : key -> input -> output
    
    proc init() : unit = {
      var gk : input -> output;
      
      gk <$ dfcs;
      
      g <$ dfun kdfcs.[k0 <- dunit gk];
    }
    
    proc get(k : key, x : input) = {
      return g k x;
    }
  }
  
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    
    k0 <$ dkey;
    
    O_TCR_SS.init();
    
    x <@ A(O_TCR_SS).pick();
    y <@ O_TCR_SS.get(k0, x);
    
    x' <@ A(O_TCR_SS).find(k0);
    y' <@ O_TCR_SS.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.

local lemma EqPr_TCR_TCRSS &m:
  Pr[TCR(A, O_Default).main() @ &m : res]
  =
  Pr[TCR_SS.main() @ &m : res].
proof.
byequiv => //=.
proc; inline *.
swap{1} 3 -2.
seq 1 1: (={glob A} /\ k{1} = TCR_SS.k0{2}); 1: by rnd.
wp.
conseq (: _ ==>    ={x, x', y} 
                /\ k{1} = TCR_SS.k0{2} 
                /\ O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}); 1: by smt().
call (: O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}); 1: by proc.
wp; call (: O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}); 1: by proc.
conseq (: _ ==> O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}) => //.
transitivity{1} {O_Default.f <$ dfc;}
                (true ==> ={O_Default.f})
                (true ==>  O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}) => //.
+ by rnd; skip => />; rewrite eq_df_dfc.
rnd: *0 *0.       
wp; skip => /> &2.
split => [g gin | eqmug f fin]. 
+ rewrite dmap_id; congr.
  rewrite /dfc /kdfcs /dfcs (MUFF_Key.dfunE_dlet_fix1 _ (TCR_SS.k0{2})) /=.
  by congr; rewrite fun_ext => f; rewrite dmap_id.
rewrite supp_dlet /=; exists (f TCR_SS.k0{2}).
split; 1: by rewrite dfun_fu /= 1:dunifin_fu dmap_id //= dfun_fu.
rewrite dmap_id dfun_supp => k @/(_.[_<-_]). 
case (TCR_SS.k0{2} = k) => [-> | ?]; 1: by rewrite supp_dunit.
by rewrite dmap_id dfun_supp in fin => /#.
qed.


local module TCR_SSR = {
  var k0 : key
  var gk : input -> output
  var g : key -> input -> output
  
  module O_TCR_SSR_Pick : Oracle_t = {  
    proc get(k : key, x : input) = {
      var y : output;
      
      if (k = k0) {
        y <- gk x;
      } else {
        y <- g k x;
      } 
      
      return y;
    }
  }

 module O_TCR_SSR_Find : Oracle_t = {  
    proc get(k : key, x : input) = {
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
    
    x <@ A(O_TCR_SSR_Pick).pick();
    y <@ O_TCR_SSR_Find.get(k0, x);
    
    x' <@ A(O_TCR_SSR_Find).find(k0);
    y' <@ O_TCR_SSR_Find.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.

local lemma EqPr_TCRSS_TCRSSR &m:
  Pr[TCR_SS.main() @ &m : res]
  =
  Pr[TCR_SSR.main() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
seq 3 3 : (   ={glob A} 
           /\ ={k0}(TCR_SS, TCR_SSR)
           /\ TCR_SS.O_TCR_SS.g{1} 
              = 
              (fun (k : key) => 
                if k = TCR_SSR.k0{2}
                then TCR_SSR.gk{2}
                else TCR_SSR.g{2} k)).
+ seq 1 1 : (={glob A} /\ ={k0}(TCR_SS, TCR_SSR)); 1: by rnd.
  sp.
  conseq (: _ ==> TCR_SS.O_TCR_SS.g{1} 
                  =
                  fun (k : key) =>
                    if k = TCR_SSR.k0{2} 
                    then TCR_SSR.gk{2}
                    else TCR_SSR.g{2} k) => //.
  transitivity{1} {TCR_SS.O_TCR_SS.g <@ EquivSamplings.fixone_dfc(TCR_SS.k0);}
                  (={TCR_SS.k0} ==> ={TCR_SS.O_TCR_SS.g})
                  (TCR_SS.k0{1} = TCR_SSR.k0{2} 
                   ==> 
                   TCR_SS.O_TCR_SS.g{1}
                   = 
                   (fun k =>  
                     if k = TCR_SSR.k0{2}
                     then TCR_SSR.gk{2}
                     else TCR_SSR.g{2} k)); 1,2: by smt().
  - inline *.
    wp; sp.
    rnd; rnd.
    by skip.
  transitivity{1} {TCR_SS.O_TCR_SS.g <@ EquivSamplings.if_dfc(TCR_SS.k0);}
                  (={TCR_SS.k0} ==> ={TCR_SS.O_TCR_SS.g})
                  (TCR_SS.k0{1} = TCR_SSR.k0{2} 
                   ==> 
                   TCR_SS.O_TCR_SS.g{1}
                   = 
                   (fun k =>  
                     if k = TCR_SSR.k0{2}
                     then TCR_SSR.gk{2}
                     else TCR_SSR.g{2} k)); 1,2: by smt().
  - by call Eqv_fixone_if_dfc.
  inline *.
  wp; sp.
  rnd; rnd.
  by skip. 
wp.
call (:   TCR_SS.k0{1} = TCR_SSR.k0{2} 
       /\ TCR_SS.O_TCR_SS.g{1} 
          =
          (fun (k : key) =>
            if k = TCR_SSR.k0{2}
            then TCR_SSR.gk{2}
            else TCR_SSR.g{2} k)).
+ proc; inline *.
  by wp; skip.
wp.
call (: TCR_SS.O_TCR_SS.g{1} 
        =
        (fun (k : key) =>
          if k = TCR_SSR.k0{2} 
          then TCR_SSR.gk{2}
          else TCR_SSR.g{2} k)).
+ by proc; inline *; wp; skip.
by skip.
qed.


local lemma EqPr_TCR_TCRSSR &m:
  Pr[TCR(A, O_Default).main() @ &m : res]
  =
  Pr[TCR_SSR.main() @ &m : res].
proof. 
by rewrite EqPr_TCR_TCRSS EqPr_TCRSS_TCRSSR. 
qed.


local module TCR_SSR_Nin = {
  var k0 : key
  var gk : input -> output
  var g : key -> input -> output
  
  module O_TCR_SSR_Pick : Oracle_t = {  
    proc get(k : key, x : input) = {
      return g k x;
    }
  }

 module O_TCR_SSR_Find : Oracle_t = {  
    proc get(k : key, x : input) = {
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
    
    x <@ A(O_TCR_SSR_Pick).pick();
    y <@ O_TCR_SSR_Find.get(k0, x);
    
    x' <@ A(O_TCR_SSR_Find).find(k0);
    y' <@ O_TCR_SSR_Find.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.


(*
 Idea:
 Bound difference between TCR_SSR_Nin and TCR_SSR by Reprogramming advantage.
 This by reducing TCR_SSR_Nin from Reprogram.main(false), and 
 TCR_SSR from Reprogram.main(true).
 (Possibly need to create auxiliary games to do the reduction instead of the TCR_SSR.
  These auxiliary games would only have the first part of the game (up to A.pick)
  and return x. Reduce this from Reprogame. Then, in actual prove, use seq just after 
  calling A.pick and use transitivity)
 Then, continue proof as before, getting to the BF properties.
*)

(*
section.

declare module A <: Adv_TCR {-KHFO.O_Default, -BFOF, -BFOD, -R_BFFind_TCR, -Counting_O}.

declare axiom A_pick_ll (O <: Oracle_t{-A}):
  islossless O.get => islossless A(O).pick.

declare axiom A_find_ll (O <: Oracle_t{-A}):
  islossless O.get => islossless A(O).find.

local module TCR_SS = {
  var k0 : key
  
  module O_TCR_SS : Oracle_t = {  
    var g : key -> input -> output
    
    proc init() : unit = {
      var gk : input -> output;
      
      gk <$ dfcs;
      
      g <$ dfun kdfcs.[k0 <- dunit gk];
    }
    
    proc get(k : key, x : input) = {
      return g k x;
    }
  }
  
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    
    k0 <$ dkey;
    
    O_TCR_SS.init();
    
    x <@ A(O_TCR_SS).pick();
    y <@ O_TCR_SS.get(k0, x);
    
    x' <@ A(O_TCR_SS).find(k0);
    y' <@ O_TCR_SS.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.

local lemma EqPr_TCR_TCRSS &m:
  Pr[TCR(A, O_Default).main() @ &m : res]
  =
  Pr[TCR_SS.main() @ &m : res].
proof.
byequiv => //=.
proc; inline *.
swap{1} 3 -2.
seq 1 1: (={glob A} /\ k{1} = TCR_SS.k0{2}); 1: by rnd.
wp.
conseq (: _ ==>    ={x, x', y} 
                /\ k{1} = TCR_SS.k0{2} 
                /\ O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}); 1: by smt().
call (: O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}); 1: by proc.
wp; call (: O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}); 1: by proc.
conseq (: _ ==> O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}) => //.
transitivity{1} {O_Default.f <$ dfc;}
                (true ==> ={O_Default.f})
                (true ==>  O_Default.f{1} = TCR_SS.O_TCR_SS.g{2}) => //.
+ by rnd; skip => />; rewrite eq_df_dfc.
rnd: *0 *0.       
wp; skip => /> &2.
split => [g gin | eqmug f fin]. 
+ rewrite dmap_id; congr.
  rewrite /dfc /kdfcs /dfcs (MUFF_Key.dfunE_dlet_fix1 _ (TCR_SS.k0{2})) /=.
  by congr; rewrite fun_ext => f; rewrite dmap_id.
rewrite supp_dlet /=; exists (f TCR_SS.k0{2}).
split; 1: by rewrite dfun_fu /= 1:dunifin_fu dmap_id //= dfun_fu.
rewrite dmap_id dfun_supp => k @/(_.[_<-_]). 
case (TCR_SS.k0{2} = k) => [-> | ?]; 1: by rewrite supp_dunit.
by rewrite dmap_id dfun_supp in fin => /#.
qed.


local module TCR_SSR = {
  var k0 : key
  var ks : key list
  var gk : input -> output
  var g : key -> input -> output
  
  module O_TCR_SSR_Pick : Oracle_t = {  
    proc get(k : key, x : input) = {
      var y : output;
      
      ks <- rcons ks k;
      
      if (k = k0) {
        y <- gk x;
      } else {
        y <- g k x;
      } 
      
      return y;
    }
  }

 module O_TCR_SSR_Find : Oracle_t = {  
    proc get(k : key, x : input) = {
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
    
    ks <- [];
    
    gk <$ dfcs;  
    g <$ dfc;
    
    x <@ A(O_TCR_SSR_Pick).pick();
    y <@ O_TCR_SSR_Find.get(k0, x);
    
    x' <@ A(O_TCR_SSR_Find).find(k0);
    y' <@ O_TCR_SSR_Find.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.

local lemma EqPr_TCRSS_TCRSSR &m:
  Pr[TCR_SS.main() @ &m : res]
  =
  Pr[TCR_SSR.main() @ &m : res].
proof.
byequiv=> //=.
proc; inline *.
seq 3 4 : (   ={glob A} 
           /\ ={k0}(TCR_SS, TCR_SSR)
           /\ TCR_SS.O_TCR_SS.g{1} 
              = 
              (fun (k : key) => 
                if k = TCR_SSR.k0{2}
                then TCR_SSR.gk{2}
                else TCR_SSR.g{2} k)).
+ seq 1 1 : (={glob A} /\ ={k0}(TCR_SS, TCR_SSR)); 1: by rnd.
  sp.
  conseq (: _ ==> TCR_SS.O_TCR_SS.g{1} 
                  =
                  fun (k : key) =>
                    if k = TCR_SSR.k0{2} 
                    then TCR_SSR.gk{2}
                    else TCR_SSR.g{2} k) => //.
  transitivity{1} {TCR_SS.O_TCR_SS.g <@ EquivSamplings.fixone_dfc(TCR_SS.k0);}
                  (={TCR_SS.k0} ==> ={TCR_SS.O_TCR_SS.g})
                  (TCR_SS.k0{1} = TCR_SSR.k0{2} 
                   ==> 
                   TCR_SS.O_TCR_SS.g{1}
                   = 
                   (fun k =>  
                     if k = TCR_SSR.k0{2}
                     then TCR_SSR.gk{2}
                     else TCR_SSR.g{2} k)); 1,2: by smt().
  - inline *.
    wp; sp.
    rnd; rnd.
    by skip.
  transitivity{1} {TCR_SS.O_TCR_SS.g <@ EquivSamplings.if_dfc(TCR_SS.k0);}
                  (={TCR_SS.k0} ==> ={TCR_SS.O_TCR_SS.g})
                  (TCR_SS.k0{1} = TCR_SSR.k0{2} 
                   ==> 
                   TCR_SS.O_TCR_SS.g{1}
                   = 
                   (fun k =>  
                     if k = TCR_SSR.k0{2}
                     then TCR_SSR.gk{2}
                     else TCR_SSR.g{2} k)); 1,2: by smt().
  - by call Eqv_fixone_if_dfc.
  inline *.
  wp; sp.
  rnd; rnd.
  by skip. 
wp.
call (:   TCR_SS.k0{1} = TCR_SSR.k0{2} 
       /\ TCR_SS.O_TCR_SS.g{1} 
          =
          (fun (k : key) =>
            if k = TCR_SSR.k0{2}
            then TCR_SSR.gk{2}
            else TCR_SSR.g{2} k)).
+ proc; inline *.
  by wp; skip.
wp.
call (: TCR_SS.O_TCR_SS.g{1} 
        =
        (fun (k : key) =>
          if k = TCR_SSR.k0{2} 
          then TCR_SSR.gk{2}
          else TCR_SSR.g{2} k)).
+ by proc; inline *; wp; skip.
by skip.
qed.


local lemma EqPr_TCR_TCRSSR &m:
  Pr[TCR(A, O_Default).main() @ &m : res]
  =
  Pr[TCR_SSR.main() @ &m : res].
proof. 
by rewrite EqPr_TCR_TCRSS EqPr_TCRSS_TCRSSR. 
qed.


local module TCR_SSR_Nin = {
  var k0 : key
  var ks : key list
  var gk : input -> output
  var g : key -> input -> output
  
  module O_TCR_SSR_Pick : Oracle_t = {  
    proc get(k : key, x : input) = {
      ks <- rcons ks k;
      
      return g k x;
    }
  }

 module O_TCR_SSR_Find : Oracle_t = {  
    proc get(k : key, x : input) = {
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
    
    ks <- [];
    
    gk <$ dfcs;  
    g <$ dfc;
    
    x <@ A(O_TCR_SSR_Pick).pick();
    y <@ O_TCR_SSR_Find.get(k0, x);
    
    x' <@ A(O_TCR_SSR_Find).find(k0);
    y' <@ O_TCR_SSR_Find.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.


local lemma LePr_TCRSSR_In &m :
  Pr[TCR_SSR.main() @ &m : res /\ (TCR_SSR.k0 \in TCR_SSR.ks)]
  <=
  Pr[TCR_SSR.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)].
proof. by byequiv (: _ ==> ={TCR_SSR.k0, TCR_SSR.ks}) => //; sim. qed.

local lemma EqPr_TCRSSR_TCRSSRNin &m:
  Pr[TCR_SSR.main() @ &m : res /\ ! (TCR_SSR.k0 \in TCR_SSR.ks)]
  =
  Pr[TCR_SSR_Nin.main() @ &m : res /\ ! (TCR_SSR_Nin.k0 \in TCR_SSR_Nin.ks)].
proof. 
byequiv (: (res /\ ! (TCR_SSR.k0 \in TCR_SSR.ks)){1}
           <=>
           (res /\ ! (TCR_SSR_Nin.k0 \in TCR_SSR_Nin.ks)){2}) => //.
proc; inline *.
wp => /=.
seq 4 4 : (   ={glob A} 
           /\ ={k0, ks, gk, g}(TCR_SSR, TCR_SSR_Nin)
           /\ TCR_SSR.ks{1} = []); 1: by auto.
seq 1 1 : (   ={k0, gk, g}(TCR_SSR, TCR_SSR_Nin)
           /\ (TCR_SSR.k0{1} \in TCR_SSR.ks{1} <=> TCR_SSR_Nin.k0{2} \in TCR_SSR_Nin.ks{2})
           /\ (! (TCR_SSR_Nin.k0{2} \in TCR_SSR_Nin.ks{2}) 
               => 
               ={glob A, x} /\ ={ks}(TCR_SSR, TCR_SSR_Nin))).
+ call (: TCR_SSR_Nin.k0 \in TCR_SSR_Nin.ks, 
        ={k0, ks, gk, g}(TCR_SSR, TCR_SSR_Nin), 
        ={k0, gk, g}(TCR_SSR, TCR_SSR_Nin)
        /\
        TCR_SSR.k0{1} \in TCR_SSR.ks{1}
        <=>
        TCR_SSR_Nin.k0{2} \in TCR_SSR_Nin.ks{2}).
+ by move=> O Oll; move: (A_pick_ll O Oll).
+ proc.
  case (k{2} = TCR_SSR_Nin.k0{2}).
  - wp; skip => />; smt(mem_rcons).
  by wp; skip => />.
+ move=> &2 k0in.
  proc.
  wp; skip => />; smt(mem_rcons).
+ move=> &1.
  proc.
  by wp; skip => />; smt(mem_rcons).
+ by skip => /> /#.
case (TCR_SSR_Nin.k0{2} \in TCR_SSR_Nin.ks{2}).
+ conseq (: _ ==> true); 1: by smt().
  call{1} (: true ==> true); 2: call{2} (: true ==> true).
  - apply (A_find_ll TCR_SSR.O_TCR_SSR_Find).
    by proc; wp.     
  - apply (A_find_ll TCR_SSR_Nin.O_TCR_SSR_Find).
    by proc; wp.
  by wp; skip.
call (: ={k0, gk, g}(TCR_SSR, TCR_SSR_Nin)).
+ proc.
  by wp; skip.
by wp; skip => /> /#.
qed.

local module TCR_Rep = {
  var k0 : key
  var x0 : input
  var y0 : output
  var ks : key list
  var gk : input -> output
  var g : key -> input -> output
  
  module O_TCR_Rep_Pick : Oracle_t = {
    proc get(k : key, x : input) : output = {
      var b : bool;
      var y : output;
      
      ks <- rcons ks k;
      
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
    
    BFOF.init();
    
    ks <- [];
    
    k0 <$ dkey;
    y0 <$ doutput;
    
    gk <$ MUFF_In.dfun (fun _ => doutput \ (pred1 y0));    
    g <$ dfc;
    
    x0 <@ A(O_TCR_Rep_Pick).pick();
        
    x' <@ A(O_TCR_Rep_Find).find(k0);
    
    y' <@ O_TCR_Rep_Find.get(k0, x');
    
    return x' <> x0 /\ y' = y0;
  }
}.


local lemma TCRSPRNin_Implies_TCRRep &m :
  Pr[TCR_SSR_Nin.main() @ &m : res /\ ! (TCR_SSR_Nin.k0 \in TCR_SSR_Nin.ks)]
  <=
  Pr[TCR_Rep.main() @ &m : res].
proof.
byequiv=> //.
proc; inline *.
swap{2} [2..3] -1.
swap{1} [4..5] -1; swap{2} [6..7] -3; swap{2} 6 -1.
seq 4 4 : (   ={glob A} 
           /\ ={k0, ks, g}(TCR_SSR_Nin, TCR_Rep)
           /\ x{1} = TCR_Rep.x0{2}).
+ call (: ={ks, g}(TCR_SSR_Nin, TCR_Rep)); 1: by proc; wp.
  by rnd; wp; rnd; wp; skip.
wp => /=.
seq 1 3 : (   #pre 
           /\ (forall (x : input),
                 TCR_SSR_Nin.gk{1} x
                 =
                 if !BFOF.f{2} x /\ x <> TCR_Rep.x0{2} 
                 then TCR_Rep.gk{2} x
                 else TCR_Rep.y0{2})).
conseq (: _ 
          ==> 
          (forall (x : input),
             TCR_SSR_Nin.gk{1} x
             =
             if !BFOF.f{2} x /\ x <> TCR_Rep.x0{2} 
             then TCR_Rep.gk{2} x
             else TCR_Rep.y0{2})) => //.
+ transitivity{1} {TCR_SSR_Nin.gk <@ LR.LambdaRepro.left();}
                  (true ==> ={TCR_SSR_Nin.gk})
                  (x{1} = TCR_Rep.x0{2} 
                   ==>
                   (forall (x : input),
                     TCR_SSR_Nin.gk{1} x 
                     =
                     if !BFOF.f{2} x /\ x <> TCR_Rep.x0{2} 
                     then TCR_Rep.gk{2} x
                     else TCR_Rep.y0{2})); 1,2: by smt().
  - inline *.
    by wp; rnd.
  transitivity{1} {TCR_SSR_Nin.gk <@ LR.LambdaRepro.right(x);}
                  (true ==> ={TCR_SSR_Nin.gk})
                  (x{1} = TCR_Rep.x0{2} 
                   ==> 
                   (forall (x : input),
                     TCR_SSR_Nin.gk{1} x 
                     =
                     if !BFOF.f{2} x /\ x <> TCR_Rep.x0{2} 
                     then TCR_Rep.gk{2} x
                     else TCR_Rep.y0{2})); 1,2: by smt().
  - by call LR.main_theorem.
  inline *.
  by wp; rnd; rnd; rnd; wp; skip.
call (:   ={k0, ks, g}(TCR_SSR_Nin, TCR_Rep)
       /\ (forall (x : input),
             TCR_SSR_Nin.gk{1} x 
             =
             if !BFOF.f{2} x /\ x <> TCR_Rep.x0{2} 
             then TCR_Rep.gk{2} x
             else TCR_Rep.y0{2})).
+ proc; inline *.
  by wp; skip => /> /#.
by wp; skip => /> /#. 
qed.


local lemma TCRRepNin_Implies_BFFind &m :
  Pr[TCR_Rep.main() @ &m : res]
  <=
  Pr[BF_Find(R_BFFind_TCR(A), BFOF).main() @ &m: res].
proof.
byequiv=> //.
proc; inline *.
wp => /=.
call (:   ={BFOF.f}
       /\ ={k0, x0, y0, g}(TCR_Rep, R_BFFind_TCR)
       /\ TCR_Rep.gk{1} = R_BFFind_TCR.f{2}). 
+ proc; inline *.
  by wp; skip.
call (: ={g}(TCR_Rep, R_BFFind_TCR)).
+ proc.
  by wp; skip.
do 4! rnd; wp; rnd; skip => /> f ? ? ? y ? gk gkin ? ? ? r ?.
apply contraLR => -> /=.
by move/dfun_supp /(_ r) /supp_dexcepted: gkin.
qed.

local lemma TCR_Implies_BFDistinguish_A &m:
  Pr[KHFO_TCR.TCR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(true) @ &m : res] |
  +
  Pr[TCR_SSR.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)].
proof.
apply (StdOrder.RealOrder.ler_trans 
          (Pr[BF_Find(R_BFFind_TCR(A), BFOF).main() @ &m : res] +
           Pr[TCR_SSR.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)])); last first.
+ by rewrite (Find_Implies_Distinguish &m (R_BFFind_TCR(A))).
rewrite EqPr_TCR_TCRSSR Pr[mu_split (! TCR_SSR.k0 \in TCR_SSR.ks)] /= StdOrder.RealOrder.ler_add.
+ rewrite EqPr_TCRSSR_TCRSSRNin (StdOrder.RealOrder.ler_trans Pr[TCR_Rep.main() @ &m : res]).
  - by apply TCRSPRNin_Implies_TCRRep.
  by apply TCRRepNin_Implies_BFFind.
by apply LePr_TCRSSR_In.
qed.


(* Query counting *)
declare op q : { int | 0 <= q } as ge0_q.

declare axiom A_pick_qs (O <: Oracle_t{-A}) (n : int) :
  hoare[A(Counting_O(O)).pick : Counting_O.ctr = n ==> Counting_O.ctr <= n + q].


local module TCR_SSR_C = {
  import var TCR_SSR   
 
  module O_TCR_SSR_C_Pick : Oracle_t = {
    proc get(k : key, x : input) = {
      var y : output;
      
      ks <- if size ks < q then rcons ks k else ks;
      
      if (k = k0) { 
        y <- gk x;
      } else { 
        y <- g k x;
      }
      
      return y;
    }
  }
  
  module O_TCR_SSR_C_Find : Oracle_t = TCR_SSR.O_TCR_SSR_Find
   
  proc main() : bool = {
    var x, x' : input;
    var y, y' : output;
    
    Counting_O.ctr <- 0;
    ks <- [];
    
    k0 <$ dkey;
    
    gk <$ dfcs;  
    g <$ dfc;
    
    x <@ A(Counting_O(O_TCR_SSR_C_Pick)).pick();
    y <@ O_TCR_SSR_C_Find.get(k0, x);
    
    x' <@ A(O_TCR_SSR_C_Find).find(k0);
    y' <@ O_TCR_SSR_C_Find.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.

(* 
  The following only works due to the fact that O_TCR_SSR_C_Pick still returns 
  the same values after q queries have been issued (as it returns before q queries are issued). 
  I want this to be cleaner:
  I want O_TCR_SSR_C_Pick to simply return an error/witness whenever the size of the
  list of keys (ks) has reached q (i.e., q queries have been issued).
  The following lemma should then still hold simply because, by assumption, it should 
  be impossible for the size of ks to already be q in a query, as the adversary 
  is assumed to not query more than q times (Counting_O.ctr <= q, and size ks is invariably
  the same as Counting_O.ctr up until reaching q).
  However, I cannot get this to work.
*)
local lemma EqPr_TCRSSR_TCRSSRC &m:
  Pr[TCR_SSR.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)]
  =
  Pr[TCR_SSR_C.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)].
proof.
(*
rewrite Pr[mu_split (size TCR_SSR.ks <= q)] eq_sym Pr[mu_split (Counting_O.ctr <= q)] eq_sym.
congr. admit.
rewrite 2!lezNgt /=.
byequiv=> //=.
proc; inline *.
seq 4 5 : (   ={glob A, TCR_SSR.k0, TCR_SSR.ks, TCR_SSR.gk, TCR_SSR.g}
           /\ TCR_SSR.ks{1} = []
           /\ Counting_O.ctr{2} = 0); 1: by auto.
wp => /=.
call (: true).

           seq 1 1 : (   ={glob A, TCR_SSR.k0, TCR_SSR.gk, TCR_SSR.g}
           /\ TCR_SSR.ks{1} = []
           /\ Counting_O.ctr{2} = 0
           rewrite eq_sym Pr[mu_split (Counting_O.ctr <= q)] eq_sym.
*)
rewrite eq_sym Pr[mu_split (Counting_O.ctr <= q)] eq_sym.
rewrite -(StdOrder.RealOrder.Domain.addr0 Pr[TCR_SSR.main() @ &m : TCR_SSR.k0 \in TCR_SSR.ks]).
congr; last first.
+ byphoare => //.
  hoare.
  conseq (: _ ==> Counting_O.ctr <= q); 1: by smt().
  proc; inline *.
  wp.
  call (: true); 1: by proc; wp; skip.
  wp.
  call (A_pick_qs TCR_SSR_C.O_TCR_SSR_C_Pick 0).
  by do 3! rnd; wp; skip. 
byequiv => //.
proc; inline *.
wp => /=.
call{1} (: true ==> true); 2: call{2} (: true ==> true).
+ apply (A_find_ll TCR_SSR.O_TCR_SSR_Find).
  by proc; wp.     
+ apply (A_find_ll TCR_SSR_C.O_TCR_SSR_C_Find).
  by proc; wp.
wp => /=.
call (:   ={glob A, TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}
       /\ Counting_O.ctr{2} = 0
       /\ size TCR_SSR.ks{2} = 0
       ==>
          ={TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g} 
       /\ Counting_O.ctr{2} <= q
       /\ (Counting_O.ctr{2} <= q => 
             ={TCR_SSR.ks} /\
             Counting_O.ctr{2} = size TCR_SSR.ks{2})).
+ conseq (:    ={glob A, TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}
            /\ Counting_O.ctr{2} = 0 /\ size TCR_SSR.ks{2} = 0
            ==>
               ={TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g}
            /\ (Counting_O.ctr{2} <= q => 
                   size TCR_SSR.ks{2} = Counting_O.ctr{2}
                /\ ={TCR_SSR.ks})) 
         (: true ==> true)
         (A_pick_qs TCR_SSR_C.O_TCR_SSR_C_Pick 0) => //. smt().
  proc (={TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g}
            /\ (Counting_O.ctr{2} <= q => 
                   size TCR_SSR.ks{2} = Counting_O.ctr{2}
                /\ ={TCR_SSR.ks})).
  smt().
  smt().
  proc.
  inline *.
  wp. skip => />. progress. smt(size_rcons).
         smt(size_rcons). smt(size_rcons). smt(size_rcons). 
by rnd; rnd; wp; rnd; wp; skip => />. 
qed.

(*
local lemma EqPr_TCRSSR_TCRSSRC &m:
  Pr[TCR_SSR.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)]
  =
  Pr[TCR_SSR_C.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)].
proof.
byequiv => //.
proc; inline *.
seq 5 6 : (   ={glob A, TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}); last first.
+ by conseq (: _ ==> true) => //; sim.
call (: ={TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}).
+ proc; inline *.
  by wp; skip.
(*
call (:   ={glob A, TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}
       /\ Counting_O.ctr{2} = 0
       ==>
          ={glob A, TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks} 
       /\ Counting_O.ctr{2} <= q).
+ conseq (: ={glob A, TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}
            ==>
            ={glob A, TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}) 
         (: true ==> true)
         (A_pick_qs TCR_SSR.O_TCR_SSR_Pick 0) => //.
  proc (={TCR_SSR.gk, TCR_SSR.k0, TCR_SSR.g, TCR_SSR.ks}) => //.
  proc; inline *.
  by wp; skip.
*)
by rnd; rnd; wp; rnd; wp; skip.
qed.
*)


(* Check LeakyEager/SuperEager; fel doesn't work *)
local lemma Bound_TCRSSRC &m:
 Pr[TCR_SSR_C.main() @ &m : (TCR_SSR.k0 \in TCR_SSR.ks)]
 <=
 q%r * mu1 witness dkey.
proof.
print TCR_SSR_C.
fel 3
    (size TCR_SSR.ks) 
    (fun (i : int) => mu1 witness dkey) 
    q 
    (TCR_SSR.k0 \in TCR_SSR.ks)
    [TCR_SSR_C.O_TCR_SSR_C_Pick.get : (size TCR_SSR.ks < q)]
    (size TCR_SSR.ks <= q).
by rewrite (: q%r = (q - 0)%r) 1:// StdBigop.Bigreal.sumri_const 1:ge0_q.
smt().
rnd; wp; skip => />. by rewrite ge0_q.
proc.
(* Move sampling to oracle procedure? *) 
admit.
move=> c.
proc. 
wp; skip => />.  smt(size_rcons).
move=> b c.
proc. by wp; skip => />.
qed.

local lemma TCR_Implies_BFDistinguish &m:
  Pr[KHFO_TCR.TCR(A, KHFO.O_Default).main() @ &m : res]
  <=
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(R_BFFind_TCR(A)), BFOD).main(true) @ &m : res] |
  +
  q%r * mu1 witness dkey.
proof.
move: (TCR_Implies_BFDistinguish_A &m); rewrite EqPr_TCRSSR_TCRSSRC.
by move: (Bound_TCRSSRC &m) => /#.
qed.
end section.
*)

(*
section.
(* 
  Idea for doing this with Reprogramming.eca:
  - Locally clone Reprogramming.eca and use ERO obtained from there
  - Prove that sampling from df is equivalent to a while loop over the key space which
    in each iteration samples a function of type input -> output from dkfs
  - The above allows to jump from original game to a game that uses ERO (which first
    initializes via a while loop over the key space and then is called in each query
    to the TCR oracle instead of simply computing g)
  - Prove equivalence of this game to one that sets the k0-th function to a reprogrammed one
    to the one using the BFOF.f and x0 to determine the image (so after pick has returned, before that just answer queries with the regular function). Do this reprogramming using Wrapped_Oracle(MCO).set.
  - The reduction then does the same as the latter game and calls repro in its (main) distinguish function (which will reprogram only if we are in the "true" case of the reprogramming game; if we are in the "false" case, no reprogramming will occur and hence the simulated function will match the former game's) and o to answer queries.
*)

declare module A <: Adv_TCR {-KHFO.O_Default, -BFOF, -BFOD, -R_BFFind_TCR, -Counting_O}.

declare axiom A_pick_ll (O <: Oracle_t{-A}):
  islossless O.get => islossless A(O).pick.

declare axiom A_find_ll (O <: Oracle_t{-A}):
  islossless O.get => islossless A(O).find.


local clone import DFun as DF with
  type in_t <- key,
  type out_t <- input -> output,
    op dout <- dfcs,
    
  theory FT_In <- FinKey
  
  proof *.
  realize dout_ll by exact: dfcs_ll.

local clone import Reprogramming as Repro with
  type in_t <- key,
  type out_t <- input -> output,
    op dout <- dfcs,
    
  theory FT_In <- FinKey
  
  proof *.
  realize dout_ll by exact: dfcs_ll.

import LE.

require import SmtMap.

local module TCR_Fmap_Rep = {
  module O_TCR_Fmap_Rep : Oracle_t = {
    var m : (key, input -> output) fmap
    var g : key -> input -> output
    
    proc init() : unit = {
      var y : input -> output;
      var w : key list;
      var k : key;
      
      m <- empty;
      w <- FinKey.enum;
      while (w <> []){
        k <- head witness w;
        y <$ dfcs;
        m.[k] <- y;
        w <- behead w;
      }
      
      g <- fun (k : key) => oget m.[k];
    }
    
    proc get(k : key, x : input) : output = {
      return g k x;
    }
  }
  
  proc main() = {
    var k : key;
    var x, x' : input;
    var y, y' : output;
    
    BFOF.init();
    O_TCR_Fmap.init();
    
    x <@ A(O_TCR_Fmap).pick();
    
    k <$ dkey;
    
    O_TCR_Fmap_Rep <-
    
    y <@ O_TCR_Fmap.get(k, x);
        
    x' <@ A(O_TCR_Fmap).find(k);
    y' <@ O_TCR_Fmap.get(k, x');
    
    return x' <> x /\ y' = y;
  }
}.

local equiv Eqv_TCR_TCR_Fmap :
  KHFO_TCR.TCR(A, O_Default).main ~ TCR_Fmap.main :
    ={glob A} ==> ={res}.
proof.
proc.
inline *.
seq 1 4: (={glob A} /\ O_Default.f{1} = TCR_Fmap.O_TCR_Fmap.g{2}).
+ transitivity{1} {O_Default.f <$ dfc;}
                  (={glob A} ==> ={glob A} /\ ={O_Default.f})
                  (={glob A} ==> ={glob A} /\ O_Default.f{1} = TCR_Fmap.O_TCR_Fmap.g{2}); 1,2:  by smt().
  - by rnd; skip => /=; rewrite eq_df_dfc.
  transitivity{1} {O_Default.f <@ Direct.sample();}
                  (={glob A} ==> ={glob A} /\ ={O_Default.f})
                  (={glob A} ==> ={glob A} /\ O_Default.f{1} = TCR_Fmap.O_TCR_Fmap.g{2}); 1,2:  by smt().
  - inline *. 
    by wp; rnd; skip.
  wp.
  transitivity{2} {TCR_Fmap.O_TCR_Fmap.m <@ Loop_Fmap_Head.sample();}
                  (={glob A} ==> ={glob A} /\ O_Default.f{1} = fun (k' : key) => oget TCR_Fmap.O_TCR_Fmap.m{2}.[k'])
                  (={glob A} ==> ={glob A} /\ ={TCR_Fmap.O_TCR_Fmap.m}); 1,2: by smt().
  - symmetry.
    conseq (: ={glob A} 
              ==> 
                 ={glob A} 
              /\ (fun (k' : key) => oget TCR_Fmap.O_TCR_Fmap.m{1}.[k']) = O_Default.f{2}) => //.
    call Eqv_Loop_Fmap_Head_Direct_Map.
    by skip.
  inline *.
  by wp; swap{1} 1 1; sim.
wp.
call (: O_Default.f{1} = TCR_Fmap.O_TCR_Fmap.g{2}).
+ by proc.
wp; rnd.
call (: O_Default.f{1} = TCR_Fmap.O_TCR_Fmap.g{2}).
+ by proc.
by skip.
qed.


local module TCR_ERO = {
  module O_TCR_ERO : Oracle_r = {
    var m : (key, input -> output) fmap
    var g : key -> input -> output
    
    proc init() : unit = {
      var y : input -> output;
      var w : key list;
      var k : key;
      
      m <- empty;
      w <- FinKey.enum;
      while (w <> []){
        k <- head witness w;
        y <$ dfcs;
        m.[k] <- y;
        w <- behead w;
      }
      
      g <- fun (k : key) => oget m.[k];
    }
    
    proc get(k : key, x : input) : output = {
      return g k x;
    }
  }
  
  proc main() = {
    var k : key;
    var x, x' : input;
    var y, y' : output;
    
    O_TCR_Fmap.init();
    
    x <@ A(O_TCR_Fmap).pick();
    
    k <$ dkey;
    
    y <@ O_TCR_Fmap.get(k, x);
        
    x' <@ A(O_TCR_Fmap).find(k);
    y' <@ O_TCR_Fmap.get(k, x');
    
    return x' <> x /\ y' = y;
  }
}.

local module TCR_ERO_Rep = {
  var k0 : key
  
  module O_TCR_ERO : Oracle_t = {
    var g : key -> input -> output
    
    proc init() : unit = {
      g <$ dfc;
    }
    
    proc get(k : key, x : input) : output = {
      return g k x;
    }
  }
  
  proc main() = {
    var x, x' : input;
    var y, y' : output;
    
    O_TCR_ERO.init();
    
    k0 <$ dkey;
    
    x <@ A(O_TCR_ERO).pick();
    y <@ O_TCR_ERO.get(k0, x);
        
    x' <@ A(O_TCR_ERO).find(k0);
    y' <@ O_TCR_ERO.get(k0, x');
    
    return x' <> x /\ y' = y;
  }
}.





end section.
*)
end section.
end TCRBound.
