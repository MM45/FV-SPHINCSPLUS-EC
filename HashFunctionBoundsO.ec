require import AllCore List Distr FinType Dexcepted.
require import FunSamplingLib.
require KeyedHashFunctionsO.


abstract theory BooleanFunctions.

type in_t.
type out_t.

clone import FinType as FinIn with
  type t <- in_t.

clone import FinType as FinOut with
  type t <- out_t.

axiom gt1_cardout: 1 < FinOut.card.

clone import LambdaReprogram as LR with
  type X <= in_t,
  type Y <= out_t,
  
  theory MUFF.FinT <= FinIn,
  theory MFY.Support <= FinOut
  
  proof *.
  realize Ynontriv by exact: gt1_cardout.

module type BFOFi_t = {
   proc init() : unit
   proc query(x : in_t) : bool
}.

module type BFOF_t = {
   include BFOFi_t [-init]
}.

module type Adv_BFFind(O : BFOF_t) = {
  proc find() : in_t
}.

module BF_Find(A : Adv_BFFind, O : BFOFi_t) = {
  proc main() = {
    var x : in_t;
    var b : bool;
    
    O.init();
    
    x <@ A(O).find();
    
    b <@ O.query(x);
    
    return b;
  } 
}.


module type BFODi_t = {
   proc init(b : bool) : unit
   proc query(x : in_t) : bool
}.

module type BFOD_t = {
   include BFODi_t [-init]
}.

module type Adv_BFDistinguish(O : BFOD_t) = {
  proc distinguish() : bool
}.

module BF_Distinguish(A : Adv_BFDistinguish, O : BFODi_t) = {
  proc main(b : bool) = {
    var b' : bool;
    
    O.init(b);
    
    b' <@ A(O).distinguish();
    
    return b';
  }
}.


module BFOF : BFOFi_t = {
  var f : in_t -> bool
  
  proc init() = {
    f <$ dboolf;
  }
  
  proc query(x : in_t) : bool = {
    return f x;
  }
}.

module BFOD : BFODi_t = {
  var f : in_t -> bool
  
  proc init(b : bool) = {
    if (b) {
      f <$ dboolf;
    } else {
      f <- fun (x : in_t) => false;
    }
  }
  
  proc query(x : in_t) : bool = {
    return f x;
  }
}.


module (R_BFDistinguish_BFFind (A : Adv_BFFind) : Adv_BFDistinguish) (O : BFOD_t) = {
  proc distinguish() : bool = {
    var x : in_t;
    var b : bool;
    
    x <@ A(O).find();
    
    b <@ O.query(x);
    
    return b;
  }
}.


equiv Equiv_Find_DistinguishT (A <: Adv_BFFind {-BFOF, -BFOD}) :
  BF_Find(A, BFOF).main ~ BF_Distinguish(R_BFDistinguish_BFFind(A), BFOD).main : 
    ={glob A} /\ b{2} ==> ={res}.
proof.
proc; inline *.
rcondt{2} 2; 1: by auto.
wp; call (: ={f}(BFOF, BFOD)); 1: by proc.
by rnd; wp; skip.
qed.

lemma Find_Implies_Distinguish &m (A <: Adv_BFFind {-BFOF, -BFOD}) :
  Pr[BF_Find(A, BFOF).main() @ &m : res]
  =
  `| Pr[BF_Distinguish(R_BFDistinguish_BFFind(A), BFOD).main(false) @ &m : res] - 
     Pr[BF_Distinguish(R_BFDistinguish_BFFind(A), BFOD).main(true) @ &m : res] |.
proof.
have -> /=: Pr[BF_Distinguish(R_BFDistinguish_BFFind(A), BFOD).main(false) @ &m : res] = 0%r.
+ byphoare (: !b ==> _) => //.
  hoare.
  proc; inline *.
  rcondf 2; 1: by wp.
  wp; call (: true) => //.
  by wp.
rewrite StdOrder.RealOrder.normrN StdOrder.RealOrder.ger0_norm 1:Pr[mu_ge0] //.
by byequiv (Equiv_Find_DistinguishT A).
qed.

end BooleanFunctions.


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
  type t2 <= input,
  
  theory FT1 <= FinKey,
  theory FT2 <= FinIn
  
  proof *.
  
clone import FinType as FinOut with
  type t <= output.

axiom gt1_cardout : 1 < FinOut.card.

op [lossless full uniform] dkey : key distr.
op [lossless full uniform] dinput : input distr.

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

lemma eq_df_df : df = df.
proof. by rewrite &(eq_funi_ll) 1:df_funi 1:df_ll 1:df_funi df_ll. qed. 

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

lemma dmap_df'_eq (k : key) :
  dmap df' (fun f => f k) = dfun (fun (x : input) => doutput).
proof. 
rewrite dfun_projE /= eq_sym -{1}(dscalar1 (dfun (fun (_ : input) => doutput))) -/df'.
by congr; rewrite df'_ll is_losslessP 1:dfun_ll //= dunifin_ll.
qed.


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


section.

declare module A <: Adv_SPR.

local module O_NK : Oracle_t = {
  var f : input -> output
  
  proc init(f_init : input -> output) = {
    f <- f_init;
  }
  
  proc get(x : input) : output = {
    return f x;
  }
}.


local module R_SPR_NK = {
  proc find(x : input) : input = {
    var k : key;
    var x' : input;
    
    k <$ dkey;
    
    x' <@ A(O_NK).find(k, x);
    
    return x';
  }
}.

 
(* SPR game *)
local module SPR_NK = {
  proc main() : bool  = {
    var f : input -> output;
    var x, x' : input;

    (* Sample function f and key k *)
    f <$ dfun (fun (x : input) => doutput);

    (* Initialize oracle with f and k *)
    O_NK.init(f);

    (* Sample input x *)
    x <$ dinput;

    (* Ask adversary to find a second preimage x' of x w.r.t. k (i.e., under f k) *)
    x' <@ R_SPR_NK.find(x);

    (* 
      Success iff
      (1) "x <> x'": x does not equal x', and
      (2) "f k x = f k x'": f k maps x to the same element as it maps x'
    *)
    return x <> x' /\ f x = f x';
  }
}.

equiv Equiv_SPR_SPRNK :
  SPR(A, O_Default).main ~ SPR_NK.main : ={glob A} ==> ={res}. 
proof.
proc; inline *.
  
module (R_BFFind_SPR (A : Adv_SPR) : Adv_BFFind) (O : BFOF_t) = {
  var x0 : input
  var y0 : output
  var f : input -> output
  
  module O_R_BFFind_SPR : Oracle = {
    proc get(x : input) : output = {
      var b : bool;
      
      b <@ O.query(x);
      
      return (if x = x0 \/ b then y0 else f k x);
    }
  }
  
  proc find() : input = {
    var x : input;
    var k : key;
    
    x0 <$ dinput;
    y0 <$ doutput;
    
    f <$ dfun (fun (k : key, x : input) => doutput \ (pred1 y0));
    
    f <$ dfun (fun (k : key) => dfun (fun (x : input) => doutput \ (pred1 y0)));
    k <$ dkey;
    
    x <@ A(O_R_BFFind_SPR).find(k, x0);
    
    return x;
  }
}.


module (R_BFFind_SPR (A : Adv_SPR) : Adv_BFFind) (O : BFOF_t) = {
  var x0 : input
  var y0 : output
  var k : key
  var f : key -> input -> output
  
  module O_R_BFFind_SPR : Oracle = {
    proc get(x : input) : output = {
      var b : bool;
      
      b <@ O.query(x);
      
      return (if x = x0 \/ b then y0 else f k x);
    }
  }
  
  proc find() : input = {
    var x : input;
    var k : key;
    
    x0 <$ dinput;
    y0 <$ doutput;
    
    f <$ dfun (fun (k : key, x : input) => doutput \ (pred1 y0));
    
    f <$ dfun (fun (k : key) => dfun (fun (x : input) => doutput \ (pred1 y0)));
    k <$ dkey;
    
    x <@ A(O_R_BFFind_SPR).find(k, x0);
    
    return x;
  }
}.

end SPRBound.
