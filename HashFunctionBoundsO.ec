require import AllCore List Distr FinType Dexcepted DMap.
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
call (: ={f}(KHFO.O_Default, KHFO'.O_Default)); 1: by proc.
rnd; wp; rnd; rnd; skip => />.
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
    
    return x <> x' /\ f k x = f k x';
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

    return x <> x' /\ f (k, x) = f (k, x');
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
    
    return x <> x' /\ f (k, x) = f (k, x');
  }
}.

local equiv Equiv_KHFO'_SPR_SPR_DMS_Main :
  KHFO'_SPR.SPR(A, O_Default).main ~ SPR_DMS.main : ={glob A} ==> ={res}. 
proof.
proc; inline *.
call (: forall (k : key) (x : input),
          O_Default.f{1} k x = O_Default_Uncurry.f{2} (k, x)).
by proc; skip => /> /#.
by rnd; wp; rnd; rnd; skip.
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

    return x <> x' /\ f (k, x) = f (k, x');
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
