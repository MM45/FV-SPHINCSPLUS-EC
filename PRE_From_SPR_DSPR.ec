require import AllCore List Distr.
require import FinType.

require KeyedHashFunctions.

op max (x y : real) =
  if x < y then y else x.
  
lemma max_gel (x y : real) :
  x <= max x y.
proof. by case (x < y) => /#. qed.

lemma max_ger (x y : real) :
  y <= max x y.
proof. by case (x < y) => /#. qed.


type key.

type input.

clone import FinType as Input with
  type t <= input.

type output.


op f : key -> input -> output.


op [lossless] dkey : key distr.
op [lossless full uniform] dinput : input distr.


clone import KeyedHashFunctions as F with
  type key_t <- key,
  type in_t <- input,
  type out_t <- output,
  
  op f <- f
  
  proof *.

clone import PRE as F_PRE with
  op dkey <- dkey,
  op din <- dinput
  
  proof *.
  realize dkey_ll by exact: dkey_ll.
  realize din_ll by exact: dinput_ll.

clone import SPR as F_SPR with
  op dkey <- dkey,
  op din <- dinput
  
  proof *.
  realize dkey_ll by exact: dkey_ll.
  realize din_ll by exact: dinput_ll.

clone import DSPR as F_DSPR with
  op dkey <- dkey,
  op din <- dinput
  
  proof *.
  realize dkey_ll by exact: dkey_ll.
  realize din_ll by exact: dinput_ll.
  

  
module R_SPR_PRE (A : Adv_PRE) : Adv_SPR  = {
  proc find(k : key, x : input) : input = {
    var x' : input;
    
    x' <@ A.find(k, f k x);
    
    return x';
  }
}.


module R_DSPR_PRE (A : Adv_PRE) : Adv_DSPR = {
  proc guess(k : key, x : input) : bool = {
    var x' : input;
    
    x' <@ A.find(k, f k x);
    
    return x' <> x;
  }
}.


section Proof_PRE_From_DSPR_SPR.

require import Finite.
require StdBigop StdOrder.
import RField MRat.
import StdBigop.Bigreal BRA.
import StdOrder.RealOrder.


local lemma mem_size_ge1 (s : 'a list) (x : 'a) :
  x \in s => 1 <= size s.
proof. elim: s => //; smt(size_ge0). qed.

local lemma mem_size_ge2 (s : 'a list) (x x' : 'a) :
  x \in s => x' \in s => x <> x' => 2 <= size s.
proof. elim: s => //; smt(size_ge0). qed.

local lemma uniq_size_ge2_mem (s : 'a list) :
  uniq s => 2 <= size s => 
    exists (x x' : 'a), x <> x' /\ x \in s /\ x' \in s.
proof. elim: s => // /#. qed.



local op is_pre_f (k : key) (y : output) : input -> bool = 
  fun (x : input) => f k x = y.
 
local op pre_f_l (k : key) (y : output) : input list =
  to_seq (is_pre_f k y).
  
local lemma is_finite_ispref (k : key) (y : output) : 
  is_finite (is_pre_f k y).
proof. by rewrite (finite_leq predT) 2:-/finite_type 2:is_finite. qed.

local lemma ltcard_szprefl (k : key) (y : output) :
  size (pre_f_l k y) <= card.
proof. by rewrite card_size_to_seq sub_size_to_seq 2:-/finite_type 2:is_finite. qed. 


local lemma rngprefl_image (k : key) (x : input) :
  1 <= size (pre_f_l k (f k x)) <= card.
proof.
split => [| _]; 2: by apply ltcard_szprefl.
apply (mem_size_ge1 _ x).
by rewrite mem_to_seq 1:is_finite_ispref.
qed.

local lemma eqv_spex_szprefl (k : key) (x : input) :
  spexists k x <=> 2 <= size (pre_f_l k (f k x)).
proof.
split=> [| @/pre_f_l ge2_szprefl]. 
+ elim => x' [neqx_xp eqfkx_fkxp].
  by apply (mem_size_ge2 _ x' x) => //; rewrite mem_to_seq 1:is_finite_ispref.
move: (uniq_to_seq (is_pre_f k (f k x)) (is_finite_ispref k (f k x))).
move/uniq_size_ge2_mem => /(_ ge2_szprefl) -[x' x''] [#] neqxp_xpp xpin xppin.
case (x' = x) => [eqx_xp | neqx_xp].
+ exists x''; split; 1: by rewrite -eqx_xp eq_sym. 
  by move: xppin; rewrite mem_to_seq 1:is_finite_ispref.
exists x'; rewrite neqx_xp /=. 
by move: xpin; rewrite mem_to_seq 1:is_finite_ispref.
qed.


declare module A <: Adv_PRE.
declare axiom A_find_ll : islossless A.find.


local module Si = {
  var x, x' : input
  
  proc main(i : int) : bool = {
    var k : key;
    var y : output;
    
    k <$ dkey;
    x <$ dinput;
    
    y <- f k x;
    
    x' <@ A.find(k, y);
    
    return size (pre_f_l k y) = i /\ f k x' = y;
  }
}.

local module Fi = {
  proc main(i : int) : bool = {
    var k : key;
    var x, x' : input;
    var y : output;
    
    k <$ dkey;
    x <$ dinput;
    
    y <- f k x;
    
    x' <@ A.find(k, y);
    
    return size (pre_f_l k y) = i /\ f k x' <> y;
  }
}.


local module PREg = {
  var k : key
  var y : output
  
  proc main() : bool = {
    var x : input;
    var x' : input;
    
    k <$ dkey;
    x <$ dinput;
    y <- f k x;
    x' <@ A.find(k, y);
    
    return f k x' = y;
  }
}.

local module SPRg = {
  var k : key
  var x, x' : input
  
  proc main() : bool = {
  
    k <$ dkey;
    x <$ dinput;
    
    x' <@ A.find(k, f k x);

    return x' <> x /\ f k x' = f k x;
  }
}.

local module DSPRg = {
  var k : key
  var x, x' : input
  
  proc main() : bool = {
    var b : bool;
      
    k <$ dkey;
    x <$ dinput;
    
    x' <@ A.find(k, f k x);
    
    b <- x' <> x;
      
    return spexists k x = b;
  }
}.

local module SPprobA = {
  var k : key
  var x, x' : input
  
  proc main() : bool = {
    k <$ dkey;
    x <$ dinput;
    
    x' <@ A.find(k, f k x);
    
    return spexists k x;    
  }
}.

local module Si_early_fail = {
  var x, x' : input

  proc sample(i : int, k : key) = {
    var xt : input;
    var y : output <- witness;
    var r : bool;
    
    xt <$ dinput;

    if (size (pre_f_l k (f k xt)) = i) {
      y <- f k xt;
      r <- true;
    } else {
      xt <- witness;
      y <- witness;
      r <- false;     
    }
    
    return (xt, y, r);
  }
  
  proc main(i : int) : bool = {
    var k : key;
    var y : output <- witness;
    var r : bool;

    k <$ dkey;
    
    (x, y, r) <@ sample(i, k);
      
    x' <@ A.find(k, y);
    
    return r /\ (f k x' = y);
  }
}.


local module Si_inverse_sample = {
  var x, x' : input

  proc sample(i : int, k : key) = {
    var xt : input;
    var y : output <- witness;
    var r : bool;
    
    y <$ dmap dinput (f k);

    if (size (pre_f_l k y) = i) {
      xt <$ drat (pre_f_l k y);
      r <- true;
    } else {
      xt <- witness;
      y <- witness;
      r <- false;     
    }
    
    return (xt, y, r);
  }

  proc main(i : int) : bool = {
    var k : key;
    var y : output <- witness;
    var r : bool <- false;

    k <$ dkey;
    
    (x, y, r) <@ sample(i, k);
    
    x' <@ A.find(k, y);
    
    return r /\ (f k x' = y);
  }
}.


local lemma pr_Si_Sief (j : int) &m:
  Pr[Si.main(j) @ &m : res /\ Si.x' <> Si.x]
  =
  Pr[Si_early_fail.main(j) @ &m : res /\ Si_early_fail.x' <> Si_early_fail.x].
proof.
byequiv (: _ ==> ={res} /\ (res{1} => ={x, x'}(Si, Si_early_fail))) => [| // | /#].
proc; inline *.
seq 3 8 : (   (r{2} => ={k, y} /\ ={x}(Si, Si_early_fail))
           /\ (r{2} <=> (size (pre_f_l k{1} y{1}) = i{1}))
           /\ ={glob A, i}).
+ by auto.
case (r{2}).
+ call (: true).
  by skip => />.
conseq (: size (pre_f_l k{1} y{1}) <> i{1} /\ !r{2}) => />.
call{1} A_find_ll; call{2} A_find_ll.
by skip.
qed.


(*
local proc op sief = Si_early_fail.sample.
*)
local lemma pr_Sief_Siis (j : int) &m:
  Pr[Si_early_fail.main(j) @ &m : res /\ Si_early_fail.x' <> Si_early_fail.x]
  =
  Pr[Si_inverse_sample.main(j) @ &m : res /\ Si_inverse_sample.x' <> Si_inverse_sample.x].
proof.
case (0 < j) => [gt0_j | /lezNgt le0_j]; last first.
+ have ->:
    Pr[Si_early_fail.main(j) @ &m : res /\ Si_early_fail.x' <> Si_early_fail.x] = 0%r.
  - byphoare (: arg <= 0 ==> _) => //=.
    hoare.
    proc; inline *.
    seq 6 : (i0 <= 0); first by auto.
    rcondf 1; 1: by skip; smt(rngprefl_image).
    sp; conseq (: _ ==> true) => />.
    by call (: true).
+ byphoare (: arg <= 0 ==> _) => //=.
  hoare.
  proc; inline *.
  rcondf 8.
  - rnd.
    wp.
    rnd.
    by wp; skip => />; smt(supp_dmap rngprefl_image).
  seq 10 : (!r0); first by auto. 
  sp; conseq (: _ ==> true) => />.
  by call (: true).
byequiv=> //=.
proc.
call (: true).
sp.
seq 1 1 : (#pre /\ ={i, k} /\ i{1} = j); first by auto.
call (: ={arg} /\ 0 < arg{1}.`1 ==> ={res}); last first.
+ by skip.
bypr (res{1}) (res{2}) => //=.
move=> &1 &2 -[x y r] -[eq_args gt0_i].
admit.
qed.


local lemma pr_cond_neqxxp_Si (i : int) &m:
  Pr[Si.main(i) @ &m : res /\ Si.x' <> Si.x]
  =
  (i%r - 1%r) / i%r * Pr[Si.main(i) @ &m : res].
proof.
admit.
qed.
  
local lemma pr_SPprob_bigSi &m: 
  Pr[SPprob.main() @ &m : res]
  =
  bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res]) 2 (card + 1)
  +
  bigi predT (fun (i : int) => Pr[Fi.main(i) @ &m : res]) 2 (card + 1).
proof.
rewrite (: Pr[SPprob.main() @ &m : res] = Pr[SPprobA.main() @ &m : res]).
+ byequiv=> //.
  proc.
  call{2} A_find_ll. 
  by sim. 
have ->:
  Pr[SPprobA.main() @ &m : res]
  =
  Pr[SPprobA.main() @ &m : 2 <= size (pre_f_l SPprobA.k (f SPprobA.k SPprobA.x)) <= card].
+ byequiv => //=. 
  proc.
  call (: true).
  rnd; rnd.
  skip => |> k kin x xin.
  split => [x' neqx_xp eqfkx_fkxp|].
  - split => [|_]; 2: by rewrite ltcard_szprefl.
    by rewrite -eqv_spex_szprefl; exists x'.
  by rewrite eqv_spex_szprefl.
suff:
  forall (i : int),
    0 <= i => 
      Pr[SPprobA.main() @ &m : 2 <= size (pre_f_l SPprobA.k (f SPprobA.k SPprobA.x)) <= i]
      =
      bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res]) 2 (i + 1)
      +
      bigi predT (fun (i : int) => Pr[Fi.main(i) @ &m : res]) 2 (i + 1).
+ by move=> /(_ card _); 1: smt(card_gt0). 
elim => [/= | i ge0_i ih].
+ rewrite range_geq // 2!big_nil /=.
  by byphoare (: true ==> false) => // /#.
case (i = 0) => [-> | neq0_i].
+ rewrite range_geq // 2!big_nil /=.
  by byphoare (: true ==> false) => // /#.
rewrite rangeSr 1:/# 2!big_rcons /predT /= -/predT.
rewrite Pr[mu_split (size (pre_f_l SPprobA.k (f SPprobA.k SPprobA.x)) <> i + 1)].
have <-:
  Pr[SPprobA.main() @ &m : 2 <= size (pre_f_l SPprobA.k (f SPprobA.k SPprobA.x)) <= i]
  =
  Pr[SPprobA.main() @ &m : 2 <= size (pre_f_l SPprobA.k (f SPprobA.k SPprobA.x)) <= i + 1 
                            /\ size (pre_f_l SPprobA.k (f SPprobA.k SPprobA.x)) <> i + 1].
+ byequiv (: _ ==> ={glob SPprobA}) => [ | // | /#].
  proc.
  call (: true).
  rnd; rnd.
  by skip.
rewrite ih; field; rewrite addrC /= addr_eq0 opprB /= addrC.
rewrite Pr[mu_split (f SPprobA.k SPprobA.x = f SPprobA.k SPprobA.x')].
congr.
+ byequiv => //=.
  proc.
  call (: true).
  wp; rnd; rnd.
  by skip => /> /#.
byequiv => //=.
proc.
call (: true).
wp; rnd; rnd.
by skip => /> /#.
qed.

local lemma pr_DSPR_bigSiFi &m :
  Pr[DSPR(R_DSPR_PRE(A)).main() @ &m : res]
  =
  Pr[Si.main(1) @ &m : res] 
  +
  bigi predT (fun (i : int) => (i%r - 1%r) / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1)
  +
  bigi predT (fun (i : int) => Pr[Fi.main(i) @ &m : res]) 2 (card + 1).
proof.
rewrite (: Pr[DSPR(R_DSPR_PRE(A)).main() @ &m : res] = Pr[DSPRg.main() @ &m : res]).
+ by byequiv=> //=; proc; inline *; sim.
rewrite Pr[mu_split (1 <= size (pre_f_l DSPRg.k (f DSPRg.k DSPRg.x)) <= card)].
rewrite -(addr0 (big _ _ _)) addrA -addrA (addrC 0%r) addrA; congr; last first.
+ byphoare (: _ ==> false) => //=.
  by rewrite rngprefl_image.
have prsp :
  forall (i : int), 0 <= i =>
    Pr[DSPRg.main() @ &m : res /\ 1 <= size (pre_f_l DSPRg.k (f DSPRg.k DSPRg.x)) <= i]
    =
    bigi predT (fun (j : int) => Pr[DSPRg.main() @ &m : res /\ size (pre_f_l DSPRg.k (f DSPRg.k DSPRg.x)) = j]) 1 (i + 1).
+ elim => [/= | i ge0_i ih].
  - rewrite range_geq // big_nil.
    by byphoare (: _ ==> false) => // /#.
  rewrite rangeSr 1:/# big_rcons /predT /= -/predT -ih.
  rewrite Pr[mu_split (size (pre_f_l DSPRg.k (f DSPRg.k DSPRg.x)) <> i + 1)]; congr.
  - by byequiv (: _ ==> ={res, glob DSPRg}); [sim | trivial | smt()].
  by byequiv (: _ ==> ={res, glob DSPRg}); [sim | trivial | smt()].
rewrite prsp 2:range_ltn; 1,2: smt(card_gt0).
rewrite big_cons /predT /= -/predT -addrA; congr.
+ byequiv => //=.
  proc.
  wp.
  call (: true).
  wp; rnd; rnd.
  by skip => />; smt(eqv_spex_szprefl).
rewrite -big_split /= &(eq_big_seq) => i /mem_range rng_i /=.
rewrite Pr[mu_split (f DSPRg.k DSPRg.x' =f DSPRg.k DSPRg.x)]; congr; last first.
+ byequiv => //=.
  proc.
  wp.
  call (: true).
  wp; rnd; rnd.
  by skip => />; smt(eqv_spex_szprefl).
rewrite -andbA mulrAC.
have ->:
  Pr[DSPRg.main() @ &m : res /\ size (pre_f_l DSPRg.k (f DSPRg.k DSPRg.x)) = i  
                             /\ f DSPRg.k DSPRg.x' = f DSPRg.k DSPRg.x]
  =
  Pr[Si.main(i) @ &m : res /\ Si.x' <> Si.x].
+ byequiv => //.
  proc.
  wp.
  call (: true).
  wp; rnd; rnd.
  by skip => />; smt(eqv_spex_szprefl).
by apply pr_cond_neqxxp_Si.
qed.


local lemma pr_PRE_bigSi &m :
  Pr[PRE(A).main() @ &m : res]
  =
  Pr[Si.main(1) @ &m : res]
  +
  bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res]) 2 (card + 1).
proof.
have ->: Pr[PRE(A).main() @ &m : res] = Pr[PREg.main() @ &m : res].
+ by byequiv=> //=; sim.
rewrite (: Pr[Si.main(1) @ &m : res] = (fun (i : int) => Pr[Si.main(i) @ &m : res]) 1) //.
rewrite -big_consT -range_ltn; 1: smt(card_gt0).
rewrite Pr[mu_split (1 <= size (pre_f_l PREg.k PREg.y) <= card)] -(addr0 (big _ _ _)).
congr; last first.
+ byphoare => //=.
  hoare.
  proc.
  call (: true).
  wp; rnd; rnd; skip => /> k kin x xin x'.
  by rewrite rngprefl_image.
suff:
  forall (i : int),
    0 <= i => 
      Pr[PREg.main() @ &m : res /\ 1 <= size (pre_f_l PREg.k PREg.y) <= i]
      =
      bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res]) 1 (i + 1).
+ by move => /(_ card); smt(size_ge0).
elim => /= [ | i ge0_i ih].
+ rewrite range_geq 1:// big_nil.
  by byphoare (: _ ==> false) => // /#.
rewrite (: i + 2 = i + 1 + 1) 1:// rangeSr 1:/# big_rcons /predT /= -/predT.
rewrite -ih Pr[mu_split (size (pre_f_l PREg.k PREg.y) = i + 1)] addrC.
congr; last first.
+ byequiv => //=.
  proc.
  call (: true).
  wp; rnd; rnd; skip => /> /#.
byequiv => //=.
proc.
call (: true).
by wp; rnd; rnd; skip => /> /#.
qed.

local lemma pr_DSPRSPprob_bigSi &m :
  Pr[DSPR(R_DSPR_PRE(A)).main() @ &m : res] - Pr[SPprob.main() @ &m : res]
  =
  Pr[Si.main(1) @ &m : res] 
  -
  bigi predT (fun (i : int) => 1%r / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1).
proof.
rewrite pr_DSPR_bigSiFi pr_SPprob_bigSi.
field; rewrite -big_split /= subr_eq0 &(eq_big_seq) => i /mem_range rng_i /=.
rewrite -mulrDl -{1}mul1r -mulrDl (: 1%r + (i%r - 1%r) = i%r) 1:/#.
by rewrite mulrC mulrA mulVf 1:/#.
qed.

local lemma pr_SPR_bigSi &m :
  Pr[SPR(R_SPR_PRE(A)).main() @ &m : res]
  =
  bigi predT (fun (i : int) => (i%r - 1%r) / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1).
proof.
rewrite (: Pr[SPR(R_SPR_PRE(A)).main() @ &m : res] = Pr[SPRg.main() @ &m : res]).
+ byequiv => //=. 
  proc; inline *.
  wp.
  call (: true). 
  wp; rnd; rnd.
  by skip => /> /#. 
have ->:
  Pr[SPRg.main() @ &m : res]
  =
  bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res /\ Si.x' <> Si.x]) 2 (card + 1).
+ rewrite Pr[mu_split (2 <= size (pre_f_l SPRg.k (f SPRg.k SPRg.x)) <= card)].
  rewrite -(addr0 (big _ _ _)); congr; last first.
  - byphoare => //.
    hoare.
    proc; inline *.
    wp.
    call (: true).
    wp; rnd; rnd.
    skip => /> k kin x xin x'.
    rewrite negb_and /= -implybE => [#] neqx_xp eqfkx_fkxp. 
    rewrite -eqv_spex_szprefl ltcard_szprefl /=.
    by exists x'.
  suff:
    forall (i : int),
      0 <= i => 
        Pr[SPRg.main() @ &m : res /\ 2 <= size (pre_f_l SPRg.k (f SPRg.k SPRg.x)) <= i]
        =
        bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res /\ Si.x' <> Si.x]) 2 (i + 1).
  - by move=> /(_ card _). 
  elim => [/= | i ge0_i ih]. 
  - rewrite range_geq // big_nil.
    by byphoare (: _ ==> false) => // /#.
  case (i = 0) => [-> | neq0_i].
  - rewrite range_geq // big_nil.
    by byphoare (: _ ==> false) => // /#.  
  rewrite rangeSr 1:/# big_rcons /predT /= -/predT.
  rewrite Pr[mu_split (size (pre_f_l SPRg.k (f SPRg.k SPRg.x)) <> i + 1)]; congr.
  + by rewrite -ih; byequiv (: _ ==> ={glob SPRg, res}); [sim | | smt()].
  byequiv => //=. 
  proc; inline *.
  wp.
  call (: true).
  wp; rnd; rnd.
  by skip => /> /#.
apply eq_big_seq => i /mem_range rng_i /=; rewrite mulrAC.
by apply pr_cond_neqxxp_Si.
qed.


lemma PRE_From_DSPR_SPR &m :
  Pr[PRE(A).main() @ &m : res] 
  <= 
  max 0%r (Pr[DSPR(R_DSPR_PRE(A)).main() @ &m : res] - Pr[SPprob.main() @ &m : res])
  +
  3%r * Pr[SPR(R_SPR_PRE(A)).main() @ &m : res].
proof.
apply (ler_trans 
        (Pr[DSPR(R_DSPR_PRE(A)).main() @ &m : res] - Pr[SPprob.main() @ &m : res] +
         3%r * Pr[SPR(R_SPR_PRE(A)).main() @ &m : res])); last first.
+ by apply ler_add; 1: rewrite max_ger. 
rewrite pr_PRE_bigSi pr_DSPRSPprob_bigSi pr_SPR_bigSi.
rewrite -addrA &(ler_add) 1:// addrC mulrC mulr_suml sumrB /=.
apply ler_sum_seq => i /mem_range rng_i _ /=.
rewrite mulrC 2!mulrA mulrDr /= divrr 1:/# /=.
rewrite mulrAC mulrDl /= 2!mulNr /= mulrC -mulrBr.
by rewrite &(ler_pemulr) 1:Pr[mu_ge0] // /#.
qed.

end section Proof_PRE_From_DSPR_SPR. 


(*
local module Sir = {
  var i : int
  
  proc main() : bool = {
    var b : bool;
        
    i <$ [1..card];
    
    b <@ Si.main(i);
    
    return b;
  }
}.

local lemma ubpr_Sir &m (j : int) :
  Pr[Sir.main() @ &m : res /\ 1 <= Sir.i < j]
  =
  bigi predT (fun (i : int) => Pr[Sir.main() @ &m : res /\ i = Sir.i]) 1 j.
proof.
have lt2_pr0 :
  forall (k : int), k < 2 => Pr[Sir.main() @ &m : res /\ 1 <= Sir.i < k] = 0%r.
+ move=> k lt2_k.
  byphoare (: _ ==> false) => [ | //= | /#].
  by hoare => /=.
case (j < 0) => [lt0_j | /lezNgt ge0_j].
+ by rewrite range_geq 1:/# big_nil lt2_pr0 1:/#.
elim: j ge0_j => [| j ge0_j ih].
+ by rewrite range_geq 1:/# big_nil lt2_pr0 1:/#.
case (j = 0) => [-> | neq0_j]; 1: by rewrite range_geq 1:/# big_nil lt2_pr0 1:/#.
rewrite rangeSr 1:/# big_rcons /predT /= -/predT.
rewrite Pr[mu_split Sir.i < j]; congr; last first.
+ byequiv (: ={glob A} ==> ={res, Sir.i}) => [| // | /#]. 
  by sim.
have ->:
  Pr[Sir.main() @ &m : (res /\ 1 <= Sir.i < j + 1) /\ Sir.i < j]
  =
  Pr[Sir.main() @ &m : res /\ 1 <= Sir.i < j].
+ byequiv (: ={glob A} ==> ={res, Sir.i}) => [| // | /#]. 
  by sim.
by rewrite ih.
qed.

local lemma ppr_Sir &m :
  Pr[Sir.main() @ &m : res]
  =
  bigi predT (fun (i : int) => Pr[Sir.main() @ &m : res /\ i = Sir.i]) 1 (card + 1).
proof.
rewrite Pr[mu_split (1 <= Sir.i < card + 1)] -(RField.addr0 (bigi _ _ _ _)) ubpr_Sir.
congr.
byphoare => //=.
hoare.
proc.
seq 1 : (1 <= Sir.i < card + 1).
- by rnd; skip => /> i /DInterval.supp_dinter /#.
inline *.
wp; call (: true).
wp; rnd; rnd.
by wp; skip => />.
qed.

local lemma pr_Sir_cBigSi &m :
  Pr[Sir.main() @ &m : res]
  =
  (1%r / card%r) * bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res]) 1 (card + 1).
proof.
rewrite ppr_Sir.
search (big _ _ _ * _).
rewrite RField.mulrC mulr_suml /= &(eq_big_seq) /= => i /mem_range rng_i.
pose pr := Pr[Si.main(i) @ &m : res]; pose cinv := inv card%r; rewrite RField.mulrC.
byphoare (: (glob A) = (glob A){m} ==> res /\ i = Sir.i) => //=.
proc.
seq 1 : (i = Sir.i) cinv pr _ 0%r ((glob A) = (glob A){m}).
+ by rnd.
+ rnd; skip => />.
  by rewrite (: ((=) i) = pred1 i) 2:DInterval.dinter1E /#.
+ conseq />.
  call (: (glob A) = (glob A){m} /\ arg = i ==> res) => //= @/pr.
  bypr => /> &m0 eq_glA ->.
  byequiv => //=.
  proc.
  call (: true).
  by wp; rnd; rnd; skip.
+ hoare.
  by conseq (: _ ==> i <> Sir.i) => />.
by rewrite RField.mulrC.
qed.
*)

(*
rewrite (: Pr[SPprob.main() @ &m : res] = Pr[SPprobA.main() @ &m : res]).
+ byequiv => //.
  proc.
  call{2} A_find_ll.
  by sim.
rewrite (: Pr[PRE(A).main() @ &m : res] = Pr[PREg.main() @ &m : res]).
+ by byequiv=> //; sim.  
rewrite pr_PREg_BigSi range_ltn; 1: smt(card_gt0).
rewrite big_cons /predT /= -/predT.
apply (StdOrder.RealOrder.ler_trans 
        (Pr[Si.main(1) @ &m : res] + 
         bigi predT (fun (i : int) => (3%r*i%r - 4%r) / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1))).
+ apply StdOrder.RealOrder.ler_add => //.
  apply ler_sum_seq => i /mem_range rng_i _ /=.
  rewrite RField.mulrAC RField.mulrC StdOrder.RealOrder.ler_pemulr 1:Pr[mu_ge0] //.
  by rewrite StdOrder.RealOrder.ler_pdivl_mulr /= /#.
pose bigsi := big _ _ _.
have ->:
  bigsi
  =
  bigi predT (fun (i : int) => 
    (3%r * i%r - 3%r) / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1)
  -
  bigi predT (fun (i : int) => 
    1%r / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1).
+ by rewrite /bigsi sumrB /= /#. 
rewrite RField.addrA RField.addrAC StdOrder.RealOrder.ler_add.

-big_split /= &(eq_big_seq) => i /mem_range rng_i /=.
  search (_ * _ + _ * _)%Real. print RField.
  field. smt.
   => /#.
  smt(RField.mulrDr).
  
  print 
  search (big _ _ _ = big _ _ _)%Real.
    search (_ + _ <= _ + _)%Real.
rewrite ler_trans ()
1:/#. search range (::).

Pr[mu_split ]
qed.
*)
