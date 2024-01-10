require import AllCore List Distr.
require import FinType Finite. 
require StdBigop StdOrder DMap.
import StdBigop.Bigreal BRA.
import StdOrder.RealOrder.
import RField.

require TweakableHashFunctions.

type df.

type pp.
type tw.
type input.

clone import FinType as Input with
  type t <= input.

type output.

op f : pp -> tw -> input -> output.

op gd : input -> df.

op fc : df -> pp -> tw -> input -> output.
axiom in_collection: exists (df : df), fc df = f.


op [lossless] dpp : pp distr.
op [lossless full uniform] dinput : input distr.

const t : { int | 0 <= t } as ge0_t.

clone import TweakableHashFunctions as F with
  type pp_t <- pp,
  type tw_t <- tw,
  type in_t <- input,
  type out_t <- output,
  
  op f <- f,
  
  op dpp <- dpp
  
  proof *.
  realize dpp_ll by exact: dpp_ll.

clone import F.Collection as FC with
  type diff_t <- df,
  
  op get_diff <- gd,
  op fc <- fc
  
  proof *.
  realize in_collection by exact: in_collection.

clone import FC.SMDTOpenPREC as FC_OpenPRE with
  op t_smdtopenpre <- t,
  
  op din <- dinput
  
  proof *.
  realize ge0_tsmdtopenpre by exact: ge0_t.
  realize din_ll by exact: dinput_ll.

clone import FC.SMDTTCRC as FC_TCR with
  op t_smdttcr <- t
  
  proof *.
  realize ge0_tsmdttcr by exact: ge0_t.

clone import FC.SMDTDSPRC as FC_DSPR with
  op t_smdtdspr <- t
  
  proof *.
  realize ge0_tsmdtdspr by exact: ge0_t.  



module (R_TCRC_OpenPREC (A : Adv_SMDTOpenPREC) : Adv_SMDTTCRC) (O : Oracle_SMDTTCR, OC : Oracle_THFC) = {
  module O_R_TCRC_OpenPREC : Oracle_SMDTOpenPRE = {
    include O_SMDTOpenPRE_Default [-query]
        
    proc query(tw : tw) : output = {
      var x : input;
      var y : output;
      
      x <$ dinput;
      
      y <@ O.query(tw, x);
      
      return y;
    }
  }
    
  proc pick() : unit = {
    A(O_R_TCRC_OpenPREC, OC).pick();
  }
  
  proc find(pp : pp) : int * input = {
    var i : int;
    var x' : input;
    
    (i, x') <@ A(O_R_TCRC_OpenPREC, OC).find(pp);
    
    return (i, x');
  }
}.

module (R_DSPRC_OpenPREC (A : Adv_SMDTOpenPREC) : Adv_SMDTDSPRC) (O : Oracle_SMDTDSPR, OC : Oracle_THFC) = {
  module O_R_DSPRC_OpenPREC : Oracle_SMDTOpenPRE = {
    include var O_SMDTOpenPRE_Default [-init, query]
    
    proc init(pp : pp) : unit = {
      ts <- [];
      xs <- [];
      os <- [];
    }
    
    proc query(tw : tw) : output = {
      var x : input;
      var y : output;
      
      x <$ dinput;
      
      y <@ O.query(tw, x);
      
      xs <- rcons xs x;
      ts <- rcons ts (tw, y);
      
      return y;
    }
  }

  module OC_R_DSPRC_OpenPREC : Oracle_THFC = {
    var tws : tw list
    
    include O_THFC_Default [-init, query]
    
    proc init(pp : pp) : unit = {
      tws <- [];
    }
    
    proc query(tw : tw, x : input) : output = {
      var df : df;
      var y : output;

      y <@ OC.query(tw, x);
      
      tws <- rcons tws tw;

      return y;
    }
  }

  proc pick() : unit = {
    O_R_DSPRC_OpenPREC.init(witness);
    OC_R_DSPRC_OpenPREC.init(witness);
    
    A(O_R_DSPRC_OpenPREC, OC_R_DSPRC_OpenPREC).pick();
  }
  
  proc guess(pp : pp) : int * bool = {
    var i : int;
    var x, x' : input;
    var nrts : int;
    var opened, dist, b : bool;
    var twsO, twsOC : tw list;
    
    (i, x') <@ A(O_R_DSPRC_OpenPREC, OC_R_DSPRC_OpenPREC).find(pp);
    
    nrts <@ O_R_DSPRC_OpenPREC.nr_targets();
    opened <@ O_R_DSPRC_OpenPREC.opened(i);
    dist <@ O_R_DSPRC_OpenPREC.dist_tweaks();
    
    twsO <@ O_R_DSPRC_OpenPREC.get_tweaks();
    twsOC <@ OC_R_DSPRC_OpenPREC.get_tweaks();
        
    x <- nth witness O_SMDTOpenPRE_Default.xs i; (* <@ O_R_DSPRC_OpenPREC.open(i); *)
    
    b <- x <> x' \/ ! (0 <= nrts <= t /\ !opened /\ dist /\ disj_lists twsO twsOC);
    
    return (i, b);
  }
}.


section Proof_OpenPREC_From_DSPRC_TCRC.

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


local op is_pre_f (pp : pp) (tw : tw) (y : output) : input -> bool = 
  fun (x : input) => f pp tw x = y.
 
local op pre_f_l (pp : pp) (tw : tw) (y : output) : input list =
  to_seq (is_pre_f pp tw y).
  
local lemma is_finite_ispref (pp : pp) (tw : tw) (y : output) : 
  is_finite (is_pre_f pp tw y).
proof. by rewrite (finite_leq predT) 2:-/finite_type 2:is_finite. qed.

local lemma ltcard_szprefl (pp : pp) (tw : tw) (y : output) :
  size (pre_f_l pp tw y) <= card.
proof. by rewrite card_size_to_seq sub_size_to_seq 2:-/finite_type 2:is_finite. qed. 

local lemma rngprefl_image (pp : pp) (tw : tw) (x : input) :
  1 <= size (pre_f_l pp tw (f pp tw x)) <= card.
proof.
split => [| _]; 2: by apply ltcard_szprefl.
apply (mem_size_ge1 _ x).
by rewrite mem_to_seq 1:is_finite_ispref.
qed.

local lemma eqv_spex_szprefl (pp : pp) (tw : tw) (x : input) :
  spexists f pp tw x 
  <=> 
  2 <= size (pre_f_l pp tw (f pp tw x)).
proof.
split=> [| @/pre_f_l ge2_szprefl]. 
+ elim => x' [neqx_xp eqfkx_fkxp].
  by apply (mem_size_ge2 _ x x'); 1,2: rewrite mem_to_seq 1:is_finite_ispref // /#.
move: (uniq_to_seq (is_pre_f pp tw (f pp tw x)) (is_finite_ispref pp tw (f pp tw x))).
move/uniq_size_ge2_mem => /(_ ge2_szprefl) -[x' x''] [#] neqxp_xpp xpin xppin.
case (x' = x) => [eqx_xp | neqx_xp].
+ exists x''; split; 1: by rewrite -eqx_xp. 
  by move: xppin; rewrite mem_to_seq 1:is_finite_ispref /#.
exists x'; rewrite eq_sym neqx_xp /=. 
by move: xpin; rewrite mem_to_seq 1:is_finite_ispref /#.
qed.

local lemma eqv_img_prefl (pp : pp) (tw : tw) (x x' : input) :
  f pp tw x = f pp tw x' 
  <=> 
  pre_f_l pp tw (f pp tw x) = pre_f_l pp tw (f pp tw x').
proof.
split => [-> // | @/pre_f_l eq_prefl].
move: (to_seq_finite (is_pre_f pp tw (f pp tw x)) _); 1: by apply is_finite_ispref.  
rewrite uniq_to_seq 1:is_finite_ispref /= => /(_ x') /iffLR /(_ _).
+ by rewrite eq_prefl to_seq_finite 1:is_finite_ispref.
by rewrite /is_pre_f => ->.
qed.

local lemma eqv_img_mem (pp : pp) (tw : tw) (x x' : input) :
  f pp tw x = f pp tw x' 
  <=> 
  x' \in pre_f_l pp tw (f pp tw x).
proof. by rewrite to_seq_finite 1:is_finite_ispref /is_pre_f; split => ->. qed.
  
local lemma eqv_prefl_mem (pp : pp) (tw : tw) (x x' : input) :
  x' \in pre_f_l pp tw (f pp tw x) 
  <=> 
  pre_f_l pp tw (f pp tw x) = pre_f_l pp tw (f pp tw x').
proof. by rewrite -eqv_img_mem eqv_img_prefl. qed.


declare module A <: Adv_SMDTOpenPREC {-O_SMDTOpenPRE_Default, -O_SMDTDSPR_Default, -O_THFC_Default}.

declare axiom A_pick_ll (O <: Oracle_SMDTOpenPRE {-A}) (OC <: Oracle_THFC {-A}) : 
  islossless O.query => islossless O.query => islossless A(O, OC).pick.

declare axiom A_find_ll (O <: Oracle_SMDTOpenPRE {-A}) (OC <: Oracle_THFC {-A}) : 
  islossless O.open => islossless A(O, OC).find.


local module Si = {
  var x, x' : input
  
  proc main(i : int) : bool = {
    var pp : pp;
    var tw : tw;
    var y : output;
    var nrts : int;
    var opened, dist : bool;
    var twsO, twsOC : tw list;
    
    pp <$ dpp;
    
    O_SMDTOpenPRE_Default.init(pp);
    
    A(O_SMDTOpenPRE_Default, O_THFC_Default).pick();
    
    (i, x') <@ A(O_SMDTOpenPRE_Default, O_THFC_Default).find(pp);
    
    (tw, y) <@ O_SMDTOpenPRE_Default.get(i);
    
    nrts <@ O_SMDTOpenPRE_Default.nr_targets();
    opened <@ O_SMDTOpenPRE_Default.opened(i);
    dist <@ O_SMDTOpenPRE_Default.dist_tweaks();
    
    twsO <@ O_SMDTOpenPRE_Default.get_tweaks();
    twsOC <@ O_THFC_Default.get_tweaks();
    
    x <- nth witness O_SMDTOpenPRE_Default.xs i;
    
    return size (pre_f_l pp tw y) = i /\ (0 <= nrts <= t /\ !opened /\ dist /\ disj_lists twsO twsOC /\ f pp tw x' = y);
  }
}.

local module Fi = {
  proc main(i : int) : bool = {
    var pp : pp;
    var tw : tw;
    var y : output;
    var nrts : int;
    var opened, dist : bool;    
    var x, x' : input;
    var twsO, twsOC : tw list;
    
    pp <$ dpp;
    
    O_SMDTOpenPRE_Default.init(pp);
    
    A(O_SMDTOpenPRE_Default, O_THFC_Default).pick();
    
    (i, x') <@ A(O_SMDTOpenPRE_Default, O_THFC_Default).find(pp);
    
    (tw, y) <@ O_SMDTOpenPRE_Default.get(i);
    nrts <@ O_SMDTOpenPRE_Default.nr_targets();
    opened <@ O_SMDTOpenPRE_Default.opened(i);
    dist <@ O_SMDTOpenPRE_Default.dist_tweaks();
    
    twsO <@ O_SMDTOpenPRE_Default.get_tweaks();
    twsOC <@ O_THFC_Default.get_tweaks();
    
    x <- nth witness O_SMDTOpenPRE_Default.xs i;
    
    return size (pre_f_l pp tw y) = i /\ ! (0 <= nrts <= t /\ !opened /\ dist /\ disj_lists twsO twsOC /\ f pp tw x' = y);
  }
}.

    
local lemma pr_cond_neqxxp_Si (j : int) &m:
  Pr[Si.main(j) @ &m : res /\ Si.x' <> Si.x]
  =
  (j%r - 1%r) / j%r * Pr[Si.main(j) @ &m : res].
proof. admit. qed.


local lemma pr_OpenPREC_bigSi &m :
  Pr[SM_DT_OpenPRE_C(A, O_SMDTOpenPRE_Default, O_THFC_Default).main() @ &m : res]
  =
  Pr[Si.main(1) @ &m : res]
  +
  bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res]) 2 (card + 1).
proof. admit. qed.

local lemma pr_DSPRC_bigSiFi &m :
  Pr[SM_DT_DSPR_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res]
  =
  Pr[Si.main(1) @ &m : res] 
  +
  bigi predT (fun (i : int) => (i%r - 1%r) / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1)
  +
  bigi predT (fun (i : int) => Pr[Fi.main(i) @ &m : res]) 2 (card + 1).
proof. admit. qed.

local lemma pr_SPprobC_bigSi &m: 
  Pr[SM_DT_SPprob_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res]
  =
  bigi predT (fun (i : int) => Pr[Si.main(i) @ &m : res]) 2 (card + 1)
  +
  bigi predT (fun (i : int) => Pr[Fi.main(i) @ &m : res]) 2 (card + 1).
proof. admit. qed.

local lemma pr_DSPRCSPprobC_bigSi &m :
  Pr[SM_DT_DSPR_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res]
  -
  Pr[SM_DT_SPprob_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res]
  =
  Pr[Si.main(1) @ &m : res] 
  -
  bigi predT (fun (i : int) => 1%r / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1).
proof.
rewrite pr_DSPRC_bigSiFi pr_SPprobC_bigSi.
field; rewrite -big_split /= subr_eq0 &(eq_big_seq) => i /mem_range rng_i /=.
rewrite -mulrDl -{1}mul1r -mulrDl (: 1%r + (i%r - 1%r) = i%r) 1:/#.
by rewrite mulrC mulrA mulVf 1:/#.
qed.

local lemma pr_TCRC_bigSi &m :
  Pr[SM_DT_TCR_C(R_TCRC_OpenPREC(A), O_SMDTTCR_Default, O_THFC_Default).main() @ &m : res]
  =
  bigi predT (fun (i : int) => (i%r - 1%r) / i%r * Pr[Si.main(i) @ &m : res]) 2 (card + 1).
proof. admit. qed.

lemma OpenPREC_From_DSPRC_TCRC &m :
  Pr[SM_DT_OpenPRE_C(A, O_SMDTOpenPRE_Default, O_THFC_Default).main() @ &m : res]
  <= 
  maxr 0%r 
       (Pr[SM_DT_DSPR_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res]
        -
        Pr[SM_DT_SPprob_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res])
  +
  3%r * Pr[SM_DT_TCR_C(R_TCRC_OpenPREC(A), O_SMDTTCR_Default, O_THFC_Default).main() @ &m : res].
proof.
apply (ler_trans 
        (Pr[SM_DT_DSPR_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res]
         -
         Pr[SM_DT_SPprob_C(R_DSPRC_OpenPREC(A), O_SMDTDSPR_Default, O_THFC_Default).main() @ &m : res] 
         +
         3%r * Pr[SM_DT_TCR_C(R_TCRC_OpenPREC(A), O_SMDTTCR_Default, O_THFC_Default).main() @ &m : res])); last first.
+ by apply ler_add; 1: rewrite maxrr. 
rewrite pr_OpenPREC_bigSi pr_DSPRCSPprobC_bigSi pr_TCRC_bigSi.
rewrite -addrA &(ler_add) 1:// addrC mulrC mulr_suml sumrB /=.
apply ler_sum_seq => i /mem_range rng_i _ /=.
rewrite mulrC 2!mulrA mulrDr /= divrr 1:/# /=.
rewrite mulrAC mulrDl /= 2!mulNr /= mulrC -mulrBr.
by rewrite &(ler_pemulr) 1:Pr[mu_ge0] // /#.
qed.

end section Proof_OpenPREC_From_DSPRC_TCRC.
