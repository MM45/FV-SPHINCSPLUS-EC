require import AllCore List Distr.

require KeyedHashFunctions KeyedHashFunctionsO.

type in_t.
type out_t.

type key_t. 

op f : key_t -> in_t -> out_t.

op [lossless] din : in_t distr.
op [lossless] dkey : key_t distr.


clone import KeyedHashFunctions as KHF with
  type in_t <- in_t,
  type out_t <- out_t,
  type key_t <- key_t,
  
  op f <- f
  
  proof *.

  
clone import KeyedHashFunctionsO as KHFO with
  type in_t <- in_t,
  type out_t <- out_t,
  type key_t <- key_t,
  
  op df <- dunit f
  
  proof *.
  realize df_ll by exact: dunit_ll.  


clone KHF.PRE as KHFPRE with 
  op din <- din,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: din_ll.
  realize dkey_ll by exact: dkey_ll.

clone KHFO.PRE as KHFPREO with 
  op din <- din,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: din_ll.
  realize dkey_ll by exact: dkey_ll.

module (R_PREO_PRE (A : KHFPRE.Adv_PRE) : KHFPREO.Adv_PRE) (O : Oracle_t)   = {
  proc find(k : key_t, y : out_t) : in_t = {
    var x : in_t;
    
    x <@ A.find(k, y);
    
    return x;
  }
}.

module R_PRE_PREO (A : KHFPREO.Adv_PRE) : KHFPRE.Adv_PRE   = {
  proc find(k : key_t, y : out_t) : in_t = {
    var x : in_t;
    
    O_Default.init(f);
    
    x <@ A(O_Default).find(k, y);
    
    return x;
  }
}.


equiv Eqv_PRE_PREO (A <: KHFPRE.Adv_PRE{-O_Default}):
  KHFPRE.PRE(A).main ~ KHFPREO.PRE(R_PREO_PRE(A), O_Default).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: true) => /=.
wp; rnd; wp; rnd.
by rnd{2}; skip => /> f' /supp_dunit ->.
qed.

equiv Eqv_PREO_PRE (A <: KHFPREO.Adv_PRE{-O_Default}):
  KHFPREO.PRE(A, O_Default).main ~ KHFPRE.PRE(R_PRE_PREO(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: ={glob O_Default}) => /=; 1: by proc.
wp; rnd; wp; rnd.
by rnd{1}; skip => /> f' /supp_dunit ->.
qed.




clone KHF.SPR as KHFSPR with 
  op din <- din,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: din_ll.
  realize dkey_ll by exact: dkey_ll.

clone KHFO.SPR as KHFSPRO with 
  op din <- din,
  op dkey <- dkey
  
  proof *.
  realize din_ll by exact: din_ll.
  realize dkey_ll by exact: dkey_ll.

module (R_SPRO_SPR (A : KHFSPR.Adv_SPR) : KHFSPRO.Adv_SPR) (O : Oracle_t)   = {
  proc find(k : key_t, x : in_t) : in_t = {
    var x' : in_t;
    
    x' <@ A.find(k, x);
    
    return x';
  }
}.

module R_SPR_SPRO (A : KHFSPRO.Adv_SPR) : KHFSPR.Adv_SPR   = {
  proc find(k : key_t, x : in_t) : in_t = {
    var x' : in_t;
    
    O_Default.init(f);
    
    x' <@ A(O_Default).find(k, x);
    
    return x';
  }
}.


equiv Eqv_SPR_SPRO (A <: KHFSPR.Adv_SPR{-O_Default}):
  KHFSPR.SPR(A).main ~ KHFSPRO.SPR(R_SPRO_SPR(A), O_Default).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: true) => /=.
wp; rnd; wp; rnd.
by rnd{2}; skip => /> f' /supp_dunit ->.
qed.

equiv Eqv_SPRO_SPR (A <: KHFSPRO.Adv_SPR{-O_Default}):
  KHFSPRO.SPR(A, O_Default).main ~ KHFSPR.SPR(R_SPR_SPRO(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: ={glob O_Default}) => /=; 1: by proc.
wp; rnd; wp; rnd.
by rnd{1}; skip => /> f' /supp_dunit ->.
qed.



clone KHF.TCR as KHFTCR with 
  op dkey <- dkey
  
  proof *.
  realize dkey_ll by exact: dkey_ll.

clone KHFO.TCR as KHFTCRO with 
  op dkey <- dkey
  
  proof *.
  realize dkey_ll by exact: dkey_ll.

module (R_TCRO_TCR (A : KHFTCR.Adv_TCR) : KHFTCRO.Adv_TCR) (O : Oracle_t)   = {
  proc pick() : in_t = {
    var x : in_t;
    
    x <@ A.pick();
    
    return x; 
  }
  
  proc find(k : key_t) : in_t = {
    var x : in_t;
    
    x <@ A.find(k);
    
    return x;
  }
}.

module R_TCR_TCRO (A : KHFTCRO.Adv_TCR) : KHFTCR.Adv_TCR   = {
  proc pick() : in_t = {
    var x : in_t;
    
    x <@ A(O_Default).pick();
    
    return x; 
  }
  
  proc find(k : key_t) : in_t = {
    var x : in_t;
    
    O_Default.init(f);
    
    x <@ A(O_Default).find(k);
    
    return x;
  }
}.


equiv Eqv_TCR_TCRO (A <: KHFTCR.Adv_TCR{-O_Default}):
  KHFTCR.TCR(A).main ~ KHFTCRO.TCR(R_TCRO_TCR(A), O_Default).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: true) => /=.
wp; rnd; rnd{2}; wp.
call (: true).
by skip => /> x f' /supp_dunit ->.
qed.

equiv Eqv_TCRO_TCR (A <: KHFTCRO.Adv_TCR{-O_Default}):
  KHFTCRO.TCR(A, O_Default).main ~ KHFTCR.TCR(R_TCR_TCRO(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: ={glob O_Default}) => /=; 1: by proc.
wp; rnd; rnd{1}; wp.
call (: true).
by skip => /> f' /supp_dunit ->.
qed.


clone KHF.METCR as KHFMETCR with 
  op dkey <- dkey
  
  proof *.
  realize dkey_ll by exact: dkey_ll.

clone KHFO.METCR as KHFMETCRO with 
  op dkey <- dkey
  
  proof *.
  realize dkey_ll by exact: dkey_ll.


module (R_METCRO_METCR (A : KHFMETCR.Adv_METCR) : KHFMETCRO.Adv_METCR) (O : Oracle_t, CO : KHFMETCRO.Oracle_METCR_t)   = {
  proc find() : int * key_t * in_t = {
    var i : int;
    var k : key_t;
    var x : in_t;
    
    (i, k, x) <@ A(CO).find();    
    
    return (i, k, x);
  }
}.

module (R_METCR_METCRO (A : KHFMETCRO.Adv_METCR) : KHFMETCR.Adv_METCR) (CO :  KHFMETCR.Oracle_METCR_t) = {
  proc find() : int * key_t * in_t = {
    var i : int;
    var k : key_t;
    var x : in_t;
    
    O_Default.init(f);
    
    (i, k, x) <@ A(O_Default, CO).find();
    
    return (i, k, x);
  }
}.


equiv Eqv_METCR_METCRO (A <: KHFMETCR.Adv_METCR{-O_Default, -KHFMETCR.O_METCR_Default, -KHFMETCRO.O_METCR_Default}):
  KHFMETCR.M_ETCR(A, KHFMETCR.O_METCR_Default).main ~ KHFMETCRO.M_ETCR(R_METCRO_METCR(A), O_Default, KHFMETCRO.O_METCR_Default).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp; call (: (glob KHFMETCR.O_METCR_Default){1} = (glob KHFMETCRO.O_METCR_Default){2}) => /=.
+ by proc; wp; rnd; skip.
by wp; rnd{2}; wp; skip => /> f' /supp_dunit ->.
qed.

equiv Eqv_METCRO_METCR (A <: KHFMETCRO.Adv_METCR{-O_Default, -KHFMETCR.O_METCR_Default, -KHFMETCRO.O_METCR_Default}):
  KHFMETCRO.M_ETCR(A, O_Default, KHFMETCRO.O_METCR_Default).main ~ KHFMETCR.M_ETCR(R_METCR_METCRO(A), KHFMETCR.O_METCR_Default).main : ={glob A} ==> ={res}.
proof.
proc; inline *.
wp.
call (:   ={glob O_Default} 
       /\ (glob KHFMETCRO.O_METCR_Default){1} = (glob KHFMETCR.O_METCR_Default){2}).
+ by proc; wp; rnd; skip.
+ by proc.
by wp; rnd{1}; skip => /> f' /supp_dunit ->.
qed.

