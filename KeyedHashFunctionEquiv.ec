require import AllCore Distr.

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
    
    O_Default.init(f, k);
    
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
