require import AllCore Distr DBool List Dexcepted.
require import FunSamplingLib. 

abstract theory BF.

type X.
type Y.


clone import LambdaReprogram as Reprogram with
  type X <- X,
  type Y <- Y.

module type BFOi_t = {
   proc init() : unit
   proc h( x : X ) : bool
}.


module BFO0 : BFOi_t  = {
   proc init() = {}
   proc h( x : X ) : bool = { return false; }
}.

module BFO1 : BFOi_t  = {
   var f : X -> bool
   proc init() = { f <$ dboolf; }
   proc h( x : X ) : bool = { return f x; }
}.

module type BFO_t = { include BFOi_t [-init] }.

module type BFO_D(BFO : BFO_t) = {
   proc dist() : bool
}.

module type BFO_F(BFO : BFO_t) = {
   proc find() : X
}.

module BFO_Find(A : BFO_F) = {
   proc main() : bool = {
       var x;
       BFO1.init();
       x <@ A(BFO1).find();
       return (BFO1.f x);
   }
}.

module BFO_Dist(BFO : BFOi_t, A : BFO_D) = {
   proc main() : bool = {
       var b;
       BFO.init();
       b <@ A(BFO).dist();
       return b;
   }
}.

(*
axiom bfo_assumption qbfo (A <: BFO_D {-BFO1, -BFO0}) &m :  
   0 <= qbfo =>
   `| Pr [ BFO_Dist(BFO0, A).main() @ &m : res ] -
        Pr [ BFO_Dist(BFO1, A).main() @ &m : res ] | <= 8%r*lambda*qbfo%r^2.
*)

module (Red_D (A: BFO_F) : BFO_D) (O : BFO_t) = {
  proc dist() = {
    var x, b;
    x <@ A(O).find();
    b <@ O.h( x );
    return b;
  }
}.

section.
declare op qbfoF : int.

declare axiom qF_ge0 : 0 <= qbfoF. 

lemma find_implies_dist (A <: BFO_F {-BFO1}) &m :  
  Pr[ BFO_Find(A).main() @ &m : res] =
  `| Pr [ BFO_Dist(BFO0, Red_D(A)).main() @ &m : res ] -
        Pr [ BFO_Dist(BFO1, Red_D(A)).main() @ &m : res ] |.
proof.
have -> : Pr [ BFO_Dist(BFO0, Red_D(A)).main() @ &m : res ] = 0%r.     
byphoare => //.
hoare.
by proc; inline*; auto.
rewrite /= StdOrder.RealOrder.normrN StdOrder.RealOrder.ger0_norm 1:Pr[mu_ge0] //.
byequiv => //.
proc. inline*. wp. call( : ={glob BFO1}). by sim.
by auto => />.
qed.
end section.

(* Generalization to multiple lambdas *)
type Aux.
module type GBFO_ti = {
   proc init(ps : X -> real) : unit
   proc h( x : X ) : bool 
}.


module type GBFO_F(O : BFO_t) = {
   proc lambdas(aux : Aux) : (X -> real) {}
   proc find() : X { O.h }
}.

clone import MixLambdaDFun with
   type DFBM.X <- X,
   theory DFBM.MUFF <- MUFF.

import DFBM.

module GBFO1  = {
   var f : X -> bool
   proc init(ps : X -> real) = {  f <$ dfun_biased ps; }
   proc h( x : X ) : bool = { return f x; }
}.

module GBFO_Find(A : GBFO_F) = {
   proc main(lambda : real, aux : Aux) : bool = {
       var x, ps,r;
       r <- false;
       ps <@ A(GBFO1).lambdas(aux);
       if (forall x, 0%r <= ps x <= lambda) {
         GBFO1.init(ps);
         x <@ A(GBFO1).find();
         r <- (GBFO1.f x);
       }
       return r;
   }
}.

section.
declare op qbfoF : int.

declare axiom qF_ge0 : 0 <= qbfoF. 

lemma GFBO_bound lambda &m aux (A <: GBFO_F {-GBFO1}) :
    0%r < lambda < 1%r =>
    Pr [ GBFO_Find(A).main(lambda, aux) @ &m : res ] <= 
       8%r*lambda*(qbfoF+1)%r^2.
admitted. (* reduce to BFO *)
end section.

end BF.

theory SecondPreimageBound.

clone import BF.
import Reprogram.
clone import MFinite as MFX with 
  type t <- X,
  theory Support <- MUFF.FinT.

abbrev dx = MFX.dunifin.        
        
module type ROi_t = {
   proc init() : unit
   proc h( x : X ) : Y
}.

module RO : ROi_t  = {
   var f : X -> Y
   proc init() = { f <$ dh; }
   proc h( x : X ) : Y = { return f x; }
}.

print dh.
module type RO_t = { include ROi_t [-init] }.

(* Variant to support history free proofs, 
   takes h as input to init *)
module RO_hf : RO_t  = {
   var f : X -> Y
   proc init(f_in: X -> Y) = { f <- f_in; }
   proc h( x : X ) : Y = { return f x; }
}.


module type SPR_Adv(RO : RO_t) = {
   proc find(x : X) : X
}.


module SPR(A : SPR_Adv) = {
   proc main() : bool = {
       var x,x',y,y';
       x <$ dx;
       RO.init();
       x' <@ A(RO).find(x);
       y <@ RO.h(x);
       y' <@ RO.h(x');
       return (x <> x' /\ y = y');
   }
}.

(* Main theorem *)

module R_find0 (A : SPR_Adv)  = {
  var gy : X -> Y
  var x0 : X
  var y0 : Y

  module O = {
    proc h(x : X) = {
      var b;

      b <@ BFO1.h(x);
      return if !b /\ x <> x0 then gy x else y0;
    }
  }

  proc find(): bool = {
    var x, y;

    BFO1.init();

    x0 <$ dx;
    y0 <$ dy;

    gy <$ MUFF.dfun (fun _=> dy \ (pred1 y0));

    x  <@ A(O).find(x0);

    y  <@ O.h(x);
    return (x <> x0 /\ y = y0);
  }
}.

module (R_find (A : SPR_Adv) : BFO_F) (BFO : BFO_t) = {
  include var R_find0(A) [-find]

  module O = {
    proc h(x : X) = {
      var b;

      b <@ BFO.h(x);
      return if !b /\ x <> x0 then gy x else y0;
    }
  }

  proc find(): X = {
    var x;

    x0 <$ dx;
    y0 <$ dy;

    gy <$ MUFF.dfun (fun _=> dy \ (pred1 y0));

    x  <@ A(O).find(x0);
    return (x);
  }
}.

equiv finder_good (A <: SPR_Adv {-BFO1, -R_find0}): 
   R_find0(A).find ~ BFO_Find(R_find(A)).main : ={glob A} ==> res{1} => res{2}.
proc. inline *. wp. 
conseq (_: ={glob A} ==> ={BFO1.f} /\ x{1} = x0{2} /\ R_find0.gy{1} x{1} <> R_find0.y0{1}) => />; 1: by smt().

call (_: ={glob BFO1, glob R_find0}); 1: by sim.
auto => />.
move =>  ??x0?y0? gy Hgy x. 
rewrite MUFF.dfun_supp  in Hgy.
move: (Hgy x) => /=.
by rewrite supp_dexcepted /= /pred1 /= /#.
qed.

(* The plan: Externalize the function sampling into separate modules *)

lemma SPR_R (A <: SPR_Adv { -BFO0, -BFO1, -R_find0, -RO }) &m:
  Pr[SPR(A).main() @ &m: res] = Pr[R_find0(A).find() @ &m: res].
proof.
byequiv=> //.
proc; inline *.
wp.
call (: forall x, RO.f{1} x = (if !BFO1.f x /\ x <> R_find0.x0 then R_find0.gy x else R_find0.y0){2}).
+ by proc; inline *; auto=> /> &1 &2 /(_ x{2}).
swap {2} 1 1.
seq  1  1: (={glob A} /\ x{1} = R_find0.x0{2}).
+ by auto.
conseq (: forall x, RO.f{1} x = (if !BFO1.f x /\ x <> R_find0.x0 then R_find0.gy x else R_find0.y0){2}).
+ move=> /> &2 hL hR gy y0 ih r.
  rewrite (eq_sym r); congr; rewrite !ih //= /#.

transitivity {1} { RO.f <@ LambdaRepro.left();}
        (true ==> ={RO.f}) (x{1} = R_find0.x0{2} ==> forall (x2 : X), RO.f{1} x2 = if ! BFO1.f{2} x2 /\ x2 <> R_find0.x0{2} then R_find0.gy{2} x2 else R_find0.y0{2}); 1,2: by smt().
+ by inline*;auto.

transitivity {1} { RO.f <@ LambdaRepro.right(x);}
        (true ==> ={RO.f}) (x{1} = R_find0.x0{2} ==> forall (x2 : X), RO.f{1} x2 = if ! BFO1.f{2} x2 /\ x2 <> R_find0.x0{2} then R_find0.gy{2} x2 else R_find0.y0{2}); 1,2: by smt().
(* FIXME: ecall rule is broken + ecall (LambdaReprogram.main_theorem x{2} lambdaP). *)
+ by call Reprogram.main_theorem.

inline *; sp;wp; swap {2} 2 -1. auto => />.

qed.

(*
section.

declare op q : int.
declare axiom q_ge0 : 0 <= q.

lemma spr_bound(A <: SPR_Adv { -BFO0, -BFO1, -R_find0, -RO }) &m : 
  Pr[ SPR(A).main() @ &m : res ] <= 32%r*lambda*(q+1)%r^2 .
rewrite (SPR_R A &m).
have ? : 
  Pr[ BFO_Find(R_find(A)).main () @ &m : res] >=
  Pr[R_find0(A).find() @ &m : res].
byequiv  (finder_good A) => //. 
move : (find_bound cA (2*q) _ cA_ge0 (R_find(A)) _) => //; 1: by smt(q_ge0).
+ admit. (* to do : we should only have to prove the ner of queries. 
     NOTE!!!!!!!!!! The counting of queries for this finder should account
    for the fact that whenever you implement an oracle that calls another
    oracle and keeps internal state (not in place) then the semantics 
    are correct if there are implicit state clean up calls to the
    oracle => 1 extra call to clean up, so overall 2q calls. *)
move => H.
move : (H &m).
have ? : 8%r * lambda * (2 * q + 1)%r ^ 2 <= 8%r * lambda * (2 * q + 2)%r ^ 2; last first.
+ have -> : 32%r * lambda * (q + 1)%r ^ 2 =  8%r * lambda * (2 * q + 2)%r ^ 2 by ring. 
  by smt().

apply StdOrder.RealOrder.ler_pmul; 1,2,3: by smt(lambda_bound q_ge0 StdOrder.RealOrder.ge0_sqr).
apply StdOrder.RealOrder.ler_pexp => //; smt( q_ge0).

qed.

end section.
*)

end SecondPreimageBound.

theory TCRBound.
(*
Outline:
- Define a "random keyed hashfunction": F(k,x) -> y such that y is sampled uniformly at random in the co-domain, independently of other values
- Instantiate the TCR definition in KeyedHashFunction theory with it.
- Prove that finding TC => finding a 1:
  * Given x, you sample a random k, and replace F(k, . ) by the random function used in SPR.
- Question: KeyedHashFunction Lib considers the hash function to be an op. We need it to be a module. This is kind of a switch to the ROM (we want to first fix the A and then evaluate the expected number of queries necessary to break a given property which is equivalent to a ROM bound).
*)
end TCRBound.


