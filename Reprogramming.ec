require import AllCore List Int Distr RealExp SmtMap FSet FinType StdOrder StdBigop PROM.
(*---*) import Bigreal.BRA Bigreal RField RealOrder.

type in_t.

type out_t.

type pT = in_t distr.

clone import FinType as FT_In with
  type t = in_t.

op [lossless] dout : out_t distr.

const p_max_bound : { real | 0%r <= p_max_bound } as ge0_pmaxbound.

clone import FullRO as ROM_ with
  type in_t <- in_t,
  type out_t <- out_t,
  op dout <- fun _ => dout,
  type d_in_t <- int,
  type d_out_t <- bool
  
  proof *.
 
clone import FinEager as LE with 
  theory FinFrom <- FT_In
  
  proof *.

(*

(**
  Adaptive reprogramming
  The adversary is single-stage, simultaneously getting access to the 
  original oracle as well as the reprogramming oracle.
**)
theory Adaptive.
  
module type Oracleip_t = {
  include RO [init, get, set]
}.

module type Oraclep_t = {
  include Oracleip_t [-init]
}.

module O_Programmable(O : RO) : Oraclep_t = {
   var prog_list : (in_t * out_t) list  
   var ch : int

   proc init() : unit = {
     prog_list <- [];
     ch <- 0;
   }

  proc get(x : in_t) : out_t = {
    var r,c : out_t;
    var tmp : out_t option;

    r <@ O.get(x);

    ch <- ch + 1; 
    tmp <- assoc prog_list x;
    c <- if tmp = None then r else oget tmp;

    return c; 
  }

  proc set (x : in_t, y : out_t) : unit = {
    prog_list <- (x, y) :: prog_list;
  }
}.

module type Oracleir_t = {
  proc init(b : bool) : unit
  proc repro(p : pT) : in_t
}.

module type Oracler_t = {
  include Oracleir_t [-init]
}.

module O_Reprogrammer(O : Oraclep_t) : Oracler_t = {
  var ctr : int
  var b : bool
  var se : bool

  proc init(in_b : bool) : unit = {
    ctr <- 0;
    b <- in_b;
    se <- true;
  }

  proc repro(p: pT) : in_t = {
    var x : in_t;
    var y : out_t;

    se <- if p_max p <= p_max_bound then se else false;
    ctr <- ctr + 1;

    x <$ p;

    if (b) {
      y <$ dout;
      O.set(x,y);
    }

    return x;
  }
}.

module type Adv_INDRepro(O : Oraclep_t, OR : Oracler_t) = {
  proc distinguish() : bool {O.get, OR.repro}
}.

module IND_Repro(O : RO, A : Adv_INDRepro) = {
  module OP = O_Programmable(O)
  module OR = O_Reprogrammer(OP)
 
  proc main (b : bool) : bool = {
    var b' : bool;
    
    O.init();
    OP.init();
    OR.init(b);
    
    b' <@ A(OP, OR).distinguish();
    
    return b';
  } 
}.


section.

declare module A <: Adv_INDRepro {-IND_Repro, -FunRO, -RO, -FRO}.

declare const rep_ctr : {int | 0 <= rep_ctr } as ge0_repctr.
declare const query_ctr : {int | 0 <= query_ctr } as ge0_queryctr.

local module Bad = { 
  var bad : bool
  var co : int
  var cr : int
  var i  : int
}.

local module O_Programmable1 (O : RO) : Oracleip_t = {
  include var O_Programmable(O) [-get]
  import var Bad
 
  proc get(x : in_t): out_t = {
    var r, c : out_t;
    var tmp : out_t option;

    c <- witness;
    if (co < query_ctr) { 
      r <@ O.get(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;
      co <- co + 1;
    } else {
      bad <- true;
      r <@ O.get(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;      
      co <- co + 1;
    }
    
    ch <- ch + 1; 
    
    return c; 
  }

}.

local module O_Programmable2 (O: RO) : Oracleip_t = {
  include var O_Programmable(O) [-get]
  import var Bad
 
  proc get(x : in_t): out_t = {
    var r, c : out_t;
    var tmp : out_t option;

    c <- witness;
    if (co < query_ctr) { 
      r <@ O.get(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;
      co <- co + 1;
    } else {
      bad <- true;
    }
    
    ch <- ch + 1; 
    
    return c; 
  }

}.

local module O_Programmable2S (O: RO) : Oracleip_t = {
  include var O_Programmable(O) [-get]
  import var Bad

  proc get(x : in_t): out_t = {
    var r, c : out_t;
    var tmp : out_t option;

    c <- witness;
    if (co < query_ctr) { 
      r <@ O.get(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;
      co <- co + 1;
    } 

    ch <- ch + 1; 
    
    return c; 
  }

}.

local module O_Reprogrammer1(O: Oraclep_t) : Oracleir_t = {
  include var O_Reprogrammer(O) [-repro]
  import var Bad

  proc repro(p : pT) : in_t = {
    var x : in_t;
    var y : out_t;
    
    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (b) {
        y <$ dout;
        O.set(x, y);
      }
      cr <- cr + 1;
    } else { 
      bad <- true;
      x <$ p;
      if (b) {
        y <$ dout;
        O.set(x, y);
      }
      cr <- cr + 1;
    }
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module O_Reprogrammer2(O: Oraclep_t) : Oracleir_t = {
  include var O_Reprogrammer(O) [-repro]
  import var Bad

  proc repro(p : pT) : in_t = {
    var x,y;
    
    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (b) {
        y <$ dout;
        O.set(x,y);
      } 
      cr <- cr + 1;
    } else { 
      bad <- true;
    }
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module IND_Repro1 (O: RO, A: Adv_INDRepro) = {
  import var Bad
  
  module OP = O_Programmable1(O)
  module OR = O_Reprogrammer1(OP)
 
  proc main (b : bool) : bool = {
    var b' : bool;
    
    bad <- false; co <- 0; cr <- 0;
    
    O.init();
    OP.init();
    OR.init(b);
    
    b' <@ A(OP, OR).distinguish();
    
    return b';
  } 
}.

local module IND_Repro2 (O: RO, A: Adv_INDRepro) = {
  import var Bad
  
  module OP = O_Programmable2(O)
  module OR = O_Reprogrammer2(OP)
 
  proc main (b : bool) : bool = {
    var b' : bool;
    
    bad <- false; co <- 0; cr <- 0;
    
    O.init();
    OP.init();
    OR.init(b);
    
    b' <@ A(OP, OR).distinguish();
    
    return b';
  } 
}.

local lemma Pr_count &m (b : bool) : 
     hoare[ A(O_Programmable(FunRO),O_Reprogrammer(O_Programmable(FunRO))).distinguish : 
             O_Programmable.ch = 0 /\ O_Reprogrammer.ctr = 0 /\ O_Reprogrammer.se 
             ==> O_Programmable.ch <= query_ctr /\ 
             O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] 
  => Pr[IND_Repro(FunRO, A).main(b) @ &m : res] 
     = 
     Pr[IND_Repro(FunRO,A).main(b) @ &m : res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se].
proof.
move=> hhoare.
byequiv => //.
conseq (: _ ==> ={res, O_Programmable.ch, O_Reprogrammer.ctr, O_Reprogrammer.se}) 
       (: true ==> O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) 
       _ => //; 2: by sim.
by proc; call hhoare; inline *; auto => /=.
qed.

local lemma Pr_Game_Game1 &m b : 
  Pr[IND_Repro(FunRO,A).main(b) @ &m:res /\  O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] =
  Pr[IND_Repro1(FunRO,A).main(b) @ &m:res /\  O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se].
proof.
byequiv => //.
proc.
call (:    ={glob FunRO,  glob O_Reprogrammer, glob O_Programmable} 
       /\ ((O_Reprogrammer.ctr, O_Programmable.ch) = (Bad.cr,Bad.co)){2}).
+ proc.
  case (Bad.co{2} < query_ctr). 
  - rcondt{2} 2; 1: by auto.
    wp; conseq (: _ ==> ={r}) => //.
    by inline *; wp; skip.
  rcondf{2} 2; 1: by auto.
  wp; conseq (: _ ==> ={r}) => //.
  by inline *; wp; skip.
+ proc. 
  seq 1 1: (#pre); 1: by auto.
  swap{1} 1 2.
  case ((O_Reprogrammer.se /\ Bad.cr < rep_ctr){2}).
  + rcondt{2} 2; 1: by auto. 
    by wp => />; sim.
  rcondf{2} 2; 1: by auto. 
  by wp => />; sim.
by inline *;auto.
qed.

local lemma Pr_Game1_Game2 &m b: 
  Pr[IND_Repro1(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] =
  Pr[IND_Repro2(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se].
proof.
have: 
  `| Pr[IND_Repro1(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] -
     Pr[IND_Repro2(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] | 
  <=
  RealOrder.maxr Pr[IND_Repro1(FunRO,A).main(b) @ &m: (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad] 
                 Pr[IND_Repro2(FunRO,A).main(b) @ &m: (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad].
+ byupto.
have ->: 
  Pr[IND_Repro1(FunRO, A).main(b) @ &m : (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad] 
  = 
  0%r.
+ byphoare => //.
  hoare.
  proc. 
  call (:   Bad.cr <= O_Reprogrammer.ctr 
          /\ Bad.co <= O_Programmable.ch 
          /\ (Bad.bad => ! (O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se))). 
  + by proc; sp; wp; if; auto; call (: true); auto => /#.
  + proc; sp; wp; if; auto. 
    - by conseq (: _ ==> true); auto => /#.
    by swap 1 2; wp; conseq (: _ ==> true); auto => /#.
  by inline *; auto => /#.
have -> /#: 
  Pr[IND_Repro2(FunRO, A).main(b) @ &m : (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad] 
  = 
  0%r.
byphoare => //.
hoare.
proc. 
call (:   Bad.cr <= O_Reprogrammer.ctr 
       /\ Bad.co <= O_Programmable.ch 
       /\ (Bad.bad => ! (O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se))). 
+ by proc; sp; wp; if; auto; 1: call (: true); auto => /#.
+ proc; sp; wp; if; auto; 2: smt().
  by conseq (: _ ==> true); auto => /#.
by inline *; auto => /#.
qed.

local module O_Reprogrammer2i : Oracleir_t = {
  include var O_Reprogrammer(O_Programmable2S(FunRO)) [-repro]
  import var Bad

  proc repro(p: pT) : in_t = {
    var x : in_t;
    var y : out_t;
    
    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i <= cr) {
        y <$ dout;
        O_Programmable2(FunRO).set(x,y);
      }
      cr <- cr + 1;
    } 
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module Hi = {
  import var Bad
  
  module OP = O_Programmable2S(FunRO)
  module OR = O_Reprogrammer2i
 
  proc main (i0: int) : bool = {
    var b' : bool;
    
    bad <- false; cr <- 0; co <- 0; i <- i0;
    
    FunRO.init();
    OP.init();
    OR.init(false);
    
    b' <@ A(OP, OR).distinguish();
    
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local lemma Hi_true &m : 
  Pr[IND_Repro2(FunRO, A).main(true) @ &m : res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se]
  = 
  Pr[Hi.main(0) @ &m : res].
proof.
byequiv => //.
proc.
call (:   ={glob O_Programmable, O_Reprogrammer.se, O_Reprogrammer.ctr, FunRO.f, Bad.cr, Bad.co} 
       /\ O_Reprogrammer.b{1} 
       /\ (Bad.i <= Bad.cr){2}).
+ by sim />.
+ proc. 
  seq 2 2 : (#pre /\ ={x}); 1: by auto.
  wp; if; auto.
  conseq (: ={glob O_Programmable, O_Reprogrammer.se, O_Reprogrammer.ctr, FunRO.f, x}); 1: smt().
  seq 1 1 : (#pre); 1: by sim />.
  by if; auto; sim.
by inline *; swap{1} [1 ..3] 3; swap{2} [1 ..4] 3; auto; sim />.
qed.

local lemma Hi_false &m : 
  Pr[IND_Repro2(FunRO, A).main(false) @ &m : res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se]
  = 
  Pr[Hi.main(rep_ctr) @ &m : res].
proof.
byequiv => //.
proc.
call (:   ={glob O_Programmable, O_Reprogrammer.se, O_Reprogrammer.ctr, FunRO.f, Bad.cr, Bad.co} 
       /\ !O_Reprogrammer.b{1} 
       /\ (Bad.i = rep_ctr){2}).
+ by sim />.
+ proc. 
  seq 2 2 : (#pre /\ ={x}); 1: by auto.
  wp; if; auto.
  rcondf{1} ^if; 1: by auto.
  by rcondf{2} ^if; auto => /#.
inline *; swap{1} [1 ..3] 3; swap{2} [1 ..4] 3; auto; sim />.
qed.

local module O_Reprogrammer2i1 (O: RO) : Oracleir_t = {
  import var Bad

  include var O_Reprogrammer(O_Programmable2S(O)) [-repro]
  
  var x_ : in_t

  proc repro(p: pT) : in_t = {
    var x : in_t;
    var y : out_t;
    
    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i + 1 <= cr) {
        y <$ dout;
        O_Programmable2S(O).set(x,y);
      } else { 
        if (i = cr) {
          x_ <- x;
          y <@ O.get(x);
        } 
      } 
      cr <- cr + 1;
    } 
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module Hi1 (O:RO) = {
  import var Bad
  
  module OP = O_Programmable2S(O)
  module OR = O_Reprogrammer2i1(O)
 
  proc distinguish (i0: int) : bool = {
    var b' : bool;
 
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    OP.init();
    OR.init(false);
 
    b' <@ A(OP, OR).distinguish();
 
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local lemma Hip1_Hi1 &m i_ : 
  Pr[Hi.main(i_ + 1) @ &m : res] 
  = 
  Pr[MainD(Hi1,FunRO).distinguish(i_) @ &m : res].
proof.
byequiv => //. 
proc. 
inline *; wp.
call (:   ={FunRO.f, glob O_Programmable, glob O_Reprogrammer, Bad.cr, Bad.co} 
       /\ Bad.i{1} = Bad.i{2} + 1).
+ by sim />.
+ proc; wp; conseq />.
  seq 2 2 : (#pre /\ ={x}); 1: by auto.
  if => //.
  seq 1 1 : (#pre); 1: by auto.
  if => //; 1: by sim.
  by inline *; auto.
by swap{1} [1..4] 3; auto; sim />.
qed.

local lemma Hi1_FunRO_RO  &m i_ : 
  Pr[MainD(Hi1,FunRO).distinguish(i_) @ &m : res] 
  =
  Pr[MainD(Hi1,RO).distinguish(i_) @ &m : res].
proof.
have <- : Pr[MainD(Hi1, FinRO).distinguish(i_) @ &m : res] = 
          Pr[MainD(Hi1, FunRO).distinguish(i_) @ &m : res]
  by  apply (pr_FinRO_FunRO_D _ Hi1 &m i_ (fun b => b));smt(dout_ll).
by rewrite (pr_RO_FinRO_D _ Hi1 &m i_ (fun b => b));smt(dout_ll).
qed.

local module O_Reprogrammer2i2 : Oracleir_t = {
  import var Bad
  include var O_Reprogrammer(O_Programmable2S(RO)) [-repro]
  
  var x_ : in_t

  proc repro(p : pT) : in_t = {
    var x : in_t;
    var y : out_t;
    
    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\  cr < rep_ctr) { 
      x <$ p;
      if (i + 1 <= cr) {
        y <$ dout;
        O_Programmable2S(RO).set(x,y);
      } else { if (i = cr /\ fsize RO.m <= query_ctr) {
        x_ <- x;
        if (! x \in RO.m) {
          y <@ RO.get(x);
        } else { 
          bad <- true;
          y <@ RO.get(x);          
        }
      } } 
      cr <- cr + 1;
    } 
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module Hi2 = {
  import var Bad
  
  module OP = O_Programmable2S(RO)
  module OR = O_Reprogrammer2i2
 
  proc run (i0: int) : bool = {
    var b' : bool;
    
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    
    RO.init();
    OP.init();
    OR.init(false);
    
    b' <@ A(OP, OR).distinguish();
    
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local module O_Reprogrammer2i3 : Oracleir_t = {
  import var Bad
  include var O_Reprogrammer(O_Programmable2S(RO)) [-repro]

  proc repro(p: pT) : in_t = {
    var x : in_t;
    var y : out_t;

    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i + 1 <= cr) {
        y <$ dout;
        O_Programmable2S(RO).set(x,y);
      } else { if (i = cr /\ fsize RO.m <= query_ctr) {
        O_Reprogrammer2i2.x_ <- x;
        if (! x \in RO.m) {
          y <@ RO.get(x);
        } else { 
          bad <- true;
          RO.m <- rem RO.m x;
          y <@ RO.get(x); 
        }
      } } 
      cr <- cr + 1;
    } 

    ctr <- ctr + 1;
    
    return x;
  }
}.

local module Hi3 = {
  import var Bad
  
  module OP = O_Programmable2S(RO)
  module OR = O_Reprogrammer2i3
 
  proc run (i0: int) : bool = {
    var b';
    
    bad <- false;  cr <- 0; co <- 0; i <- i0;
  
    RO.init();
    OP.init();
    OR.init(false);
  
    b' <@ A(OP, OR).distinguish();
  
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local lemma Hi1_LRO_Hi2  &m i_ : Pr[ MainD(Hi1,RO).distinguish(i_) @ &m : res] = Pr[Hi2.run(i_) @ &m : res].
proof.
byequiv => //.
proc. 
inline *; wp.
call (:   ={ RO.m, glob O_Programmable, glob O_Reprogrammer, Bad.cr, Bad.co, Bad.i} 
       /\ (Bad.cr <= Bad.i => fsize RO.m <= Bad.co <= query_ctr){1}); last first.
+ by auto => />; rewrite fsize_empty ge0_queryctr.
+ by proc; sp; inline *; if; auto => /> &2 3? r *; rewrite fsize_set /b2i => /> /#.
proc. 
wp. 
seq 2 2 : (#pre /\ ={x}); 1: by sim />.
if => //.  
seq 1 1: (#pre); 1: by sim />.
if => //.
+ wp. 
  by conseq (: _ ==> ={y, O_Programmable.prog_list}); [smt() | sim].
wp. 
if => //; 1: smt().
+ sp 1 1. 
  conseq (: _ ==> ={RO.m}); [smt() | if{2}; sim].
by auto => /#.
qed.

local lemma Hi2_Hi3 &m i_ : 
  `| Pr[ Hi2.run(i_) @ &m : res] - Pr[Hi3.run(i_) @ &m : res] | 
  <=
  maxr Pr[ Hi2.run(i_) @ &m : Bad.bad] Pr[ Hi3.run(i_) @ &m : Bad.bad].
proof. byupto. qed.

local lemma Hi2_bad &m i_ : 0 <= i_ => Pr[ Hi2.run(i_) @ &m : Bad.bad] <= query_ctr%r * p_max_bound.
proof.
move=> hi.
fel 4 
    (b2i (Bad.i < Bad.cr)) 
    (fun x => query_ctr%r * p_max_bound) 
    1 
    Bad.bad
    [O_Reprogrammer2i2.repro :   ((if p_max p <= p_max_bound then O_Reprogrammer.se else false) 
                              /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ fsize RO.m <= query_ctr)] => //.
+ by rewrite sumri_const.
+ smt().
+ auto => /> /#.
+ proc; wp.
  rcondt ^if; 1: by auto.
  rcondf ^if; 1: by auto => /#.
  rcondt ^if; 1: by auto.
  wp; seq 3 : (x \in RO.m) (query_ctr%r * p_max_bound) 1%r _ 0%r (!Bad.bad) => //.
  + by auto.
  + rnd (fun p => p \in RO.m); auto.
    move=> &hr /> _ _ _ hmax _ _ hsz.
    apply (ler_trans (mu p{hr} (fun (p0 : in_t ) => exists x, dom RO.m{hr} x /\ x = p0))).
    + by apply mu_le => /> x0 *; exists x0.
    apply (ler_trans ((fsize RO.m{hr})%r * p_max_bound)).
    apply: Mu_mem.mu_mem_le_fsize.
    + move=> x hx /=; apply: ler_trans hmax; move: (pmax_upper_bound p{hr} x) => /#.
    by apply ler_wpmul2r; smt(pmax_ge0). 
  by rcondt ^if; auto; conseq (: _ ==> false).
+ move=> c.
  proc.
  rcondt ^if; 1: by auto.
  by wp; conseq (: _ ==> true) => //; smt().
move=> b c; proc.
seq 2: (   ! (O_Reprogrammer.se /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ FSet.card (fdom RO.m) <= query_ctr) 
        /\ Bad.bad = b 
        /\ b2i (Bad.i < Bad.cr) = c); 1: by auto.
wp; if; last by auto.
seq 1 : (#pre); 1: by auto.
wp; if; 1: by conseq (: _ ==> true) => // /#.
by rcondf ^if; auto => /#. 
qed.

local lemma Hi3_bad &m i_ :
     0 <= i_ 
  => Pr[ Hi3.run(i_) @ &m : Bad.bad] 
     <= 
     query_ctr%r * p_max_bound.
proof.
move=> hi.
fel 4 
    (b2i (Bad.i < Bad.cr)) 
    (fun x => query_ctr%r * p_max_bound) 
    1 
    Bad.bad
    [O_Reprogrammer2i3.repro :   ((if p_max p <= p_max_bound then O_Reprogrammer.se else false) 
                              /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ fsize RO.m <= query_ctr)] => //.
+ by rewrite sumri_const.
+ smt().
+ auto => /> /#.
+ proc; wp.
  rcondt ^if; 1: by auto.
  rcondf ^if; 1: by auto => /#.
  rcondt ^if; 1: by auto.
  wp; seq 3 : (x \in RO.m) (query_ctr%r * p_max_bound) 1%r _ 0%r (!Bad.bad) => //.
  + by auto.
  + rnd; auto.
    move=> &hr /> _ _ _ hmax _ _ hsz.
    apply (ler_trans (mu p{hr} (fun (p0 : in_t) => exists x, dom RO.m{hr} x /\ x = p0))).
    + by apply mu_le => /> x0 *; exists x0.
    apply (ler_trans ((fsize RO.m{hr})%r * p_max_bound)).
    apply: Mu_mem.mu_mem_le_fsize.
    + by move=> x hx /=; apply: ler_trans hmax;  move: (pmax_upper_bound p{hr} x) => /#.
    by apply ler_wpmul2r; smt(pmax_ge0). 
  by rcondt ^if; auto; conseq (: _ ==> false).
+ move=> c.
  proc.
  rcondt ^if; 1: by auto.
  by wp; conseq (: _ ==> true) => //; smt().
move=> b c. 
proc.
seq 2: (! (O_Reprogrammer.se /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ FSet.card (fdom RO.m) <= query_ctr) /\
             Bad.bad = b /\ b2i (Bad.i < Bad.cr) = c); 1: by auto.
wp; if; last by auto.
seq 1 : (#pre); 1: by auto.
wp; if; 1: by conseq (: _ ==> true) => // /#.
by rcondf ^if; auto => /#.
qed.

local module O_Reprogrammer2i4 (O: RO) : Oracleir_t = {
  import var Bad
  include var O_Reprogrammer(O_Programmable2S(O)) [-repro]
  
  var x_ : in_t

  proc repro(p: pT) : in_t = {
    var x : in_t;
    var y : out_t;
    
    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i <= cr) {
        y <$ dout;
        O_Programmable2S(O).set(x,y);
      }
      cr <- cr + 1;
    } 
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module Hi4 (O:RO) = {
  import var Bad
  
  module OP = O_Programmable2S(O)
  module OR = O_Reprogrammer2i4(O)
 
  proc distinguish (i0: int) : bool = {
    var b' : bool;
    
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    
    OP.init();
    OR.init(false);
    
    b' <@ A(OP, OR).distinguish();
    
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local lemma Hi3_Hi4 &m i_: 
     0 <= i_ 
  => Pr[Hi3.run(i_) @ &m : res] 
     = 
     Pr[MainD(Hi4,RO).distinguish(i_) @ &m : res].
proof.
move=> hi. 
byequiv => //. 
proc.
inline *; wp.
call (:   ={O_Programmable.ch, glob O_Reprogrammer, Bad.i, Bad.cr, Bad.co} 
       /\ if (Bad.cr <= Bad.i){1} 
          then    ={RO.m, O_Programmable.prog_list} 
               /\ O_Programmable.prog_list{1} = [] 
               /\ (fsize RO.m <= Bad.co <= query_ctr){1}
          else    ((O_Reprogrammer2i2.x_ \in RO.m){1} 
               /\ O_Programmable.prog_list{2} = (rcons O_Programmable.prog_list (O_Reprogrammer2i2.x_, oget RO.m.[O_Reprogrammer2i2.x_])){1} 
               /\ eq_except (pred1 O_Reprogrammer2i2.x_{1}) RO.m{1} RO.m{2})).
+ proc.
  sp; wp; if => //.
  inline *; auto => |> &1 &2. 
  case: (Bad.cr{2} <= Bad.i{2}) => |> 4? r ?.
  + by rewrite fsize_set /b2i => /> /#.
  rewrite -!cats1 assoc_cat.
  by case: (assocP O_Programmable.prog_list{1} x{2}) => />; smt(mem_set get_setE).
+ proc. 
  wp; seq 2 2 : (#pre /\ ={x}); 1: by auto.
  if => //.
  seq 1 1: (#pre /\ ={x}); 1: by auto.
  if{1}.
  + rcondt{2} ^if; 1: by auto => /#.
    by inline *; auto => />; smt().
  if{1}.
  + rcondt{2} ^if; 1: by auto.
    by sp 1 0; inline *; if{1}; auto; smt(get_setE remE).  
  by rcondf{2} ^if; auto => /> /#. 
  conseq />; 1: by smt().
by auto => />; rewrite fsize_empty ge0_queryctr.
qed.

local lemma Hi4_RO_FunRO &m i_: 
  Pr[MainD(Hi4,RO).distinguish(i_) @ &m : res] 
  = 
  Pr[MainD(Hi4,FunRO).distinguish(i_) @ &m : res].
proof.
have <- : Pr[MainD(Hi4, FinRO).distinguish(i_) @ &m : res] = 
          Pr[MainD(Hi4, FunRO).distinguish(i_) @ &m : res]
  by  apply (pr_FinRO_FunRO_D _ Hi4 &m i_ (fun b => b));smt(dout_ll).
by rewrite (pr_RO_FinRO_D _ Hi4 &m i_ (fun b => b));smt(dout_ll).
qed.

local lemma Hi4_Hi &m i_ : 
  Pr[MainD(Hi4,FunRO).distinguish(i_) @ &m : res] 
  = 
  Pr[Hi.main(i_) @ &m : res].
proof. 
byequiv => //; proc; inline *. 
by wp;sim;auto => />.
qed.

local lemma rom_reprogramming1 &m i_ : 
     0 <= i_ 
  => `| Pr[Hi.main(i_ + 1) @ &m : res] - Pr[Hi.main(i_) @ &m : res] | 
     <= 
     query_ctr%r * p_max_bound.
proof.
move=> hi; rewrite (Hip1_Hi1 &m i_) (Hi1_FunRO_RO  &m i_) (Hi1_LRO_Hi2 &m i_).
rewrite -(Hi4_Hi &m i_) -(Hi4_RO_FunRO &m i_) -(Hi3_Hi4 &m i_) 1://.
by move: (Hi2_Hi3 &m i_) (Hi2_bad &m i_) (Hi3_bad &m i_) => /#.
qed.

(* ----------------------------------------------------- *)

lemma Bound_IND_Repro &m : 
     hoare[A(O_Programmable(FunRO), O_Reprogrammer(O_Programmable(FunRO))).distinguish : 
             O_Programmable.ch = 0 /\ O_Reprogrammer.ctr = 0 /\ O_Reprogrammer.se 
             ==> O_Programmable.ch <= query_ctr /\ 
             O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se]
  => `| Pr[IND_Repro(FunRO, A).main(false) @ &m : res] - 
        Pr[IND_Repro(FunRO, A).main(true) @ &m : res] |
      <= 
      rep_ctr%r * query_ctr%r * p_max_bound. 
proof.
move=> Hquery.
rewrite 2!(Pr_count &m _ Hquery) 2!(Pr_Game_Game1 &m) 2!(Pr_Game1_Game2 &m).
rewrite Hi_true Hi_false.
rewrite (telescoping_sum_down (fun i => Pr[Hi.main(i) @ &m : res]) 0 rep_ctr ge0_repctr) /=.
apply (ler_trans (bigi predT (fun (i : int) => `|Pr[Hi.main(i + 1) @ &m : res] - Pr[Hi.main(i) @ &m : res]|) 0 rep_ctr)).
+ by apply big_normr.
apply (ler_trans (bigi predT (fun (i : int) => query_ctr%r * p_max_bound) 0 rep_ctr)).
+ by apply ler_sum_seq => i_ /mem_range |> *; apply (rom_reprogramming1 &m i_).
by rewrite sumri_const 1:ge0_repctr /#.
qed.

end section.

end Adaptive.

*)

(**
  Non-adaptive reprogramming
  The adversary is double-stage, getting access to the original oracle in both
  stages. Reprogramming of the oracle is performed by the game in between
  the two stages. Only queries of the first stage are counted.
**)
theory NonAdaptive.

module type Oracleip_t = {
  include RO [ init, get, set]
  proc oc(x : in_t) : out_t
}.

module type Oraclep_t = {
  include Oracleip_t [-init]
}.

module O_Programmable(O : RO) : Oraclep_t = {
   var prog_list : (in_t * out_t) list  
   var ch : int

   proc init() : unit = {
     prog_list <- [];
     ch <- 0;
   }

  proc get(x : in_t): out_t = {
    var r,c : out_t;
    var tmp : out_t option;

    r <@ O.get(x);

    tmp <- assoc prog_list x;
    c <- if tmp = None then r else oget tmp;

    return c; 
  }

  proc oc(x : in_t) : out_t = {
    var c : out_t;
    
    ch <- ch + 1;
    
    c <@ get(x);
    
    return c;
  }
  
  proc set (x : in_t, y : out_t) : unit = {
    prog_list <- (x, y) :: prog_list;
  }
}.

module type Adv_INDNARepro(O : Oraclep_t) = {
  proc pick() : pT list {O.oc}
  proc distinguish(xs : in_t list) : bool {O.get}
}.

module IND_NARepro(O : RO, A : Adv_INDNARepro) = {
  module OP = O_Programmable(O)
 
  proc main(b : bool, n : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;
    
    O.init();
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    while (size xs < min (size ds) n) {
      x <$ nth witness ds (size xs);
      
      if (b) {
        y <$ dout;
        OP.set(x, y);
      }
      
      xs <- rcons xs x;
    }
    
    b' <@ A(OP).distinguish(xs);
    
    return b';
  } 
}.

op good_ds(ds : pT list) = 
   all ((>=) p_max_bound) (map p_max ds) /\
   all (is_lossless) ds.

section.

declare module A <: Adv_INDNARepro {-IND_NARepro, -FunRO, -RO, -FRO}.

declare op rep_ctr : { int | 0 <= rep_ctr } as ge0_repctr.
declare op query_ctr : { int | 0 <= query_ctr } as ge0_queryctr.

local module Bad = { 
  var bad : bool
  var co : int
  var i  : int
}.

local module O_Programmable1 (O : RO) : Oracleip_t = {
  include var O_Programmable(O) [-oc]
  import var Bad
 
  proc oc(x : in_t): out_t = {
    var c : out_t;

    ch <- ch + 1; 

    c <- witness;
    if (co < query_ctr) { 
      c <@ get(x);
      co <- co + 1;
    } else {
      bad <- true;
      c <@ get(x);
      co <- co + 1;
    }
        
    return c; 
  }

}.

local module O_Programmable2 (O: RO) : Oracleip_t = {
  include var O_Programmable(O) [-oc]
  import var Bad
 
  proc oc(x : in_t): out_t = {
    var c : out_t;

    ch <- ch + 1; 

    c <- witness;
    if (co < query_ctr) { 
      c <@ get(x);
      co <- co + 1;
    } else {
      bad <- true;
    }
        
    return c; 
  }

}.

local module O_Programmable2S (O: RO) : Oracleip_t = {
  include var O_Programmable(O) [-oc]
  import var Bad

  proc oc(x : in_t): out_t = {
    var c : out_t;
    var tmp : out_t option;

    c <- witness;
    if (co < query_ctr) { 
      c <@ get(x);
      co <- co + 1;
    } 

    ch <- ch + 1; 
    
    return c; 
  }

}.

local module IND_NARepro1(O : RO, A : Adv_INDNARepro) = {

  import var Bad
  
  module OP = O_Programmable1(O)
 
  proc main(b : bool, n : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;

    bad <- false; co <- 0;
    
    O.init();
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    if (good_ds ds) {
       while (size xs < min (size ds) n) {
         x <$ nth witness ds (size xs);
         if (b) {
           y <$ dout;
           OP.set(x, y);
         }
        xs <- rcons xs x;
       }
    }
    
    b' <@ A(OP).distinguish(xs);
    
    return b';
  } 
}.

local module IND_NARepro2(O : RO, A : Adv_INDNARepro) = {

  import var Bad
  
  module OP = O_Programmable2(O)
 
  proc main(b : bool, n : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;

    bad <- false; co <- 0;
    
    O.init();
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    if (good_ds ds) {
      while (size xs < min (size ds) n) {
        x <$ nth witness ds (size xs);
      
        if (b) {
          y <$ dout;
          OP.set(x, y);
        }
       xs <- rcons xs x;
      }
    }

    b' <@ A(OP).distinguish(xs);
    
    return b';
  } 
}.


local lemma Pr_count &m (b : bool) : 
     hoare[A(O_Programmable(FunRO)).pick : 
             O_Programmable.ch = 0 
             ==> 
             O_Programmable.ch <= query_ctr  /\ good_ds res]
  => Pr[IND_NARepro(FunRO, A).main(b,rep_ctr) @ &m : res] 
     = 
     Pr[IND_NARepro(FunRO,A).main(b,rep_ctr) @ &m : res /\ O_Programmable.ch <= query_ctr].
proof.
move=> hhoare.
byequiv => //.
conseq (: _ ==> ={res, O_Programmable.ch}) 
       (: true ==> O_Programmable.ch <= query_ctr) 
       _ => //; 2: by sim.
proc; seq 3: #post; last by conseq />;auto.
by call hhoare; inline *; auto => /=.
qed.

local lemma hequiv : 
     equiv[ A(O_Programmable(FunRO)).pick ~ A(O_Programmable1(FunRO)).pick : 
        ={O_Programmable.ch, O_Programmable.prog_list, FunRO.f, glob A} ==> 
         ={O_Programmable.ch, O_Programmable.prog_list, FunRO.f, glob A,res}].
proc (={O_Programmable.ch, O_Programmable.prog_list, FunRO.f});1,2:smt(). 
proc. 
seq 1 2 : #pre; 1: by auto.
by if{2};auto;sim.
qed.

local lemma hoare2equiv : 
     hoare[A(O_Programmable(FunRO)).pick : 
             O_Programmable.ch = 0 
             ==> 
             O_Programmable.ch <= query_ctr  /\ good_ds res] =>
     equiv[ A(O_Programmable(FunRO)).pick ~ A(O_Programmable1(FunRO)).pick : ={O_Programmable.ch, 
                  O_Programmable.prog_list, FunRO.f, glob A} /\ 
            O_Programmable.ch{1} = 0 ==> 
       ={O_Programmable.ch, O_Programmable.prog_list, FunRO.f, glob A,res} /\ 
        good_ds res{2}] 
      by move => hhoare; conseq hequiv hhoare;smt().

local lemma Pr_Game_Game1 &m _b : 
     hoare[A(O_Programmable(FunRO)).pick : 
             O_Programmable.ch = 0 
             ==> 
             O_Programmable.ch <= query_ctr  /\ good_ds res] =>
  Pr[IND_NARepro(FunRO,A).main(_b,rep_ctr) @ &m:res /\  O_Programmable.ch <= query_ctr] =
  Pr[IND_NARepro1(FunRO,A).main(_b,rep_ctr) @ &m:res /\  O_Programmable.ch <= query_ctr].
proof.
move=> hhoare.
byequiv => //.
proc; sim 5 7.
seq 4 6 : (b{2} = _b /\ n{2} = rep_ctr /\ xs{1} = [] /\ ={b,n,xs,O_Programmable.ch, O_Programmable.prog_list, FunRO.f, glob A,ds} /\ good_ds ds{2}). 
+ wp;call (hoare2equiv hhoare).
  by inline *;auto.

rcondt{2} 1;1: by auto.
while(#post /\ ={b,ds,n} /\ n{2} = rep_ctr /\ size xs{2} <= min (size ds{2}) n{2}). 
  seq 1 1 : (#pre /\ ={x}); 1: by auto.
  by if;[by auto| | ]; inline *;auto;smt(size_rcons).

by auto => />; smt(size_ge0 ge0_repctr).
qed.

local lemma Pr_Game1_Game2 &m b: 
  Pr[IND_NARepro1(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr] =
  Pr[IND_NARepro2(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr].
proof.
have: 
  `| Pr[IND_NARepro1(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr] -
     Pr[IND_NARepro2(FunRO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr] | 
  <=
  RealOrder.maxr Pr[IND_NARepro1(FunRO,A).main(b) @ &m: (res /\ O_Programmable.ch <= query_ctr) /\ Bad.bad] 
                 Pr[IND_NARepro2(FunRO,A).main(b) @ &m: (res /\ O_Programmable.ch <= query_ctr) /\ Bad.bad].
+ byupto.
have ->: 
  Pr[IND_NARepro1(FunRO, A).main(b) @ &m : (res /\ O_Programmable.ch <= query_ctr) /\ Bad.bad] 
  = 
  0%r.
+ byphoare => //.
  hoare.
  proc. 
  seq 5 : (Bad.bad => ! (O_Programmable.ch <= query_ctr)); last first. 
  + call(:true); 1: by proc;inline *;auto.
    seq 1 : #pre;1: by auto. 
   if;2: by auto => /> /#.
    while (#pre). 
    + by conseq />;auto.
    by auto;smt().
  call (:   Bad.co <= O_Programmable.ch 
          /\ (Bad.bad => ! (O_Programmable.ch <= query_ctr))). 
  + by proc; sp; wp; if; auto; call (: true); auto => /#.
  by inline *; auto => /#.
have -> /#: 
  Pr[IND_NARepro2(FunRO, A).main(b) @ &m : (res /\ O_Programmable.ch <= query_ctr) /\ Bad.bad] 
  = 
  0%r.
byphoare => //.
hoare.
proc.
seq 5 : (Bad.bad => ! (O_Programmable.ch <= query_ctr)); last first. 
  + call(:true); 1: by proc;inline *;auto.
    seq 1 : #pre;1: by auto. 
   if;2: by auto => /> /#.
  while (#pre). 
  + by conseq />;auto.
  by auto;smt().
call (:    Bad.co <= O_Programmable.ch 
       /\ (Bad.bad => ! (O_Programmable.ch <= query_ctr))). 
+ by proc; sp; wp; if; auto; 1: call (: true); auto => /#.
by inline *; auto => /#.
qed.

local module Hi = {
  import var Bad
  
  module OP = O_Programmable2S(FunRO)
 
  proc main(i0 : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;

    bad <- false; co <- 0; i <- i0;
    
    FunRO.init();
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    if (good_ds ds) {
      while (size xs < min (size ds) rep_ctr) {
        x <$ nth witness ds (size xs);
        if (i <= size xs) {
           y <$ dout;
           OP.set(x, y);
         }
        xs <- rcons xs x;
      }
    }
    
    b' <@ A(OP).distinguish(xs);
        
    return b' /\ O_Programmable.ch <= query_ctr;
  } 
}.

local lemma Hi_true &m : 
  Pr[IND_NARepro2(FunRO, A).main(true,rep_ctr) @ &m : res /\ O_Programmable.ch <= query_ctr]
  = 
  Pr[Hi.main(0) @ &m : res].
proof.
byequiv => //.
proc.
call (:   ={glob O_Programmable, FunRO.f, Bad.co}).
+ by sim />.
conseq />.
seq 6 7 : (Bad.i{2} = 0 /\ (b{1}, n{1}) = (true, rep_ctr) /\ 
    ={ds,xs,glob A,O_Programmable.ch, O_Programmable.prog_list,FunRO.f, Bad.co}).
+ wp;call(: ={O_Programmable.ch, O_Programmable.prog_list, FunRO.f, Bad.co});
     1: by proc; inline *; auto.
  by inline *;auto. 
if;1,3: by auto.
while (#post /\ n{1} = rep_ctr /\ ={ds} /\ Bad.i{2} = 0 /\ b{1}).
+ seq 1 1 : (#pre /\ ={x}); 1 : by auto.
  if;1,3: by auto.
  by inline *;auto.
by auto.
qed.

local lemma Hi_false &m : 
  Pr[IND_NARepro2(FunRO, A).main(false,rep_ctr) @ &m : res /\ 
                                         O_Programmable.ch <= query_ctr]
  = 
  Pr[Hi.main(rep_ctr) @ &m : res].
proof.
byequiv => //.
proc.
call (:   ={glob O_Programmable, FunRO.f, Bad.co}).
+ by proc;inline*;auto.
conseq />.
seq 6 7 : (Bad.i{2} = rep_ctr /\ xs{1} = [] /\ (b{1}, n{1}) = (false, rep_ctr) /\ 
    ={ds,xs,glob A,O_Programmable.ch, O_Programmable.prog_list,FunRO.f, Bad.co}).
+ wp;call(: ={O_Programmable.ch, O_Programmable.prog_list, FunRO.f, Bad.co});
     1: by proc; inline *; auto.
  by inline *;auto => />. 
if;1,3: by auto.

while (#post /\ n{1} = rep_ctr /\ ={ds} /\ size xs{2} <= rep_ctr /\ Bad.i{2} = rep_ctr /\ !b{1}).
+ seq 1 1 : (#pre /\ ={x}); 1 : by auto.
  if;1,3: by auto;smt(size_rcons). 
  by inline *;auto.
by inline *;auto; smt(ge0_repctr).
qed.

local module Hi1(O : RO) = {
  import var Bad
  var x_ : in_t
  
  module OP = O_Programmable2S(O)
 
  proc distinguish(i0 : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;

    bad <- false; co <- 0; i <- i0;
    
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    if (good_ds ds) {
      while (size xs < min (size ds) rep_ctr) {
        x <$ nth witness ds (size xs);
        if (i + 1 <= size xs) {
          y <$ dout;
          OP.set(x, y);
        }
        else {
          if (i = size xs) {
            x_ <- x;
            y <@ O.get(x);
          }
       }
       xs <- rcons xs x;
     }
    }
    
    b' <@ A(OP).distinguish(xs);
        
    return b' /\ O_Programmable.ch <= query_ctr;
  } 
}.

local lemma Hip1_Hi1 &m i_ : 
  Pr[Hi.main(i_ + 1) @ &m : res] 
  = 
  Pr[MainD(Hi1,FunRO).distinguish(i_) @ &m : res].
proof.
byequiv => //. 
proc. 
inline *;wp;conseq />.
call(: ={FunRO.f,O_Programmable.prog_list});1:by sim.
swap {1} 4 -3.

seq 8 9 : (={xs,glob A,ds,Bad.co,FunRO.f,O_Programmable.prog_list,O_Programmable.ch} /\ Bad.i{1} = Bad.i{2} + 1 /\ xs{1} = []).
+ wp;call(: ={FunRO.f, glob O_Programmable, Bad.co});1:by sim.
  by auto.

conseq   (: ={xs, FunRO.f, O_Programmable.prog_list, O_Programmable.ch}); 1: by smt().

if;1,3: by auto => />;smt(size_rcons).
while (#post /\ ={ds} /\ Bad.i{1} = Bad.i{2} + 1 /\ size xs{2} <= rep_ctr).
+ seq 1 1 : (#pre /\ x{1} = x0{2}); 1 : by auto.
  if;1:by auto;smt(). 
  by auto;smt(size_rcons).
by auto;smt(size_rcons).

by auto; smt(ge0_repctr).
qed.

local lemma Hi1_FunRO_RO  &m i_ : 
  Pr[MainD(Hi1,FunRO).distinguish(i_) @ &m : res] 
  =
  Pr[MainD(Hi1,RO).distinguish(i_) @ &m : res].
proof.
have <- : Pr[MainD(Hi1, FinRO).distinguish(i_) @ &m : res] = 
          Pr[MainD(Hi1, FunRO).distinguish(i_) @ &m : res]
  by  apply (pr_FinRO_FunRO_D _ Hi1 &m i_ (fun b => b));smt(dout_ll).
by rewrite (pr_RO_FinRO_D _ Hi1 &m i_ (fun b => b));smt(dout_ll).
qed.

local module Hi2 = {
  import var Bad
  var x_ : in_t option
  
  module OP = O_Programmable2S(RO)
 
  proc run(i0 : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;

    bad <- false; co <- 0; i <- i0; x_ <- None;
    
    RO.init();
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    if (good_ds ds) {
      while (size xs < min (size ds) rep_ctr) {
        x <$ nth witness ds (size xs);      
        if (i + 1 <= size xs) {
          y <$ dout;
          OP.set(x, y);
        }
        else {
          if (i = size xs) {
             x_ <- Some x;
             if (! x \in RO.m) {
               y <@ RO.get(x);
             } else {
               bad <- true;
               y <@ RO.get(x);
             }
          }
       }
        xs <- rcons xs x;
      }
    }
    
    b' <@ A(OP).distinguish(xs);
        
    return b' /\ O_Programmable.ch <= query_ctr;
  } 
}.

local module Hi3 = {
  import var Bad
  
  module OP = O_Programmable2S(RO)
 
  proc run(i0 : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;

    bad <- false; co <- 0; i <- i0; Hi2.x_ <- None;
    
    RO.init();
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    if (good_ds ds) {
      while (size xs < min (size ds) rep_ctr) {
        x <$ nth witness ds (size xs);      
        if (i + 1 <= size xs) {
          y <$ dout;
          OP.set(x, y);
        }
        else {
          if (i = size xs) {
             Hi2.x_ <- Some x;
             if (! x \in RO.m) {
               y <@ RO.get(x);
             } else {
               bad <- true;
               RO.m <- rem RO.m x;
               y <@ RO.get(x); 
             }
          }
        }
        xs <- rcons xs x;
      }
    }
    
    b' <@ A(OP).distinguish(xs);
        
    return b' /\ O_Programmable.ch <= query_ctr;
  } 
}.


local lemma Hi1_LRO_Hi2  &m i_ : Pr[ MainD(Hi1,RO).distinguish(i_) @ &m : res] = Pr[Hi2.run(i_) @ &m : res].
proof.
byequiv => //.
proc. 
inline *;wp;conseq />.
call(: ={RO.m,O_Programmable.prog_list});1:by sim.

seq 9 9 : (={xs,glob A,ds,Bad.co,Bad.i,RO.m,O_Programmable.prog_list,O_Programmable.ch} /\ xs{1} = []).
+ wp;call(: ={RO.m, glob O_Programmable, Bad.co});1:by sim.
  by auto.

conseq   (: ={xs, RO.m, O_Programmable.prog_list, O_Programmable.ch}); 1: by smt().

if;1,3: by auto => />;smt(size_rcons).
while (#post /\ ={ds,Bad.i} /\ size xs{2} <= rep_ctr).
+ seq 1 1 : (#pre /\ x0{1} = x{2}); 1 : by auto.
  if;1:by auto;smt(). 
  by auto;smt(size_rcons).

if;1:by auto.
+ sp;if{2}.
  + rcondt{1} 2; 1: by auto.
    by auto;smt(size_rcons).
  rcondf{1} 2; 1: by auto.
  by auto;smt(size_rcons).
+ by auto;smt(size_rcons).

by auto; smt(ge0_repctr).
qed.

local lemma Hi2_Hi3 &m i_ : 
  `| Pr[ Hi2.run(i_) @ &m : res] - Pr[Hi3.run(i_) @ &m : res] | 
  <=
  maxr Pr[ Hi2.run(i_) @ &m : Bad.bad] Pr[ Hi3.run(i_) @ &m : Bad.bad].
proof. byupto. qed.

local lemma Hi2_bad &m i_ : 
  0 <= i_ => 
  (forall (O <: Oraclep_t{-A} ), islossless O.oc => islossless A(O).pick) =>
  (forall (O <: Oraclep_t{-A}), islossless O.get => islossless A(O).distinguish) =>
  Pr[ Hi2.run(i_) @ &m : Bad.bad] <= 
   query_ctr%r * p_max_bound.
proof.
move=> hi Apll Adll.
case (p_max_bound = 0%r \/ query_ctr = 0).
+ move => H;elim H.
  + move =>pmax0;rewrite pmax0 /=.
    byphoare => //;hoare.
    proc;call(:true);1: by auto.
    seq 8 : (xs = [] /\ !Bad.bad); 1: by inline *;wp;call(: !Bad.bad);auto => />.
    if;2: by auto.
    while(!Bad.bad /\ good_ds ds).
    + seq 1 : (#pre /\ x \in nth witness ds (size xs)); 1: by auto. 
      case (Bad.i + 1 <= size xs); 1: by rcondt 1;inline *; auto.
      rcondf 1;1: by auto.
      case (Bad.i = size xs); 2: by rcondf 1;inline *; auto.
      rcondt 1;1: by auto.
      rcondt 2. 
      + inline *;auto => /> &hr ?H*. 
        have := all_nthP (fun (y0 : real) => y0 <= p_max_bound) (map p_max ds{hr}) witness;rewrite H  /= => H0.
        by smt(size_map pmax_gt0 nth_map size_ge0).
      by inline *;auto. 
    by inline *;auto. 

  move => qctr0;rewrite qctr0 /=.
  byphoare (: i0 = i_ ==> Bad.bad)=> //;hoare.
  proc;call(:true);1: by auto.
  seq 8 : (!Bad.bad /\ RO.m = empty /\ Bad.i = i_ /\ xs = []); last first.
  + if;2: by auto.
    while (!Bad.bad /\ Bad.i = i_ /\ (size xs <= Bad.i => RO.m = empty)).
    seq 1: (#pre /\ x \in nth witness ds (size xs)); 1:by auto.
    if;1: by inline *;auto; smt(size_rcons).
    if;2: by auto; smt(size_rcons).
    sp;if;1:by inline *;auto; smt(size_rcons).
    + by exfalso;smt(mem_empty).
    by auto.
  wp;call(:!Bad.bad /\ RO.m = empty /\ Bad.i = i_ /\ 0 <= Bad.co).
  + proc;inline *;rcondf 2; 1: by auto => /#.
    by auto.
  by inline *; auto.

move => bound1.
byphoare (: arg = i_ ==> Bad.bad) => //.
proc. 
seq 8 : (!Bad.bad /\ Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co /\
           size xs <= Bad.i /\ Bad.i = i_ /\ xs = [])
           (query_ctr%r * p_max_bound ).
+ by auto.
+ wp;call (: Bad.co = 0 /\ RO.m = empty ==> Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co).
  conseq (: _ ==> _ : =1%r); 1: by smt(). 
  proc (Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co).
  + by move => />;rewrite fdom0 fcards0 /=;smt(ge0_queryctr).
  + by smt().
  + by apply Apll.
  + proc;inline *;sp;if;2:by auto.
    by auto => />;smt(dout_ll fdom_set fcardU fcard_eq1 fcard_ge0). 
  by inline *;auto.

+ if;last first. 
  hoare;1 : by  smt(ge0_queryctr ge0_pmaxbound).
  call(: !Bad.bad);1: by conseq />; auto.
  by auto.

splitwhile 1 : (size xs < Bad.i).
unroll 2.
seq 1 : (!Bad.bad /\ Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co /\ good_ds ds /\
           size xs <= Bad.i /\ Bad.i = i_ /\
           !(size xs < Bad.i /\ size xs < min (size ds) rep_ctr))
           (query_ctr%r * p_max_bound ) .
+ by auto. 
+ conseq (:_ ==> _ : <=1%r); 1: by  move => &hr _;  by smt(ge0_queryctr ge0_pmaxbound). 
  while(!Bad.bad /\ size xs <= Bad.i /\ good_ds ds /\
  Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co) (min (size ds) rep_ctr - size xs); last first.
  + inline *;sp;wp. 
    conseq (: _ ==> Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co). 
   by auto.
 by auto.  

+ move => z.
  seq 1 : #pre; 1: by auto.
  + by auto => /> *;smt(all_nthP size_map nth_map size_ge0).
  + if;1: by inline*;auto;smt(size_rcons).
    if;2: by auto;smt(size_rcons).
    sp;if;by inline *;auto;smt(size_rcons).
  + by hoare;auto. 
  by auto.

+ if;last first.
  seq 1 : #post (query_ctr%r * p_max_bound) 1%r 1%r 0%r.
  + by auto.  
  + hoare; 1: by smt(ge0_pmaxbound ge0_queryctr).
    while(!Bad.bad /\ ! size xs < min (size ds) rep_ctr).
    + by exfalso;smt().
    by auto.
  + by auto.
  + hoare. 
    call(:!Bad.bad); last by auto.
    by proc;inline *;auto. 
  by smt().

  rcondf 2;1: by auto;smt().
  rcondt 2;1: by auto;smt().
  seq 1 : (x \in RO.m) (query_ctr%r * p_max_bound) 1%r 1%r 0%r (#pre).
  + by auto.
  + rnd (fun xx => xx \in RO.m).
    auto => /> &hr???H????.
    rewrite (mu_eq _ (dom RO.m{hr}) (mem (fdom RO.m{hr})));
     1: by move => x'; rewrite -mem_fdom.
    have := Mu_mem.mu_mem_le (fdom RO.m{hr}) ((nth witness ds{hr} (size xs{hr}))) p_max_bound _; last by smt(ge0_queryctr ge0_pmaxbound).
    move => x _.  
    have := all_nthP (fun (y0 : real) => y0 <= p_max_bound) (map p_max ds{hr}) witness;rewrite H  /= => H0.
    by smt(nth_map pmax_upper_bound size_map  size_ge0).

  + rcondf 2; 1: by auto.
    conseq (: _ ==> _: =1%r).
    call(: Bad.bad).
    + by proc;inline*;auto;smt(dout_ll). 
    +  while(Bad.bad /\ good_ds ds) (min (size ds) rep_ctr - size xs); last first.
      + by inline *; auto => />;smt(dout_ll). 
      + move => *.
        seq 1: #pre.
        + by auto.
        + by auto => /> *;smt(all_nthP size_map nth_map size_ge0).
        if;1: by inline*;auto => />;smt(dout_ll size_rcons).
        if;2: by auto => />;smt(size_rcons).
        sp;if;by inline *;auto => />;smt(dout_ll size_rcons).
    + hoare. by auto. 
    + by smt().
  + hoare.
    call(: !Bad.bad);1: by proc;inline *;auto.
    while(!Bad.bad /\ Bad.i + 1 <= size xs); last first.
    + inline *;sp;wp.
      if;2: by auto.
      by auto => />;smt(dout_ll size_rcons). 
    seq 1 : #pre; 1: by auto.
    if;1: by inline*;auto;smt(size_rcons).
    if;2: by auto;smt(size_rcons).
    sp;if;by inline*;auto;smt(size_rcons).
    by smt().

+ hoare.
  while(!Bad.bad /\  size xs <= Bad.i  /\ Bad.i = i_ /\ good_ds ds /\
       Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co); last by auto => /> /#.
  seq 1 : #pre; 1: by auto.
  if;1: by inline*;auto;smt(size_rcons).
  if;2: by inline*;auto;smt(size_rcons).
  sp;if;1: by inline*;auto => />.
  by inline *;auto => />.

+ by move => &hr _; smt(ge0_queryctr ge0_pmaxbound).


+ hoare.
  wp;call (: Bad.co = 0 /\ RO.m = empty ==> Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co).
  proc (Bad.co <= query_ctr /\ card (fdom RO.m) <= Bad.co).
  + by move => />;rewrite fdom0 fcards0 /=;smt(ge0_queryctr).
  + by smt().
  + proc;inline *;sp;if;2:by auto.
    + by auto => />;smt(dout_ll fdom_set fcardU fcard_eq1 fcard_ge0). 
    by inline *;auto.

by move => &hr _; smt(ge0_queryctr ge0_pmaxbound).

qed.

local lemma Hi3_bad &m i_ :
     0 <= i_ 
  => (forall (O <: Oraclep_t{-A}), islossless O.get => islossless A(O).distinguish) 
  => Pr[ Hi3.run(i_) @ &m : Bad.bad] = 
     Pr[ Hi2.run(i_) @ &m : Bad.bad]. 
move => H All.
byequiv => />.
proc. 
seq 9 9 : (={Bad.bad}); last first.
+ conseq />.
  call{1}(:true ==> true); 1: by apply (All Hi3.OP); islossless.  
  call{2}(:true ==> true); 1: by apply (All Hi3.OP); islossless. 
  by auto.

seq 8 8 : (={Bad.bad,ds,Bad.i,ds,xs, RO.m, glob A} /\ !Bad.bad{1});
 1: by sp 1 1; conseq />;sim.

if;1,3: by auto.

while (={Bad.bad,ds,Bad.i,ds,xs} /\ (!Bad.bad{1} => ={RO.m, glob A}));last by auto.

conseq (: (={Bad.bad, ds, Bad.i, ds, xs} /\ (!Bad.bad{1} => ={RO.m, glob A}))); 1: by smt().
seq 1 1 : (#pre /\ ={x}); 1: by auto.
if; 1: by auto.
+ by inline *; auto. 
if; 1,3: by auto.
case (!Bad.bad{1}). 
+ sp;if;1: by auto => /#. 
  + by inline*;auto => /> /#.
  by inline*;auto.
by sp;if{1};if{2};inline*;auto;smt().
qed.

local module Hi4(O : RO) = {
  import var Bad
  
  module OP = O_Programmable2S(O)
 
  proc distinguish(i0 : int) : bool = {
    var b' : bool;
    var x : in_t;
    var y : out_t;
    var ds : pT list;
    var xs : in_t list;

    bad <- false; co <- 0; i <- i0;
    
    OP.init();
    
    ds <@ A(OP).pick();

    xs <- [];
    if (good_ds ds) {
      while (size xs < min (size ds) rep_ctr) {

        x <$ nth witness ds (size xs);
      
        if (i <= size xs) {
          y <$ dout;
          OP.set(x, y);
        }
        xs <- rcons xs x;
      }
    }
    
    b' <@ A(OP).distinguish(xs);
        
    return b' /\ O_Programmable.ch <= query_ctr;
  } 
}.


local lemma Hi3_Hi4 &m i_: 
     0 <= i_ 
  => Pr[Hi3.run(i_) @ &m : res] 
     = 
     Pr[MainD(Hi4,RO).distinguish(i_) @ &m : res].
proof.
move=> hi. 
byequiv => //. 
proc.
inline *;wp. 
seq 9 9 : (={glob A,Bad.bad,Bad.i,Bad.co,RO.m,O_Programmable.prog_list,O_Programmable.ch,ds,ds,xs} /\
   Bad.i{1} = i_ /\ xs{1} = [] /\ Hi2.x_{1} = None /\ O_Programmable.prog_list{1} = []).
+ wp;call(: ={O_Programmable.ch,Bad.i,RO.m,O_Programmable.prog_list,Bad.co});1: by sim.
  by auto. 

if;[ by auto | |];last first.

+ call(: ={RO.m,O_Programmable.prog_list} /\ O_Programmable.prog_list{1} = []);
    1: by proc; inline *;auto => />. 
  by auto.

call(: ={O_Programmable.ch} /\ 
   if (Hi2.x_ = None){1} 
   then ={RO.m, O_Programmable.prog_list} /\ O_Programmable.prog_list{1} = []
   else ((oget Hi2.x_{1} \in RO.m){1}  
      /\ fdom RO.m{1} = fdom RO.m{2} `|` fset1 (oget Hi2.x_{1}) 
      /\ O_Programmable.prog_list{2} = 
            (rcons O_Programmable.prog_list (oget Hi2.x_, oget RO.m.[oget Hi2.x_])){1} 
      /\ eq_except (pred1 (oget Hi2.x_{1})) RO.m{1} RO.m{2})).
+ proc;inline*;auto => /> &1 &2  H r0 ?;  split.  
  + move => *;split. 
    + move => *;do split;2,3: by smt(mem_set fdom_set fsetUAC get_setE).
      case (Hi2.x_{1} = None); 1: by smt(get_setE).
      move => hnn;move : H; rewrite ifF 1:/# => [#??->?].
      rewrite -cats1 assoc_cat !get_setE /=. 
      by have := assocTP O_Programmable.prog_list{1} x{2};smt().
    + move => *;do split;2: by smt().
      + case (Hi2.x_{1} = None); 1: by smt(get_setE).
        move => hnn;move : H; rewrite ifF 1:/# => [#??->?].
        rewrite -cats1 assoc_cat !get_setE /=. 
        by have := assocTP O_Programmable.prog_list{1} x{2};smt().
      by smt( fdom_set fsetUid fsetUA eq_except_setr).
    move => *;split;1: by smt().
    move => ?. 
    case (Hi2.x_{1} = None); 1: by smt(get_setE).
    move => hnn;move : H; rewrite ifF 1:/# => [#??->?].
    rewrite -cats1 assoc_cat /=. 
    by have := assocTP O_Programmable.prog_list{1} x{2};smt().

while(={O_Programmable.ch,glob A,xs,Bad.i,ds} /\ 
   if (Hi2.x_ = None){1} 
          then  O_Programmable.prog_list{1} = [] /\ ={RO.m, O_Programmable.prog_list} /\ size xs{1}  <= Bad.i{1}
          else ((oget Hi2.x_{1} \in RO.m){1} /\ fdom RO.m{1} = fdom RO.m{2} `|` fset1 (oget Hi2.x_{1}) /\ Bad.i{1} < size xs{1} 
               /\ O_Programmable.prog_list{2} = (rcons O_Programmable.prog_list (oget Hi2.x_, oget RO.m.[oget Hi2.x_])){1} 
               /\ eq_except (pred1 (oget Hi2.x_{1})) RO.m{1} RO.m{2})).

seq 1 1 : (#pre /\ x{1} = x0{2}); 1: by auto.
if {1}.
+ rcondt{2} 1; by auto => />;smt(size_rcons). 
  if {1}; last first. 
  + rcondf{2} 1;1: by auto;smt(size_rcons).
    by auto => />;smt(size_rcons).
  + rcondt{2} 1;1: by auto;smt(size_rcons).
    case(x{1} \notin RO.m{1}). 
    + rcondt{1} 2;1: by auto;smt(size_rcons).
      rcondt{1} 4;1: by auto;smt(size_rcons).
      auto => /> &1 &2 [#]??H??????;do split.
      + by smt(mem_set).
      + by rewrite fdom_set /#.
      + by smt(size_rcons).
      + by rewrite H get_setE /= /#.
      by smt(eq_except_setr).

    + rcondf{1} 2;1: by auto;smt(size_rcons).
      rcondt{1} 6; 1: by  auto; smt(mem_fdom mem_fdom_rem size_rcons).
      auto => /> &1 &2 [#]?H?H0?????;do split.
      + by smt(mem_set). 
      + by smt(fdom_set fdom_rem fsetP in_fsetU in_fsetD1 in_fset1).
      + by smt(size_rcons).
      + by rewrite -H0 H /= get_setE /=.
      by smt(@SmtMap).
by auto => /> /#.
qed.


local lemma Hi4_RO_FunRO &m i_: 
  Pr[MainD(Hi4,RO).distinguish(i_) @ &m : res] 
  = 
  Pr[MainD(Hi4,FunRO).distinguish(i_) @ &m : res].
proof.
have <- : Pr[MainD(Hi4, FinRO).distinguish(i_) @ &m : res] = 
          Pr[MainD(Hi4, FunRO).distinguish(i_) @ &m : res]
  by  apply (pr_FinRO_FunRO_D _ Hi4 &m i_ (fun b => b));smt(dout_ll).
by rewrite (pr_RO_FinRO_D _ Hi4 &m i_ (fun b => b));smt(dout_ll).
qed.

local lemma Hi4_Hi &m i_ : 
  Pr[MainD(Hi4,FunRO).distinguish(i_) @ &m : res] 
  = 
  Pr[Hi.main(i_) @ &m : res].
proof. 
byequiv => //; proc; inline *. 
wp;sim;auto => />.
qed.

local lemma rom_reprogramming1 &m i_ : 
     0 <= i_ =>
    (forall (O <: Oraclep_t{-A} ), islossless O.oc => islossless A(O).pick) =>
    (forall (O <: Oraclep_t{-A}), islossless O.get => islossless A(O).distinguish) =>
    `| Pr[Hi.main(i_ + 1) @ &m : res] - Pr[Hi.main(i_) @ &m : res] | 
     <= 
     query_ctr%r * p_max_bound.
proof.
move => ib Apll Adll.
rewrite (Hip1_Hi1 &m i_) (Hi1_FunRO_RO  &m i_) (Hi1_LRO_Hi2 &m i_).
rewrite -(Hi4_Hi &m i_) -(Hi4_RO_FunRO &m i_) -(Hi3_Hi4 &m i_) 1://.
by move: (Hi2_Hi3 &m i_) (Hi2_bad &m i_ ib Apll Adll) (Hi3_bad &m i_ ib Adll) => /#.
qed.

(* ----------------------------------------------------- *)


lemma Bound_IND_NARepro &m : 
    (forall (O <: Oraclep_t{-A} ), islossless O.oc => islossless A(O).pick) =>
    (forall (O <: Oraclep_t{-A}), islossless O.get => islossless A(O).distinguish) =>
     hoare[ A(O_Programmable(FunRO)).pick :
          O_Programmable.ch = 0 ==>
          O_Programmable.ch <= query_ctr /\  good_ds res]
  => `| Pr[IND_NARepro(FunRO, A).main(false, rep_ctr) @ &m : res] - 
        Pr[IND_NARepro(FunRO, A).main(true, rep_ctr) @ &m : res] |
      <= 
      rep_ctr%r * query_ctr%r * p_max_bound.
proof.
move=> Apll Adll Hquery.
rewrite 2!(Pr_count &m _ Hquery) 2!(Pr_Game_Game1 &m _ Hquery) 2!(Pr_Game1_Game2 &m).
rewrite Hi_true Hi_false.
rewrite (telescoping_sum_down (fun i => Pr[Hi.main(i) @ &m : res]) 0 rep_ctr ge0_repctr) /=.
apply (ler_trans (bigi predT (fun (i : int) => `|Pr[Hi.main(i + 1) @ &m : res] - Pr[Hi.main(i) @ &m : res]|) 0 rep_ctr)).
+ by apply big_normr.
apply (ler_trans (bigi predT (fun (i : int) => query_ctr%r * p_max_bound) 0 rep_ctr)).
+ by apply ler_sum_seq => i_ /mem_range |> *; apply (rom_reprogramming1 &m i_).
by rewrite sumri_const 1:ge0_repctr /#.
qed.

end section.
end NonAdaptive.
