require import AllCore List Int Distr RealExp SmtMap FinType StdOrder StdBigop PROM.
(*---*) import Bigreal.BRA Bigreal RField RealOrder.

type in_t.

type out_t.

type pT = in_t distr.

clone import FinType as FT_In with
  type t = in_t.

op [lossless] dout : out_t distr.

const p_max_bound : real.

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

(*
Replace while loop by sampling from djoin ds and while loop that reprograms.
Move to same game, but instead y and set, use RO.sample (PROM.ec) (both with b = true).
Bad event: sampled x is in previous queries from first adversary call (A.pick()).
Bound this bad event (try to use new ehoare logic if possible; similar example should exist in repo).
| Pr[G1 : E] - Pr[G2 : E] | <= Pr[G2 : bad], where G1 := IND_NARepro(true) and G2 := IND_NARepro(true) using RO.sample in the if statement.
Then, IND_NARepro(true) with RO = IND_NARepro(true) with LRO = IND_NARepro(false) with LRO or RO (doesn't matter because no reprogramming is done).
*)
section.

declare module A <: Adv_INDNARepro {-IND_NARepro, -FunRO}.

declare op rep_ctr : { int | 0 <= rep_ctr } as ge0_repctr.
declare op query_ctr : { int | 0 <= query_ctr } as ge0_queryctr.

lemma Bound_IND_NARepro &m : 
     hoare[A(O_Programmable(FunRO)).pick : 
             O_Programmable.ch = 0 
             ==> 
             O_Programmable.ch <= query_ctr /\ all ((>=) p_max_bound) (map p_max res)]
  => `| Pr[IND_NARepro(FunRO, A).main(false, rep_ctr) @ &m : res] - 
        Pr[IND_NARepro(FunRO, A).main(true, rep_ctr) @ &m : res] |
      <= 
      rep_ctr%r * query_ctr%r * p_max_bound.
proof.
admit.
qed.

end section.
end NonAdaptive.
