require import AllCore List Int Distr RealExp SmtMap FinType StdOrder StdBigop.
(*---*) import Bigreal.BRA Bigreal RField RealOrder.
require (*--*) ROM.

type in_t.

type out_t.

type pT = in_t distr.

clone import FinType as FT_In with
  type t <- in_t.

op [lossless] dout : out_t distr.

const p_max_bound : real.

clone import ROM as ROM_ with
  type in_t <- in_t,
  type out_t <- out_t,
  op dout <- fun _ => dout,
  type d_in_t <- int,
  type d_out_t <- bool
  
  proof *.
 
clone import ROM_.LazyEager as LE with 
  theory FinType <- FT_In
  
  proof *.
  
module type Oracleip_t = {
  include Oracle
  proc set(x : in_t, y : out_t) : unit
}.

module type Oraclep_t = {
  include Oracleip_t [-init]
}.

module O_Programmable(O : POracle) : Oraclep_t = {
   var prog_list : (in_t * out_t) list  
   var ch : int

   proc init() : unit = {
     prog_list <- [];
     ch <- 0;
   }

  proc o(x : in_t): out_t = {
    var r,c : out_t;
    var tmp : out_t option;

    r <@ O.o(x);

    ch <- ch + 1; 
    tmp <- assoc prog_list x;
    c <- if tmp = None then r else oget tmp;

    return c; 
  }

   proc set (x : in_t, y: out_t) : unit = {
     prog_list <- (x,y) :: prog_list;
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
  proc distinguish() : bool {O.o, OR.repro}
}.

module IND_Repro(O : Oracle, A : Adv_INDRepro) = {
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

declare module A <: Adv_INDRepro {-IND_Repro, -ERO, -Lazy.LRO}.

declare const rep_ctr : {int | 0 <= rep_ctr } as ge0_repctr.
declare const query_ctr : {int | 0 <= query_ctr } as ge0_queryctr.

local module Bad = { 
  var bad : bool
  var co : int
  var cr : int
  var i  : int
}.

local module O_Programmable1 (O : POracle) : Oracleip_t = {
  include var O_Programmable(O) [-o]
  import var Bad
 
  proc o(x : in_t): out_t = {
    var r, c : out_t;
    var tmp : out_t option;

    c <- witness;
    if (co < query_ctr) { 
      r <@ O.o(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;
      co <- co + 1;
    } else {
      bad <- true;
      r <@ O.o(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;      
      co <- co + 1;
    }
    
    ch <- ch + 1; 
    
    return c; 
  }

}.

local module O_Programmable2 (O: POracle) : Oracleip_t = {
  include var O_Programmable(O) [-o]
  import var Bad
 
  proc o(x : in_t): out_t = {
    var r, c : out_t;
    var tmp : out_t option;

    c <- witness;
    if (co < query_ctr) { 
      r <@ O.o(x);
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

local module O_Programmable2S (O: POracle) : Oracleip_t = {
  include var O_Programmable(O) [-o]
  import var Bad

  proc o(x : in_t): out_t = {
    var r, c : out_t;
    var tmp : out_t option;

    c <- witness;
    if (co < query_ctr) { 
      r <@ O.o(x);
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

local module IND_Repro1 (O: Oracle, A: Adv_INDRepro) = {
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

local module IND_Repro2 (O: Oracle, A: Adv_INDRepro) = {
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
     hoare[ A(O_Programmable(ERO),O_Reprogrammer(O_Programmable(ERO))).distinguish : 
             O_Programmable.ch = 0 /\ O_Reprogrammer.ctr = 0 /\ O_Reprogrammer.se 
             ==> O_Programmable.ch <= query_ctr /\ 
             O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] 
  => Pr[IND_Repro(ERO, A).main(b) @ &m : res] 
     = 
     Pr[IND_Repro(ERO,A).main(b) @ &m : res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se].
proof.
move=> hhoare.
byequiv => //.
conseq (: _ ==> ={res, O_Programmable.ch, O_Reprogrammer.ctr, O_Reprogrammer.se}) 
       (: true ==> O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) 
       _ => //; 2: by sim.
by proc; call hhoare; inline *; auto => /=.
qed.

local lemma Pr_Game_Game1 &m b : 
  Pr[IND_Repro(ERO,A).main(b) @ &m:res /\  O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] =
  Pr[IND_Repro1(ERO,A).main(b) @ &m:res /\  O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se].
proof.
byequiv => //.
proc.
call (:    ={glob ERO,  glob O_Reprogrammer, glob O_Programmable} 
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
inline *.
wp.
swap{2} [1..3] 3.
by wp => />; sim.
qed.

local lemma Pr_Game1_Game2 &m b: 
  Pr[IND_Repro1(ERO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] =
  Pr[IND_Repro2(ERO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se].
proof.
have: 
  `| Pr[IND_Repro1(ERO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] -
     Pr[IND_Repro2(ERO,A).main(b) @ &m: res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se] | 
  <=
  RealOrder.maxr Pr[IND_Repro1(ERO,A).main(b) @ &m: (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad] 
                 Pr[IND_Repro2(ERO,A).main(b) @ &m: (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad].
+ byupto.
have ->: 
  Pr[IND_Repro1(ERO, A).main(b) @ &m : (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad] 
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
  inline *; swap [1..3] 3; auto; conseq (: _ ==> true) => //= /#.
have -> /#: 
  Pr[IND_Repro2(ERO, A).main(b) @ &m : (res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se) /\ Bad.bad] 
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
by inline *; swap [1..3] 3; auto; conseq (: _ ==> true) => //= /#.
qed.

local module O_Reprogrammer2i : Oracleir_t = {
  include var O_Reprogrammer(O_Programmable2S(ERO)) [-repro]
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
        O_Programmable2(ERO).set(x,y);
      }
      cr <- cr + 1;
    } 
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module Hi = {
  import var Bad
  
  module OP = O_Programmable2S(ERO)
  module OR = O_Reprogrammer2i
 
  proc main (i0: int) : bool = {
    var b' : bool;
    
    bad <- false; cr <- 0; co <- 0; i <- i0;
    
    ERO.init();
    OP.init();
    OR.init(false);
    
    b' <@ A(OP, OR).distinguish();
    
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local lemma Hi_true &m : 
  Pr[IND_Repro2(ERO, A).main(true) @ &m : res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se]
  = 
  Pr[Hi.main(0) @ &m : res].
proof.
byequiv => //.
proc.
call (:   ={glob O_Programmable, O_Reprogrammer.se, O_Reprogrammer.ctr, ERO.m, Bad.cr, Bad.co} 
       /\ O_Reprogrammer.b{1} 
       /\ (Bad.i <= Bad.cr){2}).
+ by sim />.
+ proc. 
  seq 2 2 : (#pre /\ ={x}); 1: by auto.
  wp; if; auto.
  conseq (: ={glob O_Programmable, O_Reprogrammer.se, O_Reprogrammer.ctr, ERO.m, x}); 1: smt().
  seq 1 1 : (#pre); 1: by sim />.
  by if; auto; sim.
by inline *; swap{1} [1 ..3] 3; swap{2} [1 ..4] 3; auto; sim />.
qed.

local lemma Hi_false &m : 
  Pr[IND_Repro2(ERO, A).main(false) @ &m : res /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se]
  = 
  Pr[Hi.main(rep_ctr) @ &m : res].
proof.
byequiv => //.
proc.
call (:   ={glob O_Programmable, O_Reprogrammer.se, O_Reprogrammer.ctr, ERO.m, Bad.cr, Bad.co} 
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

local module O_Reprogrammer2i1 (O: POracle) : Oracleir_t = {
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
          y <@ O.o(x);
        } 
      } 
      cr <- cr + 1;
    } 
    
    ctr <- ctr + 1;
    
    return x;
  }
}.

local module Hi1 (O:POracle) = {
  import var Bad
  
  module OP = O_Programmable2S(O)
  module OR = O_Reprogrammer2i1(O)
 
  proc run (i0: int) : bool = {
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
  Pr[Exp(ERO, Hi1).main(i_) @ &m : res].
proof.
byequiv => //. 
proc. 
inline *; wp.
call (:   ={ERO.m, glob O_Programmable, glob O_Reprogrammer, Bad.cr, Bad.co} 
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

local lemma Hi1_ERO_LRO  &m i_ : 
  Pr[Exp(ERO,Hi1).main(i_) @ &m : res] 
  =
  Pr[Exp(Lazy.LRO,Hi1).main(i_) @ &m : res].
proof.
byequiv (: ={glob Hi1, arg} ==> ={res}) => //; symmetry.
conseq (eq_eager_sampling Hi1 _) => // *; apply dout_ll.
qed.

local module O_Reprogrammer2i2 : Oracleir_t = {
  import var Bad
  include var O_Reprogrammer(O_Programmable2S(Lazy.LRO)) [-repro]
  
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
        O_Programmable2S(Lazy.LRO).set(x,y);
      } else { if (i = cr /\ fsize Lazy.LRO.m <= query_ctr) {
        x_ <- x;
        if (! x \in Lazy.LRO.m) {
          y <@ Lazy.LRO.o(x);
        } else { 
          bad <- true;
          y <@ Lazy.LRO.o(x);          
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
  
  module OP = O_Programmable2S(Lazy.LRO)
  module OR = O_Reprogrammer2i2
 
  proc run (i0: int) : bool = {
    var b' : bool;
    
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    
    Lazy.LRO.init();
    OP.init();
    OR.init(false);
    
    b' <@ A(OP, OR).distinguish();
    
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local module O_Reprogrammer2i3 : Oracleir_t = {
  import var Bad
  include var O_Reprogrammer(O_Programmable2S(Lazy.LRO)) [-repro]

  proc repro(p: pT) : in_t = {
    var x : in_t;
    var y : out_t;

    se <- if p_max p <= p_max_bound then se else false;
    
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i + 1 <= cr) {
        y <$ dout;
        O_Programmable2S(Lazy.LRO).set(x,y);
      } else { if (i = cr /\ fsize Lazy.LRO.m <= query_ctr) {
        O_Reprogrammer2i2.x_ <- x;
        if (! x \in Lazy.LRO.m) {
          y <@ Lazy.LRO.o(x);
        } else { 
          bad <- true;
          Lazy.LRO.m <- rem Lazy.LRO.m x;
          y <@ Lazy.LRO.o(x); 
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
  
  module OP = O_Programmable2S(Lazy.LRO)
  module OR = O_Reprogrammer2i3
 
  proc run (i0: int) : bool = {
    var b';
    
    bad <- false;  cr <- 0; co <- 0; i <- i0;
  
    Lazy.LRO.init();
    OP.init();
    OR.init(false);
  
    b' <@ A(OP, OR).distinguish();
  
    return b' /\ O_Programmable.ch <= query_ctr /\ O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se;
  } 
}.

local lemma Hi1_LRO_Hi2  &m i_ : Pr[ Exp(Lazy.LRO,Hi1).main(i_) @ &m : res] = Pr[Hi2.run(i_) @ &m : res].
proof.
byequiv => //.
proc. 
inline *; wp.
call (:   ={ Lazy.LRO.m, glob O_Programmable, glob O_Reprogrammer, Bad.cr, Bad.co, Bad.i} 
       /\ (Bad.cr <= Bad.i => fsize Lazy.LRO.m <= Bad.co <= query_ctr){1}); last first.
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
  conseq (: _ ==> ={Lazy.LRO.m}); [smt() | if{2}; sim].
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
                              /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ fsize Lazy.LRO.m <= query_ctr)] => //.
+ by rewrite sumri_const.
+ smt().
+ auto => /> /#.
+ proc; wp.
  rcondt ^if; 1: by auto.
  rcondf ^if; 1: by auto => /#.
  rcondt ^if; 1: by auto.
  wp; seq 3 : (x \in Lazy.LRO.m) (query_ctr%r * p_max_bound) 1%r _ 0%r (!Bad.bad) => //.
  + by auto.
  + rnd (fun p => p \in Lazy.LRO.m); auto.
    move=> &hr /> _ _ _ hmax _ _ hsz.
    apply (ler_trans (mu p{hr} (fun (p0 : in_t ) => exists x, dom Lazy.LRO.m{hr} x /\ x = p0))).
    + by apply mu_le => /> x0 *; exists x0.
    apply (ler_trans ((fsize Lazy.LRO.m{hr})%r * p_max_bound)).
    apply: Mu_mem.mu_mem_le_fsize.
    + move=> x hx /=; apply: ler_trans hmax; move: (pmax_upper_bound p{hr} x) => /#.
    by apply ler_wpmul2r; smt(pmax_ge0). 
  by rcondt ^if; auto; conseq (: _ ==> false).
+ move=> c.
  proc.
  rcondt ^if; 1: by auto.
  by wp; conseq (: _ ==> true) => //; smt().
move=> b c; proc.
seq 2: (   ! (O_Reprogrammer.se /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ FSet.card (fdom Lazy.LRO.m) <= query_ctr) 
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
                              /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ fsize Lazy.LRO.m <= query_ctr)] => //.
+ by rewrite sumri_const.
+ smt().
+ auto => /> /#.
+ proc; wp.
  rcondt ^if; 1: by auto.
  rcondf ^if; 1: by auto => /#.
  rcondt ^if; 1: by auto.
  wp; seq 3 : (x \in Lazy.LRO.m) (query_ctr%r * p_max_bound) 1%r _ 0%r (!Bad.bad) => //.
  + by auto.
  + rnd; auto.
    move=> &hr /> _ _ _ hmax _ _ hsz.
    apply (ler_trans (mu p{hr} (fun (p0 : in_t) => exists x, dom Lazy.LRO.m{hr} x /\ x = p0))).
    + by apply mu_le => /> x0 *; exists x0.
    apply (ler_trans ((fsize Lazy.LRO.m{hr})%r * p_max_bound)).
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
seq 2: (! (O_Reprogrammer.se /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ FSet.card (fdom Lazy.LRO.m) <= query_ctr) /\
             Bad.bad = b /\ b2i (Bad.i < Bad.cr) = c); 1: by auto.
wp; if; last by auto.
seq 1 : (#pre); 1: by auto.
wp; if; 1: by conseq (: _ ==> true) => // /#.
by rcondf ^if; auto => /#.
qed.

local module O_Reprogrammer2i4 (O: POracle) : Oracleir_t = {
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

local module Hi4 (O:POracle) = {
  import var Bad
  
  module OP = O_Programmable2S(O)
  module OR = O_Reprogrammer2i4(O)
 
  proc run (i0: int) : bool = {
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
     Pr[Exp(Lazy.LRO, Hi4).main(i_) @ &m : res].
proof.
move=> hi. 
byequiv => //. 
proc.
inline *; wp.
call (:   ={O_Programmable.ch, glob O_Reprogrammer, Bad.i, Bad.cr, Bad.co} 
       /\ if (Bad.cr <= Bad.i){1} 
          then    ={Lazy.LRO.m, O_Programmable.prog_list} 
               /\ O_Programmable.prog_list{1} = [] 
               /\ (fsize Lazy.LRO.m <= Bad.co <= query_ctr){1}
          else    ((O_Reprogrammer2i2.x_ \in Lazy.LRO.m){1} 
               /\ O_Programmable.prog_list{2} = (rcons O_Programmable.prog_list (O_Reprogrammer2i2.x_, oget Lazy.LRO.m.[O_Reprogrammer2i2.x_])){1} 
               /\ eq_except (pred1 O_Reprogrammer2i2.x_{1}) Lazy.LRO.m{1} Lazy.LRO.m{2})).
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

local lemma Hi4_LRO_ERO &m i_: 
  Pr[Exp(Lazy.LRO, Hi4).main(i_) @ &m : res] 
  = 
  Pr[Exp(ERO, Hi4).main(i_) @ &m : res].
proof.
byequiv (: ={glob Hi4, arg} ==> ={res}) => //.
by conseq (eq_eager_sampling Hi4 _) => // *; apply dout_ll.
qed.

local lemma Hi4_Hi &m i_ : 
  Pr[Exp(ERO, Hi4).main(i_) @ &m : res] 
  = 
  Pr[Hi.main(i_) @ &m : res].
proof. by byequiv => //; proc; inline *; wp; swap{2} [1 .. 4] 3; sim. qed.

local lemma rom_reprogramming1 &m i_ : 
     0 <= i_ 
  => `| Pr[Hi.main(i_ + 1) @ &m : res] - Pr[Hi.main(i_) @ &m : res] | 
     <= 
     query_ctr%r * p_max_bound.
proof.
move=> hi; rewrite (Hip1_Hi1 &m i_) (Hi1_ERO_LRO  &m i_) (Hi1_LRO_Hi2 &m i_).
rewrite -(Hi4_Hi &m i_) -(Hi4_LRO_ERO &m i_) -(Hi3_Hi4 &m i_) 1://.
by move: (Hi2_Hi3 &m i_) (Hi2_bad &m i_) (Hi3_bad &m i_) => /#.
qed.

(* ----------------------------------------------------- *)

lemma Bound_IND_Repro &m : 
     hoare[A(O_Programmable(ERO), O_Reprogrammer(O_Programmable(ERO))).distinguish : 
             O_Programmable.ch = 0 /\ O_Reprogrammer.ctr = 0 /\ O_Reprogrammer.se 
             ==> O_Programmable.ch <= query_ctr /\ 
             O_Reprogrammer.ctr <= rep_ctr /\ O_Reprogrammer.se]
  => `| Pr[IND_Repro(ERO, A).main(false) @ &m : res]
       - Pr[IND_Repro(ERO, A).main(true) @ &m : res] |
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
