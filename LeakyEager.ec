require import AllCore Distr Real.

type t, t'.

module type LeakySampler_Oracle = {
  proc leak(_ : t -> t'): t'
  proc get(): t
}.

module type LeakySampler = {
  proc sample(dt : t distr): unit
  include LeakySampler_Oracle
}.

module Eager : LeakySampler = {
  var x : t

  proc sample(dt) = {
    x <$ dt;
  }

  proc leak(F : t -> t') = {
    return F x;
  }

  proc get() = {
    return x;
  }
}.

op preimage (f : 'a -> 'b) y x = f x = y.

module Lazy : LeakySampler = {
  var d : t distr

  proc sample(dt) = {
    var x;

    x <$ dt; (* enforce termination behaviour *)
    d <- dscale dt;
  }

  proc leak(F : t -> t') = {
    var xo;

    xo <$ d;
    d <- dcond d (preimage F (F xo));
   
    return F xo;
  }

  proc get() = {
    var r;

    r <$ d;
    d <- dunit r;
    
    return r;
  }
}.

module type Distinguisher (S : LeakySampler_Oracle) = {
  proc distinguish() : bool
}.

module Experiment (S : LeakySampler) (D : Distinguisher) = {
  proc main(dt : t distr) = {
    var b;

    S.sample(dt);
    b <@ D(S).distinguish();
    return b;
  }
}.

section.
declare module D <: Distinguisher {-Eager, -Lazy}.

local module Resampled : LeakySampler = {
  var d : t distr
  var x : t

  proc sample(dt) = {
    var x;

    x <$ dt; (* enforce termination behaviour *)
    d <- dscale dt;
  }

  proc leak(F : t -> t') = {
    var xo;

    xo <$ d;
    d <- dcond d (preimage F (F xo));
   
    return F xo;
  }

  proc get() = {
    var r;

    r <$ d;
    d <- dunit r;
    
    return r;
  }

  proc resample() = {
    x <$ d;
    d <- dunit x;
  }
}.

local module Experiment_rs_eager = {
  proc main(dt : t distr) = {
    var b;

    Resampled.sample(dt);
    Resampled.resample();
    b <@ D(Resampled).distinguish();
    return b;
  }
}.

local module Experiment_rs_lazy = {
  proc main(dt : t distr) = {
    var b;

    Resampled.sample(dt);
    b <@ D(Resampled).distinguish();
    Resampled.resample();
    return b;
  }
}.

local module Igor = {
  proc samp_resamp(dt) = {
    Resampled.sample(dt);
    Resampled.resample();
  }

  proc resamp_test(F : t -> t') = {
    Resampled.resample();
    Resampled.x <$ Resampled.d;
    Resampled.d <- dcond Resampled.d (preimage F (F Resampled.x));
    return F Resampled.x;
  }

  proc resamp(F : t -> t') = {
    Resampled.resample();
    return F Resampled.x;
  }

  proc test_resamp(F : t -> t') = {
    var r;

    Resampled.x <$ Resampled.d;
    Resampled.d <- dcond Resampled.d (preimage F (F Resampled.x));
    r <- F Resampled.x;
    Resampled.resample();
    return r;
  }
}.

local equiv eager_igor:
  Eager.sample ~ Igor.samp_resamp:
    ={arg} ==> Eager.x{1} = Resampled.x{2}.
proof.
exlim arg{1}=> d.
case: (0%r < weight d)=> [gt0_wd|]; last first.
+ rewrite witness_support=> /negb_exists @/predT /= d_nil.
  proc; inline *; wp; rnd{2}; auto=> />.
  by move=> x; rewrite d_nil.
bypr (Eager.x{1}) (Resampled.x{2})=> /> &1 &2 x ->> eq_arg.
have ->: Pr[Eager.sample(arg{1}) @ &1: Eager.x = x] = mu1 arg{1} x.
+ by byphoare (: dt = arg{1} ==> _)=> //; proc; rnd; auto.
rewrite eq_sym; byphoare (: dt = arg{2} ==> _)=> //.
proc; inline *.
seq 2: true (weight dt) (mu1 (dscale dt) x) _ 0%r (dt = arg{2} /\ dt0 = dt)=> //.
+ by auto.
+ by auto.
+ by wp; rnd; auto.
move=> &0 ->; rewrite eq_arg dscale1E.
by field; rewrite -eq_arg /#.
qed.

local equiv eq_eager:
  Experiment(Eager, D).main ~ Experiment_rs_eager.main:
    ={glob D, arg} ==> ={res}.
proof.
proc; inline *.
call (:    ={x}(Eager, Resampled)
        /\ Resampled.d{2} = dunit Resampled.x{2}
        /\ is_lossless Resampled.d{2}).
+ proc; auto=> /> &0 dt_ll + /supp_dunit - />.
  rewrite dcond_ll //=.
  + by rewrite dunitE.
  apply: eq_distr=> x; rewrite dcond1E !dunitE /pred1 /=.
  by case: (Resampled.x{0} = x).
+ by proc; auto=> /> &0 d_ll + /supp_dunit - />.
conseq (: Eager.x{1} = Resampled.x{2})
       _
       (: Resampled.d = dunit Resampled.x
       /\ is_lossless Resampled.d)=> //.
+ by auto=> /> &0 _ _ x _; exact: dunit_ll.
transitivity {1} { Eager.sample(dt); }
  (={dt} ==> ={Eager.x})
  (={dt} ==> Eager.x{1} = Resampled.x{2})=> />.
+ by move=> &2; exists dt{2}.
+ by inline *; auto.
transitivity {2} { Igor.samp_resamp(dt); }
  (={dt} ==> Eager.x{1} = Resampled.x{2})
  (={dt} ==> ={Resampled.x})=> />.
+ by move=> &2; exists dt{2}.
+ by call eager_igor.
by inline *; auto.
qed.

local equiv eq_lazy:
  Experiment(Lazy, D).main ~ Experiment_rs_lazy.main:
    ={glob D, arg} ==> ={res}.
proof.
proc; inline *; wp; rnd {2}.
call (: ={d}(Lazy, Resampled)
     /\ is_lossless Resampled.d{2}).
+ proc; auto=> /> &0 d_ll.
  move=> x x_in_d; rewrite dcond_ll witness_support.
  by exists x.
+ proc; auto=> /> &0 d_ll.
  by move=> x _; exact: dunit_ll.
auto=> /> &2 x x_in_d; case: (0%r < weight dt{2}).
+ by move=> /dscale_ll.
by rewrite witness_support=> /negb_exists @/predT=> /= /(_ x).
qed.

local equiv left_igor:
  Igor.resamp_test ~ Igor.resamp:
    ={arg, glob Resampled} ==> ={res, glob Resampled}.
proof.
proc; inline *; wp; rnd{1}; auto=> /> &0 x x_in_d.
split=> [|_]; 1:exact:dunit_ll.
move=> + /supp_dunit - />; apply: eq_distr=> x'.
rewrite dcond1E !dunitE=> //=.
by case: (F{0} x = F{0} x')=> //#.
qed.

local hoare igor_constrained F0:
  Igor.resamp: F = F0 ==> res = F0 Resampled.x /\ Resampled.d = dunit Resampled.x.
proof. by proc; inline *; auto. qed.

local lemma resamp_igor F0 b x d &m:
    Pr[Igor.resamp(F0) @ &m: res = b /\ Resampled.x = x /\ Resampled.d = d]
  = if (b, d) = (F0 x, dunit x) then mu1 Resampled.d{m} x else 0%r.
proof.
case: ((b, d) = (F0 x, dunit x))=> />.
+ byphoare (: F = F0 /\ Resampled.d = Resampled.d{m} ==> _)=> //.
  by proc; inline *; wp; rnd (pred1 x); auto=> /#.
move=> bad_igor; byphoare (: F = F0 ==> _)=> //.
by hoare; conseq (igor_constrained F0)=> /#.
qed.

local equiv right_igor:
  Igor.resamp ~ Igor.test_resamp:
    ={arg, glob Resampled} ==> ={res, glob Resampled}.
proof.
bypr (res, Resampled.x, Resampled.d){1} (res, Resampled.x, Resampled.d){2}=> //.
move=> &l &r [] b x d [].
move=> eq_F eq_glob.
rewrite (resamp_igor arg{l} b x d &l) eq_sym.
case: ((b, d) = (arg{l} x, dunit x))=> />; last first.
+ move=> bad_igor; byphoare (: F = arg{r} ==> _)=> //.
  by hoare; proc; inline *; auto=> />; smt(dcond_supp).
byphoare (: F = arg{l} /\ Resampled.d = Resampled.d{l} ==> _)=> // [|/#].
proc; inline *.
seq 1: (preimage F (F x) Resampled.x)
       (mu Resampled.d (preimage F (F x)))
       (mu1 (dcond Resampled.d (preimage F (F x))) x)
       _
       0%r
       (F = arg{l})=> //.
+ by auto.
+ by rnd (preimage F (F x)); auto.
+ wp; rnd (pred1 x); auto=> /> &0 eq_Fx.
  have -> /#: (preimage arg{l} (arg{l} Resampled.x{0}))
            = (preimage arg{l} (arg{l} x)).
  by apply: fun_ext=> x'; rewrite eq_Fx.
+ by hoare; auto=> /> &0 @/preimage ->.
move=> />; rewrite !dcond1E /=.
case: (x \in Resampled.d{l})=> [x_in_d|]; 2:by rewrite /support; smt(ge0_mu).
have gt0_mu_k: 0%r < mu Resampled.d{l} (preimage arg{l} (arg{l} x)).
+ by rewrite witness_support; exists x; rewrite x_in_d.
by case (preimage arg{l} (arg{l} x) x) => /#.
qed.

local lemma eager_leak:
  eager [Resampled.resample();, Resampled.leak
       ~ Resampled.leak, Resampled.resample();:
           ={arg, glob Resampled} ==> ={res, glob Resampled}].
proof.
eager proc; inline *.
rewrite equiv [{1} left_igor (F) (result) (F) (result)].
+ by sim.
by rewrite equiv [{1} right_igor (F) (result) (F) (result)].
qed.

local lemma eager_get:
  eager [Resampled.resample();, Resampled.get
       ~ Resampled.get, Resampled.resample();:
           ={arg, glob Resampled} ==> ={res, glob Resampled}].
proof.
by eager proc; inline *; auto=> /> &0 x _ + /supp_dunit.
qed.

local lemma eager_distinguish:
  eager [Resampled.resample();, D(Resampled).distinguish
       ~ D(Resampled).distinguish, Resampled.resample();:
      ={glob D, glob Resampled} ==> ={res, glob Resampled}].
proof.
eager proc (H_: Resampled.resample(); ~ Resampled.resample();
              : ={glob Resampled} ==> ={glob Resampled})
           (={glob Resampled})=> //; [1,3,5:by sim].
+ exact: eager_leak.
+ exact: eager_get.
qed.


end section.
