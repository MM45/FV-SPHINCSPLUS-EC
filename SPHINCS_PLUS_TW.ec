(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr RealExp StdOrder FinType BitEncoding.
(*---*) import IntOrder.
(*---*) import BS2Int.

(* -- Local -- *)
require import BinaryTrees MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.
require (*--*) DigitalSignatures.
require (*--*) FORS_TW_ES FL_XMSS_MT_TW_ES.



(* - Parameters - *)
(* Size of integer list associated with each address *)
const adrs_len = 6.

(* 
  Length (in bytes) of messages as well as the length of elements of 
  private keys, public keys, and signatures
*)
const n : { int | 1 <= n } as ge1_n.

(* Base 2 logarithm of the Winternitz parameter w *)
const log2_w : { int | log2_w = 2 \/ log2_w = 4 \/ log2_w = 8 } as val_log2w.

(* Winternitz parameter (base/radix) *)
const w = 2 ^ log2_w. 

(* Length of the message in base/radix w *)
const len1 : int = ceil ((8 * n)%r / log2 w%r).

(* Length of the checksum in base/radix w *)      
const len2 : int = floor (log2 ((len1 * (w - 1))%r) / log2 w%r) + 1.

(* Number of elements (of length n) in private keys, public keys, and signatures *)
const len : int = len1 + len2.

(* Height of a single inner tree *)
const h' : { int | 1 <= h' } as ge1_hp. 

(* Number of WOTS-TW/FORS-TW instances of a single inner tree (i.e., number of leaves) *)
const l' = 2 ^ h'.

(* Number of layers in the hypertree (i.e., height of tree of trees) *)
const d : { int | 1 <= d } as ge1_d.

(* 
  Height of "flattened" hypertree 
  (i.e., total height of concatenation of inner trees) 
*)
const h : int = h' * d.

(* 
  Number of leaves of "flattened" hypertree
  (i.e., total number of leaves of all inner trees on bottom layer).
  Also, number of FORS-TW instances.
*)
const l : int = 2 ^ h.

(* Number of trees in a FORS-TW instance *)
const k : { int | 1 <= k } as ge1_k.

(* Height of each FORS-TW tree *)
const a : { int | 1 <= a } as ge1_a.

(* Number of leaves of each FORS-TW tree *)
const t : int = 2 ^ a.


(* Address type for chaining (used in tweakable hash function calls of WOTS-TW chains) *)
const chtype : int.

(* 
  Address type for public (WOTS-TW) key compression 
  (used in tweakable hash function calls of WOTS-TW public key compression) 
*)
const pkcotype : int.

(* 
  Address type for tree hashing in the hypertree 
  (used in tweakable hash function calls of inner trees) 
*)
const trhxtype : int.

(* 
  Address type for tree hashing in FORS-TW trees
  (used in tweakable hash function calls of FORS-TW trees)
*)
const trhftype : int.

(* 
  Address type for (FORS-TW) tree root compression
  (used in tweakable hash function calls of FORS-TW tree root compression)
*)
const trcotype : int.


(* -- Properties of parameters -- *)
(* The different address types are distinct *)
axiom dist_adrstypes : uniq [chtype; pkcotype; trhxtype; trhftype; trcotype].

(* l' is greater than or equal to 2 *)
lemma ge2_lp : 2 <= l'.
proof. by rewrite /l' ler_eexpr; smt(ge1_hp). qed.

(* h is greater than or equal to 1 *)
lemma ge1_h : 1 <= h.
proof. by rewrite /h mulr_ege1 1:ge1_hp ge1_d. qed.

(* l is greater than or equal to 2 *)
lemma ge2_l : 2 <= l.
proof. by rewrite /l ler_eexpr; smt(ge1_h). qed.

(* Number of leaves of a FORS-TW tree is greater than or equal to 2 *)
lemma ge2_t : 2 <= t.
proof. by rewrite /t -{1}expr1 ler_weexpn2l 2:ge1_a. qed. 

(* Winternitz parameter w is a power of 2 *)
lemma wpowof2: exists a, w = 2 ^ a.
proof. by exists log2_w. qed.

(* log2_w is the (base 2) logarithm of w *)
lemma log2_wP: log2 w%r = log2_w%r.
proof. by rewrite /w -RField.fromintXn 2:-rpow_nat 1,2:#smt:(val_log2w) // /log2 logK. qed.

(* Winternitz parameter w equals either 4, 16, or 256 *)
lemma val_w : w = 4 \/ w = 16 \/ w = 256.
proof.
rewrite /w; case: val_log2w => [->|]; last case => ->.
+ by left; rewrite expr2.
+ by right; left; rewrite (: 4 = (2 + 2)) 2:exprD_nneg // expr2. 
+ by right; right; rewrite (: 8 = 2 * 2 * 2) // 2!exprM ?expr2.
qed.

(* Value of len1 equals either 4 * n, 2 * n, or n *)
lemma val_len1 : len1 = 4 * n \/ len1 = 2 * n \/ len1 = n.
proof.
rewrite /len1 log2_wP (: 8 = 2 * 2 * 2) // ?fromintM. 
case: val_log2w => [->|]; last case => ->. 
+ by left; rewrite RField.mulrC ?RField.mulrA RField.mulVf //= -fromintM from_int_ceil. 
+ right; left.
  by rewrite RField.mulrC (: 4 = 2 * 2) // 2!RField.mulrA RField.mulVf //= -fromintM from_int_ceil.
+ right; right.
  by rewrite RField.mulrC (: 8 = 2 * 2 * 2) // RField.mulrA RField.mulVf //= from_int_ceil.
qed.

(* len1 is greater than or equal to 1 *)
lemma ge1_len1 : 1 <= len1.
proof. smt(val_len1 ler_pmul ge1_n). qed.

(* len2 is greater than or equal to 1 *)
lemma ge1_len2 : 1 <= len2.
proof. 
rewrite /len2 -ler_subl_addr /= -from_int_floor floor_mono.
by rewrite RealOrder.divr_ge0 log_ge0 //; smt(ge1_len1 val_w).
qed. 

(* len is greater than or equal to 2 *)
lemma ge2_len : 2 <= len.
proof. smt(ge1_len1 ge1_len2). qed.


(* - Operators - *)
(* -- Auxiliary -- *)
(* Number of nodes in a XMSS binary tree (of total height h') at a particular height h'' *)
op nr_nodesx (h'' : int) = 2 ^ (h' - h'').

(* Number of nodes in a FORS-TW binary tree (of total height a) at a particular height a' *)
op nr_nodesf (a' : int) = 2 ^ (a - a').

(* 
  Number of trees in hypertree (with d layers) at a particular layer d'.
  Note that each "node" (i.e., inner tree) of the hypertree creates 2 ^ h' children, not 2.
  Furthermore, note that the number of layers is always one more than the height.
  This is because the number of layers increases with each level containing nodes, while height
  increases with each edge between layers. (So, in a sense, the final layer does contribute 
  to the number of layers but does not contribute to the height)
*)
op nr_trees (d' : int) = 2 ^ (h' * (d - d' - 1)).

(* 
  Number of nodes in "flattened" hypertree (with d layers and inner trees of height h') at
  a particular layer d' and (inner) height h''.
*)
op nr_nodes_ht (d' h'' : int) = nr_trees d' * nr_nodesx h''.

(* Alternative expression for nr_nodes_ht using total height of hypertree (h) *)
lemma nrnodesht_h (d' h'' : int) :
     d' < d
  => h'' <= h'
  => nr_nodes_ht d' h'' = 2 ^ (h - d' * h' - h'').
proof.
move=> gtdp_d dehpp_hp.
rewrite /nr_nodes_ht /nr_trees /nr_nodes /h -exprD_nneg; 2: smt().
+ by rewrite mulr_ge0; smt(ge1_hp).
by congr; ring.
qed. 

(* 
  Number of nodes in "flattened" hypertree at a particular layer d' 
  and (inner) height 0 is equal to the number of trees in layer d' - 1 
*)
lemma nrnodesht_nrtrees (d' : int) : 
     0 < d' < d
  => nr_nodes_ht d' 0 = nr_trees (d' - 1).
proof.
move => -[gt0_dp ltd_dp]. 
rewrite /nr_trees nrnodesht_h //= /h; 1: smt(ge1_hp). 
by congr; ring.
qed.

(* -- Validity checks for (indices corresponding to) SPHINCS+ addresses -- *)
(* Layer index validity check (note: regards hypertree) *)
op valid_lidx (lidx : int) : bool = 
  0 <= lidx < d.

(* 
  Tree index validity check
  (Note: regards hypertree; i.e., is tidx a valid index for pointing to a tree in layer lidx) 
*)
op valid_tidx (lidx tidx : int) : bool = 
  0 <= tidx < nr_trees lidx.

(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = chtype \/ typeidx = pkcotype \/ typeidx = trhxtype \/
  typeidx = trhftype \/ typeidx = trcotype.

(* Key pair index validity check (note: regards inner tree) *)
op valid_kpidx (kpidx : int) : bool =
  0 <= kpidx < l'.

(* Tree height index validity check (note: regards inner tree) *)
op valid_thxidx (thxidx : int) : bool = 
  0 <= thxidx <= h'.
  
(* Tree breadth index validity check (note: regards inner tree) *)
op valid_tbxidx (thxidx tbxidx : int) : bool = 
  0 <= tbxidx < nr_nodesx thxidx.

(* Tree height index validity check (note: regards FORS-TW tree) *)
op valid_thfidx (thfidx : int) : bool = 
  0 <= thfidx <= a.
  
(* Tree breadth index validity check (note: regards FORS-TW tree) *)
op valid_tbfidx (thfidx tbfidx : int) : bool = 
  0 <= tbfidx < k * nr_nodesf thfidx.

(* Chain index validity check *)
op valid_chidx (chidx : int) : bool =
  0 <= chidx < len.

(* Hash index validity check *)
op valid_hidx (hidx : int) : bool = 
  0 <= hidx < w - 1.

(* Chaining address indices validity check *) 
op valid_idxvalsch (adidxs : int list) : bool =
     valid_hidx (nth witness adidxs 0) 
  /\ valid_chidx (nth witness adidxs 1)
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = chtype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Public-key compression address indices value validity check *)  
op valid_idxvalspkco (adidxs : int list) : bool =
     nth witness adidxs 0 = 0 
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = pkcotype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Hypertree hashing address indices value validity check *)  
op valid_idxvalstrhx (adidxs : int list) : bool =
     valid_tbxidx (nth witness adidxs 1) (nth witness adidxs 0)
  /\ valid_thxidx (nth witness adidxs 1)
  /\ nth witness adidxs 2 = 0
  /\ nth witness adidxs 3 = trhxtype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* FORS-TW tree hashing address indices value validity check *)  
op valid_idxvalstrhf (adidxs : int list) : bool =
     valid_tbfidx (nth witness adidxs 1) (nth witness adidxs 0)
  /\ valid_thfidx (nth witness adidxs 1)
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trhftype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ nth witness adidxs 5 = 0.

(* FORS-TW root compression address indices value validity check *)  
op valid_idxvalstrco (adidxs : int list) : bool =
     nth witness adidxs 0 = 0
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trcotype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ nth witness adidxs 5 = 0.

(* Overall address indices value validity check *)
op valid_idxvals (adidxs : int list) : bool =
  valid_idxvalsch adidxs \/ valid_idxvalspkco adidxs \/ valid_idxvalstrhx adidxs \/
  valid_idxvalstrhf adidxs \/ valid_idxvalstrco adidxs.

(* Overall address indices validity check *)
op valid_adrsidxs (adidxs : int list) : bool =
  size adidxs = adrs_len /\ valid_idxvals adidxs.

(* - Types - *)
(* Index *)
clone import Subtype as Index with
  type T <= int,
    op P i <= 0 <= i < l
    
  proof *.
  realize inhabited by exists 0; smt(ge2_l).

type index = Index.sT.

type mseed.

type mkey.

type sseed.

type pseed.

type msg.

type dgst = bool list.


(* Digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DigestBlock with
  type T   <- dgst,
    op P x <- size x = 8 * n
    
  proof *.
  realize inhabited by exists (nseq (8 * n) witness); smt(size_nseq ge1_n).
  
type dgstblock = DigestBlock.sT.

(* Finiteness of dgstblock *)
clone import FinType as DigestBlockFT with
  type t <= dgstblock,
  
    op enum <= map DigestBlock.insubd (map (int2bs (8 * n)) (range 0 (2 ^ (8 * n))))
    
  proof *.
  realize enum_spec.
    move=> m; rewrite count_uniq_mem 1:map_inj_in_uniq => [x y | |].
    + rewrite 2!mapP => -[i [/mem_range rng_i ->]] -[j [/mem_range rng_j ->]] eqins. 
      rewrite -(DigestBlock.insubdK (int2bs (8 * n) i)) 1:size_int2bs; 1: smt(ge1_n).
      rewrite -(DigestBlock.insubdK (int2bs (8 * n) j)) 1:size_int2bs; 1: smt(ge1_n). 
      by rewrite eqins. 
    + rewrite map_inj_in_uniq => [x y /mem_range rng_x /mem_range rng_y|].
      rewrite -{2}(int2bsK (8 * n) x) 3:-{2}(int2bsK (8 * n) y) //; 1,2: smt(ge1_n).
      by move=> ->. 
    + by rewrite range_uniq.
    rewrite -b2i1; congr; rewrite eqT mapP. 
    exists (DigestBlock.val m).
    rewrite DigestBlock.valKd mapP /=. 
    exists (bs2int (DigestBlock.val m)).
    rewrite mem_range bs2int_ge0 /= (: 8 * n = size (DigestBlock.val m)) 1:DigestBlock.valP //. 
    by rewrite bs2intK bs2int_le2Xs.
  qed.

(*  
(* Lists of length a containing digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DBAL with
  type T   <- dgstblock list,
    op P ls <- size ls = a
    
  proof *.
  realize inhabited by exists (nseq a witness); smt(size_nseq ge1_a).
   
(* Authentication paths in FORS-TW trees *)
type apFORSTW = DBAL.sT.

(* Lists of length k containing secret key (single element)/apFORSTW pairs *)
clone import Subtype as DBAPKL with
  type T   <- (dgstblock * apFORSTW) list,
    op P ls <- size ls = k
    
  proof *.
  realize inhabited by exists (nseq k witness); smt(size_nseq ge1_k).

(* Signatures *)
type sigFORSTW = DBAPKL.sT.

(* Lists of length len of which each entry is a digest of length 1 (block of 8 * n bits) *)
clone import Subtype as DBLL with
  type T   <- dgstblock list,
    op P l <- size l = len
  
  proof *.
  realize inhabited by exists (nseq len witness); smt(size_nseq ge2_len).

type dgstblocklenlist = DBLL.sT.

type sigWOTS = dgstblocklenlist.

(* Lists of length h' of which the entries are digest of length 1 (block of 8 * n bits) *)
clone import Subtype as DBHPL with
  type T <= dgstblock list,
    op P ls <= size ls = h'
    
  proof *.
  realize inhabited by exists (nseq h' witness); rewrite size_nseq; smt(ge1_hp).
      
(* 
  Authentication paths in (single) FL-XMSS-TW tree.
  I.e., authentication paths in single inner tree of FL-XMSS-MT-TW hypertree.
*)
type apFLXMSSTW = DBHPL.sT.

(* 
  Lists of length d of which the entries are sigWOTS/authentication path pairs 
  (i.e., FL-XMSS-TW signatures) 
*)
clone import Subtype as SAPDL with
  type T <= (sigWOTS * apFLXMSSTW) list,
    op P ls <= size ls = d
    
  proof *.
  realize inhabited by exists (nseq d witness); rewrite size_nseq; smt(ge1_d).

type sigFLXMSSTWDL = SAPDL.sT.

(* Signatures *)
type sigFLXMSSMTTW = index * sigFLXMSSTWDL.
*)

(* Addresses *)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
    proof ge1_l.
    realize ge1_l by trivial.
    
import Adrs.

type adrs = HA.adrs.


(* - Clones and Imports - *)
(* FORS-TW *)
clone import FORS_TW as FTW with
    op n <- n,
    op k <- k,
    op a <- a,
    op t <- t,
    op l <- l',
    op s <- nr_trees 0,
    op d <- l,
    
  type mseed <- mseed,
  type mkey <- mkey,
  type sseed <- sseed,
  type pseed <- pseed,
  type msg <- msg,
  type dgst <- dgst,
    
    op nr_nodes <- nr_nodesf,
    op trhtype <- trhftype,
    op trcotype <- trcotype,
    op adrs_len <- adrs_len,

    op valid_tidx <- valid_tidx 0,
    op valid_kpidx <- valid_kpidx,
    op valid_thidx <- valid_thfidx,
    op valid_tbidx <- valid_tbfidx,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs,
    op valid_fidxvalsgp adidxs <- nth witness adidxs 0 = 0,
  
  theory DigestBlock <= DigestBlock,
  theory DigestBlockFT <= DigestBlockFT,
(*
  theory DBAL <= DBAL,
  theory DBAPKL <= DBAPKL,
*)
  theory InstanceIndex <= Index,
  theory HA <= HA,
  
  type dgstblock <- dgstblock,
  type adrs <- adrs
(*
  ,  
  type apFORSTW <- apFORSTW,
  type sigFORSTW <- sigFORSTW,
  type iid <- index
*)  
  proof ge5_adrslen, ge1_n, ge1_k, ge1_a, ge1_l, ge1_s, dval, dist_adrstypes, valid_fidxvals_idxvals.
  realize ge5_adrslen by trivial.
  realize ge1_n by exact: ge1_n.
  realize ge1_k by exact ge1_k.
  realize ge1_a by exact: ge1_a.
  realize ge1_l by smt(ge2_lp).
  realize ge1_s by rewrite /nr_trees -add0r -ltzE expr_gt0.
  realize dval. 
    rewrite /nr_trees /l' /l /h -exprD_nneg /= 1:mulr_ge0; 1..3: smt(ge1_d ge1_hp).
    by congr; ring.
  qed.
  realize dist_adrstypes by smt(dist_adrstypes).
  realize valid_fidxvals_idxvals.
    rewrite /(<=) => ls @/valid_fidxvals @/valid_idxvals @/valid_fidxvalslp.
    by rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco ?nth_drop ?nth_take //= /#.
  qed.

import DBAL BLKAL DBAPKL DBLLKTL.


(* FL-XMSS-MT-TW *)
clone import FL_XMSS_MT_TW as FXMTW with
  op n <- n,
  op log2_w <- log2_w,
  op w <- w,
  op len1 <- len1,
  op len2 <- len2,
  op len <- len,
  op h' <- h',
  op l' <- l',
  op d <- d,
  op h <- h,
  op l <- l,
  
  op chtype <- chtype,
  op pkcotype <- pkcotype,
  op trhtype <- trhxtype,
  
  op nr_nodes <- nr_nodesx,
  op nr_trees <- nr_trees,
  
  op valid_lidx <- valid_lidx,
  op valid_tidx <- valid_tidx,
  op valid_kpidx <- valid_kpidx,
  op valid_thidx <- valid_thxidx,
  op valid_tbidx <- valid_tbxidx,
  op valid_chidx <- valid_chidx,
  op valid_hidx <- valid_hidx,
  
  op ES.adrs_len <- adrs_len,
  op ES.valid_idxvals <- valid_idxvals,
  op ES.valid_adrsidxs <- valid_adrsidxs,
  op ES.valid_xidxvalsgp <- predT,
  
  theory ES.HA <= HA,
  theory ES.Index <= Index,
  theory ES.WTW.DigestBlock <= DigestBlock,
  theory ES.WTW.DigestBlockFT <= DigestBlockFT
(*  
  theory ES.DBHPL <= DBHPL,
  theory ES.SAPDL <= SAPDL,
*)
  proof *. ge1_n val_log2w, ge1_hp, ge1_d, dist_adrstypes, ES.ge6_adrslen, ES.ge6_adrslen,
        ES.valid_xidxvals_idxvals, 
   
import ES DBHPL SAPDL.
import WTW DBLL EmsgWOTS WAddress.

  
(* -- Setters -- *)
