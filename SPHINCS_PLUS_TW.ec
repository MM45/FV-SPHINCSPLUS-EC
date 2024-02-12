(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr IntDiv RealExp StdOrder FinType BitEncoding.
(*---*) import IntOrder.
(*---*) import BS2Int.

(* -- Local -- *)
require import BinaryTrees MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.
require (*--*) DigitalSignatures.
require (*--*) FORS_TW_ES FL_SL_XMSS_MT_TW_ES.



(* - Parameters - *)
(* -- General -- *)
(* Length of (integer list corresponding to) addresses used in tweakable hash functions *)
const adrs_len = 6.

(* 
  Length (in bytes) of messages as well as the length of elements of 
  private keys, public keys, and signatures
*)
const n : { int | 1 <= n } as ge1_n.


(* -- FORS-TW -- *)
(* Number of trees in a FORS-TW instance *)
const k : { int | 1 <= k } as ge1_k.

(* Height of each FORS-TW tree *)
const a : { int | 1 <= a } as ge1_a.

(* Number of leaves of each FORS-TW tree *)
const t : int = 2 ^ a.


(* -- WOTS-TW -- *)
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


(* -- FL-XMSS(-MT)-TW -- *)
(* Height of a single inner tree *)
const h' : { int | 0 <= h' } as ge0_hp. 

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


(* -- Address types -- *) 
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

(* l is greater than or equal to 1 *)
lemma ge1_l : 1 <= l.
proof. by rewrite /l -add0r -ltzE expr_gt0. qed.

(* l' is greater than or equal to 1 *)
lemma ge1_lp : 1 <= l'.
proof. by rewrite /l' -add0r -ltzE expr_gt0. qed.

(* h is greater than or equal to 0 *)
lemma ge0_h : 0 <= h.
proof. rewrite /h mulr_ge0 1:ge0_hp; smt(ge1_d). qed.

(* Number of leaves of a FORS-TW tree is greater than or equal to 2 *)
lemma ge2_t : 2 <= t.
proof. by rewrite /t -{1}expr1 ler_weexpn2l 2:ge1_a. qed. 

(*
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
*)

(* - Types - *)
(* -- General -- *)
(* Index *)
clone import Subtype as Index with
  type T <= int,
    op P i <= 0 <= i < l
    
  proof *.
  realize inhabited by exists 0; smt(ge1_l).

type index = Index.sT.

(* Seeds for message compression key generation function *)
type mseed.

(* Randomness for non-deterministic signature generation *)
type rm.

(* Keys for message compression *) 
type mkey.

(* Secret seeds *)
type sseed.

(* Public seeds *)
type pseed.

(* Messages *)
type msg.

(* 
  Digests, i.e., outputs of (tweakable) hash functions.
  In fact, also input of (tweakable) hash functions in this case.
*)
type dgst = bool list.

(* Digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DigestBlock with
  type T   <= dgst,
    op P x <= size x = 8 * n
    
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


  
(* - Operators - *)
(* -- Auxiliary -- *)
(* Number of nodes in a XMSS binary tree (of total height h') at a particular height h'' *)
op nr_nodesx (h'' : int) = 2 ^ (h' - h'').

(* Number of nodes in a FORS binary tree (of total height a) at a particular height a' *)
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
*)

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

(*
(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = chtype \/ typeidx = pkcotype \/ typeidx = trhxtype \/
  typeidx = trhftype \/ typeidx = trcotype.
*)

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



(* - Distributions - *)  
(* Proper distribution over seeds for message compression key generation function *)
op [lossless] dmseed : mseed distr.

(*
(* Proper distribution over randomness for non-deterministic signature generation *)
op [lossless] drm : rm distr.
*)

(* Proper distribution over randomness for message compression *)
op [lossless] dmkey : mkey distr.

(* Proper distribution over public seeds *)
op [lossless] dpseed : pseed distr.

(* Proper distribution over secret seeds *)
op [lossless] dsseed : sseed distr.


(* Proper distribution over digests of length 1 (block of 8 * n bits) *)
op [lossless] ddgstblock : dgstblock distr.



(* - Types (2/3) - *)
(* Addresses *)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
  proof *. 
  realize ge1_l by trivial.
  realize Adrs.inhabited. 
    exists [0; 0; 0; pkcotype; 0; 0].
    rewrite /valid_adrsidxs /= /adrs_len /= /valid_idxvals. right; left.
    rewrite /valid_idxvalspkco /= /valid_kpidx /valid_tidx /valid_lidx /nr_trees.
    by rewrite ?expr_gt0 //; smt(ge1_d).
  qed.
  
import Adrs.

type adrs = HA.adrs.


(* - Operators (2/2) - *)
(* -- Setters -- *)
op set_lidx (ad : adrs) (i : int) : adrs =
  set_idx ad 5 i.

op set_tidx (ad : adrs) (i : int) : adrs =
  set_idx ad 4 i.

op set_ltidx (ad : adrs) (i j : int) : adrs =
  insubd (put (put (val ad) 4 j) 5 i).

op set_typeidx (ad : adrs) (i : int) : adrs =
  insubd (put (put (put (put (val ad) 0 0) 1 0) 2 0) 3 i).
  
op set_kpidx (ad : adrs) (i : int) : adrs =
  set_idx ad 2 i.

op set_thtbidx (ad : adrs) (i j : int) : adrs =
  insubd (put (put (val ad) 0 j) 1 i).


(* -- Keyed hash functions -- *)
(* Secret key element generation function *)
op skg : sseed -> (pseed * adrs) -> dgstblock.

clone KeyedHashFunctions as SKG with
  type key_t <- sseed,
  type in_t <- pseed * adrs,
  type out_t <- dgstblock,
  
    op f <- skg
    
  proof *.

clone import SKG.PRF as SKG_PRF with
  op dkey <- dsseed,
  op doutm d <- ddgstblock
  
  proof *.
  realize dkey_ll by exact: dsseed_ll.
  realize doutm_ll by move => d; apply ddgstblock_ll. 

(* Message compression key generation function *)
op mkg : mseed -> (rm * msg) -> mkey.

clone KeyedHashFunctions as MKG with
  type key_t <- mseed,
  type in_t <- rm * msg,
  type out_t <- mkey,
  
    op f <- mkg
    
  proof *.

clone import MKG.PRF as MKG_PRF with
    op dkey <- dmseed,
    op doutm x <- dmkey 
  
  proof *.
  realize dkey_ll by exact: dmseed_ll.
  realize doutm_ll by move=> ?; apply dmkey_ll.


(* -- Tweakable Hash Functions -- *)
(* 
  Tweakable hash function collection that contains all tweakable hash functions
  used in FORS-TW, SPHINCS+ 
*)
op thfc : int -> pseed -> adrs -> dgst -> dgstblock.

(* 
  Tweakable hash function used to produce leaves from secret key values.
  (Same function as used in chains for WOTS-TW)

op f : pseed -> adrs -> dgst -> dgstblock.
*)
op f : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n).

(* Tweakable hash function used to construct Merkle trees from leaves
op trh : pseed -> adrs -> dgst -> dgstblock.
*)
op trh : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * 2).

(* Tweakable hash function used to compress WOTS public keys
op prco : pseed -> adrs -> dgst -> dgstblock.
*)
op pkco : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * len).

(* Tweakable hash function used to compress Merkle tree roots
op trco : pseed -> adrs -> dgst -> dgstblock.
*)
op trco : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * k).



(* - Underlying schemes - *)
(* FORS-TW *)
clone import FORS_TW_ES as FTWES with
    op adrs_len <- adrs_len,
    op n <- n,
    op k <- k,
    op a <- a,
    op t <- t,
    op l <- l',
    op s <- nr_trees 0,
    op d <- l,
    
  type mseed <- mseed,
  type rm <- rm,
  type mkey <- mkey,
  type sseed <- sseed,
  type pseed <- pseed,
  type msg <- msg,
  type dgst <- dgst,
    
    op nr_nodes <- nr_nodesf,
    op trhtype <- trhftype,
    op trcotype <- trcotype,

    op valid_tidx <- valid_tidx 0,
    op valid_kpidx <- valid_kpidx,
    op valid_thidx <- valid_thfidx,
    op valid_tbidx <- valid_tbfidx,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs,
    op valid_fidxvalsgp adidxs <- nth witness adidxs 0 = 0,
  
    op set_tidx <- set_tidx,
    op set_typeidx <- set_typeidx,
    op set_kpidx <- set_kpidx,
    op set_thtbidx <- set_thtbidx,
    
    op skg <- skg,
    op mkg <- mkg,
    
    op thfc <- thfc,
    op f <- f,
    op trh <- trh,
    op trco <- trco,
    
    op dmseed <- dmseed,
    op dmkey <- dmkey,  
    op dpseed <- dpseed,
    op ddgstblock <- ddgstblock,
  
  theory DigestBlock <- DigestBlock,
  theory DigestBlockFT <- DigestBlockFT,
  theory Index <- Index,
  theory HA <- HA,
  
  type dgstblock <- dgstblock,
  type index <- index,
  type adrs <- adrs
  
  proof ge5_adrslen, ge1_n, ge1_k, ge1_a, ge1_l, ge1_s, dval, dist_adrstypes, 
        valid_fidxvals_idxvals, dmseed_ll, dmkey_ll, dpseed_ll, ddgstblock_ll.
  realize ge5_adrslen by trivial.
  realize ge1_n by exact: ge1_n.
  realize ge1_k by exact ge1_k.
  realize ge1_a by exact: ge1_a.
  realize ge1_l by smt(ge1_lp).
  realize ge1_s by rewrite /nr_trees -add0r -ltzE expr_gt0.
  realize dval. 
    rewrite /nr_trees /l' /l /h -exprD_nneg /= 1:mulr_ge0; 1..3: smt(ge1_d ge0_hp).
    by congr; ring.
  qed.
  realize dist_adrstypes by smt(dist_adrstypes).
  realize valid_fidxvals_idxvals.
    rewrite /(<=) => ls @/valid_fidxvals @/valid_idxvals @/valid_fidxvalslp.
    by rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco ?nth_drop ?nth_take //= /#.
  qed.
  realize dmseed_ll by exact: dmseed_ll.
  realize dmkey_ll by exact: dmkey_ll.
  realize dpseed_ll by exact: dpseed_ll.
  realize ddgstblock_ll by exact: ddgstblock_ll.
  
import DBAL BLKAL DBAPKL DBLLKTL.


(* FL-SL-XMSS-MT-TW *)
clone import FL_SL_XMSS_MT_TW_ES as FSXMTWES with
    op adrs_len <- adrs_len,
    op n <- n,
    op log2_w <- log2_w,
    op w <- w,
    op len1 <- len1,
    op len2 <- len2,
    op len <- len,
    op h' <- h',
    op l' <- l',
    op d <- d,
    
  type sseed <- sseed,
  type pseed <- pseed,
  type dgst <- dgst,
    
    op nr_nodes <- nr_nodesx,
    op chtype <- chtype,
    op trhtype <- trhxtype,
    op pkcotype <- pkcotype,

    op valid_lidx <- valid_lidx,
    op valid_tidx <- valid_tidx,
    op valid_kpidx <- valid_kpidx,
    op valid_thidx <- valid_thxidx,
    op valid_tbidx <- valid_tbxidx,
    op valid_chidx <- valid_chidx,
    op valid_hidx <- valid_hidx,
    
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs,
    op valid_xidxvalsgp <- predT,
    
    op set_lidx <- set_lidx,
    op set_tidx <- set_tidx,
    op set_ltidx <- set_ltidx,
    op set_typeidx <- set_typeidx,
    op set_kpidx <- set_kpidx,
    op set_thtbidx <- set_thtbidx,
    
    op thfc <- thfc,
    op trh <- trh,
    op pkco <- pkco,
    op WTWES.f <- f,
    op WTWES.skg <- skg,
    
    op dpseed <- dpseed,
    op ddgstblock <- ddgstblock,
  
  theory DigestBlock <- DigestBlock,
  theory DigestBlockFT <- DigestBlockFT,
  theory Index <- Index,
  theory HA <- HA,
  
  type dgstblock <- dgstblock,
  type index <- index,
  type adrs <- adrs
  
  proof ge6_adrslen, ge1_n, val_log2w, ge0_hp, ge1_d, dist_adrstypes, 
        valid_xidxvals_idxvals, dpseed_ll, ddgstblock_ll, WTWES.WAddress.inhabited.
  realize ge6_adrslen by trivial.
  realize ge1_n by exact: ge1_n.
  realize val_log2w by exact: val_log2w.
  realize ge0_hp by exact: ge0_hp.
  realize ge1_d by exact: Top.ge1_d.
  realize dist_adrstypes by smt(Top.dist_adrstypes).
  realize valid_xidxvals_idxvals.
    move => ls @/valid_xidxvals @/valid_xidxvalslp @/predT /=.
    rewrite /valid_xidxvalslpch /valid_xidxvalslppkco /valid_xidxvalslptrh.
    by rewrite ?nth_take //= /#.
  qed.
  realize dpseed_ll by exact: dpseed_ll.
  realize ddgstblock_ll by exact: ddgstblock_ll.
  realize WTWES.WAddress.inhabited.
    exists (Adrs.insubd [0; 0; 0; chtype; 0; 0]).
    rewrite /valid_wadrs insubdK 1:/valid_adrsidxs /adrs_len /= /valid_idxvals.
    + left; rewrite /valid_idxvalsch /= /valid_kpidx /l' /valid_tidx /nr_trees.
      by rewrite ?expr_gt0 //=; smt(val_w ge2_len Top.ge1_d).
    rewrite /valid_wadrsidxs /adrs_len /= /valid_widxvals /predT /=.
    rewrite /valid_kpidx /valid_tidx /l' ?expr_gt0 //=. 
    by rewrite /valid_widxvalslp; smt(val_w ge2_len Top.ge1_d).
  qed.
  
import DBHPL SAPDL.
import WTWES DBLL EmsgWOTS WAddress.



(* - Types (3/3) - *)
(* -- SPHINCS+-TW specific -- *)
(* Public keys *)
type pkSPHINCSPLUSTW = dgstblock * pseed.

(* Secret keys *)
type skSPHINCSPLUSTW = mseed * sseed * pseed.

(* Signatures *)
type sigSPHINCSPLUSTW = mkey * sigFORSTW * sigFLSLXMSSMTTW. 



(* - Definitions and security models for digital signatures  - *)
clone import DigitalSignatures as DSS with
  type pk_t <- pkSPHINCSPLUSTW,
  type sk_t <- skSPHINCSPLUSTW,
  type msg_t <- msg,
  type sig_t <- sigSPHINCSPLUSTW
  
  proof *.

import DSS.Stateless.



(* - Specification - *)
module SPHINCS_PLUS_TW : Scheme = {
  proc keygen() : pkSPHINCSPLUSTW * skSPHINCSPLUSTW = {
    var ad : adrs;
    var ms : mseed;
    var ss : sseed;
    var ps : pseed;
    var root : dgstblock;
    var pk : pkSPHINCSPLUSTW;
    var sk : skSPHINCSPLUSTW;
    
    ad <- insubd [0; 0; chtype; 0; 0; 0];
    
    ms <$ dmseed;
    ss <$ dsseed;
    
    ps <$ dpseed;
    root <@ FL_SL_XMSS_MT_TW_ES.gen_root(ss, ps, ad);
    
    pk <- (root, ps);
    sk <- (ms, ss, ps);
    
    return (pk, sk);
  }
  
  proc sign(sk : skSPHINCSPLUSTW, m : msg) : sigSPHINCSPLUSTW = {
    var ms : mseed;
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var pkFORS : pkFORS;
    var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
    var sig : sigSPHINCSPLUSTW;
        
    (ms, ss, ps) <- sk;
    
    ad <- insubd [0; 0; chtype; 0; 0; 0];
    
    (mk, sigFORSTW) <@ M_FORS_TW_ES.sign((ms, ss, ps, ad), m);
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    pkFORS <@ FL_FORS_TW_ES.gen_pkFORS(ss, ps, set_kpidx (set_tidx (set_typeidx (set_lidx ad 0) trhftype) tidx) kpidx);
    
    sigFLSLXMSSMTTW <@ FL_SL_XMSS_MT_TW_ES.sign((ss, ps, ad), pkFORS, idx);
    
    return (mk, sigFORSTW, sigFLSLXMSSMTTW);
  }
  
  proc verify(pk : pkSPHINCSPLUSTW, m : msg, sig : sigSPHINCSPLUSTW) : bool = {
    var root, root' : dgstblock;
    var ps : pseed;
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
    var ad : adrs;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var pkFORS : pkFORS;
    
    (root, ps) <- pk;
    (mk, sigFORSTW, sigFLSLXMSSMTTW) <- sig;
    
    ad <- insubd [0; 0; chtype; 0; 0; 0];
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    pkFORS <@ FL_FORS_TW_ES.pkFORS_from_sigFORSTW(sigFORSTW, cm, ps, set_kpidx (set_tidx (set_typeidx (set_lidx ad 0) trhftype) tidx) kpidx);
    
    root' <@ FL_SL_XMSS_MT_TW_ES.root_from_sigFLSLXMSSMTTW(pkFORS, sigFLSLXMSSMTTW, idx, ps, ad);
    
    return root' = root;
  }
}.



(* - Proof - *)
(* -- Reduction adversaries -- *)
module (R_SKGPRF_EUFCMA (A : Adv_EUFCMA) : SKG_PRF.Adv_PRF) (O : SKG_PRF.Oracle_PRF) = {
  proc distinguish() : bool = {
    
    return witness;
  }
}.

module (R_MKGPRF_EUFCMA (A : Adv_EUFCMA) : MKG_PRF.Adv_PRF) (O : MKG_PRF.Oracle_PRF) = {
  proc distinguish() : bool = {
    return witness;
  }
}.

module (R_MFORSTWESNPRFEUFCMA_EUFCMA (A : Adv_EUFCMA) : Adv_EUFCMA_MFORSTWESNPRF) (O : SOracle_CMA_MFORSTWESNPRF) = {
  proc forge(pk : pkFORS list list * pseed * adrs) : msg * (mkey * sigFORSTW) = {
    return witness;
  }
}.

module R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA (A : Adv_EUFCMA) : Adv_EUFNACMA_FLSLXMSSMTTWESNPRF = {
  proc choose(pk : pkFLSLXMSSMTTW) : msgFLSLXMSSMTTW list = {
    return witness;
  }
  
  proc forge(sigl : sigFLSLXMSSMTTW list) : msgFLSLXMSSMTTW * sigFLSLXMSSMTTW * index = {
    return witness;
  }
}.


section Proof_SPHINCS_PLUS_TW_EUFCMA.

local module SPHINCS_PLUS_TW_Aux = {
  proc keygen_prf() : pkSPHINCSPLUSTW * (skFORS list list * skWOTS list list list * pseed) = {
    var ad : adrs;
    var ms : mseed;
    var ss : sseed;
    var ps : pseed;
    var skFORS_ele : dgstblock;
    var skFORSet : dgstblock list;
    var skFORS : dgstblock list list;
    var skFORSlp : skFORS list; 
    var skFORSnt : skFORS list list;
    var skWOTS_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt : skWOTS list list;
    var skWOTStd : skWOTS list list list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var pk : pkSPHINCSPLUSTW;
    var sk : skFORS list list * skWOTS list list list * pseed;
    
    ad <- insubd [0; 0; chtype; 0; 0; 0];
    
    ms <$ dmseed;
    ss <$ dsseed;
    
    ps <$ dpseed;
    
    
    skFORSnt <- [];
    while (size skFORSnt < nr_trees 0) {
      skFORSlp <- [];
      while (size skFORSlp < l') {
         skFORS <- [];
         while (size skFORS < k) {
          skFORSet <- [];
          while (size skFORSet < t) {
            skFORS_ele <- skg ss (ps, set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhftype) (size skFORSnt)) (size skFORSlp)) 0 (size skFORS * t + size skFORSet));
            skFORSet <- rcons skFORSet skFORS_ele;
          }
          skFORS <- rcons skFORS skFORSet;  
        }
        skFORSlp <- rcons skFORSlp (insubd skFORS);  
      }
      skFORSnt <- rcons skFORSnt skFORSlp;
    }
    
    skWOTStd <- [];
    while (size skWOTStd < d) {
      skWOTSnt <- [];
      while (size skWOTSnt < nr_trees (size skWOTStd)) {
        skWOTSlp <- [];
        while (size skWOTSlp < l') {
          skWOTS <- [];
          while (size skWOTS < len) {
            skWOTS_ele <- skg ss (ps, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) chtype) (size skWOTSlp)) (size skWOTS)) 0);
            skWOTS <- rcons skWOTS skWOTS_ele;  
          }
          
          (* Add WOTS-TW secret key to list of secret keys of this inner tree *)
          skWOTSlp <- rcons skWOTSlp (DBLL.insubd skWOTS);
        }
        
        (* Add secret key of inner tree to list of secret keys in this layer *)
        skWOTSnt <- rcons skWOTSnt skWOTSlp;
      }
      (* Add secret key of layer to list of secret keys for all layers *)
      skWOTStd <- rcons skWOTStd skWOTSnt; 
    }

    (* 
      Extract secret key of the top-most inner tree in the hyper tree 
      and compute the corresponding leaves.
    *)
    skWOTSlp <- nth witness (nth witness skWOTStd (d - 1)) 0;
    leaves <@ FL_SL_XMSS_MT_TW_ES_NPRF.leaves_from_sklpsad(skWOTSlp, ps, set_ltidx ad (d - 1) 0);
    
    (*
      Compute root (hash value) from the computed list of leaves, given public seed, and
      given address (after setting the type to tree hashing)
    *)
    root <- val_bt_trh ps (set_typeidx (set_ltidx ad (d - 1) 0) trhxtype) (list2tree leaves) h' 0;
    
    pk <- (root, ps);
    sk <- (skFORSnt, skWOTStd, ps);

    return (pk, sk);
  }

  proc keygen_nprf() : pkSPHINCSPLUSTW * (skFORS list list * skWOTS list list list * pseed) = {
    var ad : adrs;
    var ms : mseed;
    var ss : sseed;
    var ps : pseed;
    var skFORS_ele : dgstblock;
    var skFORSet : dgstblock list;
    var skFORS : dgstblock list list;
    var skFORSlp : skFORS list; 
    var skFORSnt : skFORS list list;
    var skWOTS_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt : skWOTS list list;
    var skWOTStd : skWOTS list list list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var pk : pkSPHINCSPLUSTW;
    var sk : skFORS list list * skWOTS list list list * pseed;
    
    ad <- insubd [0; 0; chtype; 0; 0; 0];
    
    ms <$ dmseed;
    ss <$ dsseed;
    
    ps <$ dpseed;
    
    
    skFORSnt <- [];
    while (size skFORSnt < nr_trees 0) {
      skFORSlp <- [];
      while (size skFORSlp < l') {
         skFORS <- [];
         while (size skFORS < k) {
          skFORSet <- [];
          while (size skFORSet < t) {
            skFORS_ele <$ ddgstblock;
            skFORSet <- rcons skFORSet skFORS_ele;
          }
          skFORS <- rcons skFORS skFORSet;  
        }
        skFORSlp <- rcons skFORSlp (insubd skFORS);  
      }
      skFORSnt <- rcons skFORSnt skFORSlp;
    }
    
    skWOTStd <- [];
    while (size skWOTStd < d) {
      skWOTSnt <- [];
      while (size skWOTSnt < nr_trees (size skWOTStd)) {
        skWOTSlp <- [];
        while (size skWOTSlp < l') {
          skWOTS <- [];
          while (size skWOTS < len) {
            skWOTS_ele <$ ddgstblock;
            skWOTS <- rcons skWOTS skWOTS_ele;  
          }
          
          (* Add WOTS-TW secret key to list of secret keys of this inner tree *)
          skWOTSlp <- rcons skWOTSlp (DBLL.insubd skWOTS);
        }
        
        (* Add secret key of inner tree to list of secret keys in this layer *)
        skWOTSnt <- rcons skWOTSnt skWOTSlp;
      }
      (* Add secret key of layer to list of secret keys for all layers *)
      skWOTStd <- rcons skWOTStd skWOTSnt; 
    }

    (* 
      Extract secret key of the top-most inner tree in the hyper tree 
      and compute the corresponding leaves.
    *)
    skWOTSlp <- nth witness (nth witness skWOTStd (d - 1)) 0;
    leaves <@ FL_SL_XMSS_MT_TW_ES_NPRF.leaves_from_sklpsad(skWOTSlp, ps, set_ltidx ad (d - 1) 0);
    
    (*
      Compute root (hash value) from the computed list of leaves, given public seed, and
      given address (after setting the type to tree hashing)
    *)
    root <- val_bt_trh ps (set_typeidx (set_ltidx ad (d - 1) 0) trhxtype) (list2tree leaves) h' 0;
    
    pk <- (root, ps);
    sk <- (skFORSnt, skWOTStd, ps);

    return (pk, sk);
  }
    
  proc sign(sk : skSPHINCSPLUSTW, m : msg) : sigSPHINCSPLUSTW = {
    var ms : mseed;
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var pkFORS : pkFORS;
    var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
    var sig : sigSPHINCSPLUSTW;
        
    (ms, ss, ps) <- sk;
    
    ad <- witness;
    
    (mk, sigFORSTW) <@ M_FORS_TW_ES.sign((ms, ss, ps, set_lidx ad 0), m);
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    pkFORS <@ FL_FORS_TW_ES.gen_pkFORS(ss, ps, set_kpidx (set_tidx (set_typeidx (set_lidx ad 0) trhftype) tidx) kpidx);
    
    sigFLSLXMSSMTTW <@ FL_SL_XMSS_MT_TW_ES.sign((ss, ps, ad), pkFORS, idx);
    
    return (mk, sigFORSTW, sigFLSLXMSSMTTW);
  }
  
  proc verify(pk : pkSPHINCSPLUSTW, m : msg, sig : sigSPHINCSPLUSTW) : bool = {
    var root, root' : dgstblock;
    var ps : pseed;
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
    var ad : adrs;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var pkFORS : pkFORS;
    
    (root, ps) <- pk;
    (mk, sigFORSTW, sigFLSLXMSSMTTW) <- sig;
    
    ad <- witness;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    pkFORS <@ FL_FORS_TW_ES.pkFORS_from_sigFORSTW(sigFORSTW, cm, ps, set_kpidx (set_tidx (set_typeidx (set_lidx ad 0) trhftype) tidx) kpidx);
    
    root' <@ FL_SL_XMSS_MT_TW_ES.root_from_sigFLSLXMSSMTTW(pkFORS, sigFLSLXMSSMTTW, idx, ps, ad);
    
    return root' = root;
  }
}.

declare module A <: Adv_EUFCMA {}.


(* 
  Proof functional equivalence between original SPHINCS_PLUS_TW and a variant that immediately generates all
  necessary secret values (for both the FORS and XMSS-MT parts) and maintains this collection of secret values 
  throughout, pulling the desired secret values from this collection when neeeded (instead of regenerating them via
  skg).  
*)

(*
  Define variant that 
*)



local lemma EUFCMA_SPHINCS_PLUS_TW_FX &m :
  Pr[EUF_CMA(SPHINCS_PLUS_TW, A, O_CMA_Default).main() @ &m : res]
  <= 
  `|  Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(true) @ &m : res]
    - Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(false) @ &m : res] |
  +
  `|  Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(true) @ &m : res]
    - Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(false) @ &m : res] |
  +  
  Pr[EUF_CMA_MFORSTWESNPRF(R_MFORSTWESNPRFEUFCMA_EUFCMA(A), O_CMA_MFORSTWESNPRF).main() @ &m : res]
  +
  Pr[EUF_NACMA_FLSLXMSSMTTWESNPRF(R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA(A)).main() @ &m : res].
proof. admit. qed.

(* TODO: replace OpenPRE by DSPR and TCR *)
lemma EUFCMA_SPHINCS_PLUS_TW &m :
  Pr[EUF_CMA(SPHINCS_PLUS_TW, A, O_CMA_Default).main() @ &m : res]
  <= 
  `|  Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(true) @ &m : res]
    - Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(false) @ &m : res] |
  +
  `|  Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(true) @ &m : res]
    - Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(false) @ &m : res] |
  +
  Pr[MCO_ITSR.ITSR(R_EUFCMA_ITSR(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), MCO_ITSR.O_ITSR_Default).main() @ &m : res]
  +
  Pr[FC_OpenPRE.SM_DT_OpenPRE_C(R_EUFCMA_FSMDTOpenPREC(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), FC_OpenPRE.O_SMDTOpenPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[FC_TCR.SM_DT_TCR_C(R_EUFCMA_FSMDTTCRC(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
  + 
  Pr[TRHC_TCR.SM_DT_TCR_C(R_EUFCMA_TRHSMDTTCRC(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_EUFCMA_TRCOSMDTTCRC(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res]  
  +
  (w - 2)%r
    * `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNACMA(R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA(A))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res]
        - Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNACMA(R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA(A))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]| 
  + 
  Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNACMA(R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA(A))), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res] 
  + 
  Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNACMA(R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA(A))), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFNACMA(R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA(A)), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFNACMA(R_FLSLXMSSMTTWESNPRFEUFNACMA_EUFCMA(A)), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res].
proof. admit. qed.
 
end section Proof_SPHINCS_PLUS_TW_EUFCMA.
