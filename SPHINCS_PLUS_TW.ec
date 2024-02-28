(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr SmtMap IntDiv RealExp StdOrder FinType BitEncoding.
(*---*) import IntOrder RealOrder.
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

(* Randomness for non-deterministic signature generation
type rm.
*)

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

(* Initialization ("zero") address *)
const adz : adrs = insubd [0; 0; chtype; 0; 0; 0].



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

(* Message compression key generation function
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
*)
op mkg : mseed -> msg -> mkey.

clone KeyedHashFunctions as MKG with
  type key_t <- mseed,
  type in_t <- msg,
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
  (* type rm <- rm, *)
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
  
import DBAL BLKAL DBAPKL DBLLKTL FP_OPRETCRDSPR.


(* FL-SL-XMSS-MT-TW *)
clone import FL_SL_XMSS_MT_TW_ES as FSSLXMTWES with
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
    op nr_trees <- nr_trees,
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
import WTWES DBLL EmsgWOTS WAddress FC.



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
    
    ad <- adz;
    
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
    
    ad <- adz;
    
    (mk, sigFORSTW) <@ M_FORS_TW_ES.sign((ms, ss, ps, ad), m);
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    pkFORS <@ FL_FORS_TW_ES.gen_pkFORS(ss, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx);
    
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
    
    ad <- adz;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    pkFORS <@ FL_FORS_TW_ES.pkFORS_from_sigFORSTW(sigFORSTW, cm, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx);
    
    root' <@ FL_SL_XMSS_MT_TW_ES.root_from_sigFLSLXMSSMTTW(pkFORS, sigFLSLXMSSMTTW, idx, ps, ad);
    
    return root' = root;
  }
}.



(* - Proof - *)
(* -- Reduction adversaries -- *)
module (R_SKGPRF_EUFCMA (A : Adv_EUFCMA) : SKG_PRF.Adv_PRF) (O : SKG_PRF.Oracle_PRF) = {
  var ms : mseed
  var ps : pseed
  var skFORSnt : skFORS list list
  var skWOTStd : skWOTS list list list
  var qs : msg list
  
  module O_CMA : SOracle_CMA = {
    proc sign(m : msg) : sigSPHINCSPLUSTW = {
      var skFORS : skFORS;
      var pkFORS : pkFORS;
      var skWOTS : skWOTS;
      var ad : adrs;
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx : int;
      var sigFORSTW : sigFORSTW;
      var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;

      ad <- adz;

      (* rm <$ drm;
         mk <- mkg ms (rm, m); *)
      mk <- mkg ms m;

      (cm, idx) <- mco mk m;

      (tidx, kpidx) <- edivz (val idx) l';

      skFORS <- nth witness (nth witness skFORSnt tidx) kpidx;

      sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx), cm);

      pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx);

      sigFLSLXMSSMTTW <@ FL_SL_XMSS_MT_TW_ES_NPRF.sign((skWOTStd, ps, ad), pkFORS, idx);

      qs <- rcons qs m;

      return (mk, sigFORSTW, sigFLSLXMSSMTTW);
    }
  }
  
  proc distinguish() : bool = {
    var ad : adrs;
    var ps : pseed;
    var skFORS_ele : dgstblock;
    var skFORSet : dgstblock list;
    var skFORS : dgstblock list list;
    var skFORSlp : skFORS list; 
    var skWOTS_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt : skWOTS list list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var pk : pkSPHINCSPLUSTW;
    var m' : msg;
    var sig' : sigSPHINCSPLUSTW;
    var is_valid, is_fresh : bool;
    
    (* Initialize module variables (for oracle usage) *)
    skFORSnt <- [];
    skWOTStd <- [];
    qs <- [];
    ms <$ dmseed;
    ps <$ dpseed;
    
    ad <- adz;
    
    skFORSnt <- [];
    while (size skFORSnt < nr_trees 0) {
      skFORSlp <- [];
      while (size skFORSlp < l') {
         skFORS <- [];
         while (size skFORS < k) {
          skFORSet <- [];
          while (size skFORSet < t) {
            skFORS_ele <@ O.query(ps, set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhftype) (size skFORSnt)) (size skFORSlp)) 0 (size skFORS * t + size skFORSet));
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
            skWOTS_ele <@ O.query(ps, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) chtype) (size skWOTSlp)) (size skWOTS)) 0);
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
    
    
    (* Ask adversary to forge *)
    (m', sig') <@ A(O_CMA).forge(pk);
    
    
    (* Check whether forgery is valid *)
    is_valid <@ SPHINCS_PLUS_TW.verify(pk, m', sig');
    
    (* Check whether message from forgery is fresh *)
    is_fresh <- ! m' \in qs;
    
    return is_valid /\ is_fresh;
  }
}.

module (R_MKGPRF_EUFCMA (A : Adv_EUFCMA) : MKG_PRF.Adv_PRF) (O : MKG_PRF.Oracle_PRF) = {
  var ps : pseed
  var skFORSnt : skFORS list list
  var skWOTStd : skWOTS list list list
  var qs : msg list
  
  module O_CMA : SOracle_CMA = {
    proc sign(m : msg) : sigSPHINCSPLUSTW = {
      var skFORS : skFORS;
      var pkFORS : pkFORS;
      var skWOTS : skWOTS;
      var ad : adrs;
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx : int;
      var sigFORSTW : sigFORSTW;
      var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;

      ad <- adz;

      (* rm <$ drm;
         mk <- mkg ms (rm, m); *)
      mk <@ O.query(m);

      (cm, idx) <- mco mk m;

      (tidx, kpidx) <- edivz (val idx) l';

      skFORS <- nth witness (nth witness skFORSnt tidx) kpidx;

      sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx), cm);

      pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx);

      sigFLSLXMSSMTTW <@ FL_SL_XMSS_MT_TW_ES_NPRF.sign((skWOTStd, ps, ad), pkFORS, idx);

      qs <- rcons qs m;

      return (mk, sigFORSTW, sigFLSLXMSSMTTW);
    }
  }
  
  proc distinguish() : bool = {
    var ad : adrs;
    var ps : pseed;
    var skFORS_ele : dgstblock;
    var skFORSet : dgstblock list;
    var skFORS : dgstblock list list;
    var skFORSlp : skFORS list; 
    var skWOTS_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt : skWOTS list list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var pk : pkSPHINCSPLUSTW;
    var m' : msg;
    var sig' : sigSPHINCSPLUSTW;
    var is_valid, is_fresh : bool;

    (* Initialize module variables (for oracle usage) *)
    qs <- [];
    ps <$ dpseed;
    
    ad <- adz;
    
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
    
    
    (* Ask adversary to forge *)
    (m', sig') <@ A(O_CMA).forge(pk);
    
    
    (* Check whether forgery is valid *)
    is_valid <@ SPHINCS_PLUS_TW.verify(pk, m', sig');
    
    (* Check whether message from forgery is fresh *)
    is_fresh <- ! m' \in qs;
    
    return is_valid /\ is_fresh;
  }
}.

module (R_MFORSTWESNPRFEUFCMA_EUFCMA (A : Adv_EUFCMA) : Adv_EUFCMA_MFORSTWESNPRF) (O : SOracle_CMA_MFORSTWESNPRF) = {
  var pkFORSnt : pkFORS list list
  var skWOTStd : skWOTS list list list
  var ps : pseed
  var ad : adrs
   
  module O_CMA : SOracle_CMA = {
    proc sign(m : msg) : sigSPHINCSPLUSTW = {
      var mk : mkey;
      var sigFORSTW : sigFORSTW;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx : int;
      var pkFORS : pkFORS;
      var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
      
      (mk, sigFORSTW) <@ O.sign(m);
      
      (cm, idx) <- mco mk m; 
      
      (tidx, kpidx) <- edivz (val idx) l';
      
      pkFORS <- nth witness (nth witness pkFORSnt tidx) kpidx;
      
      sigFLSLXMSSMTTW <@ FL_SL_XMSS_MT_TW_ES_NPRF.sign((skWOTStd, ps, ad), pkFORS, idx);
      
      return (mk, sigFORSTW, sigFLSLXMSSMTTW);
    }
  }
  
  proc forge(pk : pkFORS list list * pseed * adrs) : msg * (mkey * sigFORSTW) = {
    var skWOTS_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt : skWOTS list list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var m' : msg;
    var sig' : sigSPHINCSPLUSTW;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var sigFLSLXMSSMTTW' : sigFLSLXMSSMTTW; 
    
    (pkFORSnt, ps, ad) <- pk;
    
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
    

    (* Ask adversary to forge *)
    (m', sig') <@ A(O_CMA).forge((root, ps));
    
    (mk', sigFORSTW', sigFLSLXMSSMTTW') <- sig';
    
    return (m', (mk', sigFORSTW'));
  }
}.

(*
module R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA (A : Adv_EUFCMA) : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF = {
  var skFORSnt : skFORS list list
  var pkFORSnt : pkFORS list list
  var root : dgstblock
  var ps : pseed
  var ad : adrs
  var sigFLSLXMSSMTTWl : sigFLSLXMSSMTTW list
  
  module O_CMA : SOracle_CMA = {
    proc sign(m : msg) : sigSPHINCSPLUSTW = {
      var mk : mkey;
      var sigFORSTW : sigFORSTW;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx : int;
      var skFORS : skFORS;
      var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
      
      mk <$ dmkey;
      
      (cm, idx) <- mco mk m; 
      
      (tidx, kpidx) <- edivz (val idx) l';
      
      skFORS <- nth witness (nth witness skFORSnt tidx) kpidx;
      
      sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_typeidx (set_ltidx ad 0 tidx) trhftype) kpidx), cm); 
      
      sigFLSLXMSSMTTW <- nth witness sigFLSLXMSSMTTWl (val idx);
      
      return (mk, sigFORSTW, sigFLSLXMSSMTTW);
    }
  }

  proc choose(pk : pkFLSLXMSSMTTW) : msgFLSLXMSSMTTW list = {
    var skFORS_ele : dgstblock;
    var skFORSet : dgstblock list;
    var skFORS : dgstblock list list;
    var skFORSlp : skFORS list; 
    var pkFORS : pkFORS;
    var pkFORSlp : pkFORS list;
    
    (root, ps, ad) <- pk;
    
    skFORSnt <- [];
    pkFORSnt <- [];
    while (size skFORSnt < nr_trees 0) {
      skFORSlp <- [];
      pkFORSlp <- [];
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
        pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(insubd skFORS, ps, set_kpidx (set_typeidx (set_ltidx ad 0 (size skFORSnt)) trhftype) (size skFORSlp));
        skFORSlp <- rcons skFORSlp (insubd skFORS);
        pkFORSlp <- rcons pkFORSlp pkFORS;  
      }
      skFORSnt <- rcons skFORSnt skFORSlp;
      pkFORSnt <- rcons pkFORSnt pkFORSlp;
    }
    
    return flatten pkFORSnt;
  }
  
  proc forge(sigl : sigFLSLXMSSMTTW list) : msgFLSLXMSSMTTW * sigFLSLXMSSMTTW * index = {
    var m' : msg;
    var sig' : sigSPHINCSPLUSTW;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var sigFLSLXMSSMTTW' : sigFLSLXMSSMTTW;
    var cm' : msgFORSTW;
    var idx' : index;
    var tidx', kpidx' : int;
    var pkFORS' : pkFORS;
    
    sigFLSLXMSSMTTWl <- sigl;
    
    (* Ask adversary to forge *)
    (m' , sig') <@ A(O_CMA).forge((root, ps));
    
    (mk', sigFORSTW', sigFLSLXMSSMTTW') <- sig';
    
    (cm', idx') <- mco mk' m';
     
    (tidx', kpidx') <- edivz (val idx') l';
       
    pkFORS' <@ FL_FORS_TW_ES.pkFORS_from_sigFORSTW(sigFORSTW', cm', ps, set_kpidx (set_typeidx (set_ltidx ad 0 tidx') trhftype) kpidx');
   
    return (pkFORS', sigFLSLXMSSMTTW', idx');
  }
}.
*)
module (R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA (A : Adv_EUFCMA) : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF) (OC : Oracle_THFC) = {
  var skFORSnt : skFORS list list
  var pkFORSnt : pkFORS list list
  var root : dgstblock
  var ps : pseed
  var ad : adrs
  var sigFLSLXMSSMTTWl : sigFLSLXMSSMTTW list
  
  module O_CMA : SOracle_CMA = {
    proc sign(m : msg) : sigSPHINCSPLUSTW = {
      var mk : mkey;
      var sigFORSTW : sigFORSTW;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx : int;
      var skFORS : skFORS;
      var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
      
      mk <$ dmkey;
      
      (cm, idx) <- mco mk m; 
      
      (tidx, kpidx) <- edivz (val idx) l';
      
      skFORS <- nth witness (nth witness skFORSnt tidx) kpidx;
      
      sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_typeidx (set_ltidx ad 0 tidx) trhftype) kpidx), cm); 
      
      sigFLSLXMSSMTTW <- nth witness sigFLSLXMSSMTTWl (val idx);
      
      return (mk, sigFORSTW, sigFLSLXMSSMTTW);
    }
  }

  proc choose() : msgFLSLXMSSMTTW list = {
    var skFORS_ele : dgstblock;
    var skFORSet : dgstblock list;
    var skFORS : dgstblock list list;
    var skFORSlp : skFORS list; 
    var pkFORS : pkFORS;
    var pkFORSlp : pkFORS list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var kpidx : int;
    var leaf : dgstblock;
    var nodes : dgstblock list list;
    var nodespl, nodescl : dgstblock list;
    var lnode, rnode, node : dgstblock;
    
    ad <- adz;
    
    skFORSnt <- [];
    pkFORSnt <- [];
    while (size skFORSnt < nr_trees 0) {
      skFORSlp <- [];
      pkFORSlp <- [];
      while (size skFORSlp < l') {
        skFORS <- [];
        roots <- [];
        while (size skFORS < k) {
          skFORSet <- [];
          leaves <- [];
          while (size skFORSet < t) {
            skFORS_ele <$ ddgstblock;
            leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhftype) (size skFORSnt)) (size skFORSlp)) 
                                         0 (size skFORS * t + size skFORSet), 
                             (val skFORS_ele));
            skFORSet <- rcons skFORSet skFORS_ele;
            leaves <- rcons leaves leaf;
          }
          
          skFORS <- rcons skFORS skFORSet; 
          
          (* root <- val_bt_trh ps ad (list2tree leaves) (size roots); *)
          nodes <- [];
          while (size nodes < a) {
            nodespl <- last leaves nodes;
            
            nodescl <- [];
            while (size nodescl < nr_nodesf (size nodes + 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              node <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhftype) (size skFORSnt)) (size skFORSlp)) 
                                           (size nodes + 1) (size skFORS * nr_nodesf (size nodes + 1) + size nodescl), 
                               val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node;      
            }
            nodes <- rcons nodes nodescl;
          }
          roots <- rcons roots (nth witness (nth witness nodes (a - 1)) 0);
        }
        
        pkFORS <@ OC.query(set_kpidx (set_tidx (set_typeidx ad trcotype) (size skFORSnt)) (size skFORSlp), 
                           flatten (map DigestBlock.val roots));
                           
        skFORSlp <- rcons skFORSlp (insubd skFORS);
        pkFORSlp <- rcons pkFORSlp pkFORS;
      }
      skFORSnt <- rcons skFORSnt skFORSlp;
      pkFORSnt <- rcons pkFORSnt pkFORSlp;
    }
    
    return flatten pkFORSnt;
  }
  
  proc forge(pk : pkFLSLXMSSMTTW, sigl : sigFLSLXMSSMTTW list) : msgFLSLXMSSMTTW * sigFLSLXMSSMTTW * index = {
    var m' : msg;
    var sig' : sigSPHINCSPLUSTW;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var sigFLSLXMSSMTTW' : sigFLSLXMSSMTTW;
    var cm' : msgFORSTW;
    var idx' : index;
    var tidx', kpidx' : int;
    var pkFORS' : pkFORS;
    
    (root, ps, ad) <- pk;
    
    sigFLSLXMSSMTTWl <- sigl;
    
    (* Ask adversary to forge *)
    (m' , sig') <@ A(O_CMA).forge((root, ps));
    
    (mk', sigFORSTW', sigFLSLXMSSMTTW') <- sig';
    
    (cm', idx') <- mco mk' m';
     
    (tidx', kpidx') <- edivz (val idx') l';
       
    pkFORS' <@ FL_FORS_TW_ES.pkFORS_from_sigFORSTW(sigFORSTW', cm', ps, set_kpidx (set_typeidx (set_ltidx ad 0 tidx') trhftype) kpidx');
   
    return (pkFORS', sigFLSLXMSSMTTW', idx');
  }
}.



section Proof_SPHINCS_PLUS_TW_EUFCMA.


declare module A <: Adv_EUFCMA {-MCO_ITSR.O_ITSR_Default, -F_OpenPRE.O_SMDTOpenPRE_Default, -FTWES.FC_TCR.O_SMDTTCR_Default, -FP_OpenPRE.O_SMDTOpenPRE_Default, -FTWES.TRHC_TCR.O_SMDTTCR_Default, -TRCOC.O_THFC_Default, -TRCOC_TCR.O_SMDTTCR_Default, -O_CMA_MFORSTWESNPRF, -R_ITSR_EUFCMA, -R_FSMDTOpenPRE_EUFCMA, -R_TRHSMDTTCRC_EUFCMA, -R_TRCOSMDTTCRC_EUFCMA, -PKCOC.O_THFC_Default, -PKCOC_TCR.O_SMDTTCR_Default, -TRHC.O_THFC_Default, -TRHC_TCR.O_SMDTTCR_Default, -O_THFC_Default, -FC_UD.O_SMDTUD_Default, -FC_TCR.O_SMDTTCR_Default, -FC_PRE.O_SMDTPRE_Default, -O_MEUFGCMA_WOTSTWESNPRF, -R_SMDTPREC_Game4WOTSTWES, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA, -R_SMDTTCRCPKCO_EUFNAGCMA, -R_SMDTTCRCTRH_EUFNAGCMA, -R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA, -O_CMA_Default}.

declare axiom A_forge_ll (O <: SOracle_CMA{-A}) :
  islossless O.sign => islossless A(O).forge.

  
local module SPHINCS_PLUS_TW_FS = {
  proc keygen_prf() : pkSPHINCSPLUSTW * (mseed * skFORS list list * skWOTS list list list * pseed) = {
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
    var sk : mseed * skFORS list list * skWOTS list list list * pseed;
    
    ad <- adz;
    
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
          skWOTSlp <- rcons skWOTSlp (DBLL.insubd skWOTS);
        }  
        skWOTSnt <- rcons skWOTSnt skWOTSlp;
      }
      skWOTStd <- rcons skWOTStd skWOTSnt; 
    }

    skWOTSlp <- nth witness (nth witness skWOTStd (d - 1)) 0;
    leaves <@ FL_SL_XMSS_MT_TW_ES_NPRF.leaves_from_sklpsad(skWOTSlp, ps, set_ltidx ad (d - 1) 0);
    root <- val_bt_trh ps (set_typeidx (set_ltidx ad (d - 1) 0) trhxtype) (list2tree leaves) h' 0;
    
    pk <- (root, ps);
    sk <- (ms, skFORSnt, skWOTStd, ps);

    return (pk, sk);
  }

  proc keygen_nprf() : pkSPHINCSPLUSTW * (mseed * skFORS list list * skWOTS list list list * pseed) = {
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
    var sk : mseed * skFORS list list * skWOTS list list list * pseed;
    
    ad <- adz;
    
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
          skWOTSlp <- rcons skWOTSlp (DBLL.insubd skWOTS);
        }
        skWOTSnt <- rcons skWOTSnt skWOTSlp;
      }
      skWOTStd <- rcons skWOTStd skWOTSnt; 
    }

    skWOTSlp <- nth witness (nth witness skWOTStd (d - 1)) 0;
    leaves <@ FL_SL_XMSS_MT_TW_ES_NPRF.leaves_from_sklpsad(skWOTSlp, ps, set_ltidx ad (d - 1) 0);
    
    root <- val_bt_trh ps (set_typeidx (set_ltidx ad (d - 1) 0) trhxtype) (list2tree leaves) h' 0;
    
    pk <- (root, ps);
    sk <- (ms, skFORSnt, skWOTStd, ps);

    return (pk, sk);
  }
  
  proc verify = SPHINCS_PLUS_TW.verify
}.


local module O_CMA_SPHINCSPLUSTWFS_PRF : SOracle_CMA = {
  var sk : mseed * skFORS list list * skWOTS list list list * pseed
  var qs : msg list
  
  proc init(sk_init : mseed * skFORS list list * skWOTS list list list * pseed) : unit = {
    sk <- sk_init;
    qs <- [];
  }
  
  proc sign(m : msg) : sigSPHINCSPLUSTW = {
    var ms : mseed;
    var skFORS : skFORS;
    var pkFORS : pkFORS;
    var skFORSnt : skFORS list list;
    var skWOTS : skWOTS;
    var skWOTStd : skWOTS list list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sigFORSTW : sigFORSTW;
    var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
    
    (ms, skFORSnt, skWOTStd, ps) <- sk;
    
    ad <- adz;
    
    (* rm <$ drm;
       mk <- mkg ms (rm, m); *)
    mk <- mkg ms m;
         
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    skFORS <- nth witness (nth witness skFORSnt tidx) kpidx;
     
    sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx), cm);
    
    pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx);
    
    sigFLSLXMSSMTTW <@ FL_SL_XMSS_MT_TW_ES_NPRF.sign((skWOTStd, ps, ad), pkFORS, idx);
    
    qs <- rcons qs m;
    
    return (mk, sigFORSTW, sigFLSLXMSSMTTW);
  }
  
  proc fresh(m : msg) : bool = {
    return ! (m \in qs);
  }
  
  proc nr_queries() : int = {
    return size qs;
  }
}.


local module O_CMA_SPHINCSPLUSTWFS_NPRF : SOracle_CMA = {
  include var O_CMA_SPHINCSPLUSTWFS_PRF [-init, sign]
  (* var rmmap : (rm * msg, mkey) fmap *)
  var mmap : (msg, mkey) fmap
  
  proc init(sk_init : mseed * skFORS list list * skWOTS list list list * pseed) : unit = {
    sk <- sk_init;
    qs <- [];
    mmap <- empty;
  }

  proc sign(m : msg) : sigSPHINCSPLUSTW = {
    var ms : mseed;
    var skFORS : skFORS;
    var pkFORS : pkFORS;
    var skFORSnt : skFORS list list;
    var skWOTS : skWOTS;
    var skWOTStd : skWOTS list list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sigFORSTW : sigFORSTW;
    var sigFLSLXMSSMTTW : sigFLSLXMSSMTTW;
    
    (ms, skFORSnt, skWOTStd, ps) <- sk;
    
    ad <- adz;
    
    (* rm <$ drm; *)
    
    if (m \notin mmap) { 
      mk <$ dmkey;
      mmap.[m] <- mk;
    } else {
      mk <- oget mmap.[m];
    }
      
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l';
    
    skFORS <- nth witness (nth witness skFORSnt tidx) kpidx;
     
    sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx), cm);
    
    pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx) kpidx);
    
    sigFLSLXMSSMTTW <@ FL_SL_XMSS_MT_TW_ES_NPRF.sign((skWOTStd, ps, ad), pkFORS, idx);
    
    qs <- rcons qs m;

    return (mk, sigFORSTW, sigFLSLXMSSMTTW);
  }
}.

local module EUF_CMA_SPHINCSPLUSTWFS_PRFPRF = {
  proc main() : bool = {
    var pk : pkSPHINCSPLUSTW;
    var sk : mseed * skFORS list list * skWOTS list list list * pseed;
    var m : msg;
    var sig : sigSPHINCSPLUSTW;
    var is_valid : bool;
    var is_fresh : bool;
    
    (pk, sk) <@ SPHINCS_PLUS_TW_FS.keygen_prf();
    
    O_CMA_SPHINCSPLUSTWFS_PRF.init(sk);
    
    (m, sig) <@ A(O_CMA_SPHINCSPLUSTWFS_PRF).forge(pk);
    
    is_valid <@ SPHINCS_PLUS_TW_FS.verify(pk, m, sig);
    is_fresh <@ O_CMA_SPHINCSPLUSTWFS_PRF.fresh(m);
    
    return is_valid /\ is_fresh;
  }
}.


local equiv Eqv_EUF_CMA_SPHINCSPLUSTW_Orig_FSPRFPRF :
  EUF_CMA(SPHINCS_PLUS_TW, A, O_CMA_Default).main ~ EUF_CMA_SPHINCSPLUSTWFS_PRFPRF.main : 
    ={glob A} ==> ={res}.
proof.
proc.
seq 3 3 : (   ={pk, m, sig}
           /\ ={qs}(O_Base_Default, O_CMA_SPHINCSPLUSTWFS_PRF)); 2: by sim.
inline{1} 1; inline{2} 1.
inline{1} 5.
seq 4 8 : (   ={glob A, ad, ms, ss, ps}
           /\ ad{1} = adz
           /\ (forall (i j u v : int),
                 0 <= i && i < nr_trees 0 =>
                 0 <= j && j < l' =>
                 0 <= u && u < k =>
                 0 <= v && v < t =>
                 nth witness (nth witness (val (nth witness (nth witness skFORSnt{2} i) j)) u) v =
                 skg ss{1}
                   (ps{1}, set_thtbidx (set_kpidx (set_tidx (set_typeidx adz trhftype) i) j) 0 (u * t + v))) 
           /\ (forall (i j u v : int),
                0 <= i && i < d =>
                0 <= j && j < nr_trees i =>
                0 <= u && u < l' =>
                0 <= v && v < len =>
                nth witness (val (nth witness (nth witness (nth witness skWOTStd{2} i) j) u)) v =
                skg ss{1}
                  (ps{1}, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx adz i j) chtype) u) v) 0))).
+ while{2} (    ad{2} = adz
            /\ (forall (i j u v : int),
                  0 <= i && i < size skWOTStd{2} =>
                  0 <= j && j < nr_trees i =>
                  0 <= u && u < l' =>
                  0 <= v && v < len =>
                  nth witness (val (nth witness (nth witness (nth witness skWOTStd{2} i) j) u)) v =
                  skg ss{2}
                    (ps{2}, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx adz i j) chtype) u) v) 0)))
           (d - size skWOTStd{2}).
  - move=> _ z.
    wp => /=.
    while (    ad = adz
           /\ (forall (j u v : int),
                 0 <= j && j < size skWOTSnt =>
                 0 <= u && u < l' =>
                 0 <= v && v < len =>
                 nth witness (val (nth witness (nth witness skWOTSnt j) u)) v =
                 skg ss
                     (ps, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx adz (size skWOTStd) j) chtype) u) v) 0)))
          (nr_trees (size skWOTStd) - size skWOTSnt).
    * move=> z'.
      wp => /=.
      while (    ad = adz
             /\ (forall (u v : int),
                   0 <= u && u < size skWOTSlp =>
                   0 <= v && v < len =>
                   nth witness (val (nth witness skWOTSlp u)) v =
                   skg ss
                       (ps, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx adz (size skWOTStd) (size skWOTSnt)) chtype) u) v) 0)))
            (l' - size skWOTSlp).
      + move=> z''.
        wp => /=.
        while (    ad = adz
               /\ (forall (v : int),
                     0 <= v && v < size skWOTS =>
                     nth witness skWOTS v =
                     skg ss
                         (ps, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx adz (size skWOTStd) (size skWOTSnt)) chtype) (size skWOTSlp)) v) 0))
               /\ size skWOTS <= len)
              (len - size skWOTS).
        - move=> z'''.
          by wp; skip => />; smt(nth_rcons size_rcons).
        by wp; skip => />; smt(ge2_len nth_rcons size_rcons DBLL.insubdK DBLL.valP).
      by wp; skip => />; smt(nth_rcons size_rcons).
    by wp; skip => />; smt(nth_rcons size_rcons).
  wp => />; 1: smt().
  while{2} (    ad{2} = adz
            /\ (forall (i j u v : int),
                 0 <= i && i < size skFORSnt{2} =>
                 0 <= j && j < l' =>
                 0 <= u && u < k =>
                 0 <= v && v < t =>
                 nth witness (nth witness (val (nth witness (nth witness skFORSnt{2} i) j)) u) v =
                 skg ss{2}
                   (ps{2}, set_thtbidx (set_kpidx (set_tidx (set_typeidx adz trhftype) i) j) 0 (u * t + v))))
           (nr_trees 0 - size skFORSnt{2}).
  - move => _ z.
    wp => /=.
    while (   ad = adz
           /\ (forall (j u v : int),
                 0 <= j && j < size skFORSlp =>
                 0 <= u && u < k =>
                 0 <= v && v < t =>
                 nth witness (nth witness (val (nth witness skFORSlp j)) u) v =
                 skg ss
                   (ps, set_thtbidx (set_kpidx (set_tidx (set_typeidx adz trhftype) (size skFORSnt)) j) 0 (u * t + v))))
          (l' - size skFORSlp).
    * move=> z'.
      wp => /=.
      while (   ad = adz
             /\ (forall (u v : int),
                   0 <= u && u < size skFORS =>
                   0 <= v && v < t =>
                   nth witness (nth witness skFORS u) v =
                   skg ss
                     (ps, set_thtbidx (set_kpidx (set_tidx (set_typeidx adz trhftype) (size skFORSnt)) (size skFORSlp)) 0 (u * t + v)))
             /\ all (fun ls => size ls = t) skFORS
             /\ size skFORS <= k)
            (k - size skFORS).
      + move=> z''.
        wp => /=.
        while (   ad = adz
               /\ (forall (v : int),
                     0 <= v && v < size skFORSet =>
                     nth witness skFORSet v =
                     skg ss
                       (ps, set_thtbidx (set_kpidx (set_tidx (set_typeidx adz trhftype) (size skFORSnt)) (size skFORSlp)) 0 (size skFORS * t + v)))
               /\ size skFORSet <= t)
            (t - size skFORSet).
        - move=> z'''.
          by wp; skip => />; smt(nth_rcons size_rcons).
        by wp; skip => />; smt(ge2_t nth_rcons size_rcons cats1 all_cat).  
      by wp; skip => />; smt(nth_rcons size_rcons ge1_k DBLLKTL.valP DBLLKTL.insubdK).
    by wp; skip => />; smt(nth_rcons size_rcons).
  wp; do 3! rnd.
  by wp; skip => /> /#.
call (:   ={qs}(O_Base_Default, O_CMA_SPHINCSPLUSTWFS_PRF)
       /\ O_CMA_Default.sk{1}.`1 = O_CMA_SPHINCSPLUSTWFS_PRF.sk{2}.`1
       /\ O_CMA_Default.sk{1}.`3 = O_CMA_SPHINCSPLUSTWFS_PRF.sk{2}.`4 
       /\ (forall (i j u v : int),
             0 <= i && i < nr_trees 0 =>
             0 <= j && j < l' =>
             0 <= u && u < k =>
             0 <= v && v < t =>
             nth witness (nth witness (val (nth witness (nth witness O_CMA_SPHINCSPLUSTWFS_PRF.sk{2}.`2 i) j)) u) v =
             skg O_CMA_Default.sk{1}.`2
               (O_CMA_Default.sk{1}.`3, set_thtbidx (set_kpidx (set_tidx (set_typeidx adz trhftype) i) j) 0 (u * t + v)))
       /\ (forall (i j u v : int),
            0 <= i && i < d =>
            0 <= j && j < nr_trees i =>
            0 <= u && u < l' =>
            0 <= v && v < len =>
            nth witness (val (nth witness (nth witness (nth witness O_CMA_SPHINCSPLUSTWFS_PRF.sk{2}.`3 i) j) u)) v =
            skg O_CMA_Default.sk{1}.`2
              (O_CMA_Default.sk{1}.`3, set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx adz i j) chtype) u) v) 0))).
+ proc.
  inline{1} 1.
  wp.
  conseq (: _ ==> ={mk, sigFORSTW, sigFLSLXMSSMTTW}) => //.
  inline{1} 9; inline{2} 9.
  wp => /=.
  while (   ={sapl, root, tidx0, kpidx0, ps0, ad0}
         /\ O_CMA_Default.sk{1} = (ms, ss0, ps0){1}
         /\ O_CMA_SPHINCSPLUSTWFS_PRF.sk{2} = (ms, skFORSnt, skWOTStd0, ps0){2}
         /\ ad0{1} = adz
         /\ 0 <= tidx0{1} < nr_trees (size sapl{1} - 1)
         /\ 0 <= kpidx0{1} < l'
         /\ size sapl{1} <= d
         /\ #pre).
  - inline{1} 3; inline{2} 5.
    wp => />.
    while (   ={leaves0, ad1, ps1}
           /\ ss1{1} = ss0{1}
           /\ ad1{1} = set_ltidx ad0{1} (size sapl{1}) tidx0{1}
           /\ ps1{1} = ps0{1}
           /\ skWOTSl{2} = nth witness (nth witness skWOTStd0{2} (size sapl{2})) tidx0{2}
           /\ 0 <= tidx0{2} < nr_trees (size sapl{2})
           /\ size leaves0{1} <= l'
           /\ #pre).
    * inline{1} 2; inline{1} 1; inline{2} 2.
      wp => />.
      while (   ={ps2, ad2, pkWOTS0}
             /\ skWOTS1{1} = skWOTS2{2}
             /\ size pkWOTS0{1} <= len).
      - by wp; skip => />; smt(size_rcons).
      wp => />; 1: smt().
      while{1} (   (forall (i : int), 0 <= i < size skWOTS2{1} =>
                     nth witness skWOTS2{1} i 
                     =
                     skg ss2{1} (ps3{1}, set_hidx (set_chidx ad3{1} i) 0))
                /\ size skWOTS2{1} <= len)
           (len - size skWOTS2{1}).
      - move=> _ z.
        by wp; skip => />; smt(nth_rcons size_rcons).
      wp; skip => /> &1 &2 ge0_tidx ltnt_tidx _ _ ltnt1_tidx ge0_kpidx ltlp_kpidx _ nthskf nthskw ltd_szsapl ltlp_szlfs.
      split => [| skw]; 1: smt(ge2_len).
      split => [/# | /lezNgt gelen_szskw nthskwp lelen_szskw].
      split; 2: smt(size_rcons).
      split; 2: smt(ge2_len).
      rewrite &(DBLL.val_inj) &(eq_from_nth witness) ?valP //= => i rng_i.
      by rewrite insubdK 1:/# nthskwp 1:/# nthskw 1:size_ge0.
    inline{1} 2; inline{2} 4.
    wp => />; 1: smt().
    while (   ={ps2, ad2, em} 
           /\ sig2{1} = sig0{2}
           /\ skWOTS1{1} = skWOTS2{2}
           /\ size sig2{1} <= len).
    * by wp; skip => />; smt(size_rcons).
    inline{1} 8.
    wp => />; 1: smt().
    while{1} (   (forall (i : int), 0 <= i < size skWOTS2{1} =>
                   nth witness skWOTS2{1} i 
                   =
                   skg ss3{1} (ps3{1}, set_hidx (set_chidx ad3{1} i) 0))
              /\ size skWOTS2{1} <= len)
         (len - size skWOTS2{1}).
    * move=> _ z. 
      by wp; skip => />; smt(nth_rcons size_rcons).
    wp; skip => /> &1 &2 ge0_tidx ltnt1_tidx ge0_kpidx ltlp_kpidx _ nthskf nthskw ltd_szsapl.
    split => [| skw]; 1: smt(ge2_len).
    split => [/# | /lezNgt gelen_szskw nthskwp lelen_szskw].
    split => [| sigw /lezNgt gelen_szsigw _ lelen_szsigw].
    * split; 2: smt(ge2_len).
      rewrite &(DBLL.val_inj) &(eq_from_nth witness) ?valP //= => i rng_i.
      rewrite insubdK 1:/# nthskwp 1:/# nthskw 1:size_ge0 //=.
      + rewrite divz_ge0 2:ge0_tidx 2:ltz_divLR /=; 1,2: smt(ge1_lp).
        by rewrite /nr_trees /l' -exprD_nneg 1:mulr_ge0; smt(ge0_hp ge1_d).
      by rewrite modz_ge0 2:ltz_pmod; smt(ge1_lp).
    split => [| lfs]; 2: smt(size_rcons).
    rewrite modz_ge0 2:ltz_pmod /=; 1,2: smt(ge1_lp).
    rewrite divz_ge0 2:ge0_tidx 2:(: 0 <= l') /=; 1,2: smt(ge1_lp).
    rewrite ltz_divLR 2:(: nr_trees (size sapl{2}) * l' =  nr_trees (size sapl{2} - 1)); 1: smt(ge1_lp).
    - by rewrite /nr_trees /l' -exprD_nneg 1:mulr_ge0; smt(ge0_hp ge1_d).
    by rewrite ltnt1_tidx /= (IntOrder.ler_lt_trans tidx0{2}) //= leq_div //; smt(ge1_lp).
  inline{1} 8; inline{2} 8.
  wp => /=.
  while (   ={roots, ad, ps1, ad1, tidx, kpidx}
         /\ O_CMA_Default.sk{1} = (ms, ss1, ps1){1}
         /\ O_CMA_SPHINCSPLUSTWFS_PRF.sk{2} = (ms, skFORSnt, skWOTStd, ps1){2}
         /\ ad1{1} = set_kpidx (set_tidx (set_typeidx adz trhftype) tidx{1}) kpidx{1}
         /\ skFORS0{2} = nth witness (nth witness skFORSnt{2} tidx{2}) kpidx{2}
         /\ 0 <= tidx{2} < nr_trees 0
         /\ 0 <= kpidx{2} < l'
         /\ size roots{1} <= k
         /\ #pre).
  - inline{1} 1; inline{2} 1.
    wp => />.
    while (   ={leaves1, ps2, ad2, idxt}
           /\ ss2{1} = ss1{1}
           /\ ps2{1} = ps1{1}
           /\ size leaves1{1} <= t
           /\ ad2{2} = ad1{2}
           /\ skFORS1{2} = skFORS0{2}
           /\ 0 <= idxt{1} < k
           /\ #pre).
    * wp; skip => /> &1 &2 _ ge0_idxt ltk_idxt ge0_tidx ltnt_tidx ge0_kpidx ltlp_kpidx _ nthskf nthskw ltk_szrs ltt_szlfs.
      rewrite -!andbA; split; 2: by smt(size_rcons).
      by do 3! congr; rewrite nthskf.    
    by wp; skip => />; smt(ge2_t size_rcons size_ge0).
  inline{1} 5; inline{1} 11; inline{2} 7.
  wp => /=. 
  while (   tidx{2} = (val idx{2}) %/ l'
         /\ kpidx{2} = (val idx{2}) %% l'
         /\ O_CMA_Default.sk{1} = (ms, ss2, ps2){1}
         /\ O_CMA_SPHINCSPLUSTWFS_PRF.sk{2} = (ms, skFORSnt, skWOTStd, ps2){2}
         /\ sig3{1} = sig0{2}
         /\ m3{1} = m1{2}
         /\ idx1{1} = idx{2}
         /\ ad3{1} = ad2{2}
         /\ ps3{1} = ps2{2}
         /\ ss3{1} = ss2{1}
         /\ skFORS1{2} = nth witness (nth witness skFORSnt{2} tidx{2}) kpidx{2}
         /\ ad2{2} = set_kpidx (set_tidx (set_typeidx adz trhftype) tidx{2}) kpidx{2}
         /\ 0 <= tidx{2} < nr_trees 0
         /\ 0 <= kpidx{2} < l'
         /\ size sig3{1} <= k
         /\ #pre).
  - inline{1} 4; inline{2} 4.
    wp => />.
    while (  ={leaves2, idxt}
           /\ idxt{1} = size sig3{1}
           /\ skFORS2{2} = skFORS1{2}
           /\ ss4{1} = ss3{1}
           /\ ps4{1} = ps3{1}
           /\ ps4{1} = ps3{2}
           /\ ad4{1} = ad3{1}
           /\ ad4{1} = ad3{2}
           /\ size leaves2{1} <= t
           /\ #pre).
    * by wp; skip => />; smt(size_ge0 size_rcons).
    wp; skip => /> ? ? ? ? ? ? ? nthskf *.
    split=> [| lfs /lezNgt get_lfs _ let_lfs]; 1: smt(ge2_t).
    rewrite -!andbA; split; 2: smt(size_rcons).
    do 2! congr; rewrite nthskf // bs2int_ge0 /=.
    pose ls := rev _; rewrite (IntOrder.ltr_le_trans (2 ^ size ls)) 1:bs2int_le2Xs //.
    apply IntOrder.ler_weexpn2l => //. 
    rewrite size_ge0 /= /ls size_rev size_take 2:size_drop; 1,2: smt(ge1_a size_ge0). 
    by rewrite ?valP /#. 
  wp; skip => /> &1 &2 ? ? /= nthskf nthskw *.
  split; 2: smt(ge1_k ge1_lp ge1_d Index.valP).
  rewrite !andbA -4!andbA; split => [/#| ].
  rewrite divz_ge0 2:modz_ge0 3:ltz_pmod 4:ltz_divLR /=; 1..4: smt(ge1_lp).
  by rewrite /nr_trees /= /l' -exprD_nneg; smt(ge0_hp ge1_d ge1_k Index.valP).
inline{1} 10; inline{2} 7.
inline{1} 4; inline{2} 2.
sp 6 4; wp => />.
while (   ={leaves0}
       /\ size leaves0{1} <= l'
       /\ #pre).
+ wp; call (: true); 1: by sim.
  inline{1} 1.
  wp => />; 1: smt().
  while{1} (   (forall (i : int), 0 <= i < size skWOTS0{1} =>
                 nth witness skWOTS0{1} i 
                 =
                 skg ss2{1} (ps2{1}, set_hidx (set_chidx ad2{1} i) 0))
            /\ size skWOTS0{1} <= len)
           (len - size skWOTS0{1}).
  + move=> _ z.
    by wp; skip => />; smt(nth_rcons size_rcons).
  wp; skip => />. progress. smt(ge2_len). smt(ge2_len). smt(ge2_len). 
  rewrite &(DBLL.val_inj) &(eq_from_nth witness) ?valP // => i rng_i. 
  rewrite insubdK 1:/#.
  rewrite H4 1:/#. rewrite H1 //; smt(ge1_d ge1_lp ge2_len IntOrder.expr_gt0).
  smt(ge1_d ge1_lp ge2_len IntOrder.expr_gt0 size_rcons).
by wp; skip => />; smt(ge1_lp).
qed.

local module EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF = {
  proc main() : bool = {
    var pk : pkSPHINCSPLUSTW;
    var sk : mseed * skFORS list list * skWOTS list list list * pseed;
    var m : msg;
    var sig : sigSPHINCSPLUSTW;
    var is_valid : bool;
    var is_fresh : bool;
    
    (pk, sk) <@ SPHINCS_PLUS_TW_FS.keygen_nprf();
    
    O_CMA_SPHINCSPLUSTWFS_PRF.init(sk);
    
    (m, sig) <@ A(O_CMA_SPHINCSPLUSTWFS_PRF).forge(pk);
    
    is_valid <@ SPHINCS_PLUS_TW_FS.verify(pk, m, sig);
    is_fresh <@ O_CMA_SPHINCSPLUSTWFS_PRF.fresh(m);
    
    return is_valid /\ is_fresh;
  }
}.


local lemma EqAdv_EUF_CMA_SPHINCSPLUSTWFS_PRFPRF_NPRFPRF_SKGPRF &m :
  `|  Pr[EUF_CMA_SPHINCSPLUSTWFS_PRFPRF.main() @ &m : res]
    - Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF.main() @ &m : res] |
  =
  `|  Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(false) @ &m : res]
    - Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(true) @ &m : res] |.
proof.
do 2! congr; 2: congr.
+ byequiv => //.
  by admit.
byequiv => //.
by admit.
qed.


local module EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF = {
  proc main() : bool = {
    var pk : pkSPHINCSPLUSTW;
    var sk : mseed * skFORS list list * skWOTS list list list * pseed;
    var m : msg;
    var sig : sigSPHINCSPLUSTW;
    var is_valid : bool;
    var is_fresh : bool;
    
    (pk, sk) <@ SPHINCS_PLUS_TW_FS.keygen_nprf();
    
    O_CMA_SPHINCSPLUSTWFS_NPRF.init(sk);
    
    (m, sig) <@ A(O_CMA_SPHINCSPLUSTWFS_NPRF).forge(pk);
    
    is_valid <@ SPHINCS_PLUS_TW_FS.verify(pk, m, sig);
    is_fresh <@ O_CMA_SPHINCSPLUSTWFS_NPRF.fresh(m);
    
    return is_valid /\ is_fresh;
  }
}.

local lemma EqAdv_EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF_NPRFNPRF_MKGPRF &m :
  `|  Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF.main() @ &m : res]
    - Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF.main() @ &m : res] |
  =
  `|  Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(false) @ &m : res]
    - Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(true) @ &m : res] |.
proof.
do 2! congr; 2: congr.
+ byequiv => //.
  by admit.
byequiv => //.
by admit.
qed.



local module EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V = {
  var valid_MFORSTWESNPRF : bool
  
  proc main() : bool = {
    var pk : pkSPHINCSPLUSTW;
    var sk : mseed * skFORS list list * skWOTS list list list * pseed;
    var m' : msg;
    var sig' : sigSPHINCSPLUSTW;
    var is_valid : bool;
    var is_fresh : bool;
    var ad : adrs;
    var skFORSnt : skFORS list list;
    var ps : pseed;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var sigFLSLXMSSMTTW' : sigFLSLXMSSMTTW;
    var cm' : msgFORSTW;
    var idx' : index;
    var tidx', kpidx' : int;
    var pkFORS, pkFORS' : pkFORS;
    var skFORS : skFORS;
    
    (pk, sk) <@ SPHINCS_PLUS_TW_FS.keygen_nprf();
    
    O_CMA_SPHINCSPLUSTWFS_NPRF.init(sk);
    
    (m', sig') <@ A(O_CMA_SPHINCSPLUSTWFS_NPRF).forge(pk);
    
    is_valid <@ SPHINCS_PLUS_TW_FS.verify(pk, m', sig');
    is_fresh <@ O_CMA_SPHINCSPLUSTWFS_NPRF.fresh(m');
    
    
    (* is_valid_MFORSTWESNPRF <@ M_FORS_TW_ES_NPRF.verify(); *)
    ad <- adz; 
    skFORSnt <- sk.`2;
    ps <- sk.`4;
    
    (mk', sigFORSTW', sigFLSLXMSSMTTW') <- sig';
    
    (cm', idx') <- mco mk' m';
    (tidx', kpidx') <- edivz (val idx') l';
    
    skFORS <- nth witness (nth witness skFORSnt tidx') kpidx';
    pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx') kpidx');
    
    pkFORS' <@ FL_FORS_TW_ES.pkFORS_from_sigFORSTW(sigFORSTW', cm', ps, set_kpidx (set_tidx (set_typeidx ad trhftype) tidx') kpidx');
    
    valid_MFORSTWESNPRF <- pkFORS' = pkFORS;
    
    return is_valid /\ is_fresh;
  }
}.

local equiv Eqv_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V :
  EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF.main ~ EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.main : ={glob A} ==> ={res}.
proof. admit. qed.


local lemma EqPr_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_VT_MFORSTWESNPRF &m :
  Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.main() @ &m : res /\ EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.valid_MFORSTWESNPRF]
  =
  Pr[EUF_CMA_MFORSTWESNPRF(R_MFORSTWESNPRFEUFCMA_EUFCMA(A), O_CMA_MFORSTWESNPRF).main() @ &m : res].
proof.
byequiv=> //.
admit.
qed.

local lemma EqPr_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_VF_FLSLXMSSMTTWESNPRF &m :
  Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.main() @ &m : res /\ ! EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.valid_MFORSTWESNPRF]
  =
  Pr[EUF_NAGCMA_FLSLXMSSMTTWESNPRF(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A), FSSLXMTWES.TRHC.O_THFC_Default).main() @ &m : res].
proof.
byequiv=> //.
admit.
qed. 

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
  `|  Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(false) @ &m : res]
    - Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(true) @ &m : res] |
  +
  `|  Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(false) @ &m : res]
    - Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(true) @ &m : res] |
  +  
  Pr[EUF_CMA_MFORSTWESNPRF(R_MFORSTWESNPRFEUFCMA_EUFCMA(A), O_CMA_MFORSTWESNPRF).main() @ &m : res]
  +
  Pr[EUF_NAGCMA_FLSLXMSSMTTWESNPRF(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A), FSSLXMTWES.TRHC.O_THFC_Default).main() @ &m : res].
proof.
have ->:
  Pr[EUF_CMA(SPHINCS_PLUS_TW, A, O_CMA_Default).main() @ &m : res]
  =
  Pr[EUF_CMA_SPHINCSPLUSTWFS_PRFPRF.main() @ &m : res].
+ by byequiv Eqv_EUF_CMA_SPHINCSPLUSTW_Orig_FSPRFPRF.
rewrite -(RealOrder.ger0_norm) 1:Pr[mu_ge0] // -RField.addr0.
rewrite -(RField.subrr Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF.main() @ &m : res]).
rewrite RField.addrCA RField.addrC.
apply (RealOrder.ler_trans (`|Pr[EUF_CMA_SPHINCSPLUSTWFS_PRFPRF.main() @ &m : res] -
                              Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF.main() @ &m : res]| +
                            `|Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF.main() @ &m : res]|)).
+ by apply RealOrder.ler_norm_add.
rewrite EqAdv_EUF_CMA_SPHINCSPLUSTWFS_PRFPRF_NPRFPRF_SKGPRF -!RField.addrA RealOrder.ler_add //.
rewrite -RField.addr0 -(RField.subrr Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF.main() @ &m : res]).
rewrite RField.addrCA RField.addrC.
apply (RealOrder.ler_trans (`|Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF.main() @ &m : res] -
                              Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF.main() @ &m : res]| +
                            `|Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF.main() @ &m : res]|)).
+ by apply RealOrder.ler_norm_add.
rewrite EqAdv_EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF_NPRFNPRF_MKGPRF RealOrder.ler_add //.
rewrite RealOrder.ger0_norm 1:Pr[mu_ge0] //.
have ->:
  Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF.main() @ &m : res]
  =
  Pr[EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.main() @ &m : res].
+ by byequiv Eqv_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.
rewrite Pr[mu_split EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V.valid_MFORSTWESNPRF].
rewrite EqPr_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_VT_MFORSTWESNPRF.
by rewrite EqPr_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_VF_FLSLXMSSMTTWESNPRF.
qed.


lemma EUFCMA_SPHINCS_PLUS_TW &m :
  Pr[EUF_CMA(SPHINCS_PLUS_TW, A, O_CMA_Default).main() @ &m : res]
  <= 
  `|  Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(false) @ &m : res]
    - Pr[SKG_PRF.PRF(R_SKGPRF_EUFCMA(A), SKG_PRF.O_PRF_Default).main(true) @ &m : res] |
  +
  `|  Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(false) @ &m : res]
    - Pr[MKG_PRF.PRF(R_MKGPRF_EUFCMA(A), MKG_PRF.O_PRF_Default).main(true) @ &m : res] |
  +
  Pr[MCO_ITSR.ITSR(R_ITSR_EUFCMA(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), MCO_ITSR.O_ITSR_Default).main() @ &m : res]
  +
  maxr 0%r 
       (Pr[FP_DSPR.SM_DT_DSPR(R_DSPR_OpenPRE(R_FPOpenPRE_FOpenPRE(R_MFORSTWESNPRFEUFCMA_EUFCMA(A))), FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res]
        -
        Pr[FP_DSPR.SM_DT_SPprob(R_DSPR_OpenPRE(R_FPOpenPRE_FOpenPRE(R_MFORSTWESNPRFEUFCMA_EUFCMA(A))), FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res])
  +
  3%r * Pr[FP_TCR.SM_DT_TCR(R_TCR_OpenPRE(R_FPOpenPRE_FOpenPRE(R_MFORSTWESNPRFEUFCMA_EUFCMA(A))), FP_TCR.O_SMDTTCR_Default).main() @ &m : res]
  + 
  Pr[FTWES.TRHC_TCR.SM_DT_TCR_C(R_TRHSMDTTCRC_EUFCMA(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), FTWES.TRHC_TCR.O_SMDTTCR_Default, FTWES.TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_TRCOSMDTTCRC_EUFCMA(R_MFORSTWESNPRFEUFCMA_EUFCMA(A)), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res]  
  +
  (w - 2)%r
    * `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res]
        - Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]| 
  + 
  Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A))), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res] 
  + 
  Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A))), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFNAGCMA(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A)), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
  +
  Pr[FSSLXMTWES.TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFNAGCMA(R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A)), FSSLXMTWES.TRHC_TCR.O_SMDTTCR_Default, FSSLXMTWES.TRHC.O_THFC_Default).main() @ &m : res].
proof.
move: (EUFNAGCMA_FLSLXMSSMTTWESNPRF (R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA(A)) _ _ &m)
      (EUFCMA_MFORSTWESNPRF (R_MFORSTWESNPRFEUFCMA_EUFCMA(A)) &m)
      (EUFCMA_SPHINCS_PLUS_TW_FX &m); last smt(). 
+ move=> OC OCll.
  proc.
  while (true) (nr_trees 0 - size R_FLSLXMSSMTTWESNPRFEUFNAGCMA_EUFCMA.skFORSnt).
  - move=> z.
    wp.
    while (true) (l' - size skFORSlp).
    * move=> z''.
      wp.
      call OCll.
      while (true) (k - size skFORS).
      + move=> z'''.
        wp.
        while (true) (a - size nodes).
        - move=> z''''.
          wp.
          while (true) (nr_nodesf (size nodes + 1) - size nodescl).
          * move=> z'''''.
            wp.
            call OCll.
            by wp; skip => />; smt(size_rcons).
          by wp; skip => />; smt(size_rcons).
        wp.
        while (true) (t - size skFORSet).
        + move=> z''''.
          wp.
          call OCll.
          rnd.
          by wp; skip => />; smt(size_rcons ddgstblock_ll).
        by wp; skip => />; smt(size_rcons). 
      by wp; skip => />; smt(size_rcons).
    by wp; skip => />; smt(size_rcons).
  by wp; skip => />; smt(size_rcons).
move=> OC.
proc; inline *.
wp.
while (true) (k - size roots).
+ move=> z. 
  by wp; skip => />; smt(size_rcons).
wp.
call (: true). 
+ by move=> O Oll; apply (A_forge_ll O).
+ proc; inline *.
  wp.
  while (true) (k - size sig).
  + move=> z.
    wp => /=.
    while (true) (t - size leaves0).
    - move=> z'.
      by wp; skip => />; smt(size_rcons).
    by wp; skip => />; smt(size_rcons).
  wp; rnd; skip => />; smt(dmkey_ll).
by wp; skip => /> /#.
qed.
 
end section Proof_SPHINCS_PLUS_TW_EUFCMA.
