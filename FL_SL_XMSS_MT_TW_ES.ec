(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList StdOrder StdBigop IntDiv RealExp FinType BitEncoding.
(*---*) import BS2Int BitChunking.
(*---*) import IntOrder Bigint BIA.

(* -- Local -- *)
require import BinaryTrees MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.
require (*--*) DigitalSignatures.
require (*--*) WOTS_TW_ES.


(* - Parameters - *)
(* -- General -- *)
(* Length of addresses used in tweakable hash functions (including unspecified global/context part) *)
const adrs_len : { int | 6 <= adrs_len} as ge6_adrslen.

(* 
  Length (in bytes) of messages as well as the length of elements of 
  private keys, public keys, and signatures
*)
const n : { int | 1 <= n } as ge1_n.


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


(* -- FL-SL-XMSS(-MT)-TW -- *)
(* Height of a single inner (XMSS) tree  *)
const h' : { int | 0 <= h' } as ge0_hp. 

(* Number of WOTS-TW instances of a single inner (XMSS) tree (i.e., number of leaves) *)
const l' = 2 ^ h'.

(* Number of layers in the hypertree (i.e., height of tree of XMSS trees) *)
const d : { int | 1 <= d } as ge1_d.

(* 
  Height of "flattened" hypertree (i.e., total height of concatenation of inner trees) 
*)
const h : int = h' * d.

(* 
  Number of leaves of "flattened" hypertree
  (i.e., total number of leaves of all inner trees on bottom layer)
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

(* Address type for tree hashing (used in tweakable hash function calls of inner hash trees) *)
const trhtype : int.


(* -- Properties of parameters -- *)
(* The different address types are distinct *)
axiom dist_adrstypes : chtype <> pkcotype /\ chtype <> trhtype /\ pkcotype <> trhtype.

(* l' is greater than or equal to 1 *)
lemma ge1_lp : 1 <= l'.
proof. by rewrite /l' -add0r -ltzE expr_gt0. qed.

(* h is greater than or equal to 0 *)
lemma ge0_h : 0 <= h.
proof. by rewrite /h mulr_ge0 1:ge0_hp; smt(ge1_d). qed.

(* l is greater than or equal to 1 *)
lemma ge2_l : 1 <= l.
proof.  by rewrite /l -add0r -ltzE expr_gt0. qed.



(* - Types (1/3) - *)
(* -- General -- *)
(* Index *)
clone import Subtype as Index with
  type T <= int,
    op P i <= 0 <= i < l
    
  proof *.
  realize inhabited by exists 0; smt(ge2_l).

type index = Index.sT.

(* Secret seeds *)
type sseed.

(* Public seeds *)
type pseed.

(* Digests, i.e., outputs of (tweakable) hash functions. *)
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



(* - Operators (1/3) - *)
(* -- Auxiliary -- *)
(* Number of nodes in a (XMSS) binary tree (of total height h') at a particular height h'' *)
op nr_nodes (h'' : int) = 2 ^ (h' - h'').

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
op nr_nodes_ht (d' h'' : int) = nr_trees d' * nr_nodes h''.

(* Alternative expression for nr_nodes_ht using total height of hypertree (h) *)
lemma nrnodesht_h (d' h'' : int) :
     d' < d
  => h'' <= h'
  => nr_nodes_ht d' h'' = 2 ^ (h - d' * h' - h'').
proof.
move=> gtdp_d dehpp_hp.
rewrite /nr_nodes_ht /nr_trees /nr_nodes /h -exprD_nneg; 2: smt().
+ by rewrite mulr_ge0 1:ge0_hp /#.
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
rewrite /nr_trees nrnodesht_h //= /h 1:ge0_hp. 
by congr; ring.
qed.

(* The number of inner trees in the bottom d' layers is greater than or equal to 1. *)
lemma ge1_bigitrees (d' : int) :
     0 < d' <= d
  => 1 <= bigi predT nr_trees 0 d'.
proof.
move=> [gt0_dp led_dp]; rewrite (: d' = d' - 1 + 1) 1:// big_int_recr 1:/#.
rewrite -{1}add0r ler_add; last first.
+ by rewrite /nr_trees {1}(: 1 = 0 + 1) 1:// -ltzE expr_gt0.
rewrite sumz_ge0 filter_predT allP => x /mapP [x' [/mem_range [ge0_x _] ->]].
by rewrite /nr_trees expr_ge0.
qed.


(* -- Validity checks for (indices corresponding to) XMSS-MT-TW addresses -- *)
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
  typeidx = chtype \/ typeidx = pkcotype \/ typeidx = trhtype.
*)

(* Key pair index validity check (note: regards inner tree) *)
op valid_kpidx (kpidx : int) : bool =
  0 <= kpidx < l'.

(* Tree height index validity check (note: regards inner tree) *)
op valid_thidx (thidx : int) : bool = 
  0 <= thidx <= h'.
  
(* Tree breadth index validity check (note: regards inner tree) *)
op valid_tbidx (thidx tbidx : int) : bool = 
  0 <= tbidx < nr_nodes thidx.

(* Chain index validity check *)
op valid_chidx (chidx : int) : bool =
  0 <= chidx < len.

(* Hash index validity check *)
op valid_hidx (hidx : int) : bool = 
  0 <= hidx < w - 1.

(* Chaining address indices validity check (local part) *) 
op valid_xidxvalslpch (adidxs : int list) : bool =
     valid_hidx (nth witness adidxs 0) 
  /\ valid_chidx (nth witness adidxs 1)
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = chtype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Public-key compression address indices validity check (local part) *)  
op valid_xidxvalslppkco (adidxs : int list) : bool =
     nth witness adidxs 0 = 0 
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = pkcotype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Tree hashing address indices validity check (local part)*)  
op valid_xidxvalslptrh (adidxs : int list) : bool =
     valid_tbidx (nth witness adidxs 1) (nth witness adidxs 0)
  /\ valid_thidx (nth witness adidxs 1)
  /\ nth witness adidxs 2 = 0
  /\ nth witness adidxs 3 = trhtype
  /\ valid_tidx (nth witness adidxs 5) (nth witness adidxs 4)
  /\ valid_lidx (nth witness adidxs 5).

(* Local address indices validity check *)
op valid_xidxvalslp (adidxs : int list) : bool =
  valid_xidxvalslpch adidxs \/ valid_xidxvalslppkco adidxs \/ valid_xidxvalslptrh adidxs.

(* 
  Validity check for the values of the list of integers corresonding to addresses used in
  the encompassing structure.
  As the encompassing structure is abstract, many of the valid 
  addresses may be unknown (as their validity is defined by this unknown structure).
  For this reason, the validity check is left abstract.
*)
op valid_idxvals : int list -> bool.

(* 
  Overall validity check for the list of integers corresponding to addresses used in the
  encompassing structure. This checks for the correct length and valid values.
*)
op valid_adrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_idxvals adidxs.

(* 
  Validity check for the values of the global/context part of the list of integers 
  corresponding to FL-SL-XMSS-MT-TW addresses used in the
  encompassing structure. This global/context part is the part that is to be defined
  by this unknown structure and, therefore, this validity check is left abstract.
*)
op valid_xidxvalsgp : int list -> bool.

(* 
  Validity check for the values of the list of integers corresponding to 
  FL-SL-XMSS-MT-TW addresses used in the encompassing structure.
  This includes the local part that we defined, and the abstract global/context part
  defined by the unknown structure.  
*) 
op valid_xidxvals (adidxs : int list) =
  valid_xidxvalsgp (drop 6 adidxs) /\ valid_xidxvalslp (take 6 adidxs).

(*
  Overall validity check for the list of integers corresponding to 
  FL-SL-XMSS-MT-TW addresses used in the encompassing structure.
  This checks for the correct length and valid values.
*)
op valid_xadrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_xidxvals adidxs.

(*
  The list of integers that correspond to FL-SL-XMSS-MT-TW addresses are a subset of
  the list of integers that correspond to valid addresses. (In other words,
  the FL-SL-XMSS-MT-TW addresses are a subset of the complete set of valid addresses
  used in the encompassing structure.)
*)
axiom valid_xidxvals_idxvals : 
  valid_xidxvals <= valid_idxvals.

(*
  The FL-SL-XMSS-MT-TW addresses are a subset of the complete set of valid addresses
  used in the encompassing structure. 
*)  
lemma valid_xadrsidxs_adrsidxs :
  valid_xadrsidxs <= valid_adrsidxs.
proof. 
rewrite /(<=) /valid_xadrsidxs /valid_adrsidxs => adidxs [-> /=].
by apply valid_xidxvals_idxvals.
qed.



(* - Distributions (1/2) - *)
(* Proper distribution over public seeds *)
op [lossless] dpseed : pseed distr.

(* Proper distribution over (single) digestblocks  *)
op [lossless] ddgstblock : dgstblock distr.



(* - Types (2/3) - *)
(* 
  Addresses used in encompassing structure (complete set, including FL-SL-XMSS-MT-TW addresses)
*)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
    proof ge1_l.
    realize ge1_l by smt(ge6_adrslen).

import Adrs.

type adrs = HA.adrs.


(* - Operators (2/3) -- *)
(* -- Tweakable hash functions -- *)
(* 
  Tweakable hash function collection that contains all tweakable hash functions
  used in FORS-TW, FL-SL-XMSS-MT-TW, SPHINCS+ 
*)
op thfc : int -> pseed -> adrs -> dgst -> dgstblock.

(* 
  Tweakable hash function used for the compression of public (WOTS-TW) keys to leaves
  of inner trees
*)
op pkco : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * len).
  
(* Import and instantiate tweakable hash function definitions for pkco *)
clone TweakableHashFunctions as PKCO with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,

  op f <- pkco,
  
  op dpp <- dpseed
  
  proof *. 
  realize dpp_ll by exact: dpseed_ll.

clone PKCO.Collection as PKCOC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
  
  proof *.
  realize in_collection by exists (8 * n * len).

clone PKCOC.SMDTTCRC as PKCOC_TCR with
  op t_smdttcr <- bigi predT (fun (d' : int) => nr_nodes_ht d' 0) 0 d
  
  proof *.
  realize ge0_tsmdttcr.
  rewrite (: d = d - 1 + 1) // big_int_recr /= 2:ler_paddl; 1: smt(ge1_d).
  + rewrite sumr_ge0_seq => d' /mem_range [ge0_dp ltd_dp] _ /=. 
    by rewrite nrnodesht_h 3:expr_ge0 //; 1,2: smt(ge0_h).     
  by rewrite nrnodesht_h 3:expr_ge0; 1,2: smt(ge0_hp ge1_d).
  qed.
  
(* 
  Tweakable hash function used for the hashing operations of the binary hash tree of XMSS.
*)
op trh : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * 2).

clone TweakableHashFunctions as TRH with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,

  op f <- trh,
  
  op dpp <- dpseed
  
  proof *. 
  realize dpp_ll by exact: dpseed_ll.

clone import TRH.Collection as TRHC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
  
  proof *.
  realize in_collection by exists (8 * n * 2).

clone TRHC.SMDTTCRC as TRHC_TCR with
  op t_smdttcr <- l - 1
  
  proof *.
  realize ge0_tsmdttcr by smt(ge2_l).  

  
(* -- Validity/type checks for (indices corresponding to) XMSS-TW addresses -- *)
op valid_xidxchvals (adidxs : int list) : bool =
  valid_xidxvalsgp (drop 6 adidxs) /\ valid_xidxvalslpch (take 6 adidxs).

op valid_xidxpkcovals (adidxs : int list) : bool =
  valid_xidxvalsgp (drop 6 adidxs) /\ valid_xidxvalslppkco (take 6 adidxs).
  
op valid_xidxtrhvals (adidxs : int list) : bool =
  valid_xidxvalsgp (drop 6 adidxs) /\ valid_xidxvalslptrh (take 6 adidxs).
  
op valid_xadrschidxs (adidxs : int list) : bool =
  size adidxs = adrs_len /\ valid_xidxchvals adidxs.

op valid_xadrspkcoidxs (adidxs : int list) : bool =
  size adidxs = adrs_len /\ valid_xidxpkcovals adidxs.
  
op valid_xadrstrhidxs (adidxs : int list) : bool =
  size adidxs = adrs_len /\ valid_xidxtrhvals adidxs.

lemma valid_xadrsidxs_xadrschpkcotrhidxs (adidxs : int list) :
  valid_xadrsidxs adidxs
  <=>
  valid_xadrschidxs adidxs \/ valid_xadrspkcoidxs adidxs \/ valid_xadrstrhidxs adidxs.  
proof. smt(). qed.

op valid_xadrsch (ad : adrs) : bool =
  valid_xadrschidxs (val ad).
  
op valid_xadrspkco (ad : adrs) : bool =
  valid_xadrspkcoidxs (val ad).
  
op valid_xadrstrh (ad : adrs) : bool =
  valid_xadrstrhidxs (val ad).

op valid_xadrs (ad : adrs) : bool =
  valid_xadrsidxs (val ad).

lemma valid_xadrs_xadrschpkcotrh (ad : adrs) :
  valid_xadrs ad
  <=>
  valid_xadrsch ad \/ valid_xadrspkco ad \/ valid_xadrstrh ad.  
proof. smt(). qed.


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


(* -- Getters -- *)
op get_typeidx (ad : adrs) : int =
  get_idx ad 3.
  

(* - Clones and imports - *)
(* WOTS-TW-ES *)
clone import WOTS_TW_ES as WTWES with 
    op adrs_len <- adrs_len,
    op n <- n,
    op log2_w <- log2_w,
    op w <- w,
    op len1 <- len1,
    op len2 <- len2,
    op len <- len,
    op c <- bigi predT (fun (d' : int) => nr_nodes_ht d' 0) 0 d,

  type sseed <- sseed,
  type pseed <- pseed,
  type dgst <- dgst,
  
    op valid_chidx <- valid_chidx,
    op valid_hidx <- valid_hidx,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs,
    op valid_widxvalsgp adidxswgp <=    valid_kpidx (nth witness adidxswgp 0) 
                                     /\ nth witness adidxswgp 1 = chtype
                                     /\ valid_tidx (nth witness adidxswgp 3) (nth witness adidxswgp 2) 
                                     /\ valid_lidx (nth witness adidxswgp 3)
                                     /\ valid_xidxvalsgp (drop 4 adidxswgp),
    
    op thfc <- thfc,
    
    op dpseed <- dpseed,
    op ddgstblock <- ddgstblock,
    
  theory DigestBlock <- DigestBlock,
  theory DigestBlockFT <- DigestBlockFT,
  theory HA <- HA,
  
  type dgstblock <- dgstblock,
  type adrs <- adrs
  
  proof ge2_adrslen, ge1_n, val_log2w, ge1_c, dpseed_ll, ddgstblock_ll, valid_widxvals_idxvals.
  realize ge2_adrslen by smt(ge6_adrslen).
  realize ge1_n by exact: ge1_n.
  realize val_log2w by exact: val_log2w.
  realize ge1_c.
    rewrite (: d = d - 1 + 1) // big_int_recr /= 2:ler_paddl; 1: smt(ge1_d).
    + rewrite sumr_ge0_seq => d' /mem_range [ge0_dp ltd_dp] _ /=. 
      by rewrite nrnodesht_h 3:expr_ge0 //; 1,2: smt(ge0_h).   
    rewrite nrnodesht_h; 1,2: smt(ge0_hp ge1_d).
    by rewrite -add0r -ltzE expr_gt0.
  qed.
  realize dpseed_ll by exact: dpseed_ll. 
  realize ddgstblock_ll by exact: ddgstblock_ll.
  realize valid_widxvals_idxvals.
    rewrite /(<=) => adidxs valwadidxs; apply valid_xidxvals_idxvals.
    move: valwadidxs => @/valid_widxvals @/valid_widxvalsgp @/valid_widxvalslp.
    rewrite /valid_xidxvals /valid_xidxvalslp /valid_xidxvalslpch. 
    by rewrite drop_drop //= ?nth_drop //= ?nth_take //= /#.
  qed.
    
import DBLL WAddress EmsgWOTS.

(*
lemma eq_valid_xadrsch_wadrs (ad : adrs) :
  valid_xadrsch ad <=> valid_wadrs ad.
proof.
rewrite /valid_xadrsch /valid_xadrschidxs /valid_xidxchvals /valid_xidxvalslpch. 
rewrite /valid_wadrs /valid_wadrsidxs /valid_widxvals /valid_widxvalslp.
by rewrite drop_drop // ?nth_drop // ?nth_take. 
qed.
*)

(* - Types (3/3) - *)
(* -- FL-SL-XMSS(-MT)-TW specific -- *)
(* Public keys *)
type pkFLXMSSMTTW = dgstblock * pseed * adrs.
type pkFLSLXMSSMTTW = pkFLXMSSMTTW.

(* Secret keys 
type skFLXMSSMTTW = index * sseed * pseed * adrs.
*)
type skFLSLXMSSMTTW = sseed * pseed * adrs.

(* Messages *)
type msgFLXMSSMTTW = msgWOTS.
type msgFLSLXMSSMTTW = msgFLXMSSMTTW.

(* Lists of length h' of which the entries are digest of length 1 (block of 8 * n bits) *)
clone import Subtype as DBHPL with
  type T <= dgstblock list,
    op P ls <= size ls = h'
    
  proof *.
  realize inhabited by exists (nseq h' witness); rewrite size_nseq; smt(ge0_hp).
      
(* Authentication paths in inner (XMSS) tree *)
type apFLXMSSTW = DBHPL.sT.

(* 
  Lists of length d of which the entries are sigWOTS/authentication path pairs 
  (i.e., FL-SL-XMSS signatures) 
*)
clone import Subtype as SAPDL with
  type T <= (sigWOTS * apFLXMSSTW) list,
    op P ls <= size ls = d
    
  proof *.
  realize inhabited by exists (nseq d witness); rewrite size_nseq; smt(ge1_d).

type sigFLSLXMSSMTTW = SAPDL.sT.

(* Signatures
type sigFLXMSSMT = index * sigFLXMSSMTNI.
type sigFLXMSSMTTW = sigFLXMSSMT.
*)


(* - Distributions (2/2) - *)
(* Proper distribution over messages considered for FL-SL-XMSS-MT *)
op [lossless] dmsgFLSLXMSSMTTW : msgFLSLXMSSMTTW distr.

(*
(*
  Proper distribution over (full) secret keys of FL-SL-XMSS, 
  i.e., a list of length l' containing (full) WOTS secret keys.
*)
op dskWOTSlp : skWOTS list distr = dlist dskWOTS l'.

(* Properness of distribution over full FL-SL-XMSS secret keyes*)
lemma dskWOTSlp_ll : is_lossless dskWOTSlp.
proof. by rewrite dlist_ll dskWOTS_ll. qed.
*)



(* - Operators (2/2) - *)
(* -- Merkle (hyper)ree -- *)
(* Update function for height and breadth indices (down the tree) *)
op updhbidx (hbidx : int * int) (b : bool) : int * int = 
  (hbidx.`1 - 1, if b then 2 * hbidx.`2 + 1 else 2 * hbidx.`2).

(* Function around trh with desired form for use in abstract merkle tree operators  *)
op trhi (ps : pseed) (ad : adrs) (hbidx : int * int) (x x' : dgstblock) : dgstblock =
  trh ps (set_thtbidx ad hbidx.`1 hbidx.`2) (val x ++ val x').

(* 
  Computes the (hash) value corresponding to the root of a binary tree w.r.t.
  a certain public seed, address, height index, and breadth index. 
*)
op val_bt_trh (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (hidx bidx : int) : dgstblock =
  val_bt (trhi ps ad) updhbidx bt (hidx, bidx).

(* 
  Constructs an authentication path (without embedding it in the corresponding subtype)
  from a binary tree and a path represented by a boolean list w.r.t. a certain 
  public seed, address, height index, and breadth index
*)
op cons_ap_trh_gen (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (bs : bool list) (hidx bidx : int) : dgstblock list =
  cons_ap (trhi ps ad) updhbidx bt bs (hidx, bidx).  

(*
  Computes the (hash) value corresponding to an authentication path, a leaf, and a 
  path represented by a boolean list w.r.t a certain public seed, address, height index, 
  and breadth index
*)  
op val_ap_trh_gen (ps : pseed) (ad : adrs) (ap : dgstblock list) (bs : bool list) (leaf : dgstblock) (hidx : int) (bidx : int) : dgstblock =
  val_ap (trhi ps ad) updhbidx ap bs leaf (hidx, bidx).

(* 
  Constructs authentication path (embedding it in the corresponding subtype)
  for the special case of binary trees of height h' and indices between 0 (including) and
  2 ^ h' (including) w.r.t. a certain public seed, address, height index h', and breadth index
  0. Note that, in case the given binary tree is not of height h',
  this operator does not explicitly fail; instead, witness is returned.
*)
op cons_ap_trh (bt : dgstblock bintree) (idx : index) (ps : pseed) (ad : adrs) : apFLXMSSTW =
  DBHPL.insubd (cons_ap_trh_gen ps ad bt (rev (int2bs h (val idx))) h' 0).

(* 
  Computes value corresponding to an authentication path, leaf, and a path represented 
  by the big-endian binary representation of an index between 0 (including) 
  and 2 ^ h (including) w.r.t. a certain public seed, address, height index h, 
  and breadth index 0. 
*)
op val_ap_trh (ap : apFLXMSSTW) (idx : index) (leaf : dgstblock) (ps : pseed) (ad : adrs) : dgstblock = 
  val_ap_trh_gen ps ad (val ap) (rev (int2bs h (val idx))) leaf h 0.
  
(*
  Extracts a collision, height index, and breadth index from a binary tree and 
  an authentication path w.r.t. a certain public seed, address, (initial) height index, and 
  (initial) breadth index
*)   
op extract_coll_bt_ap_trh (ps : pseed) 
                          (ad : adrs) 
                          (bt : dgstblock bintree) 
                          (ap : dgstblock list) 
                          (bs : bool list) 
                          (leaf : dgstblock) 
                          (hidx bidx : int) =
   extract_collision_bt_ap (trhi ps ad) updhbidx bt ap bs leaf (hidx, bidx).


(* - Types (3/3) - *)
(* 
  FL-SL-XMSS-MT-TW addresses
  Only used to select arbitrary valid FL-SL-XMSS-MT-TW 
  address in security notion/reductions
 *)
clone import Subtype as XHA with
  type T <= adrs,
    op P ad <= valid_xadrs ad. 
  
type xadrs = XHA.sT.



(* - Specifications - *)
(* Fixed-Length, StateLess XMSS-MT-TW in Encompassing Structure *)
module FL_SL_XMSS_MT_TW_ES = {
  (* Compute list of (inner tree) leaves from a secret seed, public seed, and address *) 
  proc leaves_from_sspsad(ss : sseed, ps : pseed, ad : adrs) : dgstblock list = {
    var skWOTS : skWOTS;
    var pkWOTS : pkWOTS;
    var leaf : dgstblock;
    var leaves : dgstblock list;
    
    leaves <- [];
    while (size leaves < l') {
      (* Generate a WOTS-TW secret key *)
      skWOTS <@ WOTS_TW_ES.gen_skWOTS(ss, ps, set_kpidx (set_typeidx ad chtype) (size leaves));
      
      (* Compute the WOTS-TW public key from the generated WOTS-TW secret key *)
      pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leaves));
      
      (* Compute leaf from the computed WOTS-TW public key *)
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leaves)) (flatten (map DigestBlock.val (val pkWOTS)));

      leaves <- rcons leaves leaf;
    }
    
    return leaves;
  }
  
  (* Generate root of hypertree from secret seed, public seed, and address *)
  proc gen_root(ss : sseed, ps : pseed, ad : adrs) : dgstblock = {
    var root : dgstblock;
    var leaves : dgstblock list;
    
    (* Compute list of leaves *)
    leaves <@ leaves_from_sspsad(ss, ps, set_ltidx ad (d - 1) 0);
    
    (* 
      Compute root (hash value) from the computed list of leaves, given public seed, and
      given address (after setting the type to tree hashing)
    *)
    root <- val_bt_trh ps (set_typeidx (set_ltidx ad (d - 1) 0) trhtype) (list2tree leaves) h' 0;

    return root;
  }
  
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : pkFLSLXMSSMTTW * skFLSLXMSSMTTW = {
    var root : dgstblock;
    var leaves : dgstblock list;
    var pk : pkFLSLXMSSMTTW;
    var sk : skFLSLXMSSMTTW;
    
    root <@ gen_root(ss, ps, ad);
    
    pk <- (root, ps, ad);
    sk <- (ss, ps, ad);
    
    return (pk, sk); 
  }
  
  (* 
    Signing procedure.
    Note that, in contrast to the signing procedure of XMSS-MT as a standalone, 
    this signing procedure does not update the secret key itself.
    This is assumed to be taken care of by the encompassing structure.
  *)
  proc sign(sk : skFLSLXMSSMTTW, m : msgFLSLXMSSMTTW, idx : index) : sigFLSLXMSSMTTW = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var tidx, kpidx : int;
    var skWOTS : skWOTS;
    var sigWOTS : sigWOTS;
    var skWOTSl : skWOTS list;
    var leaves : dgstblock list;
    var ap : apFLXMSSTW;
    var sapl : (sigWOTS * apFLXMSSTW) list;
    var sig : sigFLSLXMSSMTTW;
    
    (* Extract secret seed, public seed, and address from the secret key *)
    (ss, ps, ad) <- sk;
    
    (* Initialize signature list, tree index, and key pair index *)
    sapl <- [];
    (tidx, kpidx) <- edivz (val idx) l';
    while (size sapl < d) {
      (* Compute the WOTS-TW signature on the given message *)
      sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx (set_ltidx ad (size sapl) tidx) chtype) kpidx), m);

      (* Compute the list of leaves *)
      leaves <@ leaves_from_sspsad(ss, ps, (set_ltidx ad (size sapl) tidx));

      (* Construct the authentication path from the computed list of leaves *)
      ap <- cons_ap_trh (list2tree leaves) idx ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype);
      
      (* Add computed WOTS-TW signature and authentication path  *)
      sapl <- rcons sapl (sigWOTS, ap);
      
      (* Compute next tree and key pair indices *)
      (tidx, kpidx) <- edivz tidx l';
    }
    
    sig <- insubd sapl;
    
    return sig;
  }
  
  proc root_from_sigFLSLXMSSMTTW(m : msgFLSLXMSSMTTW, sig : sigFLSLXMSSMTTW, idx : index, ps : pseed, ad : adrs) : dgstblock = {
    var root : dgstblock;
    var tidx, kpidx : int;
    var i : int;
    var sigWOTS : sigWOTS;
    var ap : apFLXMSSTW;
    var pkWOTS : pkWOTS;
    var leaf : dgstblock;
    
    (* Initialize loop counter, (supposed) root variable, tree index, and key pair index *)
    i <- 0;
    root <- m;
    (tidx, kpidx) <- edivz (val idx) l';
    while (i < d) {
      (* Extract WOTS-TW signature and corresponding authentication path for considered tree *)
      (sigWOTS, ap) <- nth witness (val sig) i;
      
      (* Compute WOTS-TW public key *)
      pkWOTS <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(root, sigWOTS, ps, set_kpidx (set_typeidx (set_ltidx ad i tidx) chtype) kpidx);
    
      (* Compute leaf from the computed WOTS-TW public key *)
      leaf <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad i tidx) pkcotype) kpidx) (flatten (map DigestBlock.val (val pkWOTS)));
    
      (* Compute root from computed leaf (and extracted authentication path) *)
      root <- val_ap_trh ap idx leaf ps (set_typeidx (set_ltidx ad i tidx) trhtype);
      
      (* Compute next tree and key pair indices and increase loop counter *)
      (tidx, kpidx) <- edivz tidx l';
      i <- i + 1;
    }
    
    return root;    
  }
  
  proc verify(pk : pkFLSLXMSSMTTW, m : msgFLSLXMSSMTTW, sig : sigFLSLXMSSMTTW, idx : index) : bool = {
    var root, root' : dgstblock;
    var ps : pseed;
    var ad : adrs;
     
    (* Extract root (hash) value, public seed, and address from the public key *)
    (root, ps, ad) <- pk;
    
    root' <@ root_from_sigFLSLXMSSMTTW(m, sig, idx, ps, ad);
      
    return root' = root;
  }
}.

(* Fixed-Length StateLess FL-SL-XMSS-MT-TW in Encompassing Structure (No PRF) *)  
module FL_SL_XMSS_MT_TW_ES_NPRF = {
  (* Compute list of (inner tree) leaves from a WOTS-TW secret key, public seed, and address *) 
  proc leaves_from_sklpsad(skWOTSl : skWOTS list, ps : pseed, ad : adrs) : dgstblock list = {
    var skWOTS : skWOTS;
    var pkWOTS : pkWOTS;
    var leaf : dgstblock;
    var leaves : dgstblock list;
    
    leaves <- [];
    while (size leaves < l') {
      (* Extract considered WOTS-TW secret key *)
      skWOTS <- nth witness skWOTSl (size leaves);
      
      (* Compute the WOTS-TW public key from WOTS-TW secret key *)
      pkWOTS <@ WOTS_TW_ES_NPRF.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leaves));
      
      (* Compute leaf from the computed WOTS-TW public key *)
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leaves)) (flatten (map DigestBlock.val (val pkWOTS)));

      leaves <- rcons leaves leaf;
    }
    
    return leaves;
  }
  
  proc keygen(ps : pseed, ad : adrs) : pkFLSLXMSSMTTW * (skWOTS list list list * pseed * adrs) = {
    var root : dgstblock;
    var skWOTS_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSit : skWOTS list;
    var skWOTSsl : skWOTS list list;
    var skWOTSal : skWOTS list list list;
    var leaves : dgstblock list;
    var pk : pkFLSLXMSSMTTW;
    var sk : skWOTS list list list * pseed * adrs;
    
    (*
      For each layer in the hypertree (starting from layer 0, i.e., the bottom layer),
      sample the secret key for each inner tree in that layer (starting from the left-most inner tree).
      The result is the full secret key of the hypertree (skWOTSlal).
      This secret key is a list that contains a single list for each of the layers in the hypertree, starting with
      a list for the bottom layer and ending with a list of the top layer.
      In turn, a list for a layer contains the secret keys for each of the inner trees in that layer, starting
      with the secret key for the left-most inner tree and ending with the secret key for the right-most inner tree.
      Then, each secret key of an inner tree is a list of length l' containing WOTS-TW secret keys
      corresponding to the leaves of that inner tree, from left to right.
      Finally, each WOTS-TW secret key is a list of length len of dgstblock elements.
      Nested while-loop construction (instead of using, e.g., dlist) in order to ease PRF proof step.   
    *)
    skWOTSal <- [];
    while (size skWOTSal < d) {
      skWOTSsl <- [];
      while (size skWOTSsl < nr_trees (size skWOTSal)) {
        skWOTSit <- [];
        while (size skWOTSit < l) {
          skWOTS <- [];
          while (size skWOTS < len) {
            skWOTS_ele <$ ddgstblock;
            skWOTS <- rcons skWOTS skWOTS_ele;  
          }
          
          (* Add WOTS-TW secret key to list of secret keys of this inner tree *)
          skWOTSit <- rcons skWOTSit (DBLL.insubd skWOTS);
        }
        
        (* Add secret key of inner tree to list of secret keys in this layer *)
        skWOTSsl <- rcons skWOTSsl skWOTSit;
      }
      (* Add secret key of layer to list of secret keys for all layers *)
      skWOTSal <- rcons skWOTSal skWOTSsl; 
    }

    (* 
      Extract secret key of the top-most inner tree in the hyper tree 
      and compute the corresponding leaves.
    *)
    skWOTSit <- nth witness (nth witness skWOTSal (d - 1)) 0;
    leaves <@ leaves_from_sklpsad(skWOTSit, ps, set_ltidx ad (d - 1) 0);
    
    (*
      Compute root (hash value) from the computed list of leaves, given public seed, and
      given address (after setting the type to tree hashing)
    *)
    root <- val_bt_trh ps (set_typeidx (set_ltidx ad (d - 1) 0) trhtype) (list2tree leaves) h' 0;
    
    pk <- (root, ps, ad);
    sk <- (skWOTSal, ps, ad);
    
    return (pk, sk); 
  }
  
  (* 
    Signing procedure.
    Note that, in contrast to the signing procedure of XMSS-MT as a standalone, 
    this signing procedure does not update the secret key itself.
    This is assumed to be taken care of by the encompassing structure.
  *)
  proc sign(sk : skWOTS list list list * pseed * adrs, m : msgFLSLXMSSMTTW, idx : index) : sigFLSLXMSSMTTW = {
    var ps : pseed;
    var ad : adrs;
    var tidx, kpidx : int;
    var skWOTS : skWOTS;
    var sigWOTS : sigWOTS;
    var skWOTSlp : skWOTS list;
    var skWOTSld : skWOTS list list list;
    var leaves : dgstblock list;
    var ap : apFLXMSSTW;
    var sapl : (sigWOTS * apFLXMSSTW) list;
    var sig : sigFLSLXMSSMTTW;
    
    (* Extract index, secret key, public seed, and address from the secret key *)
    (skWOTSld, ps, ad) <- sk;
    
    (* Initialize signature list, tree index, and key pair index *)
    sapl <- [];
    (tidx, kpidx) <- edivz (val idx) l';
    while (size sapl < d) {
      (* 
        Extract FL-SL-XMSS-TW secret key in considered layer (size sapl), and corresponding to
        considered inner tree in this layer (tidx).
      *)
      skWOTSlp <- nth witness (nth witness skWOTSld (size sapl)) tidx;
      
      (* 
        Extract WOTS-TW secret key from secret key of considered inner tree, 
        and corresponding to considered key pair in this inner tree (kpidx)  
      *) 
      skWOTS <- nth witness skWOTSlp kpidx;
      
      (* Compute the WOTS-TW signature on the given message *)
      sigWOTS <@ WOTS_TW_ES_NPRF.sign((skWOTS, ps, set_kpidx (set_typeidx (set_ltidx ad (size sapl) tidx) chtype) kpidx), m);

      (* Compute the list of leaves *)
      leaves <@ leaves_from_sklpsad(skWOTSlp, ps, set_ltidx ad (size sapl) tidx);

      (* Construct the authentication path from the computed list of leaves *)
      ap <- cons_ap_trh (list2tree leaves) idx ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype);
      
      (* Add computed WOTS-TW signature and authentication path  *)
      sapl <- rcons sapl (sigWOTS, ap);
      
      (* Compute next tree and key pair indices *)
      (tidx, kpidx) <- edivz tidx l';
    }
    
    sig <- insubd sapl;
    
    return sig;
  }
  
  proc verify = FL_SL_XMSS_MT_TW_ES.verify
(*  
  proc verify(pk : pkFLSLXMSSMTTW, m : msgFLSLXMSSMTTW, sig : sigFLSLXMSSMTTW) : bool = {
    var root, root' : dgstblock;
    var ps : pseed;
    var ad : adrs;
    var idx : index;
    var signi : sigFLXMSSMTNI;
    var tidx, kpidx : int;
    var i : int;
    var sigWOTS : sigWOTS;
    var ap : apFLXMSSTW;
    var pkWOTS : pkWOTS;
    var leaf : dgstblock;
     
    (* Extract root (hash) value, public seed, and address from the public key *)
    (root, ps, ad) <- pk;
    
    (* Extract index, WOTS-TW signature, and authentication path from the signature *)
    (idx, signi) <- sig;
    
    (* Initialize loop counter, (supposed) root variable, tree index, and key pair index *)
    i <- 0;
    root' <- m;
    (tidx, kpidx) <- edivz (val idx) l';
    while (i < d) {
      (* Extract WOTS-TW signature and corresponding authentication path for considered tree *)
      (sigWOTS, ap) <- nth witness (val signi) i;
      
      (* Compute WOTS-TW public key *)
      pkWOTS <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(root', sigWOTS, ps, set_kpidx (set_typeidx (set_ltidx ad i) tidx) chtype) kpidx);
    
      (* Compute leaf from the computed WOTS-TW public key *)
      leaf <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad i) tidx) pkcotype) kpidx) (flatten (map DigestBlock.val (val pkWOTS)));
    
      (* Compute root from computed leaf (and extracted authentication path) *)
      root' <- val_ap_trh ap idx leaf ps (set_typeidx (set_ltidx ad i) tidx) trhtype);
      
      (* Compute next tree and key pair indices and increase loop counter *)
      (tidx, kpidx) <- edivz tidx l';
      i <- i + 1;
    }
    
    return root' = root;
  }
*)
}.



(* - Proof - *)
(* -- Adversary classes -- *)
module type Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF (OC : Oracle_THFC) = {
  proc choose() : msgFLSLXMSSMTTW list {OC.query}
  proc forge(pk : pkFLSLXMSSMTTW, sigl : sigFLSLXMSSMTTW list) : msgFLSLXMSSMTTW * sigFLSLXMSSMTTW * index {}
}.

  
(* -- Security notions -- *)
module EUF_NAGCMA_FLSLXMSSMTTWESNPRF (A : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF, OC : Oracle_THFC) = {
  proc main() : bool = {
    var ad : adrs;
    var ps : pseed;
    var pk : pkFLSLXMSSMTTW;
    var sk : skWOTS list list list * pseed * adrs;
    var ml : msgFLSLXMSSMTTW list;
    var sigl : sigFLSLXMSSMTTW list;
    var m, m' : msgFLSLXMSSMTTW;
    var sig, sig' : sigFLSLXMSSMTTW;
    var idx' : index;
    var is_valid, is_fresh : bool;
    var adsOC : adrs list; 
    
    ad <- val (witness<:xadrs>);
    ps <$ dpseed;

    OC.init(ps);

    ml <@ A(OC).choose();
            
    (pk, sk) <@ FL_SL_XMSS_MT_TW_ES_NPRF.keygen(ps, ad);

    sigl <- [];
    while (size sigl < min (size ml) l) {
      m <- nth witness ml (size sigl);

      sig <@ FL_SL_XMSS_MT_TW_ES_NPRF.sign(sk, m, insubd (size sigl));
      
      sigl <- rcons sigl sig;
    }
    
    (m', sig', idx') <@ A(OC).forge(pk, sigl);

    is_valid <@ FL_SL_XMSS_MT_TW_ES_NPRF.verify(pk, m', sig', idx');

    is_fresh <- ! m' \in take (size sigl) ml;

    adsOC <@ OC.get_tweaks();
    
    return is_valid /\ is_fresh /\ 
           all (fun (ad : adrs) =>   get_typeidx ad <> chtype 
                                  /\ get_typeidx ad <> pkcotype
                                  /\ get_typeidx ad <> trhtype) adsOC; 
  }
}.

print Oracle_THFC.

(* -- Reduction adversaries -- *)
module (R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA (A : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF) : Adv_MEUFGCMA_WOTSTWESNPRF) (O : Oracle_MEUFGCMA_WOTSTWESNPRF, OC : Oracle_THFC) = {
  var ad : adrs
  
  module O_THFC : Oracle_THFC = {
    var ads : adrs list
    var xs : dgst list 
    
    proc init(ps : pseed) : unit = {
      ads <- [];
      xs <- [];
    }
    
    proc query(adq : adrs, x : dgst) : dgstblock = {
      var y : dgstblock;
      
      
      y <@ OC.query(adq, x);
      
      ads <- rcons ads adq;
      xs <- rcons xs x;
      
      return y;
    }
    
    proc get_tweaks() : adrs list = {
      return ads;
    }
  }
  
  proc choose() : unit = {
    var ml : msgFLSLXMSSMTTW list;
    
    O_THFC.init(witness);
    
    ml <@ A(O_THFC).choose();
    
    ad <- val (witness<:xadrs>);
    
    
  }
  
  proc forge(ps : pseed) : int * msgWOTS * sigWOTS = {
    return witness;
  }
}.


module (R_SMDTTCRCPKCO_EUFNAGCMA (A : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF) : PKCOC_TCR.Adv_SMDTTCRC) (O : PKCOC_TCR.Oracle_SMDTTCR, OC : PKCOC.Oracle_THFC) = {
  proc pick() : unit = {
  
  }
  
  proc find(ps : pseed) : int * dgst = {
    return witness;
  }
}.

module (R_SMDTTCRCTRH_EUFNAGCMA (A : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF) : TRHC_TCR.Adv_SMDTTCRC) (O : TRHC_TCR.Oracle_SMDTTCR, OC : TRHC.Oracle_THFC) = {
  proc pick() : unit = {
  
  }
  
  proc find(ps : pseed) : int * dgst = {
    return witness;
  }
}.


section Proof_EUF_NAGCMA_FL_SL_XMSS_MT_TW_ES_NPRF.

declare module A <: Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF {-O_MEUFGCMA_WOTSTWESNPRF, -PKCOC_TCR.O_SMDTTCR_Default, -PKCOC_TCR.O_SMDTTCR_Default, -TRHC_TCR.O_SMDTTCR_Default, -TRHC_TCR.O_SMDTTCR_Default, -FC_UD.O_SMDTUD_Default, -FC_TCR.O_SMDTTCR_Default, -FC_PRE.O_SMDTPRE_Default, -PKCOC.O_THFC_Default, -FC.O_THFC_Default, -TRHC.O_THFC_Default, -R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA, -R_SMDTTCRCPKCO_EUFNAGCMA, -R_SMDTTCRCTRH_EUFNAGCMA, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_SMDTPREC_Game4WOTSTWES}.


local lemma EUFNAGCMA_FLSLXMSSMTTWESNPRF_MEUFGCMAWOTSTWES &m :
  Pr[EUF_NAGCMA_FLSLXMSSMTTWESNPRF(A, O_THFC_Default).main() @ &m : res]
  <=
  Pr[M_EUF_GCMA_WOTSTWESNPRF(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A), O_MEUFGCMA_WOTSTWESNPRF, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFNAGCMA(A), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFNAGCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res].
proof. admit. qed.


lemma EUFNAGCMA_FLSLXMSSMTTWESNPRF &m :
  Pr[EUF_NAGCMA_FLSLXMSSMTTWESNPRF(A, O_THFC_Default).main() @ &m : res]
  <=
  (w - 2)%r
    * `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A)), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res]
        - Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A)), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]| 
  + 
  Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A)), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res] 
  + 
  Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A)), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFNAGCMA(A), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFNAGCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res].
proof.
move: (MEUFGCMA_WOTSTWESNPRF (R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A)) _ _ &m) 
      (EUFNAGCMA_FLSLXMSSMTTWESNPRF_MEUFGCMAWOTSTWES &m); 3: smt(). 
+ admit. 
admit. 
qed.

end section Proof_EUF_NAGCMA_FL_SL_XMSS_MT_TW_ES_NPRF.
