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
lemma ge1_l : 1 <= l.
proof. by rewrite /l -add0r -ltzE expr_gt0. qed.



(* - Types (1/3) - *)
(* -- General -- *)
(* Index *)
clone import Subtype as Index with
  type T <= int,
    op P i <= 0 <= i < l
    
  proof *.
  realize inhabited by exists 0; smt(ge1_l).

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
move=> gtdp_d gehpp_hp.
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
  realize ge0_tsmdttcr by smt(Top.ge1_l).  

  
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

(* Initialization ("zero") address *)
const adz : { adrs | valid_xadrs adz } as valx_adz.


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
    
import DBLL WAddress EmsgWOTS BaseW.

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
op cons_ap_trh (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (idx : int) : apFLXMSSTW =
  DBHPL.insubd (cons_ap_trh_gen ps ad bt (rev (int2bs h' idx)) h' 0).

(* 
  Computes value corresponding to an authentication path, leaf, and a path represented 
  by the big-endian binary representation of an index between 0 (including) 
  and 2 ^ h' (including) w.r.t. a certain public seed, address, height index h', 
  and breadth index 0. 
*)
op val_ap_trh (ap : apFLXMSSTW) (idx : int) (leaf : dgstblock) (ps : pseed) (ad : adrs) : dgstblock = 
  val_ap_trh_gen ps ad (val ap) (rev (int2bs h' idx)) leaf h' 0.
  
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

clone import Subtype as XHA with
  type T <= adrs,
    op P ad <= valid_xadrs ad. 
  
type xadrs = XHA.sT.
*)

lemma validxadrs_validwadrs_setallch (i j u v : int) (ad : adrs) :
     valid_xadrs ad
  => valid_lidx i
  => valid_tidx i j
  => valid_kpidx u
  => valid_chidx v
  => valid_wadrs (set_chidx (set_kpidx (set_typeidx (set_ltidx ad i j) chtype) u) v).
proof.
move=> @/valid_xadrs @/valid_xadrsidxs [eqal_szad @/valid_xidxvals [valgpad @/valid_xidxvalslp vallpad]].
have gtl6_szad : forall i, i < 6 => i < adrs_len by smt(ge6_adrslen).
have gtif_szad : forall i, i < 6 => i < if 6 < adrs_len then 6 else adrs_len by smt(ge6_adrslen).
move=> vali valj valu valv @/set_ltidx @/set_typeidx.
+ rewrite insubdK 1:/valid_adrsidxs 1:?size_put 1:eqal_szad /= 1:valid_xidxvals_idxvals.
  rewrite /valid_xidxvals ?drop_putK 1,2:// valgpad /= /valid_xidxvalslp.
  move: vallpad => @/valid_xidxvalslpch @/valid_xidxvalslppkco @/valid_xidxvalslptrh.
  by rewrite ?take_put /= ?nth_put ?size_put ?size_take ?eqal_szad
              1,3,5,7,9,11,13,15,17,19,21,23:// 1..12:gtif_szad 1..24:// /= /#.
rewrite /set_kpidx /set_idx insubdK 1:/valid_adrsidxs 1:?size_put 1:eqal_szad /= 1:valid_xidxvals_idxvals.
+ rewrite /valid_xidxvals ?drop_putK 1..6:// valgpad /= /valid_xidxvalslp.
  (* move: vallpad => @/valid_xidxvalslpch @/valid_xidxvalslppkco @/valid_xidxvalslptrh. *)
  left.
  by rewrite ?take_put /= /valid_xidxvalslpch ?nth_put ?size_put ?size_take ?eqal_szad
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71:// 1..36:gtif_szad 1..72:// /=; smt(val_w ge2_len ge1_lp).
rewrite /set_chidx /set_idx insubdK 1:/valid_adrsidxs 1:?size_put 1:eqal_szad /= 1:valid_xidxvals_idxvals.
+ rewrite /valid_xidxvals ?drop_putK 1..7:// valgpad /= /valid_xidxvalslp.
  left.
  by rewrite ?take_put /= /valid_xidxvalslpch ?nth_put ?size_put ?size_take ?eqal_szad
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81,83:// 1..42:gtif_szad 1..84:// /=; smt(val_w ge2_len ge1_lp).
rewrite /valid_wadrs insubdK 1:/valid_adrsidxs 1:?size_put 1:eqal_szad /= 1:valid_xidxvals_idxvals.
+ rewrite /valid_xidxvals ?drop_putK 1..8:// valgpad /= /valid_xidxvalslp.
  left.
  by rewrite ?take_put /= /valid_xidxvalslpch ?nth_put ?size_put ?size_take ?eqal_szad
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95:// 1..48:gtif_szad 1..96:// /=; smt(val_w ge2_len ge1_lp).
rewrite /valid_wadrsidxs ?size_put eqal_szad /= /valid_widxvals drop_drop 1,2://.
rewrite ?nth_drop 1..8:// /= ?nth_put ?size_put ?eqal_szad ?gtl6_szad 1..64:// /=.
rewrite ?drop_putK 1..8:// valgpad /= ?take_put /= /valid_widxvalslp.
by rewrite ?nth_put ?size_put ?size_take ?eqal_szad 1,3,5,7,9,11:// /=; smt(val_w). 
qed. 



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
    var root : dgstblock;
    
    (* Extract secret seed, public seed, and address from the secret key *)
    (ss, ps, ad) <- sk;
    
    (* Initialize signature list, tree index, and key pair index *)
    root <- m;
    sapl <- [];
    (tidx, kpidx) <- (val idx, 0);
    while (size sapl < d) {
      (* Update tree and key pair indices *)
      (tidx, kpidx) <- edivz tidx l';

      (* Compute the WOTS-TW signature on the given message *)
      sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx (set_ltidx ad (size sapl) tidx) chtype) kpidx), root);

      (* Compute the list of leaves *)
      leaves <@ leaves_from_sspsad(ss, ps, (set_ltidx ad (size sapl) tidx));

      (* Construct the authentication path from the computed list of leaves *)
      ap <- cons_ap_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) kpidx;
      
      (* Compute next message/root to sign *)
      root <- val_bt_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) h' 0;
      
      (* Add computed WOTS-TW signature and authentication path  *)
      sapl <- rcons sapl (sigWOTS, ap);
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
    
    (* Initialize loop counter, (supposed) root variable, and tree index *)
    i <- 0;
    root <- m;
    (tidx, kpidx) <- (val idx, 0);
    while (i < d) {
      (* Update tree and key pair indices *)
      (tidx, kpidx) <- edivz tidx l';
    
      (* Extract WOTS-TW signature and corresponding authentication path for considered tree *)
      (sigWOTS, ap) <- nth witness (val sig) i;
      
      (* Compute WOTS-TW public key *)
      pkWOTS <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(root, sigWOTS, ps, set_kpidx (set_typeidx (set_ltidx ad i tidx) chtype) kpidx);
    
      (* Compute leaf from the computed WOTS-TW public key *)
      leaf <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad i tidx) pkcotype) kpidx) (flatten (map DigestBlock.val (val pkWOTS)));
    
      (* Compute root from computed leaf (and extracted authentication path) *)
      root <- val_ap_trh ap kpidx leaf ps (set_typeidx (set_ltidx ad i tidx) trhtype);
      
      (* Increase loop counter *)
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
    var skWOTSlp : skWOTS list;
    var skWOTSnt : skWOTS list list;
    var skWOTStd : skWOTS list list list;
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
    leaves <@ leaves_from_sklpsad(skWOTSlp, ps, set_ltidx ad (d - 1) 0);
    
    (*
      Compute root (hash value) from the computed list of leaves, given public seed, and
      given address (after setting the type to tree hashing)
    *)
    root <- val_bt_trh ps (set_typeidx (set_ltidx ad (d - 1) 0) trhtype) (list2tree leaves) h' 0;
    
    pk <- (root, ps, ad);
    sk <- (skWOTStd, ps, ad);
    
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
    var root : dgstblock;
    var skWOTS : skWOTS;
    var sigWOTS : sigWOTS;
    var skWOTSlp : skWOTS list;
    var skWOTStd : skWOTS list list list;
    var leaves : dgstblock list;
    var ap : apFLXMSSTW;
    var sapl : (sigWOTS * apFLXMSSTW) list;
    var sig : sigFLSLXMSSMTTW;
    
    (* Extract index, secret key, public seed, and address from the secret key *)
    (skWOTStd, ps, ad) <- sk;
    
    (* Initialize root, signature list, and tree index *)
    root <- m;
    sapl <- [];
    (tidx, kpidx) <- (val idx, 0);
    while (size sapl < d) {
      (* Update tree and key pair indices *)
      (tidx, kpidx) <- edivz tidx l';
      
      (* 
        Extract FL-SL-XMSS-TW secret key in considered layer (size sapl), and corresponding to
        considered inner tree in this layer (tidx).
      *)
      skWOTSlp <- nth witness (nth witness skWOTStd (size sapl)) tidx;
      
      (* 
        Extract WOTS-TW secret key from secret key of considered inner tree, 
        and corresponding to considered key pair in this inner tree (kpidx)  
      *) 
      skWOTS <- nth witness skWOTSlp kpidx;
      
      (* Compute the WOTS-TW signature on the given message *)
      sigWOTS <@ WOTS_TW_ES_NPRF.sign((skWOTS, ps, set_kpidx (set_typeidx (set_ltidx ad (size sapl) tidx) chtype) kpidx), root);

      (* Compute the list of leaves *)
      leaves <@ leaves_from_sklpsad(skWOTSlp, ps, set_ltidx ad (size sapl) tidx);

      (* Construct the authentication path from the computed list of leaves *)
      ap <- cons_ap_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) kpidx;
      
      (* Compute next message/root to sign *)
      root <- val_bt_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) h' 0;
      
      (* Add computed WOTS-TW signature and authentication path  *)
      sapl <- rcons sapl (sigWOTS, ap);
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
  proc choose() : msgFLSLXMSSMTTW list { OC.query }
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
    
    ad <- adz;
    ps <$ dpseed;

    OC.init(ps);

    ml <@ A(OC).choose();
            
    (pk, sk) <@ FL_SL_XMSS_MT_TW_ES_NPRF.keygen(ps, ad);

    sigl <- [];
    while (size sigl < l) {
      m <- nth witness ml (size sigl);

      sig <@ FL_SL_XMSS_MT_TW_ES_NPRF.sign(sk, m, Index.insubd (size sigl));
      
      sigl <- rcons sigl sig;
    }
    
    (m', sig', idx') <@ A(OC).forge(pk, sigl);

    is_valid <@ FL_SL_XMSS_MT_TW_ES_NPRF.verify(pk, m', sig', idx');
    
    (*
    is_fresh <- ! m' \in take (size sigl) ml;
    *)
    is_fresh <- m' <> nth witness ml (val idx');
    
    return is_valid /\ is_fresh; 
  }
}.


(* -- Reduction adversaries -- *)
module (R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA (A : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF) : Adv_MEUFGCMA_WOTSTWESNPRF) (O : Oracle_MEUFGCMA_WOTSTWESNPRF, OC : Oracle_THFC) = {
  var ad : adrs
  var ml : msgFLSLXMSSMTTW list
  var pkWOTStd : pkWOTS list list list
  var sigWOTStd : sigWOTS list list list
  var leavestd : dgstblock list list list
  var rootstd : dgstblock list list
    
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
    var pkWOTS : pkWOTS;
    var pkWOTSlp : pkWOTS list;
    var pkWOTSnt, pkWOTSntp : pkWOTS list list;
    var sigWOTS : sigWOTS;
    var sigWOTSlp : sigWOTS list;
    var sigWOTSnt, sigWOTSntp : sigWOTS list list;
    var leaf : dgstblock;
    var leaveslp : dgstblock list;
    var leavesnt, leavesntp : dgstblock list list;
    var root : dgstblock;
    var rootsnt, rootsntp : dgstblock list;
    var lnode, rnode, node : dgstblock;
    var nodespl, nodescl : dgstblock list;
    var nodes : dgstblock list list;
    
    O_THFC.init(witness);
    
    ml <@ A(O_THFC).choose();
    
    ad <- adz;

    (* 
      Using the provided oracles, compute and store all the 
      WOTS-TW public keys, WOTS-TW signatures, (inner tree) leaves, and (inner tree) roots.
    *)
    pkWOTStd <- [];
    sigWOTStd <- [];
    leavestd <- [];
    rootstd <- [];
    (* For each layer in the hypertree, starting from the bottom-most layer,... *)
    while (size pkWOTStd < d) {
      pkWOTSnt <- [];
      sigWOTSnt <- [];
      leavesnt <- [];
      rootsnt <- [];
      rootsntp <- last ml rootstd;
      (* For each tree in the current layer, starting from the left-most tree,... *)
      while (size pkWOTSnt < nr_trees (size pkWOTStd)) {
        pkWOTSlp <- [];
        sigWOTSlp <- [];
        leaveslp <- [];
        (* For each leaf of the current tree, starting from the left-most leaf,... *)
        while (size pkWOTSlp < l') {
          (* Compute the to-be-signed message/root *)
          root <- nth witness rootsntp (size pkWOTSnt * l' + size pkWOTSlp);

          (* Query the challenge oracle on the computed message/root to obtain a (WOTS-TW) signature and public key *)
          (pkWOTS, sigWOTS) <@ O.query(WAddress.insubd (set_kpidx (set_typeidx (set_ltidx ad (size pkWOTStd) (size pkWOTSnt)) chtype) (size pkWOTSlp)), 
                                       root);  

          (* Query the family oracle to compress the obtained WOTS-TW public key to the corresponding leaf  *)
          leaf <@ OC.query(set_kpidx (set_typeidx (set_ltidx ad (size pkWOTStd) (size pkWOTSnt)) pkcotype) (size pkWOTSlp), 
                           flatten (map DigestBlock.val (val pkWOTS)));

          pkWOTSlp <- rcons pkWOTSlp pkWOTS;
          sigWOTSlp <- rcons sigWOTSlp sigWOTS;
          leaveslp <- rcons leaveslp leaf;
        }

        
        nodes <- [];
        (* For each layer in the current tree, starting from the layer right above the leaves,... *)
        while (size nodes < h') {
          nodespl <- last leaveslp nodes;

          nodescl <- [];
          (* For each (to-be-computed) node in the currently considered layer,... *)
          while (size nodescl < nr_nodes (size nodes + 1)) {
            (* Get the left and right children *)
            lnode <- nth witness nodespl (2 * size nodescl);
            rnode <- nth witness nodespl (2 * size nodescl + 1);

            (* Query the family oracle on the concatenation of the children to obtain the node *)
            node <@ OC.query(set_thtbidx (set_kpidx (set_typeidx (set_ltidx ad (size pkWOTStd) (size pkWOTSnt)) trhtype) (size pkWOTSlp)) 
                                         (size nodes + 1) (size nodescl), 
                             val lnode ++ val rnode);

            nodescl <- rcons nodescl node;
          }
          nodes <- rcons nodes nodescl;
        }  
        pkWOTSnt <- rcons pkWOTSnt pkWOTSlp;
        sigWOTSnt <- rcons sigWOTSnt sigWOTSlp;
        leavesnt <- rcons leavesnt leaveslp;
        rootsnt <- rcons rootsnt (nth witness (nth witness nodes (h' - 1)) 0); (* Root of current tree is the last computed/stored node *)
      }
      pkWOTStd <- rcons pkWOTStd pkWOTSnt;
      sigWOTStd <- rcons sigWOTStd sigWOTSnt;
      leavestd <- rcons leavestd leavesnt;
      rootstd <- rcons rootstd rootsnt;
    }
  }
  
  proc forge(ps : pseed) : int * msgWOTS * sigWOTS = {
    var m : msgFLSLXMSSMTTW;
    var pk : pkFLSLXMSSMTTW;
    var sigWOTS, sigWOTS' : sigWOTS;
    var pkWOTS, pkWOTS' : pkWOTS;
    var ap, ap' : apFLXMSSTW;
    var sapl, sapl' : (sigWOTS * apFLXMSSTW) list;
    var sig : sigFLSLXMSSMTTW;
    var sigl : sigFLSLXMSSMTTW list; 
    var m' : msgFLSLXMSSMTTW;
    var sig' : sigFLSLXMSSMTTW;
    var idx' : index;
    var root, root' : dgstblock;
    var roots' : dgstblock list;
    var tidx, kpidx : int;
    var tkpidxs : (int * int) list;
    var leaf' : dgstblock;
    var leaves : dgstblock list;
    var forgeryfs : bool list; 
    var ffidx, forgeryidx : int;
    
    (* Sign adversary-chosen messages using computed leaves/signatures *)
    sigl <- [];
    while (size sigl < l) {
      m <- nth witness ml (size sigl);
      
      sapl <- [];
      (tidx, kpidx) <- (size sigl, 0);
      while (size sapl < d) {
        (tidx, kpidx) <- edivz tidx l';
      
        sigWOTS <- nth witness (nth witness (nth witness sigWOTStd (size sapl)) tidx) kpidx;
        
        leaves <- nth witness (nth witness leavestd (size sapl)) tidx;

        ap <- cons_ap_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) kpidx;

        sapl <- rcons sapl (sigWOTS, ap);
      }

      sig <- insubd sapl;
      sigl <- rcons sigl sig;
    }
    
    root <- nth witness (nth witness rootstd (d - 1)) 0; (* Root of hypertree is the last computed root *)
    
    (m', sig', idx') <@ A(O_THFC).forge((root, ps, ad), sigl);
    
    (tidx, kpidx) <- (val idx', 0);
    tkpidxs <- [];
    root' <- m';
    roots' <- [];
    forgeryfs <- [];
    (* 
      For each WOTS-TW signature/authentication path pair in the forgery, check whether
      the signature is valid on the previous root (first one being the forgery's message),
      then compute the next root using the authentication path and the leaf resulting from
      compressing the WOTS-TW public key derived from the signature.
      Keep track of the intermediate roots and tree/keypair indices. 
    *)
    while (size forgeryfs < d) {
      (tidx, kpidx) <- edivz tidx l';
      
      (sigWOTS', ap') <- nth witness (val sig') (size forgeryfs);
      
      pkWOTS' <@ WOTS_TW_ES_NPRF.pkWOTS_from_sigWOTS(root', sigWOTS', ps, 
                                                     (set_kpidx (set_typeidx (set_ltidx ad (size forgeryfs) tidx) chtype) kpidx));
      pkWOTS <- nth witness (nth witness (nth witness pkWOTStd (size forgeryfs)) tidx) kpidx;
      
      forgeryfs <- rcons forgeryfs (pkWOTS' = pkWOTS);
      
      leaf' <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad (size forgeryfs) tidx) pkcotype) kpidx) 
                   (flatten (map DigestBlock.val (val pkWOTS'))); 
      root' <- val_ap_trh ap' kpidx leaf' ps (set_typeidx (set_ltidx ad (size forgeryfs) tidx) trhtype) ;
      roots' <- rcons roots' root';
      
      tkpidxs <- rcons tkpidxs (tidx, kpidx);
    }
    
    (* Get index of the first valid WOTS-TW signature in the forgery *)
    ffidx <- find ((=) true) forgeryfs;
    
    (* Get tree and key pair index corresponding to first WOTS-TW signature forgery *)    
    (tidx, kpidx) <- nth witness tkpidxs ffidx;
    
    (* Compute index in the challenge oracle's query list of the forgery *)
    forgeryidx <- bigi predT (fun i => nr_trees i) 0 ffidx * l' + tidx * l' + kpidx; 
    
    (* Get root and WOTS-TW sigature forming a forgery *)
    root' <- nth witness roots' ffidx;
    sigWOTS' <- (nth witness (val sig') ffidx).`1;
    
    return (forgeryidx, root', sigWOTS');
  }
}.

module (R_SMDTTCRCPKCO_EUFNAGCMA (A : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF) : PKCOC_TCR.Adv_SMDTTCRC) (O : PKCOC_TCR.Oracle_SMDTTCR, OC : PKCOC.Oracle_THFC) = {
  var ad : adrs
  var ml : msgFLSLXMSSMTTW list
  var skWOTStd : skWOTS list list list
  var pkWOTStd : pkWOTS list list list
  var sigWOTStd : sigWOTS list list list
  var leavestd : dgstblock list list list
  var rootstd : dgstblock list list
    
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
  
  proc pick() : unit = {
    var m : msgFLSLXMSSMTTW;
    var em : emsgWOTS;
    var ch_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt, skWOTSntp : skWOTS list list;
    var pkWOTS : dgstblock list;
    var pkWOTSlp : pkWOTS list;
    var pkWOTSnt, pkWOTSntp : pkWOTS list list;
    var sigWOTS : dgstblock list;
    var sigWOTSlp : sigWOTS list;
    var sigWOTSnt, sigWOTSntp : sigWOTS list list;
    var leaf : dgstblock;
    var leaveslp : dgstblock list;
    var leavesnt, leavesntp : dgstblock list list;
    var root : dgstblock;
    var rootsnt, rootsntp : dgstblock list;
    var lnode, rnode, node : dgstblock;
    var nodespl, nodescl : dgstblock list;
    var nodes : dgstblock list list;
    var i : int;
    
    O_THFC.init(witness);
    
    ml <@ A(O_THFC).choose();
    
    ad <- adz;

    (* 
      Using the provided oracles, compute and store all the 
      WOTS-TW secret keys, WOTS-TW public keys, WOTS-TW signatures, 
      (inner tree) leaves, and (inner tree) roots.
    *)
    skWOTStd <- [];
    pkWOTStd <- [];
    sigWOTStd <- [];
    leavestd <- [];
    rootstd <- [];
    (* For each layer in the hypertree, starting from the bottom-most layer,... *)
    while (size skWOTStd < d) {
      skWOTSnt <- [];
      pkWOTSnt <- [];
      sigWOTSnt <- [];
      leavesnt <- [];
      rootsnt <- [];
      rootsntp <- last ml rootstd;
      (* For each tree in the current layer, starting from the left-most tree,... *)
      while (size skWOTSnt < nr_trees (size skWOTStd)) {
        skWOTSlp <- [];
        pkWOTSlp <- [];
        sigWOTSlp <- [];
        leaveslp <- [];
        (* For each leaf of the current tree, starting from the left-most leaf,... *)
        while (size skWOTSlp < l') {
          (* Get the to-be-signed message/root and encode it *)
          root <- nth witness rootsntp (size skWOTSnt * l' + size skWOTSlp);
          em <- encode_msgWOTS root;
          
          skWOTS <- [];
          pkWOTS <- [];
          sigWOTS <- [];
          (* For each element of the WOTS-TW artifacts... *)
          while (size skWOTS < len) {
            (* Sample and store a skWOTS element *)
            ch_ele <$ ddgstblock;
            skWOTS <- rcons skWOTS ch_ele;
            
            (* Compute the corresponding signature and public elements *)
            i <- 0;
            while (i < w - 1) {
              ch_ele <@ OC.query(set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) chtype) 
                                                                (size skWOTSlp)) (size skWOTS)) i,
                                 val ch_ele);
              
              if (i = BaseW.val em.[size skWOTS]) {
                sigWOTS <- rcons sigWOTS ch_ele;
              }
              
              i <- i + 1;
            }
            
            pkWOTS <- rcons pkWOTS ch_ele;
          }
          
          (* Query the challenge oracle to compress the obtained WOTS-TW public key to the corresponding leaf  *)
          leaf <@ O.query(set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) pkcotype) (size skWOTSlp), 
                          flatten (map DigestBlock.val pkWOTS));

          pkWOTSlp <- rcons pkWOTSlp (DBLL.insubd pkWOTS);
          sigWOTSlp <- rcons sigWOTSlp (DBLL.insubd sigWOTS);
          leaveslp <- rcons leaveslp leaf;
        }

        
        nodes <- [];
        (* For each layer in the current tree, starting from the layer right above the leaves,... *)
        while (size nodes < h') {
          nodespl <- last leaveslp nodes;

          nodescl <- [];
          (* For each (to-be-computed) node in the currently considered layer,... *)
          while (size nodescl < nr_nodes (size nodes + 1)) {
            (* Get the left and right children *)
            lnode <- nth witness nodespl (2 * size nodescl);
            rnode <- nth witness nodespl (2 * size nodescl + 1);

            (* Query the family oracle on the concatenation of the children to obtain the node *)
            node <@ OC.query(set_thtbidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) trhtype) 
                                                    (size skWOTSlp)) 
                                         (size nodes + 1) (size nodescl), 
                             val lnode ++ val rnode);

            nodescl <- rcons nodescl node;
          }
          nodes <- rcons nodes nodescl;
        }  
        pkWOTSnt <- rcons pkWOTSnt pkWOTSlp;
        sigWOTSnt <- rcons sigWOTSnt sigWOTSlp;
        leavesnt <- rcons leavesnt leaveslp;
        rootsnt <- rcons rootsnt (nth witness (nth witness nodes (h' - 1)) 0); (* Root of current tree is the last computed/stored node *)
      }
      pkWOTStd <- rcons pkWOTStd pkWOTSnt;
      sigWOTStd <- rcons sigWOTStd sigWOTSnt;
      leavestd <- rcons leavestd leavesnt;
      rootstd <- rcons rootstd rootsnt;
    }
  }
  
  proc find(ps : pseed) : int * dgst = {
    var m : msgFLSLXMSSMTTW;
    var pk : pkFLSLXMSSMTTW;
    var sigWOTS, sigWOTS' : sigWOTS;
    var pkWOTS, pkWOTS' : pkWOTS;
    var ap, ap' : apFLXMSSTW;
    var sapl, sapl' : (sigWOTS * apFLXMSSTW) list;
    var sig : sigFLSLXMSSMTTW;
    var sigl : sigFLSLXMSSMTTW list; 
    var m' : msgFLSLXMSSMTTW;
    var sig' : sigFLSLXMSSMTTW;
    var idx' : index;
    var root, root' : dgstblock;
    var roots' : dgstblock list;
    var tidx, kpidx : int;
    var tkpidxs : (int * int) list;
    var leaf, leaf' : dgstblock;
    var leaves : dgstblock list;
    var tcfs : bool list; 
    var ffidx, tcidx : int;
    
    (* Sign adversary-chosen messages using computed leaves/signatures *)
    sigl <- [];
    while (size sigl < l) {
      m <- nth witness ml (size sigl);
      
      sapl <- [];
      (tidx, kpidx) <- (size sigl, 0);
      while (size sapl < d) {
        (tidx, kpidx) <- edivz tidx l';
        
        sigWOTS <- nth witness (nth witness (nth witness sigWOTStd (size sapl)) tidx) kpidx;
        
        leaves <- nth witness (nth witness leavestd (size sapl)) tidx;

        ap <- cons_ap_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) kpidx;

        sapl <- rcons sapl (sigWOTS, ap);
      }

      sig <- insubd sapl;
      sigl <- rcons sigl sig;
    }
    
    root <- nth witness (nth witness rootstd (d - 1)) 0; (* Root of hypertree is the last computed root *)
    
    (m', sig', idx') <@ A(O_THFC).forge((root, ps, ad), sigl);
    
    (tidx, kpidx) <- (val idx', 0);
    tkpidxs <- [];
    root' <- m';
    tcfs <- [];
    (* 
      For each WOTS-TW signature/authentication path pair in the forgery, check whether
      the leaf derived from the (public key corresponding to the) signature equals the
      corresponding leaf from the original tree. Assuming the public keys are different,
      this gives a collision. 
      Also keep track of the intermediate tree/keypair indices. 
    *)
    while (size tcfs < d) {
      (tidx, kpidx) <- edivz tidx l';
      
      (sigWOTS', ap') <- nth witness (val sig') (size tcfs);
      
      pkWOTS' <@ WOTS_TW_ES_NPRF.pkWOTS_from_sigWOTS(root', sigWOTS', ps, 
                                                     (set_kpidx (set_typeidx (set_ltidx ad (size tcfs) tidx) chtype) kpidx));
      
      leaf' <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad (size tcfs) tidx) pkcotype) kpidx) 
                   (flatten (map DigestBlock.val (val pkWOTS'))); 
      leaf <- nth witness (nth witness (nth witness leavestd (size tcfs)) tidx) kpidx;
      
      tcfs <- rcons tcfs (leaf' = leaf);
      
      root' <- val_ap_trh ap' kpidx leaf' ps (set_typeidx (set_ltidx ad (size tcfs) tidx) trhtype); 
            
      tkpidxs <- rcons tkpidxs (tidx, kpidx);
    }
    
    (* Get index of the first collision extractable from the forgery *)
    ffidx <- find ((=) true) tcfs;
    
    (* Get tree and key pair index corresponding to first collision *)    
    (tidx, kpidx) <- nth witness tkpidxs ffidx;
    
    (* Compute index in the challenge oracle's query list of the collision *)
    tcidx <- bigi predT (fun i => nr_trees i) 0 ffidx * l' + tidx * l' + kpidx; 
    
    (* Get root and WOTS-TW sigature forming a forgery *)
    pkWOTS' <- nth witness (nth witness (nth witness pkWOTStd (size tcfs)) tidx) kpidx; 
    
    return (tcidx, flatten (map DigestBlock.val (DBLL.val pkWOTS')));
  }
}.

module (R_SMDTTCRCTRH_EUFNAGCMA (A : Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF) : TRHC_TCR.Adv_SMDTTCRC) (O : TRHC_TCR.Oracle_SMDTTCR, OC : TRHC.Oracle_THFC) = {
  var ad : adrs
  var ml : msgFLSLXMSSMTTW list
  var skWOTStd : skWOTS list list list
  var pkWOTStd : pkWOTS list list list
  var sigWOTStd : sigWOTS list list list
  var leavestd : dgstblock list list list
  var nodestd : dgstblock list list list list
  var rootstd : dgstblock list list
    
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
  
  proc pick() : unit = {
    var m : msgFLSLXMSSMTTW;
    var em : emsgWOTS;
    var ch_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt, skWOTSntp : skWOTS list list;
    var pkWOTS : dgstblock list;
    var pkWOTSlp : pkWOTS list;
    var pkWOTSnt, pkWOTSntp : pkWOTS list list;
    var sigWOTS : dgstblock list;
    var sigWOTSlp : sigWOTS list;
    var sigWOTSnt, sigWOTSntp : sigWOTS list list;
    var leaf : dgstblock;
    var leaveslp : dgstblock list;
    var leavesnt, leavesntp : dgstblock list list;
    var root : dgstblock;
    var rootsnt, rootsntp : dgstblock list;
    var lnode, rnode, node : dgstblock;
    var nodespl, nodescl : dgstblock list;
    var nodes : dgstblock list list;
    var nodesnt : dgstblock list list list;
    var i : int;
    
    O_THFC.init(witness);
    
    ml <@ A(O_THFC).choose();
    
    ad <- adz;

    (* 
      Using the provided oracles, compute and store all the 
      WOTS-TW secret keys, WOTS-TW public keys, WOTS-TW signatures, 
      (inner tree) leaves, (inner tree) nodes, and (inner tree) roots.
    *)
    skWOTStd <- [];
    pkWOTStd <- [];
    sigWOTStd <- [];
    leavestd <- [];
    nodestd <- [];
    rootstd <- [];
    (* For each layer in the hypertree, starting from the bottom-most layer,... *)
    while (size skWOTStd < d) {
      skWOTSnt <- [];
      pkWOTSnt <- [];
      sigWOTSnt <- [];
      leavesnt <- [];
      nodesnt <- [];
      rootsnt <- [];
      rootsntp <- last ml rootstd;
      (* For each tree in the current layer, starting from the left-most tree,... *)
      while (size skWOTSnt < nr_trees (size skWOTStd)) {
        skWOTSlp <- [];
        pkWOTSlp <- [];
        sigWOTSlp <- [];
        leaveslp <- [];
        (* For each leaf of the current tree, starting from the left-most leaf,... *)
        while (size skWOTSlp < l') {
          (* Get the to-be-signed message/root and encode it *)
          root <- nth witness rootsntp (size skWOTSnt * l' + size skWOTSlp);
          em <- encode_msgWOTS root;
          
          skWOTS <- [];
          pkWOTS <- [];
          sigWOTS <- [];
          (* For each element of the WOTS-TW artifacts... *)
          while (size skWOTS < len) {
            (* Sample and store a skWOTS element *)
            ch_ele <$ ddgstblock;
            skWOTS <- rcons skWOTS ch_ele;
            
            (* Compute the corresponding signature and public elements *)
            i <- 0;
            while (i < w - 1) {
              ch_ele <@ OC.query(set_hidx (set_chidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) chtype) 
                                                                (size skWOTSlp)) (size skWOTS)) i,
                                 val ch_ele);
              
              if (i = BaseW.val em.[size skWOTS]) {
                sigWOTS <- rcons sigWOTS ch_ele;
              }
              
              i <- i + 1;
            }
            
            pkWOTS <- rcons pkWOTS ch_ele;
          }
          
          (* Query the collection oracle to compress the obtained WOTS-TW public key to the corresponding leaf *)
          leaf <@ OC.query(set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) pkcotype) (size skWOTSlp), 
                           flatten (map DigestBlock.val pkWOTS));

          pkWOTSlp <- rcons pkWOTSlp (DBLL.insubd pkWOTS);
          sigWOTSlp <- rcons sigWOTSlp (DBLL.insubd sigWOTS);
          leaveslp <- rcons leaveslp leaf;
        }

        
        nodes <- [];
        (* For each layer in the current tree, starting from the layer right above the leaves,... *)
        while (size nodes < h') {
          nodespl <- last leaveslp nodes;

          nodescl <- [];
          (* For each (to-be-computed) node in the currently considered layer,... *)
          while (size nodescl < nr_nodes (size nodes + 1)) {
            (* Get the left and right children *)
            lnode <- nth witness nodespl (2 * size nodescl);
            rnode <- nth witness nodespl (2 * size nodescl + 1);

            (* Query the challenge oracle on the concatenation of the children to obtain the node *)
            node <@ O.query(set_thtbidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) trhtype) (size skWOTSlp)) 
                                        (size nodes + 1) (size nodescl), 
                             val lnode ++ val rnode);

            nodescl <- rcons nodescl node;
          }
          nodes <- rcons nodes nodescl;
        }  
        pkWOTSnt <- rcons pkWOTSnt pkWOTSlp;
        sigWOTSnt <- rcons sigWOTSnt sigWOTSlp;
        leavesnt <- rcons leavesnt leaveslp;
        nodesnt <- rcons nodesnt nodes;
        rootsnt <- rcons rootsnt (nth witness (nth witness nodes (h' - 1)) 0); (* Root of current tree is the last computed/stored node *)
      }
      pkWOTStd <- rcons pkWOTStd pkWOTSnt;
      sigWOTStd <- rcons sigWOTStd sigWOTSnt;
      leavestd <- rcons leavestd leavesnt;
      nodestd <- rcons nodestd nodesnt;
      rootstd <- rcons rootstd rootsnt;
    }
  }
    
  proc find(ps : pseed) : int * dgst = {
    var m : msgFLSLXMSSMTTW;
    var pk : pkFLSLXMSSMTTW;
    var sigWOTS, sigWOTS' : sigWOTS;
    var pkWOTS, pkWOTS' : pkWOTS;
    var ap, ap' : apFLXMSSTW;
    var sapl, sapl' : (sigWOTS * apFLXMSSTW) list;
    var sig : sigFLSLXMSSMTTW;
    var sigl : sigFLSLXMSSMTTW list; 
    var m' : msgFLSLXMSSMTTW;
    var sig' : sigFLSLXMSSMTTW;
    var idx' : index;
    var root, root' : dgstblock;
    var tidx, kpidx, hidx, bidx : int;
    var tkpidxs : (int * int) list;
    var leaf, leaf' : dgstblock;
    var leaves, leaves' : dgstblock list;
    var tcfs : bool list; 
    var ffidx, tcidx : int;
    var cr;
    var cnode : dgst;
    
    (* Sign adversary-chosen messages using computed leaves/signatures *)
    sigl <- [];
    while (size sigl < l) {
      m <- nth witness ml (size sigl);
      
      sapl <- [];
      (tidx, kpidx) <- (size sigl, 0);
      while (size sapl < d) {
        (tidx, kpidx) <- edivz tidx l';
      
        sigWOTS <- nth witness (nth witness (nth witness sigWOTStd (size sapl)) tidx) kpidx;
        
        leaves <- nth witness (nth witness leavestd (size sapl)) tidx;

        ap <- cons_ap_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) kpidx;

        sapl <- rcons sapl (sigWOTS, ap);
      }

      sig <- insubd sapl;
      sigl <- rcons sigl sig;
    }
    
    root <- nth witness (nth witness rootstd (d - 1)) 0; (* Root of hypertree is the last computed root *)
    
    (m', sig', idx') <@ A(O_THFC).forge((root, ps, ad), sigl);
    
    (tidx, kpidx) <- (val idx', 0);
    tkpidxs <- [];
    root' <- m';
    leaves' <- [];
    tcfs <- [];
    (* 
      For each WOTS-TW signature/authentication path pair in the forgery, check whether
      the root computed from the (public key corresponding to the) signature and the authentication 
      path equals the corresponding original root. Assuming the starting leafs are different,
      this allows for the extraction of a collision. 
      Also keep track of the intermediate leaves and tree/keypair indices. 
    *)
    while (size tcfs < d) {
      (tidx, kpidx) <- edivz tidx l';
            
      (sigWOTS', ap') <- nth witness (val sig') (size tcfs);
      
      pkWOTS' <@ WOTS_TW_ES_NPRF.pkWOTS_from_sigWOTS(root', sigWOTS', ps, 
                                                     (set_kpidx (set_typeidx (set_ltidx ad (size tcfs) tidx) chtype) kpidx));
      
      leaf' <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad (size tcfs) tidx) pkcotype) kpidx) 
                    (flatten (map DigestBlock.val (val pkWOTS')));
      
      root' <- val_ap_trh ap' kpidx leaf' ps (set_typeidx (set_ltidx ad (size tcfs) tidx) trhtype); 
      root <- nth witness (nth witness rootstd (size tcfs)) tidx;
      
      tcfs <- rcons tcfs (root' = root);
      
      leaves' <- rcons leaves' leaf';  
      tkpidxs <- rcons tkpidxs (tidx, kpidx);
    }
    
    (* Get index of the first authentication path (in the forgery) that allows the extraction of a collision *)
    ffidx <- find ((=) true) tcfs;
    
    (* Get authentication path and leaf that allow to extract a collision *)
    (sigWOTS', ap') <- nth witness (val sig') ffidx;
    leaf' <- nth witness leaves' ffidx; 
    
    (* Get tree and key pair index corresponding to first collision *)    
    (tidx, kpidx) <- nth witness tkpidxs ffidx;
    
    (* Get leaves of the tree in which collision occurs *)
    leaves <- nth witness (nth witness leavestd ffidx) tidx;
    
    (* Extract collision information from considered (inner) tree *)
    cr <- extract_coll_bt_ap_trh ps (set_ltidx (set_typeidx ad trhtype) ffidx tidx)
                                 (list2tree leaves) (val ap') (rev (int2bs h' kpidx)) leaf' h' 0; 
    
    (* Get collision and height/breadth indices *)
    cnode <- (val cr.`3) ++ (val cr.`4);
    (hidx, bidx) <- cr.`5;
    
    (* Compute index in the challenge oracle's query list of the collision *)
    tcidx <- bigi predT (fun i => nr_trees i) 0 ffidx * (2 ^ h' - 1) + tidx * (2 ^ h' - 1) + 
             bigi predT (fun i => nr_nodes i) 1 hidx + bidx; 
    
    return (tcidx, cnode);
  }
}.


section Proof_EUF_NAGCMA_FL_SL_XMSS_MT_TW_ES_NPRF.

declare module A <: Adv_EUFNAGCMA_FLSLXMSSMTTWESNPRF {-O_MEUFGCMA_WOTSTWESNPRF, -PKCOC_TCR.O_SMDTTCR_Default, -PKCOC_TCR.O_SMDTTCR_Default, -TRHC_TCR.O_SMDTTCR_Default, -TRHC_TCR.O_SMDTTCR_Default, -FC_UD.O_SMDTUD_Default, -FC_TCR.O_SMDTTCR_Default, -FC_PRE.O_SMDTPRE_Default, -PKCOC.O_THFC_Default, -FC.O_THFC_Default, -TRHC.O_THFC_Default, -R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA, -R_SMDTTCRCPKCO_EUFNAGCMA, -R_SMDTTCRCTRH_EUFNAGCMA, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_SMDTPREC_Game4WOTSTWES}.

(*
Adversary assumptions:
size ml = l /\ 
all (fun (ad : adrs) =>   get_typeidx ad <> chtype 
                      /\ get_typeidx ad <> pkcotype
                      /\ get_typeidx ad <> trhtype) adsOC
*)
declare axiom A_choose_ll (OC <: Oracle_THFC{-A}) : 
  islossless OC.query => islossless A(OC).choose.

declare axiom A_forge_ll (OC <: Oracle_THFC{-A}) : 
  islossless A(OC).forge.
    
  
local module EUF_NAGCMA_FLSLXMSSMTTWESNPRF_V = {
  var valid_WOTSTWES, valid_TCRPKCO, valid_TCRTRH : bool
  
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
    var em : emsgWOTS;
    var em_ele : int;
    var skWOTS_ele : dgstblock;
    var skWOTS : dgstblock list;
    var skWOTSlp : skWOTS list;
    var skWOTSnt, skWOTSntp : skWOTS list list;
    var skWOTStd : skWOTS list list list;
    var pkWOTS_ele : dgstblock;
    var pkWOTS : dgstblock list;
    var pkWOTSlp : pkWOTS list;
    var pkWOTSnt, pkWOTSntp : pkWOTS list list;
    var pkWOTStd : pkWOTS list list list;
    var sigWOTS_ele : dgstblock;
    var sigWOTS : dgstblock list;
    var sigWOTSlp : sigWOTS list;
    var sigWOTSnt, sigWOTSntp : sigWOTS list list;
    var sigWOTStd : sigWOTS list list list;
    var leaf, leaf' : dgstblock;
    var leaves, leaves', leaveslp : dgstblock list;
    var leavesnt, leavesntp : dgstblock list list;
    var leavestd : dgstblock list list list;
    var root, root' : dgstblock;
    var rootsnt, rootsntp : dgstblock list;
    var rootstd : dgstblock list list;
    var sapl : (sigWOTS * apFLXMSSTW) list;
    var ap, ap' : apFLXMSSTW;
    var sigWOTS', sigWOTSins : sigWOTS;
    var pkWOTS', pkWOTSins : pkWOTS;
    var tidx, kpidx : int;
    var tkpidxs : (int * int) list;
    var forgeryfs, tclfs, tcrfs : bool list;
    
        
    ad <- adz;
    ps <$ dpseed;

    O_THFC_Default.init(ps);

    ml <@ A(O_THFC_Default).choose();

    (* (pk, sk) <@ FL_SL_XMSS_MT_TW_ES_NPRF.keygen(ps, ad); *)
    (* 
      Using the provided oracles, compute and store all the 
      WOTS-TW secret keys, WOTS-TW public keys, WOTS-TW signatures, 
      (inner tree) leaves, and (inner tree) roots.
    *)
    skWOTStd <- [];
    pkWOTStd <- [];
    sigWOTStd <- [];
    leavestd <- [];
    rootstd <- [];
    (* For each layer in the hypertree, starting from the bottom-most layer,... *)
    while (size skWOTStd < d) {
      skWOTSnt <- [];
      pkWOTSnt <- [];
      sigWOTSnt <- [];
      leavesnt <- [];
      rootsnt <- [];
      rootsntp <- last ml rootstd;
      (* For each tree in the current layer, starting from the left-most tree,... *)
      while (size skWOTSnt < nr_trees (size skWOTStd)) {
        skWOTSlp <- [];
        pkWOTSlp <- [];
        sigWOTSlp <- [];
        leaveslp <- [];
        (* For each leaf of the current tree, starting from the left-most leaf,... *)
        while (size skWOTSlp < l') {
          (* Get the to-be-signed message/root and encode it *)
          root <- nth witness rootsntp (size skWOTSnt * l' + size skWOTSlp);
          em <- encode_msgWOTS root;
          
          skWOTS <- [];
          pkWOTS <- [];
          sigWOTS <- [];
          (* For each element of the WOTS-TW artifacts... *)
          while (size skWOTS < len) {
            em_ele <- BaseW.val em.[size skWOTS];
            
            (* Sample a skWOTS element *)
            skWOTS_ele <$ ddgstblock;
            
            sigWOTS_ele <- cf ps (set_chidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) chtype) 
                                                       (size skWOTSlp)) (size skWOTS)) 
                              0 em_ele (val skWOTS_ele);
            
            pkWOTS_ele <- cf ps (set_chidx (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) chtype) (size skWOTSlp)) (size skWOTS)) 
                             em_ele (w - 1 - em_ele) (val sigWOTS_ele);
            
            skWOTS <- rcons skWOTS skWOTS_ele;
            pkWOTS <- rcons pkWOTS pkWOTS_ele;
            sigWOTS <- rcons sigWOTS sigWOTS_ele;
          }
          
          leaf <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) pkcotype) (size skWOTSlp)) (flatten (map DigestBlock.val pkWOTS));
          
          skWOTSlp <- rcons skWOTSlp (DBLL.insubd skWOTS);
          pkWOTSlp <- rcons pkWOTSlp (DBLL.insubd pkWOTS);
          sigWOTSlp <- rcons sigWOTSlp (DBLL.insubd sigWOTS);
          leaveslp <- rcons leaveslp leaf;
        }

        root <- val_bt_trh ps (set_typeidx (set_ltidx ad (size skWOTStd) (size skWOTSnt)) trhtype)
                           (list2tree leaveslp) h' 0;
        
        skWOTSnt <- rcons skWOTSnt skWOTSlp;
        pkWOTSnt <- rcons pkWOTSnt pkWOTSlp;
        sigWOTSnt <- rcons sigWOTSnt sigWOTSlp;
        leavesnt <- rcons leavesnt leaveslp;
        rootsnt <- rcons rootsnt root;
      }
      skWOTStd <- rcons skWOTStd skWOTSnt;
      pkWOTStd <- rcons pkWOTStd pkWOTSnt;
      sigWOTStd <- rcons sigWOTStd sigWOTSnt;
      leavestd <- rcons leavestd leavesnt;
      rootstd <- rcons rootstd rootsnt;
    }
    
    root <- nth witness (nth witness rootstd (d - 1)) 0; (* Root of hypertree is the last computed root *)
    pk <- (root, ps, ad);
    
    sigl <- [];
    while (size sigl < l) {
      m <- nth witness ml (size sigl);
      
      sapl <- [];
      (tidx, kpidx) <- (size sigl, 0);
      while (size sapl < d) {
        (tidx, kpidx) <- edivz tidx l';
                
        sigWOTSins <- nth witness (nth witness (nth witness sigWOTStd (size sapl)) tidx) kpidx;
        
        leaves <- nth witness (nth witness leavestd (size sapl)) tidx;

        ap <- cons_ap_trh ps (set_typeidx (set_ltidx ad (size sapl) tidx) trhtype) (list2tree leaves) kpidx;

        sapl <- rcons sapl (sigWOTSins, ap);
      }

      sig <- insubd sapl;
      sigl <- rcons sigl sig;
    }
    
    (m', sig', idx') <@ A(O_THFC_Default).forge(pk, sigl);

    is_valid <@ FL_SL_XMSS_MT_TW_ES_NPRF.verify(pk, m', sig', idx');

    (*
    is_fresh <- ! m' \in take (size sigl) ml;
    *)
    is_fresh <- m' <> nth witness ml (val idx'); 
    
    (* Additional checks *)
    (tidx, kpidx) <- (val idx', 0);
    tkpidxs <- [];
    root' <- m';
    leaves' <- [];
    forgeryfs <- [];
    tclfs <- [];
    tcrfs <- [];
    (* 
      For each WOTS-TW signature/authentication path pair in the forgery, check whether
      the root computed from the (public key corresponding to the) signature and the authentication 
      path equals the corresponding original root. Assuming the starting leafs are different,
      this allows for the extraction of a collision. 
      Also keep track of the intermediate leaves and tree/keypair indices. 
    *)
    while (size forgeryfs < d) {
      (tidx, kpidx) <- edivz tidx l';
            
      (sigWOTS', ap') <- nth witness (val sig') (size forgeryfs);
      
      pkWOTS' <@ WOTS_TW_ES_NPRF.pkWOTS_from_sigWOTS(root', sigWOTS', ps, 
                                                     (set_kpidx (set_typeidx (set_ltidx ad (size forgeryfs) tidx) chtype) kpidx));
      pkWOTSins <- nth witness (nth witness (nth witness pkWOTStd (size forgeryfs)) tidx) kpidx;
      forgeryfs <- rcons forgeryfs (pkWOTS' = pkWOTSins);
      
      leaf' <- pkco ps (set_kpidx (set_typeidx (set_ltidx ad (size forgeryfs) tidx) pkcotype) kpidx) 
                    (flatten (map DigestBlock.val (val pkWOTS')));
      leaf <- nth witness (nth witness (nth witness leavestd (size forgeryfs)) tidx) kpidx;
      tclfs <- rcons tclfs (leaf' = leaf);
      
      root' <- val_ap_trh ap' kpidx leaf' ps (set_typeidx (set_ltidx ad (size forgeryfs) tidx) trhtype); 
      root <- nth witness (nth witness rootstd (size forgeryfs)) tidx;
      
      tcrfs <- rcons tcrfs (root' = root);
    }
    
    valid_WOTSTWES <- has ((=) true) forgeryfs;
    valid_TCRPKCO <- has ((=) true) tclfs;
    valid_TCRTRH <- has ((=) true) tcrfs;
    
    return is_valid /\ is_fresh; 
  }
}.

local equiv Eqv_EUFNAGCMA_FLSLXMSSMTTWESNPRF_Orig_V :
  EUF_NAGCMA_FLSLXMSSMTTWESNPRF(A, O_THFC_Default).main ~ EUF_NAGCMA_FLSLXMSSMTTWESNPRF_V.main :
    ={glob A} ==> ={res}.
proof.
proc.
seq 7 14 : (={glob A, sigl, pk, ml}); last first. 
+ wp.
  while{2} (true) (d - size forgeryfs{2}).
  - move=> ? z.
    inline *.
    wp.
    while (true) (len - size pkWOTS0).
    - move=> z'.
      by wp; skip => />; smt(size_rcons).
    by wp; skip => />; smt(size_rcons).
  wp. 
  call (: true) => /=; 1: by sim.
  call (: true).
  by skip => />; smt(ge1_d).
inline{1} 5.
seq 14 12 : (   ={glob A, ad, ps, ml, root, skWOTStd, pk}
             /\ pk{1} = (root, ps, ad){1}
             /\ sk{1} = (skWOTStd, ps ,ad){1}
             /\ (forall (i j u v : int), 
                   0 <= i < d => 0 <= j < nr_trees i => 0 <= u < l' => 0 <= v < len =>
                     nth witness (val (nth witness (nth witness (nth witness pkWOTStd{2} i) j) u)) v
                     =
                     cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} i j) chtype) u) v) 0 (w - 1) 
                     (val (nth witness (val (nth witness (nth witness (nth witness skWOTStd{2} i) j) u)) v)))
             /\ (forall (i j u : int),
                   0 <= i < d => 0 <= j < nr_trees i => 0 <= u < l' =>
                     nth witness (nth witness (nth witness leavestd{2} i) j) u
                     =
                     pkco ps{2} (set_kpidx (set_typeidx (set_ltidx ad{2} i j) pkcotype) u) 
                     (flatten (map DigestBlock.val (val (nth witness (nth witness (nth witness pkWOTStd{2} i) j) u)))))
             /\ (forall (i j : int),
                   0 <= i < d => 0 <= j < nr_trees i =>
                     nth witness (nth witness rootstd{2} i) j
                     =
                     val_bt_trh ps{2} (set_typeidx (set_ltidx ad{2} i j) trhtype)
                                (list2tree (nth witness (nth witness leavestd{2} i) j)) h' 0)
             /\ (forall (i j u v : int),
                   0 <= i < d => 0 <= j < nr_trees i => 0 <= u < l' => 0 <= v < len => 
                     nth witness (val (nth witness (nth witness (nth witness sigWOTStd{2} i) j) u)) v
                     =
                     cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} i j) chtype) u) v) 0 
                     (BaseW.val (encode_msgWOTS 
                                   (if i = 0
                                    then nth witness ml{2} (j * l' + u)
                                    else nth witness (nth witness rootstd{2} (i - 1)) (j * l' + u))).[v])
                     (val (nth witness (val (nth witness (nth witness (nth witness skWOTStd{2} i) j) u)) v)))
             /\ (forall (i j : int), 
                   0 <= i < d => 0 <= j < nr_trees i =>
                     size (nth witness (nth witness leavestd{2} i) j) = l')).
+ inline{1} 10.
  wp => /=. 
  while{1} (leaves0{1} 
            = 
            mkseq (fun (i : int) =>
              pkco ps1{1} (set_kpidx (set_typeidx ad1{1} pkcotype) i) 
                   (flatten (map DigestBlock.val (mkseq (fun (j : int) =>
                      cf ps1{1} (set_chidx (set_kpidx (set_typeidx ad1{1} chtype) i) j) 
                         0 (w - 1) (val (nth witness (val (nth witness skWOTSl{1} i)) j))) len)))) (size leaves0{1})
            /\ 0 <= size leaves0{1} <= l')
           (l' - size leaves0{1}).
  - move=> _ z.
    inline *.
    wp => /=.
    while (pkWOTS0
           =
           mkseq (fun (j : int) =>
             cf ps2 (set_chidx ad2 j) 0 (w - 1) (val (nth witness (val skWOTS1) j))) (size pkWOTS0)
           /\ 0 <= size pkWOTS0 <= len)
          (len - size pkWOTS0).
    - move=> z'.
      by wp; skip => />; smt(size_rcons mkseqS).
    wp; skip => /> *.
    split => [| pkWOTS]; 1: by rewrite mkseq0 /=; smt(ge2_len).
    split => [/# | /lezNgt gelen_szpk *].
    by rewrite insubdK 1:/# size_rcons ?mkseqS 1://; smt(ge2_len mkseqS).
  wp => /=.
  while (   ={skWOTStd}
         /\ valid_xadrs ad{2} 
         /\ (forall (i j u v : int), 
               0 <= i < size pkWOTStd{2} => 0 <= j < nr_trees i => 0 <= u < l' => 0 <= v < len =>
                 nth witness (val (nth witness (nth witness (nth witness pkWOTStd{2} i) j) u)) v
                 =
                 cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} i j) chtype) u) v) 0 (w - 1) 
                 (val (nth witness (val (nth witness (nth witness (nth witness skWOTStd{2} i) j) u)) v)))
         /\ (forall (i j u : int),
               0 <= i < size leavestd{2} => 0 <= j < nr_trees i => 0 <= u < l' =>
                 nth witness (nth witness (nth witness leavestd{2} i) j) u
                 =
                 pkco ps{2} (set_kpidx (set_typeidx (set_ltidx ad{2} i j) pkcotype) u) 
                 (flatten (map DigestBlock.val (val (nth witness (nth witness (nth witness pkWOTStd{2} i) j) u)))))
         /\ (forall (i j : int),
               0 <= i < size rootstd{2} => 0 <= j < nr_trees i =>
                 nth witness (nth witness rootstd{2} i) j
                 =
                 val_bt_trh ps{2} (set_typeidx (set_ltidx ad{2} i j) trhtype)
                            (list2tree (nth witness (nth witness leavestd{2} i) j)) h' 0)
         /\ (forall (i j u v : int),
               0 <= i < size sigWOTStd{2} => 0 <= j < nr_trees i => 0 <= u < l' => 0 <= v < len => 
                 nth witness (val (nth witness (nth witness (nth witness sigWOTStd{2} i) j) u)) v
                 =
                 cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} i j) chtype) u) v) 0 
                 (BaseW.val (encode_msgWOTS 
                               (if i = 0
                                then nth witness ml{2} (j * l' + u)
                                else nth witness (nth witness rootstd{2} (i - 1)) (j * l' + u))).[v])
                 (val (nth witness (val (nth witness (nth witness (nth witness skWOTStd{2} i) j) u)) v)))
         /\ (forall (i j : int), 
               0 <= i < size leavestd{2} => 0 <= j < nr_trees i =>
                 size (nth witness (nth witness leavestd{2} i) j) = l')
         /\ 0 <= size skWOTStd{2} <= d
         /\ size skWOTStd{2} = size pkWOTStd{2}
         /\ size skWOTStd{2} = size sigWOTStd{2}
         /\ size skWOTStd{2} = size leavestd{2}
         /\ size skWOTStd{2} = size rootstd{2}).
  - wp.
    while (   ={skWOTStd, skWOTSnt}
           /\ valid_xadrs ad{2}
           /\ rootsntp{2} = last ml{2} rootstd{2}
           /\ (forall (j u v : int), 
                 0 <= j < size pkWOTSnt{2} => 0 <= u < l' => 0 <= v < len =>
                   nth witness (val (nth witness (nth witness pkWOTSnt{2} j) u)) v
                   =
                   cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} (size pkWOTStd{2}) j) chtype) u) v) 0 (w - 1) 
                   (val (nth witness (val (nth witness (nth witness skWOTSnt{2} j) u)) v)))
           /\ (forall (j u : int),
                 0 <= j < size leavesnt{2} => 0 <= u < l' =>
                   nth witness (nth witness leavesnt{2} j) u
                   =
                   pkco ps{2} (set_kpidx (set_typeidx (set_ltidx ad{2} (size leavestd{2}) j) pkcotype) u) 
                   (flatten (map DigestBlock.val (val (nth witness (nth witness pkWOTSnt{2} j) u)))))
           /\ (forall (j : int),
                 0 <= j < size rootsnt{2} =>
                   nth witness rootsnt{2} j
                   =
                   val_bt_trh ps{2} (set_typeidx (set_ltidx ad{2} (size rootstd{2}) j) trhtype)
                              (list2tree (nth witness leavesnt{2} j)) h' 0)
           /\ (forall (j u v : int),
                 0 <= j < size sigWOTSnt{2} => 0 <= u < l' => 0 <= v < len => 
                   nth witness (val (nth witness (nth witness sigWOTSnt{2} j) u)) v
                   =
                   cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} (size sigWOTStd{2}) j) chtype) u) v) 0 
                   (BaseW.val (encode_msgWOTS 
                                 (if size sigWOTStd{2} = 0
                                  then nth witness ml{2} (j * l' + u)
                                  else nth witness (nth witness rootstd{2} (size sigWOTStd{2} - 1)) (j * l' + u))).[v])
                   (val (nth witness (val (nth witness (nth witness skWOTSnt{2} j) u)) v)))
           /\ (forall (j : int), 
                 0 <= j < size leavesnt{2} =>
                   size (nth witness leavesnt{2} j) = l')
           /\ 0 <= size skWOTSnt{2} <= nr_trees (size skWOTStd{2})
           /\ size skWOTSnt{2} = size pkWOTSnt{2}
           /\ size skWOTSnt{2} = size sigWOTSnt{2}
           /\ size skWOTSnt{2} = size leavesnt{2}
           /\ size skWOTSnt{2} = size rootsnt{2}
           /\ 0 <= size skWOTStd{2} < d
           /\ size skWOTStd{2} = size pkWOTStd{2}
           /\ size skWOTStd{2} = size sigWOTStd{2}
           /\ size skWOTStd{2} = size leavestd{2}
           /\ size skWOTStd{2} = size rootstd{2}).
    * wp.
      while (   ={skWOTStd, skWOTSnt, skWOTSlp}
             /\ valid_xadrs ad{2}
             /\ rootsntp{2} = last ml{2} rootstd{2}
             /\ (forall (u v : int), 
                   0 <= u < size pkWOTSlp{2} => 0 <= v < len =>
                     nth witness (val (nth witness pkWOTSlp{2} u)) v
                     =
                     cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} (size pkWOTStd{2}) (size pkWOTSnt{2})) chtype) u) v) 0 (w - 1) 
                     (val (nth witness (val (nth witness skWOTSlp{2} u)) v)))
             /\ (forall (u : int),
                   0 <= u < size leaveslp{2} =>
                     nth witness leaveslp{2} u
                     =
                     pkco ps{2} (set_kpidx (set_typeidx (set_ltidx ad{2} (size leavestd{2}) (size leavesnt{2})) pkcotype) u) 
                     (flatten (map DigestBlock.val (val (nth witness pkWOTSlp{2} u)))))
             /\ (forall (u v : int),
                   0 <= u < size sigWOTSlp{2} => 0 <= v < len => 
                     nth witness (val (nth witness sigWOTSlp{2} u)) v
                     =
                     cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} (size sigWOTStd{2}) (size sigWOTSnt{2})) chtype) u) v) 0 
                     (BaseW.val (encode_msgWOTS 
                                   (if size sigWOTStd{2} = 0
                                    then nth witness ml{2} (size sigWOTSnt{2} * l' + u)
                                    else nth witness (nth witness rootstd{2} (size sigWOTStd{2} - 1)) (size sigWOTSnt{2} * l' + u))).[v])
                     (val (nth witness (val (nth witness skWOTSlp{2} u)) v)))
             /\ 0 <= size skWOTSlp{2} <= l'
             /\ size skWOTSlp{2} = size pkWOTSlp{2}
             /\ size skWOTSlp{2} = size sigWOTSlp{2}
             /\ size skWOTSlp{2} = size leaveslp{2}
             /\ 0 <= size skWOTSnt{2} < nr_trees (size skWOTStd{2})
             /\ size skWOTSnt{2} = size pkWOTSnt{2}
             /\ size skWOTSnt{2} = size sigWOTSnt{2}
             /\ size skWOTSnt{2} = size leavesnt{2}
             /\ size skWOTSnt{2} = size rootsnt{2}
             /\ 0 <= size skWOTStd{2} < d
             /\ size skWOTStd{2} = size pkWOTStd{2}
             /\ size skWOTStd{2} = size sigWOTStd{2}
             /\ size skWOTStd{2} = size leavestd{2}
             /\ size skWOTStd{2} = size rootstd{2}).
      + wp.
        while (   ={skWOTStd, skWOTSnt, skWOTSlp, skWOTS}
               /\ valid_xadrs ad{2}
               /\ em{2} = encode_msgWOTS (nth witness (last ml{2} rootstd{2}) (size skWOTSnt{2} * l' + size skWOTSlp{2}))
               /\ (forall (v : int), 
                     0 <= v < size pkWOTS{2} =>
                       nth witness pkWOTS{2} v
                       =
                       cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} (size pkWOTStd{2}) (size pkWOTSnt{2})) chtype) (size pkWOTSlp{2})) v) 0 (w - 1)
                       (val (nth witness skWOTS{2} v)))
               /\ (forall (v : int),
                     0 <= v < size sigWOTS{2} => 
                       nth witness sigWOTS{2} v
                       =
                       cf ps{2} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad{2} (size sigWOTStd{2}) (size sigWOTSnt{2})) chtype) (size sigWOTSlp{2})) v) 0 
                       (BaseW.val (encode_msgWOTS 
                                     (if size sigWOTStd{2} = 0
                                      then nth witness ml{2} (size sigWOTSnt{2} * l' + size sigWOTSlp{2})
                                      else nth witness (nth witness rootstd{2} (size sigWOTStd{2} - 1)) (size sigWOTSnt{2} * l' + size sigWOTSlp{2}))).[v])
                       (val (nth witness skWOTS{2} v)))
               /\ 0 <= size skWOTS{2} <= len
               /\ size skWOTS{2} = size pkWOTS{2}
               /\ size skWOTS{2} = size sigWOTS{2}
               /\ 0 <= size skWOTSlp{2} < l'
               /\ size skWOTSlp{2} = size pkWOTSlp{2}
               /\ size skWOTSlp{2} = size sigWOTSlp{2}
               /\ size skWOTSlp{2} = size leaveslp{2}
               /\ 0 <= size skWOTSnt{2} < nr_trees (size skWOTStd{2})
               /\ size skWOTSnt{2} = size pkWOTSnt{2}
               /\ size skWOTSnt{2} = size sigWOTSnt{2}
               /\ size skWOTSnt{2} = size leavesnt{2}
               /\ size skWOTSnt{2} = size rootsnt{2}
               /\ 0 <= size skWOTStd{2} < d
               /\ size skWOTStd{2} = size pkWOTStd{2}
               /\ size skWOTStd{2} = size sigWOTStd{2}
               /\ size skWOTStd{2} = size leavestd{2}
               /\ size skWOTStd{2} = size rootstd{2}).
        - wp; rnd; wp; skip => |> &2 valad nthpk nthsig ge0_szsk _ eqszsp eqszss ge0_szsklp 
                                     ltlp_szsklp eqszlpsp eqszlpss eqszlpsl ge0_szsknt 
                                     ltnt_szsknt eqszntsp eqszntss eqszntsl eqszntsr 
                                     ge0_szsktd ltd_szskts eqsztdsp eqsztdss eqsztdsl 
                                     eqsztdsr ltlen_szsk skele skelein.
          rewrite ?size_rcons; split => [v ge0_v ltszpk1_v|].
          * rewrite 2!nth_rcons; case (v = size pkWOTS{2}) => [eqsz | /#].
            rewrite eqsz eqszsp /= eq_sym.
            pose emt := encode_msgWOTS _.
            rewrite (: w - 1 = val emt.[size pkWOTS{2}] + (w - 1 - val emt.[size pkWOTS{2}])) 1:/# /cf.
            rewrite ch_comp 2:valP //=; 2..4: smt(BaseW.valP val_w).
            - by apply validxadrs_validwadrs_setallch => // /#.
            by rewrite eqsztdsp eqszntsp eqszlpsp; congr; ring.
          split => [v ge0_v ltszsig1_v | /#].
          rewrite 2!nth_rcons eqszss; case (v = size sigWOTS{2}) => [eqsz | /#].
          rewrite eqsz /= eq_sym eqsztdss eqszntss eqszlpss.
          do 4! congr.
          by rewrite (last_nth witness) /= -eqsztdsr eqsztdss /#.
        wp; skip => |> &2 valad nthpks nthlfs nthsigs ge0_szsklp ltlp_szsklp eqszlpsp 
                          eqszlpss eqszlpsl ge0_szsknt ltnt_szsknt eqszntsp eqszntss 
                          eqszntsl eqszntsr ge0_szsktd ltd_szskts eqsztdsp eqsztdss 
                          eqsztdsl eqsztdsr ltl_szsklp.
        split => [| pk sig sk /lezNgt gelen_szsk _]; 1: smt(ge2_len).
        move=> nthpkp nthsigp ge0_szsk lelen_szsk eqszspp eqszssp.
        split => [u v |].
        - rewrite size_rcons => ge0_u ltszpk1_u ge0_v ltlen_v. 
          rewrite 2!nth_rcons eqszlpsp; case (u = size pkWOTSlp{2}) => [eqsz | /#].
          by rewrite eqsz /= ?insubdK // /#.
        split => [u |].
        - rewrite size_rcons => ge0_u ltszlp1_u. 
          rewrite 2!nth_rcons -eqszlpsp eqszlpsl; case (u = size leaveslp{2}) => [eqsz | /#].
          by rewrite eqsz /= insubdK // /#.
        split => [u v |]; 2: smt(size_rcons).
        rewrite size_rcons => ge0_u ltszsig1_u ge0_v ltlen_v. 
        rewrite 2!nth_rcons ?eqszlpss; case (u = size sigWOTSlp{2}) => [eqsz | /#].
        by rewrite eqsz /= ?insubdK // /#.
      wp; skip => |> &2 valad nthpks nthlfs nthrs nthsigs nthszlfs ge0_szsknt lent_szsknt eqszntsp 
                        eqszntss eqszntsl eqszntsr ge0_szsktd ltd_szsktd eqsztdsp eqsztdss 
                        eqsztdsl eqsztdsr ltnrt_szskts.
      split => [| lfs pks sigs sks /lezNgt gelp_szsks _]; 1: by smt(ge1_lp).
      move=> nthpkp nthlfp nthsigp ge0_szsks lelp_szsks eqszspp eqszssp eqszslp.
      do 4! (split; 1: smt(ge1_d ge1_lp nth_rcons size_rcons)). 
      by split; smt(ge1_d ge1_lp nth_rcons size_rcons).
    wp; skip => |> &2 valad nthpk nthlf nthrt nthsig sznthlf ge0_szsk _ eqszpk eqszsig eqszlf eqszrt ltd_szsk.
    split => [|lfs pks rts sigs sks /lezNgt genrt_szsk _].
    - by rewrite /nr_trees expr_ge0 /#.
    move=> nthpkp nthlfp nthrtp nthsigp sznthlfp ge0_szskp lenrt_szsk eqszpkp eqszsigp eqszlfp eqszrtp.
    have eqnrt_szsk : size sks = nr_trees (size skWOTStd{2}) by smt().
    rewrite ?size_rcons -andbA; split => [i j u v *|].
    - by rewrite 2!nth_rcons /#.
    split => [i j u *|].
    - by rewrite 2!nth_rcons /#.
    split => [i j *|].
    - by rewrite 2!nth_rcons /#.
    split => [i j u v *|].
    - rewrite 3!nth_rcons.
      case (i = size sigWOTStd{2}) => [eqsz | neqsz].
      * by rewrite eqsz eqszsig /= nthsigp // /#.
      rewrite (: i < size sigWOTStd{2}) 1:/# /=.
      by rewrite nthsig // /#.
    split => [i j *| /#].
    by rewrite nth_rcons /#.
  wp.
  call (: ={O_THFC_Default.pp}); 1: by sim.
  inline *.
  wp; rnd; wp; skip => |> ps psin ml; rewrite valx_adz /=. 
  split => [| lfs pks rs sigs sks /lezNgt ged_szsks _]; 1: smt(ge1_d).
  move => nthpks nthlfs nthrs nthsigs nthszlfs ge0_szsknt lent_szsknt 
          eqszntsp eqszntss eqszntsl eqszntsr.
  split => [| lfslp]; 1: smt(ge1_lp mkseq0). 
  split => [/#| /lezNgt gelp_szlfslp lfslpval ge0_szlfslp lelp_szlfslp].
  split; first rewrite -andaE; split => //.
  - rewrite nthrs; 1,2: smt(ge1_d expr_gt0).
    do 2! congr; rewrite &(eq_from_nth witness); 1: smt(ge1_d expr_gt0).
    move=> i rng_i; rewrite nthlfs; 1,2,3: smt(ge1_d expr_gt0). 
    rewrite lfslpval nth_mkseq //=.
    do 3! congr; rewrite &(eq_from_nth witness) 1:size_mkseq 1:valP; 1: smt(ge2_len).
    move=> j; rewrite size_mkseq => rng_j; rewrite nth_mkseq 1:/# /=.
    by rewrite nthpks //; smt(ge1_d expr_gt0). 
  by do ? (split; 1: smt()); smt().
conseq (: _ ==> ={sigl}) => //=.
inline *.
while (#pre /\ ={sigl} /\ 0 <= size sigl{1} <= l).
+ wp; sp 5 1 => />.
  conseq (: _ ==> ={sapl}) => />; 1: by smt(size_rcons).
  while (   #pre 
         /\ ={sapl, tidx, kpidx}
         /\ root0{1} 
            =
            (if size sapl{1} = 0
             then m0{1}
             else val_bt_trh ps1{1} (set_typeidx (set_ltidx ad1{1} (size sapl{1} - 1) tidx{1}) trhtype) 
                    (list2tree (mkseq (fun (i : int) => 
                      pkco ps1{1} (set_kpidx (set_typeidx (set_ltidx ad1{1} (size sapl{1} - 1) tidx{1}) pkcotype) i)
                           (flatten (map DigestBlock.val (mkseq (fun (j : int) => 
                             cf ps1{1} (set_chidx (set_kpidx (set_typeidx (set_ltidx ad1{1} (size sapl{1} - 1) tidx{1}) chtype) i) j) 0 (w - 1) 
                                (val (nth witness (val (nth witness (nth witness (nth witness skWOTStd0{1} (size sapl{1} - 1)) tidx{1}) i)) j))) len)))) l')) h' 0)
         /\ (size sapl{1} < d => 
                   tidx{1} = (fold (fun (idxs : _ * _) => edivz idxs.`1 l') (size sigl{1}, 0) (size sapl{1})).`1
                /\ kpidx{1} = (fold (fun (idxs : _ * _) => edivz idxs.`1 l') (size sigl{1}, 0) (size sapl{1})).`2)
         /\ (0 < size sapl{1} => tidx{1} < nr_trees (size sapl{1} - 1))
         /\ 0 <= tidx{1}
         /\ 0 <= kpidx{1} < l'
         /\ 0 <= size sapl{1} <= d).
  - wp => /=.
    while{1} ((forall (i : int), 0 <= i < size leaves1{1} =>
                nth witness leaves1{1} i
                =
                pkco ps3{1} (set_kpidx (set_typeidx ad3{1} pkcotype) i)
                     (flatten (map DigestBlock.val (mkseq (fun (j : int) => 
                       cf ps3{1} (set_chidx (set_kpidx (set_typeidx ad3{1} chtype) i) j) 0 (w - 1) (val (nth witness (val (nth witness skWOTSl{1} i)) j))) len))))
              /\ 0 <= size leaves1{1} <= l')
             (l' - size leaves1{1}).
    * move=> &1 z.
      wp => /=.
      while ((forall (i : int), 0 <= i < size pkWOTS0 =>
                nth witness pkWOTS0 i
                =
                cf ps4 (set_chidx ad4 i) 0 (w - 1) (val (nth witness (val skWOTS3) i)))
             /\ 0 <= size pkWOTS0 <= len)
            (len - size pkWOTS0).
      + move=> z'.
        wp; skip => /> &2 nthval ? ? ?. 
        rewrite -!andbA; split; 2: by smt(size_rcons).
        move=> i ge0_i; rewrite size_rcons => ltsz1_i.
        rewrite nth_rcons; case (i = size pkWOTS0{2}) => [-> //| neqsz_i].
        by rewrite (: i < size pkWOTS0{2}) 1:/# /= nthval 1:/#.
      wp; skip => /> &2 nthlf ? ? ?.
      split => [| pkWOTS]; 1: smt(ge2_len).
      split => [/# | /lezNgt gelen_szpk nthpk ? ?].
      rewrite -!andbA; split; 2: by smt(size_rcons).
      move=> i ge0_i; rewrite size_rcons => ltsz1_i.
      rewrite nth_rcons; case (i = size leaves1{2}) => [-> //=| neqsz_i].
      + do 3! congr.
        rewrite insubdK 1:/# &(eq_from_nth witness) => [|j rng_j].
        - by rewrite size_mkseq; smt(ge2_len).
        rewrite (nth_map witness) 1:size_iota /=; 1: smt(ge2_len).
        by rewrite nthpk 1:rng_j nth_iota 1:/# //. 
      by rewrite (: i < size leaves1{2}) 1:/# /= nthlf 1:/#.
    wp => /=.
    while{1} ((forall (i : int), 0 <= i < size sig1{1} =>
                nth witness sig1{1} i
                =
                cf ps2{1} (set_chidx ad2{1} i) 0 (BaseW.val em{1}.[i]) (val (nth witness (val skWOTS1{1}) i)))
              /\ 0 <= size sig1{1} <= len)
             (len - size sig1{1}).
    * move=> ? z.
      wp; skip => /> &1 nthsig ? ? ?.
      rewrite -!andbA; split => [i ge0_i|]; 2: smt(size_rcons).
      rewrite size_rcons => ltsz1_i; rewrite nth_rcons.
      case (i = size sig1{1}) => [-> // | neqszs_i].
      by rewrite (: i < size sig1{1}) 1:/# /= nthsig 1:/#.
    wp; skip => /> &2 nthpks nthlfs nthrs nthsigs nthszlfs ge0_szsigl _ ltl_szsigl
                      tkpidxsv ltnt_tidx ge0_tidx ge0_kpidx ltlp_kpidx ge0_szsapl
                      _ ltd_szsapl.
    split => [| siglp]; 1: smt(ge2_len).
    split => [/# | /lezNgt gelen_szsiglp nthsiglp _ lelen_szsiglp].
    split => [| lfsp]; 1: smt(ge1_lp).
    split => [/#| /lezNgt gelp_lfsp nthlfsp _ lelp_lfsp].
    have rng_tidxdiv : 0 <= tidx{2} %/ l' && tidx{2} %/ l' < nr_trees (size sapl{2}).
    * case (size sapl{2} = 0) => [eq0 | neq0] /=.
      + move: (tkpidxsv _); 1: smt().
        rewrite eq0 fold0 /= => -[-> _].
        rewrite divz_ge0 2:ge0_szsigl /= 2:ltz_divLR; 1,2: smt(ge1_lp).
        by rewrite (ltr_le_trans l) // /nr_trees /l' -exprD_nneg 1:mulr_ge0; smt(ge0_hp ge1_d).
      rewrite divz_ge0 2:ltz_divLR; 1,2: smt(ge1_lp). 
      rewrite (: nr_trees (size sapl{2}) * l' = nr_trees (size sapl{2} - 1)). 
      + rewrite /nr_trees /l' -exprD_nneg 1:mulr_ge0; 1..3: smt(ge0_hp ge1_d).
        by congr; ring.
      by rewrite ge0_tidx /= ltnt_tidx 1:/#.
    have rng_tidxmod : 0 <= tidx{2} %% l' && tidx{2} %% l' < l' by smt(ge1_lp modz_ge0 ltz_pmod). 
    rewrite ?size_rcons -!andbA; split.
    * do 2! congr; 1: rewrite &(DBLL.val_inj).
      + rewrite &(eq_from_nth witness) 1:?valP //.
        move=> i; rewrite valP => rng_i; rewrite insubdK 1:/#.
        rewrite nthsiglp 1:/# nthsigs 1:/# //.
        case (size sapl{2} = 0) => [eq0 | neq0] /=; do ? congr.
        - move: (tkpidxsv ltd_szsapl); rewrite eq0 fold0 /=. 
          by rewrite -divz_eq => -[-> _].
        rewrite nthrs 1:/# -?divz_eq; 2: do ? congr.
        - by split => [/#|_]; rewrite ltnt_tidx /#.
        rewrite &(eq_from_nth witness) 1:size_mkseq 1:nthszlfs 1..3:/#.
        move=> j; rewrite size_mkseq => rng_j.
        rewrite nth_mkseq 1:/# /= nthlfs 1..3:/# /=; do ? congr.
        rewrite &(eq_from_nth witness) 1:size_mkseq 1:valP 1:/#.
        move=> m; rewrite size_mkseq => rng_m.
        by rewrite nth_mkseq 1:/# /= nthpks // /#.
      do ? congr; rewrite &(eq_from_nth witness) 1:nthszlfs 1,3:/# //.
      move=> i rng_i; rewrite nthlfsp 2:nthlfs // 1:/#.
      do ? congr; rewrite &(eq_from_nth witness) 1:size_mkseq 1:valP; 1: smt(ge2_len). 
      move=> m; rewrite size_mkseq => rng_m.
      by rewrite nth_mkseq 1:/# /= nthpks // /#.
    rewrite andbA; split; 2: smt(size_rcons).
    split; 1: rewrite (: size sapl{2} + 1 <> 0) 1:/# /=.     
    * do ? congr; rewrite &(eq_from_nth witness) 1:size_mkseq 1:/#.
      by move=> i rng_i; rewrite nthlfsp 2:nth_mkseq // /#. 
    by move=> ltd_szsapl1; rewrite 2?foldS /#.
  by wp; skip => />; smt(ge1_lp ge1_d fold0 Index.valP Index.insubdK).
by wp; skip => />; smt(Top.ge1_l).
qed.


local lemma EUFNAGCMA_FLSLXMSSMTTWESNPRF_MEUFGCMAWOTSTWES &m :
  hoare[A(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A, O_MEUFGCMA_WOTSTWESNPRF, FC.O_THFC_Default).O_THFC).choose : 
          R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads = [] 
          ==> 
          all (fun (ad : adrs) => get_typeidx ad <> chtype \/ get_typeidx ad <> pkcotype \/ get_typeidx ad <> trhtype) R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads] =>
  Pr[EUF_NAGCMA_FLSLXMSSMTTWESNPRF(A, O_THFC_Default).main() @ &m : res]
  <=
  Pr[M_EUF_GCMA_WOTSTWESNPRF(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A), O_MEUFGCMA_WOTSTWESNPRF, FC.O_THFC_Default).main() @ &m : res]
  +
  Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFNAGCMA(A), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFNAGCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res].
proof.
move=> allntads.
have ->:
  Pr[EUF_NAGCMA_FLSLXMSSMTTWESNPRF(A, O_THFC_Default).main() @ &m : res]
  =
  Pr[EUF_NAGCMA_FLSLXMSSMTTWESNPRF_V.main() @ &m : res].
+ by byequiv (Eqv_EUFNAGCMA_FLSLXMSSMTTWESNPRF_Orig_V).
rewrite -RField.addrA Pr[mu_split EUF_NAGCMA_FLSLXMSSMTTWESNPRF_V.valid_WOTSTWES] RealOrder.ler_add.
+ byequiv=> //. 
  proc.
  inline{2} 5; inline{2} 4.
  swap{1} 3.
  inline{1} 2; inline{2} 3; inline{2} 2; inline{2} 8.
  swap{2} 4 7.
  seq 5 10 : (   ={glob A, ps}
              /\ O_THFC_Default.pp{1} = O_MEUFGCMA_WOTSTWESNPRF.ps{2}
              /\ O_THFC_Default.pp{1} = FC.O_THFC_Default.pp{2}
              /\ O_THFC_Default.tws{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2}
              /\ ml{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.ml{2}
              /\ all (fun (ad : adrs) => get_typeidx ad <> chtype \/ get_typeidx ad <> pkcotype \/ get_typeidx ad <> trhtype) R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2}).
  - call (:   ={glob A, arg}
           /\ O_THFC_Default.pp{1} = FC.O_THFC_Default.pp{2}
           /\ O_THFC_Default.tws{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2}
           /\ R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2} = []
           ==>
              ={glob A, res}
           /\ O_THFC_Default.pp{1} = FC.O_THFC_Default.pp{2}
           /\ O_THFC_Default.tws{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2}
           /\ all (fun (ad : adrs) => get_typeidx ad <> chtype \/ get_typeidx ad <> pkcotype \/ get_typeidx ad <> trhtype) R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2}).
    * conseq (: ={glob A, arg} /\ O_THFC_Default.pp{1} = FC.O_THFC_Default.pp{2} /\ O_THFC_Default.tws{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2} 
                ==> 
                ={glob A, res} /\ O_THFC_Default.pp{1} = FC.O_THFC_Default.pp{2} /\ O_THFC_Default.tws{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2})
             _
             allntads => //.
      proc (O_THFC_Default.pp{1} = FC.O_THFC_Default.pp{2} /\ O_THFC_Default.tws{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads{2}) => //.  
      proc; inline{2} 1.
      by wp; skip. print O_MEUFGCMA_WOTSTWESNPRF. 
    by wp; rnd; skip.
  (*
  seq 7 7 : (   #pre
             /\ ad{1} = adz
             /\ ad{1} = R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.ad{2}
             /\ ) 
  forall i j u, 
    nth witness O_MEUFGCMA_WOTSTWESNPRF.qs{2} (bigi predT (fun (m : int) => nr_trees m) 0 i * l' + j * l' + u)
    =
    (set_kpidx (set_typeidx (set_ltidx adz i j) chtype) u, 
     if i = 0
     then nth witness ml{2} (j * t + u)
     else nth witness (nth witness (nth witness rootstd (i - 1)) j) u) 
   * + 
  *)
  admit.
rewrite Pr[mu_split EUF_NAGCMA_FLSLXMSSMTTWESNPRF_V.valid_TCRPKCO] RealOrder.ler_add.
+ admit.
admit.
qed.


lemma EUFNAGCMA_FLSLXMSSMTTWESNPRF &m :
  hoare[A(R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A, O_MEUFGCMA_WOTSTWESNPRF, FC.O_THFC_Default).O_THFC).choose : 
          R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads = [] 
          ==> 
          all (fun (ad : adrs) => get_typeidx ad <> chtype \/ get_typeidx ad <> pkcotype \/ get_typeidx ad <> trhtype) R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.O_THFC.ads] =>
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
move=> allntds.
move: (MEUFGCMA_WOTSTWESNPRF (R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA(A)) _ _ &m)
      (EUFNAGCMA_FLSLXMSSMTTWESNPRF_MEUFGCMAWOTSTWES &m allntds); 3: smt(). 
+ move=> O OC Oll OCll.
  proc; inline *.
  wp.
  while (true) (d - size R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.pkWOTStd).
  - move=> z.
    wp.
    while (true) 
          (nr_trees (size R_MEUFGCMAWOTSTWESNPRF_EUFNAGCMA.pkWOTStd) - size pkWOTSnt).
    * move=> z'.
      wp => /=.
      while (true) (h' - size nodes).
      + move=> z''.
        wp => /=.
        while (true) (nr_nodes (size nodes + 1) - size nodescl).
        - move=> z'''.
          by wp; call OCll; wp; skip => />; smt(size_rcons). 
        by wp; skip => />; smt(size_rcons).
      wp => /=.
      while (true) (l' - size pkWOTSlp).
      + move=> z''.
        wp => /=.
        call OCll; call Oll.
        by wp; skip => />; smt(size_rcons).
      by wp; skip => />; smt(size_rcons).
    by wp; skip => />; smt(size_rcons).
  wp; call (: true). 
  - by move=> OC' OCpll; apply (A_choose_ll OC' OCpll).
  - proc.
    by wp; call OCll.
  by wp; skip => /> /#.
move => O OC.
proc; inline *.
wp => /=.
while (true) (d - size forgeryfs).
+ move=> z.
  wp.
  while (true) (len - size pkWOTS0).
  - move=> z'.
    by wp; skip => />; smt(size_rcons).
  by wp; skip => />; smt(size_rcons).
wp.
call (: true).
+ by move=> OC'; apply (A_forge_ll OC').
wp => /=.
while (true) (l - size sigl).
+ move=> z.
  wp.
  while (true) (d - size sapl).
  - move=> z'.
    by wp; skip => />; smt(size_rcons).
  by wp; skip => />; smt(size_rcons).
by wp; skip => /> /#.
qed.

end section Proof_EUF_NAGCMA_FL_SL_XMSS_MT_TW_ES_NPRF.
