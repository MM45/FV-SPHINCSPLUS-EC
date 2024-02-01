(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList StdOrder StdBigop IntDiv RealExp FinType BitEncoding.
(*---*) import BS2Int BitChunking.
(*---*) import IntOrder Bigint BIA.

(* -- Local -- *)
require import BinaryTrees MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.
require (*--*) DigitalSignatures.
require (*--*) WOTS_TW.



(* --- Parameters --- *)
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

(* Height of a single (XMSS) binary hash tree *)
const h' : { int | 1 <= h' } as ge1_hp. 

(* Number of WOTS-TW instances of a single (XMSS) binary hash tree (i.e., number of leaves) *)
const l' = 2 ^ h'.

(* Number of layers in the hypertree (i.e., height of tree of XMSS trees) *)
const d : { int | 1 <= d } as ge1_d.

(* 
  Height of "flattened" hypertree 
  (i.e., total height of concatenation of inner trees) 
*)
const h : int = h' * d.

(* 
  Number of leaves of "flattened" hypertree
  (i.e., total number of leaves of all inner trees on bottom layer)
*)
const l : int = 2 ^ h.
 
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

(* l' is greater than or equal to 2 *)
lemma ge2_lp : 2 <= l'.
proof. by rewrite /l' ler_eexpr; smt(ge1_hp). qed.

(* h is greater than or equal to 1 *)
lemma ge1_h : 1 <= h.
proof. by rewrite /h mulr_ege1 1:ge1_hp ge1_d. qed.

(* l is greater than or equal to 2 *)
lemma ge2_l : 2 <= l.
proof. by rewrite /l ler_eexpr; smt(ge1_h). qed.



(* --- Operators (1/2) --- *)
(* -- Auxiliary -- *)
(* Number of nodes in a (XMSS) binary hash tree (of total height h') at a particular height h'' *)
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
+ by rewrite mulr_ge0; smt(ge1_hp).
by congr; ring.
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

(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = chtype \/ typeidx = pkcotype \/ typeidx = trhtype.

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



(* --- Fixed-Length XMSS-MT-TW in an encompassing structure --- *)
theory ES.
(* Length of addresses used in tweakable hash functions (including unspecified global/context part) *)
const adrs_len : { int | 6 <= adrs_len} as ge6_adrslen.

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
  corresponding to FL-XMSS-MT-TW addresses used in the
  encompassing structure. This global/context part is the part that is to be defined
  by this unknown structure and, therefore, this validity check is left abstract.
*)
op valid_xidxvalsgp : int list -> bool.

(* 
  Validity check for the values of the list of integers corresponding to 
  FL-XMSS-MT-TW addresses used in the encompassing structure.
  This includes the local part that we defined, and the abstract global/context part
  defined by the unknown structure.  
*) 
op valid_xidxvals (adidxs : int list) =
  valid_xidxvalsgp (drop 6 adidxs) /\ valid_xidxvalslp (take 6 adidxs).

(*
  Overall validity check for the list of integers corresponding to 
  FL-XMSS-MT-TW addresses used in the encompassing structure.
  This checks for the correct length and valid values.
*)
op valid_xadrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_xidxvals adidxs.

(*
  The list of integers that correspond to FL-XMSS-MT-TW addresses are a subset of
  the list of integers that correspond to valid addresses. (In other words,
  the FL-XMSS-MT-TW addresses are a subset of the complete set of valid addresses
  used in the encompassing structure.)
*)
axiom valid_xidxvals_idxvals : 
  valid_xidxvals <= valid_idxvals.

(*
  The FL-XMSS-MT-TW addresses are a subset of the complete set of valid addresses
  used in the encompassing structure. 
*)  
lemma valid_xadrsidxs_adrsidxs :
  valid_xadrsidxs <= valid_adrsidxs.
proof. 
rewrite /(<=) /valid_xadrsidxs /valid_adrsidxs => adidxs [-> /=].
by apply valid_xidxvals_idxvals.
qed.



(* --- Types (1/3) --- *)
(* 
  Addresses used in encompassing structure (complete set, including FL-XMSS-MT-TW addresses)
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



(* --- Clones and imports --- *)
(* WOTS-TW *)
clone import WOTS_TW as WTW with
  op adrs_len <- adrs_len,
  op n <- n,
  op log2_w <- log2_w,
  op w <- w,
  op len <- len,
  op d <- bigi predT (fun (d' : int) => nr_nodes_ht d' 0) 0 d,
  op valid_chidx <- valid_chidx,
  op valid_hidx <- valid_hidx,
  op valid_idxvals <- valid_idxvals,
  op valid_adrsidxs <- valid_adrsidxs,
  op valid_widxvalsgp adidxswgp <=    valid_kpidx (nth witness adidxswgp 0) 
                                   /\ nth witness adidxswgp 1 = chtype
                                   /\ valid_tidx (nth witness adidxswgp 3) (nth witness adidxswgp 2) 
                                   /\ valid_lidx (nth witness adidxswgp 3)
                                   /\ valid_xidxvalsgp (drop 4 adidxswgp),
  
  theory HA <- HA
  
  proof ge2_adrslen, ge1_n, val_log2w, ge1_d, valid_widxvals_idxvals.
  realize ge2_adrslen by smt(ge6_adrslen).
  realize ge1_n by exact: ge1_n.
  realize val_log2w by exact: val_log2w.
  realize ge1_d.
    rewrite (: d = d - 1 + 1) // big_int_recr /= 2:nrnodesht_h; 1,2,3: smt(ge1_d ge1_h).
    rewrite ler_paddl // 2:exprn_ege1 //; 2: smt(ge1_h ge1_d).
    rewrite sumr_ge0_seq => d' /mem_range [ge0_dp ltd_dp] _ /=. 
    by rewrite nrnodesht_h 3:expr_ge0 //; 1,2: smt(ge1_h).
  qed.
  realize valid_widxvals_idxvals.
    rewrite /(<=) => adidxs valwadidxs; apply valid_xidxvals_idxvals.
    move: valwadidxs => @/valid_widxvals @/valid_widxvalsgp @/valid_widxvalslp.
    rewrite /valid_xidxvals /valid_xidxvalslp /valid_xidxvalslpch. 
    by rewrite drop_drop //= ?nth_drop //= ?nth_take //= /#.
  qed.
    
import DigestBlock DBLL WAddress EmsgWOTS.



(* --- Types (2/3) --- *)
(* Integers between 0 (including) and l (including), used for the signing index *)
clone import Subtype as Index with
  type T <= int,
    op P <= fun (i : int), 0 <= i < l
    
  proof *.
  realize inhabited by exists 0; smt(ge2_l).
  
type index = Index.sT.

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

(* Public keys *)
type pkFLXMSSMTTW = dgstblock * pseed * adrs.

(* Secret keys *)
type skFLXMSSMTTW = index * sseed * pseed * adrs.

(* Messages *)
type msgFLXMSSMTTW = msgWOTS.

(* 
  Lists of length d of which the entries are sigWOTS/authentication path pairs 
  (i.e., FL-XMSS-TW signatures) 
*)
clone import Subtype as SAPDL with
  type T <= (sigWOTS * apFLXMSSTW) list,
    op P ls <= size ls = d
    
  proof *.
  realize inhabited by exists (nseq d witness); rewrite size_nseq; smt(Top.ge1_d).

type sigFLXMSSTWDL = SAPDL.sT.

(* Signatures *)
type sigFLXMSSMTTW = index * sigFLXMSSTWDL.



(* --- Distributions --- *)
(* Proper, full, and uniform distribution over messages considered for FL-XMSS-MT-TW *)
op [lossless full uniform] dmsgFLXMSSMTTW : msgFLXMSSMTTW distr.



(* --- Operators --- *)
(* - Validity/type checks for (indices corresponding to) XMSS-TW addresses - *)
op valid_xidxchvals (adidxs : int list) : bool =
  valid_xidxvalsgp (drop 4 adidxs) /\ valid_xidxvalslpch (take 4 adidxs).

op valid_xidxpkcovals (adidxs : int list) : bool =
  valid_xidxvalsgp (drop 4 adidxs) /\ valid_xidxvalslppkco (take 4 adidxs).
  
op valid_xidxtrhvals (adidxs : int list) : bool =
  valid_xidxvalsgp (drop 4 adidxs) /\ valid_xidxvalslptrh (take 4 adidxs).
  
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

lemma eq_valid_xadrsch_wadrs (ad : adrs) :
  valid_xadrsch ad <=> valid_wadrs ad.
proof.
rewrite /valid_xadrsch /valid_xadrschidxs /valid_xidxchvals /valid_xidxvalslpch. 
rewrite /valid_wadrs /valid_wadrsidxs /valid_widxvals /valid_widxvalslp.
by rewrite drop_drop // ?nth_drop // ?nth_take. 
qed.
  
lemma valid_xadrschidxs_xadrsidxs :
  valid_xadrschidxs <= valid_xadrsidxs.
proof.
rewrite /(<=) => adidxs @/valid_xadrschidxs @/valid_xadrsidxs [-> /=].
rewrite /valid_xidxchvals /valid_xidxvals => -[-> /=].
by rewrite /valid_xidxvalslp /valid_xidxvalslpch ?nth_take // => [#] -> -> -> ->.
qed.

lemma valid_xadrspkcoidxs_xadrsidxs :
  valid_xadrspkcoidxs <= valid_xadrsidxs.
proof.
rewrite /(<=) => adidxs @/valid_xadrspkcoidxs @/valid_xadrsidxs [-> /=].
rewrite /valid_xidxpkcovals /valid_xidxvals => -[-> /=].
by rewrite /valid_xidxvalslp /valid_xidxvalslppkco ?nth_take // => [#] -> -> -> ->.
qed.

lemma valid_xadrstrhidxs_xadrsidxs :
  valid_xadrstrhidxs <= valid_xadrsidxs.
proof.
rewrite /(<=) => adidxs @/valid_xadrstrhidxs @/valid_xadrsidxs [-> /=].
rewrite /valid_xidxtrhvals /valid_xidxvals => -[-> /=].
by rewrite /valid_xidxvalslp /valid_xidxvalslptrh ?nth_take // => [#] -> -> -> ->.
qed.

lemma valid_xadrschnpkco (ad : adrs) :
  valid_xadrsch ad => ! valid_xadrspkco ad.
proof.
rewrite /valid_xadrsch /valid_xadrschidxs /valid_xadrspkco /valid_xadrspkcoidxs => -[-> /=].
rewrite /valid_xidxchvals /valid_xidxpkcovals => -[-> /=].
rewrite /valid_xidxvalslpch /valid_xidxvalslppkco ?nth_take //; smt(dist_adrstypes).
qed.


(* - Setters - *)
op set_typeidx (ad : adrs) (i : int) : adrs =
  insubd (put (put (put (put (val ad) 0 0) 1 0) 2 0) 3 i).

op set_kpidx (ad : adrs) (i : int) : adrs =
  set_idx ad 2 i.
  
op set_thtbidx (ad : adrs) (i j : int) : adrs =
  insubd (put (put (val ad) 0 j) 1 i).
