(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr FinType BitEncoding.
(*---*) import BS2Int.


(* -- Local -- *)
require import MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.



(* - Parameters - *)
(* -- General -- *)
(* Length of addresses used in tweakable hash functions (including unspecified global/context part) *)
const adrs_len : { int | 4 <= adrs_len} as ge4_adrslen.

(* Byte-length of each private key element, public key element, and signature element *)
const n : { int | 1 <= n } as ge1_n.

(* Number of private key sets and merkle trees *)
const k : { int | 1 <= k } as ge1_k.

(* Height of each merkle tree *)
const a : { int | 1 <= a } as ge1_a.

(* Number of elements in each private key set and leaves in each merkle tree *)
const t : int = 2 ^ a.

(* Address type constant for tree hashing *)
const trhtype : int.

(* Address type constant for tree root compression *)
const trcotype : int.


(* -- Notions -- *)
(*  Number of FORS-TW instances to consider in security notion *)
const d : { int | 1 <= d } as ge1_d.


(* -- Properties of parameters -- *)
(* The different address types are distinct *)
axiom dist_adrstypes : trhtype <> trcotype. 

(* t is greater than or equal to 2 *)
lemma ge2_t : 2 <= t.
proof. by rewrite /t -{1}expr1 StdOrder.IntOrder.ler_weexpn2l 2:ge1_a. qed. 



(* - Types (1/2) - *)
(* -- General -- *)
(*
(* Randomness for message compression *)
type mkey.
*)
(* Secret seeds *)
type sseed.

(* Public seeds *)
type pseed.
(*
(* Messages *)
type msg = bool list.
*)
(* 
  Digests, i.e., outputs of (tweakable) hash functions. 
  In fact, also input of (tweakable) hash functions in this case.
*)
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


(* -- FORS/FORS-TW specific -- *)
(* Public keys *)
type pkFORS = dgstblock.

(* Secret keys *)
clone import Subtype as SkFORS with
  type T   <- dgstblock list,
    op P l <- size l = k * t
    
  proof *.
  realize inhabited by exists (nseq (k * t) witness); smt(size_nseq ge1_k ge2_t).

type skFORS = SkFORS.sT.

clone import Subtype as MsgFORSTW with
  type T   <- bool list,
    op P l <- size l = k * a
    
  proof *.
  realize inhabited by exists (nseq (k * a) witness); smt(size_nseq ge1_k ge1_a).

type msgFORSTW = MsgFORSTW.sT.

(* Lists of length a containing digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DBAL with
  type T   <- dgstblock list,
    op P l <- size l = a
    
  proof *.
  realize inhabited by exists (nseq a witness); smt(size_nseq ge1_a).
   
(* Authentication paths in merkle trees *)
type apFORSTW = DBAL.sT.

(* Lists of length k containing skFORSTW (single element)/apFORSTW pairs *)
clone import Subtype as DBAPKL with
  type T   <- (dgstblock * apFORSTW) list,
    op P l <- size l = k
    
  proof *.
  realize inhabited by exists (nseq k witness); smt(size_nseq ge1_k).

(* Signatures *)
type sigFORSTW = DBAPKL.sT.



(* - Operators (1/2) - *)
(* -- Auxiliary -- *)
(* Number of nodes in a merkle tree (of total height a) at a particular height a' *)
op nr_nodes (a' : int) = 2 ^ (a - a').


(* -- Validity checks -- *)
(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = trhtype \/ typeidx = trcotype.

(* Keypair index validity check *)
op valid_kpidx (kpidx : int) : bool = 
  0 <= kpidx < k.

(* Tree height index validity check *)
op valid_thidx (thidx : int) : bool = 
  0 <= thidx <= a.

(* Tree breadth index validity check *)
op valid_tbidx (thidx tbidx : int) : bool = 
  0 <= tbidx < nr_nodes thidx.

(* Overall (generic) validity check for indices of addresses *)
op valid_idxvals : int list -> bool.

(* Overall (generic) validity check for indices of addresses, including the number of indices *)
op valid_adrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_idxvals adidxs.

(* 
  Generic validity check for the global/context part of the indices 
  corresponding to a FORS-TW address
*)
op valid_fidxvalsgp : int list -> bool.

(* Tree hash address indices validity check (local part) *)
op valid_fidxvalslptrh (adidxs : int list) : bool = 
     valid_tbidx (nth witness adidxs 1) (nth witness adidxs 0)
  /\ valid_thidx (nth witness adidxs 1)
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trhtype.

(* Tree root compression address indices validity check (local part) *)
op valid_fidxvalslptrco (adidxs : int list) : bool = 
     nth witness adidxs 0 = 0
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trcotype.
   
(* 
  Validity check for the local part of the indices corresponding to a FORS-TW address
  (i.e., type, keypair, tree height, and tree breadth indices) 
*)
op valid_fidxvalslp (adidxs : int list) : bool =
  valid_fidxvalslptrh adidxs \/ valid_fidxvalslptrco adidxs.
  
(* 
  Overall validity check for the indices corresponding to a FORS-TW address
  (the first four indices must be valid local indices, and the remaining indices 
  must constitute valid global/context indices)
*)  
op valid_fidxvals (adidxs : int list) =
  valid_fidxvalsgp (drop 4 adidxs) /\ valid_fidxvalslp (take 4 adidxs).

(* 
  Overall validity check for the indices corresponding to a FORS-TW address,
  including the number of indices
*)    
op valid_fadrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_fidxvals adidxs.

(* 
  The set of (indices corresponding to) valid FORS-TW addresses must be a subset
  of the full set of (indices corresonding to) addresses
*) 
axiom valid_fidxvals_idxvals :
  valid_fidxvals <= valid_idxvals.

(* 
  The set of (indices corresponding to) valid FORS-TW addresses must be a subset
  of the full set of (indices corresonding to) addresses, including length check
*) 
lemma valid_fadrsidxs_adrsidxs :
  valid_fadrsidxs <= valid_adrsidxs.
proof. 
rewrite /(<=) /valid_fadrsidxs /valid_adrsidxs => adidxs [-> /=].
by apply valid_fidxvals_idxvals.
qed.



(* - Distributions - *)  
(* Proper distribution over public seeds *)
op [lossless] dpseed : pseed distr.

(* Proper distribution over secret seeds *)
op [lossless] dsseed : sseed distr.

(* Proper distribution over digests of length 1 (block of 8 * n bits) *)
op [lossless] ddgstblock : dgstblock distr.



(* - Types (2/2) - *)
(* -- General -- *)
(* Addresses used in tweakable hash functions *)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
    proof ge1_l by smt(ge4_adrslen).
    
import Adrs.

type adrs = HA.adrs.


(* -- FORS/FORS-TW specific -- *)
(* Public keys *)
type pkFORSTW = pkFORS * pseed * adrs.

(* Secret keys *)
type skFORSTW = sseed * pseed * adrs.



(* - Operators (2/2) - *)
(* -- Validity checks -- *)
(* Overall (generic) validity check for addresses *)
op valid_adrs (ad : adrs) =
  valid_adrsidxs (val ad).

(* Overall validity check for FORS-TW addresses *)    
op valid_fadrs (ad : adrs) : bool =
  valid_fadrsidxs (val ad).

(* The set of valid FORS-TW addresses is a subset of the full set of addresses *)
lemma valid_fadrs_adrs :
  valid_fadrs <= valid_adrs.
proof. smt(valid_fadrsidxs_adrsidxs). qed.


(* -- Setters -- *)
op set_typeidx (ad : adrs) (i : int) : adrs =
  insubd (put (put (put (put (val ad) 0 0) 1 0) 2 0) 3 i).

op set_kpidx (ad : adrs) (i : int) : adrs =
  set_idx ad 2 i.
  
op set_thtbidx (ad : adrs) (i j : int) : adrs =
  insubd (put (put (val ad) 0 j) 1 i).

  

(* -- Tweakable Hash Functions -- *)
(* 
  Tweakable hash function collection that contains all tweakable hash functions
  used in WOTS-TW, XMSS, and SPHINCS+
*)
op thfc : int -> pseed -> adrs -> dgst -> dgstblock.

(* Tweakable hash function used to construct merkle trees from secret values *)
op trh : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * 2).

clone import TweakableHashFunctions as TRH with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,
  
    op f <- trh,
  
    op dpp <- dpseed
    
  proof *.
  realize dpp_ll by exact: dpseed_ll.

clone import TRH.Collection as TRHC with
  type diff <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n * 2).

clone import TRHC.SMDTTCRC as TRHC_TCR with
  op t_smdttcr <- d * k * (t - 1)
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).

(* Tweakable hash function used compress merkle tree roots to public key *)
op trco : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * k).

clone import TweakableHashFunctions as TRCO with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,
  
    op f <- trco,
  
    op dpp <- dpseed
    
  proof *.
  realize dpp_ll by exact: dpseed_ll.

clone import TRCO.Collection as TRCOC with
  type diff <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n * k).

clone import TRCOC.SMDTTCRC as TRCOC_TCR with
  op t_smdttcr <- d * k
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k).


(* -- Merkle trees -- *)
(* 
  Computes the (hash) value corresponding to the root of the binary tree w.r.t.
  a certain public seed, address, height index, and breadth index. 
*)
op val_bt_trh (bt : dgstblock bintree) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock =
  with bt = Leaf x => x
  with bt = Node l r => 
    trh ps (set_thtbidx ad hidx bidx) 
      (val (val_bt_trh l ps ad (hidx - 1) (2 * bidx)) ++ val (val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1))).

(* 
  Constructs an authentication path (without embedding it in the corresponding subtype)
  from a binary tree and a path represented by a boolean list w.r.t. a certain 
  public seed, address, height index, and breadth index. 
*)
op cons_ap_trh_gen (bt : dgstblock bintree) (bs : bool list) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock list =
  with bt = Leaf _, bs = [] => []
  with bt = Leaf _, bs = _ :: _ => witness
  with bt = Node _ _, bs = [] => witness
  with bt = Node l r, bs = b :: bs' =>
    (val_bt_trh (if b then l else r) ps ad (hidx - 1) (if b then 2 * bidx else 2 * bidx + 1)) 
    :: cons_ap_trh_gen (if b then r else l) bs' ps ad (hidx - 1) (if b then 2 * bidx + 1 else 2 * bidx). 

(*
  Computes the (hash) value corresponding to an authentication path, a leaf, and a 
  path represented by a boolean list w.r.t a certain public seed, address, height index, 
  and breadth index.
*)  
op val_ap_trh_gen (ap : dgstblock list) (bs : bool list) (leaf : dgstblock) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock =
  with ap = [], bs = [] => leaf
  with ap = [], bs = _ :: _ => witness 
  with ap = _ :: _, bs = [] => witness
  with ap = x :: ap', bs = b :: bs' =>
      trh ps (set_thtbidx ad hidx bidx) 
       (if b 
        then val x ++ val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx + 1))
        else val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx)) ++ val x).

(* 
  Constructs authentication path (embedding it in the corresponding subtype)
  for the special case of binary trees of height a w.r.t. a certain public seed, address, 
  height index a, and breadth index 0. Expects a binary tree (bt) that is 
  a merkle tree of height a and index (idx) in [0, 2 ^ a - 1].
*)
op cons_ap_trh (bt : dgstblock bintree) (idx : int) (ps : pseed) (ad : adrs) : apFORSTW =
  DBAL.insubd (cons_ap_trh_gen bt (rev (int2bs a idx)) ps ad a 0).

(* 
  Computes value corresponding to an authentication path, leaf, and a path represented 
  by the big-endian binary representation of an index between 0 (including) 
  and 2 ^ a (including) w.r.t. a certain public seed, address, height index a, 
  and breadth index 0. Expects an index (idx) in [0, 2 ^ a - 1].
*)
op val_ap_trh (ap : apFORSTW) (idx : int) (leaf : dgstblock) (ps : pseed) (ad : adrs) : dgstblock = 
  val_ap_trh_gen (val ap) (rev (int2bs a idx)) leaf ps ad a 0.


(* - Types (3/3) - *)
(*
  FORS-TW addresses
  Introduced only for the purpose of the proof; specifically, to ensure that 
  the adversary provides us with a valid FORST-TW addresses in the security notion. 
  Essentially, this excludes the "irrelevant"
  adversaries that provide invalid addresses from the considered class of
  adversaries. Equivalently, we could introduce a behavioral check on the adversary
  at the end of the game (i.e., only let the adversary succeed if the
  provided address is a valid FORS-TW address). Furthermore, this approach
  would also be equivalent to having no subtype or extended behavioral check
  but instead have the considered scheme/oracle do input sanitization (i.e., have the scheme
  check whether the provided address ia a valid FORS-TW addresses).
*)
clone import Subtype as FAddress with
  type T <- adrs,
    op P <- valid_fadrs.
    
type fadrs = FAddress.sT.


(* - Specification - *)
module FL_FORS_TW_ES = {
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : pkFORSTW * skFORSTW =  {
    return witness;
  }
  
  proc sign(sk : skFORSTW, m : msgFORSTW) : sigFORSTW = {
    return witness;
  }
  
  proc verify(pk : pkFORSTW, m : msgFORSTW, sig : sigFORSTW) : bool = {
    return witness;
  } 
}.



(* - Proof - *)
(* -- Oracles -- *)
module type Oraclei_EUFCMA_FLFORSTWES = {
  proc init(sk_init : skFORSTW) : unit
  proc sign(m : msgFORSTW) : 
}.

module type Oracle_EUFCMA_FLFORSTWES = {
  
}.


(* -- Adversary classes -- *)
module type Adv_EUFCMA_FLFORSTWES (O : Oracle_EUFCMA_FLFORSTWES) = {
  proc forge(pk : pkFORSTW) : msgFORSTW * sigFORSTW 
}.

(* -- Notions -- *)
