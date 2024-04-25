(* - Require/Import - *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr SmtMap DList FinType IntDiv BitEncoding StdOrder StdBigop LoopTransform.
(*---*) import BS2Int BitChunking Bigint BIA.
(*---*) import IntOrder RealOrder.

(* -- Local -- *)
require import BinaryTrees MerkleTrees.
require (*--*) KeyedHashFunctions TweakableHashFunctions HashAddresses.
require (*--*) DigitalSignatures.
require (*--*) OpenPRE_From_TCR_DSPR_THF.



(* - Parameters - *)
(* -- General -- *)
(* Length of addresses used in tweakable hash functions (including unspecified global/context part) *)
const adrs_len : { int | 5 <= adrs_len} as ge5_adrslen.

(* Byte-length of each private key element, public key element, and signature element *)
const n : { int | 1 <= n } as ge1_n.

(* Number of private key sets and Merkle trees *)
const k : { int | 1 <= k } as ge1_k.

(* Height of each Merkle tree *)
const a : { int | 1 <= a } as ge1_a.

(* Number of elements in each private key set and leaves in each Merkle tree *)
const t : int = 2 ^ a.

(* Address type constant for tree hashing *)
const trhtype : int.

(* Address type constant for tree root compression *)
const trcotype : int.


(* -- Instances -- *)
(* 
  Number of FORS-TW instances in a keypair set 
  (SPHINCS+: Number of leaves of single XMSS instance on bottom layer)  
*)
const l : { int | 1 <= l } as ge1_l.

(* 
  Number of keypair sets 
  (SPHINCS+: Number of XMSS instance on bottom layer)  
*)
const s : { int | 1 <= s } as ge1_s. 

(* 
  Number of FORS-TW instances to consider
  Axiomatized instead of explicitly defined to be able to instantiate.
*)
const d : { int | d = s * l } as dval.


(* -- Properties of parameters -- *)
(* The different address types are distinct *)
axiom dist_adrstypes : trhtype <> trcotype. 

(* 
  Number of leaves of a Merkle tree in a FORS-TW instance is 
  greater than or equal to 2 
*)
lemma ge2_t : 2 <= t.
proof. by rewrite /t -{1}expr1 StdOrder.IntOrder.ler_weexpn2l 2:ge1_a. qed. 

(* 
  Number of FORS-TW instances is greater than or equal to 1
*)
lemma ge1_d : 1 <= d.
proof. by rewrite dval StdOrder.IntOrder.mulr_ege1 1:ge1_s ge1_l. qed.



(* - Types (1/3) - *)
(* -- General -- *)
(* Instance index *)
clone import Subtype as Index with
  type T <= int,
    op P i <= 0 <= i < d
    
  proof *.
  realize inhabited by exists 0; smt(ge1_d).

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
clone import Subtype as DBLLKTL with
  type T <- dgstblock list list,
    op P lss <- size lss = k /\ all (fun ls => size ls = t) lss 
    
  proof *.
  realize inhabited.
    by exists (nseq k (nseq t witness)); smt(allP mem_nseq size_nseq ge1_k ge2_t). 
  qed.

type skFORS = DBLLKTL.sT.

clone import Subtype as BLKAL with
  type T <- bool list,
    op P ls <- size ls = k * a
    
  proof *.
  realize inhabited by exists (nseq (k * a) witness); smt(size_nseq ge1_k ge1_a).

type msgFORSTW = BLKAL.sT.

(* Lists of length a containing digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DBAL with
  type T   <- dgstblock list,
    op P ls <- size ls = a
    
  proof *.
  realize inhabited by exists (nseq a witness); smt(size_nseq ge1_a).
   
(* Authentication paths in Merkle trees *)
type apFORSTW = DBAL.sT.

(* Lists of length k containing skFORSTW (single element)/apFORSTW pairs *)
clone import Subtype as DBAPKL with
  type T   <- (dgstblock * apFORSTW) list,
    op P ls <- size ls = k
    
  proof *.
  realize inhabited by exists (nseq k witness); smt(size_nseq ge1_k).

(* Signatures *)
type sigFORSTW = DBAPKL.sT.



(* - Operators (1/2) - *)
(* -- Auxiliary -- *)
(* Number of nodes in a Merkle tree (of total height a) at a particular height a' *)
op nr_nodes (a' : int) = 2 ^ (a - a').


(* -- Validity checks -- *)
(* Tree (keypair set) index validity check *)
op valid_tidx (tidx : int) : bool =
  0 <= tidx < s.

(*
(* Type index validity check *)
op valid_typeidx (typeidx : int) : bool =
  typeidx = trhtype \/ typeidx = trcotype.
*)

(* Keypair index validity check *)
op valid_kpidx (kpidx : int) : bool = 
  0 <= kpidx < l.

(* Tree height index validity check *)
op valid_thidx (thidx : int) : bool = 
  0 <= thidx <= a.

(* 
  Tree breadth index validity check.
  Note that, according to the specs, this index is not reset
  across Merkle trees in a FORS-TW instance. E.g.,
  the breadth index of the left-most leaf of the i-th tree (out of k)
  has breadth index i * t; the left-most node of the i-th tree at
  height 1 has breadth index i * (t // 2); and the root node of the
  i-th tree has breadth index i. In other words, the left-most node of 
  a certain layer in the i-th tree is given the incremented breadth index
  from the right-most node at the same layer of the (i - 1)-th tree.
  The generic formula for the breadth index of a node at height j in the
  i-th tree should thus be i * (t // 2 ^ j).
*)
op valid_tbidx (thidx tbidx : int) : bool =
  0 <= tbidx < k * nr_nodes thidx.

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
  /\ nth witness adidxs 3 = trhtype
  /\ valid_tidx (nth witness adidxs 4).
  
(* Tree root compression address indices validity check (local part) *)
op valid_fidxvalslptrco (adidxs : int list) : bool = 
     nth witness adidxs 0 = 0
  /\ nth witness adidxs 1 = 0
  /\ valid_kpidx (nth witness adidxs 2)
  /\ nth witness adidxs 3 = trcotype
  /\ valid_tidx (nth witness adidxs 4).
   
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
  valid_fidxvalsgp (drop 5 adidxs) /\ valid_fidxvalslp (take 5 adidxs).

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
(* Proper distribution over seeds for message compression key generation function *)
op [lossless] dmseed : mseed distr.

(* Proper distribution over randomness for non-deterministic signature generation
op [lossless] drm : rm distr.
*)
 
(* Proper distribution over randomness for message compression *)
op [lossless] dmkey : mkey distr.

(* Proper distribution over public seeds *)
op [lossless] dpseed : pseed distr.

(*
(* Proper distribution over secret seeds *)
op [lossless] dsseed : sseed distr.
*)

(* Proper, full, and uniform distribution over digests of length 1 (block of 8 * n bits) *)
op [lossless full uniform] ddgstblock : dgstblock distr.

(* Proper distribution over digests of length 1 (block of 8 * n bits), lifted to dgst type *)
op ddgstblocklift : dgst distr = dmap ddgstblock DigestBlock.val.

lemma ddgstblocklift_ll : is_lossless ddgstblocklift.
proof. by rewrite dmap_ll ddgstblock_ll. qed.

(*
(* 
  Proper distribution that samples a FORS secret key by independently sampling
  each individual secret key element independently from ddgstblock
*)
op dskFORS : skFORS distr = dmap (dlist (dlist ddgstblock t) k) DBLLKTL.insubd.

lemma dskFORS_ll : is_lossless dskFORS.
proof. by rewrite dmap_ll 2!dlist_ll ddgstblock_ll. qed.
*)


(* - Types (2/3) - *)
(* -- General -- *)
(* Addresses used in tweakable hash functions *)
clone import HashAddresses as HA with
  type index <= int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
    proof ge1_l by smt(ge5_adrslen).
    
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

(* Initialization ("zero") address *)
const adz : { adrs | valid_fadrs adz } as valf_adz.


(* -- Setters -- *)
op set_tidx (ad : adrs) (i : int) : adrs =
  set_idx ad 4 i.
  
op set_typeidx (ad : adrs) (i : int) : adrs =
  insubd (put (put (put (put (val ad) 0 0) 1 0) 2 0) 3 i).

op set_kpidx (ad : adrs) (i : int) : adrs =
  set_idx ad 2 i.
  
op set_thtbidx (ad : adrs) (i j : int) : adrs =
  insubd (put (put (val ad) 0 j) 1 i).


(* -- Getters -- *)
op get_tbidx (ad : adrs) : int =
  get_idx ad 0.

op get_thidx (ad : adrs) : int =
  get_idx ad 1.

op get_kpidx (ad : adrs) : int =
  get_idx ad 2.

op get_typeidx (ad : adrs) : int =
  get_idx ad 3.

op get_tidx (ad : adrs) : int =
  get_idx ad 4.

  

(* -- Keyed Hash Functions -- *)
(* Secret key element generation function *)
op skg : sseed -> (pseed * adrs) -> dgstblock.

(*
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
*)  

(* --- Message compression --- *)
(* Message compression key geneneration function
op mkg : mseed -> (rm * msg) -> mkey.
*)
op mkg : mseed -> msg -> mkey.


(*
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

(* Message compression function *)
op mco : mkey -> msg -> msgFORSTW * index.

(* 
  Function mapping output of message compression function to a list
  containing three-tuples of which the entries respectively signify the following.
  - The index of a key set (i.e., pointer to a specific FORS-TW instance).
  - The index of a secret value set (i.e., pointer to Merkle tree in FORS-TW instance indicated by first value of tuple). 
  - The index of a secret value (i.e., pointer to a leaf of the Merkle tree indicated by second value of tuple). 
*)
op g (mi : msgFORSTW * index) : (int * int * int) list =
  let cmsg = chunk a (val mi.`1) in
  let idx = val mi.`2 in
    mkseq (fun (i : int) => (idx, i, bs2int (rev (nth witness cmsg i)))) k.

clone KeyedHashFunctions as MCO with
  type key_t <- mkey,
  type in_t <- msg,
  type out_t <- msgFORSTW * index,
  
    op f <- mco
    
  proof *.
  
clone import MCO.ITSR as MCO_ITSR with  
(*
  op ks <- d,
  op svsks <- k,
  op svsvs <- t,
*)  
  op g <- g,
  
  op dkey <- dmkey
  
  proof *.
(*
  realize ge1_ks by exact: ge1_d.
  realize ge1_svsks by exact: ge1_k.
  realize ge1_svsvs by smt(ge2_t).
  realize size_g by move=> mi @/g /=; rewrite size_mkseq; smt(ge1_k).
  realize rng_iks. by move => x mi @/g /= /mkseqP [i] [_ ->] /=; rewrite valP. qed.
  realize rng_sv.
    move=> x mi @/g /= /mkseqP [i] [rng_i -> /=].
    rewrite bs2int_ge0 /= /t; pose r := rev _.
    suff ->: a = size r; 1: by rewrite bs2int_le2Xs.
    rewrite /r size_rev. search size nth.
    have: all (((=) a) \o size) (chunk a (val mi.`1)).
    + rewrite allP => bs bsin.
      by rewrite /(\o) eq_sym (in_chunk_size a (val mi.`1)) //; smt(ge1_a).
    move/all_nthP => /= /(_ witness i _) //.
    by rewrite size_chunk 2:valP 2:mulzK; smt(ge1_a).
  qed.
  realize eqiks_g. by move=> x x' mi @/g /= /mkseqP [?] [? ->] /mkseqP [?] [? ->]. qed.
  realize neqisvs_g. 
    move=> x x' mi @/g /= /mkseqP [i] [rng_i ->] /mkseqP [j] [rng_j ->] /=. 
    by apply contra => ->.
  qed.
*)  
  realize dkey_ll by exact: dmkey_ll.


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

clone TweakableHashFunctions as F with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,
  
    op f <- f,
  
    op dpp <- dpseed
    
  proof *.
  realize dpp_ll by exact: dpseed_ll.

(*
clone import F.SMDTTCR as F_TCR with
  op t_smdttcr <- d * k * t
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).
*)
clone import F.SMDTOpenPRE as F_OpenPRE with
  op t_smdtopenpre <- d * k * t,
  
  op din <- ddgstblocklift
    
  proof *.
  realize ge0_tsmdtopenpre by smt(ge1_d ge1_k ge2_t).
  realize din_ll by exact: ddgstblocklift_ll.

clone import F.Collection as FC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n).
(*
clone import FC.SMDTOpenPREC as FC_OpenPRE with
  op t_smdtopenpre <- d * k * t,
  
  op din <- ddgstblocklift
    
  proof *.
  realize ge0_tsmdtopenpre by smt(ge1_d ge1_k ge2_t).
  realize din_ll by exact: ddgstblocklift_ll.
*)    
clone import FC.SMDTTCRC as FC_TCR with
  op t_smdttcr <- d * k * t
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).

(* (Explicitly) Domain-restricted version of f; used for DSPR-related proofs  *)
op f' (ps : pseed) (ad : adrs) (x : dgstblock) : dgstblock = 
  f ps ad (val x).

clone import OpenPRE_From_TCR_DSPR_THF as FP_OPRETCRDSPR with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgstblock,
  type out_t <- dgstblock,
      
    op f <- f',
    
    op t <- d * k * t,
    
    op dpp <- dpseed,
    op din <- ddgstblock,
    
  theory InFT <= DigestBlockFT
  
  rename [theory] "F" as "FP"
  rename [theory] "F_OpenPRE" as "FP_OpenPRE"
  rename [theory] "F_TCR" as "FP_TCR"
  rename [theory] "F_DSPR" as "FP_DSPR" 
  
  proof *.
  realize dpp_ll by exact: dpseed_ll.
  realize din_ll by exact: ddgstblock_ll.
  realize din_fu by exact: ddgstblock_fu.
  realize din_uni by exact: ddgstblock_uni.
  realize ge0_t by smt(ge2_t ge1_k ge1_d).

(* Tweakable hash function used to construct Merkle trees from leaves
op trh : pseed -> adrs -> dgst -> dgstblock.
*)
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

(*
clone import TRH.SMDTTCR as TRH_TCR with
  op t_smdttcr <- d * k * (t - 1)
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).
*)

clone import TRH.Collection as TRHC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n * 2).

clone import TRHC.SMDTTCRC as TRHC_TCR with
  op t_smdttcr <- d * k * (t - 1)
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k ge2_t).

(* Tweakable hash function used compress Merkle tree roots to public key
op trco : pseed -> adrs -> dgst -> dgstblock.
*)
op trco : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * k).

clone TweakableHashFunctions as TRCO with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,
  
    op f <- trco,
  
    op dpp <- dpseed
    
  proof *.
  realize dpp_ll by exact: dpseed_ll.
(*
clone import TRCO.SMDTTCR as TRCO_TCR with
  op t_smdttcr <- d * k
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k).
*)
  
clone import TRCO.Collection as TRCOC with
  type diff_t <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n * k).

clone import TRCOC.SMDTTCRC as TRCOC_TCR with
  op t_smdttcr <- d * k
  
  proof *.
  realize ge0_tsmdttcr by smt(ge1_d ge1_k).


(* -- Merkle trees -- *)
(* Update function for height and breadth indices (down the tree) *)
op updhbidx (hbidx : int * int) (b : bool) : int * int = 
  (hbidx.`1 - 1, if b then 2 * hbidx.`2 + 1 else 2 * hbidx.`2).

(* Function around trh with desired form for use in abstract merkle tree operators  *)
op trhi (ps : pseed) (ad : adrs) (hbidx : int * int) (x x' : dgstblock) : dgstblock =
  trh ps (set_thtbidx ad hbidx.`1 hbidx.`2) (val x ++ val x').
  
(*
(* 
  Computes the (hash) value corresponding to the root of the binary tree w.r.t.
  a certain public seed, address, height index, and breadth index. 
*)
op val_bt_trh (bt : dgstblock bintree) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock =
  with bt = Leaf x => x
  with bt = Node l r => 
    trh ps (set_thtbidx ad hidx bidx) 
        (val (val_bt_trh l ps ad (hidx - 1) (2 * bidx)) ++ val (val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1))).
*)
op val_bt_trh_gen (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (hidx bidx : int) : dgstblock =
  val_bt (trhi ps ad) updhbidx bt (hidx, bidx).

op val_bt_trh (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (bidx : int) : dgstblock =
  val_bt_trh_gen ps ad bt a bidx.
  
(*     
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
*)
op cons_ap_trh_gen (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (bs : bool list) (hidx bidx : int) : dgstblock list =
  cons_ap (trhi ps ad) updhbidx bt bs (hidx, bidx).


(*
(* 
  Constructs authentication path (embedding it in the corresponding subtype)
  for the special case of binary trees of height a w.r.t. a certain public seed, address, 
  height index a, and breadth index bidx. Here, idx should be a valid leaf index (i.e., in [0, 2 ^ a -1])
  and bidx should be a valid breadth index for root nodes of the Merkle trees in a FORS-TW 
  instance (i.e., in [0, k - 1]).
*)
op cons_ap_trh (bt : dgstblock bintree) (idx : int) (ps : pseed) (ad : adrs) (bidx : int) : apFORSTW =
  DBAL.insubd (cons_ap_trh_gen bt (rev (int2bs a idx)) ps ad a bidx).
*)
op cons_ap_trh (ps : pseed) (ad : adrs) (bt : dgstblock bintree) (idx : int) (bidx : int) : apFORSTW =
  DBAL.insubd (cons_ap_trh_gen ps ad bt (rev (int2bs a idx)) a bidx).

  
(*
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
*)
op val_ap_trh_gen (ps : pseed) (ad : adrs) (ap : dgstblock list) (bs : bool list) (leaf : dgstblock) (hidx bidx : int) : dgstblock =
  val_ap (trhi ps ad) updhbidx ap bs leaf (hidx, bidx).

(*
(* 
  Computes value corresponding to an authentication path, leaf, and a path represented 
  by the big-endian binary representation of an index  w.r.t. a certain public seed, address, 
  height index a, and breadth index bidx. Here, idx should be a valid leaf index (i.e., in [0, 2 ^ a - 1])
  and bidx should be a valid breadth index for root nodes of the Merkle trees in a FORS-TW 
  instance (i.e., in [0, k - 1]).
*)
op val_ap_trh (ap : apFORSTWTW) (idx : int) (leaf : dgstblock) (ps : pseed) (ad : adrs) (bidx : int) : dgstblock = 
  val_ap_trh_gen (val ap) (rev (int2bs a idx)) leaf ps ad a bidx.
*)

op val_ap_trh (ps : pseed) (ad : adrs) (ap : apFORSTW) (idx : int) (leaf : dgstblock) (bidx : int) : dgstblock =
  val_ap_trh_gen ps ad (val ap) (rev (int2bs a idx)) leaf a bidx. 

(* 
  Extracts collision from original binary tree (bt) and 
  an authentication path/leaf (ap, bs, leaf), if any. 
*)
op extract_collision_bt_ap_trh (ps : pseed) 
                               (ad : adrs) 
                               (bt : dgstblock bintree) 
                               (ap : dgstblock list) 
                               (bs : bool list) 
                               (leaf : dgstblock) 
                               (bidx : int) =
  extract_collision_bt_ap (trhi ps ad) updhbidx bt ap bs leaf (a, bidx).



(* - Types (3/3) - *)
(* 
  FORS-TW addresses 
  Only used to select arbitrary valid FORS-TW in security notion/reductions 

clone import Subtype as FHA with
  type T <= adrs,
    op P ad <= valid_fadrs ad. 
  
type fadrs = FHA.sT.
*)
lemma vkpidx_setkpttype (i j t : int) (ad : adrs) :
     valid_fadrs ad
  => valid_tidx i
  => t = trhtype \/ t = trcotype
  => valid_kpidx j
  => valid_kpidx (get_kpidx (set_kpidx (set_tidx (set_typeidx ad t) i) j)).
proof.
move=> vad vi vt vj.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
rewrite /get_kpidx /set_typeidx /set_tidx /set_idx insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39://
          1..20:gtif_szad 1..40:// /= ?nth_take 1..2:// /=; smt(ge1_a ge1_k ge1_l nth_take IntOrder.expr_gt0).
rewrite /set_kpidx /set_idx insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 5?drop_put_out 1..5:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,
             37,39,41,43,45,47,49:// 1..25:gtif_szad 1..50:// /=; smt(ge1_a ge1_k nth_take IntOrder.expr_gt0).
rewrite /get_idx insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59:// 1..30:gtif_szad 1..60:// /= vi vj /=; smt(ge1_a ge1_k nth_take IntOrder.expr_gt0).
by rewrite /valid_kpidx ?nth_put ?size_put 7:// /#.
qed.

lemma gettype_setthtbkptypetrh (i j u v : int) (ad : adrs) :
     valid_fidxvalsgp (drop 5 (val ad))
  => valid_tidx (nth witness (val ad) 4)
  => valid_tidx i
  => valid_kpidx j
  => valid_thidx u
  => valid_tbidx u v
  => get_typeidx (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) u v) = trhtype.
proof.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> vadgp vti vi vj vu vv @/get_typeidx @/set_typeidx @/set_tidx @/set_idx; rewrite insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39://
          1..20:gtif_szad 1..40:// /= ?nth_take 1..2:// /=; smt(ge1_a ge1_k ge1_l IntOrder.expr_gt0).
rewrite /set_kpidx /set_idx insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 5?drop_put_out 1..5:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,
             37,39,41,43,45,47,49:// 1..25:gtif_szad 1..50:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0). 
rewrite /set_thtbidx /set_idx insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59:// 1..30:gtif_szad 1..60:// /= vi vj /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
rewrite /get_idx insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81:// 1..40:gtif_szad 1..80:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
by rewrite ?nth_put ?size_put 9:// /#.  
qed.


lemma gettype_setkp2type2trhtrco (i j j' : int) (ad : adrs) :
     valid_fidxvalsgp (drop 5 (val ad))
  => valid_tidx (nth witness (val ad) 4)
  => valid_tidx i
  => valid_kpidx j
  => valid_kpidx j'
  => get_typeidx (set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) trcotype) j') = trcotype.
proof.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> vadgp vti vi vj vjp @/get_typeidx @/set_typeidx @/set_tidx @/set_idx.
rewrite (insubdK (put _ _ trhtype)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39://
          1..20:gtif_szad 1..40:// /= ?nth_take 1..2:// /=; smt(ge1_a ge1_k ge1_l IntOrder.expr_gt0).
rewrite /set_kpidx /set_idx (insubdK (put _ 4 i)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 5?drop_put_out 1..5:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,
             37,39,41,43,45,47,49:// 1..25:gtif_szad 1..50:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0). 
rewrite (insubdK (put _ 2 j)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59:// 1..30:gtif_szad 1..60:// /= vi vj /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
rewrite insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..10:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99:// 
             1..50:gtif_szad 1..100:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
rewrite /get_idx insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..11:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99,101,103,105,107,109://
             1..55:gtif_szad 1..110:// /=; smt(ge1_a ge1_k IntOrder.expr_gt0).
by rewrite ?nth_put ?size_put 12:// /#.  
qed.


lemma getth_setthtbkpttype (i j u v: int) (ad : adrs) :
     valid_fadrs ad
  => valid_tidx i
  => valid_kpidx j
  => valid_thidx u
  => valid_tbidx u v
  => get_thidx (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) u v) = u.
proof.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> vad vi vj vu vv @/set_typeidx @/set_tidx @/set_idx.
rewrite (insubdK (put _ _ trhtype)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39://
          1..20:gtif_szad 1..40:// /= ?nth_take 1..2:// /=; smt(ge1_a ge1_k ge1_l nth_take IntOrder.expr_gt0).
rewrite /set_kpidx /set_idx (insubdK (put _ 4 i)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp 5?drop_put_out 1..5:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,
             37,39,41,43,45,47,49:// 1..25:gtif_szad 1..50:// /=; smt(ge1_a ge1_k nth_take IntOrder.expr_gt0). 
rewrite /set_thtbidx /set_idx insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59:// 1..30:gtif_szad 1..60:// /= vi vj /=; smt(ge1_a ge1_k nth_take IntOrder.expr_gt0).
rewrite /get_thidx /get_idx insubdK. 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrco /valid_fidxvalslptrh.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,
             57,59,61,63,65,67,69,71,73,75,77,79,81:// 1..40:gtif_szad 1..80:// /=; smt(ge1_a ge1_k nth_take IntOrder.expr_gt0).
by rewrite ?nth_put ?size_put 9:// /#.  
qed.

lemma neqtidx_setthtbkpt (i i' j j' u u' v v' : int) (ad : adrs)  :
     valid_fadrs ad
  => valid_tidx i
  => valid_tidx i'
  => valid_kpidx j
  => valid_kpidx j'
  => valid_thidx u
  => valid_thidx u'
  => valid_tbidx u v
  => valid_tbidx u' v'
  => i <> i'
  => nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) u v)) 4  
     <> 
     nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i') j') u' v')) 4.
proof.
move=> vad vi vip vj vjp vu vup vv vvp neqip_i.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> @/set_tidx @/set_typeidx @/set_idx.  
rewrite (Adrs.insubdK (put _ 3 _)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// 4?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take 
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41:// 
             1..20:gtif_szad 1..40:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite /set_kpidx /set_idx (Adrs.insubdK (put _ 4 i)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite (Adrs.insubdK (put _ 4 i')). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite /set_thtbidx /set_idx (Adrs.insubdK (put _ 2 j)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite  (Adrs.insubdK (put _ 2 j')).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite ?nth_put ?size_put 17:// /#.
qed.


lemma neqkpidx_setthtbkpt (i i' j j' u u' v v' : int) (ad : adrs)  :
     valid_fadrs ad
  => valid_tidx i
  => valid_tidx i'
  => valid_kpidx j
  => valid_kpidx j'
  => valid_thidx u
  => valid_thidx u'
  => valid_tbidx u v
  => valid_tbidx u' v'
  => j <> j'
  => nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) u v)) 2  
     <> 
     nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i') j') u' v')) 2.
proof.
move=> vad vi vip vj vjp vu vup vv vvp neqip_i.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> @/set_tidx @/set_typeidx @/set_idx.  
rewrite (Adrs.insubdK (put _ 3 _)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// 4?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take 
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41:// 
             1..20:gtif_szad 1..40:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite /set_kpidx /set_idx (Adrs.insubdK (put _ 4 i)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite (Adrs.insubdK (put _ 4 i')). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite /set_thtbidx /set_idx (Adrs.insubdK (put _ 2 j)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite  (Adrs.insubdK (put _ 2 j')).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite ?nth_put ?size_put 17:// /#.
qed.

lemma neqthidx_setthtbkpt (i i' j j' u u' v v' : int) (ad : adrs)  :
     valid_fadrs ad
  => valid_tidx i
  => valid_tidx i'
  => valid_kpidx j
  => valid_kpidx j'
  => valid_thidx u
  => valid_thidx u'
  => valid_tbidx u v
  => valid_tbidx u' v'
  => u <> u'
  => nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) u v)) 1
     <> 
     nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i') j') u' v')) 1.
proof.
move=> vad vi vip vj vjp vu vup vv vvp neqip_i.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> @/set_tidx @/set_typeidx @/set_idx.  
rewrite (Adrs.insubdK (put _ 3 _)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// 4?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take 
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41:// 
             1..20:gtif_szad 1..40:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite /set_kpidx /set_idx (Adrs.insubdK (put _ 4 i)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite (Adrs.insubdK (put _ 4 i')). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite /set_thtbidx /set_idx (Adrs.insubdK (put _ 2 j)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite  (Adrs.insubdK (put _ 2 j')).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite ?nth_put ?size_put 17:// /#.
qed.


lemma neqtbidx_setthtbkpt (i i' j j' u u' v v' : int) (ad : adrs)  :
     valid_fadrs ad
  => valid_tidx i
  => valid_tidx i'
  => valid_kpidx j
  => valid_kpidx j'
  => valid_thidx u
  => valid_thidx u'
  => valid_tbidx u v
  => valid_tbidx u' v'
  => v <> v'
  => nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i) j) u v)) 0
     <> 
     nth witness (val (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) i') j') u' v')) 0.
proof.
move=> vad vi vip vj vjp vu vup vv vvp neqip_i.
have gtif_szad : forall i, i < 5 => i < if 5 < size (val ad) then 5 else size (val ad) by smt(Adrs.valP ge5_adrslen).
move=> @/set_tidx @/set_typeidx @/set_idx.  
rewrite (Adrs.insubdK (put _ 3 _)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp 4?drop_put_out 1..4:// 4?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take 
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41:// 
             1..20:gtif_szad 1..40:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite /set_kpidx /set_idx (Adrs.insubdK (put _ 4 i)). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite (Adrs.insubdK (put _ 4 i')). 
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  move: vad => @/valid_fadrs @/valid_fadrsidxs [eqszad].
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49://
             1..25:gtif_szad 1..50:// /= ?nth_take 1..10://; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite /set_thtbidx /set_idx (Adrs.insubdK (put _ 2 j)).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).            
rewrite  (Adrs.insubdK (put _ 2 j')).
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..6:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59:// 1..30:gtif_szad 
             1..60:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite Adrs.insubdK.
+ rewrite /valid_adrsidxs valid_fidxvals_idxvals 2:?size_put; 2: smt(Adrs.valP).
  rewrite /valid_fidxvals /valid_fidxvalslp ?drop_put_out 1..8:// ?take_put /=.
  rewrite /valid_fidxvalslptrh /valid_fidxvalslptrco.
  by rewrite ?nth_put ?size_put ?size_take
             1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,
             45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79:// 1..40:gtif_szad 
             1..80:// /=; smt(ge1_k ge1_a Top.ge1_l ge2_t).
rewrite ?nth_put ?size_put 17:// /#.
qed.


(*
  nth witness
  (val
     (set_thtbidx
        (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (u %/ (l * k * t)))
           (u %% (l * k * t) %/ (k * t))) 0 (u %% (k * t) %/ t * t + u %% t))) 4 <>
nth witness
  (val
     (set_thtbidx
        (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (v %/ (l * k * t)))
           (v %% (l * k * t) %/ (k * t))) 0 (v %% (k * t) %/ t * t + v %% t))) 4
*)

lemma ltlltr (x x' y y' c : int) :
     0 <= c
  => 0 <= y'
  => x < x'
  => y < c
  => x * c + y
     <
     x' * c + y'.
proof. smt(). qed.

lemma leller (x x' y y' c : int) :
     0 <= c
  => 0 <= y'
  => x < x'
  => y <= c
  => x * c + y
     <=
     x' * c + y'.
proof. smt(). qed.

lemma neqsmnt (x x' y y' z z' c c') :
     0 <= y < c
  => 0 <= y' < c
  => 0 <= z < c'
  => 0 <= z' < c'
  => x <> x' \/ y <> y' \/ z <> z'
  => x * c * c' + y * c' + z
     <>  
     x' * c * c' + y' * c' + z'.
proof.
move=> rng_y rng_yp rng_z rng_zp.
case (x <> x') => [/= | /= -> /#].
rewrite 2!neq_ltz => -[ltxp_x | ltx_xp]; [left | right].
+ by rewrite -?addrA -?mulrA ltlltr 1..4:/#.
by rewrite -?addrA -?mulrA ltlltr 1..4:/#.
qed.

lemma ltnn1_bignna (v w : int) :
     0 <= v < a
  => 0 <= w < nr_nodes (v + 1)
  => bigi predT nr_nodes 1 (v + 1) + w < 2 ^ a - 1.
proof.
move=> [ge0_v lthp_v] [ge0_w @/nr_nodes ltnnu1_w].
rewrite (: 2 ^ a - 1 = bigi predT nr_nodes 1 (a + 1)).
+ rewrite eq_sym /nr_nodes; have ge0_a: 0 <= a by smt(ge1_a).
  rewrite (big_reindex _ _ (fun i => a - i) (fun i => a - i)).
  + by move=> i /mem_range rng_i /= /#.
  rewrite /(\o) /predT /= -/predT (eq_bigr _ _ (fun i => 2 ^ i)) => [i _ /= /# |].
  rewrite (eq_big_perm _ _ _ (range 0 a)).
  - rewrite uniq_perm_eq_size 2:range_uniq 2:size_map 2:?size_range 2://.
    * by rewrite map_inj_in_uniq 2:range_uniq => i j rng_i rng_j /= /#.
    by move=> i /mapP [j] [/mem_range rng_j /= ->]; rewrite mem_range; smt(ge1_a).
  elim: a ge0_a=> [| i ge0_i ih]; 1: by rewrite expr0 big_geq.  
  by rewrite big_int_recr 1:// exprD_nneg 1,2:// /= ih expr1 /#.
rewrite (big_cat_int (v + 1) _ (a + 1)) 1,2:/# ltr_add2l.
rewrite big_ltn 1:/#; suff /# : 0 <= bigi predT nr_nodes (v + 2) (a + 1).
by rewrite sumr_ge0 => ? _; rewrite expr_ge0.
qed.


(* - Specifications - *)
(* -- With PRF -- *)
(* 
  Fixed-Length FORS-TW in Encompassing Structure.
  Auxiliary scheme to simplify specification of multi-instance FORS-TW scheme.
  Represents single FORS-TW instance that signs fixed-length messages. 
*)
module FL_FORS_TW_ES = {
  proc gen_leaves_single_tree(idxt : int, ss : sseed, ps : pseed, ad : adrs) : dgstblock list = {
    var skFORS_ele : dgstblock;
    var leaf : dgstblock;
    var leaves : dgstblock list;
    
    leaves <- [];
    while (size leaves < t) {
      skFORS_ele <- skg ss (ps, set_thtbidx ad 0 (idxt * t + size leaves));
      leaf <- f ps (set_thtbidx ad 0 (idxt * t + size leaves)) (val skFORS_ele);
      leaves <- rcons leaves leaf;
    }
    
    return leaves;
  }
  
  proc gen_pkFORS(ss : sseed, ps : pseed, ad : adrs) : pkFORS = {
    var pkFORS : dgstblock;
    var leaves : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var kpidx : int;
    
    roots <- [];
    while (size roots < k) {
      leaves <@ gen_leaves_single_tree(size roots, ss, ps, ad); 
      root <- val_bt_trh ps ad (list2tree leaves) (size roots);
      roots <- rcons roots root;
    }
     
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;  
  }
  
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : pkFORSTW * skFORSTW =  {
    var pkFORS : pkFORS;
    var pk : pkFORSTW;
    var sk : skFORSTW;
    
    pkFORS <@ gen_pkFORS(ss, ps, ad);
    
    pk <- (pkFORS, ps, ad);
    sk <- (ss, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : skFORSTW, m : msgFORSTW) : sigFORSTW = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var bsidx : bool list;
    var idx : int;
    var skFORS_ele : dgstblock;
    var leaves : dgstblock list;
    var ap : apFORSTW;
    var sig : (dgstblock * apFORSTW) list;
    
    (ss, ps, ad) <- sk;
    
    sig <- [];
    while (size sig < k) {
      bsidx <- take a (drop (a * (size sig)) (val m));  
      idx <- bs2int (rev bsidx);
      skFORS_ele <- skg ss (ps, set_thtbidx ad 0 (size sig * t + idx));
      leaves <@ gen_leaves_single_tree(size sig, ss, ps, ad);
      ap <- cons_ap_trh ps ad (list2tree leaves) idx (size sig);
      sig <- rcons sig (skFORS_ele, ap);
    }
    
    return insubd sig;
  }
  
  proc pkFORS_from_sigFORSTW(sig : sigFORSTW, m : msgFORSTW, ps : pseed, ad : adrs) : pkFORS = {
    var skFORS_ele : dgstblock;
    var ap : apFORSTW;
    var leaf : dgstblock;
    var bsidx : bool list;
    var idx : int;
    var roots : dgstblock list;
    var root : dgstblock;
    var pkFORS : pkFORS;
    
    roots <- [];
    while (size roots < k) {
      bsidx <- take a (drop (a * (size roots)) (val m));  
      idx <- bs2int (rev bsidx);
      (skFORS_ele, ap) <- nth witness (val sig) (size roots);
      leaf <- f ps (set_thtbidx ad 0 (size roots * t + idx)) (val skFORS_ele);
      root <- val_ap_trh ps ad ap idx leaf (size roots);
      roots <- rcons roots root;
    }
    
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;
  }
  
  proc verify(pk : pkFORSTW, m : msgFORSTW, sig : sigFORSTW) : bool = {
    var ps : pseed;
    var ad : adrs;
    var pkFORS, pkFORS' : pkFORS;
    
    (pkFORS, ps, ad) <- pk;
    
    pkFORS' <@ pkFORS_from_sigFORSTW(sig, m, ps, ad);
    
    return pkFORS' = pkFORS;
  } 
}.

(* 
  Multi-instance FORS-TW in Encompassing Structure.
*)
module M_FORS_TW_ES = {
  proc gen_pkFORSs (ss : sseed, ps : pseed, ad : adrs) : pkFORS list list = {
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    var pkFORSs : pkFORS list list;
     
    (* 
      Total of d instances, but these are divided in 
      s sets (SPHINCS+: XMSS instances on bottom layer) 
      each containing l instances (SPHINCS+: leaves of XMSS instance on bottom layer)
    *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        pkFORS <@ FL_FORS_TW_ES.gen_pkFORS(ss, ps, set_kpidx (set_tidx ad (size pkFORSs)) (size pkFORSl));
        pkFORSl <- rcons pkFORSl pkFORS; 
      }
      
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
    
    return pkFORSs;
  }
   
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : (pkFORS list list * pseed * adrs) * (mseed * sseed * pseed * adrs) =  {
    var ms : mseed;
    var pkFORSs : pkFORS list list;
    var pk : (pkFORS list list * pseed * adrs);
    var sk : mseed * sseed * pseed * adrs;
    
    ms <$ dmseed;
    
    pkFORSs <@ gen_pkFORSs(ss, ps, set_typeidx ad trhtype);
    
    pk <- (pkFORSs, ps, ad);
    sk <- (ms, ss, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : mseed * sseed * pseed * adrs, m : msg) : mkey * sigFORSTW = {
    var ms : mseed;
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sig : sigFORSTW;
    
    (ms, ss, ps, ad) <- sk;
    
    (* rm <$ drm; *)
    (* mk <- mkg ms (rm, m); *)
    mk <- mkg ms m;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    sig <@ FL_FORS_TW_ES.sign((ss, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
    return (mk, sig);
  }
  
  proc verify(pk : pkFORS list list * pseed * adrs, m : msg, sig : mkey * sigFORSTW) : bool = {
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var sigFORSTW : sigFORSTW;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var is_valid : bool; 
        
    (pkFORSl, ps, ad) <- pk;
    (mk, sigFORSTW) <- sig;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    pkFORS <- nth witness (nth witness pkFORSl tidx) kpidx;
    
    is_valid <@ FL_FORS_TW_ES.verify((pkFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm, sigFORSTW);
    
    return is_valid;
  } 
}.


(* -- Without PRF -- *)
(* 
  Fixed-Length FORS-TW in Encompassing Structure (No PRF).
  Auxiliary scheme to simplify specification of multi-instance FORS-TW scheme.
  Represents single FORS-TW instance that signs fixed-length messages. 
*)
module FL_FORS_TW_ES_NPRF = {
  proc gen_leaves_single_tree(idxt : int, skFORS : skFORS, ps : pseed, ad : adrs) : dgstblock list = {
    var skFORS_ele : dgstblock;
    var leaf : dgstblock;
    var leaves : dgstblock list;
    
    leaves <- [];
    while (size leaves < t) {
      skFORS_ele <- nth witness (nth witness (val skFORS) idxt) (size leaves);
      leaf <- f ps (set_thtbidx ad 0 (idxt * t + size leaves)) (val skFORS_ele);
      leaves <- rcons leaves leaf;
    }
    
    return leaves;
  }
  
  proc gen_skFORS() : skFORS = {
    var skFORS_ele : dgstblock;
    var skFORSt : dgstblock list;
    var skFORS : dgstblock list list;
    
    skFORS <- [];
    while (size skFORS < k) {
      skFORSt <- [];
      while (size skFORSt < t) {
        skFORS_ele <$ ddgstblock;
        skFORSt <- rcons skFORSt skFORS_ele;
      }
      skFORS <- rcons skFORS skFORSt;  
    }
    
    return insubd skFORS;
  }
  
  proc gen_pkFORS(skFORS : skFORS, ps : pseed, ad : adrs) : pkFORS = {
    var pkFORS : dgstblock;
    var leaves : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    
    roots <- [];
    while (size roots < k) {
      leaves <@ gen_leaves_single_tree(size roots, skFORS, ps, ad); 
      root <- val_bt_trh ps ad (list2tree leaves) (size roots);
      roots <- rcons roots root;
    }
     
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;
  }
  
  proc keygen(ps : pseed, ad : adrs) : pkFORSTW * (skFORS * pseed * adrs) =  {
    var ms : mseed;
    var pkFORS : pkFORS;
    var skFORS : skFORS;
    var pk : pkFORSTW;
    var sk : skFORS * pseed * adrs;
    
    skFORS <@ gen_skFORS();
    
    pkFORS <@ gen_pkFORS(skFORS, ps, ad);
    
    pk <- (pkFORS, ps, ad);
    sk <- (skFORS, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : skFORS * pseed * adrs, m : msgFORSTW) : sigFORSTW = {
    var skFORS : skFORS;
    var ps : pseed;
    var ad : adrs;
    var bsidx : bool list;
    var idx : int;
    var skFORS_ele : dgstblock;
    var leaves : dgstblock list;
    var ap : apFORSTW;
    var sig : (dgstblock * apFORSTW) list;
    
    (skFORS, ps, ad) <- sk;
    
    sig <- [];
    while (size sig < k) {
      bsidx <- take a (drop (a * (size sig)) (val m));  
      idx <- bs2int (rev bsidx);
      skFORS_ele <- nth witness (nth witness (val skFORS) (size sig)) idx;
      leaves <@ gen_leaves_single_tree(size sig, skFORS, ps, ad);
      ap <- cons_ap_trh ps ad (list2tree leaves) idx (size sig);
      sig <- rcons sig (skFORS_ele, ap);
    }
    
    return insubd sig;
  }
  
  proc verify = FL_FORS_TW_ES.verify
(*  
  proc pkFORS_from_sigFORSTW(sig : sigFORSTW, m : msgFORSTW, ps : pseed, ad : adrs) : pkFORS = {
    var skFORS_ele : dgstblock;
    var ap : apFORSTW;
    var leaf : dgstblock;
    var bsidx : bool list;
    var idx : int;
    var roots : dgstblock list;
    var root : dgstblock;
    var pkFORS : pkFORS;
    
    roots <- [];
    while (size roots < k) {
      bsidx <- take a (drop (a * (size roots)) (val m));  
      idx <- bs2int (rev bsidx);
      (skFORS_ele, ap) <- nth witness (val sig) (size roots);
      leaf <- f ps (set_thtbidx ad 0 (size roots * t + idx)) (val skFORS_ele);
      root <- val_ap_trh ps ad ap idx leaf (size roots);
      roots <- rcons roots root;
    }
    
    pkFORS <- trco ps (set_kpidx (set_typeidx ad trcotype) (get_kpidx ad)) (flatten (map DigestBlock.val roots));
    
    return pkFORS;
  }
  
  proc verify(pk : pkFORSTW, m : msgFORSTW, sig : sigFORSTW) : bool = {
    var ps : pseed;
    var ad : adrs;
    var pkFORS, pkFORS' : pkFORS;
    
    (pkFORS, ps, ad) <- pk;
    
    pkFORS' <@ pkFORS_from_sigFORSTW(sig, m, ps, ad);
    
    return pkFORS' = pkFORS;
  }
*) 
}.

(* 
  Multi-instance FORS-TW in Encompassing Structure (No PRF).
*)
module M_FORS_TW_ES_NPRF = {
  proc keygen(ps : pseed, ad : adrs) : (pkFORS list list * pseed * adrs) * (skFORS list list * pseed * adrs) =  {
    (*
    var ps : pseed;
    var ad : adrs;
    *)
    var skFORS : skFORS;
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    var skFORSl : skFORS list;
    var skFORSs : skFORS list list;
    var pkFORSs : pkFORS list list;
    var pk : (pkFORS list list * pseed * adrs);
    var sk : (skFORS list list * pseed * adrs);
    
    (*
    ps <$ dpseed;
    ad <- witness;
    *)
    
    (* 
      Total of d instances, but these are divided in 
      s sets (SPHINCS+: XMSS instances on bottom layer) 
      each containing l instances (SPHINCS+: leaves of XMSS instance on bottom layer)
    *)
    skFORSs <- [];
    pkFORSs <- [];
    while (size skFORSs < s) {
      skFORSl <- [];
      pkFORSl <- [];
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        pkFORS <@ FL_FORS_TW_ES_NPRF.gen_pkFORS(skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl));
        skFORSl <- rcons skFORSl skFORS;
        pkFORSl <- rcons pkFORSl pkFORS; 
      }
      
      skFORSs <- rcons skFORSs skFORSl;
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
        
    pk <- (pkFORSs, ps, ad);
    sk <- (skFORSs, ps, ad);
    
    return (pk, sk);
  }
(*  
  proc sign(sk : skFORS list list * pseed * adrs, m : msg) : mkey * sigFORSTW = {
    var skFORS : skFORS;
    var skFORSs : skFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sig : sigFORSTW;
    
    (skFORSs, ps, ad) <- sk;
    
    mk <$ dmkey;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
     
    sig <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
    return (mk, sig);
  }
*)  
  proc verify = M_FORS_TW_ES.verify
(*  
  proc verify(pk : pkFORS list list * pseed * adrs, m : msg, sig : mkey * sigFORSTW) : bool = {
    var pkFORS : pkFORS;
    var pkFORSs : pkFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var sigFORSTWTW : sigFORSTW;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var is_valid : bool; 
        
    (pkFORSs, ps, ad) <- pk;
    (mk, sigFORSTWTW) <- sig;
    
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    pkFORS <- nth witness (nth witness pkFORSs tidx) kpidx;
    
    is_valid <@ FL_FORS_TW_ES_NPRF.verify((pkFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm, sigFORSTWTW);
    
    return is_valid;
  }
*) 
}.




(* - Proof - *)
(*
(* -- Import of relevant definitions and properties --  *)
clone import DigitalSignatures as DSS_MFORSTWESNPRF with
  type pk_t <- pkFORS list list * pseed * adrs,
  type sk_t <- skFORS list list * pseed * adrs,
  type msg_t <- msg,
  type sig_t <- mkey * sigFORSTWTW
  
  proof *.

import Stateless.
*)

(* -- Oracle interfaces -- *)
(*
module O_CMA_MFORSTWESNPRF = O_CMA_Default(M_FORS_TW_ES_NPRF).

module O_CMA_MFORSTWESNPRF_AV = {
  include var O_CMA_MFORSTWESNPRF [-init, sign] 
  
  var lidxs : (int * int * int) list
  
  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    O_CMA_MFORSTWESNPRF.init(sk);
    lidxs <- [];
  }
  
  proc sign(m : msg) : mkey * sigFORSTWTW = {
    var mk : mkey;
    var sigFORSTWTW : sigFORSTWTW;
    
    (mk, sigFORSTWTW) <@ O_CMA_MFORSTWESNPRF.sign(m);
    
    lidxs <- lidxs ++ g (mco mk m);
    
    return (mk, sigFORSTWTW);  
  }
}. 
*)
module type Oracle_CMA_MFORSTWESNPRF = {
  proc init(sk_init : skFORS list list * pseed * adrs) : unit
  proc sign(m : msg) : mkey * sigFORSTW
  proc fresh(m : msg) : bool
  proc nr_queries() : int
}.

module type SOracle_CMA_MFORSTWESNPRF = {
  include Oracle_CMA_MFORSTWESNPRF [sign]
}.



(* -- Adversary classes -- *)
module type Adv_EUFCMA_MFORSTWESNPRF (O : SOracle_CMA_MFORSTWESNPRF) = {
  proc forge(pk : pkFORS list list * pseed * adrs) : msg * (mkey * sigFORSTW)
}.


(* -- Security notions -- *)
module EUF_CMA_MFORSTWESNPRF (A : Adv_EUFCMA_MFORSTWESNPRF, O : Oracle_CMA_MFORSTWESNPRF) = {
  proc main() : bool = {    
    var ad : adrs;
    var ps : pseed;
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;

    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);

    O.init(sk);

    (m', sig') <@ A(O).forge(pk);

    is_valid <@ M_FORS_TW_ES_NPRF.verify(pk, m', sig');

    is_fresh <@ O.fresh(m');

    return is_valid /\ is_fresh; 
  }
}.


(* -- Oracle implementations -- *)
(* Default implementation of CMA oracle used for EUF_CMA_MFORSTWESNPRF  *)
module O_CMA_MFORSTWESNPRF : Oracle_CMA_MFORSTWESNPRF = {
  var sk : skFORS list list * pseed * adrs
  var qs : msg list
  (*var rmmap : (rm * msg, mkey) fmap *)
  var mmap : (msg, mkey) fmap
  
  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    sk <- sk_init;
    qs <- [];
    mmap <- empty;
  }

  proc sign(m : msg) : mkey * sigFORSTW = {
    var skFORS : skFORS;
    var skFORSs : skFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sigFORSTW : sigFORSTW;
    
    (skFORSs, ps, ad) <- sk;
    
    (* rm <$ drm; *)
    
    if (m \notin mmap) { 
      mk <$ dmkey;
      mmap.[m] <- mk;
    }
    mk <- oget mmap.[m];
      
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
     
    sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
    qs <- rcons qs m;

    return (mk, sigFORSTW);
  }
    
  proc fresh(m : msg) : bool = {
    return ! m \in qs;
  }

  proc nr_queries() : int = {
    return size qs;
  }
}.

(* 
  As O_CMA_MFORSTWESNPRF, but additionally keeps track of 
  all indices resulting from applying the message compression on 
  the queried messaged
*) 
module O_CMA_MFORSTWESNPRF_AV : Oracle_CMA_MFORSTWESNPRF = {
  include var O_CMA_MFORSTWESNPRF [-init, sign]
  var mks : mkey list
  var lidxs : (int * int * int) list
  
  proc init(sk_init : skFORS list list * pseed * adrs) : unit = {
    O_CMA_MFORSTWESNPRF.init(sk_init);
    mks <- [];
    lidxs <- [];
  }

  proc sign(m : msg) : mkey * sigFORSTW = {
    var skFORS : skFORS;
    var skFORSs : skFORS list list;
    var ps : pseed;
    var ad : adrs;
    var mk : mkey;
    var cm : msgFORSTW;
    var idx : index;
    var tidx, kpidx : int;
    var sigFORSTW : sigFORSTW;
    
    (skFORSs, ps, ad) <- sk;
    
    if (m \notin mmap) { 
      mk <$ dmkey;
      mmap.[m] <- mk;
      mks <- rcons mks mk;
      lidxs <- lidxs ++ g (mco mk m);
      qs <- rcons qs m;
    }
    mk <- oget mmap.[m];
      
    (cm, idx) <- mco mk m;
    
    (tidx, kpidx) <- edivz (val idx) l;
    
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
     
    sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);

    return (mk, sigFORSTW);
  }
}.

(* -- Reduction adversaries -- *)
module (R_ITSR_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : Adv_ITSR) (O : Oracle_ITSR) = {  
  var ps : pseed
  var ad : adrs
  var skFORSs : skFORS list list
  var mmap : (msg, mkey) fmap
  
  module O_CMA_R_EUFCMA_ITSR : SOracle_CMA_MFORSTWESNPRF = {    
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx : int;
      var skFORS : skFORS;
      var sigFORSTW : sigFORSTW;
      
      if (m \notin mmap) {  
        mk <@ O.query(m);
        mmap.[m] <- mk;
      }
      mk <- oget mmap.[m]; 
      
      (cm, idx) <- mco mk m;
    
      (tidx, kpidx) <- edivz (val idx) l;

      skFORS <- nth witness (nth witness skFORSs tidx) kpidx;

      sigFORSTW <@ FL_FORS_TW_ES_NPRF.sign((skFORS, ps, set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx), cm);
    
      return (mk, sigFORSTW);
    }
  }
  
  proc find() : mkey * msg = {
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var mk' : mkey;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    
    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);    
    
    skFORSs <- sk.`1;
    mmap <- empty;
    
    (m', sig') <@ A(O_CMA_R_EUFCMA_ITSR).forge(pk);
    
    mk' <- sig'.`1;
    
    return (mk', m');
  }
}.
    
(* 
  One of the cases for forgery of FORS-TW is that one of the private key elements
  in the signature was not included in the responses to the adversary's queries, but it does
  map to the original corresnding leaf. Then, there are two possibilities:
  1. The private key element is the same as the original one. 
  2. The private key element is different than the original one.
  In the first case, we cannot directly reduce to PRE because this does not allow for
  answering signature queries from the FORS-TW adversary (since we would not know the
  private key elements corresponding to the leaves as these would be the pre-image
  challenges). So, we need to reduce to TopenPRE, which in turn reduces
  to DSPR + TCR (see DSPR/SPHINCS+ paper); might be able to directly reduce (i.e., not go via TopenPRE)
  In the second case, we can reduce to SMDTTCR.
module (R_FSMDTOpenPREC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : FC_OpenPRE.Adv_SMDTOpenPREC) (O : FC_OpenPRE.Oracle_SMDTOpenPRE, OC : FC.Oracle_THFC) = {
  var ps : pseed
  var ad : adrs
  var leavess : dgstblock list list list list
  var lidxs : (int * int * int) list
  (* var rmmap : (rm * msg, mkey) fmap *)
  var mmap : (msg, mkey) fmap
  
  module O_CMA_R_FSMDTOpenPREC_EUFCMA : SOracle_CMA_MFORSTWESNPRF = {
    (* Signing as with FORS-TW (No PRF), but obtain secret key elements from OpenPRE oracle *)
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx, lidx : int;
      var bslidx : bool list;
      var sigFORSTW : (dgstblock * apFORSTW) list;
      var leaves : dgstblock list;
      var skFORS_ele : dgst;
      var ap : apFORSTW;
      
      (* rm <$ drm; *)
    
      if (m \notin mmap) { 
        mk <$ dmkey;
        mmap.[m] <- mk;
      } else {
        mk <- oget mmap.[m];
      }

      (cm, idx) <- mco mk m;

      (tidx, kpidx) <- edivz (val idx) l;

      sigFORSTW <- [];
      while (size sigFORSTW < k) {
        bslidx <- take a (drop (a * (size sigFORSTW)) (val cm));  
        lidx <- bs2int (rev bslidx);
        skFORS_ele <@ O.open(tidx * l * k * t + kpidx * k * t + size sigFORSTW * t + lidx);
        leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) (size sigFORSTW);
        ap <- cons_ap_trh ps ad (list2tree leaves) lidx (size sigFORSTW);
        sigFORSTW <- rcons sigFORSTW (DigestBlock.insubd skFORS_ele, ap);
      }
      
      lidxs <- lidxs ++ g (cm, idx);
      
      return (mk, insubd sigFORSTW);
    }
  }

  proc pick() : unit = {
    var leaf : dgstblock;
    var leavest : dgstblock list;
    var leavesk : dgstblock list list;
    var leavesl : dgstblock list list list;
    
    (* Pick address *)
    ad <- adz;
    
    (* 
      Sample FORS-TW secret keys, specify each secret key element as target 
      and obtain corresponding leaves
    *)
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size leavess < s) {
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size leavesl < l) {
        leavesk <- [];
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Obtain the leaves by querying challenge oracle *)
          while (size leavest < t) {
            leaf <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size leavess)) (size leavesl)) 0 (size leavesk * t + size leavest));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        leavesl <- rcons leavesl leavesk;
      }
      leavess <- rcons leavess leavesl;
    }
  }
  
  proc find(ps_init : pseed) : int * dgst = {
    var pkFORSs : pkFORS list list;
    var pkFORSl : pkFORS list;
    var pkFORS : pkFORS;
    var roots : dgstblock list;
    var root : dgstblock;
    var leaves : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var lidxs' : (int * int * int) list;
    var tidx, kpidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var x' : dgstblock;
    var ap' : apFORSTW;
    
    (* Initialize module variables (for oracle use) *)
    ps <- ps_init;
    lidxs <- [];
    mmap <- empty;
    
    (* Compute public keys corresponding to previously computed secret keys/leaves *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- [];
        while (size roots < k) {
          leaves <- nth witness (nth witness (nth witness leavess (size pkFORSs)) (size pkFORSl)) (size roots);
          root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) (list2tree leaves) (size roots);
          roots <- rcons roots root;
        }
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }

    (* Ask adversary to forge *)
    (m', mksigFORSTW') <@ A(O_CMA_R_FSMDTOpenPREC_EUFCMA).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries. From this tuple, extract the inner tree
      index (which is also the index of the element in the forged signature
      that we want to extract)
    *)
    dfidx <- (nth witness lidxs' (find (fun i => ! i \in lidxs) lidxs')).`2;
    
    (* Get element from forged signature containing the non-matching secret key element  *)
    (x', ap') <- nth witness (val sigFORSTW') dfidx;

    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* 
      Compute index in the target list of the OpenPRE oracle for which x' is a collision.
      Since we queried the targets in order, starting from the left, this index is exactly
      the index of the secret key/leaf (for which x' is a collision) if you were to
      flatten the complete structure.
    *)
    cidx <- tidx * l * k * t + kpidx * k * t + dfidx * t + bs2int (rev (take a (drop (a * dfidx) (val cm'))));

    return (cidx, val x');
  }
}.
*) print FL_FORS_TW_ES_NPRF.

module (R_FSMDTOpenPRE_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : F_OpenPRE.Adv_SMDTOpenPRE) (O : F_OpenPRE.Oracle_SMDTOpenPRE) = {
  var ps : pseed
  var ad : adrs
  var lidxs : (int * int * int) list
  var leavess : dgstblock list
  (* var rmmap : (rm * msg, mkey) fmap *)
  var mmap : (msg, mkey) fmap
  
  module O_CMA : SOracle_CMA_MFORSTWESNPRF = {
    (* Signing as with FORS-TW (No PRF), but obtain secret key elements from OpenPRE oracle *)
    proc sign(m : msg) : mkey * sigFORSTW = {
      var mk : mkey;
      var cm : msgFORSTW;
      var idx : index;
      var tidx, kpidx, lidx : int;
      var bslidx : bool list;
      var sigFORSTW : (dgstblock * apFORSTW) list;
      var leaves : dgstblock list;
      var skFORS_ele : dgst;
      var ap : apFORSTW;
      
      (* rm <$ drm; *)
    
      if (m \notin mmap) { 
        mk <$ dmkey;
        mmap.[m] <- mk;
        lidxs <- lidxs ++ g (mco mk m);
      }
      mk <- oget mmap.[m];

      (cm, idx) <- mco mk m;

      (tidx, kpidx) <- edivz (val idx) l;

      sigFORSTW <- [];
      while (size sigFORSTW < k) {
        bslidx <- take a (drop (a * (size sigFORSTW)) (val cm));  
        lidx <- bs2int (rev bslidx);
        skFORS_ele <@ O.open(tidx * l * k * t + kpidx * k * t + size sigFORSTW * t + lidx);
        (* leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) (size sigFORSTW); *)
        leaves <- take t (drop (tidx * l * k * t + kpidx * k * t + size sigFORSTW * t) leavess);
        ap <- cons_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) lidx (size sigFORSTW);
        sigFORSTW <- rcons sigFORSTW (DigestBlock.insubd skFORS_ele, ap);
      }
      
      return (mk, insubd sigFORSTW);
    }
  }

  proc pick() : adrs list = {
    var adl : adrs list;
    var tidx, kpidx, tbidx : int;
    
    (* Pick address *)
    ad <- adz;
    
    adl <- [];
    tidx <- 0;
    while (tidx < s) {
      kpidx <- 0;
      while (kpidx < l) {
        tbidx <- 0;
        while (tbidx < k * t) {
          adl <- rcons adl (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 tbidx);
          tbidx <- tbidx + 1;
        }
        kpidx <- kpidx + 1;
      }
      tidx <- tidx + 1;
    }
    
    return adl;  
  }
  
  proc find(ps_init : pseed, leavess_init : dgstblock list) : int * dgst = {
    var pkFORSs : pkFORS list list;
    var pkFORSl : pkFORS list;
    var pkFORS : pkFORS;
    var roots : dgstblock list;
    var root : dgstblock;
    var leaves : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var lidxs' : (int * int * int) list;
    var tidx, kpidx, dfidx, dftidx, dflfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var x' : dgstblock;
    var ap' : apFORSTW;
    
    (* Initialize module variables (for oracle use) *)
    ps <- ps_init;
    leavess <- leavess_init;
    lidxs <- [];
    mmap <- empty;

    (*
    (* Compute public keys corresponding to previously computed secret keys/leaves *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- [];
        while (size roots < k) {
          leaves <- nth witness (nth witness (nth witness leavess (size pkFORSs)) (size pkFORSl)) (size roots);
          root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) (list2tree leaves) (size roots);
          roots <- rcons roots root;
        }
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
    *)
    
    (* Compute public keys corresponding to previously computed secret keys/leaves *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- [];
        while (size roots < k) {
       (* leaves <- nth witness (nth witness (nth witness leavess (size pkFORSs)) (size pkFORSl)) (size roots); *)
          leaves <- take t (drop (size pkFORSs * l * k * t + size pkFORSl * k * t + size roots * t) leavess); 
          root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) (list2tree leaves) (size roots);
          roots <- rcons roots root;
        }
        pkFORS <- trco ps (set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) trcotype) 
                                     (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl))))
                          (flatten (map DigestBlock.val roots));
        
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }

    (* Ask adversary to forge *)
    (m', mksigFORSTW') <@ A(O_CMA).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries.
    *)
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in lidxs) lidxs');
    
    (* Get element from forged signature containing the non-matching secret key element  *)
    (x', ap') <- nth witness (val sigFORSTW') dftidx;

    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* 
      Compute index in the target list of the OpenPRE oracle for which x' is a collision.
      Since we queried the targets in order, starting from the left, this index is exactly
      the index of the secret key/leaf (for which x' is a collision) if you were to
      flatten the complete structure.
    *)
    cidx <- tidx * l * k * t + kpidx * k * t + dftidx * t + dflfidx; (* bs2int (rev (take a (drop (a * dfidx) (val cm')))) *)

    return (cidx, val x');
  }
}.

module (R_FPOpenPRE_FOpenPRE (A :  Adv_EUFCMA_MFORSTWESNPRF) : FP_OpenPRE.Adv_SMDTOpenPRE) (O : FP_OpenPRE.Oracle_SMDTOpenPRE) = {
  module O_SMDTOpenPRE : F_OpenPRE.Oracle_SMDTOpenPRE = {
    include var F_OpenPRE.O_SMDTOpenPRE_Default [-open]     
    
    proc open(i : int) : dgst ={
      var x : dgstblock;
      
      x <@ O.open(i);
      
      return val x;
    }
  }
  
  proc pick() : adrs list = {
    var adl : adrs list;
    
    adl <@ R_FSMDTOpenPRE_EUFCMA(A, O_SMDTOpenPRE).pick();
    
    return adl;
  }
  
  proc find(ps : pseed, ys : dgstblock list) : int * dgstblock = {
    var i : int;
    var x : dgst;
    
    (i, x) <@ R_FSMDTOpenPRE_EUFCMA(A, O_SMDTOpenPRE).find(ps, ys);
    
    return (i, DigestBlock.insubd x);
  }
}.
 
(*
module (R_FSMDTTCRC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : FC_TCR.Adv_SMDTTCRC) (O : FC_TCR.Oracle_SMDTTCR, OC : FC.Oracle_THFC) = {
  var ad : adrs
  var skFORSs : skFORS list list
  var leavess : dgstblock list list list list
    
  proc pick() : unit = {
    var skFORS : skFORS;
    var skFORSl : skFORS list;
    var leaf : dgstblock;
    var leavest : dgstblock list;
    var leavesk : dgstblock list list;
    var leavesl : dgstblock list list list;
    
    (* Pick address *)
    ad <- adz;
    
    (* 
      Sample FORS-TW secret keys, specify each secret key element as target 
      and obtain corresponding leaves
    *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
        leavesk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying challenge oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 0 (size leavesk * t + size leavest), 
                            val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
    }
  }
  
  proc find(ps : pseed) : int * dgst = {
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    var pkFORSs : pkFORS list list;
    var leaves : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var tidx, kpidx, dfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var x' : dgstblock;
    var ap' : apFORSTW;
    var lidxs' : (int * int * int) list;
    
    (* Initialize CMA oracle *)
    O_CMA_MFORSTWESNPRF_AV.init((skFORSs, ps, ad));
    
    (* Compute public keys corresponding to previously computed secret keys/leaves *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- [];
        while (size roots < k) {
          leaves <- nth witness (nth witness (nth witness leavess (size pkFORSs)) (size pkFORSl)) (size roots);
          root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) (list2tree leaves) (size roots);
          roots <- rcons roots root;
        }
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }

    (* Ask adversary to forge *)
    (m', mksigFORSTW') <@ A(O_CMA_MFORSTWESNPRF_AV).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries. From this tuple, extract the inner tree
      index (which is also the index of the element in the forged signature
      that we want to extract)
    *)
    dfidx <- (nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs')).`2;
    
    (* Get element from forged signature containing the non-matching secret key element (pointed to by dfidx) *)
    (x', ap') <- nth witness (val sigFORSTW') dfidx;

    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* 
      Compute index of the element in the target list of the OpenPRE oracle for which x' is a collision.
      Note that, if you were to flatten the whole structure, i.e., sequence all (trees of) considered 
      FORS-TW instances, we have effectively queried the leaves from left to right.
    *)
    cidx <- tidx * l * k * t + kpidx * k * t + dfidx * t + bs2int (rev (take a (drop (a * dfidx) (val cm'))));

    return (cidx, val x');
  }
}.
*)
module (R_TRHSMDTTCRC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : TRHC_TCR.Adv_SMDTTCRC) (O : TRHC_TCR.Oracle_SMDTTCR, OC : TRHC.Oracle_THFC) = {
  var ad : adrs
  var skFORSs : skFORS list list
  var pkFORSs : pkFORS list list
  var leavess : dgstblock list list list list
  var nodess : dgstblock list list list list list
  var rootss : dgstblock list list list
  
  proc pick() : unit = {
    var skFORS : skFORS;
    var pkFORS : pkFORS;
    var skFORSl : skFORS list;
    var pkFORSl : pkFORS list;
    var leaf, lnode, rnode, node : dgstblock;
    var leavest, nodespl, nodescl, rootsk : dgstblock list;
    var leavesk, nodest, rootsl : dgstblock list list;
    var leavesl, nodesk : dgstblock list list list;
    var nodesl : dgstblock list list list list;
    
    (* Pick address *)
    ad <- adz;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    nodess <- [];
    rootss <- [];
    pkFORSs <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      nodesl <- [];
      rootsl <- [];
      pkFORSl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
        leavesk <- [];
        nodesk <- [];
        rootsk <- [];        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying family oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 
                                         0 (size leavesk * t + size leavest), 
                             val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          
          (* Compute the trees from the leaves by querying the challenge oracle *)
          nodest <- [];
          (* For each layer in a tree (of a FORS-TW instance)... *)
          while (size nodest < a) {
            (* Get nodes from the previous layer *)
            nodespl <- last leavest nodest;
            
            (* 
              Compute the nodes in the current layer by mapping the (concatenations of sibling) nodes
              from the previous layer, specifying each of these (concatenations of) nodes as targets
            *)
            nodescl <- [];
            while (size nodescl < nr_nodes (size nodest + 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              node <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size nodess)) (size nodesl)) 
                                          (size nodest + 1) (size nodesk * nr_nodes (size nodest + 1) + size nodescl), 
                              val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node; 
            }
            nodest <- rcons nodest nodescl;
          }
          
          leavesk <- rcons leavesk leavest;
          nodesk <- rcons nodesk nodest;
          rootsk <- rcons rootsk (nth witness (nth witness nodest (a - 1)) 0); (* Final computed node is the root *)
        }
        
        pkFORS <@ OC.query(set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) trcotype)
                                     (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl))), 
                          flatten (map DigestBlock.val rootsk));
                          
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
        nodesl <- rcons nodesl nodesk;
        rootsl <- rcons rootsl rootsk;
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
      nodess <- rcons nodess nodesl;
      rootss <- rcons rootss rootsl;
      pkFORSs <- rcons pkFORSs pkFORSl; 
    }
  }

(*
  proc pick() : unit = {
    var skFORS : skFORS;
    var skFORSl : skFORS list;
    var leaf, lnode, rnode, node : dgstblock;
    var leavest, nodespl, nodescl, rootsk : dgstblock list;
    var leavesk, nodest, rootsl : dgstblock list list;
    var leavesl, nodesk : dgstblock list list list;
    var nodesl : dgstblock list list list list;
    
    (* Pick address *)
    ad <- adz;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
        leavesk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying family oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 
                                         0 (size leavesk * t + size leavest), 
                             val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
    }

    (* 
      Compute nodes of trees corresponding to leaves, 
      specifying all concatenations of sibling nodes as targets 
    *)
    nodess <- [];
    rootss <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size nodess < s) {
      nodesl <- [];
      rootsl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size nodesl < l) {
        nodesk <- [];
        rootsk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size nodesk < k) { 
          nodest <- [];
          leavest <- nth witness (nth witness (nth witness leavess (size nodess)) (size nodesl)) (size nodesk);
          (* For each layer in a tree (of a FORS-TW instance)... *)
          while (size nodest < a) {
            (* Get nodes from the previous layer *)
            nodespl <- last leavest nodest;
            
            (* 
              Compute the nodes in the current layer by mapping the (concatenations of sibling) nodes
              from the previous layer, specifying each of these (concatenations of) nodes as targets
            *)
            nodescl <- [];
            while (size nodescl < nr_nodes (size nodest + 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              node <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size nodess)) (size nodesl)) 
                                          (size nodest + 1) (size nodesk * nr_nodes (size nodest + 1) + size nodescl), 
                              val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node; 
            }
            nodest <- rcons nodest nodescl;
          }
          nodesk <- rcons nodesk nodest;
          rootsk <- rcons rootsk (nth witness (nth witness nodest (a - 1)) 0); (* Final computed node is the root *)
        }
        nodesl <- rcons nodesl nodesk;
        rootsl <- rcons rootsl rootsk;
      }
      nodess <- rcons nodess nodesl;
      rootss <- rcons rootss rootsl;
    }
  }
*)  
  proc find(ps : pseed) : int * dgst = {
    var pkFORS : pkFORS;
    (*
    var pkFORSl : pkFORS list;
    var pkFORSs : pkFORS list list;
    *)
    var skFORS : skFORS;
    var skFORSt : dgstblock list;
    var leaves, sleaves, sleaves' : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var tidx, kpidx, hidx, bidx, dfidx, dftidx, dflfidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var x' : dgstblock;
    var ap' : apFORSTW;
    var leavesk : dgstblock list list;
    var leaf' : dgstblock;
    var bs' : bool list;
    var idx'' : int;
    var c : dgst;
    var lidxs' : (int * int * int) list;
    var cr;
    
    (* Initialize CMA oracle *)
    O_CMA_MFORSTWESNPRF_AV.init((skFORSs, ps, ad));
(*    
    (* Compute public keys corresponding to previously computed roots *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        roots <- nth witness (nth witness rootss (size pkFORSs)) (size pkFORSl);
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl)) (flatten (map DigestBlock.val roots));
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
*)
    (* Ask adversary to forge *)
    (m', mksigFORSTW') <@ A(O_CMA_MFORSTWESNPRF_AV).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
    (cm', idx') <- mco mk' m';
    
    (* 
      Compute (instance index, inner tree index, leaf index) tuples from 
      the compressed message and instance index 
    *)
    lidxs' <- g (cm', idx');
    
    (* 
      Find the (instance index, inner tree index, leaf index) tuple computed from
      the forgery message that did not yet occur in the tuples computed from 
      the messages in the oracle queries. From this tuple, extract the inner tree
      index (which is also the index of the element in the forged signature
      that we want to extract)
    *)
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs');
    
    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;

    (* Construct non-matching leaf from non-matching secret key value in forgery (pointed to by dftidx) *) 
    leaf' <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx))
               (val (nth witness (unzip1 (val sigFORSTW')) dftidx));

    (* Get/recompute (original) leaves of tree pointed to by dftidx in instance pointed to by kpidx in set pointed to by tidx *)
    (* leaves <- nth witness (nth witness (nth witness leavess tidx) kpidx) dftidx; *)
    skFORSt <- nth witness (val (nth witness (nth witness skFORSs tidx) kpidx)) dftidx;
    leaves <- mkseq (fun (i : int) => f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + i)) (val (nth witness skFORSt i))) t;
    root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) dftidx;
        
    (* 
      Get element from forged signature containing non-matching secret key element 
      that maps to non-matching leaf  
    *)
    (x', ap') <- nth witness (val sigFORSTW') dftidx;
    
    (* Extract colliding values from the original tree and the non-matching leaf/authentication path *)
    cr <- extract_collision_bt_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 
                                      (list2tree leaves) (val ap') (rev (int2bs a dflfidx)) 
                                      leaf' dftidx;
    
    (* Collision from leaf/authentication path *)
    c <- val cr.`3 ++ val cr.`4;
    
    (* Height and breadth indices of address under which the extracted values collide *)
    (hidx, bidx) <- cr.`5;
    
    (* 
      Compute index of the element in the target list of the SMDDTTCR oracle for which c is a collision.
      Note that, if you were to flatten the whole structure, i.e., sequence all (trees of) considered 
      FORS-TW instances, we have effectively queried the complete trees from left to right; for each 
      tree, have effectively queried bottom-up layer-wise; and, for each layer, we
      queried from left to right.
    *)
    cidx <- tidx * l * k * (2 ^ a - 1) + kpidx * k * (2 ^ a - 1) + dftidx * (2 ^ a - 1) 
            + bigi predT (fun (i : int) => nr_nodes i) 1 hidx + (bidx %% nr_nodes hidx);

    return (cidx, c);
  }
}.


module (R_TRCOSMDTTCRC_EUFCMA (A : Adv_EUFCMA_MFORSTWESNPRF) : TRCOC_TCR.Adv_SMDTTCRC) (O : TRCOC_TCR.Oracle_SMDTTCR, OC : TRCOC.Oracle_THFC) = {
  var ad : adrs
  var skFORSs : skFORS list list
  var leavess : dgstblock list list list list
  var nodess : dgstblock list list list list list
  var rootss : dgstblock list list list
  var pkFORSs : pkFORS list list
  
    proc pick() : unit = {
    var skFORS : skFORS;
    var pkFORS : pkFORS;
    var skFORSl : skFORS list;
    var pkFORSl : pkFORS list;
    var leaf, lnode, rnode, node : dgstblock;
    var leavest, nodespl, nodescl, rootsk : dgstblock list;
    var leavesk, nodest, rootsl : dgstblock list list;
    var leavesl, nodesk : dgstblock list list list;
    var nodesl : dgstblock list list list list;
    
    (* Pick address *)
    ad <- adz;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    nodess <- [];
    rootss <- [];
    pkFORSs <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      nodesl <- [];
      rootsl <- [];
      pkFORSl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
        leavesk <- [];
        nodesk <- [];
        rootsk <- [];        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying family oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 
                                         0 (size leavesk * t + size leavest), 
                             val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          
          (* Compute the trees from the leaves by querying the challenge oracle *)
          nodest <- [];
          (* For each layer in a tree (of a FORS-TW instance)... *)
          while (size nodest < a) {
            (* Get nodes from the previous layer *)
            nodespl <- last leavest nodest;
            
            (* 
              Compute the nodes in the current layer by mapping the (concatenations of sibling) nodes
              from the previous layer, specifying each of these (concatenations of) nodes as targets
            *)
            nodescl <- [];
            while (size nodescl < nr_nodes (size nodest + 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              node <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size nodess)) (size nodesl)) 
                                           (size nodest + 1) (size nodesk * nr_nodes (size nodest + 1) + size nodescl), 
                              val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node; 
            }
            nodest <- rcons nodest nodescl;
          }
          
          leavesk <- rcons leavesk leavest;
          nodesk <- rcons nodesk nodest;
          rootsk <- rcons rootsk (nth witness (nth witness nodest (a - 1)) 0); (* Final computed node is the root *)
        }
        
        pkFORS <@ O.query(set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) trcotype)
                                    (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl))), 
                          flatten (map DigestBlock.val rootsk));
                          
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
        nodesl <- rcons nodesl nodesk;
        rootsl <- rcons rootsl rootsk;
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
      nodess <- rcons nodess nodesl;
      rootss <- rcons rootss rootsl;
      pkFORSs <- rcons pkFORSs pkFORSl; 
    }
  }

  (* 
  proc pick() : unit = {
    var skFORS : skFORS;
    var skFORSl : skFORS list;
    var leaf, lnode, rnode, node, root : dgstblock;
    var leavest, nodespl, nodescl, rootsk : dgstblock list;
    var leavesk, nodest, rootsl : dgstblock list list;
    var leavesl, nodesk : dgstblock list list list;
    var nodesl : dgstblock list list list list;
    var pkFORS : pkFORS;
    var pkFORSl : pkFORS list;
    
    (* Pick address *)
    ad <- adz;
    
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
        leavesk <- [];
        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves by querying challenge oracle on secret key elements *)
          while (size leavest < t) {
            leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 
                                         0 (size leavesk * t + size leavest), 
                             val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          leavesk <- rcons leavesk leavest;
        }
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
    }

    (* Compute nodes of trees corresponding to leaves *)
    rootss <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size rootss < s) {
      rootsl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size rootsl < l) {
        rootsk <- [];
        (* For each tree in a FORS-TW instance... *)
        while (size rootsk < k) { 
          nodest <- [];
          leavest <- nth witness (nth witness (nth witness leavess (size rootss)) (size rootsl)) (size rootsk);
          (* For each layer in a tree (of a FORS-TW instance)... *)
          while (size nodest < a) {
            (* Get nodes from the previous layer *)
            nodespl <- last leavest nodest;
            
            (* 
              Compute the nodes in the current layer by mapping the (concatenations of sibling) nodes
              from the previous layer, specifying each of these (concatenations of) nodes as targets
            *)
            nodescl <- [];
            while (size nodescl < nr_nodes (size nodest + 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              node <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size rootss)) (size rootsl)) 
                                           (size nodest + 1) (size rootsk * nr_nodes (size nodest + 1) + size nodescl), 
                               val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node; 
            }
            nodest <- rcons nodest nodescl;
          }
          rootsk <- rcons rootsk (nth witness (nth witness nodest (a - 1)) 0); (* Final computed node is the root *)
        }
        rootsl <- rcons rootsl rootsk;
      }
      rootss <- rcons rootss rootsl;
    }
    
    (* 
      Compute public keys corresponding of FORS-TW instances, specifying 
      (concatenation of) roots of each instance as targets.
    *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        rootsk <- nth witness (nth witness rootss (size pkFORSs)) (size pkFORSl);
        pkFORS <@ O.query(set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) trcotype)
                                    (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl))), 
                          flatten (map DigestBlock.val rootsk));
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
  }
  *)
  proc find(ps : pseed) : int * dgst = {
    var skFORS : skFORS;
    var leaves, sleaves, sleaves' : dgstblock list;
    var root : dgstblock;
    var roots : dgstblock list;
    var m' : msg;
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var mksigFORSTW' : mkey * sigFORSTW;
    var tidx, kpidx, cidx : int;
    var cm' : msgFORSTW;
    var idx' : index;
    var skFORSels : dgstblock list;
    var roots' : dgstblock list;
    var c : dgst;
    
    (* Initialize CMA oracle *)
    O_CMA_MFORSTWESNPRF_AV.init((skFORSs, ps, ad));
        
    (* Ask adversary to forge *)
    (m', mksigFORSTW') <@ A(O_CMA_MFORSTWESNPRF_AV).forge((pkFORSs, ps, ad));
    
    (* Compress message and extract instance index *)
    (mk', sigFORSTW') <- mksigFORSTW';
    (cm', idx') <- mco mk' m';
    
    (* Compute (outer) tree and keypair index from instance index *)
    (tidx, kpidx) <- edivz (val idx') l;
    
    (* Get (list of) roots of instance pointed to by kpidx in set pointed to by tidx *)
    roots' <- nth witness (nth witness rootss tidx) kpidx;
    
    (* Compute the collision as the concatenation of the roots *)
    c <- flatten (map DigestBlock.val roots');
    
    (* 
      Compute index of element in the target list of the SMDDTTCR oracle for which c is a collision.
      Note that, if you were to flatten the whole structure, i.e., sequence all (trees of) considered 
      FORS-TW instances, we have effectively queried (the concatenation of) the roots of each FORS-TW
      instance from left to right.
    *)
    cidx <- val idx';
    
    return (cidx, c);
  }
}.

section Proof_EUFCMA_M_FORS_TW_ES.

declare module A <: Adv_EUFCMA_MFORSTWESNPRF {-O_CMA_MFORSTWESNPRF, -O_CMA_MFORSTWESNPRF_AV, -O_ITSR_Default, -F_OpenPRE.O_SMDTOpenPRE_Default, -FP_OpenPRE.O_SMDTOpenPRE_Default, -FP_DSPR.O_SMDTDSPR_Default, -FC_TCR.O_SMDTTCR_Default, -TRHC_TCR.O_SMDTTCR_Default, -TRCOC_TCR.O_SMDTTCR_Default, -TRHC.O_THFC_Default, -O_THFC_Default, -R_ITSR_EUFCMA, -R_FSMDTOpenPRE_EUFCMA, -R_TRHSMDTTCRC_EUFCMA, -R_TRCOSMDTTCRC_EUFCMA}.

declare axiom A_forge_ll (O <: SOracle_CMA_MFORSTWESNPRF{-A}) :
  islossless O.sign => islossless A(O).forge.

(* As EUF_CMA_MFORSTWESNPRF, but with additional checks for possibility of breaking considered properties of THFs  *)
local module EUF_CMA_MFORSTWESNPRF_C = {
  var valid_ITSR, valid_OpenPRE, valid_TRHTCR : bool
  
  proc main() : bool = {    
    var ad : adrs;
    var ps : pseed;
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;
    var skFORSt, leaves : dgstblock list;
    var skFORS : skFORS;
    var pkFORSs : pkFORS list list;
    var skFORSs : skFORS list list; 
    var mk' : mkey;
    var sigFORSTW' : sigFORSTW;
    var lidxs' : (int * int * int) list;
    var dfidx, dftidx, dflfidx, tidx, kpidx : int;
    var x, x', leaf, leaf', root, root' : dgstblock;
    var ap' : apFORSTW;
    
    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);

    O_CMA_MFORSTWESNPRF_AV.init(sk);

    (m', sig') <@ A(O_CMA_MFORSTWESNPRF_AV).forge(pk);

    is_valid <@ M_FORS_TW_ES_NPRF.verify(pk, m', sig');

    is_fresh <@ O_CMA_MFORSTWESNPRF_AV.fresh(m');
    
    (* Additional checks *)
    (* 
      ITSR: 
      The adversary managed to find a message that, when signed, only uses secret key values that
      have already been revealed as part of signatures of different, previously signed messages 
    *)
    (mk', sigFORSTW') <- sig';
    lidxs' <- g (mco mk' m');
    valid_ITSR <-    (forall idx, idx \in lidxs' => idx \in O_CMA_MFORSTWESNPRF_AV.lidxs) 
                  /\ ! (mk', m') \in zip O_CMA_MFORSTWESNPRF_AV.mks O_CMA_MFORSTWESNPRF.qs;
    
    
    (*
      OpenPRE (assuming no ITSR break):
      Even though the signed message uses a secret key value that was not yet revealed (i.e., no ITSR break),
      the adversary managed to find a value that maps to the same leaf as this original secret key value.  
    *)
    skFORSs <- sk.`1;
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs');
    (x', ap') <- nth witness (val sigFORSTW') dftidx;
    (tidx, kpidx) <- edivz dfidx l;
    skFORS <- nth witness (nth witness skFORSs tidx) kpidx;
    skFORSt <- nth witness (val skFORS) dftidx; 
    x <- nth witness skFORSt dflfidx;
    leaf' <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx)) (val x');
    leaf <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx)) (val x);
    valid_OpenPRE <- leaf' = leaf;  
    
    (*
      Tree-hash TCR (assuming no ITSR and no OpenPRE breaks):
      Even though there is a leaf (computed from the secret key value) in the forged signature that does not match
      the corresponding original leaf, the adversary managed to find an authentication path that still results in the
      same root as the original tree's root (which requires a collision for the tree hash function). 
    *) 
    root' <- val_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) ap' dflfidx leaf' dftidx; 
    leaves <- mkseq (fun (i : int) => f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + i)) (val (nth witness skFORSt i))) t;
    root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) dftidx;
    valid_TRHTCR <- root' = root;
    
    return is_valid /\ is_fresh; 
  }
}.

local equiv Eqv_EUF_CMA_MFORSTWESNPRF_Orig_C:
  EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main ~ EUF_CMA_MFORSTWESNPRF_C.main :
    ={glob A} ==> ={res}.
proof.
proc.
seq 5 5 : (   ={sig', pk, m'} 
           /\ mem O_CMA_MFORSTWESNPRF.qs{1} = mem O_CMA_MFORSTWESNPRF.qs{2}). 
+ call (:   ={O_CMA_MFORSTWESNPRF.mmap, O_CMA_MFORSTWESNPRF.sk}
         /\ mem O_CMA_MFORSTWESNPRF.qs{1} = mem O_CMA_MFORSTWESNPRF.qs{2}
         /\ dom O_CMA_MFORSTWESNPRF.mmap{1} = mem O_CMA_MFORSTWESNPRF.qs{1}).
  - proc; inline *.
    sp 1 1.
    if => //.
    * wp=> /=. 
      while (={ps0, ad0, skFORS0, m0, sig}).
      + wp => /=.
        by while (={leaves0, skFORS1, idxt, ps1, ad1}); wp; skip.
      wp => /=.
      by rnd; skip => />; smt(mem_set mem_rcons).
    wp => /=.
    while (={ps0, ad0, skFORS0, m0, sig}).
    + wp => /=.
      by while (={leaves0, skFORS1, idxt, ps1, ad1}); wp; skip.
    by wp; skip => />; smt(mem_set mem_rcons).
  inline{1} 4; inline{2} 4; inline{2} 5.
  wp => />.
  conseq (: _ ==> ={pk, sk}); 1: smt(mem_empty).
  by sim.
inline{1} 2; inline{2} 2.
wp => /=.
conseq (: _ ==> ={is_valid}); 1: smt(). 
by sim.
qed.


(* As EUF_CMA_MFORSTWESNPRF, but with additional checks for possibility of breaking considered properties of THFs  *)
local module EUF_CMA_MFORSTWESNPRF_V = {
  var valid_ITSR, valid_OpenPRE, valid_TRHTCR : bool
  
  proc main() : bool = {    
    var ad : adrs;
    var ps : pseed;
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;
    var skFORSt, leaves : dgstblock list;
    var skFORS : skFORS;
    var pkFORS, pkFORS' : pkFORS;
    var pkFORSs : pkFORS list list;
    var skFORSs : skFORS list list; 
    var mk' : mkey;
    var cm' : msgFORSTW;
    var idx' : index;
    var sigFORSTW' : sigFORSTW;
    var lidxs' : (int * int * int) list;
    var dfidx, dftidx, dflfidx, tidx, kpidx, lfidx : int;
    var x, x', leaf, leaf', root, root' : dgstblock;
    var ap' : apFORSTW;
    var skFORS_ele' : dgstblock;
    var skFORS_eles', leaves' : dgstblock list;
    var roots' : dgstblock list;
    
    ad <- adz;
    ps <$ dpseed;
    
    (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad);

    O_CMA_MFORSTWESNPRF_AV.init(sk);

    (m', sig') <@ A(O_CMA_MFORSTWESNPRF_AV).forge(pk);
    
    pkFORSs <- pk.`1;
    (mk', sigFORSTW') <- sig';
    (cm', idx') <- mco mk' m';
    (tidx, kpidx) <- edivz (val idx') l;
    pkFORS <- nth witness (nth witness pkFORSs tidx) kpidx;
    lidxs' <- g (cm', idx');
    
    skFORS_eles' <- [];
    leaves' <- [];
    roots' <- [];
    while (size roots' < k){
      lfidx <- (nth witness lidxs' (size roots')).`3;
      (skFORS_ele', ap') <- nth witness (val sigFORSTW') (size roots');
      leaf' <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (size roots' * t + lfidx)) (val skFORS_ele');
      root' <- val_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) ap' lfidx leaf' (size roots');
      skFORS_eles' <- rcons skFORS_eles' skFORS_ele';
      leaves' <- rcons leaves' leaf';
      roots' <- rcons roots' root';
    }
    pkFORS' <- trco ps (set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) trcotype) 
                                  (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx)))
                    (flatten (map DigestBlock.val roots'));
    
    
    (* Additional checks *)
    (* 
      ITSR: 
      The adversary managed to find a message that, when signed, only uses secret key values that
      have already been revealed as part of signatures of different, previously signed messages 
    *)
    valid_ITSR <-    (forall idx, idx \in lidxs' => idx \in O_CMA_MFORSTWESNPRF_AV.lidxs) 
                  /\ ! (mk', m') \in zip O_CMA_MFORSTWESNPRF_AV.mks O_CMA_MFORSTWESNPRF.qs;
    
    (*
      OpenPRE (assuming no ITSR break):
      Even though the signed message uses a secret key value that was not yet revealed (i.e., no ITSR break),
      the adversary managed to find a value that maps to the same leaf as this original secret key value.  
    *)
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs');
    (x', ap') <- nth witness (val sigFORSTW') dftidx;
    skFORSt <- nth witness (val (nth witness (nth witness sk.`1 tidx) kpidx)) dftidx;
    x <- nth witness skFORSt dflfidx;
    leaf' <- nth witness leaves' dftidx;
    leaf <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx)) (val x);
    valid_OpenPRE <- leaf' = leaf;  
    
    (*
      Tree-hash TCR (assuming no ITSR and no OpenPRE breaks):
      Even though there is a leaf (computed from the secret key value) in the forged signature that does not match
      the corresponding original leaf, the adversary managed to find an authentication path that still results in the
      same root as the original tree's root (which requires a collision for the tree hash function). 
    *) 
    root' <- nth witness roots' dftidx; 
    leaves <- mkseq (fun (i : int) => f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + i)) (val (nth witness skFORSt i))) t;
    root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) dftidx;
    valid_TRHTCR <- root' = root;

    is_valid <- pkFORS' = pkFORS;
    
    is_fresh <- ! (m' \in O_CMA_MFORSTWESNPRF.qs);
    
    return is_valid /\ is_fresh; 
  }
}.

local equiv Eqv_EUF_CMA_MFORSTWESNPRF_C_V:
  EUF_CMA_MFORSTWESNPRF_C.main ~ EUF_CMA_MFORSTWESNPRF_V.main :
    ={glob A} ==> ={res}.
proof.
proc.
seq 5 5 : (   ={ad, ps, sk, pk, m', sig', O_CMA_MFORSTWESNPRF.qs}
           /\ pk{1}.`2 = ps{1}
           /\ pk{1}.`3 = ad{1}).
+ call (: ={glob O_CMA_MFORSTWESNPRF_AV}); 1: by sim.
  inline{1} 4; inline{1} 5; inline{2} 4; inline{2} 5.
  inline{1} 3; inline{2} 3.
  wp => />.
  while (#post).
  - wp => /=. 
    conseq (: _ ==> ={skFORSl, pkFORSl}) => //.
    by sim.
  by wp; rnd; wp; skip.
inline{1} 2; inline{1} 1; inline{1} 9; inline{1} 13.
swap{1} 24 17; swap{1} [21..22] 19; swap{1} 21 -20.
sp 1 0; wp 20 11.
conseq (: _ ==> ={pkFORS'} /\ pkFORS0{1} = pkFORS{2}) => //.
wp => /=.
while (   roots{1} = roots'{2}
       /\ ps2{1} = ps{2}
       /\ ad2{1} = set_kpidx (set_tidx (set_typeidx ad{2} trhtype) tidx{2}) kpidx{2}
       /\ sig1{1} = sigFORSTW'{2}
       /\ lidxs'{2} = g (m2{1}, idx{1})).
+ wp; skip => /> &1 &2 ltk_szrsp.
  have -> //:
    bs2int (rev (take a (drop (a * size roots'{2}) (val m2{1})))) 
    =
    (nth witness (g (m2{1}, idx{1})) (size roots'{2})).`3.
  rewrite /g /= nth_mkseq 2:/=; 1: smt(size_ge0).
  do 2! congr; rewrite /chunk nth_mkseq 2://.
  by rewrite size_ge0 valP /= mulzK 2://; 1: smt(ge1_a).
by wp; skip.
qed.


(* As EUF_CMA_MFORSTWESNPRF_V, but key generation in a way that facilitates TRH and TRCO proofs  *)
local module EUF_CMA_MFORSTWESNPRF_VI = {
  import var EUF_CMA_MFORSTWESNPRF_V
  
  proc main() : bool = {    
    var ad : adrs;
    var ps : pseed;
    var pk : pkFORS list list * pseed * adrs;
    var sk : skFORS list list * pseed * adrs;
    var m' : msg;
    var sig' : mkey * sigFORSTW;
    var is_valid, is_fresh : bool;
    var skFORSt, leaves : dgstblock list;
    var skFORS : skFORS;
    var pkFORS, pkFORS' : pkFORS;
    var pkFORSs : pkFORS list list;
    var skFORSs : skFORS list list; 
    var mk' : mkey;
    var cm' : msgFORSTW;
    var idx' : index;
    var sigFORSTW' : sigFORSTW;
    var lidxs' : (int * int * int) list;
    var dfidx, dftidx, dflfidx, tidx, kpidx, lfidx : int;
    var x, x', leaf, leaf', root, root' : dgstblock;
    var ap' : apFORSTW;
    var skFORS_ele' : dgstblock;
    var skFORS_eles', leaves' : dgstblock list;
    var roots' : dgstblock list;
    var skFORSl : skFORS list;
    var pkFORSl : pkFORS list;
    var lnode, rnode, node : dgstblock;
    var leavest, nodespl, nodescl, rootsk : dgstblock list;
    var leavesk, nodest, rootsl : dgstblock list list;
    var leavesl, nodesk, rootss : dgstblock list list list;
    var leavess, nodesl : dgstblock list list list list;
    var nodess : dgstblock list list list list list;
    
    ad <- adz;
    ps <$ dpseed;
    
    (* (pk, sk) <@ M_FORS_TW_ES_NPRF.keygen(ps, ad); *)
    (* Sample FORS-TW secret keys and compute corresponding leaves *)
    skFORSs <- [];
    leavess <- [];
    nodess <- [];
    rootss <- [];
    pkFORSs <- [];
    (* For each set of FORS-TW instances (SPHINCS+: XMSS instance)... *)
    while (size skFORSs < s) {
      skFORSl <- [];
      leavesl <- [];
      nodesl <- [];
      rootsl <- [];
      pkFORSl <- [];
      (* For each FORS-TW instance in a set (SPHINCS+: leaf of XMSS instance)... *)
      while (size skFORSl < l) {
        skFORS <@ FL_FORS_TW_ES_NPRF.gen_skFORS();
        
        leavesk <- [];
        nodesk <- [];
        rootsk <- [];        
        (* For each tree in a FORS-TW instance... *)
        while (size leavesk < k)  {
          leavest <- [];
          (* Compute the leaves *)
          while (size leavest < t) {
            (* leaf <@ OC.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl)) 
                                         0 (size leavesk * t + size leavest), 
                                val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest))); *)
            leaf <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size skFORSs)) (size skFORSl))
                                      0 (size leavesk * t + size leavest))
                      (val (nth witness (nth witness (val skFORS) (size leavesk)) (size leavest)));
            leavest <- rcons leavest leaf;
          }
          
          (* Compute the trees incrementally from the leaves *)
          nodest <- [];
          (* For each layer in a tree (of a FORS-TW instance)... *)
          while (size nodest < a) {
            (* Get nodes from the previous layer *)
            nodespl <- last leavest nodest;
            
            (* 
              Compute the nodes in the current layer by mapping the (concatenations of sibling) nodes
              from the previous layer
            *)
            nodescl <- [];
            while (size nodescl < nr_nodes (size nodest + 1)) {
              lnode <- nth witness nodespl (2 * size nodescl);
              rnode <- nth witness nodespl (2 * size nodescl + 1);
              
              (* node <@ O.query(set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size nodess)) (size nodesl)) 
                                          (size nodest + 1) (size nodesk * nr_nodes (size nodest + 1) + size nodescl), 
                                 val lnode ++ val rnode); *)
              node <- trh ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size nodess)) (size nodesl))
                                         (size nodest + 1) (size nodesk * nr_nodes (size nodest + 1) + size nodescl))
                          (val lnode ++ val rnode);
              
              nodescl <- rcons nodescl node; 
            }
            nodest <- rcons nodest nodescl;
          }
          leavesk <- rcons leavesk leavest;
          nodesk <- rcons nodesk nodest;
          rootsk <- rcons rootsk (nth witness (nth witness nodest (a - 1)) 0); (* Final computed node is the root *)
        }
        
        pkFORS <- trco ps (set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl)) trcotype)
                                     (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) (size pkFORSs)) (size pkFORSl))))
                       (flatten (map DigestBlock.val rootsk));
        
        skFORSl <- rcons skFORSl skFORS;
        leavesl <- rcons leavesl leavesk;
        nodesl <- rcons nodesl nodesk;
        rootsl <- rcons rootsl rootsk;
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      skFORSs <- rcons skFORSs skFORSl;
      leavess <- rcons leavess leavesl;
      nodess <- rcons nodess nodesl;
      rootss <- rcons rootss rootsl;
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
    
    (*
    (* 
      Compute public keys corresponding of FORS-TW instances
    *)
    pkFORSs <- [];
    while (size pkFORSs < s) {
      pkFORSl <- [];
      while (size pkFORSl < l) {
        rootsk <- nth witness (nth witness rootss (size pkFORSs)) (size pkFORSl);
        
        (* pkFORS <@ O.query(set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl), 
                             flatten (map DigestBlock.val rootsk)); *)
        
        pkFORS <- trco ps (set_kpidx (set_tidx (set_typeidx ad trcotype) (size pkFORSs)) (size pkFORSl))
                       (flatten (map DigestBlock.val rootsk));
        pkFORSl <- rcons pkFORSl pkFORS;
      }
      pkFORSs <- rcons pkFORSs pkFORSl;
    }
    *)
    O_CMA_MFORSTWESNPRF_AV.init((skFORSs, ps, ad));

    (m', sig') <@ A(O_CMA_MFORSTWESNPRF_AV).forge((pkFORSs, ps, ad));
    
    (mk', sigFORSTW') <- sig';
    (cm', idx') <- mco mk' m';
    (tidx, kpidx) <- edivz (val idx') l;
    pkFORS <- nth witness (nth witness pkFORSs tidx) kpidx;
    lidxs' <- g (cm', idx');
    
    skFORS_eles' <- [];
    leaves' <- [];
    roots' <- [];
    while (size roots' < k){
      lfidx <- (nth witness lidxs' (size roots')).`3;
      (skFORS_ele', ap') <- nth witness (val sigFORSTW') (size roots');
      leaf' <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (size roots' * t + lfidx)) (val skFORS_ele');
      root' <- val_ap_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) ap' lfidx leaf' (size roots');
      skFORS_eles' <- rcons skFORS_eles' skFORS_ele';
      leaves' <- rcons leaves' leaf';
      roots' <- rcons roots' root';
    }
    pkFORS' <- trco ps (set_kpidx (set_typeidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) trcotype) 
                                  (get_kpidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx)))
                    (flatten (map DigestBlock.val roots'));
    
    
    (* Additional checks *)
    (* 
      ITSR: 
      The adversary managed to find a message that, when signed, only uses secret key values that
      have already been revealed as part of signatures of different, previously signed messages 
    *)
    valid_ITSR <-    (forall idx, idx \in lidxs' => idx \in O_CMA_MFORSTWESNPRF_AV.lidxs) 
                  /\ ! (mk', m') \in zip O_CMA_MFORSTWESNPRF_AV.mks O_CMA_MFORSTWESNPRF.qs;
    
    (*
      OpenPRE (assuming no ITSR break):
      Even though the signed message uses a secret key value that was not yet revealed (i.e., no ITSR break),
      the adversary managed to find a value that maps to the same leaf as this original secret key value.  
    *)
    (dfidx, dftidx, dflfidx) <- nth witness lidxs' (find (fun i => ! i \in O_CMA_MFORSTWESNPRF_AV.lidxs) lidxs');
    (x', ap') <- nth witness (val sigFORSTW') dftidx;
    skFORSt <- nth witness (val (nth witness (nth witness skFORSs tidx) kpidx)) dftidx;
    x <- nth witness skFORSt dflfidx;
    leaf' <- nth witness leaves' dftidx;
    leaf <- f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + dflfidx)) (val x);
    valid_OpenPRE <- leaf' = leaf;  
    
    (*
      Tree-hash TCR (assuming no ITSR and no OpenPRE breaks):
      Even though there is a leaf (computed from the secret key value) in the forged signature that does not match
      the corresponding original leaf, the adversary managed to find an authentication path that still results in the
      same root as the original tree's root (which requires a collision for the tree hash function). 
    *) 
    root' <- nth witness roots' dftidx; 
    leaves <- mkseq (fun (i : int) => f ps (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) 0 (dftidx * t + i)) (val (nth witness skFORSt i))) t;
    root <- val_bt_trh ps (set_kpidx (set_tidx (set_typeidx ad trhtype) tidx) kpidx) (list2tree leaves) dftidx;
    valid_TRHTCR <- root' = root;

    is_valid <- pkFORS' = pkFORS;
    
    is_fresh <- ! (m' \in O_CMA_MFORSTWESNPRF.qs);
    
    return is_valid /\ is_fresh; 
  }
}.


local lemma take_take_drop_cat (s : 'a list) (i j : int):
  0 <= i => 0 <= j =>
  take (i + j) s = take i s ++ take j (drop i s).
proof.
elim: s i j => // x s ih /= i j /= ge0_i ge0_j.
case (i = 0) => [/#| neq0j].
rewrite (: ! i <= 0) 2:(: ! i + j <= 0) 1,2:/# /=.
by move: (ih (i - 1) j _ _); smt().
qed.

local lemma take1_head (x0 : 'a) (s : 'a list) :
     1 <= size s
  => take 1 s = [head x0 s].
proof. by elim: s => /#. qed.

local lemma drop1_behead (s : 'a list) :
     drop 1 s = behead s.
proof. by elim: s => /#. qed.


local equiv Eqv_EUF_CMA_MFORSTWESNPRF_V_VI:
  EUF_CMA_MFORSTWESNPRF_V.main ~ EUF_CMA_MFORSTWESNPRF_VI.main :
    ={glob A} 
    ==> 
    ={EUF_CMA_MFORSTWESNPRF_V.valid_ITSR, EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE, EUF_CMA_MFORSTWESNPRF_V.valid_TRHTCR, res}.
proof.
proc.
seq 3 8 : (   ={glob A, ps, ad}
           /\ pk{1} = (pkFORSs, ps, ad){2}
           /\ sk{1} = (skFORSs, ps, ad){2}).
+ seq 2 2 : (={glob A, ps, ad}); 1: by rnd; wp; skip.
  inline{1} 1.
  wp; sp 2 0 => />.
  while (   ps0{1} = ps{2}
         /\ ad0{1} = ad{2}
         /\ skFORSs0{1} = skFORSs{2}
         /\ pkFORSs0{1} = pkFORSs{2}
         /\ size skFORSs0{1} = size pkFORSs0{1}
         /\ size skFORSs{2} = size nodess{2}
         /\ size skFORSs0{1} <= s).
  - wp => /=.
    while (   #pre
           /\ ={skFORSl, pkFORSl}
           /\ size skFORSl{1} = size pkFORSl{1}
           /\ size skFORSl{2} = size nodesl{2}
           /\ size skFORSl{1} <= l).
    + seq 1 1 : (#pre /\ skFORS0{1} = skFORS{2}).
      - by call (: true); [sim | skip].
      inline{1} 1.
      wp; sp 3 0 => />.
      conseq (: _ ==> roots{1} = rootsk{2}).
      - by move=> /> &2 *; smt(size_rcons).
      while (   #pre
             /\ roots{1} = rootsk{2}
             /\ size roots{1} = size leavesk{2}
             /\ size leavesk{2} = size rootsk{2}
             /\ size leavesk{2} = size nodesk{2}
             /\ size roots{1} <= k).
      - wp => />.
        conseq (: _ 
                  ==>
                     leaves0{1} = leavest{2}
                  /\ nth witness (nth witness nodest{2} (a - 1)) 0
                     =
                     val_bt_trh ps{2} (set_kpidx (set_tidx (set_typeidx ad{2} trhtype) (size skFORSs{2})) (size skFORSl{2})) (list2tree leavest{2}) (size rootsk{2})).
        * by move=> /> &2 *; smt(size_rcons).
        inline{1} 1.
        wp => /=.
        while{2} (   (forall (u v : int), 0 <= u < size nodest{2} => 0 <= v < nr_nodes (u + 1) =>
                        nth witness (nth witness nodest{2} u) v
                        =
                        val_bt_trh_gen ps{2} (set_kpidx (set_tidx (set_typeidx ad{2} trhtype) (size nodess{2})) (size nodesl{2})) 
                                       (oget (sub_bt (list2tree leavest{2}) (rev (int2bs (a - u - 1) v)))) (u + 1) (size nodesk{2} * nr_nodes (u + 1) + v))
                  /\ size leavest{2} = t
                  /\ size nodess{2} < s
                  /\ size nodesl{2} < l
                  /\ size nodesk{2} < k
                  /\ size nodest{2} <= a)
                 (a - size nodest{2}).
        * move=> _ z.
          wp => /=.
          while (   #pre
                 /\ nodespl = last leavest nodest 
                 /\ (forall (v : int), 0 <= v < size nodescl =>
                       nth witness nodescl v
                       =
                       val_bt_trh_gen ps (set_kpidx (set_tidx (set_typeidx ad trhtype) (size nodess)) (size nodesl)) 
                                      (oget (sub_bt (list2tree leavest) (rev (int2bs (a - size nodest - 1) v)))) 
                                      (size nodest + 1) (size nodesk * nr_nodes (size nodest + 1) + v))
                 /\ size nodescl <= nr_nodes (size nodest + 1))
                (nr_nodes (size nodest + 1) - size nodescl).
          + move=> z'.
            wp; skip => /> &2 nthndst eqt_szlfs lts_szndss ltl_szndsl ltk_szndsk _ lta_szndst nthndscl _ ltnrn1_szndscl.
            rewrite ?size_rcons -andbA; split => [v ge0_v ltsz1_v | /#].
            rewrite nth_rcons; case (v < size nodescl{2}) => [/# | ?].
            have eqsz_v : v = size nodescl{2} by smt().
            rewrite eqsz_v /val_bt_trh_gen (: a - size nodest{2} - 1 = a - (size nodest{2} + 1)) 1:/# /=.
            rewrite subbt_list2tree_takedrop 4:oget_some; 1..3: smt(ge1_a size_ge0).
            have ltnn_2szndscl1 : 2 * size nodescl{2} + 1 < nr_nodes (size nodest{2}).
            - rewrite &(IntOrder.ltr_le_trans (2 + 2 * (nr_nodes (size nodest{2} + 1) - 1))) 1:/#.
              by rewrite /nr_nodes mulzDr /= -{1}expr1 -exprD_nneg // /#.
            have ge1_2aszn2szncl : 1 <= 2 ^ (a - size nodest{2}) - 2 * size nodescl{2} - 1 by smt().
            rewrite (last_nth witness); case (size nodest{2} = 0) => [szn0 | nszn0].
            - rewrite szn0 /= expr1 {3}(: 2 = 1 + 1) 1:// (take_nth witness) 1:size_drop 2:/=; 1,2: smt(size_ge0). 
              rewrite (take1_head witness) 1:size_drop 3:nth_drop 2:/= 4://; 1..3: smt(size_ge0). 
              rewrite -cats1 (list2treeS 0) ?expr0 1..3:// /trhi /=. 
              by rewrite ?list2tree1 /= -nth0_head nth_drop; smt(size_ge0).
            rewrite nszn0 /= (: 2 ^ (size nodest{2} + 1) = 2 ^ (size nodest{2}) + 2 ^ (size nodest{2})).
            + by rewrite exprD_nneg 1:size_ge0 //= expr1 /#.
            rewrite take_take_drop_cat 1,2:expr_ge0 1,2://.
            rewrite drop_drop 1:expr_ge0 1://; 1: smt(IntOrder.expr_ge0).
            rewrite (list2treeS (size nodest{2})) 1:size_ge0 1,2:size_take 1,3:expr_ge0 1,3:// 1,2:size_drop; 1,3: smt(size_ge0 IntOrder.expr_ge0).
            + rewrite eqt_szlfs /t (: 2 ^ a = 2 ^ (a - size nodest{2}) * 2 ^ (size nodest{2})) 1:-exprD_nneg 2:size_ge0 1,2:/#.
              pose szn2 := 2 ^ (size nodest{2}). 
              rewrite (: 2 ^ (a - size nodest{2}) * szn2 - size nodescl{2} * (szn2 + szn2) = (2 ^ (a - size nodest{2}) - 2 * size nodescl{2}) * szn2) 1:/#.
              pose mx := max _ _; rewrite (: 2 ^ (size nodest{2}) < mx) // /mx.
              pose sb := ((_ - _ * _) * _)%Int; rewrite &(IntOrder.ltr_le_trans sb) /sb 2:maxrr.
              by rewrite ltr_pmull 1:expr_gt0 // /#.
            + rewrite eqt_szlfs /t (: 2 ^ a = 2 ^ (a - size nodest{2}) * 2 ^ (size nodest{2})) 1:-exprD_nneg 2:size_ge0 1,2:/#.
              pose szn2 := 2 ^ (size nodest{2}). 
              rewrite (: 2 ^ (a - size nodest{2}) * szn2 - (szn2 + size nodescl{2} * (szn2 + szn2)) = (2 ^ (a - size nodest{2}) - 2 * size nodescl{2} - 1) * szn2) 1:/#.
              pose sb := ((_ - _ - _) * _)%Int.
              move: ge1_2aszn2szncl; rewrite lez_eqVlt => -[eq1_2as | gt1_2as].
              - by rewrite /sb -eq1_2as /= lez_maxr 1:expr_ge0.
              rewrite lez_maxr /sb 1:mulr_ge0 2:expr_ge0 //= 1:subr_ge0 1:ler_subr_addr.
              - rewrite &(IntOrder.ler_trans (1 + 2 * (nr_nodes (size nodest{2} + 1) - 1))) 1:/#.
                by rewrite /nr_nodes mulzDr -{1}(expr1 2) -exprD_nneg // /#.
              rewrite (: szn2 < (2 ^ (a - size nodest{2}) - 2 * size nodescl{2} - 1) * szn2) //.    
              by rewrite ltr_pmull 1:expr_gt0.
            rewrite 2?nthndst /=; 1..4: smt(size_ge0).
            rewrite (: a - (size nodest{2} - 1) - 1 = a - size nodest{2}) 1:/#.
            rewrite 2?subbt_list2tree_takedrop 3,6://; 1..4: smt(size_ge0).
            rewrite oget_some /val_bt_trh_gen /trhi /updhbidx /=; do 4! congr => [/# | /= | /# | /=].
            + rewrite /nr_nodes mulrDr mulrA; congr.
              by rewrite eq_sym mulrAC -{1}expr1 -exprD_nneg 1:// /#.
            rewrite /nr_nodes mulrDr -addrA; congr.
            by rewrite eq_sym mulrCA; congr; rewrite -{1}expr1 -exprD_nneg 1:// /#.
          wp; skip => /> &2 nthndst eqt_szlfs lts_szndss ltl_szndsl ltk_szndsk _ lta_szndst.
          split => [| ndscl] ; 1: by rewrite expr_ge0 /#.
          split => [/# | /lezNgt genn1_szndscl nthndscl lenn1_szndscl].
          rewrite ?size_rcons -andbA; split => [u v ge0_u ltsz1_u ge0_v ltnnu1_v | /#].
          rewrite nth_rcons; case (u < size nodest{2}) => [/# | /lezNgt gesz_u].
          have eqsz_u : u = size nodest{2} by smt(size_rcons).
          by rewrite eqsz_u /= nthndscl 1:/# //.
        wp => /=.
        while (   #pre
               /\ leaves1{1} = leavest{2}
               /\ ps2{1} = ps1{1}
               /\ ad2{1} = ad1{1}
               /\ skFORS2{1} = skFORS1{1}
               /\ idxt{1} = size roots{1}
               /\ size leavest{2} <= t).
        * by wp; skip => />; smt(size_rcons).
        wp; skip => /> &2 eqszpksks eqszndssks _ lts_szsks eqszpkskl eqszndsskl _ ltl_szskl eqszlfsrsk _ eqszndslfsk _ ltk_szrsk ltk_szlfsk.
        split => [| lfs /lezNgt get_szlfs _ let_szlfs]; 1: smt(ge2_t).
        split => [ | ndst ]; 1: smt(ge1_a).
        split => [/# | /lezNgt gea_szndst nthndst eqt_szlfs lts_szndss ltl_szndsl ltk_szndsk lea_szndst].
        rewrite nthndst 2:expr_gt0 2..3:// 2:/=; 1: smt(ge1_a).
        rewrite (: a - (a - 1) - 1 = 0) 1:/#.
        by rewrite int2bs0s rev_nil subbt_empty /nr_nodes /= expr0 /#.
      by wp; skip => />; smt(ge1_k).
    by wp; skip => />; smt(Top.ge1_l size_rcons).
  by wp; skip => />; smt(ge1_s).
wp => /=.
while (={ps, ad, roots', lidxs', sigFORSTW', tidx, kpidx, skFORS_eles', leaves'}).
+ by wp; skip.
wp => /=.
call (: ={glob O_CMA_MFORSTWESNPRF_AV}); 1: by proc; sim.
inline{1} 1; inline{1} 2. 
inline{2} 1; inline{2} 2.
by wp; skip.
qed.


local clone import ExactIter as EI with
  type t <- dgstblock list,
  
  op c <- 1,
  op step <- 1
  
  proof *.
  realize c_gt0 by trivial.
  realize step_gt0 by trivial.


local module O_SMDTOpenPRE_Default_Init_LoopBody : AdvLoop = {
  import var O_SMDTOpenPRE_Default
  var tws : adrs list
  
  proc body(ys : dgstblock list, i : int) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tw <- nth witness tws i;
    x <$ ddgstblocklift;
    y <- f pp tw x;
    twy <- (tw, y);
    xs <- rcons xs x;
    ys <- rcons ys y;
    ts <- rcons ts twy;
    
    return ys;
  }
}.
  
local module O_SMDTOpenPRE_Default_Init_LoopBodyNest1 : AdvLoop = {
  import var O_SMDTOpenPRE_Default
  import var O_SMDTOpenPRE_Default_Init_LoopBody
  var i : int
   
  proc body(ys : dgstblock list, j : int) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tw <- nth witness tws (i * l * k * t + j);
    x <$ ddgstblocklift;
    y <- f pp tw x;
    twy <- (tw, y);
    xs <- rcons xs x;
    ys <- rcons ys y;
    ts <- rcons ts twy;
    
    return ys;
  }
}.

local module O_SMDTOpenPRE_Default_Init_LoopBodyNest2 : AdvLoop = {
  import var O_SMDTOpenPRE_Default
  import var O_SMDTOpenPRE_Default_Init_LoopBody
  import var O_SMDTOpenPRE_Default_Init_LoopBodyNest1
  var j : int
   
  proc body(ys : dgstblock list, u : int) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tw <- nth witness tws (i * l * k * t + j * k * t + u);
    x <$ ddgstblocklift;
    y <- f pp tw x;
    twy <- (tw, y);
    xs <- rcons xs x;
    ys <- rcons ys y;
    ts <- rcons ts twy;
    
    return ys;
  }
}.


local module O_SMDTOpenPRE_Default_Init_CL = {
  import var O_SMDTOpenPRE_Default
  import var O_SMDTOpenPRE_Default_Init_LoopBody
  import var O_SMDTOpenPRE_Default_Init_LoopBodyNest1
  import var O_SMDTOpenPRE_Default_Init_LoopBodyNest2
  
  proc init1(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tws <- tws_init;
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    
    ys <@ Loop(O_SMDTOpenPRE_Default_Init_LoopBody).loop1(ys, d * k * t);
    
    return ys;
  }
  
  proc init2(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tws <- tws_init;
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    
    i <- 0;
    while (i < s) {
      ys <@ Loop(O_SMDTOpenPRE_Default_Init_LoopBodyNest1).loop1(ys, l * k * t);
      i <- i + 1;
    }
    
    return ys;
  }
  
  proc init3(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    
    tws <- tws_init;
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    
    i <- 0;
    while (i < s) {
      j <- 0;
      while (j < l) {
        ys <@ Loop(O_SMDTOpenPRE_Default_Init_LoopBodyNest2).loop1(ys, k * t);
        j <- j + 1;
      }
      i <- i + 1;
    }
    
    return ys;
  }
}.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_Orig_CL1:
  O_SMDTOpenPRE_Default.init ~ O_SMDTOpenPRE_Default_Init_CL.init1 :
    ={arg} /\ d * k * t <= size tws_init{1} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
inline{2} 7.
wp => /=.
while (   ={glob O_SMDTOpenPRE_Default}
       /\ ys{1} = t{2} 
       /\ tws_init{1} = O_SMDTOpenPRE_Default_Init_LoopBody.tws{2}
       /\ n{2} = d * k * Top.t
       /\ d * k * Top.t <= size O_SMDTOpenPRE_Default_Init_LoopBody.tws{2} 
       /\ size O_SMDTOpenPRE_Default.ts{1} = i{2}
       /\ size O_SMDTOpenPRE_Default.ts{1} <= d * k * t).
+ inline{2} 1.
  by wp; rnd; wp; skip => />; smt(size_rcons).
by wp; skip => />; smt(ge1_d ge1_k ge2_t).
qed.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_CL1_CL2:
  O_SMDTOpenPRE_Default_Init_CL.init1 ~ O_SMDTOpenPRE_Default_Init_CL.init2 :
    ={arg} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
rewrite equiv [{1} 7 (loop1_loopk O_SMDTOpenPRE_Default_Init_LoopBody) (ys, s, l * k * t :@ ys)].
+ wp; skip => />; rewrite dval; smt(ge1_s Top.ge1_l ge1_k ge2_t). 
inline{1} 7.
wp => /=.
while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBody}
       /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{2}
       /\ t{1} = ys{2} 
       /\ tws_init{1} = O_SMDTOpenPRE_Default_Init_LoopBody.tws{2}
       /\ n{1} = s
       /\ k{1} = l * Top.k * Top.t).
+ inline{2} 1.
  wp => /=.
  while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBody, t}
         /\ j{1} = i{2}
         /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{2}
         /\ k{1} = n{2}
         /\ k{1} = l * Top.k * Top.t).
  - inline{1} 1; inline{2} 1.
    by wp; rnd; wp; skip => /> /#.
  by wp; skip => /> /#.
by wp; skip => /> /#.
qed.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_CL2_CL3:
  O_SMDTOpenPRE_Default_Init_CL.init2 ~ O_SMDTOpenPRE_Default_Init_CL.init3 :
    ={arg} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
while (={glob O_SMDTOpenPRE_Default_Init_LoopBodyNest1, ys}).
+ rewrite equiv [{1} 1 (loop1_loopk O_SMDTOpenPRE_Default_Init_LoopBodyNest1) (ys, l, k * t :@ ys)].
  - by wp; skip => />; smt(ge1_k ge2_t).
  inline{1} 1.
  wp => /=.
  while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBodyNest1}
         /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{2}
         /\ k{1} = Top.k * Top.t
         /\ n{1} = l
         /\ t{1} = ys{2}).
  - inline{2} 1.
    wp => /=.
    while (   ={glob O_SMDTOpenPRE_Default_Init_LoopBodyNest1, t}
           /\ i{1} = O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{2}
           /\ k{1} = Top.k * Top.t
           /\ n{1} = l
           /\ j{1} = i{2}
           /\ n{2} = Top.k * Top.t).
    * inline{1} 1; inline{2} 1.
      wp; rnd; wp; skip => /> /#.
    by wp; skip.
  by wp; skip => /> /#.
by wp; skip => /> /#.
qed.

local module O_SMDTOpenPRE_Default_ILN = {
  import var O_SMDTOpenPRE_Default
  
  proc init(pp_init : pseed, tws_init : adrs list) : dgstblock list = {
    var x : dgst;
    var y : dgstblock;
    var ys : dgstblock list;
    var tw : adrs;
    var twy : adrs * dgstblock;
    var i, j, u, v : int;
    
    pp <- pp_init;
    ts <- [];
    xs <- [];
    os <- [];
    ys <- [];
    i <- 0;
    while (i < s) {
      j <- 0;
      while (j < l) {
        u <- 0;
        while (u < k) {
          v <- 0;
          while (v < t) {
            tw <- nth witness tws_init (i * l * k * t + j * k * t + u * t + v);
            x <$ ddgstblocklift;
            y <- f pp tw x;
            twy <- (tw, y);
            xs <- rcons xs x;
            ys <- rcons ys y;
            ts <- rcons ts twy;
            v <- v + 1;
          }
          u <- u + 1;
        }
        j <- j + 1;
      }
      i <- i + 1;
    }
    
    return ys;
  }
}.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_CL3_ILN:
  O_SMDTOpenPRE_Default_Init_CL.init3 ~ O_SMDTOpenPRE_Default_ILN.init :
    ={arg} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
proc.
while (   ={glob O_SMDTOpenPRE_Default, ys}
       /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{1} = i{2}
       /\ O_SMDTOpenPRE_Default_Init_LoopBody.tws{1} = tws_init{2}).
+ wp => /=.
  while (   #pre
         /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{1} = j{2}).
  - rewrite equiv [{1} 1 (loop1_loopk O_SMDTOpenPRE_Default_Init_LoopBodyNest2) (ys, k, t :@ ys)].
    * by wp; skip => />; smt(ge2_t).
    inline{1} 1.
    wp => /=.
    while (   ={glob O_SMDTOpenPRE_Default}
           /\ O_SMDTOpenPRE_Default_Init_LoopBody.tws{1} = tws_init{2}
           /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest1.i{1} = i{2}
           /\ O_SMDTOpenPRE_Default_Init_LoopBodyNest2.j{1} = j{2}
           /\ i{1} = u{2}
           /\ t{1} = ys{2}
           /\ n{1} = Top.k
           /\ k{1} = Top.t).
    * wp => /=.
      while (   #pre
             /\ j{1} = v{2}).
      + inline{1} 1.
        by wp; rnd; wp; skip => /> /#.
      by wp; skip => /> /#.
    by wp; skip => /> /#.
  by wp; skip => /> /#. 
by wp; skip => /> /#.
qed.

local equiv Eqv_O_SMDTOpenPRE_Default_Init_Orig_ILN:
  O_SMDTOpenPRE_Default.init ~ O_SMDTOpenPRE_Default_ILN.init :
    ={arg} /\ d * k * t <= size tws_init{1} ==> ={res, glob O_SMDTOpenPRE_Default}.
proof.
transitivity O_SMDTOpenPRE_Default_Init_CL.init1
             (={arg} /\ d * k * t <= size tws_init{1} ==> ={res, glob O_SMDTOpenPRE_Default})
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default}) => [/# | // | |].
+ by apply Eqv_O_SMDTOpenPRE_Default_Init_Orig_CL1.
transitivity O_SMDTOpenPRE_Default_Init_CL.init2
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default})
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default}) => [/# | // | |].
+ by apply Eqv_O_SMDTOpenPRE_Default_Init_CL1_CL2.
transitivity O_SMDTOpenPRE_Default_Init_CL.init3
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default})
             (={arg} ==> ={res, glob O_SMDTOpenPRE_Default}) => [/# | // | |].
+ by apply Eqv_O_SMDTOpenPRE_Default_Init_CL2_CL3.
by apply Eqv_O_SMDTOpenPRE_Default_Init_CL3_ILN.
qed.



local lemma take_rev_int2bs (i j n : int):
  0 <= j <= i =>
  take j (rev (int2bs i n)) = rev (int2bs j (n %/ 2 ^ (i - j))).
proof.
move=> rng_j.
rewrite (int2bs_cat (i - j) i n) 1:/# rev_cat take_cat size_rev size_int2bs.
rewrite (: ! j < max 0 (i - (i - j))) 1:/# /= (: max 0 (i - (i - j)) = j) 1:/# /=.
by rewrite take0 cats0 /#.
qed.

local lemma rcons_take_rev_int2bs (i j n : int) (b : bool):
     0 <= j <= i 
  => rcons (take j (rev (int2bs i n))) b 
     = 
     if b
     then rev (int2bs (j + 1) (2 * (n %/ 2 ^ (i - j)) + 1))
     else rev (int2bs (j + 1) (2 * (n %/ 2 ^ (i - j)))).
proof.
move=> rng_j.
rewrite take_rev_int2bs // -rev_cons {1}(: j = j + 1 - 1) //.
case b => _.
+ rewrite {1}(: n %/ 2 ^ (i - j) = (2 * (n %/ 2 ^ (i - j)) + 1) %/ 2).
  - rewrite divzDl 1:dvdz_mulr //.
    by move: (divz_eq0 1 2 _) => //; move/iffLR => /(_ _) // -> /=; rewrite mulKz.
  rewrite (: true = ! 2 %| (2 * (n %/ 2 ^ (i - j)) + 1)).
  - by rewrite dvdzE mulzC modzMDl.
  by rewrite -int2bs_cons 1:/#.
rewrite {1}(: n %/ 2 ^ (i - j) = 2 * (n %/ 2 ^ (i - j)) %/ 2) 1:mulKz //.
rewrite (: false = ! 2 %| (2 * (n %/ 2 ^ (i - j)))) 1: dvdz_mulr //.
by rewrite -int2bs_cons 1:/#.
qed.

local lemma foldlupdhbidx (i j : int) (bs : bool list) :
  foldl updhbidx (i, j) (rev bs) = (i - size bs, j * 2 ^ (size bs) + bs2int bs).
proof.
elim: bs i j => /= [i j | b bs ih i j].
+ by rewrite rev_nil expr0 bs2int_nil.
rewrite rev_cons foldl_rcons ih /updhbidx bs2int_cons /=.
by rewrite exprD_nneg 1,2:// expr1 /#.
qed.


local lemma EUFCMA_MFORSTWESNPRF_OPRE &m:
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res] 
  <= 
  Pr[MCO_ITSR.ITSR(R_ITSR_EUFCMA(A), MCO_ITSR.O_ITSR_Default).main() @ &m : res]
  +
  Pr[F_OpenPRE.SM_DT_OpenPRE(R_FSMDTOpenPRE_EUFCMA(A), F_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res]
(*
  +  
  Pr[FC_TCR.SM_DT_TCR_C(R_FSMDTTCRC_EUFCMA(A), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
*)
  + 
  Pr[TRHC_TCR.SM_DT_TCR_C(R_TRHSMDTTCRC_EUFCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_TRCOSMDTTCRC_EUFCMA(A), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res].
proof.
have ->:
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res]
  =
  Pr[EUF_CMA_MFORSTWESNPRF_V.main() @ &m : res].
+ byequiv => //.
  transitivity EUF_CMA_MFORSTWESNPRF_C.main (={glob A} ==> ={res}) (={glob A} ==> ={res}) => [/# | // | |].
  - by apply Eqv_EUF_CMA_MFORSTWESNPRF_Orig_C.
  by apply Eqv_EUF_CMA_MFORSTWESNPRF_C_V.
rewrite -!RField.addrA.
rewrite Pr[mu_split EUF_CMA_MFORSTWESNPRF_V.valid_ITSR] StdOrder.RealOrder.ler_add.
+ byequiv => //.
  proc.
  inline{2} 2; inline{2} 1.
  seq 5 7 : (   ={pk, sk, m', sig'}
             /\ ad{1} = R_ITSR_EUFCMA.ad{2}
             /\ ps{1} = R_ITSR_EUFCMA.ps{2}
             /\ O_ITSR_Default.ts{2} = zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}
             /\ O_CMA_MFORSTWESNPRF_AV.lidxs{1} 
                = 
                flatten (map (fun (mkm : mkey * msg) => g (mco mkm.`1 mkm.`2)) 
                             (zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}))).
  - call (:   ={mmap}(O_CMA_MFORSTWESNPRF, R_ITSR_EUFCMA)
           /\ O_CMA_MFORSTWESNPRF.sk{1} = (R_ITSR_EUFCMA.skFORSs, R_ITSR_EUFCMA.ps, R_ITSR_EUFCMA.ad){2}
           /\ O_ITSR_Default.ts{2} = zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}
           /\ O_CMA_MFORSTWESNPRF_AV.lidxs{1}
              =
              flatten (map (fun (mkm : mkey * msg) => g (mco mkm.`1 mkm.`2)) 
                           (zip O_CMA_MFORSTWESNPRF_AV.mks{1} O_CMA_MFORSTWESNPRF.qs{1}))
           /\ size O_CMA_MFORSTWESNPRF_AV.mks{1} = size O_CMA_MFORSTWESNPRF.qs{1}).
    * proc; inline *.
      sp 1 0.
      if => //.
      + wp => />.
        while (   ={sig, m0, skFORS0}
               /\ ps0{1} = ps{2}
               /\ ad0{1} = ad{2}).
        - wp 10 10 => /=.
          sp 7 7.
          conseq (: _ ==> ={sig, leaves}) => //.
          by sim.
        wp; rnd; wp; skip => /> &1 &2 eqszmkss ninm mk mkin sig /lezNgt gek_szsig _.
        by rewrite zip_rcons 1:// /= map_rcons flatten_rcons ?size_rcons eqszmkss.
      wp => /=.
      conseq (: _ ==> ={mk, sig}) => //.
      by sim.
    inline{1} 4; inline{1} 5.
    wp => /=.
    seq 2 3 : (   #pre 
               /\ ad{1} = adz 
               /\ ad{1} = R_ITSR_EUFCMA.ad{2} 
               /\ ps{1} = R_ITSR_EUFCMA.ps{2}
               /\ O_ITSR_Default.ts{2} = []).
    * by rnd; wp; skip. 
    inline{1} 1; inline{2} 1.
    sp 2 2; wp => />.
    by sim.
  inline{2} 4.
  conseq (: _ ==> EUF_CMA_MFORSTWESNPRF_V.valid_ITSR{1} 
                  => 
                     (forall (x0 : int * int * int), x0 \in ikssl_f{2} => x0 \in ikssl_q{2}) 
                  /\ ! ((k{2}, x{2}) \in kxl{2})) => //.
  swap{1} [2..3] -1; swap{1} 6 -3; sp 3 0.
  wp => /=.
  conseq (: _ ==> true) => [/> &1 &2 cmidxv idxinimp mkmnin lidx lidxin |].
  - by rewrite idxinimp cmidxv lidxin.
  while{1} (true) (Top.k - size roots'{1}).
  - move=> _ z.
    by wp; skip => />; smt(size_rcons).
  by wp; skip => /> /#.
rewrite Pr[mu_split EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE] StdOrder.RealOrder.ler_add.
+ byequiv=> //.
  proc.
  rewrite equiv [{2} 3 Eqv_O_SMDTOpenPRE_Default_Init_Orig_ILN]; last first.
  - inline{1} 2; inline{2} 2.
    wp => />.
    while (   ={tidx, adl, pp, R_FSMDTOpenPRE_EUFCMA.ad}
            /\ size adl{1} = tidx{1} * l * k * t
            /\ 0 <= tidx{1} <= s).
    * wp => /=.
      while (   ={tidx, kpidx, adl, pp, R_FSMDTOpenPRE_EUFCMA.ad}
             /\ size adl{1} = tidx{1} * l * k * t + kpidx{1} * k * t
             /\ 0 <= tidx{1} < s
             /\ 0 <= kpidx{1} <= l).
      + wp => /=.
        while (   ={tidx, kpidx, tbidx, adl, pp, R_FSMDTOpenPRE_EUFCMA.ad}
               /\ size adl{1} = tidx{1} * l * k * t + kpidx{1} * k * t + tbidx{1}
               /\ 0 <= tidx{1} < s
               /\ 0 <= kpidx{1} < l
               /\ 0 <= tbidx{1} <= k * t).
        - by wp; skip => />; smt(size_rcons).
        by wp; skip => />; smt(ge1_k ge2_t).      
      by wp; skip => />; smt(Top.ge1_l ge1_k ge2_t).
    by wp; rnd; skip => />; smt(dval ge1_s Top.ge1_l ge1_k ge2_t).
  inline{1} 3; inline{2} 2; inline{2} 7.
  inline{2} 17.
  seq 7 24 : (   ={glob A}
              /\ ad{1} = adz
              /\ ad{1} = R_FSMDTOpenPRE_EUFCMA.ad{2}
              /\ ad{1} = ad0{1}
              /\ ps{1} = pp{2}
              /\ ps{1} = ps0{1}
              /\ pp{2} = O_SMDTOpenPRE_Default.pp{2}
              /\ pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
              /\ O_SMDTOpenPRE_Default.os{2} = []
              /\ R_FSMDTOpenPRE_EUFCMA.lidxs{2} = []
              /\ R_FSMDTOpenPRE_EUFCMA.mmap{2} = empty
              /\ R_FSMDTOpenPRE_EUFCMA.leavess{2} = unzip2 O_SMDTOpenPRE_Default.ts{2}
              /\ pkFORSs0{1} = pkFORSs{2}
              /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                    nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
                    =
                    val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))
              /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                    nth witness O_SMDTOpenPRE_Default.ts{2} (i * l * k * t + j * k * t + u * t + v)
                    =
                    (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v),
                     f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                       (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v))))
              /\ size O_SMDTOpenPRE_Default.ts{2} = d * k * t
              /\ size O_SMDTOpenPRE_Default.xs{2} = size O_SMDTOpenPRE_Default.ts{2}).
  - while{2} ((forall (i j : int), 0 <= i < size pkFORSs{2} => 0 <= j < l =>
                nth witness (nth witness pkFORSs{2} i) j
                =
                let adb = set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j in                      
                let rs = mkseq (fun (u : int) =>
                            val_bt_trh R_FSMDTOpenPRE_EUFCMA.ps{2} adb
                                       (list2tree (take t (drop (i * l * k * t + j * k * t + u * t) R_FSMDTOpenPRE_EUFCMA.leavess{2}))) u) k in
                  trco R_FSMDTOpenPRE_EUFCMA.ps{2} (set_kpidx (set_typeidx adb trcotype) (get_kpidx adb))
                       (flatten (map DigestBlock.val rs)))
              /\ all ((=) l \o size) pkFORSs{2}
              /\ size pkFORSs{2} <= s)
             (s - size pkFORSs{2}).
    * move=> _ z.
      wp => /=.
      while ((forall (j : int), 0 <= j < size pkFORSl =>
                  nth witness pkFORSl j
                  =
                  let adb = set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad trhtype) (size pkFORSs)) j in                      
                  let rs = mkseq (fun (u : int) =>
                              val_bt_trh R_FSMDTOpenPRE_EUFCMA.ps adb 
                                         (list2tree (take t (drop (size pkFORSs * l * k * t + j * k * t + u * t) R_FSMDTOpenPRE_EUFCMA.leavess))) u) k in
                    trco R_FSMDTOpenPRE_EUFCMA.ps (set_kpidx (set_typeidx adb trcotype) (get_kpidx adb))
                         (flatten (map DigestBlock.val rs)))
                /\ size pkFORSs < s
                /\ size pkFORSl <= l)
               (l - size pkFORSl).
      + move=> z'.
        wp => /=.
        while (   roots 
                  =
                  mkseq (fun (u : int) =>
                    val_bt_trh R_FSMDTOpenPRE_EUFCMA.ps (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad trhtype) (size pkFORSs)) (size pkFORSl)) 
                               (list2tree (take t (drop (size pkFORSs * l * k * t + size pkFORSl * k * t + u * t) R_FSMDTOpenPRE_EUFCMA.leavess))) u) (size roots)
               /\ size pkFORSs < s
               /\ size pkFORSl < l
               /\ size roots <= k)
              (k - size roots).
        - move=> z''.
          wp; skip => /> &2. 
          by rewrite ?size_rcons mkseqS 1:size_ge0 /=; smt(size_rcons).
        wp; skip => /> &2 nthpkfl lts_szpkfs _ ltl_szpkfl.
        split => [| rs]; 1: by rewrite mkseq0; smt(ge1_k).
        split => [/#| /lezNgt gek_szrs rsval lek_szrs].
        rewrite ?size_rcons -andbA; split => [j ge0_j ltsz1_j | /#].
        rewrite ?nth_rcons; case (j < size pkFORSl{2}) => ?; 1: by rewrite nthpkfl. 
        by rewrite (: j = size pkFORSl{2}) 1:/# rsval (: size rs = k) 1:/#.
      wp; skip => /> &2 nthpkfs allszl_pkfs _ lts_szpkfs.
      split => [| pkfl]; 1: smt(Top.ge1_l).
      split => [/#| /lezNgt gel_szpkfl nthpkfl lel_szpkfl].
      rewrite ?size_rcons -cats1 all_cat allszl_pkfs /= -andbA.
      split => [i j ge0_i ltsz1_i ge0_j ltl_j /= | /#].
      rewrite nth_cat; case (i < size pkFORSs{2}) => ?; 1: by rewrite nthpkfs.
      by rewrite (: i = size pkFORSs{2}) 1:/# /= nthpkfl 1:/#.
    wp => /=.
    while (   ps0{1} = O_SMDTOpenPRE_Default.pp{2}
           /\ ad0{1} = R_FSMDTOpenPRE_EUFCMA.ad{2}
           /\ ys0{2} = unzip2 O_SMDTOpenPRE_Default.ts{2}
           /\ (forall (i j : int), 0 <= i < size skFORSs0{1} => 0 <= j < l =>
                nth witness (nth witness pkFORSs0{1} i) j
                =
                let adb = set_kpidx (set_tidx (set_typeidx ad0{1} trhtype) i) j in
                let rs = mkseq (fun (u : int) =>
                          let lfs = mkseq (fun (v : int) => 
                                      f ps0{1} (set_thtbidx adb 0 (u * t + v)) 
                                        (val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))) t in
                            val_bt_trh ps0{1} adb (list2tree lfs) u) k in
                  trco ps0{1} (set_kpidx (set_typeidx adb trcotype) (get_kpidx adb))
                       (flatten (map DigestBlock.val rs)))
           /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness tws_init{2} (i * l * k * t + j * k * t + u * t + v)
                =
                set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
           /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
                =
                val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))
           /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                 nth witness O_SMDTOpenPRE_Default.ts{2} (i * l * k * t + j * k * t + u * t + v)
                 =
                 (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v),
                  f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                    (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v))))
           /\ all ((=) l \o size) pkFORSs0{1}
           /\ size skFORSs0{1} = i0{2}
           /\ size skFORSs0{1} <= s
           /\ size skFORSs0{1} = size pkFORSs0{1}
           /\ size O_SMDTOpenPRE_Default.ts{2} = i0{2} * l * k * t
           /\ size O_SMDTOpenPRE_Default.xs{2} = size O_SMDTOpenPRE_Default.ts{2}).
    * wp => /=.
      while (   ps0{1} = O_SMDTOpenPRE_Default.pp{2}
             /\ ad0{1} = R_FSMDTOpenPRE_EUFCMA.ad{2}
             /\ ys0{2} = unzip2 O_SMDTOpenPRE_Default.ts{2}
             /\ (forall (i j : int), 0 <= i < size skFORSs0{1} => 0 <= j < l =>
                  nth witness (nth witness pkFORSs0{1} i) j
                  =
                  let adb = set_kpidx (set_tidx (set_typeidx ad0{1} trhtype) i) j in
                  let rs = mkseq (fun (u : int) =>
                            let lfs = mkseq (fun (v : int) => 
                                        f ps0{1} (set_thtbidx adb 0 (u * t + v)) 
                                          (val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))) t in
                              val_bt_trh ps0{1} adb (list2tree lfs) u) k in
                    trco ps0{1} (set_kpidx (set_typeidx adb trcotype) (get_kpidx adb))
                         (flatten (map DigestBlock.val rs)))
             /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                  nth witness tws_init{2} (i * l * k * t + j * k * t + u * t + v)
                  =
                  set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
             /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                  nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
                  =
                  val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))
             /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                   nth witness O_SMDTOpenPRE_Default.ts{2} (i * l * k * t + j * k * t + u * t + v)
                   =
                   (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v),
                    f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                      (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v))))
             /\ (forall (j : int), 0 <= j < size skFORSl{1} =>
                  nth witness pkFORSl{1} j
                  =
                  let adb = set_kpidx (set_tidx (set_typeidx ad0{1} trhtype) (size skFORSs0{1})) j in
                  let rs = mkseq (fun (u : int) =>
                            let lfs = mkseq (fun (v : int) => 
                                        f ps0{1} (set_thtbidx adb 0 (u * t + v)) 
                                          (val (nth witness (nth witness (val (nth witness skFORSl{1} j)) u) v))) t in
                              val_bt_trh ps0{1} adb (list2tree lfs) u) k in
                    trco ps0{1} (set_kpidx (set_typeidx adb trcotype) (get_kpidx adb))
                         (flatten (map DigestBlock.val rs)))
             /\ (forall (j u v : int), 0 <= j < size skFORSl{1} => 0 <= u < k => 0 <= v < t =>
                  nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v)
                  =
                  val (nth witness (nth witness (val (nth witness skFORSl{1} j)) u) v))
             /\ (forall (j u v : int), 0 <= j < size skFORSl{1} => 0 <= u < k => 0 <= v < t =>
                   nth witness O_SMDTOpenPRE_Default.ts{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v)
                   =
                   (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) j) 0 (u * t + v),
                    f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) j) 0 (u * t + v))
                      (nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v))))
             /\ size skFORSs0{1} = i0{2}
             /\ size skFORSs0{1} < s
             /\ size skFORSs0{1} = size pkFORSs0{1}
             /\ size O_SMDTOpenPRE_Default.ts{2} = i0{2} * l * k * t + j{2} * k * t
             /\ size O_SMDTOpenPRE_Default.xs{2} = size O_SMDTOpenPRE_Default.ts{2}
             /\ size skFORSl{1} = j{2}
             /\ size skFORSl{1} = size pkFORSl{1}
             /\ size skFORSl{1} <= l).
      + inline{1} 2; inline{1} 1.
        wp=> /=.
        while{1} (   roots{1}
                     =
                     mkseq (fun (u : int) =>
                             let lfs = mkseq (fun (v : int) => 
                                   f ps1{1} (set_thtbidx ad1{1} 0 (u * t + v)) 
                                     (val (nth witness (nth witness (val skFORS1{1}) u) v))) t in
                        val_bt_trh ps1{1} ad1{1} (list2tree lfs) u) (size roots{1})
                  /\ size pkFORSs0{1} < s
                  /\ size pkFORSl{1} < l
                  /\ size roots{1} <= k)
                 (k - size roots{1}). 
        - move=> _ z.
          inline 1.
          wp => /=.
          while (   leaves1
                    =
                    mkseq (fun (v : int) =>
                      f ps2 (set_thtbidx ad2 0 (idxt * t + v))
                        (val (nth witness (nth witness (val skFORS3) idxt) v))) (size leaves1)
                /\ size leaves1 <= t)
                (t - size leaves1).
          * move=> z'.
            wp; skip => /> &2 lfsdef _ ltt_szlfs.
            by rewrite ?size_rcons mkseqS 1:size_ge0 -andbA; split => [| /#]; congr.
          wp; skip => /> &2 rsdef lts_szpkfs ltl_szpkfs _ ltk_szrs.
          split => [| lfs]; 1: by rewrite mkseq0; smt(ge2_t).
          split => [/#| /lezNgt get_szlfs lfsdef let_szlfs].
          rewrite size_rcons mkseqS 1:size_ge0 /= -andbA; split => [| /#].
          by do 3! congr; rewrite lfsdef (: size lfs = t) 1:/#.
        wp => /=.
        while (   ps0{1} = O_SMDTOpenPRE_Default.pp{2}
               /\ ad0{1} = R_FSMDTOpenPRE_EUFCMA.ad{2}
               /\ ys0{2} = unzip2 O_SMDTOpenPRE_Default.ts{2}
               /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>                     
                    nth witness tws_init{2} (i * l * k * t + j * k * t + u * t + v)
                    =
                    set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
               /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                    nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
                    =
                    val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))
               /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                     nth witness O_SMDTOpenPRE_Default.ts{2} (i * l * k * t + j * k * t + u * t + v)
                     =
                     (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v),
                      f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                        (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v))))
               /\ (forall (j u v : int), 0 <= j < size skFORSl{1} => 0 <= u < k => 0 <= v < t =>
                    nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v)
                    =
                    val (nth witness (nth witness (val (nth witness skFORSl{1} j)) u) v))
               /\ (forall (j u v : int), 0 <= j < size skFORSl{1} => 0 <= u < k => 0 <= v < t =>
                     nth witness O_SMDTOpenPRE_Default.ts{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v)
                     =
                     (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) j) 0 (u * t + v),
                      f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) j) 0 (u * t + v))
                         (nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v))))
               /\ (forall (u v : int), 0 <= u < size skFORS2{1} => 0 <= v < t =>
                    nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v)
                    =
                    val (nth witness (nth witness skFORS2{1} u) v))
               /\ (forall (u v : int), 0 <= u < size skFORS2{1} => 0 <= v < t =>
                     nth witness O_SMDTOpenPRE_Default.ts{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v)
                      =
                      (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) (size skFORSl{1})) 0 (u * t + v),
                       f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) (size skFORSl{1})) 0 (u * t + v))
                         (nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v))))
               /\ all ((=) t \o size) skFORS2{1}
               /\ size skFORSs0{1} = i0{2}
               /\ size skFORSs0{1} = size pkFORSs0{1}
               /\ size skFORSs0{1} < s
               /\ size O_SMDTOpenPRE_Default.ts{2} = i0{2} * l * k * t + j{2} * k * t + u{2} * t
               /\ size O_SMDTOpenPRE_Default.xs{2} = size O_SMDTOpenPRE_Default.ts{2}
               /\ size skFORSl{1} = j{2}
               /\ size skFORSl{1} = size pkFORSl{1}
               /\ size skFORSl{1} < l
               /\ size skFORS2{1} = u{2}
               /\ size skFORS2{1} <= k).
        - wp => /=.
          while (   ps0{1} = O_SMDTOpenPRE_Default.pp{2}
                 /\ ad0{1} = R_FSMDTOpenPRE_EUFCMA.ad{2}
                 /\ ys0{2} = unzip2 O_SMDTOpenPRE_Default.ts{2}
                 /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>                     
                      nth witness tws_init{2} (i * l * k * t + j * k * t + u * t + v)
                      =
                      set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                 /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                      nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
                      =
                      val (nth witness (nth witness (val (nth witness (nth witness skFORSs0{1} i) j)) u) v))
                 /\ (forall (i j u v : int), 0 <= i < size skFORSs0{1} => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                       nth witness O_SMDTOpenPRE_Default.ts{2} (i * l * k * t + j * k * t + u * t + v)
                       =
                       (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v),
                        f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                          (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v))))
                 /\ (forall (j u v : int), 0 <= j < size skFORSl{1} => 0 <= u < k => 0 <= v < t =>
                      nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v)
                      =
                      val (nth witness (nth witness (val (nth witness skFORSl{1} j)) u) v))
                 /\ (forall (j u v : int), 0 <= j < size skFORSl{1} => 0 <= u < k => 0 <= v < t =>
                       nth witness O_SMDTOpenPRE_Default.ts{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v)
                       =
                       (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) j) 0 (u * t + v),
                        f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) j) 0 (u * t + v))
                           (nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + j * k * t + u * t + v))))
                 /\ (forall (u v : int), 0 <= u < size skFORS2{1} => 0 <= v < t =>
                      nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v)
                      =
                      val (nth witness (nth witness skFORS2{1} u) v))
                 /\ (forall (u v : int), 0 <= u < size skFORS2{1} => 0 <= v < t =>
                       nth witness O_SMDTOpenPRE_Default.ts{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v)
                        =
                        (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) (size skFORSl{1})) 0 (u * t + v),
                         f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) (size skFORSl{1})) 0 (u * t + v))
                           (nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v))))                 
                 /\ (forall (v : int), 0 <= v < size skFORSt0{1} =>
                      nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + v)
                      =
                      val (nth witness skFORSt0{1} v))
                 /\ (forall (v : int), 0 <= v < size skFORSt0{1} =>
                       nth witness O_SMDTOpenPRE_Default.ts{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + v)
                        =
                        (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) (size skFORSl{1})) 0 (size skFORS2{1} * t + v),
                         f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) (size skFORSs0{1})) (size skFORSl{1})) 0 (size skFORS2{1} * t + v))
                           (nth witness O_SMDTOpenPRE_Default.xs{2} (size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + v))))
                 /\ size skFORSs0{1} = i0{2}
                 /\ size skFORSs0{1} < s
                 /\ size skFORSs0{1} = size pkFORSs0{1}
                 /\ size O_SMDTOpenPRE_Default.ts{2} = i0{2} * l * k * t + j{2} * k * t + u{2} * t + v{2}
                 /\ size O_SMDTOpenPRE_Default.xs{2} = size O_SMDTOpenPRE_Default.ts{2}
                 /\ size skFORSl{1} = j{2}
                 /\ size skFORSl{1} = size pkFORSl{1}
                 /\ size skFORSl{1} < l
                 /\ size skFORS2{1} = u{2}
                 /\ size skFORS2{1} < k
                 /\ size skFORSt0{1} = v{2}
                 /\ size skFORSt0{1} <= t).
          * wp => /=. 
            rnd DigestBlock.val DigestBlock.insubd.
            wp; skip => /> &1 &2 nthtws nthxs nthts nthxs1 nthts1 nthxs2 nthts2 nthxs3 nthts3 lts_szskfs eqszskpkfs szts eqszxsts eqszskpkfl ltl_szskfl ltk_szskf _ ltt_szskft.
            split => [x /supp_dmap [x'] [_ ->] | vibij]; 1: by rewrite valKd.
            split => [x /supp_dmap [x'] [xin xval] | eqmu1vi skfele skfelein].
            + by rewrite &(in_dmap1E_can) 1:insubdK 1:xval 1:valP 1,2:// => y _ <-; rewrite valKd.
            split => [| vskfelein]; 1: rewrite supp_dmap; 1: by exists skfele.
            split => [ | _]; 1: by rewrite valKd.
            rewrite map_rcons ?size_rcons /= !andbA -2!andbA; split => [| /#].
            rewrite -!andbA; split => [i j u v ge0_i ltsz_i ge0_j ltl_j ge0_u ltk_u ge0_v ltt_v |].
            + rewrite nth_rcons eqszxsts szts.
              have -> /= /#:
                i * l * k * t + j * k * t + u * t + v 
                <
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + size skFORSt0{1}.
              rewrite -?addrA -?(mulrA _ k) -?(mulrA _ l) ltlltr 3://; 1,2: smt(Top.ge1_l ge1_k ge2_t size_ge0).
              rewrite -(addr0 (l * (k * t))) ltlltr 2,3://; 1: smt(ge1_k ge2_t).
              by rewrite -(addr0 (k * t)) ltlltr 2..4://; smt(ge2_t).
            split => [i j u v ge0_i ltsz_i ge0_j ltl_j ge0_u ltk_u ge0_v ltt_v |].
            + rewrite ?nth_rcons eqszxsts szts.
              have -> /= /#:
                i * l * k * t + j * k * t + u * t + v 
                <
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + size skFORSt0{1}.
              rewrite -?addrA -?(mulrA _ k) -?(mulrA _ l) ltlltr 3://; 1,2: smt(Top.ge1_l ge1_k ge2_t size_ge0).
              rewrite -(addr0 (l * (k * t))) ltlltr 2,3://; 1: smt(ge1_k ge2_t).
              by rewrite -(addr0 (k * t)) ltlltr 2..4://; smt(ge2_t).
            split => [j u v ge0_j ltsz_j ge0_u ltk_u ge0_v ltt_v |].
            + rewrite ?nth_rcons eqszxsts szts.
              have -> /= /#:
                size skFORSs0{1} * l * k * t + j * k * t + u * t + v 
                <
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + size skFORSt0{1}.
              rewrite -?addrA IntOrder.ler_lt_add 1:// -2!(mulrA _ k) ltlltr 3:// ; 1,2: smt(ge1_k ge2_t size_ge0).
              by rewrite -(addr0 (k * t)) ltlltr 2..4://; smt(ge2_t).
            split => [j u v ge0_j ltsz_j ge0_u ltk_u ge0_v ltt_v |].
            + rewrite ?nth_rcons eqszxsts szts.
              have -> /= /#:
                size skFORSs0{1} * l * k * t + j * k * t + u * t + v 
                <
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + size skFORSt0{1}.
              rewrite -?addrA IntOrder.ler_lt_add 1:// -2!(mulrA _ k) ltlltr 3:// ; 1,2: smt(ge1_k ge2_t size_ge0).
              by rewrite -(addr0 (k * t)) ltlltr 2..4://; smt(ge2_t).
            split => [u v ge0_u ltsz_u ge0_v ltt_v |].
            + rewrite ?nth_rcons eqszxsts szts.
              have -> /= /#:
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v 
                <
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + size skFORSt0{1}.
              rewrite -?addrA IntOrder.ler_lt_add 1:// IntOrder.ler_lt_add 1://.
              by rewrite ltlltr 2..4://; smt(ge2_t).
            split => [u v ge0_u ltsz_u ge0_v ltt_v |].
            + rewrite ?nth_rcons eqszxsts szts.
              have -> /= /#:
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + u * t + v 
                <
                size skFORSs0{1} * l * k * t + size skFORSl{1} * k * t + size skFORS2{1} * t + size skFORSt0{1}.
              rewrite -?addrA IntOrder.ler_lt_add 1:// IntOrder.ler_lt_add 1://.
              by rewrite ltlltr 2..4://; smt(ge2_t).
            split => v ge0_v ltsz1_v.
            + by rewrite ?nth_rcons eqszxsts szts /#.
            rewrite ?nth_rcons eqszxsts szts.
            case (v < size skFORSt0{1}) => [/# | ?].
            by rewrite (: v = size skFORSt0{1}) 1:/# /= nthtws.
          wp; skip => /> &1 &2 nthtws nthxs nthts nthxs1 nthts1 nthxs2 nthts2 allszt_skf eqszskpkfs lts_szskfs szts eqszxsts eqszskpkfl ltl_szskfl _ ltk_szskf.
          split => [| skft ts' xs' /lezNgt get_szskft _ nthxsp nthtsp nthxsp1 nthtsp1 nthxsp2 nthtsp2 nthxsp3 nthtsp3 eqsztsp eqszxsptsp le_szskft]; 1: smt(ge2_t).
          rewrite ?size_rcons -cats1 all_cat allszt_skf /= eqsztsp (: size skft = t) 1:/#.
          rewrite andbA; split => [| /#].
          split => u v ge0_u ltsz1_u ge0_v ltt_v; 2: smt().
          rewrite nth_cat; case (u < size skFORS2{1}) => ?; 1: by rewrite nthxsp2.
          by rewrite (: u = size skFORS2{1}) 1:/# /= nthxsp3 2:// /#.
        wp; skip => /> &1 &2 nthpkfs nthtws nthxs nthts nthpkfl nthxs1 nthts1 lts_szskfs eqszskpkfs szts eqszxsts eqszskpkfl _ ltl_szskfl.
        split => [| skf ts' xs' /lezNgt gek_szskf _ nthxsp nthtsp nthxsp1 nthtsp1 nthxsp2 nthtsp2 allszt_skf sztsp eqszxsptsp lek_skf]; 1: smt(ge1_k).
        split => [| rs]; 1: by rewrite mkseq0; smt(ge1_k).
        split => [/# | /lezNgt gek_szrs rsdef lts_szpkfs ltl_szpkfl lek_szrs].
        rewrite ?size_rcons sztsp !andbA -5!andbA; split => [| /#].
        rewrite -!andbA; split => [j ge0_j ltsz_j |].
        - rewrite ?nth_rcons -eqszskpkfl; case (j < size skFORSl{1}) => ?; 1: by rewrite nthpkfl.
          rewrite (: j = size skFORSl{1}) 1:/# /=. 
          by do 3! congr; rewrite rsdef (: size rs = k) 1:/#.
        split => j u v ge0_j ltsz_j ge0_u ltk_u ge0_v ltt_v.
        - rewrite nth_rcons; case (j < size skFORSl{1}) => ?; 1: by rewrite nthxsp1.
          rewrite (: j = size skFORSl{1}) 1:/# /= insubdK.
          * split => [/# |]; rewrite allP => x xin /=.
            by move/allP: allszt_skf => /(_ x xin) @/(\o) ->.
          by rewrite nthxsp2 1:/#.
        case (j < size skFORSl{1}) => ?; 1: by rewrite nthtsp1.
        by rewrite (: j = size skFORSl{1}) 1:/# /= nthtsp2 // /#.
      wp; skip => /> &1 &2 nthpkfs nthtws nthxs nthts allszl_pkfs _ eqszskpkfs szts eqszxsts lts_szskfs.
      split => [| pkfl skfl ts' xs' /lezNgt gel_szskfl _ nthxsp nthtsp nthpkfl nthxsp1 nthtsp1 sztsp eqszxsptsp eqszskpkfl lel_zskfl]; 1: smt(Top.ge1_l).
      rewrite ?size_rcons -cats1 all_cat allszl_pkfs /= sztsp !andbA -3!andbA. 
      split => [| /#].
      rewrite -andbA; split => [i j ge0_i ltsz1_i ge0_j ltl_j|].
      + rewrite nth_cat ?nth_rcons -eqszskpkfs; case (i < size skFORSs0{1}) => ?; 1: by rewrite nthpkfs.
        by rewrite (: i = size skFORSs0{1}) 1:/# /= nthpkfl 2:// 1:/#.
      split => i j u v ge0_i ltsz1_i ge0_j ltl_j ge0_u ltk_u ge0_v ltt_v.
      + rewrite nth_rcons; case (i < size skFORSs0{1}) => ?; 1: by rewrite nthxsp.
        by rewrite (: i = size skFORSs0{1}) 1:/# /= nthxsp1 2:// 1:/#.
       case (i < size skFORSs0{1}) => ?; 1: by rewrite nthtsp.
       by rewrite (: i = size skFORSs0{1}) 1:/# /= nthtsp1 2:// 1:/#.
    wp => /=.
    while{2} (   (forall (i j u v : int), 0 <= i < tidx{2} => 0 <= j < l => 0 <= u < k => 0 <= v < t => 
                  nth witness adl{2} (i * l * k * t + j * k * t + u * t + v) 
                  = 
                  set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
             /\ size adl{2} = tidx{2} * l * k * t
             /\ 0 <= tidx{2} <= s)
             (s - tidx{2}).
    * move=> _ z.
      wp => /=.
      while (   (forall (i j u v : int), 0 <= i < tidx => 0 <= j < l => 0 <= u < k => 0 <= v < t => 
                  nth witness adl (i * l * k * t + j * k * t + u * t + v) 
                  = 
                  set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad trhtype) i) j) 0 (u * t + v))
             /\ (forall (j u v : int), 0 <= j < kpidx => 0 <= u < k => 0 <= v < t => 
                  nth witness adl (tidx * l * k * t + j * k * t + u * t + v) 
                  = 
                  set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad trhtype) tidx) j) 0 (u * t + v))
             /\ size adl = tidx * l * k * t + kpidx * k * t
             /\ 0 <= tidx < s
             /\ 0 <= kpidx <= l)
             (l - kpidx).
      + move=> z'.
        wp => /=.
        while (   (forall (i j u v : int), 0 <= i < tidx => 0 <= j < l => 0 <= u < k => 0 <= v < t => 
                    nth witness adl (i * l * k * t + j * k * t + u * t + v) 
                    = 
                    set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad trhtype) i) j) 0 (u * t + v))
               /\ (forall (j u v : int), 0 <= j < kpidx => 0 <= u < k => 0 <= v < t => 
                    nth witness adl (tidx * l * k * t + j * k * t + u * t + v) 
                    = 
                    set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad trhtype) tidx) j) 0 (u * t + v))
               /\ (forall (u : int), 0 <= u < tbidx =>
                    nth witness adl (tidx * l * k * t + kpidx * k * t + u) 
                    = 
                    set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad trhtype) tidx) kpidx) 0 u)
               /\ size adl = tidx * l * k * t + kpidx * k * t + tbidx
               /\ 0 <= tidx < s
               /\ 0 <= kpidx < l
               /\ 0 <= tbidx <= k * t)
               (k * t - tbidx).
        - move=> z''.
          wp; skip => /> &2 nthadl nthadl1 nthadl2 szadl ge0_tidx lts_tidx ge0_kpidx ltl_kpidx ge0_tbidx _ ltkt_tbidx.
          rewrite ?size_rcons !andbA -3!andbA; split => [| /#]; 1: rewrite -!andbA.
          split => [i j u v ge0_i lttidx_i ge0_j ltl_j ge0_u ltk_u ge0_v ltt_v |].
          * rewrite nth_rcons szadl.
            have -> /= /#:
              i * l * k * t + j * k * t + u * t + v 
              < 
              tidx{2} * l * k * t + kpidx{2} * k * t + tbidx{2}.
            rewrite -?addrA -?(mulrA _ k) -?(mulrA _ l) ltlltr 3://; 1,2: smt(Top.ge1_l ge1_k ge2_t).
            rewrite -(addr0 (l * (k * t))) ltlltr 2,3://; 1: smt(ge1_k ge2_t).
            by rewrite -(addr0 (k * t)) ltlltr 2..4://; smt(ge2_t).
          split => [j u v ge0_j ltkpidx_j ge0_u ltk_u ge0_v ltt_v |].
          * rewrite nth_rcons szadl.
            have -> /= /#:
              tidx{2} * l * k * t + j * k * t + u * t + v 
              < 
              tidx{2} * l * k * t + kpidx{2} * k * t + tbidx{2}.
            rewrite -?addrA IntOrder.ler_lt_add 1:// -?(mulrA _ k) ltlltr 3://; 1,2: smt(ge1_k ge2_t).
            by rewrite -(addr0 (k * t)) ltlltr 2..4://; smt(ge2_t).
          by move => u ge0_u lttbidx1_u; rewrite nth_rcons szadl /#.
        wp; skip => /> &2 nthadl nthadl1 szadl ge0_tidx lts_tidx ge0_kpidx _ ltl_kpidx.
        split => [| adl' tbidx' ]; 1: smt(ge1_k ge2_t).
        split => [/#| /lezNgt gekt_tbidxp nthadlp nthadlp1 nthadlp2 szadlp ge0_tbidxp lekt_tbidxp].
        rewrite -!andbA; split => [j u v ge0_j ltkpidx1_j ge0_u ltk_u ge0_v ltt_v | /#].
        case (j < kpidx{2}) => [/# | ?]; rewrite (: j = kpidx{2}) 1:/#.
        rewrite -addrA nthadlp2 2:// (: tbidx' = (k - 1) * t + t) 1:/#.
        by rewrite IntOrder.addr_ge0 1:/# 1:// /= IntOrder.ler_lt_add 1:/#. 
      wp; skip => /> &2 nthadl szadl ge0_tidx _ lts_tidx.
      split => [| adl' kpidx']; 1: smt(Top.ge1_l).
      split => [/# | /lezNgt gel_kpidxp nthadlp nthadlp1 szadlp ge0_kpidxp lel_kpidxp].
      rewrite -!andbA; split => [i j u v ge0_i lttidx1_i ge0_j ltl_j ge0_u ltk_u ge0_v ltt_v | /#].
      case (i < tidx{2}) => [/# | ?]; rewrite (: i = tidx{2}) 1:/#.
      by rewrite nthadlp1 2..4:// /#.
    wp; rnd; wp; skip => /> ps psin.
    split => [| adl tidx]; 1: smt(ge1_s).
    split => [/# | /lezNgt ges_tidx nthadl szadl ge0_tidx les_tidx].
    split => [| pkfs skfs ts xs /lezNgt ges_szskfs _ nthpkfs nthadls nthxs nthts allszl_pkfs les_skfs eqszskpkfs szts eqszxsts]; 1: smt(ge1_s).
    split => [/# | pkfs'].
    split => [/# | /lezNgt ges_szpkfsp nthpkfsp allszl_pkfsp les_szpkfsp].
    rewrite !andbA szts; split; 2: smt(dval).
    rewrite -andbA; split => [ | /#].
    rewrite &(eq_from_nth witness) 1:/# => i rng_i.
    have eql_sznthpkfs : size (nth witness pkfs i) = l by move/all_nthP: allszl_pkfs => /(_ witness i rng_i) @/(\o) ->.
    rewrite &(eq_from_nth witness) => [| j rng_j].
    * by rewrite eql_sznthpkfs; move/all_nthP: allszl_pkfsp => /(_ witness i _) /#.
    rewrite eql_sznthpkfs in rng_j; rewrite nthpkfs 3:nthpkfsp 2,4:// 1,2:/#.
    do 3! congr; rewrite &(eq_in_mkseq) => u rng_u /=.
    do 2! congr; rewrite &(eq_from_nth witness) 1:size_mkseq 1:size_take; 1: smt(ge2_t).
    * rewrite size_drop 2:size_map 2:szts 2:(: size skfs = s) 3:lez_maxr; 1..3: smt(Top.ge1_l ge1_k ge2_t).
      suff: t <= s * l * k * t - (i * l * k * t + j * k * t + u * t) by smt(ge2_t).
      rewrite IntOrder.ler_subr_addl -(addr0 (s * l * k * t)) -?addrA -?mulrA.
      rewrite leller 2://; 1,2: smt(Top.ge1_l ge1_k ge2_t).
      rewrite -(addr0 (l * (k * t))) leller 2://; 1,2: smt(ge1_k ge2_t).
      by rewrite -{2}(mul1r t) -mulrDl IntOrder.ler_pmul2r; 1,2: smt(ge2_t).
    move=> v [ge0_v]; rewrite size_mkseq lez_maxr => [| ltt_v]; 1: smt(ge2_t).
    rewrite nth_mkseq 1:// /= nth_take 2://; 1: smt(ge2_t).
    rewrite nth_drop 2://; 1: smt(Top.ge1_l ge1_k ge2_t).
    rewrite (nth_map witness) 1:szts 1:(: size skfs = s) 1:/# 2:/=. 
    * split => [| _]; 1: smt(Top.ge1_l ge1_k ge2_t).
      rewrite -(addr0 (s * l * k * t)) -?addrA -?mulrA.
      rewrite ltlltr 2://; 1,2: smt(Top.ge1_l ge1_k ge2_t).
      rewrite -(addr0 (l * (k * t))) ltlltr 2://; 1,2: smt(ge1_k ge2_t).
      by rewrite -(addr0 (k * t)) ltlltr 2://; 1,2: smt(ge2_t).
    by rewrite nthts 1:/# 1..3:// nthxs 1:/#.
  inline{2} 13; inline{2} 12; inline{2} 11.
  wp 30 10 => /=.
  conseq (: _ 
            ==> 
               is_fresh{1} 
            /\ !EUF_CMA_MFORSTWESNPRF_V.valid_ITSR{1} 
            /\ EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE{1} 
            =>
               ! (i{2} \in O_SMDTOpenPRE_Default.os{2})
            /\ f pp{2} tw{2} x{2} = y{2}).
  - move=> &1 &2 [#] eqgl adval eqrad eqad eqpspp eqps0 eqppo eqppr osval lidxsval mmapval equnz2ts_lfs eqpkfs nthxs nthts szts eqszxsts valitsr valop isf isv os i tw x y + [#] isvT isfT valistrF valopT.
    rewrite isfT valistrF valopT /= => -[nini eqy_fx].
    rewrite nini eqy_fx szts /=; split; 1: smt(dval ge1_s Top.ge1_l ge1_k ge2_t).
    rewrite nth_uniq => u v; rewrite size_map => rng_u rng_v nequ_v.
    rewrite 2?(nth_map witness) 1:rng_u 1:rng_v /=; move: (nequ_v).
    rewrite (divz_eq u (l * k * t)) (divz_eq v (l * k * t)).
    rewrite (divz_eq (u %% (l * k * t)) (k * t)) (divz_eq (v %% (l * k * t)) (k * t)).
    rewrite 2?modz_dvd 1,2:-mulrA 1,2:dvdz_mull 1,2:dvdzz.
    rewrite (divz_eq (u %% (k * t)) t) (divz_eq (v %% (k * t)) t).
    rewrite 2?modz_dvd 1,2:dvdz_mull 1,2:dvdzz ?mulrA ?addrA => dsnequ_v.
    have rng_udlkt : 0 <= u %/ (l * k * t) && u %/ (l * k * t) < s.
    * by rewrite divz_ge0 2:ltz_divLR; smt(Top.ge1_l ge1_k ge2_t dval).
    have rng_vdlkt : 0 <= v %/ (l * k * t) && v %/ (l * k * t) < s.
    * by rewrite divz_ge0 2:ltz_divLR; smt(Top.ge1_l ge1_k ge2_t dval).
    have rng_udkt : 0 <= u %% (l * k * t) %/ (k * t) && u %% (l * k * t) %/ (k * t) < l.
    + by rewrite divz_ge0 2:modz_ge0 3:ltz_divLR 4:mulrA 4:ltz_pmod 5://; smt(Top.ge1_l ge1_k ge2_t).
    have rng_vdkt : 0 <= v %% (l * k * t) %/ (k * t) && v %% (l * k * t) %/ (k * t) < l.
    + by rewrite divz_ge0 2:modz_ge0 3:ltz_divLR 4:mulrA 4:ltz_pmod 5://; smt(Top.ge1_l ge1_k ge2_t).
    have rng_udt : 0 <= u %% (k * t) %/ t && u %% (k * t) %/ t < k.
    + by rewrite divz_ge0 2:modz_ge0 3:ltz_divLR 4:ltz_pmod 5://; smt(ge1_k ge2_t).
    have rng_vdt : 0 <= v %% (k * t) %/ t && v %% (k * t) %/ t < k.
    + by rewrite divz_ge0 2:modz_ge0 3:ltz_divLR 4:ltz_pmod 5://; smt(ge1_k ge2_t).
    have rng_udtdv : 0 <= u %% (k * t) %/ t * t + u %% t && u %% (k * t) %/ t * t + u %% t < k * nr_nodes 0.
    + rewrite addr_ge0 1:mulr_ge0 1:divz_ge0 4:modz_ge0 5:/=; 1..4: smt(ge2_t).
      rewrite /nr_nodes /= -/t {2}(: k = k - 1 + 1) 1:// mulrDl.
      rewrite ler_lt_add 1:ler_pmul2r 3:/= 3:ltz_pmod; 1,3: smt(ge2_t).
      suff /#: u %% (k * t) %/ t < k. 
      by rewrite ltz_divLR 2:ltz_pmod; 1,2: smt(ge1_k ge2_t).
    have rng_vdtdv : 0 <= v %% (k * t) %/ t * t + v %% t && v %% (k * t) %/ t * t + v %% t < k * nr_nodes 0.
    + rewrite addr_ge0 1:mulr_ge0 1:divz_ge0 4:modz_ge0 5:/=; 1..4: smt(ge2_t).
      rewrite /nr_nodes /= -/t {2}(: k = k - 1 + 1) 1:// mulrDl.
      rewrite ler_lt_add 1:ler_pmul2r 3:/= 3:ltz_pmod; 1,3: smt(ge2_t).
      suff /#: u %% (k * t) %/ t < k. 
      by rewrite ltz_divLR 2:ltz_pmod; 1,2: smt(ge1_k ge2_t).
    rewrite 2?nthts 1,2,3,5,6,7:// 1,2:modz_ge0 2,4:ltz_pmod 3,6://; 1..4:smt(ge2_t).
    rewrite -eq_adrs_idxsq negb_forall /= /eq_idx /get_idx.
    have :
      u %/ (l * k * t) <> v %/ (l * k * t) 
      \/ 
      u %% (l * k * t) %/ (k * t) <> v %% (l * k * t) %/ (k * t)
      \/
      u %% (k * t) %/ t * t + u %% t <> v %% (k * t) %/ t * t + v %% t by smt().
    move=> [neqdlkt | [neqdkt | neqdt ]]; [exists 4 | exists 2 | exists 0]. 
    * by rewrite neqtidx_setthtbkpt 2..5,8..11:// 1:-eqrad 1:adval 1:valf_adz; 1,2:smt(ge1_a).
    * by rewrite neqkpidx_setthtbkpt 2..5,8..11:// 1:-eqrad 1:adval 1:valf_adz; 1,2:smt(ge1_a).
    by rewrite neqtbidx_setthtbkpt 2..5,8..11:// 1:-eqrad 1:adval 1:valf_adz; 1,2:smt(ge1_a).
  inline{2} 10.
  wp => /=.
  while{1} (   leaves'{1} 
               =
               mkseq (fun (i : int) => 
                         f ps{1} (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad{1} trhtype) tidx{1}) kpidx{1}) 
                                              0 (i * t + (nth witness lidxs'{1} i).`3)) 
                           (val (nth witness (val sigFORSTW'{1}) i).`1)) (size roots'{1})
            /\ size roots'{1} = size skFORS_eles'{1}
            /\ size roots'{1} = size leaves'{1}
            /\ size roots'{1} <= k)
           (k - size roots'{1}).
  - move=> _ z.
    wp; skip => /> &2 eqszrsskfelesp _ _ ltk_szrs.
    by rewrite ?size_rcons mkseqS 1:size_ge0 /= size_mkseq lez_maxr 1:size_ge0 /= /#.
  wp => /=.
  call (:   O_CMA_MFORSTWESNPRF.sk{1}.`2 = R_FSMDTOpenPRE_EUFCMA.ps{2}
         /\ O_CMA_MFORSTWESNPRF.sk{1}.`3 = R_FSMDTOpenPRE_EUFCMA.ad{2}
         /\ O_SMDTOpenPRE_Default.pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
         /\ ={mmap}(O_CMA_MFORSTWESNPRF, R_FSMDTOpenPRE_EUFCMA)
         /\ ={lidxs}(O_CMA_MFORSTWESNPRF_AV, R_FSMDTOpenPRE_EUFCMA)
         /\ dom O_CMA_MFORSTWESNPRF.mmap{1} = mem O_CMA_MFORSTWESNPRF.qs{1}
         /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness R_FSMDTOpenPRE_EUFCMA.leavess{2} (i * l * k * t + j * k * t + u * t + v)
                =
                f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                  (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)))
         /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
              nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)
              =
              val (nth witness (nth witness (val (nth witness (nth witness O_CMA_MFORSTWESNPRF.sk{1}.`1 i) j)) u) v))
         /\ (forall (m : msg),
              m \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
              =>
              all (mem R_FSMDTOpenPRE_EUFCMA.lidxs{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m]) m)))
         /\ (forall (idxs : int * int * int),
              idxs \in R_FSMDTOpenPRE_EUFCMA.lidxs{2}
              <=>
              (0 <= idxs.`1 < d /\ 0 <= idxs.`2 < k /\ 0 <= idxs.`3 < t /\  
               idxs.`1 %/ l * l * k * t +
               idxs.`1 %% l * k * t +
               idxs.`2 * t +
               idxs.`3 \in
               O_SMDTOpenPRE_Default.os{2}))
         /\ size R_FSMDTOpenPRE_EUFCMA.leavess{2} = d * k * t).
  - proc.
    inline{1} 7.
    wp; sp 1 0 => /=.
    if => //.
    * while (   ={tidx, kpidx, idx}
             /\ O_SMDTOpenPRE_Default.pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
             /\ m{2} \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
             /\ (cm, idx){2} = mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2}
             /\ tidx{2} = val idx{2} %/ l
             /\ kpidx{2} = val idx{2} %% l
             /\ sig{1} = sigFORSTW{2}
             /\ m0{1} = cm{2}
             /\ ps0{1} = R_FSMDTOpenPRE_EUFCMA.ps{2}
             /\ ad0{1} = set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) tidx{2}) kpidx{2}
             /\ skFORS0{1} = nth witness (nth witness skFORSs{1} tidx{1}) kpidx{1}
             /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                  nth witness R_FSMDTOpenPRE_EUFCMA.leavess{2} (i * l * k * t + j * k * t + u * t + v)
                  =
                  f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                    (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)))
             /\ (forall (i j u v : int),
                   0 <= i && i < s =>
                   0 <= j && j < l =>
                   0 <= u && u < k =>
                   0 <= v && v < t =>
                   nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v) 
                   =
                   val (nth witness (nth witness (val (nth witness (nth witness skFORSs{1} i) j)) u) v))
             /\ (forall (m : msg),
                  m \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
                  =>
                  all (mem R_FSMDTOpenPRE_EUFCMA.lidxs{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m]) m)))
             /\ (forall (idxs : int * int * int),
                  idxs \in R_FSMDTOpenPRE_EUFCMA.lidxs{2}
                  <=>
                  (0 <= idxs.`1 < d /\ 0 <= idxs.`2 < k /\ 0 <= idxs.`3 < t /\
                  (idxs.`1 %/ l * l * k * t +
                  idxs.`1 %% l * k * t +
                  idxs.`2 * t +
                  idxs.`3 \in
                  O_SMDTOpenPRE_Default.os{2}
                  \/ 
                  idxs \in drop (size sigFORSTW{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2})))))
             /\ size R_FSMDTOpenPRE_EUFCMA.leavess{2} = d * k * t
             /\ size sig{1} <= k).
      + inline{1} 4; inline{2} 3.
        wp => /=.
        while{1} (   leaves0{1} 
                     = 
                     mkseq (fun (i : int) =>
                             f ps1{1} (set_thtbidx ad1{1} 0 (idxt{1} * t + i)) (val (nth witness (nth witness (val skFORS1{1}) idxt{1}) i))) (size leaves0{1})
                  /\ size leaves0{1} <= t)
                 (t - size leaves0{1}).
        - move=> _ z.
          wp; skip => /> &2 lfsdef _ ltt_szlfs.
          by rewrite ?size_rcons mkseqS 1:size_ge0 /= /#. 
        wp; skip => /> &1 &2 minm cmidxval nthlfs nthxs mmapimpl lidxsdef szlfs _ ltk_szsigf.
        split => [| lfs]; 1: by rewrite mkseq0 /=; smt(ge2_t).
        split => [/# | /lezNgt get_szlfs lfsdef let_szlfs].
        rewrite ?size_rcons !andbA -2!andbA; split => [| /#].
        split => [| idxs].
        - congr; rewrite nthxs 3:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 6://; 1..5: smt(Top.ge1_l Index.valP dval).
          * pose rtd := rev _; rewrite /t (: a = size rtd) 2:bs2int_ge0 2:bs2int_le2Xs 2://.
            rewrite /rtd size_rev size_take 2:size_drop; 1,2: smt(ge1_a size_ge0).
            rewrite valP (: k = k - size sigFORSTW{2} + size sigFORSTW{2}) 1:/# mulrDl -addrA (mulrC a) subrr /=.
            have: 1 <= k - size sigFORSTW{2} by smt().
            case => [gt1_ks | <- /=]; 2: smt(ge1_a).
            rewrite lez_maxr 2:(: a < (k - size sigFORSTW{2}) * a) 3://; 1: smt(ge1_a).
            by rewrite -ltz_divLR 2:divzz; 1,2: smt(ge1_a).
          rewrite valKd /=; do 2! congr; rewrite lfsdef.
          rewrite &(eq_from_nth witness).
          * rewrite size_mkseq size_take 2:size_drop 3:szlfs; 1,2: smt(divz_ge0 modz_ge0 size_ge0 Top.ge1_l ge1_k ge2_t Index.valP).
            suff: t <= d * k * t - (val idx{2} %/ l * l * k * t + val idx{2} %% l * k * t + size sigFORSTW{2} * t) by smt(ge2_t).
            rewrite ler_subr_addl -2!(mulrA _ k t) -mulrDl -divz_eq.
            rewrite -(addr0 (d * k * t)) -?addrA -?mulrA.
            rewrite leller 2://; 1,2: smt(ge1_k ge2_t Index.valP).
            by rewrite -{2}(mul1r t) -mulrDl IntOrder.ler_pmul2r; 1,2: smt(ge2_t).
          move=> i [ge0_i]; rewrite size_mkseq => ltt_i.
          rewrite nth_mkseq 1:/# /= nth_take; 1,2: smt(ge2_t).
          rewrite nth_drop 2://; 1: smt(divz_ge0 modz_ge0 size_ge0 Top.ge1_l ge1_k ge2_t Index.valP).
          rewrite nthlfs 3:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 3:-dval 3:valP 5://; 1..5: smt(Top.ge1_l).
          by rewrite nthxs 3,5:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 3:-dval 3:valP 5://; 1..5: smt(Top.ge1_l).
        split => [/lidxsdef [#] ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3 |].
        - rewrite ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3 mem_rcons /= => -[-> //|].
          rewrite -(cat_take_drop (0 + 1) (drop (size sigFORSTW{2}) _)) (take_nth witness) 1:size_drop 1:size_ge0 /= 1:/g /= 1:size_mkseq 1:/#.
          rewrite take0 /= drop_drop 1:// 1:size_ge0 (addrC 1) => -[-> /= | -> //].
          left; left; rewrite nth_drop 1:size_ge0 1:// /g /= nth_mkseq 1:size_ge0 1:/# /=.
          by rewrite /chunk nth_mkseq 1:size_ge0 1:valP /= 1:mulzK 3:-cmidxval; 1,2: smt(ge1_a).
        rewrite mem_rcons /= => ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3. 
        move=> -[[idxsval |]|]; 2,3: rewrite lidxsdef.
        - move: (mmapimpl m{2} minm); rewrite -cmidxval allP => /(_ idxs).
          apply => @/g /=; rewrite mkseqP /=; exists (size sigFORSTW{2}).
          split; 1: smt(size_ge0).
          move: ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3 idxsval. 
          case: idxs => id1 id2 id3 /= ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3. 
          rewrite &(contraLR) ?negb_and /chunk nth_mkseq 1:valP 1:mulzK 2:// /=; 1: smt(ge1_a).
          move => neqids; rewrite -4!(mulrA _ k t) -2!mulrDl -2!divz_eq ?mulrA.
          rewrite neqsmnt 1..3,5,6:// bs2int_ge0 /=.
          pose rtd := rev _; rewrite /t (: a = size rtd) 2:bs2int_le2Xs.
          rewrite /rtd size_rev size_take 2:size_drop; 1,2: smt(ge1_a size_ge0).
          rewrite valP; suff: a <= k * a - a * size sigFORSTW{2} by smt().
          rewrite IntOrder.ler_subr_addr (: a + a * size sigFORSTW{2} = (size sigFORSTW{2} + 1) * a) 1:/#.
          by rewrite IntOrder.ler_pmul 3:/#; smt(ge1_a size_ge0).
        - by move=> ->.
        rewrite -(cat_take_drop (0 + 1) (drop (size sigFORSTW{2}) _)) (take_nth witness) 
                 1:size_drop 1:size_ge0 /= 1:/g /= 1:size_mkseq 1:/#.
        by rewrite take0 /= drop_drop 1:// 1:size_ge0 (addrC 1) => ->.
      wp; rnd; skip => /> &1 &2 eqdomem nthlfs nthxs mmapimpl lidxsdef szlfs mninmmap mkl mklin.
      rewrite ?mem_set /=; split=> [| os sigf /lezNgt gek_szsigf _ _ mmapimplcat lidxsdefcat lek_szsigf].
      + split => [/# |].
        split => [m' |].
        - rewrite mem_set allP => + idxs; rewrite mem_cat.
          case (m' = m{2}) => [eqmm /= | neqmm /= /mmapimpl].
          * by rewrite eqmm get_set_sameE oget_some => ->.
          rewrite get_setE neqmm /= allP => /(_ idxs) + idxsin.
          by move=> /(_ idxsin) => ->.
        split => [idxs |]; 2: smt(ge1_k).
        rewrite drop0 ?mem_cat ?get_set_sameE ?oget_some. 
        split => [[/lidxsdef /# | idxsin /=] | /#].
        rewrite idxsin /=; move: idxsin => @/g /=; rewrite mkseqP => -[i] [rng_i -> /=].
        split; 2: split; 1,2: smt(Index.valP).
        rewrite bs2int_ge0 /=; pose rtd := rev _; rewrite /t (: a = size rtd) 2:bs2int_le2Xs.
        rewrite /rtd size_rev /chunk nth_mkseq.
        rewrite valP mulzK 2://; 1: smt(ge1_a).
        rewrite /= size_take 2:size_drop; 1,2: smt(ge1_a size_ge0).
        rewrite valP; suff: a <= k * a - a * i by smt().
        rewrite IntOrder.ler_subr_addr (: a + a * i = (i + 1) * a) 1:/#.
        by rewrite IntOrder.ler_pmul 1:/# 2://; smt(ge1_a).
      split=> [| idxs]; 1: by rewrite fun_ext => x; 1: rewrite mem_set mem_rcons /#.
      rewrite lidxsdefcat; pose gmco := g _.
      rewrite (: size sigf = size gmco) 2:drop_size 2:/#.
      by rewrite /gmco /g /= size_mkseq; smt(ge1_k).
    while (   ={tidx, kpidx, idx}
           /\ O_SMDTOpenPRE_Default.pp{2} = R_FSMDTOpenPRE_EUFCMA.ps{2}
           /\ m{2} \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
           /\ (cm, idx){2} = mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2}
           /\ tidx{2} = val idx{2} %/ l
           /\ kpidx{2} = val idx{2} %% l
           /\ sig{1} = sigFORSTW{2}
           /\ m0{1} = cm{2}
           /\ ps0{1} = R_FSMDTOpenPRE_EUFCMA.ps{2}
           /\ ad0{1} = set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) tidx{2}) kpidx{2}
           /\ skFORS0{1} = nth witness (nth witness skFORSs{1} tidx{1}) kpidx{1}
           /\ (forall (i j u v : int), 0 <= i < s => 0 <= j < l => 0 <= u < k => 0 <= v < t =>
                nth witness R_FSMDTOpenPRE_EUFCMA.leavess{2} (i * l * k * t + j * k * t + u * t + v)
                =
                f O_SMDTOpenPRE_Default.pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_FSMDTOpenPRE_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + v))
                  (nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v)))
           /\ (forall (i j u v : int),
                 0 <= i && i < s =>
                 0 <= j && j < l =>
                 0 <= u && u < k =>
                 0 <= v && v < t =>
                 nth witness O_SMDTOpenPRE_Default.xs{2} (i * l * k * t + j * k * t + u * t + v) 
                 =
                 val (nth witness (nth witness (val (nth witness (nth witness skFORSs{1} i) j)) u) v))
           /\ (forall (m : msg),
              m \in R_FSMDTOpenPRE_EUFCMA.mmap{2}
              =>
              all (mem R_FSMDTOpenPRE_EUFCMA.lidxs{2}) (g (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m]) m)))
           /\ (forall (idxs : int * int * int),
              idxs \in R_FSMDTOpenPRE_EUFCMA.lidxs{2}
              <=>
              (0 <= idxs.`1 < d /\ 0 <= idxs.`2 < k /\ 0 <= idxs.`3 < t /\
              idxs.`1 %/ l * l * k * t +
              idxs.`1 %% l * k * t +
              idxs.`2 * t +
              idxs.`3 \in
              O_SMDTOpenPRE_Default.os{2}))
           /\ size R_FSMDTOpenPRE_EUFCMA.leavess{2} = d * k * t
           /\ size sig{1} <= k).
    * inline{1} 4; inline{2} 3.
      wp => /=.
      while{1} (   leaves0{1} 
                   = 
                   mkseq (fun (i : int) =>
                           f ps1{1} (set_thtbidx ad1{1} 0 (idxt{1} * t + i)) (val (nth witness (nth witness (val skFORS1{1}) idxt{1}) i))) (size leaves0{1})
                /\ size leaves0{1} <= t)
               (t - size leaves0{1}).
      + move=> _ z.
        wp; skip => /> &1 lfsdef _ ltt_szlfs.
        by rewrite ?size_rcons mkseqS 1:size_ge0 /= /#.
      wp; skip => /> &1 &2 minm cmidxval nthlfs nthxs mmapimpl lidxsdef szlfs _ ltk_szsigf.
      split => [| lfs]; 1: by rewrite mkseq0; smt(ge2_t).
      split => [/# | /lezNgt get_szlfs lfsdef let_szlfs].
      rewrite ?size_rcons !andbA -2!andbA; split => [|/#].
      split => [| idxs].
      + rewrite nthxs 3,5:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 3:-dval 3:valP 5://; 1..4: smt(Top.ge1_l).
        - rewrite bs2int_ge0 /=; pose rtd := rev _; rewrite /t (: a = size rtd) 2:bs2int_le2Xs.
          rewrite /rtd size_rev size_take 2:size_drop; 1,2: smt(ge1_a size_ge0).
          rewrite valP; suff: a <= k * a - a * size sigFORSTW{2} by smt().
          rewrite IntOrder.ler_subr_addr (: a + a * size sigFORSTW{2} = (size sigFORSTW{2} + 1) * a) 1:/#.
          by rewrite IntOrder.ler_pmul 3://; smt(size_ge0 ge1_a).
        rewrite valKd; congr => /=.
        do 2! congr; rewrite lfsdef.  
        rewrite &(eq_from_nth witness).
        - rewrite size_mkseq size_take 2:size_drop 3:szlfs; 1,2: smt(divz_ge0 modz_ge0 size_ge0 Top.ge1_l ge1_k ge2_t Index.valP).
          suff: t <= d * k * t - (val idx{2} %/ l * l * k * t + val idx{2} %% l * k * t + size sigFORSTW{2} * t) by smt(ge2_t).
          rewrite ler_subr_addl -2!(mulrA _ k t) -mulrDl -divz_eq.
          rewrite -(addr0 (d * k * t)) -?addrA -?mulrA.
          rewrite leller 2://; 1,2: smt(ge1_k ge2_t Index.valP).
          by rewrite -{2}(mul1r t) -mulrDl IntOrder.ler_pmul2r; 1,2: smt(ge2_t).
        move=> i [ge0_i]; rewrite size_mkseq => ltt_i.
        rewrite nth_mkseq 1:/# /= nth_take; 1,2: smt(ge2_t).
        rewrite nth_drop 2://; 1: smt(divz_ge0 modz_ge0 size_ge0 Top.ge1_l ge1_k ge2_t Index.valP).
        rewrite nthlfs 3:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 3:-dval 3:valP 5://; 1..5: smt(Top.ge1_l).
        by rewrite nthxs 3,5:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 3:-dval 3:valP 5://; 1..5: smt(Top.ge1_l).
      split => [/lidxsdef [#] ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3 |]; 1: by rewrite mem_rcons /= /#.
      rewrite mem_rcons /= => ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3. 
      move=> -[idxsval |]; 2: by rewrite lidxsdef.
      move: (mmapimpl m{2} minm); rewrite -cmidxval allP => /(_ idxs).
      apply => @/g /=; rewrite mkseqP /=; exists (size sigFORSTW{2}).
      split; 1: smt(size_ge0).
      move: ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3 idxsval. 
      case: idxs => id1 id2 id3 /= ge0_id1 ltd_id1 ge0_id2 ltk_id2 ge0_id3 ltt_id3.
      rewrite &(contraLR) ?negb_and /chunk nth_mkseq 1:valP 1:mulzK 2:// /=; 1: smt(ge1_a).
      move => neqids; rewrite -4!(mulrA _ k t) -2!mulrDl -2!divz_eq ?mulrA.
      rewrite neqsmnt 1..3,5,6:// bs2int_ge0 /=.
      pose rtd := rev _; rewrite /t (: a = size rtd) 2:bs2int_le2Xs.
      rewrite /rtd size_rev size_take 2:size_drop; 1,2: smt(ge1_a size_ge0).
      rewrite valP; suff: a <= k * a - a * size sigFORSTW{2} by smt().
      rewrite IntOrder.ler_subr_addr (: a + a * size sigFORSTW{2} = (size sigFORSTW{2} + 1) * a) 1:/#.
      by rewrite IntOrder.ler_pmul 3:/#; smt(ge1_a size_ge0).
    by wp; skip => />; smt(ge1_k).
  inline{1} 4; inline{1} 5.
  wp; skip => /> &1 &2 nthxs nthts szts eqsztsxs.
  split => [| eqdm0 _ _ _ sig qs mks lidxs mmap os eqdm mmaplidxsrel lidxsdef].
  - split; 1: by rewrite fun_ext => x; rewrite mem_empty.
    rewrite size_map szts /=; split => [i j u v * | m]; 2: by rewrite mem_empty. 
    rewrite (nth_map witness witness) /= 2:nthts 2..6:// szts.
    split => [| _]; 1: smt(Top.ge1_l ge1_k ge2_t).
    rewrite -(addr0 (d * k * t)) dval -?addrA -?mulrA.
    rewrite ltlltr 2://; 1,2: smt(Top.ge1_l ge1_k ge2_t).
    rewrite -(addr0 (l * (k * t))) ltlltr 2://; 1,2: smt(ge1_k ge2_t).
    by rewrite -(addr0 (k * t)) ltlltr 2://; 1,2: smt(ge2_t).
  split => [| rs' skfeles']; 1: by rewrite mkseq0 /=; smt(ge1_k).
  split => [/# | /lezNgt gek_szrsp eqszrsskfep _ lek_szrsp ninqs_sig1].
  pose cmidx := mco _ _; pose fit := List.find _ _.
  rewrite negb_and negb_forall /= => -[| /mem_zip_snd /=]; 2: by rewrite ninqs_sig1.
  move=> -[idxs]; rewrite negb_imply => -[idxsing idxsninlidxs].
  have hasnin : has (fun (idxs : int * int * int) => ! (idxs \in lidxs)) (g (cmidx.`1, cmidx.`2)).
  - by rewrite hasP; exists idxs.
  have rng_fit : 0 <= fit < k.
  - by rewrite find_ge0 /= (: k = size (g (cmidx.`1, cmidx.`2))) 1:/g 1:/= 1:size_mkseq 2:-has_find 2:hasnin; smt(ge1_k).
  move/nth_find: (hasnin) => /= /(_ witness) /= nthgnin.
  rewrite (: val cmidx.`2 = (nth witness (g (cmidx.`1, cmidx.`2)) fit).`1) 1:/cmidx 1:/g /= 1:nth_mkseq 1:rng_fit 1://.
  rewrite nth_mkseq 1:/g /= 1:?nth_mkseq 1:// 1:/= 1:/#.
  have bsltt : bs2int (rev (nth witness (chunk a (val cmidx.`1)) fit)) < t.
  - pose rtd := rev _; rewrite /t (: a = size rtd) 2:bs2int_le2Xs /=.
    rewrite /rtd size_rev /chunk nth_mkseq; 1: rewrite valP mulzK 2://; 1: smt(ge1_a).
    rewrite /= size_take 2:size_drop; 1,2: smt(ge1_a size_ge0).
    rewrite valP; suff: a <= k * a - a * fit by smt().
    rewrite IntOrder.ler_subr_addr (: a + a * fit = (fit + 1) * a) 1:/#.
    by rewrite IntOrder.ler_pmul 1:/# 2://; smt(ge1_a). 
  move=> eqlf; split.
  - move/iffRL /contra: (lidxsdef (nth witness (g (cmidx.`1, cmidx.`2)) fit)).
    rewrite /g /= nth_mkseq 1:// /= rng_fit bs2int_ge0 /= bsltt.
    move: (Index.valP cmidx.`2) => -> /=; apply.
    by move: nthgnin => @/g /=; rewrite nth_mkseq 1://.
  move: eqlf; rewrite /g /= nth_mkseq 1:// /= => eqlf.
  rewrite nthts 3:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 6:// 6:bs2int_ge0 6:bsltt 6://; 1..5: smt(Top.ge1_l Index.valP dval).
  rewrite nthxs 3:// 1:divz_ge0 2:ltz_divLR 4:modz_ge0 5:ltz_pmod 6:// 6:bs2int_ge0 6:bsltt 6://; 1..5: smt(Top.ge1_l Index.valP dval).
  rewrite -eqlf /= /chunk ?nth_mkseq 1:valP 1:mulzK 2,3://; 1: smt(ge1_a).
  by do ? congr => /=; rewrite nth_mkseq 1:valP 1:mulzK 2://;1: smt(ge1_a).
have ->:
  Pr[EUF_CMA_MFORSTWESNPRF_V.main() @ &m : (res /\ !EUF_CMA_MFORSTWESNPRF_V.valid_ITSR) /\ !EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE]
  =
  Pr[EUF_CMA_MFORSTWESNPRF_VI.main() @ &m : res /\ !EUF_CMA_MFORSTWESNPRF_V.valid_ITSR /\ !EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE].
+ by byequiv Eqv_EUF_CMA_MFORSTWESNPRF_V_VI.
rewrite Pr[mu_split EUF_CMA_MFORSTWESNPRF_V.valid_TRHTCR] StdOrder.RealOrder.ler_add.
+ byequiv=> //.
  proc.
  inline{2} 5; inline{2} 4.
  seq 9 12 : (   ={glob A, glob O_CMA_MFORSTWESNPRF_AV, ps}
              /\ ps{1} = pp{2}
              /\ ad{1} = adz
              /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}
              /\ skFORSs{1} = R_TRHSMDTTCRC_EUFCMA.skFORSs{2}
              /\ pkFORSs{1} = R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
              /\ (forall (i j u v w : int), 0 <= i < s => 0 <= j < Top.l => 0 <= u < k => 0 <= v < a => 0 <= w < nr_nodes (v + 1) => 
                   nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                       (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                        bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                   =
                   (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) (v + 1) (u * nr_nodes (v + 1) + w),
                    let leavesl 
                        = 
                        mkseq (fun (m : int) => 
                                  f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + m)) 
                                    (val (nth witness (nth witness (val (nth witness (nth witness R_TRHSMDTTCRC_EUFCMA.skFORSs{2} i) j)) u) m))) t in
                      val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                          (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                      ++
                      val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                          (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))

              /\ uniq (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
              /\ all (fun (ad : adrs) => get_typeidx ad = trhtype /\ get_thidx ad <> 0) (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
              /\ all (fun (ad : adrs) => get_typeidx ad = trcotype \/ get_thidx ad = 0) (TRHC.O_THFC_Default.tws{2})
              /\ size TRHC_TCR.O_SMDTTCR_Default.ts{2} = d * k * (t - 1)).
  - swap{2} 4 -3.
    seq 2 2 : (   ={glob A}
               /\ ps{1} = pp{2}
               /\ ad{1} = adz
               /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}); 1: by rnd; wp; skip.
    inline{1} 7; inline{1} 8.
    inline{2} 10; inline{2} 11.
    wp => /=.
    while (   ps{1} = pp{2}
           /\ ps{1} = TRHC.O_THFC_Default.pp{2}
           /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
           /\ ad{1} = adz
           /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}
           /\ skFORSs{1} = R_TRHSMDTTCRC_EUFCMA.skFORSs{2}
           /\ pkFORSs{1} = R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
           /\ leavess{1} = R_TRHSMDTTCRC_EUFCMA.leavess{2}
           /\ nodess{1} = R_TRHSMDTTCRC_EUFCMA.nodess{2}
           /\ rootss{1} = R_TRHSMDTTCRC_EUFCMA.rootss{2}
           /\ (forall (adx : adrs * dgst),
                 adx \in TRHC_TCR.O_SMDTTCR_Default.ts{2}
                 <=>
                 (exists (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} /\ 0 <= j < Top.l /\ 0 <= u < k /\ 
                                            0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                   adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                             (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                              bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)))
           /\ (forall (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} => 0 <= j < Top.l => 0 <= u < k => 
                                         0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                 nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                     (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                      bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                 =
                 (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) (v + 1) (u * nr_nodes (v + 1) + w),
                  let leavesl 
                      = 
                      mkseq (fun (m : int) => 
                                f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + m)) 
                                  (val (nth witness (nth witness (val (nth witness (nth witness R_TRHSMDTTCRC_EUFCMA.skFORSs{2} i) j)) u) m))) t in
                    val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                        (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                    ++
                    val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                        (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
           /\ uniq (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
           /\ all (fun (ad : adrs) => get_typeidx ad = trhtype /\ get_thidx ad <> 0) (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
           /\ all (fun (ad : adrs) => get_typeidx ad = trcotype \/ get_thidx ad = 0) (TRHC.O_THFC_Default.tws{2})
           /\ size TRHC_TCR.O_SMDTTCR_Default.ts{2} = size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * l * k * (t - 1)
           /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
           /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.leavess{2}
           /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.nodess{2}
           /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.rootss{2}
           /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} <= s).
    * wp => /=.
      while (   ={skFORSl, pkFORSl, leavesl, nodesl, rootsl}
             /\ ps{1} = pp{2}
             /\ ps{1} = TRHC.O_THFC_Default.pp{2}
             /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
             /\ ad{1} = adz
             /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}
             /\ skFORSs{1} = R_TRHSMDTTCRC_EUFCMA.skFORSs{2}
             /\ pkFORSs{1} = R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
             /\ nodess{1} = R_TRHSMDTTCRC_EUFCMA.nodess{2}
             /\ (forall (adx : adrs * dgst),
                   adx \in TRHC_TCR.O_SMDTTCR_Default.ts{2}
                   <=>
                   (exists (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} /\ 0 <= j < Top.l /\ 0 <= u < k /\ 
                                              0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                     adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                               (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                   \/
                   (exists (j u v w : int), 0 <= j < size skFORSl{2} /\ 0 <= u < k /\ 
                                            0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                     adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                               (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)))
             /\ (forall (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} => 0 <= j < Top.l => 0 <= u < k => 
                                           0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                   nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                       (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                        bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                   =
                   (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) (v + 1) (u * nr_nodes (v + 1) + w),
                    let leavesl 
                        = 
                        mkseq (fun (m : int) => 
                                  f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + m)) 
                                    (val (nth witness (nth witness (val (nth witness (nth witness R_TRHSMDTTCRC_EUFCMA.skFORSs{2} i) j)) u) m))) t in
                      val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                          (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                      ++
                      val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                          (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
             /\ (forall (j u v w : int), 0 <= j < size skFORSl{2} => 0 <= u < k => 
                                         0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                   nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                       (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                        bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                   =
                   (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                (v + 1) (u * nr_nodes (v + 1) + w),
                    let leavesl 
                        = 
                        mkseq (fun (m : int) => 
                                  f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                          0 (u * t + m)) 
                                    (val (nth witness (nth witness (val (nth witness skFORSl{2} j)) u) m))) t in
                      val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                          (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                      ++
                      val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                          (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
             /\ uniq (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
             /\ all (fun (ad : adrs) => get_typeidx ad = trhtype /\ get_thidx ad <> 0) (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
             /\ all (fun (ad : adrs) => get_typeidx ad = trcotype \/ get_thidx ad = 0) (TRHC.O_THFC_Default.tws{2})
             /\ size TRHC_TCR.O_SMDTTCR_Default.ts{2} = size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * l * k * (t - 1) + size skFORSl{2} * k * (t - 1)
             /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
             /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.leavess{2}
             /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.nodess{2}
             /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.rootss{2}
             /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} < s
             /\ size skFORSl{2} = size pkFORSl{2}
             /\ size skFORSl{2} = size leavesl{2}
             /\ size skFORSl{2} = size nodesl{2}
             /\ size skFORSl{2} = size rootsl{2}
             /\ size skFORSl{2} <= l).
      * inline{2} 6. 
        wp => /=.
        while (   ={skFORSl, pkFORSl, leavesl, nodesl, rootsl, nodesk, rootsk}
               /\ ps{1} = pp{2}
               /\ ps{1} = TRHC.O_THFC_Default.pp{2}
               /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
               /\ ad{1} = adz
               /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}
               /\ skFORSs{1} = R_TRHSMDTTCRC_EUFCMA.skFORSs{2}
               /\ pkFORSs{1} = R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
               /\ nodess{1} = R_TRHSMDTTCRC_EUFCMA.nodess{2}
               /\ skFORS{1} = skFORS0{2}
               /\ leavesk{1} = leavesk0{2}
               /\ (forall (adx : adrs * dgst),
                     adx \in TRHC_TCR.O_SMDTTCR_Default.ts{2}
                     <=>
                     (exists (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} /\ 0 <= j < Top.l /\ 0 <= u < k /\ 
                                                0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                       adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                 (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                  bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                     \/
                     (exists (j u v w : int), 0 <= j < size skFORSl{2} /\ 0 <= u < k /\ 
                                              0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                       adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                 (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                  bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                     \/
                     (exists (u v w : int), 0 <= u < size leavesk0{2} /\ 
                                            0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                       adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                 (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                  bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)))
               /\ (forall (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} => 0 <= j < Top.l => 0 <= u < k => 
                                             0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                     nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                         (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                          bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                     =
                     (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) (v + 1) (u * nr_nodes (v + 1) + w),
                      let leavesl 
                          = 
                          mkseq (fun (m : int) => 
                                    f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + m)) 
                                      (val (nth witness (nth witness (val (nth witness (nth witness R_TRHSMDTTCRC_EUFCMA.skFORSs{2} i) j)) u) m))) t in
                        val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                            (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                        ++
                        val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                            (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
               /\ (forall (j u v w : int), 0 <= j < size skFORSl{2} => 0 <= u < k => 
                                           0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                     nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                         (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                          bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                     =
                     (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                  (v + 1) (u * nr_nodes (v + 1) + w),
                      let leavesl 
                          = 
                          mkseq (fun (m : int) => 
                                    f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                            0 (u * t + m)) 
                                      (val (nth witness (nth witness (val (nth witness skFORSl{2} j)) u) m))) t in
                        val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                            (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                        ++
                        val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                            (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
               /\ (forall (u v w : int), 0 <= u < size leavesk0{2} => 
                                         0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                     nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                         (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                          bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                     =
                     (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                  (v + 1) (u * nr_nodes (v + 1) + w),
                      let leavesl 
                          = 
                          mkseq (fun (m : int) => 
                                    f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                            0 (u * t + m)) 
                                      (val (nth witness (nth witness (val skFORS0{2}) u) m))) t in
                        val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                            (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                        ++
                        val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                            (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
               /\ uniq (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
               /\ all (fun (ad : adrs) => get_typeidx ad = trhtype /\ get_thidx ad <> 0) (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
               /\ all (fun (ad : adrs) => get_typeidx ad = trcotype \/ get_thidx ad = 0) (TRHC.O_THFC_Default.tws{2})
               /\ size TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                  = 
                  size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * l * k * (t - 1) + 
                  size skFORSl{2} * k * (t - 1) + 
                  size leavesk0{2} * (t - 1)
               /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
               /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.nodess{2}
               /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} < s
               /\ size skFORSl{2} = size pkFORSl{2}
               /\ size skFORSl{2} = size nodesl{2}
               /\ size skFORSl{2} < l
               /\ size leavesk0{2} = size nodesk{2}
               /\ size leavesk0{2} = size rootsk{2}
               /\ size leavesk0{2} <= k).
        - wp => /=.
          while (   ={skFORSl, pkFORSl, leavesl, nodesl, rootsl, nodesk, rootsk, leavest, nodest}
                 /\ ps{1} = pp{2}
                 /\ ps{1} = TRHC.O_THFC_Default.pp{2}
                 /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
                 /\ ad{1} = adz
                 /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}
                 /\ skFORSs{1} = R_TRHSMDTTCRC_EUFCMA.skFORSs{2}
                 /\ pkFORSs{1} = R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
                 /\ nodess{1} = R_TRHSMDTTCRC_EUFCMA.nodess{2}
                 /\ skFORS{1} = skFORS0{2}
                 /\ leavesk{1} = leavesk0{2}
                 /\ (forall (adx : adrs * dgst),
                       adx \in TRHC_TCR.O_SMDTTCR_Default.ts{2}
                       <=>
                       (exists (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} /\ 0 <= j < Top.l /\ 0 <= u < k /\ 
                                                  0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                         adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                   (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                    bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                       \/
                       (exists (j u v w : int), 0 <= j < size skFORSl{2} /\ 0 <= u < k /\ 
                                                0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                         adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                   (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                    bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                       \/
                       (exists (u v w : int), 0 <= u < size leavesk0{2} /\ 
                                              0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                         adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                   (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                    bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                       \/ 
                       (exists (v w : int), 0 <= v < size nodest{2} /\ 0 <= w < nr_nodes (v + 1) /\
                         adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                   (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + size leavesk0{2} * (2 ^ a - 1) + 
                                    bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)))
                 /\ (forall (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} => 0 <= j < Top.l => 0 <= u < k => 
                                               0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                       nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                           (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                            bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                       =
                       (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) (v + 1) (u * nr_nodes (v + 1) + w),
                        let leavesl 
                            = 
                            mkseq (fun (m : int) => 
                                      f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + m)) 
                                        (val (nth witness (nth witness (val (nth witness (nth witness R_TRHSMDTTCRC_EUFCMA.skFORSs{2} i) j)) u) m))) t in
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                              (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                          ++
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                              (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
                 /\ (forall (j u v w : int), 0 <= j < size skFORSl{2} => 0 <= u < k => 
                                             0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                       nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                           (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                            bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                       =
                       (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                    (v + 1) (u * nr_nodes (v + 1) + w),
                        let leavesl 
                            = 
                            mkseq (fun (m : int) => 
                                      f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                              0 (u * t + m)) 
                                        (val (nth witness (nth witness (val (nth witness skFORSl{2} j)) u) m))) t in
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                              (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                          ++
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                              (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
                 /\ (forall (u v w : int), 0 <= u < size leavesk0{2} => 
                                           0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                       nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                           (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                            bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                       =
                       (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                    (v + 1) (u * nr_nodes (v + 1) + w),
                        let leavesl 
                            = 
                            mkseq (fun (m : int) => 
                                      f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                              0 (u * t + m)) 
                                        (val (nth witness (nth witness (val skFORS0{2}) u) m))) t in
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                              (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                          ++
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                              (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
                 /\ (forall (v w : int), 0 <= v < size nodest{2} => 0 <= w < nr_nodes (v + 1) =>
                       nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                           (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + size leavesk0{2} * (2 ^ a - 1) + 
                            bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                       =
                       (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                    (v + 1) (size leavesk0{2} * nr_nodes (v + 1) + w),
                        (*
                        let leavesl 
                            = 
                            mkseq (fun (m : int) => 
                                      f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                              0 (u * t + m)) 
                                        (val (nth witness (nth witness (val skFORS0{2}) u) m))) t in
                        *)
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                              (oget (sub_bt (list2tree leavest{2}) (rev (int2bs (a - v) (2 * w))))) v (size leavesk0{2} * nr_nodes v + 2 * w))
                          ++
                          val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                              (oget (sub_bt (list2tree leavest{2}) (rev (int2bs (a - v) (2 * w + 1))))) v (size leavesk0{2} * nr_nodes v + 2 * w + 1))))
                 /\ uniq (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
                 /\ all (fun (ad : adrs) => get_typeidx ad = trhtype /\ get_thidx ad <> 0) (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
                 /\ size TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                    = 
                    size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * l * k * (t - 1) + 
                    size skFORSl{2} * k * (t - 1) + 
                    size leavesk0{2} * (t - 1) +
                    bigi predT (fun (m : int) => nr_nodes m) 1 (size nodest{2} + 1)
                 /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
                 /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.nodess{2}
                 /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} < s
                 /\ size skFORSl{2} = size pkFORSl{2}
                 /\ size skFORSl{2} = size nodesl{2}
                 /\ size skFORSl{2} < l
                 /\ size leavesk0{2} = size nodesk{2}
                 /\ size leavesk0{2} = size rootsk{2}
                 /\ size leavesk0{2} < k
                 /\ size nodest{2} <= a).
          * wp => /=.
            while (   ={skFORSl, pkFORSl, leavesl, nodesl, nodesk, leavest, nodest, nodescl, nodespl}
                   /\ ps{1} = pp{2}
                   /\ ps{1} = TRHC.O_THFC_Default.pp{2}
                   /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
                   /\ ad{1} = adz
                   /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}
                   /\ skFORSs{1} = R_TRHSMDTTCRC_EUFCMA.skFORSs{2}
                   /\ pkFORSs{1} = R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
                   /\ nodess{1} = R_TRHSMDTTCRC_EUFCMA.nodess{2}
                   /\ skFORS{1} = skFORS0{2}
                   /\ leavesk{1} = leavesk0{2}
                   /\ (forall (adx : adrs * dgst),
                        adx \in TRHC_TCR.O_SMDTTCR_Default.ts{2}
                        <=>
                        (exists (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} /\ 0 <= j < Top.l /\ 0 <= u < k /\ 
                                                   0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                          adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                    (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                     bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                        \/
                        (exists (j u v w : int), 0 <= j < size skFORSl{2} /\ 0 <= u < k /\ 
                                                 0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                          adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                    (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                     bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                        \/
                        (exists (u v w : int), 0 <= u < size leavesk0{2} /\ 
                                               0 <= v < a /\ 0 <= w < nr_nodes (v + 1) /\
                          adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                    (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                                     bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                        \/ 
                        (exists (v w : int), 0 <= v < size nodest{2} /\ 0 <= w < nr_nodes (v + 1) /\
                          adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                    (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + size leavesk0{2} * (2 ^ a - 1) + 
                                     bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w))
                        \/ 
                        (exists (w : int), 0 <= w < size nodescl{2} /\
                          adx = nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                                    (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + size leavesk0{2} * (2 ^ a - 1) + 
                                     bigi predT (fun (m : int) => nr_nodes m) 1 (size nodest{2} + 1) + w)))
                   /\ (forall (i j u v w : int), 0 <= i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} => 0 <= j < Top.l => 0 <= u < k => 
                                                 0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                         nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                             (i * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                              bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                         =
                         (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) (v + 1) (u * nr_nodes (v + 1) + w),
                          let leavesl 
                              = 
                              mkseq (fun (m : int) => 
                                        f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j) 0 (u * t + m)) 
                                          (val (nth witness (nth witness (val (nth witness (nth witness R_TRHSMDTTCRC_EUFCMA.skFORSs{2} i) j)) u) m))) t in
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                                (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                            ++
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) i) j)
                                                (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
                   /\ (forall (j u v w : int), 0 <= j < size skFORSl{2} => 0 <= u < k => 
                                               0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                         nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                             (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + j * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                              bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                         =
                         (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                      (v + 1) (u * nr_nodes (v + 1) + w),
                          let leavesl 
                              = 
                              mkseq (fun (m : int) => 
                                        f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j) 
                                                0 (u * t + m)) 
                                          (val (nth witness (nth witness (val (nth witness skFORSl{2} j)) u) m))) t in
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                                (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                            ++
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) j)
                                                (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
                   /\ (forall (u v w : int), 0 <= u < size leavesk0{2} => 
                                             0 <= v < a => 0 <= w < nr_nodes (v + 1) =>
                         nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                             (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + u * (2 ^ a - 1) + 
                              bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                         =
                         (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                      (v + 1) (u * nr_nodes (v + 1) + w),
                          let leavesl 
                              = 
                              mkseq (fun (m : int) => 
                                        f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                                0 (u * t + m)) 
                                          (val (nth witness (nth witness (val skFORS0{2}) u) m))) t in
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                                (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w))))) v (u * nr_nodes v + 2 * w))
                            ++
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                                (oget (sub_bt (list2tree leavesl) (rev (int2bs (a - v) (2 * w + 1))))) v (u * nr_nodes v + 2 * w + 1))))
                   /\ (forall (v w : int), 0 <= v < size nodest{2} => 0 <= w < nr_nodes (v + 1) =>
                         nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                             (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + size leavesk0{2} * (2 ^ a - 1) + 
                              bigi predT (fun (m : int) => nr_nodes m) 1 (v + 1) + w)
                         =
                         (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                      (v + 1) (size leavesk0{2} * nr_nodes (v + 1) + w),
                          (*
                          let leavesl 
                              = 
                              mkseq (fun (m : int) => 
                                        f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                                0 (u * t + m)) 
                                          (val (nth witness (nth witness (val skFORS0{2}) u) m))) t in
                          *)
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                                (oget (sub_bt (list2tree leavest{2}) (rev (int2bs (a - v) (2 * w))))) v (size leavesk0{2} * nr_nodes v + 2 * w))
                            ++
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                                (oget (sub_bt (list2tree leavest{2}) (rev (int2bs (a - v) (2 * w + 1))))) v (size leavesk0{2} * nr_nodes v + 2 * w + 1))))
                   /\ (forall (w : int), 0 <= w < size nodescl{2} =>
                         nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                             (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * Top.l * k * (2 ^ a - 1) + size skFORSl{2} * k * (2 ^ a - 1) + size leavesk0{2} * (2 ^ a - 1) + 
                              bigi predT (fun (m : int) => nr_nodes m) 1 (size nodest{2} + 1) + w)
                         =
                         (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                      (size nodest{2} + 1) (size leavesk0{2} * nr_nodes (size nodest{2} + 1) + w),
                          (*
                          let leavesl 
                              = 
                              mkseq (fun (m : int) => 
                                        f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                                0 (u * t + m)) 
                                          (val (nth witness (nth witness (val skFORS0{2}) u) m))) t in
                          *)
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                                (oget (sub_bt (list2tree leavest{2}) (rev (int2bs (a - size nodest{2}) (2 * w))))) (size nodest{2}) (size leavesk0{2} * nr_nodes (size nodest{2}) + 2 * w))
                            ++
                            val (val_bt_trh_gen pp{2} (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2}))
                                                (oget (sub_bt (list2tree leavest{2}) (rev (int2bs (a - size nodest{2}) (2 * w + 1))))) (size nodest{2}) (size leavesk0{2} * nr_nodes (size nodest{2}) + 2 * w + 1))))
                   /\ uniq (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
                   /\ all (fun (ad : adrs) => get_typeidx ad = trhtype /\ get_thidx ad <> 0) (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})
                   /\ size TRHC_TCR.O_SMDTTCR_Default.ts{2} 
                      = 
                      size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * l * k * (t - 1) + 
                      size skFORSl{2} * k * (t - 1) + 
                      size leavesk0{2} * (t - 1) +
                      bigi predT (fun (m : int) => nr_nodes m) 1 (size nodest{2} + 1) +
                      size nodescl{2}  
                   /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.pkFORSs{2}
                   /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} = size R_TRHSMDTTCRC_EUFCMA.nodess{2}
                   /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} < s
                   /\ size skFORSl{2} = size pkFORSl{2}
                   /\ size skFORSl{2} = size nodesl{2}
                   /\ size skFORSl{2} < l
                   /\ size leavesk0{2} = size nodesk{2}
                   /\ size leavesk0{2} = size rootsk{2}
                   /\ size leavesk0{2} < k
                   /\ size nodest{2} < a
                   /\ size nodescl{2} <= nr_nodes (size nodest{2} + 1)).
            + inline{2} 3.
              wp; skip => /> &2 otsdef nthots nthots1 nthots2 nthots3 nthots4 uqun1ots allots szots
                                eqszskpkfs eqszskfnds lts_szskfs eqszskpkfl eqszskfndsl ltl_szskfs
                                eqszlfsndsk eqszlfsrsk ltk_szlfsk lta_szndst _ ltnnsz1_szndscl.
              rewrite ?size_rcons !andbA -andbA; split => [| /#].
              rewrite all_map -?cats1 all_cat /= -all_map allots /= /preim /=.
              rewrite map_cat /= cat_uniq uqun1ots /=.
              split; last first.
              - rewrite gettype_setthtbkptypetrh 6:/=; 1..5: smt(valf_adz nth_take size_ge0).
                * split => [| _]; 1: smt(size_ge0).
                  by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
                rewrite getth_setthtbkpttype 1:valf_adz; 1..3,5:smt(size_ge0).
                split => [| _]; 1: smt(size_ge0).
                by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
              
              split; last first. 
              - have vtbnad : valid_tbidx (size nodest{2} + 1) (size nodesk{2} * nr_nodes (size nodest{2} + 1) + size nodescl{2}).
                * split => [| _]; 1: smt(size_ge0).
                  by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
                have vthnad : valid_thidx (size nodest{2} + 1) by smt(size_ge0).
                have vkpnad : valid_kpidx (size nodesl{2}) by smt(size_ge0).
                have vtnad : valid_tidx (size R_TRHSMDTTCRC_EUFCMA.nodess{2}) by smt(size_ge0).
                rewrite mapP negb_exists => adx /=.
                rewrite negb_and -implybE => /otsdef.
                case; 2: case; 3: case; 4: case.
                * elim => i j u v w [rng_i [rng_j [rng_u [rng_v [rng_w]]]]].
                  rewrite nthots 1..5:// => -> /=.
                  rewrite -eq_adrs_idxs &(neq_from_nth witness _ _ 4).
                  rewrite neqtidx_setthtbkpt 1:valf_adz 1,3,4,5,7,10:// 1,2,4:/#.
                  split => [| _]; 1: smt(size_ge0).
                  by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
                * elim => j u v w [rng_j [rng_u [rng_v [rng_q]]]].
                  rewrite nthots1 1..4:// => -> /=.
                  rewrite -eq_adrs_idxs &(neq_from_nth witness _ _ 2).
                  rewrite neqkpidx_setthtbkpt 1:valf_adz 1,2,3,5,7,10:// 1,2,4:/#.
                  split => [| _]; 1: smt(size_ge0).
                  by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
                * elim => u v w [rng_u [rng_v [rng_w]]].
                  rewrite nthots2 1..3:// => -> /=.
                  rewrite -eq_adrs_idxs; case (v = size nodest{2}) => [eqsz_v | neqsz_v].
                  + rewrite eqsz_v &(neq_from_nth witness _ _ 0).
                    rewrite neqtbidx_setthtbkpt 1:valf_adz 1..5,7,10:// 1:/#.
                    - split => [| _]; 1: smt(size_ge0).
                      by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
                    rewrite (: size nodesk{2} = size nodesk{2} - u + u) 1:/# mulrDl.
                    rewrite neq_ltz; right; suff /#: 0 <= size nodescl{2}.
                    by rewrite size_ge0.
                  rewrite &(neq_from_nth witness _ _ 1).
                  rewrite neqthidx_setthtbkpt 1:valf_adz 1..5,7,10:// 1,3:/#.
                  split => [| _]; 1: smt(size_ge0).
                  by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
                * elim => v w [rng_v [rng_w]].
                  rewrite nthots3 1..2:// => -> /=.
                  rewrite -eq_adrs_idxs &(neq_from_nth witness _ _ 1).
                  rewrite neqthidx_setthtbkpt 1:valf_adz 1..5,7,10:// 1,3:/#.
                  split => [| _]; 1: smt(size_ge0).
                  by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
                elim => w [rng_w].
                rewrite nthots4 1:// => -> /=.
                rewrite -eq_adrs_idxs &(neq_from_nth witness _ _ 0).
                rewrite neqtbidx_setthtbkpt 1:valf_adz 1..5,7,10:// 1,3:/#.
                split => [| _]; 1: smt(size_ge0).
                by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
              rewrite -!andbA; split => [adx |].
              - rewrite mem_cat /=; split; last first.
                * rewrite otsdef; case; 2: case; 3: case; 4: case.
                  + elim => i j u v w [rng_i [rng_j [rng_u [rng_v [rng_w]]]]].
                    rewrite nth_cat szots -/t.
                    suff /#:
                      i * l * k * (t - 1) + j * k * (t - 1) + u * (t - 1) + bigi predT nr_nodes 1 (v + 1) + w 
                      < 
                      size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} * l * k * (t - 1) + size skFORSl{2} * k * (t - 1) + size leavesk0{2} * (t - 1) + bigi predT nr_nodes 1 (size nodest{2} + 1) + size nodescl{2}.
                    rewrite -?mulrA /t -?addrA ltlltr 3:/#.
                    - by rewrite ?mulr_ge0; 1..3: smt(Top.ge1_l ge1_k ge2_t).
                    - rewrite ?addr_ge0 ?mulr_ge0 1,4,7://; 1..3: smt(Top.ge1_l ge1_k size_ge0 ge2_t).
                      by rewrite sumr_ge0 => ? _; rewrite expr_ge0.
                    rewrite -(addr0 (l * _)) ltlltr 1:mulr_ge0 3://; 1..3: smt(ge1_k ge2_t).
                    rewrite -(addr0 (k * _)) ltlltr 2:// 2:/#; 1: smt(ge2_t).
                    by rewrite ltnn1_bignna.
                  + elim => j u v w [rng_j [rng_u [rng_v [rng_w]]]].
                    rewrite nth_cat szots -/t.
                    suff /#:
                      j * k * (t - 1) + u * (t - 1) + bigi predT nr_nodes 1 (v + 1) + w 
                      < 
                      size skFORSl{2} * k * (t - 1) + size leavesk0{2} * (t - 1) + bigi predT nr_nodes 1 (size nodest{2} + 1) + size nodescl{2}.
                    rewrite -?mulrA -?addrA ltlltr 3:/#; 1: smt(ge1_k ge2_t). 
                    - rewrite ?addr_ge0 2:sumr_ge0 1:mulr_ge0 4:// => [| | a _]; 1,2: smt(size_ge0 ge2_t).
                      by rewrite expr_ge0.
                    rewrite -(addr0 (k * _)) ltlltr 2:// 2:/#; 1: smt(IntOrder.expr_gt0).
                    by rewrite ltnn1_bignna.
                  + elim => u v w [rng_u [rng_v [rng_w]]].
                    rewrite nth_cat szots -/t.
                    suff /#:
                      u * (t - 1) + bigi predT nr_nodes 1 (v + 1) + w 
                      < 
                      size leavesk0{2} * (t - 1) + bigi predT nr_nodes 1 (size nodest{2} + 1) + size nodescl{2}.
                    rewrite -?addrA ltlltr 3:/#; 1: smt(ge2_t). 
                    - by rewrite addr_ge0 2:size_ge0 sumr_ge0 => a _; rewrite expr_ge0.
                    by rewrite ltnn1_bignna.
                  + elim => v w [rng_v [rng_w]].
                    rewrite nth_cat szots -/t.
                    suff /#:
                      bigi predT nr_nodes 1 (v + 1) + w 
                      < 
                      bigi predT nr_nodes 1 (size nodest{2} + 1) + size nodescl{2}.
                    print big_cat_int.
                    rewrite (big_cat_int (v + 1) _ (size nodest{2} + 1)) 1,2:/#.
                    rewrite -addrA ler_lt_add 1:// (big_cat_int (v + 2)) 1,2:/# big_int1.
                    by rewrite -(addr0 w) -addrA ltr_le_add 1:/# addr_ge0 2:size_ge0 1:sumr_ge0 => a _; rewrite expr_ge0.
                  elim => w [rng_w].
                  rewrite nth_cat szots -/t; case (w < size nodescl{2}) => [/# | ?].
                  by rewrite (: w = size nodescl{2}) 1:/# /= => ->.
                admit.
              admit.
            wp; skip => /> &2 otsdef nthots nthots1 nthots2 nthots3 uqun1ots allots szots
                              eqszskpkfs eqszskfnds lts_szskfs eqszskpkfl eqszskfndsl ltl_szskfs
                              eqszlfsndsk eqszlfsrsk ltk_szlfsk _ lta_szndst.
            rewrite expr_ge0 1:// /=.
            split => [| ts ndscl /lezNgt gennsz1_szndscl _ tsdef nthts nthts1 nthts2 nthts3 nthts4 uqunz1ts allts szts lennsz1_szndscl].            
            + split => [adx | /#]. 
              by rewrite ?otsdef /#.
            rewrite ?size_rcons !andbA; split => [| /#].
            split; last first.
            + rewrite (lez_trans _ _ _ szts) -addrA ler_add 1://.
              by rewrite (big_int_recr (size nodest{2} + 1)) 2:ler_add; 1: smt(size_ge0).
            split => [adx | v w ge0_v ltsz1_v ge0_w ltnnv1_w].
            - split => [/tsdef | ].
              * do 3! (case => [-> // |]).
                case => [/# | [w] [rng_w ->]]; do ? right. 
                by exists (size nodest{2}) w; smt(size_ge0).
              rewrite tsdef; do 3! (case => [-> // |]).
              move => -[v w] [rng_v] [rng_w] -> /=.
              case (v < size nodest{2}) => ?.
              * by do 3! right; left; exists v w => /#.
              by do 4! right; exists w => /#.
            case (v < size nodest{2}) => ?; 1: by rewrite nthts3.
            by rewrite (: v = size nodest{2}) 1:/# /= nthts4 1:/#.
          wp => /=.
          while (   ={leavest, skFORSl}
                 /\ ps{1} = pp{2}
                 /\ ps{1} = TRHC.O_THFC_Default.pp{2}
                 /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
                 /\ ad{1} = adz
                 /\ ad{1} = R_TRHSMDTTCRC_EUFCMA.ad{2}
                 /\ skFORSs{1} = R_TRHSMDTTCRC_EUFCMA.skFORSs{2}
                 /\ skFORS{1} = skFORS0{2}
                 /\ leavesk{1} = leavesk0{2}
                 /\ leavest{2}
                    =
                    mkseq (fun (m : int) => 
                            f pp{2} (set_thtbidx (set_kpidx (set_tidx (set_typeidx R_TRHSMDTTCRC_EUFCMA.ad{2} trhtype) (size R_TRHSMDTTCRC_EUFCMA.skFORSs{2})) (size skFORSl{2})) 
                                    0 (size leavesk0{2} * t + m)) 
                              (val (nth witness (nth witness (val skFORS0{2}) (size leavesk0{2})) m))) (size leavest{2})
                 /\ all (fun (ad : adrs) => get_typeidx ad = trcotype \/ get_thidx ad = 0) (TRHC.O_THFC_Default.tws{2})
                 /\ size R_TRHSMDTTCRC_EUFCMA.skFORSs{2} < s
                 /\ size skFORSl{2} < l
                 /\ size leavesk0{2} < k
                 /\ size leavest{2} <= t).
          * inline{2} 1.
            wp; skip => /> &2 lfstdef allotws lts_szskfs ltl_szskfs ltk_szlfsk _ ltt_szlfst.
            rewrite ?size_rcons -?cats1 all_cat allotws /=.
            rewrite mkseqS 1:size_ge0 ?cats1 /= {8}lfstdef /f valP /= /=.
            split => [| /#]; 1: right.
            rewrite getth_setthtbkpttype 1:valf_adz 5://; 1..3: smt(ge1_a size_ge0). 
            split => [| _]; 1: smt(size_ge0).
            by rewrite (: k = k - 1 + 1) 1:// mulrDl /= ler_lt_add 1:/t 1:ler_pmul2r 3:// 1:expr_gt0 1:// /#.
          wp; skip => /> &2 otsdef nthots nthots1 nthots2 uqun1ots allots allotws szots
                            eqszskpkfs lts_szskfs eqszskpkfl ltl_szskfs
                            eqszlfsndsk eqszlfsrsk _ ltk_szlfsk.
          split => [| tws lfst /lezNgt get_szlfst _ lfstdef alltws let_szlfst]; 1: by rewrite mkseq0; smt(ge2_t).
          split => [| ts ndst /lezNgt gea_szndst _ tsdef nthts nthts1 nthts2 nthts3 uqunz1ts allts szts lea_szndst]. 
          - rewrite big_geq 1://= szots.
            split => [adx |]; 2: smt(ge1_a).
            by rewrite ?otsdef /#.
          rewrite ?size_rcons !andbA -2!andbA; split => [| /#].
          split; last first.
          - rewrite mulrDl /= addrA (lez_trans _ _ _ szts).
            rewrite ler_add 1:// (: size ndst = a) 1:/#.
            rewrite lez_eqVlt; left.
            rewrite /t eq_sym /nr_nodes; have ge0_a: 0 <= a by smt(ge1_a).
            rewrite (big_reindex _ _ (fun i => a - i) (fun i => a - i)).
            + by move=> i /mem_range rng_i /= /#.
            rewrite /(\o) /predT /= -/predT (eq_bigr _ _ (fun i => 2 ^ i)) => [i _ /= /# |].
            rewrite (eq_big_perm _ _ _ (range 0 a)).
            - rewrite uniq_perm_eq_size 2:range_uniq 2:size_map 2:?size_range 2://.
              * by rewrite map_inj_in_uniq 2:range_uniq => i j rng_i rng_j /= /#.
              by move=> i /mapP [j] [/mem_range rng_j /= ->]; rewrite mem_range; smt(ge1_a).
            elim: a ge0_a=> [| i ge0_i ih]; 1: by rewrite expr0 big_geq.  
            by rewrite big_int_recr 1:// exprD_nneg 1,2:// /= expr1 -ih /#.
          split => [adx | u v w ge0_u ltsz1_u ge0_v lta_v ge0_w ltnnv1_w].
          + split => [/tsdef | ]; 1: smt(size_ge0).
            by rewrite tsdef; smt(size_ge0).
          case (u < size leavesk0{2}) => ?; 1: by rewrite nthts2.
          rewrite (: u = size leavesk0{2}) 1:/# /= nthts3 1:/# 1://.
          by rewrite lfstdef (: size lfst = t) 1:/#.
        wp => /=.
        call (: true); 1: by sim.
        skip => /> &2 otsdef nthots nthots1 uqun1ots allots allotws szots
                      eqszskpkfs eqszskflfss eqszskfndss eqszskfrss lts_szskfs
                      eqszskpkfl eqszskflfsl eqszskfndsl eqszskfrsl _ ltl_szskfs skf.
        split => [|  tws ts lfsk ndsk rsk /lezNgt gek_szlfs _ tsdef nthts nthts1 nthts2 uqun1ts allts alltws szts]. 
        - split => [adx |]; 2: smt(ge1_k).
          by rewrite ?otsdef /#.
        move=> eqszndslfsk eqszrslfsk lek_szlfsk; rewrite ?size_rcons.
        rewrite !andbA -5!andbA; split => [| /#].
        rewrite -?cats1 all_cat alltws /= gettype_setkp2type2trhtrco 6:/=; 1..4: smt(valf_adz nth_take size_ge0).
        - by rewrite vkpidx_setkpttype 1:valf_adz; smt(size_ge0).
        rewrite /trco size_flatten sumzE 2!big_map /(\o) /predT /= -/predT.
        rewrite (eq_bigr _ _ (fun _ => 8 * n)) => [x _ /= |]; 1: by rewrite valP. 
        rewrite big_constz count_predT (: size rsk = k) 1:/# /=.
        split => [adx | j u v w ge0_j ltsz1_j ge0_u ltk_u ge0_v lta_v ge0_w ltnnv1_w].
        - split => [/tsdef | ] @/predT; 1: smt(size_ge0).
          by rewrite tsdef /predT; smt(size_ge0).
        rewrite ?nth_cat; case (j < size skFORSl{2}) => ?; 1: by rewrite nthts1.
        by rewrite (: j = size skFORSl{2}) 1:/# /= nthts2 1:/#.
      wp; skip => /> &2 otsdef nthots uqun1ots allots allotws szots eqszskpkfs _ lts_skfs.
      split => [| tws ts pkfl skfl /lezNgt gel_szskfl _ tsdef nthts nthts1 uqun1ts allts alltws szts eqszskpkfl lel_szskfl]; 1: smt(Top.ge1_l).
      rewrite ?size_rcons !andbA -2!andbA; split => [| /#].
      split => [adx | i j u v w ge0_i ltsz1_i ge0_j ltl_j ge0_u ltk_u ge0_v lta_v ge0_w ltnnv1_w].
      * split => [/tsdef | i j u v w ge0_i ltsz1_i ge0_j ltl_j ge0_u ltk_u ge0_v lta_v ge0_w ltnnv1_w]; 1: smt(size_ge0).
        by rewrite tsdef; case (i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2}); smt(size_ge0).
      rewrite ?nth_rcons.
      case (i < size R_TRHSMDTTCRC_EUFCMA.skFORSs{2}) => ? /=; 1: by rewrite nthts.
      by rewrite (: i = size R_TRHSMDTTCRC_EUFCMA.skFORSs{2}) 1:/# /= nthts1 1:/#.
    inline{2} 2; inline{2} 1.
    wp; skip => /> &2.
    split =>  [| pkfs skfs tws ts /lezNgt ges_szskfs _ ? nthts tsdflr tsfrl *]; 1: smt(ge1_s).
    by split => [* | ]; [rewrite nthts 1:/# | smt(dval)].
  inline{2} 21; inline{2} 20; inline{2} 19; inline{2} 18.
  swap{1} 24 1; wp 24 17 => /=.
  conseq (: _   
            ==>
               is_fresh{1} 
            /\ !EUF_CMA_MFORSTWESNPRF_V.valid_ITSR{1}
            /\ !EUF_CMA_MFORSTWESNPRF_V.valid_OpenPRE{1}
            /\ EUF_CMA_MFORSTWESNPRF_V.valid_TRHTCR{1}
            =>
               x{2} <> x'{2}
            /\ trh pp{2} tw{2} x{2} = trh pp{2} tw{2} x'{2}) => //.
  - move=> /> &2 uqunz1ts nthts allts alltws ledkt1_szts vITSR vOPRE vTCR isf tw x x' + isfT vITSRF vOPREF vTCRT.
    rewrite isfT vITSRF vOPREF vTCRT size_ge0 => -[-> ->] /=.
    rewrite hasPn => ad adints; rewrite -negP => adintws.
    move/allP: allts => /(_ ad adints) /=; rewrite negb_and /=.
    by move/allP: alltws => /(_ ad adintws) /= [-> | -> //]; rewrite eq_sym dist_adrstypes.
  inline{2} 17.
  wp => /=.
  while{1} (  roots'{1}
              =
              mkseq (fun (i : int) => 
                         val_ap_trh ps{1} (set_kpidx (set_tidx (set_typeidx ad{1} trhtype) tidx{1}) kpidx{1})
                                    (nth witness (val sigFORSTW'{1}) i).`2 (nth witness lidxs'{1} i).`3 
                                    (nth witness leaves'{1} i) i) (size roots'{1}) 
            /\ leaves'{1} 
               =
               mkseq (fun (i : int) => 
                         f ps{1} (set_thtbidx (set_kpidx (set_tidx (set_typeidx ad{1} trhtype) tidx{1}) kpidx{1}) 
                                              0 (i * t + (nth witness lidxs'{1} i).`3)) 
                           (val (nth witness (val sigFORSTW'{1}) i).`1)) (size roots'{1})
            /\ size roots'{1} = size skFORS_eles'{1}
            /\ size roots'{1} = size leaves'{1}
            /\ size roots'{1} <= k)
           (k - size roots'{1}).
  - move=> _ z.
    wp; skip => /> &2 rsdef eqszrsskfelesp _ _ ltk_szrs.
    rewrite ?size_rcons ?mkseqS 1,2:size_ge0 /= ?size_mkseq lez_maxr 1:size_ge0 /=.
    rewrite -andbA; split => [| /#].
    congr; 2: by rewrite nth_rcons size_mkseq lez_maxr 1:size_ge0.
    rewrite {1}rsdef &(eq_in_mkseq) => i [ge0_k ltszrs_i] /=. 
    by rewrite nth_rcons size_mkseq lez_maxr 1:size_ge0 ltszrs_i.
  wp => /=.
  call (: ={glob O_CMA_MFORSTWESNPRF_AV}); 1: by sim.
  skip => /> &2 uqunz1 nthts allts alltws ledkt1_szts sig qs lidxs mks.
  split => [| rs skfeles]; 1: by rewrite ?mkseq0; smt(ge1_k).
  split => [/# | /lezNgt gek_szr]. 
  pose cmidx := mco _ _; pose fit := List.find _ _. 
  pose lf := f pp{2} _ _; pose lf' := f pp{2} _ _. 
  pose l2bt := list2tree _.   
  move=> rsdef eqszrsskfeles _ lek_szrs ninqs_sig1.
  rewrite negb_and negb_forall /= => -[| /mem_zip_snd /=]; 2: by rewrite ninqs_sig1.
  move=> -[idxs]; rewrite negb_imply => -[idxsing idxsninlidxs].
  have hasnin : has (fun (idxs : int * int * int) => ! (idxs \in lidxs)) (g (cmidx.`1, cmidx.`2)).
  - by rewrite hasP; exists idxs.
  have rng_fit : 0 <= fit < k.
  - by rewrite find_ge0 /= (: k = size (g (cmidx.`1, cmidx.`2))) 1:/g 1:/= 1:size_mkseq 2:-has_find 2:hasnin; smt(ge1_k).
  move/nth_find: (hasnin) => /= /(_ witness) /= nthgnin neqlfs eqrs.
  move: (ecbtapP (trhi pp{2} (set_kpidx (set_tidx (set_typeidx adz trhtype) (val cmidx.`2 %/ l)) (val cmidx.`2 %% l)))
                 updhbidx
                 l2bt
                 (val (nth witness (val sig.`2.`2) (nth witness (g (cmidx.`1, cmidx.`2)) fit).`2).`2)
                 (rev (int2bs a (nth witness (g (cmidx.`1, cmidx.`2)) fit).`3))
                 lf'
                 lf
                 (a, (nth witness (g (cmidx.`1, cmidx.`2)) fit).`2)).
  move: (ecbtap_vals (trhi pp{2} (set_kpidx (set_tidx (set_typeidx adz trhtype) (val cmidx.`2 %/ l)) (val cmidx.`2 %% l)))
                     updhbidx
                     l2bt
                     (val (nth witness (val sig.`2.`2) (nth witness (g (cmidx.`1, cmidx.`2)) fit).`2).`2)
                     (rev (int2bs a (nth witness (g (cmidx.`1, cmidx.`2)) fit).`3))
                     lf'
                     lf
                     (a, (nth witness (g (cmidx.`1, cmidx.`2)) fit).`2)).
  move: (ecbtabp_props (trhi pp{2} (set_kpidx (set_tidx (set_typeidx adz trhtype) (val cmidx.`2 %/ l)) (val cmidx.`2 %% l)))
                       updhbidx
                       l2bt
                       (val (nth witness (val sig.`2.`2) (nth witness (g (cmidx.`1, cmidx.`2)) fit).`2).`2)
                       (rev (int2bs a (nth witness (g (cmidx.`1, cmidx.`2)) fit).`3))
                       lf'
                       lf
                       (a, (nth witness (g (cmidx.`1, cmidx.`2)) fit).`2)).
  rewrite (list2tree_fullybalanced _ a) 3:/=; 1: smt(ge1_a).
  - by rewrite size_mkseq lez_maxr /t 1:expr_ge0.
  have eqfit_gcm2 : (nth witness (g (cmidx.`1, cmidx.`2)) fit).`2 = fit.
  - by rewrite /g /chunk /= nth_mkseq 1://; smt(ge1_a).
  have eqbs_gcm3 : (nth witness (g (cmidx.`1, cmidx.`2)) fit).`3 = bs2int (rev (take a (drop (a * fit) (val cmidx.`1)))).
  - by rewrite /g /g /chunk /= nth_mkseq 1:// /= nth_mkseq 1:valP 1:mulzK 2://; 1: smt(ge1_a).
  rewrite eqfit_gcm2 valP size_rev size_int2bs 1:/= lez_maxr; 1: smt(ge1_a).
  have eqa_iam :
    (if a < max 0 (k * a - a * fit) then a else max 0 (k * a - a * fit))
    =
    a.
  - rewrite lez_maxr 1:ler_subr_addr; 1: smt(ge1_a).
    suff /#: a <= k * a - a * fit.
    by rewrite -{1}(mulr1 a) ler_subr_addr -mulrDr mulrC ler_pmul2r; smt(ge1_a).
  rewrite (list2tree_height _ a) 2:size_mkseq 2:// 2:lez_maxr 2:expr_ge0 2,3:// /=; 1: smt(ge1_a). 
  rewrite /lf'; move: (neqlfs); rewrite eqfit_gcm2 nth_mkseq 1:/# /=.
  rewrite /g /chunk /= nth_mkseq 1:// /= nth_mkseq 1:valP 1:mulzK 2:// 2:/=; 1: smt(ge1_a).
  rewrite (nth_map witness) 1:valP 1:// /= eq_sym => -> /=.
  move: (eqrs); rewrite /val_bt_trh {1}/val_bt_trh_gen.
  rewrite rsdef nth_mkseq 1:eqfit_gcm2 1:/# /= eqfit_gcm2 /= nth_mkseq 1:/# /=.
  rewrite /val_ap_trh {1}/val_ap_trh_gen => <-.
  rewrite /g /chunk /= nth_mkseq 1:// /= nth_mkseq 1:valP 1:mulzK 2:// 2:/=; 1: smt(ge1_a).
  rewrite /lf list2tree_lvb 2:size_mkseq 2:lez_maxr 2:expr_ge0 2,3://; 1: smt(ge1_a). 
  - rewrite bs2int_ge0 /= size_mkseq lez_maxr 1:expr_ge0 1,2://.
    pose rtd := rev (take a _); rewrite /t (: a = size rtd) 2:bs2int_le2Xs.
    by rewrite size_rev size_take 2:size_drop 3:valP 3:eqa_iam; 1,2: smt(ge1_a).
  rewrite (onth_nth witness) 2:nth_mkseq 1,2:bs2int_ge0 /= 1:size_mkseq 1:lez_maxr 1:expr_ge0 1,2://.
  - pose rtd := rev (take a _); rewrite /t (: a = size rtd) 2:bs2int_le2Xs.
    by rewrite size_rev size_take 2:size_drop 3:valP 3:eqa_iam; 1,2: smt(ge1_a).
  - pose rtd := rev (take a _); rewrite /t (: a = size rtd) 2:bs2int_le2Xs.
    by rewrite size_rev size_take 2:size_drop 3:valP 3:eqa_iam; 1,2: smt(ge1_a).
  rewrite eqbs_gcm3 /= /extract_collision_bt_ap_trh; pose ecbt := extract_collision_bt_ap _ _ _ _ _ _ _.
  case: ecbt => /= [x1 x1' x2 x2' hbidx l r bs].
  move=> [#] eqhlr eqszhl lthphl lthpszbs.
  rewrite take_rev_int2bs; 1: smt(size_ge0).
  pose rtd := rev (take a _); rewrite (: int2bs a (bs2int rtd) = rtd).
  - rewrite (: a = size rtd) 2:bs2intK 2://.
    by rewrite size_rev size_take 2:size_drop 3:valP 3:eqa_iam; 1,2: smt(ge1_a).
  rewrite revK /=; move=> [#] x1val x1pval x2val x2pval.
  rewrite foldlupdhbidx size_int2bs lez_maxr 1:/# (: a - (a - size bs - 1) =  size bs + 1) 1:/# /=. 
  move=> hbidxval lval rval bsval [#] neqin eqout; pose nthtsc := nth _ _ (_ + _ + _ + _)%Int.
  move: (nthts (val cmidx.`2 %/ Top.l) (val cmidx.`2 %% Top.l) fit (hbidx.`1 - 1) 
               (hbidx.`2 %% nr_nodes hbidx.`1) _ _ _ _ _); 3,4: by rewrite //; smt(size_ge0 ge1_a).
  - by rewrite divz_ge0 2:ltz_divLR; smt(Top.ge1_l dval Index.valP).
  - by rewrite modz_ge0 2:ltz_pmod; 1,2: smt(Top.ge1_l).
  - by rewrite /= modz_ge0 2:ltz_pmod; 1,2: smt(IntOrder.expr_gt0).
  pose vb := val_bt_trh_gen _ _ _ _ _; pose vb' := val_bt_trh_gen _ _ _ _ _.
  suff: x1 = vb /\ x1' = vb'.
  - move => -[<- <-]; rewrite /nthtsc => -> /=.
    move: eqout => @/trhi.
    rewrite hbidxval /= -2!modzDm /(nr_nodes (size bs + 1)) (: a - (size bs + 1) = a - size bs - 1) 1:/#.
    rewrite ?modzMl /= ?modz_mod (pmod_small (bs2int _)). 
    * rewrite bs2int_ge0; pose i2bs := int2bs _ _; rewrite (: a - size bs - 1 = size i2bs) 2:bs2int_le2Xs 2://.
      by rewrite size_int2bs lez_maxr 1:/#.
    move => -> /=; rewrite eqseq_cat 1:2!valP 1://; move: neqin; rewrite 2!negb_and => neqxor.
    by move: neqxor 
             (DigestBlock.val_inj x1 x2) 
             (DigestBlock.val_inj x1' x2') => + /contra + /contra /#.
  rewrite x1val /vb x1pval /vb' hbidxval /val_bt_trh_gen lval rval /l2bt /updhbidx /=.
  rewrite -modzDm /(nr_nodes (size bs + 1)) (: a - (size bs + 1) = a - size bs - 1) 1:/#.
  rewrite ?modzMl /= ?modz_mod (pmod_small (bs2int _)). 
    - rewrite bs2int_ge0; pose i2bs := int2bs _ _; rewrite (: a - size bs - 1 = size i2bs) 2:bs2int_le2Xs 2://.
      by rewrite size_int2bs lez_maxr 1:/#.
  rewrite mulrDr mulrCA -{4 17}(expr1 2) -exprD_nneg 1:// 1:/# /= /(nr_nodes (size bs)) eqfit_gcm2.
  split; do 3! congr; rewrite (int2bs_cat 1 (a - size bs)) 1:/# (int2bs_cons 1) 1://.
  - rewrite dvdz_mulr // /= int2bs0s /= -rev_cons /= expr1 mulKz 1:// /=.
    by rewrite {2}(: a - size bs - 1 = size (int2bs (a - size bs - 1) (bs2int rtd %/ 2 ^ (size bs + 1)))) 1:size_int2bs 1:/# bs2intK.
  rewrite dvdzE (mulrC 2) modzMDl /= int2bs0s /= expr1 divzMDl //= -rev_cons.
  by rewrite {2}(: a - size bs - 1 = size (int2bs (a - size bs - 1) (bs2int rtd %/ 2 ^ (size bs + 1)))) 1:size_int2bs 1:/# bs2intK.
admit.
qed.

local lemma EqPr_SMDTOpenPRE_FOpenPRE_FPOpenPRE &m :
  Pr[F_OpenPRE.SM_DT_OpenPRE(R_FSMDTOpenPRE_EUFCMA(A), F_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res]
  =
  Pr[FP_OpenPRE.SM_DT_OpenPRE(R_FPOpenPRE_FOpenPRE(A), FP_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res].
proof.
byequiv => //.
proc.
conseq (: ={glob A} ==> ={nrts, opened, dist, pp, tw, y} /\ x{1} = val x{2}); 1,2: smt().
seq 4 4 : (   ={pp, i} 
           /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
           /\ x{1} = val x{2}).
+ inline{1} 4; inline{2} 4; inline{2} 6.  
  wp 19 21 => /=.
  conseq (:  ={glob A} 
             ==> 
                ={pp, cidx, x'} 
             /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)).
  - by move=> &1 &2; smt(DigestBlock.valKd).
  wp => /=.
  call (:    ={glob R_FSMDTOpenPRE_EUFCMA}
          /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
          /\ F_OpenPRE.O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
          /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = d * k * t).
  - proc; inline *.
    wp => /=.
    while (   ={glob R_FSMDTOpenPRE_EUFCMA, sigFORSTW, cm, tidx, kpidx}
           /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
           /\ F_OpenPRE.O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
           /\ 0 <= kpidx{1} < l
           /\ 0 <= tidx{1} < s
           /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = d * k * t).
    * wp; skip => /> &2 ge0_kp ltl_kp ge0_t lts_t eqdkt_szxs ltk_szsig. 
      rewrite (nth_map witness) 2:size_rcons //= eqdkt_szxs.
      split => [|_]; 1: by rewrite ?StdOrder.IntOrder.addr_ge0 4:bs2int_ge0; smt(size_ge0 ge1_l ge1_k ge2_t).
      rewrite dval (: s * l * k * t = (s - 1) * l * k * t + (l - 1) * k * t + (k - 1) * t + t); 1: by ring.
      rewrite StdOrder.IntOrder.ler_lt_add ?StdOrder.IntOrder.ler_add; 1..3: smt(ge1_l ge1_k ge2_t).
      pose ls := rev _; rewrite (: t = 2 ^ size ls) 2:bs2int_le2Xs /t /ls.
      rewrite size_rev size_take 2:size_drop 3:valP 3:lez_maxr; 1,2,3: smt(ge1_a size_ge0). 
      have: a <= k * a - a * size sigFORSTW{2} by smt(ge1_a size_ge0).
      by case => [-> | <-].
    wp; if => //=.
    * wp; rnd; skip => /> &2 _ mnin mk mkin. 
      move: (Index.valP (mco mk m{2}).`2) => [ge0_idx ltd_idx].
      rewrite get_set_sameE oget_some.
      by rewrite modz_ge0 2:divz_ge0 3:ltz_pmod 4:ltz_divLR 5:-dval; 1..4: smt(Top.ge1_l).
    wp; skip => /> &2 _ _.  
    move: (Index.valP (mco (oget R_FSMDTOpenPRE_EUFCMA.mmap{2}.[m{2}]) m{2}).`2) => [ge0_idx ltd_idx].
    by rewrite modz_ge0 2:divz_ge0 3:ltz_pmod 4:ltz_divLR 5:-dval; 1..4: smt(Top.ge1_l).
  conseq />.
  seq 9 11 : (   ={glob R_FSMDTOpenPRE_EUFCMA, pp}
              /\ ={os, ts}(F_OpenPRE.O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default)
              /\ F_OpenPRE.O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
              /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = d * k * t).
  - wp => /=.
    seq 2 2 : (#pre /\ ={pp, tws, R_FSMDTOpenPRE_EUFCMA.ad} /\ size tws{1} = d * k * t).
    * inline *.
      wp.
      while (   ={R_FSMDTOpenPRE_EUFCMA.ad, tidx0}
             /\ adl{1} = adl0{2}
             /\ size adl{1} = tidx0{1} * l * k * t
             /\ 0 <= tidx0{1} <= s).
      + wp => /=.
        while (   ={R_FSMDTOpenPRE_EUFCMA.ad, tidx0, kpidx0}
               /\ adl{1} = adl0{2}
               /\ size adl{1} = tidx0{1} * l * k * t 
                                + kpidx0{1} * k * t
               /\ 0 <= kpidx0{1} <= l).  
        - wp => /=.
          while (   ={R_FSMDTOpenPRE_EUFCMA.ad, tidx0, kpidx0, tbidx}
                 /\ adl{1} = adl0{2}
                 /\ size adl{1} = tidx0{1} * l * k * t
                                  + kpidx0{1} * k * t 
                                  + tbidx{1}
                 /\ 0 <= tbidx{1} <= k * t).
          * by wp; skip => />; smt(size_rcons).
          by wp; skip => />; smt(ge1_k ge2_t). 
        by wp; skip => />; smt(Top.ge1_l).
      by wp; rnd; skip => />; smt(ge1_s dval). 
    inline *.
    wp.
    while (   ={tws_init}
           /\ size tws_init{1} = d * k * t
           /\ ys0{1} = ys1{2}
           /\ ={pp, ts}(O_SMDTOpenPRE_Default, FP_OpenPRE.O_SMDTOpenPRE_Default) 
           /\ O_SMDTOpenPRE_Default.xs{1} = map DigestBlock.val FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2}
           /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.xs{2} = size FP_OpenPRE.O_SMDTOpenPRE_Default.ts{2}
           /\ size FP_OpenPRE.O_SMDTOpenPRE_Default.ts{2} <= min (size tws_init{2}) (d * k * t)).
    * wp; rnd DigestBlock.insubd DigestBlock.val.
      wp; skip => /> &2 eqdkt_sztws. 
      rewrite eqdkt_sztws lez_minr //= => eqszs _ ltdkt_szts.
      split => [* |_]; 1: by rewrite valKd.
      split => [x xin | _ x /supp_dmap [x'] [_ eqvins_x]]. 
      + rewrite (in_dmap1E_can _ _ DigestBlock.insubd) 1,3:valKd //. 
        by move=> y _ <-; rewrite valKd.
      by rewrite eqvins_x valKd /= map_rcons; smt(size_rcons).
    by wp; skip => />; smt(dval ge1_s Top.ge1_l ge1_k ge2_t).
  by conseq />; sim.     
by conseq />; sim.
qed.

(*
local clone F.SMDTDSPR as F_DSPR with
    op t_smdtdspr <- d * k * t
  
  proof *.
  realize ge0_tsmdtdspr by smt(ge1_d ge1_k ge2_t).
  
local module (R_FDSPR_FPDSPR (A : FP_DSPR.Adv_SMDTDSPR) : F_DSPR.Adv_SMDTDSPR) (O : F_DSPR.Oracle_SMDTDSPR) = {  
  module O_SMDTDSPR : FP_DSPR.Oracle_SMDTDSPR = {
    include var FP_DSPR.O_SMDTDSPR_Default [-query]
    
    proc query(ad : adrs, x : dgstblock) : dgstblock = {
      var y : dgstblock;
      var adx : adrs * dgstblock;
      
      y <@ O.query(ad, val x);
      
      adx <- (ad, x);
      ts <- rcons ts adx;
      
      return y;  
    }
  }
  proc pick() : unit = {
    A(O_SMDTDSPR).pick();
  }
  
  proc guess(ps : pseed) : int * bool = {
    var i : int;
    var b : bool;
    
    (i, b) <@ A(O_SMDTDSPR).guess(ps);
    
    return (i, b);
  }
}.

local lemma EqPr_SMDTOpenPRE_FOpenPRE_FPOpenPRE &m (B <: FP_DSPR.Adv_SMDTDSPR):
  Pr[FP_DSPR.SM_DT_DSPR(B, FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res]
  <=
  Pr[F_DSPR.SM_DT_DSPR(R_FDSPR_FPDSPR(B), F_DSPR.O_SMDTDSPR_Default).main() @ &m : res].
proof. admit. qed.
*)

(* 
  TODO:
  I cannot prove that the DSPR advantage for f' is equal to the DSPR advantage
  for f due to the fact it is a distinguishing game.
  The main reason I cannot prove an equality is that f' is simply a 
  domain-restricted version of f, meaning that a second preimage for f' always implies
  a second preimage for f, but not the other way around (because 
  the second preimage for f could be outside the domain of f').
  Contrapositively, no second preimage for f always implies no second preimage for
  f', but not the other way around. So, if the given adversary returns makes the right
  judgment, i.e., true if there is a second preimage under f' and false if there isn't, 
  then in the former case the reduction adversary is always right but in the latter case 
  it might be wrong.  
*)
lemma EUFCMA_MFORSTWESNPRF &m :
  Pr[EUF_CMA_MFORSTWESNPRF(A, O_CMA_MFORSTWESNPRF).main() @ &m : res] 
  <= 
  Pr[MCO_ITSR.ITSR(R_ITSR_EUFCMA(A), MCO_ITSR.O_ITSR_Default).main() @ &m : res]
  +
  (* Pr[F_OpenPRE.SM_DT_OpenPRE(R_FSMDTOpenPRE_EUFCMA(A), F_OpenPRE.O_SMDTOpenPRE_Default).main() @ &m : res]*)
  maxr 0%r 
       (Pr[FP_DSPR.SM_DT_DSPR(R_DSPR_OpenPRE(R_FPOpenPRE_FOpenPRE(A)), FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res]
        -
        Pr[FP_DSPR.SM_DT_SPprob(R_DSPR_OpenPRE(R_FPOpenPRE_FOpenPRE(A)), FP_DSPR.O_SMDTDSPR_Default).main() @ &m : res])
  +
  3%r * Pr[FP_TCR.SM_DT_TCR(R_TCR_OpenPRE(R_FPOpenPRE_FOpenPRE(A)), FP_TCR.O_SMDTTCR_Default).main() @ &m : res]
(*  
  +
  Pr[FC_TCR.SM_DT_TCR_C(R_FSMDTTCRC_EUFCMA(A), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res]
*)
  + 
  Pr[TRHC_TCR.SM_DT_TCR_C(R_TRHSMDTTCRC_EUFCMA(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
  +
  Pr[TRCOC_TCR.SM_DT_TCR_C(R_TRCOSMDTTCRC_EUFCMA(A), TRCOC_TCR.O_SMDTTCR_Default, TRCOC.O_THFC_Default).main() @ &m : res].
proof.
move: (EUFCMA_MFORSTWESNPRF_OPRE &m).
rewrite EqPr_SMDTOpenPRE_FOpenPRE_FPOpenPRE.
move: (OpenPRE_From_DSPR_TCR (R_FPOpenPRE_FOpenPRE(A)) _ _ &m); 3: smt().
+ move=> O.
  proc; inline *.
  wp => /=.
  while (true) (s - tidx).
  - move=> z.
    wp => /=.
    while (true) (l - kpidx).
    * move=> z'.
      wp => /=.
      while (true) (k * t - tbidx).
      + move=> z''.
        by wp; skip => /> /#.
      by wp; skip => /> /#.
    by wp; skip => /> /#.
  by wp; skip => /> /#.
move=> O Oll.
proc; inline *.
wp => /=.
call (: true); 1: by apply A_forge_ll.
+ proc; inline *.
  wp => /=.
  while (true) (k - size sigFORSTW).
  - move=> z.
    wp; call Oll; wp; skip => />; smt(size_rcons).
  wp => /=.
  if; [wp; rnd |]; skip => />; 2: smt().
  by move=> *; rewrite dmkey_ll /#.
while (true) (s - size pkFORSs).
- move=> z.
  wp => /=.
  while (true) (l - size pkFORSl).
  * move=> z'.
    wp => /=.
    while (true) (k - size roots).
    + move=> z''.
      by wp; skip => />; smt(size_rcons).
    by wp; skip => />; smt(size_rcons).
  by wp; skip => />; smt(size_rcons).
by wp; skip => /> /#.        
qed.

end section Proof_EUFCMA_M_FORS_TW_ES.
