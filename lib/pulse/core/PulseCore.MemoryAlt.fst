(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulseCore.MemoryAlt
open FStar.Ghost
open FStar.PCM
module PST = PulseCore.HoareStateMonad
module U = FStar.Universe
module S = FStar.Set
module CM = FStar.Algebra.CommMonoid
module H = PulseCore.HeapSig
module E = PulseCore.HeapExtension
module B = PulseCore.BaseHeapSig
/// This module adds memory invariants to the heap to expose the
/// final interface for Pulse's PCM-based memory model.

(**** Basic memory properties *)
let small_sig : H.heap_sig u#(a + 1) = E.extend (B.base_heap u#a)
let sig : H.heap_sig u#(a + 2) = E.extend small_sig
(** Abstract type of memories *)
let mem  : Type u#(a + 3) = sig.mem

let is_ghost_action (m0 m1:mem u#a) : prop = sig.is_ghost_action m0 m1

let ghost_action_preorder (_:unit)
: Lemma (FStar.Preorder.preorder_rel is_ghost_action)
= sig.is_ghost_action_preorder ()
 
(**** Separation logic *)

(** The type of separation logic propositions. Based on Steel.Heap.slprop *)
let slprop : Type u#(a + 3) = sig.slprop

let big_slprop : Type u#(a + 2) = sig.bprop
let cm_big_slprop : CM.cm big_slprop = H.cm_slprop small_sig
let down (s:slprop u#a) : big_slprop u#a = sig.down s
let up (s:big_slprop u#a) : slprop u#a = sig.up s
let up_big_is_big (b:big_slprop) : Lemma (is_big (up b)) = sig.up_down b

let small_slprop : Type u#(a + 1) = small_sig.bprop
let cm_small_slprop : CM.cm small_slprop = H.cm_slprop B.base_heap
let down2 (s:slprop u#a) : small_slprop u#a = small_sig.down (sig.down s)
let up2 (s:small_slprop u#a) : slprop u#a = sig.up (small_sig.up s)
let small_is_also_big (s:slprop)
: Lemma (is_small s ==> is_big s)
= sig.up_down (small_sig.up (small_sig.down (down s)))

let up2_small_is_small_alt (s:small_slprop)
: Lemma (ensures is_small (up2 s))
        [SMTPat (is_small (up2 s))]
= calc (==) {
    up2 (down2 (up2 s));
  (==) {}
    up2 (down2 (sig.up (small_sig.up s)));
  (==) {}
    up2 (small_sig.down (sig.down (sig.up (small_sig.up s))));
  (==) { sig.up_down (small_sig.up s) }
    up2 (small_sig.down (small_sig.up s));
  (==) { small_sig.up_down s }
    up2 s;
  }
let up2_small_is_small s = up2_small_is_small_alt s
(** Interpreting mem assertions as memory predicates *)
let interp (p:slprop u#a) (m:mem u#a) : prop = H.interpret p m

let equiv (p1 p2:slprop u#a) : prop = p1 == p2

(**
  An extensional equivalence principle for slprop
 *)

let slprop_extensionality (p q:slprop u#a)
: Lemma
    (requires p `equiv` q)
    (ensures p == q)
= ()

let slprop_equiv_refl (p:slprop)
: Lemma (p `equiv` p)
        [SMTPat (equiv p p)]
= ()
          
(** A memory maps a [ref]erence to its associated value *)
let core_ref : Type u#0 = PulseCore.Heap2.core_ref

(** [null] is a specific reference, that is not associated to any value
*)
let core_ref_null : core_ref = PulseCore.Heap2.core_ref_null

let core_ref_is_null (r:core_ref)
: b:bool { b <==> r == core_ref_null }
= PulseCore.Heap2.core_ref_is_null r

assume
val emp_up
        (h:H.heap_sig)
: Lemma ((E.extend h).emp == (E.extend h).up h.emp)

assume
val pure_up
        (h:H.heap_sig)
        (p:prop)
: Lemma ((E.extend h).pure p == (E.extend h).up (h.pure p))

let emp_is_small () 
: Lemma (is_small sig.emp)
= emp_up B.base_heap;
  emp_up small_sig;
  small_sig.up_down B.base_heap.emp;
  sig.up_down small_sig.emp

let pure_is_small (p:prop) 
: Lemma (is_small (sig.pure p))
= pure_up B.base_heap p;
  pure_up small_sig p;
  small_sig.up_down (B.base_heap.pure p);
  sig.up_down (small_sig.pure p)

let emp
: vprop u#a
= emp_is_small(); sig.emp

let pure (p:prop)
: vprop u#a
= pure_is_small p; sig.pure p

let star  (p1 p2:slprop u#a)
: slprop u#a
= sig.star p1 p2

module F = FStar.FunctionalExtensionality
let h_exists (#a:Type u#b) (f: (a -> slprop u#a))
: slprop u#a
= H.exists_ sig #a (fun x -> f x)

(***** Properties of separation logic equivalence *)
let emp_unit (p:slprop)
: Lemma (p `equiv` (p `star` emp))
= sig.emp_unit p

let pure_equiv (p q:prop)
: Lemma ((p <==> q) ==> (pure p `equiv` pure q))
= FStar.PropositionalExtensionality.apply p q

let pure_true_emp (_:unit)
: Lemma (pure True `equiv` emp)
= sig.pure_true_emp ()

(***** Properties of the separating conjunction *)
let star_commutative (p1 p2:slprop)
: Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))
= sig.star_commutative p1 p2

let star_associative (p1 p2 p3:slprop)
: Lemma ((p1 `star` (p2 `star` p3))
          `equiv`
          ((p1 `star` p2) `star` p3))
= sig.star_associative p1 p2 p3

let star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))
= ()

let big_star_congruence (p1 p2:big_vprop u#a)
: Lemma (is_big (p1 `star` p2))
= admit()

let big_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
  (requires forall x. is_big (p x))
  (ensures is_big (h_exists p))
= admit()

let small_star_congruence (p1 p2:vprop u#a)
: Lemma (is_small (p1 `star` p2))
= admit()

let small_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
  (requires forall x. is_small (p x))
  (ensures is_small (h_exists p))
= admit()

let h_exists_equiv (#a:Type) (p q : a -> slprop)
: Lemma
    (requires (forall x. p x `equiv` q x))
    (ensures (h_exists p == h_exists q))
= admit()

let up_emp_big ()
: Lemma (up cm_big_slprop.unit == emp)
= admit()

let down_emp_big ()
: Lemma (down emp == cm_big_slprop.unit)
= admit()

let up_star_big (p q:big_slprop)
: Lemma (up (p `cm_big_slprop.mult` q) == up p `star` up q)
= admit()

let down_star_big (p q:big_vprop)
: Lemma (down (p `star` q) == down p `cm_big_slprop.mult` down q)
= admit()

let up2_emp ()
: Lemma (up2 cm_small_slprop.unit == emp)
= admit()

let down2_emp ()
: Lemma (down2 emp == cm_small_slprop.unit)
= admit()

let up2_star (p q:small_slprop)
: Lemma (up2 (p `cm_small_slprop.mult` q) == up2 p `star` up2 q)
= admit()

let down2_star (p q:vprop)
: Lemma (down2 (p `star` q) == down2 p `cm_small_slprop.mult` down2 q)
= admit()

(**** Memory invariants *)

(** Invariants have a name *)
let iname : eqtype = sig.iname
let inames_ok (e:inames) (m:mem) : prop = H.inames_ok e m

(** The empty set of invariants is always empty *)
let inames_ok_empty (m:mem)
: Lemma (ensures inames_ok Set.empty m)
          [SMTPat (inames_ok Set.empty m)]
= ()

(**
  This separation logic proposition asserts that all the invariants whose names are in [e]
  are in effect and satisfied on the heap inside the memory [m]
*)
let mem_invariant (e:inames) (m:mem u#a)
: slprop u#a
= sig.mem_invariant e m

let full_mem_pred: mem -> prop = sig.full_mem_pred 

let iref : Type0 = sig.iref

let iname_of (i:iref) : GTot iname = sig.iname_of i

let inv (i:iref) (p:slprop u#a) : slprop u#a = sig.inv i p

#push-options "--print_universes --print_implicits"
let coerce_action
    (#a:Type u#x)
    (#mg:bool)
    (#ex:inames)
    (#pre:slprop u#a)
    (#post:a -> GTot (slprop u#a))
    (act:H._action_except (sig u#a) a mg ex pre post)
    (pre':slprop u#a)
    (post':a -> slprop u#a)
    (_:squash (pre == reveal pre' /\ (forall x. post x == reveal (post' x))))
: _pst_action_except a mg ex pre' post'
= fun frame m0 -> act frame m0 

let dup_inv (e:inames) (i:iref) (p:slprop u#a)
: pst_ghost_action_except unit e 
    (inv i p) 
    (fun _ -> inv i p `star` inv i p)
= E.dup_inv #(small_sig u#a) e i p

let new_invariant (e:inames) (p:slprop { is_big p })
: pst_ghost_action_except iref e
    p
    (fun i -> inv i p)
= E.new_invariant #(small_sig u#a) e p 

let with_invariant (#a:Type u#x)
                   (#fp:slprop u#a)
                   (#fp':a -> slprop u#a)
                   (#opened_invariants:inames)
                   (#p:slprop u#a)
                   (#maybe_ghost:bool)
                   (i:iref{not (mem_inv opened_invariants i)})
                   (f:_pst_action_except a maybe_ghost
                        (add_inv opened_invariants i) 
                        (p `star` fp)
                        (fun x -> p `star` fp' x))
: _pst_action_except a maybe_ghost opened_invariants 
      (inv i p `star` fp)
      (fun x -> inv i p `star` fp' x)
= E.with_invariant #(small_sig u#a) #a #fp #fp' #opened_invariants #p #maybe_ghost i f

(*
val distinct_invariants_have_distinct_names
      (e:inames)
      (p:slprop u#m)
      (q:slprop u#m { p =!= q })
      (i j: iref)
: pst_ghost_action_except u#0 u#m 
    (squash (iname_of i =!= iname_of j))
    e 
    (inv i p `star` inv j q)
    (fun _ -> inv i p `star` inv j q)

val invariant_name_identifies_invariant
      (e:inames)
      (p q:slprop u#m)
      (i:iref)
      (j:iref { iname_of i == iname_of j } )
: pst_ghost_action_except (squash (p == q /\ i == j)) e
   (inv i p `star` inv j q)
   (fun _ -> inv i p `star` inv j q)
   
let rec all_live (ctx:list iref) =
  match ctx with
  | [] -> emp
  | hd::tl -> live hd `star` all_live tl

let fresh_wrt (ctx:list iref)
              (i:iref)
  = forall i'. List.Tot.memP i' ctx ==> iname_of i' <> iname_of i

val fresh_invariant (e:inames) (p:big_vprop u#m) (ctx:list iref)
  : pst_ghost_action_except (i:iref { fresh_wrt ctx i }) e
       (p `star` all_live ctx)
       (fun i -> inv i p)
*)

(* Some generic actions and combinators *)

let pst_frame (#a:Type)
              (#maybe_ghost:bool)
              (#opened_invariants:inames)
              (#pre:slprop)
              (#post:a -> slprop)
              (frame:slprop)
              ($f:_pst_action_except a maybe_ghost opened_invariants pre post)
: _pst_action_except a maybe_ghost opened_invariants (pre `star` frame) (fun x -> post x `star` frame)
= admit()

let witness_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
: pst_ghost_action_except (erased a) opened_invariants
           (h_exists p)
           (fun x -> p x)
= admit()

let intro_exists (#opened_invariants:_) (#a:_) (p:a -> slprop) (x:erased a)
  : pst_ghost_action_except unit opened_invariants
           (p x)
           (fun _ -> h_exists p)
= admit ()

let lift_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
  : pst_ghost_action_except unit opened_invariants
           (h_exists p)
           (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))
 = admit()

let elim_pure (#opened_invariants:_) (p:prop)
  : pst_ghost_action_except (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)
  = admit()

let intro_pure (#opened_invariants:_) (p:prop) (_:squash p)
  : pst_ghost_action_except unit opened_invariants emp (fun _ -> pure p)
  = admit()
  
let drop (#opened_invariants:_) (p:slprop)
  : pst_ghost_action_except unit opened_invariants p (fun _ -> emp)
  = admit()

let lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a opened_invariants p q))
  : pst_ghost_action_except a opened_invariants p q
  = admit ()

(* Concrete references to "small" types *)
let pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : vprop u#a
 = //up2_small_is_small (B.base_heap.pts_to #a #pcm r v);
   up2 (B.base_heap.pts_to #a #pcm r v)

val sel_action (#a:Type u#a) (#pcm:_) (e:inames) (r:ref a pcm) (v0:erased a)
  : pst_action_except (v:a{compatible pcm v0 v}) e (pts_to r v0) (fun _ -> pts_to r v0)

val upd_action (#a:Type u#a) (#pcm:_) (e:inames)
               (r:ref a pcm)
               (v0:FStar.Ghost.erased a)
               (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : pst_action_except unit e (pts_to r v0) (fun _ -> pts_to r v1)

val free_action (#a:Type u#a) (#pcm:pcm a) (e:inames)
                (r:ref a pcm) (x:FStar.Ghost.erased a{FStar.PCM.exclusive pcm x /\ pcm.refine pcm.FStar.PCM.p.one})
  : pst_action_except unit e (pts_to r x) (fun _ -> pts_to r pcm.FStar.PCM.p.one)

(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 `star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (pts_to r v0 `star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

val alloc_action (#a:Type u#a) (#pcm:pcm a) (e:inames) (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> pts_to r x)

val select_refine (#a:Type u#a) (#p:pcm a)
                  (e:inames)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (pts_to r x)
    (fun v -> pts_to r (f v))

val upd_gen (#a:Type u#a) (#p:pcm a) (e:inames) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (pts_to r x)
    (fun _ -> pts_to r y)

val pts_to_not_null_action 
      (#a:Type u#a) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (pts_to r v)
    (fun _ -> pts_to r v)

(* Ghost references to "small" types *)
[@@erasable]
val core_ghost_ref : Type0
let ghost_ref (#a:Type u#a) (p:pcm a) : Type0 = core_ghost_ref
val ghost_pts_to (#a:Type u#a) (#p:pcm a) (r:ghost_ref p) (v:a) : vprop u#a

val ghost_alloc
    (#o:_)
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    o
    emp 
    (fun r -> ghost_pts_to r x)

val ghost_read
    #o
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    #o
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit o 
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    #o
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit o
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)

val ghost_gather
    #o
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) o
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

(* Concrete references to "big" types *)
val big_pts_to (#a:Type u#(a + 1)) (#pcm:_) (r:ref a pcm) (v:a) : big_vprop u#a

val big_sel_action
      (#a:Type u#(a + 1))
      (#pcm:_)
      (e:inames)
      (r:ref a pcm)
      (v0:erased a)
: pst_action_except (v:a{compatible pcm v0 v}) e
    (big_pts_to r v0)
    (fun _ -> big_pts_to r v0)

val big_upd_action
      (#a:Type u#(a + 1)) (#pcm:_) (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
: pst_action_except unit e
    (big_pts_to r v0)
    (fun _ -> big_pts_to r v1)

val big_free_action
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (x:FStar.Ghost.erased a{FStar.PCM.exclusive pcm x /\ pcm.refine pcm.FStar.PCM.p.one})
: pst_action_except unit e
    (big_pts_to r x)
    (fun _ -> big_pts_to r pcm.FStar.PCM.p.one)

(** Splitting a permission on a composite resource into two separate permissions *)
val big_split_action
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (big_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_pts_to r v0 `star` big_pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val big_gather_action
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (big_pts_to r v0 `star` big_pts_to r v1)
    (fun _ -> big_pts_to r (op pcm v0 v1))

val big_alloc_action
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> big_pts_to r x)

val big_select_refine
      (#a:Type u#(a + 1))
      (#p:pcm a)
      (e:inames)
      (r:ref a p)
      (x:erased a)
      (f:(v:a{compatible p x v}
          -> GTot (y:a{compatible p y v /\
                      FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (big_pts_to r x)
    (fun v -> big_pts_to r (f v))

val big_upd_gen
    (#a:Type u#(a + 1))
    (#p:pcm a)
    (e:inames)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (big_pts_to r x)
    (fun _ -> big_pts_to r y)

val big_pts_to_not_null_action 
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)

(* Ghost references to "small" types *)
val big_ghost_pts_to (#a:Type u#(a + 1)) (#p:pcm a) (r:ghost_ref p) (v:a) : big_vprop u#a

val big_ghost_alloc
    (#o:_)
    (#a:Type u#(a + 1))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    o
    emp 
    (fun r -> big_ghost_pts_to r x)

val big_ghost_read
    #o
    (#a:Type u#(a + 1))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    (big_ghost_pts_to r x)
    (fun v -> big_ghost_pts_to r (f v))

val big_ghost_write
    #o
    (#a:Type u#(a + 1))
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit o 
    (big_ghost_pts_to r x)
    (fun _ -> big_ghost_pts_to r y)

val big_ghost_share
    #o
    (#a:Type u#(a + 1))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit o
    (big_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)

val big_ghost_gather
    #o
    (#a:Type u#(a + 1))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) o
    (big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)
    (fun _ -> big_ghost_pts_to r (op pcm v0 v1))

