module PulseCore.Coinduction.Sig

module HS = PulseCore.HeapSig

let pred (hs:HS.heap_sig u#hh) (a:Type u#aa)
  : Type u#(max (1+hh) aa)
  = a -> hs.slprop

let slimp (hs:HS.heap_sig u#hh) (p q : hs.slprop) : prop = 
  forall (m:hs.mem).
    hs.interp p (hs.sep.core_of m) ==> hs.interp q (hs.sep.core_of m)

let slimp1 (hs:HS.heap_sig u#hh) (#a:Type u#aa) (p q : pred hs a) : prop = 
  forall (x:a).
    slimp hs (p x) (q x)

let is_mono (hs:HS.heap_sig u#hh) (#a:Type u#aa) (f: pred hs a -> pred hs a) : prop =
  forall p q.
    slimp1 hs p q ==> slimp1 hs (f p) (f q)
    
val gfp (hs:HS.heap_sig u#hh) (#a:Type u#aa) (f: pred hs a -> pred hs a)
  : pred hs a

val gfp_is_fixed_point
  (hs:HS.heap_sig u#hh) (#a:Type u#aa)
  (f: pred hs a -> pred hs a{is_mono hs f}) (x:a)
:
  Lemma (gfp hs f x == f (gfp hs f) x)

val gfp_is_largest
  (hs:HS.heap_sig u#hh) (#a:Type u#aa)
  (f: pred hs a -> pred hs a{is_mono hs f})
  (p:pred hs a)
:
  Lemma (requires forall x. p x == f p x)
        (ensures  forall x. p x `slimp hs` gfp hs f x)
